#!/usr/bin/env python3
"""Export the pinned Challenge and Solution and run Palomar's three kernels."""
import argparse
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--package', type=Path, required=True)
parser.add_argument('--report', type=Path)
parser.add_argument('--label', default='comparator')
args = parser.parse_args()
root = args.package.resolve()
report = (args.report or root / 'verification').resolve()
report.mkdir(parents=True, exist_ok=True)
evidence = report / args.label
evidence.mkdir(exist_ok=True)
prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
env = {**os.environ, 'PATH': str(prefix / 'bin') + os.pathsep + os.environ['PATH'],
       'LEAN_NUM_THREADS': '1', 'LEAN_ABORT_ON_PANIC': '1'}
configuration = json.loads((root / 'comparator.json').read_text())
source = (prefix / 'src/lean/lake/Lake/CLI/Check.lean').read_text()
primitive = source.split('def primitiveTargets', 1)[1].split('def builtinTargets', 1)[0]
primitive = re.sub(r'--[^\n]*', '', primitive)
targets = configuration['theorem_names'] + configuration['permitted_axioms']
targets += re.findall(r'``([A-Za-z0-9_.]+)', primitive)
targets += ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
targets += configuration.get('definition_names', [])
targets = list(dict.fromkeys(targets))
result = {'scope': 'Export-based Palomar Comparator; default sandbox enabled',
          'package': str(root), 'configuration': configuration, 'targets': targets,
          'commands': [], 'accepted': False, 'status': 'RUNNING',
          'binary_sha256': {name: hashlib.sha256((prefix / 'bin' / name).read_bytes()).hexdigest()
                           for name in ['lean', 'lake', 'leanexport', 'leanchecker', 'con-ron', 'nanoda_bin']}}
resultpath = evidence / 'comparator-result.json'

def save():
    resultpath.write_text(json.dumps(result, indent=2) + '\n')

def run(label, command, output=None):
    log = evidence / (label + '.log')
    print('COMMAND', args.label, label, command, flush=True)
    started = time.monotonic()
    with log.open('w') as errors:
        if output is not None:
            with output.open('wb') as data:
                proc = subprocess.run(command, cwd=root, env=env, stdout=data, stderr=errors)
        else:
            proc = subprocess.run(command, cwd=root, env=env, stdout=errors, stderr=subprocess.STDOUT)
    rec = {'label': label, 'argv': list(map(str, command)), 'cwd': str(root),
           'exit_code': proc.returncode, 'elapsed_seconds': round(time.monotonic() - started, 3),
           'log': str(log)}
    if output is not None:
        with output.open('rb') as data:
            rec.update(export=str(output), export_bytes=output.stat().st_size,
                       export_sha256=hashlib.file_digest(data, 'sha256').hexdigest())
    result['commands'].append(rec)
    save()
    print(f'EXIT {args.label} {label}: {proc.returncode}; seconds={rec["elapsed_seconds"]}', flush=True)
    if proc.returncode:
        print(log.read_text()[-8000:], flush=True)
        raise RuntimeError(label + ' failed')
    return log.read_text()

try:
    save()
    exports = []
    for side in ('challenge', 'solution'):
        output = evidence / (side + '.ndjson')
        exports.append(output)
        run(side + '-export', ['lake', 'env', 'leanexport', configuration[side + '_module'], '--', *targets], output)
    transcript = run('comparator', ['lake', 'env', 'lake', 'comparator', '--config', str(root / 'comparator.json'),
                         '--challenge-from-export', str(exports[0]), '--solution-from-export', str(exports[1])])
    markers = ['con-ron kernel accepts the solution', 'nanoda kernel accepts the solution',
               'Lean default kernel accepts the solution', 'Your solution is okay!']
    result['acceptance_markers'] = {m: bool(re.search('^' + re.escape(m) + '$', transcript, re.M)) for m in markers}
    result['accepted'] = all(result['acceptance_markers'].values())
    print(transcript, flush=True)
    if not result['accepted']:
        raise RuntimeError('Missing required acceptance marker')
    result['status'] = 'PASS'
except Exception as error:
    result['status'] = 'FAIL'
    result['error'] = str(error)
finally:
    save()
print('VERDICT:', args.label, result['status'], '; accepted=', result['accepted'], flush=True)
raise SystemExit(0 if result['accepted'] else 1)
