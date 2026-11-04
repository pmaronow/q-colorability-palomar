#!/usr/bin/env python3
"""Build and compare the current sources with Lean, NanoDa, and optional con-ron.

This is a local reproducibility check, not Palomar's protected verification
workflow. The submitted comparator.json stays compatible with Palomar; external
kernel commands are added only to a temporary execution configuration.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


def sha256(path):
    with path.open('rb') as data:
        return hashlib.file_digest(data, 'sha256').hexdigest()


def snapshot(root, evidence):
    """Hash versioned inputs and new source files, excluding build/report output."""
    paths = subprocess.check_output(
        ['git', 'ls-files', '--cached', '--others', '--exclude-standard', '-z'],
        cwd=root,
    ).decode().split('\0')
    hashes = {}
    for relative in sorted(set(filter(None, paths))):
        path = root / relative
        if (relative.startswith(('verification/', '.lake/'))
                or evidence == path or evidence in path.parents):
            continue
        if path.is_symlink():
            hashes[relative] = {'symlink': os.readlink(path)}
        elif path.is_file():
            hashes[relative] = sha256(path)
    payload = json.dumps(hashes, sort_keys=True, separators=(',', ':')).encode()
    return {'sha256': hashlib.sha256(payload).hexdigest(), 'files': hashes}


def primitive_targets(prefix):
    """Read the selected Comparator's literal builtin list rather than guessing."""
    source = (prefix / 'src/lean/lake/Lake/CLI/Check.lean').read_text()
    match = re.search(r'^def primitiveTargets[^\n]*\n(.*?)^def ', source, re.M | re.S)
    if match is None:
        raise RuntimeError('Unrecognised Comparator primitiveTargets definition')
    body = re.sub(r'/-.*?-/', '', match.group(1), flags=re.S)
    body = '\n'.join(line.split('--', 1)[0] for line in body.splitlines())
    literal = re.fullmatch(r'\s*return\s*#\[([^\[\]]*)\]\s*', body)
    if literal is None:
        raise RuntimeError('Unrecognised Comparator primitiveTargets array')
    names = []
    for item in literal.group(1).split(','):
        if not item.strip():
            continue
        name = re.fullmatch(r"``([A-Za-z_][A-Za-z0-9_'.]*)", item.strip())
        if name is None:
            raise RuntimeError('Unrecognised Comparator primitive target')
        names.append(name.group(1))
    if not names or len(names) != len(set(names)):
        raise RuntimeError('Empty or duplicate Comparator primitive targets')
    return names


def configuration(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError('Duplicate Comparator key: ' + key)
            result[key] = value
        return result

    config = json.loads(path.read_text(), object_pairs_hook=unique_object)
    required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    allowed = required | {'definition_names', 'enable_nanoda'}
    if not isinstance(config, dict) or not required <= config.keys() or config.keys() - allowed:
        raise ValueError('comparator.json must use Palomar\'s submitted configuration schema')
    for field in ('challenge_module', 'solution_module'):
        if not isinstance(config[field], str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*", config[field]):
            raise ValueError('Invalid ' + field)
    if config['challenge_module'] == config['solution_module']:
        raise ValueError('Challenge and Solution must be distinct modules')
    if not isinstance(config['theorem_names'], list) or not config['theorem_names']:
        raise ValueError('theorem_names must be a nonempty array')
    if not isinstance(config.get('definition_names', []), list):
        raise ValueError('definition_names must be an array')
    for name in config['theorem_names'] + config.get('definition_names', []):
        if not isinstance(name, str) or not name or re.search(r'[\x00-\x1f\x7f]', name):
            raise ValueError('Invalid declaration name')
    axioms = config['permitted_axioms']
    if (not isinstance(axioms, list) or not all(isinstance(name, str) for name in axioms)
            or not set(axioms) <= {'propext', 'Quot.sound', 'Classical.choice'}):
        raise ValueError('permitted_axioms exceeds the standard allowlist')
    return config


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--report', type=Path)
    parser.add_argument('--label', default='comparator-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
    parser.add_argument('--nanoda', type=Path, help='NanoDa binary; defaults to the selected toolchain')
    parser.add_argument('--con-ron', type=Path, help='Optional checker override (e.g. Palomar\'s pinned update)')
    parser.add_argument('--without-con-ron', action='store_true', help='Run only the mandatory Lean and NanoDa checks')
    args = parser.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]*', args.label):
        parser.error('--label must be a single safe directory name')
    if args.con_ron and args.without_con_ron:
        parser.error('--con-ron and --without-con-ron are mutually exclusive')
    root = args.package.resolve()
    report = (args.report or root / 'verification').resolve()
    report.mkdir(parents=True, exist_ok=True)
    evidence = report / args.label
    evidence.mkdir(exist_ok=False)  # Never overwrite evidence for an earlier tree.
    resultpath = evidence / 'comparator-result.json'
    result = {
        'scope': 'Local build and export-based Comparator check; not an official Palomar verification',
        'started_at': datetime.now(timezone.utc).isoformat(),
        'package': str(root), 'commands': [], 'accepted': False, 'status': 'RUNNING',
        'build_kind': 'Lake rebuild with source trace validation; not a claim of a clean checkout',
    }

    def save():
        resultpath.write_text(json.dumps(result, indent=2) + '\n')

    def run(label, command, output=None):
        command = list(map(str, command))
        log = evidence / (label + '.log')
        print('COMMAND', args.label, label, command, flush=True)
        started = time.monotonic()
        with log.open('wb') as errors:
            if output is not None:
                with output.open('wb') as data:
                    proc = subprocess.run(command, cwd=root, env=env, stdout=data, stderr=errors)
            else:
                proc = subprocess.run(command, cwd=root, env=env, stdout=errors, stderr=subprocess.STDOUT)
        rec = {'label': label, 'argv': command, 'cwd': str(root), 'exit_code': proc.returncode,
               'elapsed_seconds': round(time.monotonic() - started, 3), 'log': log.name}
        if output is not None:
            rec.update(export=output.name, export_bytes=output.stat().st_size, export_sha256=sha256(output))
        result['commands'].append(rec)
        save()
        print(f'EXIT {args.label} {label}: {proc.returncode}; seconds={rec["elapsed_seconds"]}', flush=True)
        if proc.returncode:
            print(log.read_text(errors='replace')[-8000:], flush=True)
            raise RuntimeError(label + ' failed')
        return log.read_text(errors='replace')

    try:
        save()
        prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=root, text=True).strip())
        env = {**os.environ, 'PATH': str(prefix / 'bin') + os.pathsep + os.environ['PATH'],
               'LEAN_ABORT_ON_PANIC': '1'}
        config = configuration(root / 'comparator.json')
        result['configuration'] = config
        result['toolchain'] = (root / 'lean-toolchain').read_text().strip()
        result['lean_version'] = subprocess.check_output(['lean', '--version'], cwd=root, env=env, text=True).strip()
        result['git_head'] = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip()
        result['git_status'] = subprocess.check_output(['git', 'status', '--porcelain'], cwd=root, text=True).splitlines()
        result['source_snapshot'] = snapshot(root, evidence)
        required = {name: prefix / 'bin' / name for name in ('lean', 'lake', 'leanexport', 'leanchecker')}
        required['nanoda_bin'] = (args.nanoda or prefix / 'bin/nanoda_bin').resolve()
        for name, path in required.items():
            if not path.is_file() or not os.access(path, os.X_OK):
                raise RuntimeError('Required executable is missing: ' + str(path))
        kernels = {'nanoda': [str(required['nanoda_bin'])]}
        con_ron = (args.con_ron or Path(shutil.which('con-ron') or prefix / 'bin/con-ron')).resolve()
        if not args.without_con_ron and con_ron.is_file() and os.access(con_ron, os.X_OK):
            kernels['con-ron'] = [str(con_ron), '--verified', '--jobs=2']
            required['con-ron'] = con_ron
        elif args.con_ron:
            raise RuntimeError('Requested con-ron executable is missing: ' + str(con_ron))
        result['kernels'] = kernels
        result['binary_sha256'] = {name: sha256(path) for name, path in required.items()}
        result['binary_paths'] = {name: str(path) for name, path in required.items()}
        targets = config['theorem_names'] + config['permitted_axioms'] + primitive_targets(prefix)
        if 'Quot.sound' in config['permitted_axioms']:
            targets += ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
        targets += config.get('definition_names', [])
        targets = list(dict.fromkeys(targets))
        result['targets'] = targets
        save()
        run('build', ['lake', '--no-cache', 'build'])
        exports = []
        for side in ('challenge', 'solution'):
            output = evidence / (side + '.ndjson')
            exports.append(output)
            run(side + '-export', ['lake', 'env', required['leanexport'], config[side + '_module'], '--', *targets], output)
        effective = {key: value for key, value in config.items() if key != 'enable_nanoda'}
        effective['external_kernels'] = kernels
        result['execution_configuration'] = effective
        # Keep execution-only external_kernels out of the submitted configuration.
        with tempfile.TemporaryDirectory(prefix='q-colorability-comparator-') as directory:
            temporary_config = Path(directory) / 'comparator.json'
            temporary_config.write_text(json.dumps(effective, indent=2) + '\n')
            transcript = run('comparator', ['lake', 'env', 'lake', 'comparator', '--config', temporary_config,
                             '--challenge-from-export', exports[0], '--solution-from-export', exports[1]])
        markers = [name + ' kernel accepts the solution' for name in kernels]
        markers += ['Lean default kernel accepts the solution', 'Your solution is okay!']
        result['acceptance_markers'] = {marker: bool(re.search('^' + re.escape(marker) + '$', transcript, re.M))
                                        for marker in markers}
        result['source_snapshot_after'] = snapshot(root, evidence)['sha256']
        if result['source_snapshot_after'] != result['source_snapshot']['sha256']:
            raise RuntimeError('Source files changed during verification; rerun against a stable tree')
        result['accepted'] = all(result['acceptance_markers'].values())
        if not result['accepted']:
            raise RuntimeError('Missing required kernel acceptance marker')
        result['status'] = 'PASS'
    except Exception as error:
        result['accepted'] = False
        result['status'] = 'FAIL'
        result['error'] = str(error)
        print('ERROR:', error, flush=True)
    finally:
        result['finished_at'] = datetime.now(timezone.utc).isoformat()
        save()
    print('VERDICT:', args.label, result['status'], '; accepted=', result['accepted'], flush=True)
    return 0 if result['accepted'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
