#!/usr/bin/env python3
"""Run Palomar's current non-building checks against this project.

Use a checkout of https://github.com/PalomarRegistry/PalomarSubmission and its
Python requirements. This script imports that checkout's validators instead
of maintaining a second copy of Palomar's policy. It does not contact Palomar,
change repository visibility, submit a result, or establish a kernel verdict.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import subprocess
import sys


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--palomar-submission", type=Path, required=True,
                        help="checkout containing PalomarSubmission/scripts")
    parser.add_argument("--licensee-bundle", type=Path,
                        help="Bundler executable with PalomarSubmission's locked gems installed")
    parser.add_argument("--json-output", type=Path)
    args = parser.parse_args()
    root = args.package.resolve()
    upstream = args.palomar_submission.resolve()
    if not (upstream / "scripts/submission_contract.py").is_file():
        parser.error("--palomar-submission must name a PalomarSubmission checkout")

    sys.path.insert(0, str(upstream))
    try:
        from scripts import submission_contract, verify_submission
        from scripts.source_requirements import inspect_lean_sources
    except ImportError as error:
        parser.error(f"Cannot import upstream validators: {error}; install their requirements.txt")

    result = {"scope": "Local non-building Palomar checks; public access and kernel replay are separate",
              "package": str(root), "checks": {}}
    try:
        result["palomar_submission_commit"] = subprocess.check_output(
            ["git", "-C", str(upstream), "rev-parse", "HEAD"], text=True).strip()
    except subprocess.CalledProcessError:
        result["palomar_submission_commit"] = "unavailable"

    def check(name, action):
        try:
            value = action()
            result["checks"][name] = {"status": "PASS", "result": value}
            return value
        except Exception as error:
            result["checks"][name] = {"status": "FAIL", "error": str(error)}
            return None

    def require_manifest():
        path = root / "lake-manifest.json"
        if path.is_symlink() or not path.is_file():
            raise ValueError("Commit a regular lake-manifest.json before submitting")
        # The committed-manifest path does not manufacture or resolve a lockfile.
        return verify_submission.ensure_lake_manifest(root, root)

    def inspect_sources():
        summary, issues = inspect_lean_sources(root)
        if issues:
            raise ValueError("; ".join(str(issue) for issue in issues))
        return summary

    def challenge_limits(configuration):
        if configuration is None:
            raise ValueError("Comparator configuration must pass first")
        suffix = verify_submission.module_source_suffix(configuration["challenge_module"])
        path = root / suffix
        if path.is_symlink() or not path.is_file():
            raise ValueError("Challenge source must be a regular project-root module")
        data = path.read_bytes()
        lines = data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))
        if len(data) > verify_submission.MAX_CHALLENGE_BYTES or lines > verify_submission.MAX_CHALLENGE_LINES:
            raise ValueError("Challenge exceeds Palomar's 100 KiB or 1,000-line limit")
        return {"path": suffix.as_posix(), "bytes": len(data), "lines": lines}

    configuration = check("comparator", lambda: verify_submission.load_comparator_config(root / "comparator.json"))
    check("manifest_present", require_manifest)
    check("dependency_pins", lambda: verify_submission.manifest_packages(root))
    check("preservable_git", lambda: verify_submission.validate_preservable_git_checkout(root, "submitted source"))
    check("no_compiled_artifacts", lambda: verify_submission.reject_committed_build_artifacts(root))
    check("lean_sources", inspect_sources)
    check("challenge_limits", lambda: challenge_limits(configuration))
    license_path = check("license_file", lambda: str(verify_submission.repository_license_file(root)))
    metadata = check("formalization", lambda: submission_contract.load_formalization_metadata(root / "formalization.yaml"))
    if args.licensee_bundle:
        def inspect_license():
            if license_path is None or metadata is None:
                raise ValueError("License file and metadata must pass first")
            detected = verify_submission.detect_spdx_identifier(Path(license_path), args.licensee_bundle.resolve())
            declared = metadata["project"]["license"].strip()
            if declared != detected:
                raise ValueError(f"Declared license {declared!r} differs from detected {detected!r}")
            return detected
        check("license_spdx", inspect_license)
    else:
        result["checks"]["license_spdx"] = {
            "status": "NOT RUN",
            "reason": "Supply --licensee-bundle to run Palomar's exact locked SPDX detector"}

    for name, entry in result["checks"].items():
        print(f"{entry['status']}: {name}" + (f": {entry['error']}" if "error" in entry else ""))
    failed = any(entry["status"] == "FAIL" for entry in result["checks"].values())
    incomplete = any(entry["status"] == "NOT RUN" for entry in result["checks"].values())
    result["status"] = "FAIL" if failed else "INCOMPLETE" if incomplete else "PASS"
    if args.json_output:
        args.json_output.parent.mkdir(parents=True, exist_ok=True)
        args.json_output.write_text(json.dumps(result, indent=2) + "\n")
    print(f"Local preflight: {result['status']}")
    return 1 if failed else 2 if incomplete else 0


if __name__ == "__main__":
    raise SystemExit(main())
