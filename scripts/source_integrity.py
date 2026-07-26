#!/usr/bin/env python3
"""Record or verify the byte-for-byte integrity of the released Lean sources."""

from __future__ import annotations

import argparse
import hashlib
import json
from datetime import date
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BASELINE = ROOT / "reports" / "source-integrity.json"
SOURCE_ROOTS = (ROOT / "DG", ROOT / "EnumerationTheory")


def collect() -> dict:
    entries: list[dict] = []
    scopes: dict[str, dict[str, int]] = {}

    for path in sorted(
        (p for root in SOURCE_ROOTS for p in root.rglob("*.lean")),
        key=lambda p: p.relative_to(ROOT).as_posix(),
    ):
        relative = path.relative_to(ROOT).as_posix()
        data = path.read_bytes()
        lines = data.splitlines()
        scope = relative.split("/", 1)[0]
        scope_data = scopes.setdefault(
            scope, {"files": 0, "physical_lines": 0, "nonblank_lines": 0}
        )
        scope_data["files"] += 1
        scope_data["physical_lines"] += len(lines)
        scope_data["nonblank_lines"] += sum(bool(line.strip()) for line in lines)
        entries.append(
            {
                "path": relative,
                "sha256": hashlib.sha256(data).hexdigest(),
                "bytes": len(data),
                "physical_lines": len(lines),
                "nonblank_lines": sum(bool(line.strip()) for line in lines),
            }
        )

    aggregate_text = "".join(
        f"{entry['sha256']}  {entry['path']}\n" for entry in entries
    ).encode("utf-8")
    totals = {
        "files": len(entries),
        "physical_lines": sum(entry["physical_lines"] for entry in entries),
        "nonblank_lines": sum(entry["nonblank_lines"] for entry in entries),
        "bytes": sum(entry["bytes"] for entry in entries),
    }
    return {
        "schema_version": 1,
        "generated_on": date.today().isoformat(),
        "algorithm": "SHA-256 over each file; aggregate over sorted '<hash>  <path>\\n' records",
        "aggregate_sha256": hashlib.sha256(aggregate_text).hexdigest(),
        "totals": totals,
        "scopes": scopes,
        "files": entries,
    }


def verify(current: dict, baseline: dict) -> None:
    expected = {entry["path"]: entry["sha256"] for entry in baseline["files"]}
    actual = {entry["path"]: entry["sha256"] for entry in current["files"]}
    added = sorted(actual.keys() - expected.keys())
    removed = sorted(expected.keys() - actual.keys())
    changed = sorted(
        path for path in actual.keys() & expected.keys() if actual[path] != expected[path]
    )
    if added or removed or changed:
        if added:
            print("Added Lean files:", *added, sep="\n  ")
        if removed:
            print("Removed Lean files:", *removed, sep="\n  ")
        if changed:
            print("Changed Lean files:", *changed, sep="\n  ")
        raise SystemExit("Lean source integrity verification failed.")

    if current["aggregate_sha256"] != baseline["aggregate_sha256"]:
        raise SystemExit("Aggregate Lean source hash does not match the baseline.")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the current source state as the release baseline",
    )
    args = parser.parse_args()
    current = collect()

    if args.write:
        BASELINE.parent.mkdir(parents=True, exist_ok=True)
        BASELINE.write_text(
            json.dumps(current, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        action = "Wrote"
    else:
        if not BASELINE.is_file():
            raise SystemExit(f"Missing baseline: {BASELINE.relative_to(ROOT)}")
        baseline = json.loads(BASELINE.read_text(encoding="utf-8"))
        verify(current, baseline)
        action = "Verified"

    totals = current["totals"]
    print(
        f"{action} {totals['files']} Lean files; "
        f"{totals['physical_lines']} physical lines; "
        f"{totals['nonblank_lines']} nonblank lines."
    )
    print(f"Aggregate SHA-256: {current['aggregate_sha256']}")


if __name__ == "__main__":
    main()
