#!/usr/bin/env bash
# Adapted from PalomarRegistry/PalomarTemplate, scripts/verify-comparator.sh
# at 2891de4c48955af824969a263d31b25e7a9a1406 (Apache-2.0).
set -euo pipefail
cd "$(dirname "$0")/.."
for program in lean lake python3 bwrap; do
  if ! command -v "$program" >/dev/null; then
    echo "Missing required executable: $program" >&2
    exit 2
  fi
done
prefix=$(lean --print-prefix)
for program in lake leanchecker leanexport nanoda_bin con-ron; do
  if [[ ! -x "$prefix/bin/$program" ]]; then
    echo "Missing $prefix/bin/$program in the active Lean release." >&2
    exit 2
  fi
done

# The submitted JSON contains only the registry fields. This temporary copy
# configures the independent checkers used by the official Palomar template.
config=$(mktemp)
trap 'rm -f "$config"' EXIT
python3 - "$prefix" "$config" <<'PY'
import json
import sys
from pathlib import Path

source = json.loads(Path("comparator.json").read_text(encoding="utf-8"))
targets = ["Density.euclidean", "Density.integerLp", "Density.nonEuclideanLp"]
if source.get("theorem_names") != targets:
    raise SystemExit("The configuration must check all three introduction theorems.")
allowed = {"propext", "Classical.choice", "Quot.sound"}
if not set(source["permitted_axioms"]) <= allowed:
    raise SystemExit("The axiom allowlist was enlarged.")
if "external_kernels" in source:
    raise SystemExit("Palomar reserves external_kernels for its verifier.")
source.pop("enable_nanoda", None)
bin_dir = Path(sys.argv[1]) / "bin"
source["external_kernels"] = {
    "nanoda": [str(bin_dir / "nanoda_bin")],
    "con-ron": [str(bin_dir / "con-ron")],
}
Path(sys.argv[2]).write_text(json.dumps(source), encoding="utf-8")
PY

set -x
lean --version
lake --version
bwrap --version
"$prefix/bin/lake" comparator --config "$config"
