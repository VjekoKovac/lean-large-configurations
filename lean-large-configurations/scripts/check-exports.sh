#!/usr/bin/env bash
# Replay pre-built local exports inside a separate, read-only Linux sandbox.
# Run from the repository checkout with a pinned Lean toolchain, Mathlib's
# cache, bubblewrap, and util-linux unshare. This also works on the managed
# host on which Lake's nested network-namespace setup cannot start.
set -euo pipefail
cd "$(dirname "$0")/.."
scope=${1:?Use all to check the three public declarations}
out=${2:?Supply a directory outside the repository to hold large exports}
mkdir -p "$out"
out=$(realpath "$out")
prefix=$(lean --print-prefix)
if [[ "$scope" != all ]]; then
  echo "Use all as the first argument to check the three introduction theorems." >&2
  exit 2
fi
targets=(Density.euclidean Density.integerLp Density.nonEuclideanLp)

# Lake.CLI.Check.primitiveTargets and builtinTargets, Lean 4.35.0.
primitives=(Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble
  Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List
  eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam)
quotients=(Quot Quot.mk Quot.lift Quot.ind)
axioms=(propext Classical.choice Quot.sound)
export_names=("${quotients[@]}" "${targets[@]}" "${axioms[@]}" "${primitives[@]}")

set -x
lean --version
lake --version
bwrap --version
lake build Challenge Solution
for module in Challenge Solution; do
  lake env leanexport "$module" -- "${export_names[@]}" > "$out/${module,,}.ndjson"
done
sha256sum "$out/challenge.ndjson" "$out/solution.ndjson"
set +x
python3 - "$out" "${targets[@]}" <<'PY'
from pathlib import Path
import sys, json
cfg = json.loads(Path("comparator.json").read_text())
targets = sys.argv[2:]
assert set(targets) <= set(cfg["theorem_names"])
cfg["theorem_names"] = targets
cfg["external_kernels"] = {
    "nanoda": ["/lean/bin/nanoda_bin"],
    "con-ron": ["/lean/bin/con-ron"],
}
Path(sys.argv[1], "judgment.json").write_text(json.dumps(cfg))
PY

# The checker sees the pinned toolchain, the exports, and the operating system
# runtime, with read-only mounts. Its temporary directory is disposable. The
# independent user and network namespaces leave it unprivileged and offline.
# No project source, .olean files, home directory, or Git credentials are mounted.
set -x
unshare --user --map-current-user --net --fork \
  bwrap --die-with-parent --new-session --unshare-pid --unshare-ipc --unshare-uts \
  --cap-drop ALL --tmpfs / --ro-bind /usr /usr --ro-bind-try /etc/alternatives /etc/alternatives --symlink usr/bin /bin \
  --symlink usr/lib /lib --symlink usr/lib64 /lib64 --proc /proc --dev /dev \
  --tmpfs /tmp --dir /empty --dir /root --dir /run/user --chdir /empty \
  --ro-bind "$prefix" /lean --ro-bind "$out" /exports \
  --clearenv --setenv PATH /lean/bin:/usr/bin --setenv LEAN_NUM_THREADS 2 \
  /lean/bin/lake comparator --inadvisably-no-sandbox --config=/exports/judgment.json \
  --challenge-from-export=/exports/challenge.ndjson --solution-from-export=/exports/solution.ndjson
