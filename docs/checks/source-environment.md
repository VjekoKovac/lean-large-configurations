# Source-build Comparator environment

The public verification command on a Linux host with a working bubblewrap installation is `bash scripts/verify-comparator.sh`. The GitHub workflow is configured to use that command from a fresh checkout. On the preparation host two additional steps supplied mount points and an empty network namespace. Both retained Lake's build and export sandbox, including its use of separate environments for Challenge and Solution.

The host lacked `/root` and `/run/user`, two mount targets in Lake's standard sandbox. An outer bubblewrap process supplied them. The host allowed creation of an isolated network namespace but denied the route socket which bubblewrap normally opens to bring up loopback there. The `COMPARATOR_BWRAP` executable uses `unshare` to create a fresh network namespace first, then tells the real bubblewrap to inherit that namespace. Lake's other sandbox arguments pass through to bubblewrap. This configuration uses cached dependencies and isolates even the dependency-resolution step from the network. [Exact adapter from this run](../../scripts/offline-bwrap)

The following commands were used in the preparation workspace. The local adapter path referred to a byte-identical copy of `scripts/offline-bwrap`.

```sh
cd /workspace/scratch/8dddb3cf0936/repo
export COMPARATOR_BWRAP=/workspace/scratch/8dddb3cf0936/setup/offline-bwrap
export PATH="/workspace/scratch/8dddb3cf0936/setup/tools/lean-4.35.0-linux/bin:/usr/local/bin:/usr/bin:/bin"
bwrap --tmpfs / --ro-bind /usr /usr --symlink usr/bin /bin \
  --symlink usr/lib /lib --symlink usr/lib64 /lib64 --symlink usr/sbin /sbin \
  --proc /proc --dev /dev --ro-bind /etc /etc --tmpfs /tmp --ro-bind /opt /opt \
  --ro-bind /home /home --dir /root --dir /run/user --dir /var --dir /sys \
  --bind /workspace /workspace --chdir "$PWD" -- bash scripts/verify-comparator.sh all
```

An independent namespace test using the adapter reported a different network namespace identifier inside the sandbox, only the `lo` device with zero traffic, and an empty IPv4 routing table. The source-build log records Lake's own build, export, comparison, and kernel output. [Source-build log](comparator-source.txt)
