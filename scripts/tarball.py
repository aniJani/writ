"""Writes <out>, a reproducible .tar.gz of the directory <parent>/<name>, stored as <name>/...

    python3 -I scripts/tarball.py <out> <parent> <name>

Entries are sorted, owned by uid and gid 0 with empty user and group names, dated
SOURCE_DATE_EPOCH (default: the commit time of HEAD), with mode 0755 for directories and
executables and 0644 otherwise, and no extended attributes; the gzip header has mtime 0 and no
file name. The same files give the same tar stream on any machine; the compressed bytes are fixed
for a given Python and zlib (macOS Python 3.15 and Linux Python 3.12 give the same tar stream but
different gzip bytes). Only regular files and directories
are accepted.
"""

from __future__ import annotations

import gzip
import os
import subprocess
import sys
import tarfile


def main() -> None:
    if len(sys.argv) != 4:
        sys.exit("usage: python3 -I scripts/tarball.py <out> <parent> <name>")
    out, parent, name = sys.argv[1:]
    epoch = os.environ.get("SOURCE_DATE_EPOCH") or subprocess.run(
        ["git", "log", "-1", "--format=%ct"], check=True, capture_output=True, text=True
    ).stdout.strip()
    mtime = int(epoch)

    paths = [name]
    for dirpath, dirnames, filenames in os.walk(os.path.join(parent, name)):
        rel = os.path.relpath(dirpath, parent)
        paths += [os.path.join(rel, n) for n in dirnames + filenames]
    paths.sort()

    with open(out, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0) as gz:
        with tarfile.open(fileobj=gz, mode="w", format=tarfile.GNU_FORMAT) as tar:
            for path in paths:
                full = os.path.join(parent, path)
                info = tarfile.TarInfo(path.replace(os.sep, "/"))
                info.uid = info.gid = 0
                info.uname = info.gname = ""
                info.mtime = mtime
                if os.path.islink(full):
                    sys.exit(f"{full} is a symbolic link")
                if os.path.isdir(full):
                    info.type = tarfile.DIRTYPE
                    info.mode = 0o755
                    tar.addfile(info)
                elif os.path.isfile(full):
                    info.mode = 0o755 if os.stat(full).st_mode & 0o111 else 0o644
                    info.size = os.path.getsize(full)
                    with open(full, "rb") as f:
                        tar.addfile(info, f)
                else:
                    sys.exit(f"{full} is neither a file nor a directory")


if __name__ == "__main__":
    main()
