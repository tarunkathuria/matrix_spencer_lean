#!/bin/sh
set -eu
matrix_repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$matrix_repo_dir"
exec python3 -B check_rectangular_proof.py --module MatrixSpencer --kernel-replay imports --timeout 3600 "$@"
