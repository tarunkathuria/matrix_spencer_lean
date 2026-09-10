#!/bin/sh
set -eu
matrix_repo_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$matrix_repo_dir"
if command -v lake >/dev/null 2>&1; then
  exec lake "$@"
fi
if [ -x "$HOME/.elan/bin/lake" ]; then
  exec "$HOME/.elan/bin/lake" "$@"
fi
printf '%s\n' 'Lake is unavailable. Install Lean with elan, then rerun this command.' >&2
exit 127
