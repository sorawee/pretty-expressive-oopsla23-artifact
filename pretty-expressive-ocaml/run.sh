#!/usr/bin/env sh

# Usage example:
#   ./run.sh ./wadler_time.ml -- 100
#   ./run.sh ./wadler_time.ml -- -show 100
#   ./run.sh ./wadler_opt.ml
# Note that ./ is significant!

exe=${1%.ml}.exe
shift
dune exec --display=quiet "$exe" "$@"
