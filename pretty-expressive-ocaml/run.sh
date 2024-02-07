#!/usr/bin/env sh

exe=${1%.ml}.exe
shift
dune exec --release --display=quiet "$exe" "$@"
