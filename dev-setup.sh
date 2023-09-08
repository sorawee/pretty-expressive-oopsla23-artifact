#!/usr/bin/env sh

# This script is for development setup outside Docker.

ln -s ~/projects/pretty-expressive pretty-expressive-racket
ln -s ~/projects/fmt fmt
git clone https://github.com/jyp/prettiest
cp -r prettiest/Text ./other-artifacts/Text
pushd other-artifacts
patch -p1 < ../bernardy-remove-width-limit.patch
popd
mv other-artifacts/Text other-artifacts/TextPatched
cp -r prettiest/Text ./other-artifacts/Text
rm -rf prettiest
