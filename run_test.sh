set -e
mkdir -p test/build
lake env lean test/basic.lean -o test/build/basic.olean
lake exe oleandump test/build/basic.olean > test/build/basic.oleandump
git diff --no-index test/basic.oleandump.expected test/build/basic.oleandump
