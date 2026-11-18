#!/usr/bin/env bash
# Builds the contents of https://wsts.xyz: the rustdoc API documentation, the
# paper as a PDF, and the landing page that links to both.
#
# Invoked directly by .github/workflows/{ci,static}.yml, so it needs its own
# shebang and error handling: without `set -e` a pdflatex or cargo failure
# leaves the step green and silently publishes an incomplete site.
set -euo pipefail

# Build API Documentation. --all-features so that feature-gated modules (v1,
# and the test helpers) appear on the site; without it they are simply missing,
# which is why wsts.xyz/wsts/v1/ used to 404. -D warnings catches broken
# intra-doc links, which RUSTFLAGS does not reach.
RUSTDOCFLAGS="-D warnings" cargo doc --no-deps --all-features

# We have to build the pdf twice. The way the bibliography works is that the
# first run creates the bibtex aux files, then the second run puts the ref
# numbers into the inline citations.
pdflatex -halt-on-error ./wsts.tex
pdflatex -halt-on-error ./wsts.tex

# Copy PDF File
cp ./wsts.pdf ./target/doc/

# Copy index.html
cp ./.doc/index.html ./target/doc/
