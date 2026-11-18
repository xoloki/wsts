#!/usr/bin/env bash
# Installs the LaTeX packages .doc/build.sh needs to render wsts.tex.
# Ubuntu-only; invoked by .github/workflows/{ci,static}.yml.
set -euo pipefail

# Update apt
sudo apt-get update
# Install LaTeX base and extra packages
sudo apt-get install --yes texlive texlive-latex-extra
