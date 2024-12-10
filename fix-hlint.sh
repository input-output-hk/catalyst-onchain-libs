#!/usr/bin/env bash

# hlint -j --refactor --refactor-options="-i"

fd --extension hs --exclude 'dist-newstyle/*' --exclude 'dist/*' --exclude '.stack-work/*' --exec bash -c "hlint  -j --refactor --refactor-options='-i' {}"
