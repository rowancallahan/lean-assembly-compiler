#!/bin/bash
# runs the front end on Orig.lean; prints each message with its line (the "-- F<n>" marker precedes each attempt)
cd "$(dirname "$0")/../.." && export PATH=~/.elan/bin:$PATH
lake env lean Testing/leansvg/Orig.lean 2>&1
