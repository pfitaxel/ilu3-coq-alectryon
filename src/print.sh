#!/bin/sh
alectryon --frontend coq+rst "$1" --backend webpage --output-directory output && open output/`basename $1 .v`.html
