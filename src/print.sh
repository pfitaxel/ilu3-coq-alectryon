#!/bin/sh
alectryon --html-dialect=html5 --frontend coq+rst "$1" --backend webpage --output-directory output && open output/`basename $1 .v`.html
