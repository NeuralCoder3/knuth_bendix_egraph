#!/bin/bash

python translate.py > rules.rule

../target/debug/main -r rules.rule -t input.txt -i 1
