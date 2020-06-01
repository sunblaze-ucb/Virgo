#!/bin/sh

./sha256gen.py -4
( for i in $(seq 1 8); do echo $i; done ) | parallel python sha256gen.py -R -P -m
