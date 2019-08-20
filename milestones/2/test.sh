#!/bin/bash

set -eu

cchop ./milestones/1/main.ch -o main
./main
cchop ./milestones/1/advanced.ch -o main
./main