#!/bin/bash

NC='\033[0m'
GREEN='\033[0;32m'
RED='\033[0;31m'

MILESTONES_DIR=$(dirname $0)

FAILED=0

CASES=(
    "1/main.ch" "1/advanced.ch"
    "2/test.sh"
)

for CASE in "${CASES[@]}"; do
    $MILESTONES_DIR/$CASE > /dev/null
    if test "$?" -ne "0"; then
        let "FAILED++"
        echo -e "${RED}Test $CASE failed!$NC"
    else
        echo -e "${GREEN}Test $CASE was ok.$NC"
    fi
done


if test "$FAILED" -eq "0"; then
    echo -e "${GREEN}All Milestones tests succeeded!$NC"
    exit 0
else
    echo -e "${RED}$FAILED Milestones tests failed!$NC"
    exit 1
fi