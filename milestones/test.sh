#!/bin/bash

PATH=$PATH:$PWD/target/release

NC='\033[0m'
GREEN='\033[0;32m'
RED='\033[0;31m'

MILESTONES_DIR=$(dirname $0)

FAILED=0

CASES=($(ls ./milestones/*/*.ch))

RUN_ICHOP=1
RUN_CCHOP=1

TIMEOUT=1

while [[ $# -gt 0 ]]; do
    key="$1"
    case $key in
        --only-ichop)
        RUN_CCHOP=""
        ;;
        --only-cchop)
        RUN_ICHOP=""
        ;;
    esac
    shift
done

errors=()
if [ -n "$RUN_ICHOP" ]; then
    printf "Testing interpretor\n"
    for CASE in "${CASES[@]}"; do
        printf "test $CASE ... "
        expected=$(cat "${CASE%.*}".out)
        actual=$(timeout $TIMEOUT $CASE)

        if test "$?" -ne "0"; then
            let "FAILED++"
            printf "${RED} crashed!$NC\n"
        elif test "$actual" != "$expected" ;then
            let "FAILED++"
            printf "${RED} failed!$NC\n"
            errors+="Interpeter $CASE\n Expteced: \"$expected\" got \"$actual\""
        else
            printf "${GREEN} ok$NC\n"
        fi
    done
fi

if [ -n "$RUN_CCHOP" ]; then
    printf "\nTesting compiler\n"
    for CASE in "${CASES[@]}"; do
        printf "test $CASE ... "
        expected=$(cat "${CASE%.*}".out)
        timeout $TIMEOUT cchop $CASE -o build/main
        if test "$?" -ne "0"; then
            let "FAILED++"
            echo -e "${RED}cchop crashed!$NC"
        fi
        actual=$(build/main)
        if test "$?" -ne "0"; then
            let "FAILED++"
            echo -e "${RED}executable crashed!$NC"
        elif test "$actual" != "$expected" ;then
            let "FAILED++"
            printf "${RED}failed!$NC\n"
            errors+="Compiler $CASE Expteced: \"$expected\" got \"$actual\""
        else
            printf "${GREEN}ok$NC\n"
        fi
    done
fi

printf "\n"
if test "$FAILED" -eq "0"; then
    echo -e "${GREEN}All milestone tests succeeded!$NC"
    exit 0
else
    echo -e "${RED}$FAILED milestone tests failed!$NC"
    for error in ${errors[@]}; do
        echo $error
    done
    exit 1
fi