#!/bin/bash

PATH=$PATH:$PWD/target/release

NC='\033[0m'
GREEN='\033[0;32m'
RED='\033[0;31m'

MILESTONES_DIR=$(dirname $0)

CASES=($(ls milestones/*/*.ch))

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
            printf "${RED}ichop crashed!$NC\n"
            errors+=("Interpreter $CASE crashed")
        elif test "$actual" != "$expected" ;then
            printf "${RED} failed!$NC\n"
            errors+=("Interpreter $CASE\n Expected: \"$expected\" got \"$actual\"")
        else
            printf "${GREEN} ok$NC\n"
        fi
    done
fi

if [ -n "$RUN_CCHOP" ]; then
    printf "\nTesting compiler\n"
    for CASE in "${CASES[@]}"; do
        printf "test $CASE ... "
        target_bin="build/${CASE%.*}"
        mkdir -p `dirname $target_bin`
        expected=$(cat "${CASE%.*}".out)
        timeout $TIMEOUT cchop $CASE -o $target_bin
        if test "$?" -ne "0"; then
            echo -e "${RED}cchop crashed!$NC"
            errors+=("Compiler $CASE crashed")
            continue
        fi
        if [ ! -f $target_bin ]; then
            echo -e "${RED}binary missing!$NC"
            errors+=("Compiler $CASE misses binary $target_bin")
            continue
        fi
        actual=$($target_bin)
        if test "$?" -ne "0"; then
            echo -e "${RED}executable crashed!$NC"
        elif test "$actual" != "$expected" ;then
            printf "${RED}failed!$NC\n"
            errors+=("Compiler $CASE Expected: \"$expected\" got \"$actual\"")
        else
            printf "${GREEN}ok$NC\n"
        fi
    done
fi

printf "\n"
if test "${#errors[@]}" -eq "0"; then
    echo -e "${GREEN}All milestone tests succeeded!$NC"
    exit 0
else
    echo -e "${RED}${#errors[@]} milestone tests failed!$NC"
    for error in "${errors[@]}"; do
        echo $error
    done
    exit 1
fi