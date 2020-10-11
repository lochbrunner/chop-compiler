#!/bin/bash

PATH=$PATH:$PWD/target/release

NC='\033[0m'
GREEN='\033[0;32m'
RED='\033[0;31m'

MILESTONES_DIR=$(dirname $0)

FAILED=0

CASES=($(ls ./milestones/*/*.ch))

errors=()

printf "Testing interpretor\n"
for CASE in "${CASES[@]}"; do
    printf "test $CASE ... "
    expected=$(cat "${CASE%.*}".out)
    actual=$($CASE)

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

printf "\nTesting compiler\n"
for CASE in "${CASES[@]}"; do
    printf "test $CASE ... "
    expected=$(cat "${CASE%.*}".out)
    cchop $CASE -o build/main
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

printf "\n"
if test "$FAILED" -eq "0"; then
    echo -e "${GREEN}All milestones tests succeeded!$NC"
    exit 0
else
    echo -e "${RED}$FAILED milestones tests failed!$NC"
    for error in ${errors[@]}; do
        echo $error
    done
    exit 1
fi