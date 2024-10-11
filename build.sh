#!/bin/bash

set -e

SESSION_NAME=Weak_Spectroscopy

if test $# -ge 1 && test $1 == -c; then
    BUILD_CLEAN_AND_CHECK=true
    ISABELLE_ARG=-c
else
    BUILD_CLEAN_AND_CHECK=false
    ISABELLE_ARG=""
fi

# Build isabelle
isabelle build \
    -v \
    $ISABELLE_ARG \
    -o document=pdf \
    -o document_variants=document:outline=/proof,/ML \
    -P out \
    -d . \
    $SESSION_NAME \
| tee isabelle_log

RED='\033[;31m'
GREEN='\033[0;32m'
NOCOLOR='\033[0m'

if $BUILD_CLEAN_AND_CHECK;
then
    # Check that all .thy files not ending with an "_" were presented
    (diff \
        <( \
            cat isabelle_log | \
            grep "Presenting theory \"$SESSION_NAME." | \
            grep $SESSION_NAME | \
            sort\
        ) \
        <( \
            find . -name "*.thy" -not -name "*_.thy" -exec basename {} .thy ';' | \
            sort | \
            awk -v SN=$SESSION_NAME '{print "Presenting theory \"" SN "." $0 "\""}' \
        ) \
    ) || (echo -e "${RED}Not all .thy files were 'presented'.${NOCOLOR}"; /bin/false)

    echo -e "\n${GREEN}Build succeeded, all theories were presented.${NOCOLOR}"
else
    echo -e "${GREEN}Build succeeded, did **not** check that all theories were presented.${NOCOLOR}"
fi
