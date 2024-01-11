#!/bin/bash

set -e

SESSION_NAME=LinearTimeBranchingTimeSpectroscopyAccountingForSilentSteps

# Build isabelle
isabelle build \
    -v \
    -c \
    -o document=pdf \
    -o document_variants=document:outline=/proof,/ML \
    -P out \
    -d . \
    $SESSION_NAME \
| tee isabelle_log

RED='\033[;31m'
GREEN='\033[0;32m'
NOCOLOR='\033[0m'

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

echo -e "\n${GREEN}Build sucseeded, all theorys were presented.${NOCOLOR}"
