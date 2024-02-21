#!/usr/bin/env bash
for defn_test in {,**/}*; do
    ./extract_aegis_tests.py $defn_test "${defn_test}_aegis"
done
