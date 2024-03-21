# Various scripts useful for contributors or developers

This is a "catch-all" directory to hold every script which are roughly relevant to Aegis, but not necessarily fits any structure right now.
It follows the classical `contrib/` directory you may find in other projects.

## Extraction of E2EE libfuncs

Cairo has a treasure of many Sierra code they use to run E2E testing on their libfuncs in https://github.com/starkware-libs/cairo/tree/main/tests/e2e_test_data/libfuncs.
As noted in https://github.com/lindy-labs/aegis/issues/11, it makes sense to extract all of their Sierra and load it in Aegis
for further refinements (spec & proof).

To update those extracted files, you can use:

- `extract_all_e2e_tests.sh` to run in the current working directory of a checkout of Cairo's compiler `libfuncs` directory to generate all `*_aegis` directories containing
split out specification of _each_ function for _each_ family of libfuncs.
- `extract_aegis_tests.py` is the core script which does some very basic string parsing to discover test data and generate it. Note that the parsing is brittle and expect StarkWare to follow their own seemingly consistent (actually, no…) format, some files will fail and that's expected, getting 100 % coverage is a work in progress in parser recovery… :-).
