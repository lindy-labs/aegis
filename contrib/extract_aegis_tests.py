#!/usr/bin/env python3
import sys
from dataclasses import dataclass
from collections import defaultdict
from pathlib import Path

TEST_MARKER = "//! > =========================================================================="

@dataclass
class TestFunData:
    name: str
    test_runner_name: str
    casm: str
    function_costs: str
    sierra_code: str
    cairo_code: str
    test_comments: str | None

@dataclass
class TestData:
    funs: list[TestFunData]

def parse_comment(comment: str) -> str:
    """
    >>> parse_comment("//! > cairo")
    cairo
    >>> parse_comment("//! > test_runner_name")
    test_runner_name
    """
    return comment.split('>')[1].strip()

def build_fun_data(indexes: dict[str, dict[str, int]], lines: list[str]) -> TestFunData:
    attrs = {}

    attrs['test_comments'] = None

    for key, range_ in indexes.items():
        if 'libfunc' in key:
            attrs['name'] = key[:key.find('libfunc')].strip()
        else:
            start, stop = range_['start'], range_.get('end')
            if stop is None:
                attrs[key] = '\n'.join(lines[start:]).strip()
            else:
                # stop is excluded here.
                attrs[key] = '\n'.join(lines[start:stop]).strip()

    return TestFunData(**attrs)

def parse_test(lines: list[str]) -> TestFunData:
    indexes = defaultdict(dict)
    last_key = None
    for index, line in enumerate(lines):
        if line.startswith("//!"):
            key = parse_comment(line)
            indexes[key]['start'] = index + 1
            if last_key is not None:
                # end will be excluded by range syntax anyway.
                indexes[last_key]['end'] = index

            last_key = key

    return build_fun_data(indexes, lines)

def parse_test_file(target: str) -> TestData:
    contents = None
    with open(target, 'r') as f:
        contents = ''.join(f.readlines())

    if contents is None:
        raise RuntimeError('Failed to read test file')

    tests = [test.split('\n') for test in contents.split(TEST_MARKER)]
    funs = []
    for test in tests:
        try:
            funs.append(parse_test(test))
        except Exception as e:
            print(f'Skipped invalid test: {test}', e)

    return TestData(funs=funs)

def main():
    target = sys.argv[1]
    out_folder = Path(sys.argv[2])
    test_data = parse_test_file(target)
    out_folder.mkdir(exist_ok=True)
    for fun in test_data.funs:
        with open((out_folder / fun.name).with_suffix('.sierra'), 'w') as f:
            f.write(fun.sierra_code)

if __name__ == '__main__':
    main()
