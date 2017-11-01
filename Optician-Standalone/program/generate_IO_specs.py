#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
from os.path import splitext, join
import subprocess
import sys
import time

TEST_EXT = '.ls'
BASELINE_EXT = '.out'
TSV_EXT = '.tsv'
BASE_FLAGS = ['-generate_io_spec']
TIMEOUT_TIME = 6000
REPETITION_COUNT = 2
BASE_TSV_DIR = 'generated_io_specs/'

def ensure_dir(f):
    if not os.path.exists(f):
        os.makedirs(f)

def find_tests_and_ensure_output_dirs(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
        ensure_dir(BASE_TSV_DIR + path)
    return tests

def gather_tsv(rootlength, prog, path, base, num_examples):
    process_output = EasyProcess([prog] + BASE_FLAGS + [str(num_examples)] + [join(path, base + TEST_EXT)]).call(timeout=TIMEOUT_TIME)
    if (process_output.stdout == "" or process_output.stderr != "" or process_output.return_code != 0):
        raise Exception("emptystdout")
    return process_output.stdout

def write_tsv(tsv, path, base):
    with open(join(BASE_TSV_DIR+path, base + TSV_EXT),'w') as tsvfile:
        tsvfile.write(tsv)

def print_usage(args):
    print("Usage: {0} <prog> <testdir>".format(args[0]))

def transform_data(path, base, run_data):
    current_data = {"Test":join(path, base + TEST_EXT).replace("_","-")[6:]}
    run_data_transpose = transpose(run_data)
    for index in range(len(run_data_transpose)/2):
	col_name = run_data_transpose[index][0]
	col_data = run_data_transpose[index+1]
        if "" in col_data:
	    current_data[col_name]="Timeout"
        else:
            col = [float(x) for x in col_data]
            current_data[col_name] = str(sum(col)/len(col))
    return current_data

def main(args):
    if len(args) == 4:
        prog = args[1]
        path = args[2]
        num_examples = args[3]
        rootlength = len(path)
        data = []
        base_tsv_dir = ensure_dir('generated_io_specs/')
        if not os.path.exists(prog):
            print_usage(args)
        elif os.path.exists(path) and os.path.isdir(path):
            for path, base in find_tests_and_ensure_output_dirs(path):
                print(join(path, base + TEST_EXT).replace("_","-")[rootlength:])
                current_tsv = gather_tsv(rootlength,prog, path, base,num_examples)
                write_tsv(current_tsv, path, base)
        else:
            print_usage(args)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
