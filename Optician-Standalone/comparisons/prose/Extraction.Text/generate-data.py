#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time

TEST_EXT = '.tsv'
BASELINE_EXT = '.out'
BASE_FLAGS = []
TIMEOUT_TIME = 600

def ensure_dir(f):
    d = os.path.dirname(f)
    if not os.path.exists(d):
        os.makedirs(d)

def transpose(matrix):
    return zip(*matrix)

def find_tests(root):
    tests = []
    for path, dirs, files in os.walk(root):
        files = [(f[0], f[1]) for f in [splitext(f) for f in files]]
        tests.extend([(path, f[0]) for f in files if f[1] == TEST_EXT])
    return tests

def gather_datum(prog, path, base, additional_flags, timeout):
    print(["mono", prog] + BASE_FLAGS + additional_flags + [join(path, base + TEST_EXT)])
    process_output = EasyProcess(["mono", prog] + BASE_FLAGS + additional_flags + [join(path, base + TEST_EXT)]).call(timeout=timeout)
    return (process_output.stdout,process_output.stderr)


def gather_data(rootlength, prog, path, base):
    current_data = {"Test":join(path, base).replace("_","-")[rootlength:]}
    timeout = False
    error = False
    num_inputs = 0
    result = "IncorrectResponse"
    while (result == "IncorrectResponse"):
        num_inputs=int(float(num_inputs)*1.5+1.0)
        print(num_inputs)
        (datum,err) = gather_datum(prog, path, base, [str(num_inputs)],TIMEOUT_TIME)
        if datum == "":
            if err == "":
	            result="-1"
            else:
                print(err)
                result="-1"
        elif (num_inputs > 100000):
            result="TooLargeSpec"
        else:
	        result=datum
    print(result)
    if result == "NothingLearned" or result == "TooLargeSpec":
        result = -1
    current_data["FlashExtract"]=result
    current_data["ExsTaken"]=num_inputs
    return current_data

def print_data(data):
    ensure_dir("generated_data/")
    with open("generated_data/data.csv", "wb") as csvfile:
	datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
	datawriter.writeheader()
	datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <prog> <test>".format(args[0]))

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

def load_data():
    try:
        with open("generated_data/data.csv", "r") as csvfile:
            datareader = csv.DictReader(csvfile)
            return [row for row in datareader]
    except:
        return []

def main(args):
    if len(args) == 3:
        prog = args[1]
        path = args[2]
        rootlength = len(path)
        data = load_data()
        if not os.path.exists(prog):
            print_usage(args)
        elif os.path.exists(path) and os.path.isdir(path):
            for path, base in find_tests(path):
                test_name = join(path, base).replace("_","-")[rootlength:]
                print(test_name)
                if (not (any(row["Test"] == test_name for row in data))):
                    current_data = gather_data(rootlength,prog, path, base)
                    data.append(current_data)
                else:
                    print("data already retrieved")
                print_data(data)
        else:
            print_usage(args)
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
