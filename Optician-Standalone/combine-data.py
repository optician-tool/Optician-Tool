#!/usr/local/bin/python

from __future__ import print_function
from easyprocess import EasyProcess

import os
import csv
from os.path import splitext, join
import subprocess
import sys
import time

TEST_EXT = '.ls'
BASELINE_EXT = '.out'
BASE_FLAGS = []
TIMEOUT_TIME = 600
GENERATE_EXAMPLES_TIMEOUT_TIME = 600000

REPETITION_COUNT = 10

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
    process_output = EasyProcess([prog] + BASE_FLAGS + additional_flags + [join(path, base + TEST_EXT)]).call(timeout=timeout)
    return (process_output.stdout,process_output.stderr)


def gather_data(rootlength, prog, path, base):
    current_data = {"Test":join(path, base).replace("_","-")[rootlength:]}

    def gather_col(flags, run_combiner, col_name, timeout_time, repetition_count):
        print(col_name)
        run_data = []
        timeout = False
        error = False
        for iteration in range(repetition_count):
    	    (datum,err) = gather_datum(prog, path, base,flags,timeout_time)
            if datum == "":
                if err == "":
                    timeout = True
                else:
                    error = True
                break
            else:
	            run_data.append(datum.split(","))
        if error:
            current_data[col_name]=-1
        elif timeout:
	        current_data[col_name]=-1
        else:
            run_data_transpose = transpose(run_data)
            current_data[col_name]=run_combiner(run_data_transpose)

    def ctime_combiner(run_data_transpose):
        computation_time_col = [float(x) for x in run_data_transpose[0]]
        ans = sum(computation_time_col)/len(computation_time_col)
        ans = (int)(ans * 1000)
        return ans

    def exs_reqd_combiner(run_data_transpose):
	    example_number_col = [float(x) for x in run_data_transpose[0]]
	    return "{:.1f}".format(sum(example_number_col)/len(example_number_col))

    def max_exs_reqd_combiner(run_data_transpose):
	    example_number_col = [float(x) for x in run_data_transpose[0]]
	    return int(sum(example_number_col)/len(example_number_col))

    def specsize_combiner(run_data_transpose):
	    example_number_col = [float(x) for x in run_data_transpose[0]]
	    return int(sum(example_number_col)/len(example_number_col))


    gather_col(['-time'],ctime_combiner,"ComputationTime",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-forceexpand','-time'],ctime_combiner,"ForceExpandTime",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-naive_strategy','-time'],ctime_combiner,"NaiveStrategy",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_pqueue','-time'],ctime_combiner,"NaivePQueue",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-no_short_circuit','-time'],ctime_combiner,"NoShortCircuit",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-no_lens_context','-time'],ctime_combiner,"NoLensContext",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-no_short_circuit','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNoSC",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-no_short_circuit','-no_lens_context','-time'],ctime_combiner,"NoLCNoSC",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-naive_expansion_search','-no_lens_context','-time'],ctime_combiner,"NaiveExpansionNoLC",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-use_only_forced_expansions','-no_lens_context','-time'],ctime_combiner,"OnlyForcedExpansionsNoLC",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-naive_expansion_search','-time'],ctime_combiner,"NaiveExpansion",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-use_only_forced_expansions','-time'],ctime_combiner,"OnlyForcedExpansions",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-forceexpand','-naive_expansion_search','-time'],ctime_combiner,"NoUDTypes",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-generatedexamples'],exs_reqd_combiner,"ExamplesRequired",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-max_to_specify'],max_exs_reqd_combiner,"MaxExampleCount",TIMEOUT_TIME,1)
    gather_col(['-spec_size'],max_exs_reqd_combiner,"SpecSize",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-lens_size'],max_exs_reqd_combiner,"LensSize",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-lens_size','-no_lens_context'],max_exs_reqd_combiner,"LensSizeNoLensContext",TIMEOUT_TIME,REPETITION_COUNT)
    gather_col(['-expansions_inferred'],max_exs_reqd_combiner,"ExpansionsInferred",TIMEOUT_TIME,1)
    gather_col(['-expansions_inferred','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsInferredNoLensContext",TIMEOUT_TIME,1)
    gather_col(['-expansions_forced'],max_exs_reqd_combiner,"ExpansionsForced",TIMEOUT_TIME,1)
    gather_col(['-expansions_forced','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsForcedNoLensContext",TIMEOUT_TIME,1)
    gather_col(['-specs_visited'],max_exs_reqd_combiner,"SpecsVisited",TIMEOUT_TIME,1)
    gather_col(['-specs_visited','-naive_expansion_search'],max_exs_reqd_combiner,"SpecsVisitedNaiveExpansion",TIMEOUT_TIME,1)
    gather_col(['-specs_visited','-use_only_forced_expansions'],max_exs_reqd_combiner,"SpecsVisitedOnlyForcedExpansions",TIMEOUT_TIME,1)
    gather_col(['-specs_visited','-no_lens_context'],max_exs_reqd_combiner,"SpecsVisitedNoLensContext",TIMEOUT_TIME,1)
    gather_col(['-expansions_performed'],max_exs_reqd_combiner,"ExpansionsPerformed",TIMEOUT_TIME,1)
    gather_col(['-expansions_performed','-no_lens_context'],max_exs_reqd_combiner,"ExpansionsPerformedNoLensContext",TIMEOUT_TIME,1)
    #gather_col(['-naive_pqueue','-no_lens_context','-time'],ctime_combiner,"NoLensContextNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_pqueue','-no_short_circuit','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNoSCNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_pqueue','-no_short_circuit','-no_lens_context','-time'],ctime_combiner,"NoLCNoSCNPQ",TIMEOUT_TIME,REPETITION_COUNT)
    #gather_col(['-naive_pqueue','-no_inferred_expansions','-no_lens_context','-time'],ctime_combiner,"NoInferenceNoLCNPQ",TIMEOUT_TIME,REPETITION_COUNT)

    return current_data

def specsize_compare(x,y):
    return int(x["SpecSize"])-int(y["SpecSize"])

def sort_data(data):
    return sorted(data,cmp=specsize_compare)

def print_data(data):
    ensure_dir("generated_data/")
    with open("generated_data/data.csv", "wb") as csvfile:
	datawriter = csv.DictWriter(csvfile,fieldnames=data[0].keys())
	datawriter.writeheader()
	datawriter.writerows(data)

def print_usage(args):
    print("Usage: {0} <file1> <file2> <file3>".format(args[0]))

def transform_data(path, base, run_data):
    current_data = {"Test":join(path, base + TEST_EXT).replace("_","-")[6:]}
    run_data_transpose = transpose(run_data)
    for index in range(len(run_data_transpose)/2):
	col_name = run_data_transpose[index][0]
	col_data = run_data_transpose[index+1]
        if "" in col_data:
	    current_data[col_name]=-1
        else:
            col = [float(x) for x in col_data]
            current_data[col_name] = str(sum(col)/len(col))
    return current_data

def retrieve_csv(filename):
    csv_rows = []
    with open(filename, 'rb') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            csv_rows.append(row)
    return csv_rows

def main(args):
    if len(args) == 4:
        prog1_path = args[1]
        prog2_path = args[2]
        prog3_path = args[3]
        ensure_dir("data/generated-data/")
        csv1 = retrieve_csv(prog1_path)
        csv2 = retrieve_csv(prog2_path)
        csv3 = retrieve_csv(prog3_path)
        data_keyed_by_test = {r["Test"]: r for r in csv1}
        for row in csv2:
            relevant_data = data_keyed_by_test[row["Test"]]
            for key, value in row.items():
                relevant_data[key] = value
        for row in csv3:
            relevant_data = data_keyed_by_test[row["Test"]]
            for key, value in row.items():
                relevant_data[key] = value
        print(data_keyed_by_test)
        with open("data/generated-data/data.csv", "wb") as csvfile:
            fieldnames = data_keyed_by_test[data_keyed_by_test.keys()[0]].keys()
            writer = csv.DictWriter(csvfile, fieldnames=fieldnames)

            writer.writeheader()
            writer.writerows(list(data_keyed_by_test.values()))
    else:
        print_usage(args)

if __name__ == '__main__':
    main(sys.argv)
