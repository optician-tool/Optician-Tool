Synthesizing Bijective Lenses Artifact Evaluation
-------------------------------------------------

Makefile
 - make regenerate-specs creates specifications for Flash Fill and FlashExtract
 - make regenerate-data must be ran after specifications are made, and generates data and graphs

program contains the Optician program

comparisons contains code for testing Flash Fill and FlashExtract

data transforms the generated data

combine-data.py aggregates the data from multiple tests into a single CSV file
