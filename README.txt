There are two ways that Optician can be run.  These reflect the two
subfolders in this repository: Optician-Standalone and Optician-Integrated.

-------------------------
Optician-Standalone
-------------------------
In the standalone mode, Optician takes in a custom file format (*.ls) which 
can specify regular expressions, synthesis tasks, and unit tests on the
lenses.

When run on these files, Optician outputs a fully formed Boomerang program 
to stdout.  It was on this tool that data was collected for the paper. This
directory also includes tests, and scripts to run tests, which allows for 
reproduction of the results.


-------------------------
Optician-Integrated
-------------------------
In the integrated mode, Optician has been integrated into Boomerang.
Optician-Integrated is a modified Boomerang, which allows for synthesis
tasks to be written in place of lenses.  We did not run the tests on this
version of Optician.  Credit for Optician-Integrated goes to Solomon Maina.
