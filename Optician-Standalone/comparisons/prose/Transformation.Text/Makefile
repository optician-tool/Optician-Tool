XB := xbuild

GENERATE_DATA := python generate-data.py

.PHONY: all clean

all:
	$(XB) /target:build

clean:
	$(XB) /target:clean

generate-data: all
	$(GENERATE_DATA) bin/Debug/Transformation.Text.exe ../../io_specs/
