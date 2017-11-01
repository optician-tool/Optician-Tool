.PHONY: all clean

all:
	make -C Extraction.Text && make -C Transformation.Text

clean:
	make -C Extraction.Text clean && make -C Transformation.Text clean

generate-data:
	make -C Extraction.Text generate-data && make -C Transformation.Text generate-data
