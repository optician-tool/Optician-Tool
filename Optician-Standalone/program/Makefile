CFLAGS := -w,@A,-w,-4,-w,-44,-w,-48,-w,-26,-w,-41,-w,-42,-w,-39,-w,-32
OCBFLAGS := -cflags $(CFLAGS)
OCB := ocamlbuild $(OCBFLAGS)

.PHONY: all debug clean top profile unittest

all: cmdline.native
debug: all cmdline.cma

%.cma: .FORCE
	$(OCB) $@

%.cmxa: .FORCE
	$(OCB) $@

%.native: .FORCE
	$(OCB) $@

%.p.native: .FORCE
	$(OCB) $@

%.byte: .FORCE
	$(OCB) $@

.FORCE:

clean:
	$(OCB) -clean

top: cmdline.cma
	utop

GENERATE_DATA := python generate-data.py

GENERATE_IO_SPECS := python generate_IO_specs.py

GENERATE_EXTRACTION_SPECS := python generate_extraction_specs.py

generate-data: cmdline.native
	$(GENERATE_DATA) ./cmdline.native example-inputs/

generate-io-specs: cmdline.native
	$(GENERATE_IO_SPECS) ./cmdline.native example-inputs/ 10100

generate-extraction-specs: cmdline.native
	$(GENERATE_EXTRACTION_SPECS) ./cmdline.native example-inputs/ 10100

profile: cmdline.p.native
	instruments -t "/Applications/Xcode.app/Contents/Applications/Instruments.app/Contents/Resources/templates/Time Profiler.tracetemplate" cmdline.p.native

unittest: unittests.native
	./unittests.native
