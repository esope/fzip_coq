.PHONY: all clean opt byte

all: byte opt

byte: xcodec.ml
	ocamlbuild -tag camlp4o xcodec.byte

opt: xcodec.ml
	ocamlbuild -tag camlp4o xcodec.native

clean:
	ocamlbuild -clean
