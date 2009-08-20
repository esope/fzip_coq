.PHONY: all clean opt byte

all: byte opt

byte: xcodec.ml
	ocamlbuild xcodec.byte

opt: xcodec.ml
	ocamlbuild xcodec.native

clean:
	ocamlbuild -clean
