TARGET=xcodec

.PHONY: all clean opt byte

all: byte opt

byte: xcodec.ml
	ocamlbuild xcodec.byte
	ln -s _build/xcodec.byte $(TARGET)

opt: xcodec.ml
	ocamlbuild xcodec.native
	ln -s _build/xcodec.native $(TARGET)

clean:
	rm $(TARGET)
	ocamlbuild -clean
