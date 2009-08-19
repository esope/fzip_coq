.PHONY: all clean doc doc-htmlized xcodec

DIRS = \
	lib \
	metatheory \
	PLC \
	STLC \
	F \
	FzipCore \

all: Makefile
	$(foreach i, $(DIRS), $(MAKE) -C $(i) ;)

clean:
	make -C xcodec clean
	$(foreach i, $(DIRS), $(MAKE) -C $(i) clean;)
	rm -rf doc

doc: xcodec
	mkdir -p doc
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc;\
	ln -f -s ../$(i)/doc/html doc/$(i);)

doc-htmlized: doc
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc-htmlized;\
	ln -f -s ../htmlized doc/$(i)/htmlized;)

xcodec:
	make -C xcodec byte
