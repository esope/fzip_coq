.PHONY: all clean doc doc-htmlized xcodec ocamldot

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

doc: xcodec ocamldot
	mkdir -p doc
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc;\
	ln -f -s ../$(i)/doc/html doc/$(i);)

xcodec:
	make -C xcodec opt

ocamldot:
	make -C ocamldot