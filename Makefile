.PHONY: all clean doc doc-htmlized

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
	$(foreach i, $(DIRS), $(MAKE) -C $(i) clean;)
	rm -rf doc

doc:
	mkdir -p doc
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc;\
	ln -f -s ../$(i)/doc/html doc/$(i);)

doc-htmlized: doc
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc-htmlized;\
	ln -f -s ../htmlized doc/$(i)/htmlized;)
