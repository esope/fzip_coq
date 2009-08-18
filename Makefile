.PHONY: all clean

DIRS = \
	metatheory \
	PLC \
	STLC \
	F \
	FzipCore \

all:
	$(foreach i, $(DIRS), $(MAKE) -C $(i) ;)

clean:
	$(foreach i, $(DIRS), $(MAKE) -C $(i) clean;)

doc:
	$(foreach i, $(DIRS), $(MAKE) -C $(i) doc;)
