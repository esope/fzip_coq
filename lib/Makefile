############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
#  Other targets (intended to be used by the developers of this library):
#    gens          - builds generated .v files on demand
#    dist          - builds a zip file for distribution
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc --utf8 --light --quiet --noindex --html

## Include directories, one per line.

INCDIRS = \
	. \

## Directory where generated HTML documentation should go.

DOCDIR = doc/html

## List of other files that should be compiled.

FILES = \
	Rel \

## Lists calculated from the above.

VFILES = \
	$(foreach i, $(FILES), $(i).v) \

VOFILES  = $(VFILES:.v=.vo)

INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation force
.SUFFIXES: .v .vo

all: coq

coq: $(VOFILES)

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

force:
	touch *.v
	+make

check:	coq
	coqchk $(INCFLAGS) $(FILES)

############################################################################

%.vo: %.v
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
