############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc --utf8 --light --quiet --noindex --html

## Paths for ott and lngen.

OTT = /opt/bin/ott
LNGEN = /opt/bin/lngen

## Flags to lngen.  Mainly for --coq-admitted.

LNGENFLAGS = --coq-loadpath=../metatheory ## --coq-admitted

## Include directories, one per line.

INCDIRS = \
	. \
	../metatheory \

## Directory where generated HTML documentation should go.

DOCDIR = doc/html

## List of files that are processed by LNgen.

LNGEN_FILES = \
	FzipCore \

## List of other files that should be compiled.

FILES = \
#	FzipCore_init \
#	FzipCore_soundness \
#	FzipCore_dec \
#	FzipCore_sim \
#	FzipCore_normalization \

## Lists calculated from the above.

VFILES = \
	$(foreach i, $(LNGEN_FILES), $(i)_inf.v $(i)_ott.v) \
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

doc-htmlized:
	+make documentation-htmlized

documentation-htmlized: $(DOCDIR) $(VOFILES)
	mkdir -p doc/htmlized
	emacs --kill --eval '(htmlize-many-files (file-expand-wildcards "*.v") "doc/htmlized")'

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)
	rm -rf doc/htmlized

force:
	touch *.ott
	+make

check:	coq
	coqchk $(INCFLAGS) $(FILES)

############################################################################

%.vo: %.v
	$(COQC) -q $(INCFLAGS) $<

%_ott.v: %.ott
	$(OTT) -coq $*_ott.v $*.ott
	for i in `ls $*_ott.patch.?? | sort`; do patch $*_ott.v $$i; done

%_inf.v: %_ott.v $(LNGEN)
	$(LNGEN) $(LNGENFLAGS) --coq $*_inf.v --coq-ott $*_ott --coq-loadpath metatheory $*.ott

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
