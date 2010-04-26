############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#    check         - runs coqchk on compiled files
#
############################################################################

## encoding/decoding UTF8 due to a bug in coqdoc
XCODEC = ../xcodec/xcodec
XENCODE = $(XCODEC) encode
XDECODE = $(XCODEC) decode

## path to ocamldot to draw the dependency graph
OCAMLDOT = ../ocamldot/ocamldot -urls

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc -dont-load-proofs
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

.PHONY: all clean coq dist doc documentation force check view_deps view_fulldeps
.SUFFIXES: .v .vo .dot

all: coq

coq: $(VOFILES)

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES) deps.dot
	mkdir -p $(DOCDIR)
	cp *.glob $(DOCDIR)
	$(foreach i, $(VFILES), $(XENCODE) < $(i) > $(DOCDIR)/$(i); )
	$(foreach i, $(FILES), $(COQDOC) -o $(DOCDIR)/tmp_$(i).html $(DOCDIR)/$(i).v; )
	rm -f $(foreach i, $(VFILES), $(DOCDIR)/$(i)) $(DOCDIR)/*.glob
	$(foreach i, $(FILES), $(XDECODE) < $(DOCDIR)/tmp_$(i).html > $(DOCDIR)/$(i).html && rm $(DOCDIR)/tmp_$(i).html; )
	dot -Tsvg -o$(DOCDIR)/index.svg deps.dot
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o *.dot
	rm -rf $(DOCDIR)

force:
	touch *.v
	+make

check:	coq
	coqchk -m -o $(INCFLAGS) $(FILES)

############################################################################

%.vo: %.v
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

deps.dot: .depend
	$(OCAMLDOT) .depend > deps.dot

view_deps: deps.dot
	dot -Txlib deps.dot &

fulldeps.dot: .depend
	$(OCAMLDOT) -fullgraph .depend > fulldeps.dot

view_fulldeps: fulldeps.dot
	dot -Txlib fulldeps.dot &
############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend
