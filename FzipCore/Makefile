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

## Paths for ott and lngen.

OTT = /opt/bin/ott
LNGEN = /opt/bin/lngen

## Flags to lngen.  Mainly for --coq-admitted.

LNGENFLAGS = --coq-loadpath=../metatheory # --coq-admitted

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
	FzipCore_init \
	FzipCore_weakenU \
	FzipCore_val \
	FzipCore_red \
	FzipCore_red_close \
	FzipCore_zip \
	FzipCore_pure \
	FzipCore_env_typ \
	FzipCore_typeq \
	FzipCore_term \
	FzipCore_soundness \
	FzipCore_renameT \
	FzipCore_examples \
#	FzipCore_dec \
#	FzipCore_sim \
#	FzipCore_normalization \

## Lists calculated from the above.

VFILESBASE = \
	$(foreach i, $(LNGEN_FILES), $(i)_inf $(i)_ott) \
	$(FILES) \

VFILES = $(foreach i, $(VFILESBASE), $(i).v) \

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
	$(foreach i, $(VFILESBASE), $(COQDOC) -o $(DOCDIR)/tmp_$(i).html $(DOCDIR)/$(i).v; )
	rm -f $(foreach i, $(VFILES), $(DOCDIR)/$(i)) $(DOCDIR)/*.glob
	$(foreach i, $(VFILESBASE), $(XDECODE) < $(DOCDIR)/tmp_$(i).html > $(DOCDIR)/$(i).html && rm $(DOCDIR)/tmp_$(i).html; )
	ln -sf ../../../doc/metatheory/Metatheory.html $(DOCDIR)
	ln -sf ../../../doc/metatheory/LibLNgen.html $(DOCDIR)
	dot -Tsvg -o$(DOCDIR)/index.svg deps.dot
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o *.dot
	rm -rf $(DOCDIR)

force:
	touch *.ott
	+make

check:	coq
	coqchk -m -o $(INCFLAGS) $(FILES)

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
