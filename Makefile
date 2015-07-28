all: theories examples

theories: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

install:
	$(MAKE) -f Makefile.coq install

examples: theories
	$(MAKE) -C examples

clean:
	$(MAKE) -f Makefile.coq clean

uninstall:
	$(MAKE) -C theories uninstall


dist:
	@ git archive --prefix coq-ext-lib/ HEAD -o $(PROJECT_NAME).tgz

.dir-locals.el: tools/dir-locals.el
	@ sed s,PWD,$(shell pwd -P),g tools/dir-locals.el > .dir-locals.el

.PHONY: all clean dist theories examples
