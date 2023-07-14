.PHONY: all install coq clean clean_coq

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

install: coq

clean_coq: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

clean: clean_coq
	$(RM) Makefile.coq
	$(RM) Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@
