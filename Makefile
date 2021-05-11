.PHONY: all coq clean clean_coq

all: coq

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean_coq: Makefile.coq
	$(MAKE) -f Makefile.coq clean

clean: clean_coq
	$(RM) Makefile.coq
	$(RM) Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

