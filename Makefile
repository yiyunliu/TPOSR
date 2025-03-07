SYNTAX_FILE=theories/Autosubst2/syntax.v
COQMAKEFILE=CoqMakefile

theories: $(COQMAKEFILE)
	$(MAKE) -f $^

$(COQMAKEFILE) : $(SYNTAX_FILE)
	$(COQBIN)coq_makefile -f _CoqProject -o $(COQMAKEFILE)

install: $(COQMAKEFILE)
	$(MAKE) -f $^ install

uninstall: $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) uninstall

$(SYNTAX_FILE) : syntax.sig
	autosubst -f -v ge813 -s ucoq -o $(SYNTAX_FILE) syntax.sig

.PHONY: clean
clean:
	test ! -f $(COQMAKEFILE) || ( $(MAKE) -f $(COQMAKEFILE) clean && rm $(COQMAKEFILE) )
	rm -f $(SYNTAX_FILE)
