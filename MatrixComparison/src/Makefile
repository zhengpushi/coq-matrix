# ===================================================================
# MFMM: Multiple Formal Matrix Models in Coq
# E-mail: zhengpushi@nuaa.edu.cn
# Copyright FEM-NUAA.CN 2022
# ===================================================================

COQMAKEFILE ?= Makefile.coq

all: $(COQMAKEFILE)
	$(MAKE) -f $^ $@

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall

cleanall: $(COQMAKEFILE)
	$(MAKE) -f $^ cleanall
	$(RM) $^ $^.conf

.PHONY: all clean cleanall
