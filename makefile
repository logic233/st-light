COQC= coqc \
-R "./velus/src" Velus \
-R "./velus/CompCert/lib" compcert.lib \
-R "./velus/CompCert/common" compcert.common \
-R "./velus/CompCert/backend" compcert.backend \
-R "./velus/CompCert/cfrontend" compcert.cfrontend \
-R "./velus/CompCert/driver" compcert.driver \
-R "./velus/CompCert/flocq" compcert.flocq \
-R "./velus/CompCert/exportclight" compcert.exportclight \
-R "./velus/CompCert/cparser" compcert.cparser \
-R "./velus/CompCert/x86_64" compcert.x86_64 \
-R "./velus/CompCert/x86" compcert.x86 \
-R "./velus/CompCert/arm" compcert.arm \
-R "./src" ST \


ST = MyCommon ST_Operators ST_Syntax ST_Semantics ST_Typing ST ST_Interface Cgen ST_Invariant CgenProperties ST_Correctness

define get_files_before
$(patsubst %.v,%.vo,$(filter-out $1,$(wordlist 1, $(words $(filter-out %$1, $(ST))), $(ST))))
endef

proof :  $(ST:.v=.vo)

%.vo: $(call get_files_before,%.v) %.v
	@whereis coqc
	@echo "COQC $*.v"
	@echo "FILES_BEFORE $(call get_files_before,(%.v))"
	@$(COQC) ./src/$*.v




TOTAL_FILES := $(words $(ST))
FILE_NUMBER := 0
.PHONY: all
all:
	@whereis coqc
	@touch ./src/1.vo
	@rm ./src/*.vo
	@for file in $(ST); do \
		FILE_NUMBER=$$((FILE_NUMBER+1)); \
		echo "\e[34mCompiling file $$FILE_NUMBER of $(TOTAL_FILES): $$file\e[0m"; \
		$(COQC)  ./src/$$file.v; \
		if [ -f "./src/$$file.vo" ]; then \
        	echo "\e[34m$$file prove successful\n\e[0m"; \
    	fi; \
	done