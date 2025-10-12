COQC= /home/logic/.opam/4.07.1/bin/coqc \
-R "/home/logic/project/ST/src" Velus \
-R "/home/logic/project/ST/ST" ST \
-R "/home/logic/project/ST/CompCert/lib" compcert.lib \
-R "/home/logic/project/ST/CompCert/common" compcert.common \
-R "/home/logic/project/ST/CompCert/backend" compcert.backend \
-R "/home/logic/project/ST/CompCert/cfrontend" compcert.cfrontend \
-R "/home/logic/project/ST/CompCert/driver" compcert.driver \
-R "/home/logic/project/ST/CompCert/flocq" compcert.flocq \
-R "/home/logic/project/ST/CompCert/exportclight" compcert.exportclight \
-R "/home/logic/project/ST/CompCert/cparser" compcert.cparser \
-R "/home/logic/project/ST/CompCert/x86_64" compcert.x86_64 \
-R "/home/logic/project/ST/CompCert/x86" compcert.x86 \
-R "/home/logic/project/ST/CompCert/arm" compcert.arm \

ST = MyCommon.v ST_Operators.v ST_Syntax.v ST_Semantics.v ST_Typing.v ST.v ST_Interface.v Cgen.v ST_Invariant.v CgenProperties.v

define get_files_before
$(patsubst %.v,%.vo,$(filter-out $1,$(wordlist 1, $(words $(filter-out %$1, $(ST))), $(ST))))
endef

proof :  $(ST:.v=.vo)

%.vo: $(call get_files_before,%.v) %.v
	@echo "COQC $*.v"
	@echo "FILES_BEFORE $(call get_files_before,(%.v))"
	
	@$(COQC) $*.v




TOTAL_FILES := $(words $(ST))
FILE_NUMBER := 0
.PHONY: all
all:
	@for file in $(ST); do \
		FILE_NUMBER=$$((FILE_NUMBER+1)); \
		echo "\e[34mCompiling file $$FILE_NUMBER of $(TOTAL_FILES): $$file\e[0m"; \
		$(COQC)  $$file; \
	done