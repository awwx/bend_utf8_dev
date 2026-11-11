# Build: make   (uses rocq makefile; Utf8Check.v takes ~10 min: exhaustive vm_compute)
SPEC := ../spec-rocq/Utf8Laws.v

all: spec-copy CoqMakefile
	$(MAKE) -f CoqMakefile -j2

spec-copy:
	@cmp -s $(SPEC) Utf8Laws.v || cp -f $(SPEC) Utf8Laws.v
	@cmp $(SPEC) Utf8Laws.v && echo "Utf8Laws.v is byte-identical to $(SPEC)"

CoqMakefile: _CoqProject
	rocq makefile -f _CoqProject -o CoqMakefile

clean:
	-$(MAKE) -f CoqMakefile clean
	rm -f CoqMakefile CoqMakefile.conf

.PHONY: all spec-copy clean
