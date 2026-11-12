# Build:  make   (needs: eval $(opam env --switch=wasmcert))
# Builds against the installed coq-wasm (WasmCert-Coq 2.2.1) only.
# ../decoder builds this directory first (its check.sh runs `make` here).
all: Makefile.coq
	$(MAKE) -f Makefile.coq -j 2 all

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf .Makefile.coq.d
