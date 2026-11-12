# Build proofs:  make          (needs: eval $(opam env --switch=wasmcert);
#                ../symexec and ../determinism must be built first: make -C ../symexec; make -C ../determinism)
# Build wasm:    make decoder.wasm   (prints the bytes from the Rocq term)
# Everything:    ./check.sh
# The pure layer is the REAL build in ../../pure-rocq (logical path Utf8).
all: Makefile.coq
	$(MAKE) -f Makefile.coq -j 2 all

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

decoder.wasm: all EmitHex.v
	rocq c -w -default-output-directory -Q . Decoder EmitHex.v
	node -e 'const fs=require("fs");const t=fs.readFileSync("decoder_hex.out","utf8");const h=t.match(/"([0-9a-f]*)"/)[1];fs.writeFileSync("decoder.wasm",Buffer.from(h,"hex"))'

# clean removes build products only.  decoder_hex.out and decoder.wasm are
# tracked files (check.sh regenerates both and compares them with the
# tracked copies), so clean leaves them alone.
clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf EmitHex.vo EmitHex.glob
