# Build proofs:  make          (needs: eval $(opam env --switch=wasmcert))
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

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf decoder_hex.out EmitHex.vo EmitHex.glob Assumptions.vo Assumptions.glob
