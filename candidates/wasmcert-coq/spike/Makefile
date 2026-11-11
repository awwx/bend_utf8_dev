# Build proofs:   make         (needs: eval $(opam env --switch=wasmcert))
# Build wasm:     make spike.wasm
# Run JS tests:   make test
all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	rocq makefile -f _CoqProject -o Makefile.coq

spike.wasm: all EmitHex.v
	rocq c -w -default-output-directory -Q . Spike EmitHex.v
	node -e 'const fs=require("fs");const t=fs.readFileSync("spike_hex.out","utf8");const h=t.match(/"([0-9a-f]*)"/)[1];fs.writeFileSync("spike.wasm",Buffer.from(h,"hex"))'

test: spike.wasm
	node test.mjs

clean:
	-$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf spike_hex.out spike.wasm EmitHex.vo EmitHex.glob

# Independent cross-checks of the printed bytes (not part of the proof):
# the official OCaml reference interpreter's disassembly, and the
# extracted WasmCert interpreter running the LAWS.bend examples.
crosscheck: spike.wasm
	wasm -d spike.wasm -o spike.roundtrip.wat && cat spike.roundtrip.wat
	for cp in 0 55295 55296 56320 57343 57344; do \
	  printf '%s -> ' $$cp; wasm_coq_interpreter spike.wasm -r is_surrogate_code_point -a "i32.const $$cp" --vr | sed 's/\x1b\[[0-9;]*m//g'; done
