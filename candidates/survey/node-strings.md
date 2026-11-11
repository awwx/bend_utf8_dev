# Wasm -> JS string mechanisms in Node v26.13.0 (V8 14.6)

Experiments in scratchpad `.../scratchpad/node-strings/` (t12.mjs, t3.mjs, t4.mjs, m*.wat). Target text: "Aé€\u{1F600}".
Installed (npm, local to that dir only): `wabt@1.0.39`, `binaryen@132.0.0`. Nothing global.

## Results

| # | Mechanism | Flags | Wasm features | Result |
|---|-----------|-------|---------------|--------|
| 1a | UTF-16 units in memory, `String.fromCharCode(...u16)` | none | linear memory only | works; apply/spread fails ~1e6 args (RangeError/stack overflow; 1e5 ok) so chunk |
| 1b | same, `new TextDecoder('utf-16le').decode(u16)` | none | linear memory only | works, no arg limit; lone surrogate becomes U+FFFD (fromCharCode keeps it) |
| 2 | u32 code points, `String.fromCodePoint(...u32)` | none | linear memory only | works; >0x10FFFF throws RangeError; lone surrogates pass through; same arg limit |
| 3a | `wasm:js-string` `fromCharCodeArray` over `(array (mut i16))` | none (opt `{builtins:['js-string']}` required at instantiate) | GC, ref types, imported builtins | works, export returns string directly |
| 3b | `fromCharCode`/`fromCodePoint` + `concat` | same | imported builtins only (no GC) | works |
| 3c | js-string imports without `builtins` option | none | - | fails with plain `{}` imports, but works if JS supplies polyfill functions as imports (so a fallback is possible) |
| 4 | stringref (`string.const`, `stringref` result) | `--experimental-wasm-stringref` | stringref | works only with flag; without: "invalid value type 'stringref'". Not in standard (Phase 1). Also flag `--experimental-wasm-imported-strings-utf8` exists (default off) |
| 5 | multi-value export `(result i32 externref)` | none | multi-value (wasm 2.0 core) | JS receives a plain Array `[7, 'Aé€😀']`; with js-string builtin the externref slot is already a JS string. Null externref -> `null` |

## Wrapper code required

1. Memory UTF-16 (little-endian only; typed-array view uses host endianness, Node/all realistic targets are LE; BE host would need decoding with 'utf-16be'. Alignment: Uint16Array byteOffset must be even):
```js
const [p, n] = ex.run();                       // ptr, length in code units
const s = new TextDecoder('utf-16le').decode(new Uint16Array(ex.mem.buffer, p, n));
// or chunked: for (i...) out += String.fromCharCode.apply(null, u.subarray(i, i+8192))
```
Memory view must be recreated after any memory.grow (buffer detaches).

2. Code points (u32 aligned):
```js
String.fromCodePoint(...new Uint32Array(ex.mem.buffer, p, n))  // chunk for large n
```

3. Builtins: wrapper is only
```js
const {instance} = await WebAssembly.instantiate(bytes, {}, {builtins:['js-string']});
const [state, str] = instance.exports.decode_buffer(...);
```
Caveat: the `(ref null (array (mut i16)))` argument must be built inside Wasm (JS cannot make GC arrays), which is fine.

4. stringref: `node --experimental-wasm-stringref`; wrapper would be zero logic but unusable without flag and not standard.

5. Multi-value: nothing to do; destructure the returned array.

## Minimal modules

### m1.wat (UTF-16 in memory)
```wat
(module
  (memory (export "mem") 1)
  (data (i32.const 0) "\41\00\e9\00\ac\20\3d\d8\00\de")
  (func (export "run") (result i32 i32) (i32.const 0) (i32.const 5)))
```
Assembled with wabt `parseWat(name, src, {multi_value:true})`.

### m2.wat (code points)
```wat
(module
  (memory (export "mem") 1)
  (data (i32.const 0) "\41\00\00\00\e9\00\00\00\ac\20\00\00\00\f6\01\00")
  (func (export "run") (result i32 i32) (i32.const 0) (i32.const 4)))
```

### m3.wat (js-string builtins, assembled with binaryen; enable features GC|ReferenceTypes|Multivalue|BulkMemory; do NOT use Features.All, it emitted a binary V8 rejected: "unknown import kind 0x7f")
```wat
(module
  (type $arr (array (mut i16)))
  (type $fa (func (param (ref null $arr) i32 i32) (result (ref extern))))
  (type $fc (func (param i32) (result (ref extern))))
  (type $cat (func (param externref externref) (result (ref extern))))
  (import "wasm:js-string" "fromCharCodeArray" (func $fca (type $fa)))
  (import "wasm:js-string" "fromCharCode" (func $fcc (type $fc)))
  (import "wasm:js-string" "fromCodePoint" (func $fcp (type $fc)))
  (import "wasm:js-string" "concat" (func $cat (type $cat)))
  (func (export "viaArray") (result i32 externref)
    (i32.const 7)
    (call $fca (array.new_fixed $arr 5 (i32.const 0x41) (i32.const 0xe9) (i32.const 0x20ac) (i32.const 0xd83d) (i32.const 0xde00)) (i32.const 0) (i32.const 5)))
  (func (export "viaConcat") (result externref)
    (call $cat (call $cat (call $fcc (i32.const 0x41)) (call $fcc (i32.const 0xe9)))
      (call $cat (call $fcc (i32.const 0x20ac)) (call $fcp (i32.const 0x1f600))))))
```
Outputs: viaArray -> `[7,'Aé€😀']`; viaConcat -> the string; a pair built from two fromCharCode of D83D, DE00 concatenates into a proper pair.

### m4.wat (stringref, flag needed)
```wat
(module (func (export "s") (result stringref)
  (string.const "A\c3\a9\e2\82\ac\f0\9f\98\80")))
```
Note stringref `string.const` takes UTF-8 text in binaryen.

### m5.wat (multi-value)
```wat
(module (func (export "two") (result i32 externref) (i32.const 7) (ref.null extern)))
```
-> `[7, null]`.

## Web check (standardization)
- JS String Builtins: listed in WebAssembly/proposals finished-proposals.md (phase 4; champion Ryan Hunt; spec version 3.0; core + js-api; WG notes 2025-07-23). Part of Wasm 3.0 JS API. Builtins: cast, test, fromCharCodeArray, intoCharCodeArray, fromCharCode, fromCodePoint, charCodeAt, codePointAt, length, concat, substring, equals, compare. UTF-8 text-decoder/encoder are a future extension (matches V8's off-by-default imported-strings-utf8 flag).
- Stringref: Phase 1 (champion Andy Wingo), not finished; effectively stalled/experimental, superseded in practice by js-string builtins. Engine support beyond V8's flag was not checked.
- Not verified from sources: other browsers' shipping status.
