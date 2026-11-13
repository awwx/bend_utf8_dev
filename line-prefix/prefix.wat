(module
  ;; Streaming LF-only line prefixer. The bridge passes complete-character
  ;; strings of at most 4096 UTF-16 code units to data(text, length).
  ;; Empty input emits nothing; a final LF never produces a dangling prefix.
  ;;
  ;; Compile with { builtins: ['js-string'] }. Both conversion imports below
  ;; are native engine builtins, not JavaScript conversion loops.

  ;; The string builtins require a mutable i16 array in its own recursion group.
  (type $units (array (mut i16)))
  ;; Node adaptation: handles 0/1 identify input/output; callback tokens 1/2
  ;; designate the exported data/close functions. Calls are nonreentrant.
  (import "bridge" "create_input" (func $create_input (result i32)))
  (import "bridge" "create_output" (func $create_output (result i32)))
  (import "bridge" "on_data" (func $on_data (param i32 i32)))
  (import "bridge" "on_close" (func $on_close (param i32 i32)))
  (import "bridge" "write" (func $write (param i32 externref)))
  (import "bridge" "end" (func $end (param i32)))
  ;; into copies the whole string at an array offset and returns its unit count.
  ;; from snapshots [start, stop) as an immutable JavaScript string.
  (import "wasm:js-string" "intoCharCodeArray"
    (func $into (param externref (ref null $units) i32) (result i32)))
  (import "wasm:js-string" "fromCharCodeArray"
    (func $from (param (ref null $units) i32 i32) (result (ref extern))))
  ;; Persistent state: prefix the next unit exactly when it begins a line.
  ;; This flag survives chunk boundaries, including a chunk ending in LF.
  (global $line (mut i32) (i32.const 1))
  (global $input (mut i32) (i32.const 0))
  (global $output (mut i32) (i32.const 0))
  ;; Initialization completes before the bridge may deliver any callbacks.
  (func (export "init")
    call $create_input global.set $input
    call $create_output global.set $output
    global.get $input i32.const 1 call $on_data
    global.get $input i32.const 2 call $on_close)

  ;; length must equal text.length in UTF-16 units and be at most 4096.
  ;; Input and output arrays are local GC objects; no array is retained between
  ;; callbacks. There is no linear memory and no cumulative file-size counter.
  (func (export "data") (param $text externref) (param $remaining i32)
    (local $in (ref null $units)) (local $out (ref null $units))
    (local $i i32) (local $o i32) (local $unit i32)
    ;; Worst-case expansion is three units per input unit (every unit is LF).
    ;; The 4096-unit bound makes the capacity multiplication non-overflowing.
    local.get $remaining array.new_default $units local.set $in
    local.get $remaining i32.const 3 i32.mul array.new_default $units local.set $out
    ;; Copy UTF-16 units without interpreting surrogate pairs as separate text.
    local.get $text local.get $in i32.const 0 call $into local.set $remaining
    block
      loop
        ;; Test before emitting any prefix: empty chunks and trailing LF are
        ;; handled without an extra write of "> ".
        local.get $remaining i32.eqz br_if 1
        local.get $in local.get $i array.get_u $units local.set $unit
        ;; Insert the ASCII prefix before the current unit when needed.
        global.get $line
        if
          local.get $out local.get $o i32.const 62 array.set $units
          local.get $o i32.const 1 i32.add local.set $o
          local.get $out local.get $o i32.const 32 array.set $units
          local.get $o i32.const 1 i32.add local.set $o
        end
        ;; Preserve each input unit. Surrogate units cannot equal LF, so no
        ;; prefix is inserted between a high/low pair. The bridge also keeps
        ;; pairs together at chunk boundaries; each output string is complete.
        local.get $out local.get $o local.get $unit array.set $units
        local.get $o i32.const 1 i32.add local.set $o
        local.get $unit i32.const 10 i32.eq global.set $line
        local.get $i i32.const 1 i32.add local.set $i
        local.get $remaining i32.const 1 i32.sub local.set $remaining
        br 0
      end
    end
    ;; Capture only the written array prefix. The resulting immutable string
    ;; remains safe to queue after these mutable arrays become unreachable.
    global.get $output
    local.get $out i32.const 0 local.get $o call $from
    call $write)

  ;; Request closure; the bridge reports completion only after queued writes
  ;; finish. Do not emit anything here, even if the final input unit was LF.
  (func (export "close") global.get $output call $end))
