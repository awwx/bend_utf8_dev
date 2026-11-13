(module
  (import "bridge" "create_input" (func $create_input (result i32)))
  (import "bridge" "create_output" (func $create_output (result i32)))
  (import "bridge" "on_data" (func $on_data (param i32 i32)))
  (import "bridge" "on_close" (func $on_close (param i32 i32)))
  (import "bridge" "write" (func $write (param i32 i32 i32)))
  (import "bridge" "end" (func $end (param i32)))
  (global $line (mut i32) (i32.const 1))
  (global $input (mut i32) (i32.const 0))
  (global $output (mut i32) (i32.const 0))
  (func (export "init")
    call $create_input global.set $input
    call $create_output global.set $output
    global.get $input i32.const 1 call $on_data
    global.get $input i32.const 2 call $on_close)
  (memory (export "memory") 1 1)
  (func (export "data") (param $remaining i32)
    (local $input_ptr i32) (local $output_ptr i32) (local $cp i32)
    i32.const 16384 local.set $output_ptr
    block
      loop
        local.get $remaining i32.eqz br_if 1
        local.get $input_ptr i32.load local.set $cp
        global.get $line
        if
          local.get $output_ptr i32.const 62 i32.store
          local.get $output_ptr i32.const 4 i32.add local.set $output_ptr
          local.get $output_ptr i32.const 32 i32.store
          local.get $output_ptr i32.const 4 i32.add local.set $output_ptr
        end
        local.get $output_ptr local.get $cp i32.store
        local.get $output_ptr i32.const 4 i32.add local.set $output_ptr
        local.get $cp i32.const 10 i32.eq global.set $line
        local.get $input_ptr i32.const 4 i32.add local.set $input_ptr
        local.get $remaining i32.const 1 i32.sub local.set $remaining
        br 0
      end
    end
    global.get $output i32.const 16384
    local.get $output_ptr i32.const 16384 i32.sub i32.const 4 i32.div_u
    call $write)
  (func (export "close") global.get $output call $end))
