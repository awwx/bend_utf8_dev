(module
  (memory (export "memory") 1)
  (func (export "is_surrogate_code_point") (param $cp i32) (result i32)
    local.get $cp
    i32.const 0xD800
    i32.ge_u
    local.get $cp
    i32.const 0xDFFF
    i32.le_u
    i32.and)
  (func (export "count_non_ascii") (param $ptr i32) (param $len i32) (result i32)
    (local $count i32)
    block
      loop
        local.get $len
        i32.eqz
        br_if 1
        local.get $ptr
        i32.load8_u
        i32.const 0x80
        i32.ge_u
        local.get $count
        i32.add
        local.set $count
        local.get $ptr
        i32.const 1
        i32.add
        local.set $ptr
        local.get $len
        i32.const 1
        i32.sub
        local.set $len
        br 0
      end
    end
    local.get $count))
