(module
  (type (;0;) (func (param i32) (result i32)))
  (type (;1;) (func (param i32 i32) (result i32)))
  (memory (;0;) 1)
  (export "memory" (memory 0))
  (export "is_surrogate_code_point" (func 0))
  (export "count_non_ascii" (func 1))
  (func (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 55296
    i32.ge_u
    local.get 0
    i32.const 57343
    i32.le_u
    i32.and
  )
  (func (;1;) (type 1) (param i32 i32) (result i32)
    (local i32)
    block ;; label = @1
      loop ;; label = @2
        local.get 1
        i32.eqz
        br_if 1 (;@1;)
        local.get 0
        i32.load8_u
        i32.const 128
        i32.ge_u
        local.get 2
        i32.add
        local.set 2
        local.get 0
        i32.const 1
        i32.add
        local.set 0
        local.get 1
        i32.const 1
        i32.sub
        local.set 1
        br 0 (;@2;)
      end
    end
    local.get 2
  )
)
