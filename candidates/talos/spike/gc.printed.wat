(module
  (type (;0;) (array (mut i16)))
  (type (;1;) (func (param (ref null 0) i32 i32) (result (ref extern))))
  (type (;2;) (func (result externref)))
  (import "wasm:js-string" "fromCharCodeArray" (func (;0;) (type 1)))
  (export "hello" (func 1))
  (func (;1;) (type 2) (result externref)
    (local (ref null 0))
    i32.const 104
    i32.const 105
    array.new_fixed 0 2
    local.set 0
    local.get 0
    i32.const 0
    i32.const 2
    call 0
  )
)
