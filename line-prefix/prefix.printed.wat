(module
  (type (;0;) (array (mut i16)))
  (type (;1;) (func (result i32)))
  (type (;2;) (func (param i32 i32)))
  (type (;3;) (func (param i32 externref)))
  (type (;4;) (func (param i32)))
  (type (;5;) (func (param externref (ref null 0) i32) (result i32)))
  (type (;6;) (func (param (ref null 0) i32 i32) (result (ref extern))))
  (type (;7;) (func (param externref) (result i32)))
  (type (;8;) (func (param externref i32 i32) (result (ref extern))))
  (type (;9;) (func (param externref i32) (result i32)))
  (type (;10;) (func))
  (type (;11;) (func (param externref i32)))
  (type (;12;) (func (param externref)))
  (import "bridge" "create_input" (func (;0;) (type 1)))
  (import "bridge" "create_output" (func (;1;) (type 1)))
  (import "bridge" "on_data" (func (;2;) (type 2)))
  (import "bridge" "on_close" (func (;3;) (type 2)))
  (import "bridge" "write" (func (;4;) (type 3)))
  (import "bridge" "end" (func (;5;) (type 4)))
  (import "wasm:js-string" "intoCharCodeArray" (func (;6;) (type 5)))
  (import "wasm:js-string" "fromCharCodeArray" (func (;7;) (type 6)))
  (import "wasm:js-string" "length" (func (;8;) (type 7)))
  (import "wasm:js-string" "substring" (func (;9;) (type 8)))
  (import "wasm:js-string" "charCodeAt" (func (;10;) (type 9)))
  (global (;0;) (mut i32) i32.const 1)
  (global (;1;) (mut i32) i32.const 0)
  (global (;2;) (mut i32) i32.const 0)
  (export "init" (func 11))
  (export "_chunk" (func 12))
  (export "close" (func 13))
  (export "data" (func 14))
  (func (;11;) (type 10)
    call 0
    global.set 1
    call 1
    global.set 2
    global.get 1
    i32.const 1
    call 2
    global.get 1
    i32.const 2
    call 3
  )
  (func (;12;) (type 11) (param externref i32)
    (local (ref null 0) (ref null 0) i32 i32 i32)
    local.get 1
    array.new_default 0
    local.set 2
    local.get 1
    i32.const 3
    i32.mul
    array.new_default 0
    local.set 3
    local.get 0
    local.get 2
    i32.const 0
    call 6
    local.set 1
    block ;; label = @1
      loop ;; label = @2
        local.get 1
        i32.eqz
        br_if 1 (;@1;)
        local.get 2
        local.get 4
        array.get_u 0
        local.set 6
        global.get 0
        if ;; label = @3
          local.get 3
          local.get 5
          i32.const 62
          array.set 0
          local.get 5
          i32.const 1
          i32.add
          local.set 5
          local.get 3
          local.get 5
          i32.const 32
          array.set 0
          local.get 5
          i32.const 1
          i32.add
          local.set 5
        end
        local.get 3
        local.get 5
        local.get 6
        array.set 0
        local.get 5
        i32.const 1
        i32.add
        local.set 5
        local.get 6
        i32.const 10
        i32.eq
        global.set 0
        local.get 4
        i32.const 1
        i32.add
        local.set 4
        local.get 1
        i32.const 1
        i32.sub
        local.set 1
        br 0 (;@2;)
      end
    end
    global.get 2
    local.get 3
    i32.const 0
    local.get 5
    call 7
    call 4
  )
  (func (;13;) (type 10)
    global.get 2
    call 5
  )
  (func (;14;) (type 12) (param externref)
    (local i32 i32 i32 i32)
    local.get 0
    call 8
    local.set 1
    block ;; label = @1
      loop ;; label = @2
        local.get 2
        local.get 1
        i32.eq
        br_if 1 (;@1;)
        local.get 1
        local.get 2
        i32.sub
        i32.const 4096
        i32.gt_u
        if ;; label = @3
          local.get 2
          i32.const 4096
          i32.add
          local.set 3
          local.get 0
          local.get 3
          i32.const 1
          i32.sub
          call 10
          local.set 4
          local.get 4
          i32.const 55296
          i32.ge_u
          local.get 4
          i32.const 56320
          i32.lt_u
          i32.and
          if ;; label = @4
            local.get 3
            i32.const 1
            i32.sub
            local.set 3
          end
        else
          local.get 1
          local.set 3
        end
        local.get 0
        local.get 2
        local.get 3
        call 9
        local.get 3
        local.get 2
        i32.sub
        call 12
        local.get 3
        local.set 2
        br 0 (;@2;)
      end
    end
  )
)
