(module
  (type (;0;) (func (result i32)))
  (type (;1;) (func (param i32 i32)))
  (type (;2;) (func (param i32 i32 i32)))
  (type (;3;) (func (param i32)))
  (type (;4;) (func))
  (import "bridge" "create_input" (func (;0;) (type 0)))
  (import "bridge" "create_output" (func (;1;) (type 0)))
  (import "bridge" "on_data" (func (;2;) (type 1)))
  (import "bridge" "on_close" (func (;3;) (type 1)))
  (import "bridge" "write" (func (;4;) (type 2)))
  (import "bridge" "end" (func (;5;) (type 3)))
  (memory (;0;) 1 1)
  (global (;0;) (mut i32) i32.const 1)
  (global (;1;) (mut i32) i32.const 0)
  (global (;2;) (mut i32) i32.const 0)
  (export "init" (func 6))
  (export "memory" (memory 0))
  (export "data" (func 7))
  (export "close" (func 8))
  (func (;6;) (type 4)
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
  (func (;7;) (type 3) (param i32)
    (local i32 i32 i32)
    i32.const 16384
    local.set 2
    block ;; label = @1
      loop ;; label = @2
        local.get 0
        i32.eqz
        br_if 1 (;@1;)
        local.get 1
        i32.load
        local.set 3
        global.get 0
        if ;; label = @3
          local.get 2
          i32.const 62
          i32.store
          local.get 2
          i32.const 4
          i32.add
          local.set 2
          local.get 2
          i32.const 32
          i32.store
          local.get 2
          i32.const 4
          i32.add
          local.set 2
        end
        local.get 2
        local.get 3
        i32.store
        local.get 2
        i32.const 4
        i32.add
        local.set 2
        local.get 3
        i32.const 10
        i32.eq
        global.set 0
        local.get 1
        i32.const 4
        i32.add
        local.set 1
        local.get 0
        i32.const 1
        i32.sub
        local.set 0
        br 0 (;@2;)
      end
    end
    global.get 2
    i32.const 16384
    local.get 2
    i32.const 16384
    i32.sub
    i32.const 4
    i32.div_u
    call 4
  )
  (func (;8;) (type 4)
    global.get 2
    call 5
  )
)
