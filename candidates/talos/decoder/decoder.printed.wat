(module
  (type (;0;) (func (param i32) (result i32)))
  (type (;1;) (func (param i32 i32) (result i32)))
  (type (;2;) (func (param i32 i32 i32) (result i32 i32)))
  (type (;3;) (func (result i32)))
  (type (;4;) (func (param i32 i32 i32 i32) (result i32 i32)))
  (memory (;0;) 160)
  (export "memory" (memory 0))
  (export "decode_start_state" (func 6))
  (export "decode_buffer" (func 7))
  (export "decode_done" (func 8))
  (func (;0;) (type 0) (param i32) (result i32)
    local.get 0
    i32.const 128
    i32.ge_u
    local.get 0
    i32.const 191
    i32.le_u
    i32.and
  )
  (func (;1;) (type 1) (param i32 i32) (result i32)
    local.get 0
    i32.const 224
    i32.eq
    if (result i32) ;; label = @1
      local.get 1
      i32.const 160
      i32.ge_u
      local.get 1
      i32.const 191
      i32.le_u
      i32.and
    else
      local.get 0
      i32.const 237
      i32.eq
      if (result i32) ;; label = @2
        local.get 1
        i32.const 128
        i32.ge_u
        local.get 1
        i32.const 159
        i32.le_u
        i32.and
      else
        local.get 0
        i32.const 240
        i32.eq
        if (result i32) ;; label = @3
          local.get 1
          i32.const 144
          i32.ge_u
          local.get 1
          i32.const 191
          i32.le_u
          i32.and
        else
          local.get 0
          i32.const 244
          i32.eq
          if (result i32) ;; label = @4
            local.get 1
            i32.const 128
            i32.ge_u
            local.get 1
            i32.const 143
            i32.le_u
            i32.and
          else
            local.get 1
            call 0
          end
        end
      end
    end
  )
  (func (;2;) (type 1) (param i32 i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.const 255
    i32.and
    local.set 2
    local.get 0
    i32.const 8
    i32.shr_u
    i32.const 255
    i32.and
    local.set 3
    local.get 0
    i32.const 16
    i32.shr_u
    i32.const 255
    i32.and
    local.set 4
    local.get 0
    i32.const 24
    i32.shr_u
    local.set 5
    local.get 1
    i32.const 1
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 127
      i32.le_u
      return
    end
    local.get 1
    i32.const 2
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 194
      i32.ge_u
      local.get 2
      i32.const 223
      i32.le_u
      i32.and
      local.get 2
      local.get 3
      call 1
      i32.and
      return
    end
    local.get 1
    i32.const 3
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 224
      i32.ge_u
      local.get 2
      i32.const 239
      i32.le_u
      i32.and
      local.get 2
      local.get 3
      call 1
      i32.and
      local.get 4
      call 0
      i32.and
      return
    end
    local.get 1
    i32.const 4
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 240
      i32.ge_u
      local.get 2
      i32.const 244
      i32.le_u
      i32.and
      local.get 2
      local.get 3
      call 1
      i32.and
      local.get 4
      call 0
      i32.and
      local.get 5
      call 0
      i32.and
      return
    end
    i32.const 0
  )
  (func (;3;) (type 1) (param i32 i32) (result i32)
    (local i32 i32 i32)
    local.get 0
    i32.const 255
    i32.and
    local.set 2
    local.get 0
    i32.const 8
    i32.shr_u
    i32.const 255
    i32.and
    local.set 3
    local.get 0
    i32.const 16
    i32.shr_u
    i32.const 255
    i32.and
    local.set 4
    local.get 1
    i32.const 1
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 127
      i32.le_u
      local.get 2
      i32.const 194
      i32.ge_u
      local.get 2
      i32.const 244
      i32.le_u
      i32.and
      i32.or
      return
    end
    local.get 1
    i32.const 2
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 194
      i32.ge_u
      local.get 2
      i32.const 244
      i32.le_u
      i32.and
      local.get 2
      local.get 3
      call 1
      i32.and
      return
    end
    local.get 1
    i32.const 3
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 224
      i32.ge_u
      local.get 2
      i32.const 244
      i32.le_u
      i32.and
      local.get 2
      local.get 3
      call 1
      i32.and
      local.get 4
      call 0
      i32.and
      return
    end
    local.get 0
    local.get 1
    call 2
  )
  (func (;4;) (type 1) (param i32 i32) (result i32)
    (local i32 i32 i32 i32)
    local.get 0
    i32.const 255
    i32.and
    local.set 2
    local.get 0
    i32.const 8
    i32.shr_u
    i32.const 255
    i32.and
    local.set 3
    local.get 0
    i32.const 16
    i32.shr_u
    i32.const 255
    i32.and
    local.set 4
    local.get 0
    i32.const 24
    i32.shr_u
    local.set 5
    local.get 1
    i32.const 1
    i32.eq
    if ;; label = @1
      local.get 2
      return
    end
    local.get 1
    i32.const 2
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 31
      i32.and
      i32.const 6
      i32.shl
      local.get 3
      i32.const 63
      i32.and
      i32.or
      return
    end
    local.get 1
    i32.const 3
    i32.eq
    if ;; label = @1
      local.get 2
      i32.const 15
      i32.and
      i32.const 12
      i32.shl
      local.get 3
      i32.const 63
      i32.and
      i32.const 6
      i32.shl
      i32.or
      local.get 4
      i32.const 63
      i32.and
      i32.or
      return
    end
    local.get 2
    i32.const 7
    i32.and
    i32.const 18
    i32.shl
    local.get 3
    i32.const 63
    i32.and
    i32.const 12
    i32.shl
    i32.or
    local.get 4
    i32.const 63
    i32.and
    i32.const 6
    i32.shl
    i32.or
    local.get 5
    i32.const 63
    i32.and
    i32.or
  )
  (func (;5;) (type 2) (param i32 i32 i32) (result i32 i32)
    (local i32 i32 i32)
    local.get 0
    i32.const 24
    i32.shr_u
    local.set 3
    local.get 0
    i32.const 16777215
    i32.and
    local.get 1
    local.get 3
    i32.const 3
    i32.shl
    i32.shl
    i32.or
    local.set 4
    local.get 3
    i32.const 1
    i32.add
    local.set 5
    local.get 4
    local.get 5
    call 2
    if ;; label = @1
      local.get 2
      local.get 4
      local.get 5
      call 4
      i32.store
      i32.const 0
      local.get 2
      i32.const 4
      i32.add
      return
    end
    local.get 4
    local.get 5
    call 3
    if ;; label = @1
      local.get 4
      local.get 5
      i32.const 24
      i32.shl
      i32.or
      local.get 2
      return
    end
    local.get 2
    i32.const 65533
    i32.store
    local.get 3
    i32.eqz
    if ;; label = @1
      i32.const 0
      local.get 2
      i32.const 4
      i32.add
      return
    end
    i32.const 0
    local.get 1
    local.get 2
    i32.const 4
    i32.add
    call 5
  )
  (func (;6;) (type 3) (result i32)
    i32.const 0
  )
  (func (;7;) (type 4) (param i32 i32 i32 i32) (result i32 i32)
    block ;; label = @1
      loop ;; label = @2
        local.get 2
        i32.eqz
        br_if 1 (;@1;)
        local.get 0
        local.get 1
        i32.load8_u
        local.get 3
        call 5
        local.set 3
        local.set 0
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        local.get 2
        i32.const 1
        i32.sub
        local.set 2
        br 0 (;@2;)
      end
    end
    local.get 0
    local.get 3
  )
  (func (;8;) (type 1) (param i32 i32) (result i32)
    local.get 0
    i32.eqz
    if ;; label = @1
      local.get 1
      return
    end
    local.get 1
    i32.const 65533
    i32.store
    local.get 1
    i32.const 4
    i32.add
  )
)
