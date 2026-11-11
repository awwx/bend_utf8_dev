;; Streaming UTF-8 decoder (Talos candidate).
;;
;; State: one i32.  Bits 24..31 hold n = number of pending bytes (0..3);
;; pending byte k (k = 0, 1, 2, first byte first) is in bits 8k..8k+7;
;; all other bits are 0.  It mirrors RefDecoder's State = List UInt8.
;;
;; Text: code points written as little-endian u32 at consecutive addresses
;; starting at `out`; decode_buffer and decode_done return the end address.
;;
;; The functions mirror Utf8Ref.lean: $vs = isVS, $vsp = isVSP, $cp = cpOf,
;; $step = step (stepFresh b = step [] b), the loop = List.foldl stepAcc.
;; A "sequence" q of length m (1..4) is packed like the state bytes:
;; byte k in bits 8k..8k+7.
(module
  (memory (export "memory") 160)

  ;; isCont b : 0x80 <= b <= 0xBF
  (func $cont (param $b i32) (result i32)
    (i32.and (i32.ge_u (local.get $b) (i32.const 0x80))
             (i32.le_u (local.get $b) (i32.const 0xBF))))

  ;; secondOk b1 b2
  (func $second (param $b1 i32) (param $b2 i32) (result i32)
    (if (result i32) (i32.eq (local.get $b1) (i32.const 0xE0))
      (then (i32.and (i32.ge_u (local.get $b2) (i32.const 0xA0))
                     (i32.le_u (local.get $b2) (i32.const 0xBF))))
      (else
        (if (result i32) (i32.eq (local.get $b1) (i32.const 0xED))
          (then (i32.and (i32.ge_u (local.get $b2) (i32.const 0x80))
                         (i32.le_u (local.get $b2) (i32.const 0x9F))))
          (else
            (if (result i32) (i32.eq (local.get $b1) (i32.const 0xF0))
              (then (i32.and (i32.ge_u (local.get $b2) (i32.const 0x90))
                             (i32.le_u (local.get $b2) (i32.const 0xBF))))
              (else
                (if (result i32) (i32.eq (local.get $b1) (i32.const 0xF4))
                  (then (i32.and (i32.ge_u (local.get $b2) (i32.const 0x80))
                                 (i32.le_u (local.get $b2) (i32.const 0x8F))))
                  (else (call $cont (local.get $b2)))))))))))

  ;; isVS q m
  (func $vs (param $q i32) (param $m i32) (result i32)
    (local $b1 i32) (local $b2 i32) (local $b3 i32) (local $b4 i32)
    (local.set $b1 (i32.and (local.get $q) (i32.const 0xFF)))
    (local.set $b2 (i32.and (i32.shr_u (local.get $q) (i32.const 8)) (i32.const 0xFF)))
    (local.set $b3 (i32.and (i32.shr_u (local.get $q) (i32.const 16)) (i32.const 0xFF)))
    (local.set $b4 (i32.shr_u (local.get $q) (i32.const 24)))
    (if (i32.eq (local.get $m) (i32.const 1))
      (then (return (i32.le_u (local.get $b1) (i32.const 0x7F)))))
    (if (i32.eq (local.get $m) (i32.const 2))
      (then (return
        (i32.and (i32.and (i32.ge_u (local.get $b1) (i32.const 0xC2))
                          (i32.le_u (local.get $b1) (i32.const 0xDF)))
                 (call $second (local.get $b1) (local.get $b2))))))
    (if (i32.eq (local.get $m) (i32.const 3))
      (then (return
        (i32.and (i32.and (i32.and (i32.ge_u (local.get $b1) (i32.const 0xE0))
                                   (i32.le_u (local.get $b1) (i32.const 0xEF)))
                          (call $second (local.get $b1) (local.get $b2)))
                 (call $cont (local.get $b3))))))
    (if (i32.eq (local.get $m) (i32.const 4))
      (then (return
        (i32.and (i32.and (i32.and (i32.and (i32.ge_u (local.get $b1) (i32.const 0xF0))
                                            (i32.le_u (local.get $b1) (i32.const 0xF4)))
                                   (call $second (local.get $b1) (local.get $b2)))
                          (call $cont (local.get $b3)))
                 (call $cont (local.get $b4))))))
    (i32.const 0))

  ;; isVSP q m
  (func $vsp (param $q i32) (param $m i32) (result i32)
    (local $b1 i32) (local $b2 i32) (local $b3 i32)
    (local.set $b1 (i32.and (local.get $q) (i32.const 0xFF)))
    (local.set $b2 (i32.and (i32.shr_u (local.get $q) (i32.const 8)) (i32.const 0xFF)))
    (local.set $b3 (i32.and (i32.shr_u (local.get $q) (i32.const 16)) (i32.const 0xFF)))
    (if (i32.eq (local.get $m) (i32.const 1))
      (then (return
        (i32.or (i32.le_u (local.get $b1) (i32.const 0x7F))
                (i32.and (i32.ge_u (local.get $b1) (i32.const 0xC2))
                         (i32.le_u (local.get $b1) (i32.const 0xF4)))))))
    (if (i32.eq (local.get $m) (i32.const 2))
      (then (return
        (i32.and (i32.and (i32.ge_u (local.get $b1) (i32.const 0xC2))
                          (i32.le_u (local.get $b1) (i32.const 0xF4)))
                 (call $second (local.get $b1) (local.get $b2))))))
    (if (i32.eq (local.get $m) (i32.const 3))
      (then (return
        (i32.and (i32.and (i32.and (i32.ge_u (local.get $b1) (i32.const 0xE0))
                                   (i32.le_u (local.get $b1) (i32.const 0xF4)))
                          (call $second (local.get $b1) (local.get $b2)))
                 (call $cont (local.get $b3))))))
    ;; m = 4: isVSP = isVS
    (call $vs (local.get $q) (local.get $m)))

  ;; cpOf q m
  (func $cp (param $q i32) (param $m i32) (result i32)
    (local $b1 i32) (local $b2 i32) (local $b3 i32) (local $b4 i32)
    (local.set $b1 (i32.and (local.get $q) (i32.const 0xFF)))
    (local.set $b2 (i32.and (i32.shr_u (local.get $q) (i32.const 8)) (i32.const 0xFF)))
    (local.set $b3 (i32.and (i32.shr_u (local.get $q) (i32.const 16)) (i32.const 0xFF)))
    (local.set $b4 (i32.shr_u (local.get $q) (i32.const 24)))
    (if (i32.eq (local.get $m) (i32.const 1)) (then (return (local.get $b1))))
    (if (i32.eq (local.get $m) (i32.const 2))
      (then (return
        (i32.or (i32.shl (i32.and (local.get $b1) (i32.const 0x1F)) (i32.const 6))
                (i32.and (local.get $b2) (i32.const 0x3F))))))
    (if (i32.eq (local.get $m) (i32.const 3))
      (then (return
        (i32.or (i32.or (i32.shl (i32.and (local.get $b1) (i32.const 0x0F)) (i32.const 12))
                        (i32.shl (i32.and (local.get $b2) (i32.const 0x3F)) (i32.const 6)))
                (i32.and (local.get $b3) (i32.const 0x3F))))))
    (i32.or (i32.or (i32.or (i32.shl (i32.and (local.get $b1) (i32.const 0x07)) (i32.const 18))
                            (i32.shl (i32.and (local.get $b2) (i32.const 0x3F)) (i32.const 12)))
                    (i32.shl (i32.and (local.get $b3) (i32.const 0x3F)) (i32.const 6)))
            (i32.and (local.get $b4) (i32.const 0x3F))))

  ;; step: one byte $b (0..255) from state $s; writes the emitted code
  ;; points at $out and returns (new state, new out).
  (func $step (param $s i32) (param $b i32) (param $out i32) (result i32 i32)
    (local $n i32) (local $q i32) (local $m i32)
    (local.set $n (i32.shr_u (local.get $s) (i32.const 24)))
    (local.set $q (i32.or (i32.and (local.get $s) (i32.const 0xFFFFFF))
                          (i32.shl (local.get $b) (i32.shl (local.get $n) (i32.const 3)))))
    (local.set $m (i32.add (local.get $n) (i32.const 1)))
    (if (call $vs (local.get $q) (local.get $m))
      (then
        (i32.store (local.get $out) (call $cp (local.get $q) (local.get $m)))
        (return (i32.const 0) (i32.add (local.get $out) (i32.const 4)))))
    (if (call $vsp (local.get $q) (local.get $m))
      (then
        (return (i32.or (local.get $q) (i32.shl (local.get $m) (i32.const 24)))
                (local.get $out))))
    (i32.store (local.get $out) (i32.const 0xFFFD))
    (if (i32.eqz (local.get $n))
      (then (return (i32.const 0) (i32.add (local.get $out) (i32.const 4)))))
    (call $step (i32.const 0) (local.get $b) (i32.add (local.get $out) (i32.const 4))))

  (func (export "decode_start_state") (result i32)
    (i32.const 0))

  ;; decode_buffer(state, in, len, out) -> (state', out_end)
  (func (export "decode_buffer") (param $s i32) (param $in i32) (param $len i32) (param $out i32)
    (result i32 i32)
    (block $done
      (loop $next
        (br_if $done (i32.eqz (local.get $len)))
        (call $step (local.get $s) (i32.load8_u (local.get $in)) (local.get $out))
        (local.set $out)
        (local.set $s)
        (local.set $in (i32.add (local.get $in) (i32.const 1)))
        (local.set $len (i32.sub (local.get $len) (i32.const 1)))
        (br $next)))
    (local.get $s)
    (local.get $out))

  ;; decode_done(state, out) -> out_end
  (func (export "decode_done") (param $s i32) (param $out i32) (result i32)
    (if (i32.eqz (local.get $s)) (then (return (local.get $out))))
    (i32.store (local.get $out) (i32.const 0xFFFD))
    (i32.add (local.get $out) (i32.const 4))))
