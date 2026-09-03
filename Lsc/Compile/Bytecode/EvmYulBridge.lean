import Lsc.Compile.Bytecode.EncodeProofs
import Lsc.Compile.Bytecode.EvmYulTrust
import EvmYul.EVM.Semantics
import Mathlib.Tactic.IntervalCases

namespace Lsc.Compile.Bytecode.EvmYulBridge

open EvmYul EvmYul.EVM EvmYul.Operation

abbrev UWord := EvmYul.UInt256
abbrev Decoded := Operation .EVM × Option (UWord × Nat)

open EvmYulTrust

/-- Writing a complete EVM word into fresh memory and reading that word back is exact. -/
theorem write_readWithPadding_32_empty (src : ByteArray) (hsize : src.size = 32) :
    (src.write 0 .empty 0 32).readWithPadding 0 32 = src := by
  have husize0 : USize.toNat (OfNat.ofNat 0 : USize) = 0 := rfl
  have hdata : src.data.size = 32 := hsize
  have hextract : src.data.extract 0 32 = src.data := by
    rw [← hdata]
    exact Array.extract_size
  simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
    ByteArray.copySlice, hsize, zeroes_eq_replicate, husize0, hextract]
  change src.extract 0 32 ++ ByteArray.empty = src
  rw [← hsize, ByteArray.extract_zero_size]
  simp

/-- Reading the ABI selector prefix after storing one complete word in fresh memory. -/
theorem write_readWithPadding_4_empty (src : ByteArray) (hsize : src.size = 32) :
    (src.write 0 .empty 0 32).readWithPadding 0 4 = src.extract 0 4 := by
  have husize0 : USize.toNat (OfNat.ofNat 0 : USize) = 0 := rfl
  have hwrite : src.write 0 .empty 0 32 = src := by
    simp [ByteArray.write, ByteArray.copySlice, hsize]
    cases src with
    | mk data =>
        congr
        change data.extract 0 32 = data
        rw [← hsize]
        exact Array.extract_size
  rw [hwrite]
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, hsize,
    zeroes_eq_replicate]
  change src.extract 0 4 ++ ByteArray.empty = src.extract 0 4
  simp

theorem byteArray_get?_append_size (pre code : ByteArray) :
    (pre ++ code).get? pre.size = code.get? 0 := by
  simp only [ByteArray.get?]
  by_cases hc : code.size = 0
  · have : code = ByteArray.empty := by
      cases code with
      | mk data =>
          simp only [ByteArray.size] at hc
          have : data = #[] := Array.size_eq_zero_iff.mp hc
          subst data
          rfl
    subst code
    simp
  · have hb : pre.size < (pre ++ code).size := by
      rw [ByteArray.size_append]
      omega
    rw [dif_pos hb]
    have hc0 : 0 < code.size := Nat.pos_of_ne_zero hc
    rw [dif_pos hc0]
    cases pre with
    | mk preData =>
      cases code with
      | mk codeData =>
        congr 1
        simp only [ByteArray.get, ByteArray.append]
        change (preData.toList ++ codeData.toList)[preData.size] =
          codeData.toList[0]
        rw [List.getElem_append_right (by simp)]
        simp [Array.length_toList]
        rfl

theorem byteArray_extract_append_size (pre code : ByteArray) (b e : Nat) :
    (pre ++ code).extract (pre.size + b) (pre.size + e) =
      code.extract b e := by
  rw [ByteArray.extract_append]
  have hp : pre.extract (pre.size + b) (pre.size + e) = ByteArray.empty := by
    have hs : (pre.extract (pre.size + b) (pre.size + e)).size = 0 := by
      rw [ByteArray.size_extract]
      omega
    cases hres : pre.extract (pre.size + b) (pre.size + e) with
    | mk data =>
        rw [hres] at hs
        have hd : data.size = 0 := hs
        have : data = #[] := Array.size_eq_zero_iff.mp hd
        subst data
        rfl
  rw [hp]
  simp

theorem byteArray_extract'_append_size (pre code : ByteArray) (b e : Nat) (hb : b ≤ e)
    (hlimit : pre.size + e < 2^64) :
    (pre ++ code).extract' (pre.size + b) (pre.size + e) =
      code.extract' b e := by
  have hlb : pre.size + b < 2^64 := lt_of_le_of_lt (Nat.add_le_add_left hb _) hlimit
  have heb : e < 2^64 := lt_of_le_of_lt (Nat.le_add_left _ _) hlimit
  have hbb : b < 2^64 := lt_of_le_of_lt hb heb
  have hlb' : pre.size + b < 18446744073709551616 := by norm_num at hlb ⊢; exact hlb
  have hlimit' : pre.size + e < 18446744073709551616 := by
    norm_num at hlimit ⊢
    exact hlimit
  have hbb' : b < 18446744073709551616 := by norm_num at hbb ⊢; exact hbb
  have heb' : e < 18446744073709551616 := by norm_num at heb ⊢; exact heb
  have hc1 :
      (decide (pre.size + b < 2^64) && decide (pre.size + e < 2^64)) = true := by
    norm_num
    exact ⟨hlb', hlimit'⟩
  have hc2 : (decide (b < 2^64) && decide (e < 2^64)) = true := by
    norm_num
    exact ⟨hbb', heb'⟩
  simp only [ByteArray.extract']
  rw [if_pos hc1, if_pos hc2]
  exact byteArray_extract_append_size pre code b e

/-- EvmYul's parser is a left inverse of its serializer. -/
theorem parseInstr_serializeInstr (op : Operation .EVM) :
    EVM.parseInstr (EVM.serializeInstr op) = some op := by
  cases op <;> rename_i op <;> cases op <;> rfl

theorem argOnNBytesOfInstr_eq_zero_of_not_push (op : Operation .EVM)
    (h : ¬ Operation.isPush op) :
    EVM.argOnNBytesOfInstr op = 0 := by
  cases op <;> rename_i op <;> cases op <;>
    simp_all [Operation.isPush, EVM.argOnNBytesOfInstr]

theorem argOnNBytesOfInstr_le_32 (op : Operation .EVM) :
    EVM.argOnNBytesOfInstr op ≤ 32 := by
  cases op <;> rename_i op <;> cases op <;> decide

/-- Decoding commutes with adding a byte prefix when PC points at the suffix. -/
theorem decode_append_size (pre code : ByteArray)
    (hpc : pre.size < EvmYul.UInt256.size)
    (hlimit : pre.size + 33 < 2^64) :
    EVM.decode (pre ++ code) (.ofNat pre.size) = EVM.decode code (.ofNat 0) := by
  have hpctonat : (EvmYul.UInt256.ofNat pre.size).toNat = pre.size := by
    change pre.size % EvmYul.UInt256.size = pre.size
    exact Nat.mod_eq_of_lt hpc
  have hzerotonat : (EvmYul.UInt256.ofNat 0).toNat = 0 := rfl
  simp only [EVM.decode, hpctonat, hzerotonat]
  rw [byteArray_get?_append_size]
  cases hget : code.get? 0 with
  | none => rfl
  | some byte =>
      cases hparse : EVM.parseInstr byte with
      | none => simp [Bind.bind, Option.bind, hparse]
      | some op =>
          simp only [Bind.bind, Option.bind, hparse]
          have hw := argOnNBytesOfInstr_le_32 op
          have hend : pre.size + (1 + EVM.argOnNBytesOfInstr op) < 2^64 := by
            omega
          have hex := byteArray_extract'_append_size pre code 1
            (1 + EVM.argOnNBytesOfInstr op) (by omega) hend
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            congrArg (fun bytes => some
              (op, if EVM.argOnNBytesOfInstr op == 0 then none
                else some (EvmYul.uInt256OfByteArray bytes,
                  EVM.argOnNBytesOfInstr op))) hex

/-- The actual EvmYul decoder recognizes a non-PUSH byte emitted at PC zero. -/
theorem decode_emitOp_zero (op : Operation .EVM) (tail : ByteArray)
    (h : ¬ Operation.isPush op) :
    EVM.decode (ByteArray.mk #[EVM.serializeInstr op] ++ tail) (.ofNat 0) =
      some (op, none) := by
  have hw := argOnNBytesOfInstr_eq_zero_of_not_push op h
  have hget :
      (ByteArray.mk #[EVM.serializeInstr op] ++ tail).get?
        (EvmYul.UInt256.ofNat 0).toNat = some (EVM.serializeInstr op) := by
    rfl
  rw [EVM.decode, hget]
  simp [parseInstr_serializeInstr, hw]

theorem argOnNBytesOfInstr_pushOp (width : Nat) (hwidth : width ≤ 32) :
    EVM.argOnNBytesOfInstr (pushOp width) = width := by
  interval_cases width <;> rfl

/-- The actual EvmYul decoder recognizes a canonical, at-most-32-byte PUSH at PC zero. -/
theorem decode_emitPush_zero (n : Nat) (tail : ByteArray) (hwidth : pushWidth n ≤ 32) :
    EVM.decode (emitPush n ++ tail) (.ofNat 0) =
      some (pushOp (pushWidth n),
        if pushWidth n == 0 then none else some (.ofNat n, pushWidth n)) := by
  have hget :
      (emitPush n ++ tail).get? (EvmYul.UInt256.ofNat 0).toNat =
        some (EVM.serializeInstr (pushOp (pushWidth n))) := by
    rfl
  rw [EVM.decode, hget]
  simp only [Bind.bind, Option.bind, parseInstr_serializeInstr]
  by_cases hn : n = 0
  · subst n
    rfl
  · have hwarg := argOnNBytesOfInstr_pushOp (pushWidth n) hwidth
    have hext := extract_emitPush_zero n tail hwidth
    rw [hwarg]
    have hw : pushWidth n ≠ 0 := by simp [pushWidth, hn]
    simp [hw]
    change EvmYul.uInt256OfByteArray
      ((emitPush n ++ tail).extract' 1 (1 + pushWidth n)) = .ofNat n
    rw [hext]
    exact decode_natToBigEndianBytes n hn

theorem decode_emitPush32_zero (n : Nat) (tail : ByteArray) (hn : n < 2 ^ 256) :
    EVM.decode (emitPush32 n ++ tail) (.ofNat 0) =
      some ((PUSH32 : Operation .EVM), some (.ofNat n, 32)) := by
  have hget :
      (emitPush32 n ++ tail).get? (EvmYul.UInt256.ofNat 0).toNat =
        some (EVM.serializeInstr (PUSH32 : Operation .EVM)) := by
    rfl
  rw [EVM.decode, hget]
  simp only [Bind.bind, Option.bind, parseInstr_serializeInstr]
  change some ((PUSH32 : Operation .EVM), some
    (EvmYul.uInt256OfByteArray ((emitPush32 n ++ tail).extract' 1 33), 32)) =
      some ((PUSH32 : Operation .EVM), some (.ofNat n, 32))
  rw [extract_emitPush32_zero, decode_natToBigEndianBytes_32 n hn]

def encodedPlainInstr : Instr → ByteArray
  | .op op => ByteArray.mk #[EVM.serializeInstr op]
  | .push n => emitPush n
  | .push32 n => emitPush32 n
  | _ => ByteArray.empty

def encodedPlainInstrs : List Instr → ByteArray
  | [] => ByteArray.empty
  | instr :: rest => encodedPlainInstr instr ++ encodedPlainInstrs rest

def decodedPlainInstr : Instr → Decoded
  | .op op => (op, none)
  | .push n =>
      (pushOp (pushWidth n),
        if pushWidth n == 0 then none else some (.ofNat n, pushWidth n))
  | .push32 n => (.PUSH32, some (.ofNat n, 32))
  | _ => (.INVALID, none)

def EncodablePlainInstr (instr : Instr) : Prop :=
  PlainInstr instr ∧ match instr with
    | .push n => pushWidth n ≤ 32
    | .push32 n => n < 2 ^ 256
    | _ => True

def EncodablePlainInstrs (instrs : List Instr) : Prop :=
  ∀ instr ∈ instrs, EncodablePlainInstr instr

/-- Pure decoder certificate, deliberately separate from successful execution. -/
inductive DecoderAlong (code : ByteArray) : Nat → List Instr → Prop
  | nil (pc) : DecoderAlong code pc []
  | cons (pc : Nat) (instr : Instr) (rest : List Instr)
      (hdecode : EVM.decode code (.ofNat pc) = some (decodedPlainInstr instr))
      (hrest : DecoderAlong code (pc + instrByteSize [] instr) rest) :
      DecoderAlong code pc (instr :: rest)

theorem DecoderAlong.dropPrefix {code : ByteArray} {pc : Nat}
    (pre rest : List Instr)
    (h : DecoderAlong code pc (pre ++ rest)) :
    DecoderAlong code (pc + (pre.map (instrByteSize [])).sum) rest := by
  induction pre generalizing pc with
  | nil => simpa using h
  | cons instr pre ih =>
      cases h with
      | cons _ _ _ _ htail =>
          have hrest := ih htail
          simpa [Nat.add_assoc] using hrest

theorem DecoderAlong.takePrefix {code : ByteArray} {pc : Nat}
    (pre rest : List Instr)
    (h : DecoderAlong code pc (pre ++ rest)) :
    DecoderAlong code pc pre := by
  induction pre generalizing pc with
  | nil => exact .nil pc
  | cons instr pre ih =>
      cases h with
      | cons _ _ _ hdecode htail =>
          exact .cons pc instr pre hdecode (ih htail)

theorem decode_encodedPlainInstr_zero (instr : Instr) (tail : ByteArray)
    (h : EncodablePlainInstr instr) :
    EVM.decode (encodedPlainInstr instr ++ tail) (.ofNat 0) =
      some (decodedPlainInstr instr) := by
  rcases h with ⟨hplain, henc⟩
  cases instr with
  | op op => exact decode_emitOp_zero op tail hplain
  | push n => exact decode_emitPush_zero n tail henc
      | push32 n => exact decode_emitPush32_zero n tail henc
  | pushLabel label => contradiction
  | jump label => contradiction
  | jumpi label => contradiction
  | jumpDest label => contradiction

theorem encodedPlainInstr_size (instr : Instr) (h : PlainInstr instr) :
    (encodedPlainInstr instr).size = instrByteSize [] instr := by
  cases instr with
  | op op => rfl
  | push n => exact emitPush_size n
  | push32 n => exact emitPush32_size n
  | pushLabel label => contradiction
  | jump label => contradiction
  | jumpi label => contradiction
  | jumpDest label => contradiction

theorem decoderAlong_encodedPlainInstrs (pre : ByteArray) (instrs : List Instr)
    (h : EncodablePlainInstrs instrs)
    (hlimit : (pre ++ encodedPlainInstrs instrs).size + 33 < 2^64) :
    DecoderAlong (pre ++ encodedPlainInstrs instrs) pre.size instrs := by
  induction instrs generalizing pre with
  | nil => exact .nil _
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr : EncodablePlainInstrs rest := by
        intro candidate hmem
        exact h candidate (by simp [hmem])
      have hpre64 : pre.size + 33 < 2^64 := by
        rw [ByteArray.size_append] at hlimit
        omega
      have hpreWord : pre.size < EvmYul.UInt256.size := by
        have : pre.size < 2^64 := by omega
        exact lt_trans this (by decide)
      have hdecode :
          EVM.decode (pre ++ encodedPlainInstrs (instr :: rest)) (.ofNat pre.size) =
            some (decodedPlainInstr instr) := by
        rw [encodedPlainInstrs]
        rw [decode_append_size pre
          (encodedPlainInstr instr ++ encodedPlainInstrs rest) hpreWord hpre64]
        exact decode_encodedPlainInstr_zero instr (encodedPlainInstrs rest) hi
      apply DecoderAlong.cons pre.size instr rest hdecode
      have hsize := encodedPlainInstr_size instr hi.1
      have hlimit' :
          ((pre ++ encodedPlainInstr instr) ++ encodedPlainInstrs rest).size + 33 <
            2^64 := by
        rw [encodedPlainInstrs] at hlimit
        simpa [ByteArray.size_append, Nat.add_assoc] using hlimit
      have hrest := ih (pre ++ encodedPlainInstr instr) hr hlimit'
      have hcode :
          pre ++ encodedPlainInstr instr ++ encodedPlainInstrs rest =
            pre ++ (encodedPlainInstr instr ++ encodedPlainInstrs rest) := by
        apply ByteArray.ext
        simp
      rw [hcode] at hrest
      simpa [encodedPlainInstrs, ByteArray.size_append, hsize, Nat.add_assoc] using hrest

theorem emitInstrs_eq_encodedPlainInstrs (instrs : List Instr)
    (h : PlainInstrs instrs) :
    emitInstrs [] instrs = .ok (encodedPlainInstrs instrs) := by
  induction instrs with
  | nil => rfl
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr := PlainInstrs.tail h
      simp only [emitInstrs]
      cases instr with
      | op op =>
          simp [PlainInstr] at hi
          simp [hi, ih hr, encodedPlainInstrs, encodedPlainInstr, Bind.bind, Except.bind]
      | push n =>
          simp [ih hr, encodedPlainInstrs, encodedPlainInstr, Bind.bind, Except.bind]
      | push32 n =>
          simp [ih hr, encodedPlainInstrs, encodedPlainInstr, Bind.bind, Except.bind]
      | pushLabel label => contradiction
      | jump label => contradiction
      | jumpi label => contradiction
      | jumpDest label => contradiction

theorem encode_eq_encodedPlainInstrs (instrs : List Instr)
    (h : PlainInstrs instrs) :
    encode instrs = .ok (encodedPlainInstrs instrs) := by
  rw [encode_plain instrs h]
  exact emitInstrs_eq_encodedPlainInstrs instrs h

/-- Every bounded plain stream emitted by `Encode.encode` has an automatic actual-decoder
certificate at every encoded byte PC. -/
theorem decoderAlong_encode (instrs : List Instr) (h : EncodablePlainInstrs instrs)
    (bytes : ByteArray) (hencode : encode instrs = .ok bytes)
    (hlimit : bytes.size + 33 < 2^64) :
    DecoderAlong bytes 0 instrs := by
  have hp : PlainInstrs instrs := fun instr hmem => (h instr hmem).1
  rw [encode_eq_encodedPlainInstrs instrs hp] at hencode
  cases hencode
  simpa using decoderAlong_encodedPlainInstrs ByteArray.empty instrs h hlimit

theorem evmStep_push0 (fuel cost : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (.PUSH0, none)) st =
      .ok {
        st with
        stack := .ofNat 0 :: st.stack
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_push (fuel cost : Nat) (st : EVM.State)
    (push : Operation.POp) (arg : UWord) (width : Nat)
    (hnonzero : push ≠ .PUSH0) :
    EVM.step (fuel + 1) cost (some (.Push push, some (arg, width))) st =
      .ok {
        st with
        stack := arg :: st.stack
        pc := st.pc + .ofNat (width + 1)
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  cases push <;> first | contradiction | rfl

theorem evmStep_decodedPush (n fuel cost : Nat) (hwidth : pushWidth n ≤ 32)
    (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (decodedPlainInstr (.push n))) st =
      .ok {
        st with
        stack := .ofNat n :: st.stack
        pc := st.pc + .ofNat (pushWidth n + 1)
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  by_cases hn : n = 0
  · subst n
    rfl
  · have hw : pushWidth n ≠ 0 := by simp [pushWidth, hn]
    interval_cases h : pushWidth n <;> simp_all [decodedPlainInstr, pushOp] <;> rfl

/-- The complete family of EVM `DUP1` through `DUP16` instructions. -/
inductive DupOp where
  | d1 | d2 | d3 | d4 | d5 | d6 | d7 | d8
  | d9 | d10 | d11 | d12 | d13 | d14 | d15 | d16

def DupOp.depth : DupOp → Nat
  | .d1 => 1 | .d2 => 2 | .d3 => 3 | .d4 => 4
  | .d5 => 5 | .d6 => 6 | .d7 => 7 | .d8 => 8
  | .d9 => 9 | .d10 => 10 | .d11 => 11 | .d12 => 12
  | .d13 => 13 | .d14 => 14 | .d15 => 15 | .d16 => 16

def DupOp.op : DupOp → Operation .EVM
  | .d1 => .DUP1 | .d2 => .DUP2 | .d3 => .DUP3 | .d4 => .DUP4
  | .d5 => .DUP5 | .d6 => .DUP6 | .d7 => .DUP7 | .d8 => .DUP8
  | .d9 => .DUP9 | .d10 => .DUP10 | .d11 => .DUP11 | .d12 => .DUP12
  | .d13 => .DUP13 | .d14 => .DUP14 | .d15 => .DUP15 | .d16 => .DUP16

theorem evmStep_dup_dispatch (d : DupOp) (fuel cost : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (d.op, none)) st =
      EvmYul.dup d.depth
        { st with
          gasAvailable := st.gasAvailable - .ofNat cost
          execLength := st.execLength + 1 } := by
  cases d <;> rfl

/-- Uniform stack theorem for every generated local load, including `DUP3`--`DUP16`. -/
theorem evmStep_dup (d : DupOp) (fuel cost : Nat) (st : EVM.State)
    (top tail : List UWord) (hlen : top.length = d.depth) :
    EVM.step (fuel + 1) cost (some (d.op, none))
        { st with stack := top ++ tail } =
      .ok {
        st with
        stack := top.getLast! :: top ++ tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rw [evmStep_dup_dispatch]
  simp [EvmYul.dup, hlen, EVM.State.replaceStackAndIncrPC, EVM.State.incrPC]

theorem evmStep_dup1 (fuel cost : Nat) (st : EVM.State)
    (a : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.DUP1, none)) { st with stack := a :: tail } =
      .ok {
        st with
        stack := a :: a :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_dup2 (fuel cost : Nat) (st : EVM.State)
    (a b : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.DUP2, none)) { st with stack := a :: b :: tail } =
      .ok {
        st with
        stack := b :: a :: b :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_add (fuel cost : Nat) (st : EVM.State)
    (a b : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.ADD, none)) { st with stack := a :: b :: tail } =
      .ok {
        st with
        stack := UInt256.add a b :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_mul (fuel cost : Nat) (st : EVM.State)
    (a b : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.MUL, none)) { st with stack := a :: b :: tail } =
      .ok {
        st with
        stack := UInt256.mul a b :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_sub (fuel cost : Nat) (st : EVM.State)
    (lhs rhs : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.SUB, none)) { st with stack := lhs :: rhs :: tail } =
      .ok {
        st with
        stack := UInt256.sub lhs rhs :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_div (fuel cost : Nat) (st : EVM.State)
    (lhs rhs : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.DIV, none)) { st with stack := lhs :: rhs :: tail } =
      .ok {
        st with
        stack := UInt256.div lhs rhs :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_gt (fuel cost : Nat) (st : EVM.State)
    (lhs rhs : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.GT, none)) { st with stack := lhs :: rhs :: tail } =
      .ok {
        st with
        stack := UInt256.gt lhs rhs :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_lt (fuel cost : Nat) (st : EVM.State)
    (lhs rhs : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.LT, none)) { st with stack := lhs :: rhs :: tail } =
      .ok {
        st with
        stack := UInt256.lt lhs rhs :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_eq (fuel cost : Nat) (st : EVM.State)
    (lhs rhs : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.EQ, none)) { st with stack := lhs :: rhs :: tail } =
      .ok {
        st with
        stack := UInt256.eq lhs rhs :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_shr (fuel cost : Nat) (st : EVM.State)
    (amount value : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.SHR, none)) { st with stack := amount :: value :: tail } =
      .ok {
        st with
        stack := UInt256.shiftRight value amount :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_xor (fuel cost : Nat) (st : EVM.State)
    (a b : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.XOR, none)) { st with stack := a :: b :: tail } =
      .ok {
        st with
        stack := UInt256.xor a b :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_swap1 (fuel cost : Nat) (st : EVM.State)
    (a b : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.SWAP1, none)) { st with stack := a :: b :: tail } =
      .ok {
        st with
        stack := b :: a :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_calldataload (fuel cost : Nat) (st : EVM.State)
    (offset : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.CALLDATALOAD, none))
        { st with stack := offset :: tail } =
      .ok {
        st with
        stack := EvmYul.State.calldataload st.toState offset :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_calldatasize (fuel cost : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (.CALLDATASIZE, none)) st =
      .ok {
        st with
        stack := .ofNat st.executionEnv.calldata.size :: st.stack
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_pop (fuel cost : Nat) (st : EVM.State)
    (value : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.POP, none)) { st with stack := value :: tail } =
      .ok {
        st with
        stack := tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_jump (fuel cost : Nat) (st : EVM.State)
    (dest : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.JUMP, none)) { st with stack := dest :: tail } =
      .ok {
        st with
        stack := tail
        pc := dest
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_jumpi (fuel cost : Nat) (st : EVM.State)
    (dest cond : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.JUMPI, none))
        { st with stack := dest :: cond :: tail } =
      .ok {
        st with
        stack := tail
        pc := if cond != ⟨0⟩ then dest else st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_jumpdest (fuel cost : Nat) (st : EVM.State) :
    EVM.step (fuel + 1) cost (some (.JUMPDEST, none)) st =
      .ok {
        st with
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_sload (fuel cost : Nat) (st : EVM.State)
    (slot : UWord) (tail : List UWord) :
    let loaded := EvmYul.State.sload st.toState slot
    EVM.step (fuel + 1) cost (some (.SLOAD, none))
        { st with stack := slot :: tail } =
      .ok {
        st with
        toState := loaded.1
        stack := loaded.2 :: tail
        pc := st.pc + .ofNat 1
        gasAvailable := st.gasAvailable - .ofNat cost
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_mstore (fuel cost : Nat) (st : EVM.State)
    (offset value : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.MSTORE, none))
        { st with stack := offset :: value :: tail } =
      .ok {
        st with
        stack := tail
        toMachineState := EvmYul.MachineState.mstore
          { st.toMachineState with gasAvailable := st.gasAvailable - .ofNat cost }
          offset value
        pc := st.pc + .ofNat 1
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_return (fuel cost : Nat) (st : EVM.State)
    (offset size : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.RETURN, none))
        { st with stack := offset :: size :: tail } =
      .ok {
        st with
        stack := tail
        toMachineState := EvmYul.MachineState.evmReturn
          { st.toMachineState with gasAvailable := st.gasAvailable - .ofNat cost }
          offset size
        pc := st.pc + .ofNat 1
        execLength := st.execLength + 1 } := by
  rfl

theorem evmStep_revert (fuel cost : Nat) (st : EVM.State)
    (offset size : UWord) (tail : List UWord) :
    EVM.step (fuel + 1) cost (some (.REVERT, none))
        { st with stack := offset :: size :: tail } =
      .ok {
        st with
        stack := tail
        toMachineState := EvmYul.MachineState.evmRevert
          { st.toMachineState with gasAvailable := st.gasAvailable - .ofNat cost }
          offset size
        pc := st.pc + .ofNat 1
        execLength := st.execLength + 1 } := by
  rfl

private def belongsJump (o : Option UWord) (jumps : Array UWord) : Bool :=
  match o with
  | none => false
  | some n => jumps.contains n

private def notInJumps (o : Option UWord) (jumps : Array UWord) : Bool :=
  not (belongsJump o jumps)

private def writesInStaticMode (op : Operation .EVM) (stack : EvmYul.Stack UWord) : Bool :=
  op ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4,
    .TSTORE] ∨ (op = .CALL ∧ stack[2]? ≠ some ⟨0⟩)

/-- Public mirror of the local exceptional-halt checker `Z` inside EvmYul's `EVM.X`.
This is a definition, not an axiom; `xPrecheck_eq_local` below verifies the boundary by reduction. -/
def xPrecheck (validJumps : Array UWord) (op : Operation .EVM) (st : EVM.State) :
    Except EVM.ExecutionException (EVM.State × Nat) := do
  let cost₁ := EVM.memoryExpansionCost st op
  if st.gasAvailable.toNat < cost₁ then
    .error .OutOfGass
  let gasAvailable := st.gasAvailable - .ofNat cost₁
  let st := { st with gasAvailable := gasAvailable }
  let cost₂ := EVM.C' st op
  if st.gasAvailable.toNat < cost₂ then
    .error .OutOfGass
  if EVM.δ op = none then
    .error .InvalidInstruction
  if st.stack.length < (EVM.δ op).getD 0 then
    .error .StackUnderflow
  let invalidJump := notInJumps st.stack[0]? validJumps
  if op = .JUMP ∧ invalidJump then
    .error .BadJumpDestination
  if op = .JUMPI ∧ (st.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination
  if op = .RETURNDATACOPY ∧
      (st.stack.getD 1 ⟨0⟩).toNat + (st.stack.getD 2 ⟨0⟩).toNat >
        st.returnData.size then
    .error .InvalidMemoryAccess
  if st.stack.length - (EVM.δ op).getD 0 + (EVM.α op).getD 0 > 1024 then
    .error .StackOverflow
  if (¬ st.executionEnv.perm) ∧ writesInStaticMode op st.stack then
    .error .StaticModeViolation
  if op = .SSTORE ∧ st.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass
  if op.isCreate ∧ st.stack.getD 2 ⟨0⟩ > ⟨49152⟩ then
    .error .OutOfGass
  pure (st, cost₂)

/-- Explicit sufficient gas, stack, jump, memory, and environment conditions for `xPrecheck`.
For the pure-view stream, jump/create/storage/static clauses reduce immediately. -/
def XPrecheckSafe (validJumps : Array UWord) (op : Operation .EVM)
    (st : EVM.State) : Prop :=
  let cost₁ := EVM.memoryExpansionCost st op
  let checked := { st with gasAvailable := st.gasAvailable - .ofNat cost₁ }
  let cost₂ := EVM.C' checked op
  ¬ st.gasAvailable.toNat < cost₁ ∧
  ¬ checked.gasAvailable.toNat < cost₂ ∧
  EVM.δ op ≠ none ∧
  ¬ st.stack.length < (EVM.δ op).getD 0 ∧
  ¬ (op = .JUMP ∧ notInJumps st.stack[0]? validJumps) ∧
  ¬ (op = .JUMPI ∧ st.stack[1]? ≠ some ⟨0⟩ ∧
      notInJumps st.stack[0]? validJumps) ∧
  ¬ (op = .RETURNDATACOPY ∧
      (st.stack.getD 1 ⟨0⟩).toNat + (st.stack.getD 2 ⟨0⟩).toNat >
        st.returnData.size) ∧
  ¬ st.stack.length - (EVM.δ op).getD 0 + (EVM.α op).getD 0 > 1024 ∧
  ¬ ((¬ st.executionEnv.perm) ∧ writesInStaticMode op st.stack) ∧
  ¬ (op = .SSTORE ∧ checked.gasAvailable.toNat ≤ GasConstants.Gcallstipend) ∧
  ¬ (op.isCreate ∧ checked.stack.getD 2 ⟨0⟩ > ⟨49152⟩)

theorem xPrecheck_ok_of_safe (validJumps : Array UWord) (op : Operation .EVM)
    (st : EVM.State) (hsafe : XPrecheckSafe validJumps op st) :
    xPrecheck validJumps op st =
      .ok ({ st with gasAvailable :=
        st.gasAvailable - .ofNat (EVM.memoryExpansionCost st op) },
        EVM.C' { st with gasAvailable :=
          st.gasAvailable - .ofNat (EVM.memoryExpansionCost st op) } op) := by
  simp only [XPrecheckSafe] at hsafe
  rcases hsafe with
    ⟨hgas1, hgas2, hvalid, hstack, hjump, hjumpi, hcopy, hoverflow, hstatic,
      hsstore, hcreate⟩
  simp [xPrecheck, hgas1, hgas2, hvalid, hstack, hjump, hjumpi, hoverflow, hsstore]
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals split <;> simp_all
  all_goals rfl

def xHaltOutput (machine : EvmYul.MachineState) (op : Operation .EVM) :
    Option ByteArray :=
  if op ∈ [.RETURN, .REVERT] then
    some machine.H_return
  else if op ∈ [.STOP, .SELFDESTRUCT] then
    some .empty
  else none

/-- One non-halting actual `X` iteration, with the real decoder, checker and `EVM.step`.
The hypotheses expose exactly the sufficient gas/stack/environment obligations. -/
theorem X_step_of_precheck (fuel : Nat) (validJumps : Array UWord) (st checked next : EVM.State)
    (decoded : Decoded) (cost : Nat)
    (hdecode : EVM.decode st.executionEnv.code st.pc = some decoded)
    (hcheck : xPrecheck validJumps decoded.1 st = .ok (checked, cost))
    (hstep : EVM.step fuel cost (some decoded) checked = .ok next)
    (hhalt : xHaltOutput next.toMachineState decoded.1 = none) :
    EVM.X (fuel + 1) validJumps st = EVM.X fuel validJumps next := by
  simp only [EVM.X]
  rw [hdecode]
  change (match xPrecheck validJumps decoded.1 st with
    | .error e => Except.error e
    | .ok (checked, cost) => do
        let next ← EVM.step fuel cost (some decoded) checked
        match xHaltOutput next.toMachineState decoded.1 with
        | none => EVM.X fuel validJumps next
        | some output =>
            if decoded.1 == (Operation.REVERT : Operation .EVM) then
              Except.ok (EVM.ExecutionResult.revert next.gasAvailable output)
            else Except.ok (EVM.ExecutionResult.success next output)) = _
  rw [hcheck]
  simp only [Bind.bind, Except.bind]
  rw [hstep]
  simp [hhalt]

/-- Final actual `X` iteration for the generated `RETURN`. -/
theorem X_return_of_precheck (fuel : Nat) (validJumps : Array UWord)
    (st checked final : EVM.State) (cost : Nat)
    (hdecode : EVM.decode st.executionEnv.code st.pc = some (.RETURN, none))
    (hcheck : xPrecheck validJumps .RETURN st = .ok (checked, cost))
    (hstep : EVM.step fuel cost (some (.RETURN, none)) checked = .ok final) :
    EVM.X (fuel + 1) validJumps st =
      .ok (.success final final.H_return) := by
  simp only [EVM.X]
  rw [hdecode]
  change (match xPrecheck validJumps .RETURN st with
    | .error e => Except.error e
    | .ok (checked, cost) => do
        let final ← EVM.step fuel cost (some (.RETURN, none)) checked
        Except.ok (EVM.ExecutionResult.success final final.H_return)) = _
  rw [hcheck]
  simp only [Bind.bind, Except.bind]
  rw [hstep]

/-- Final actual `X` iteration for generated `REVERT`. -/
theorem X_revert_of_precheck (fuel : Nat) (validJumps : Array UWord)
    (st checked final : EVM.State) (cost : Nat)
    (hdecode : EVM.decode st.executionEnv.code st.pc = some (.REVERT, none))
    (hcheck : xPrecheck validJumps .REVERT st = .ok (checked, cost))
    (hstep : EVM.step fuel cost (some (.REVERT, none)) checked = .ok final) :
    EVM.X (fuel + 1) validJumps st =
      .ok (.revert final.gasAvailable final.H_return) := by
  simp only [EVM.X]
  rw [hdecode]
  change (match xPrecheck validJumps .REVERT st with
    | .error e => Except.error e
    | .ok (checked, cost) => do
        let final ← EVM.step fuel cost (some (.REVERT, none)) checked
        Except.ok (EVM.ExecutionResult.revert final.gasAvailable final.H_return)) = _
  rw [hcheck]
  simp only [Bind.bind, Except.bind]
  rw [hstep]

def checkedState (st : EVM.State) (op : Operation .EVM) : EVM.State :=
  { st with gasAvailable :=
      st.gasAvailable - .ofNat (EVM.memoryExpansionCost st op) }

def checkedCost (st : EVM.State) (op : Operation .EVM) : Nat :=
  EVM.C' (checkedState st op) op

@[simp]
theorem uint256_sub_zero (value : UWord) :
    value - EvmYul.UInt256.ofNat 0 = value := by
  rcases value with ⟨value⟩
  change EvmYul.UInt256.mk (value - (0 : Fin EvmYul.UInt256.size)) =
    EvmYul.UInt256.mk value
  congr
  simp

/-- A successful, fully checked execution certificate over EvmYul's actual decoder and state.
Unlike a list simulator, this follows the program counter produced by `EVM.step`, so it also
covers resolved `JUMP`/`JUMPI` control flow. It contains no caller-supplied step equations. -/
def XSuccessReady (validJumps : Array UWord) :
    Nat → EVM.State → EVM.State → ByteArray → Prop
  | 0, _, _, _ => False
  | fuel + 1, st, final, output =>
      match EVM.decode st.executionEnv.code st.pc with
      | none => False
      | some decoded =>
          XPrecheckSafe validJumps decoded.1 st ∧
          match EVM.step fuel (checkedCost st decoded.1) (some decoded)
              (checkedState st decoded.1) with
          | .error _ => False
          | .ok next =>
              match xHaltOutput next.toMachineState decoded.1 with
              | none => XSuccessReady validJumps fuel next final output
              | some bytes =>
                  decoded.1 ≠ .REVERT ∧ next = final ∧ bytes = output

theorem X_eq_success_of_ready (validJumps : Array UWord) (fuel : Nat)
    (st final : EVM.State) (output : ByteArray)
    (hready : XSuccessReady validJumps fuel st final output) :
    EVM.X fuel validJumps st = .ok (.success final output) := by
  induction fuel generalizing st with
  | zero => simp [XSuccessReady] at hready
  | succ fuel ih =>
      simp only [XSuccessReady] at hready
      cases hdecode : EVM.decode st.executionEnv.code st.pc with
      | none => simp [hdecode] at hready
      | some decoded =>
          rw [hdecode] at hready
          rcases hready with ⟨hsafe, hready⟩
          have hcheck := xPrecheck_ok_of_safe validJumps decoded.1 st hsafe
          cases hstep : EVM.step fuel (checkedCost st decoded.1) (some decoded)
              (checkedState st decoded.1) with
          | error err =>
              rw [hstep] at hready
              contradiction
          | ok next =>
              rw [hstep] at hready
              simp only [EVM.X]
              rw [hdecode]
              change (match xPrecheck validJumps decoded.1 st with
                | .error e => Except.error e
                | .ok (checked, cost) => do
                    let next ← EVM.step fuel cost (some decoded) checked
                    match xHaltOutput next.toMachineState decoded.1 with
                    | none => EVM.X fuel validJumps next
                    | some bytes =>
                        if decoded.1 == (Operation.REVERT : Operation .EVM) then
                          .ok (.revert next.gasAvailable bytes)
                        else .ok (.success next bytes)) = _
              rw [show xPrecheck validJumps decoded.1 st =
                  .ok (checkedState st decoded.1, checkedCost st decoded.1) by
                simpa [checkedState, checkedCost] using hcheck]
              simp only [Bind.bind, Except.bind]
              rw [hstep]
              dsimp only at hready ⊢
              cases hhalt : xHaltOutput next.toMachineState decoded.1 with
              | none =>
                  rw [hhalt] at hready
                  simpa [hhalt] using ih next hready
              | some bytes =>
                  rw [hhalt] at hready
                  rcases hready with ⟨hnotRevert, rfl, rfl⟩
                  simp [hnotRevert]

/-- A checked, non-halting prefix of an actual `EVM.X` execution.

This is the compositional counterpart of `XSuccessReady`: it exposes the state at
the end of a control-flow prefix, while every transition still comes from EvmYul's decoder,
precheck, and `EVM.step`. In particular it contains no caller-supplied step equation. -/
def XContinuationReady (validJumps : Array UWord) (suffixFuel : Nat) :
    Nat → EVM.State → EVM.State → Prop
  | 0, st, final => st = final
  | fuel + 1, st, final =>
      match EVM.decode st.executionEnv.code st.pc with
      | none => False
      | some decoded =>
          XPrecheckSafe validJumps decoded.1 st ∧
          match EVM.step (fuel + suffixFuel) (checkedCost st decoded.1) (some decoded)
              (checkedState st decoded.1) with
          | .error _ => False
          | .ok next =>
              xHaltOutput next.toMachineState decoded.1 = none ∧
              XContinuationReady validJumps suffixFuel fuel next final

/-- Peel a checked non-halting prefix from `EVM.X`, preserving the caller-selected suffix fuel. -/
theorem X_add_eq_of_continuation (validJumps : Array UWord) (prefixFuel suffixFuel : Nat)
    (st next : EVM.State)
    (hready : XContinuationReady validJumps suffixFuel prefixFuel st next) :
    EVM.X (prefixFuel + suffixFuel) validJumps st =
      EVM.X suffixFuel validJumps next := by
  induction prefixFuel generalizing st with
  | zero =>
      simp only [XContinuationReady] at hready
      subst st
      simp
  | succ fuel ih =>
      simp only [XContinuationReady] at hready
      cases hdecode : EVM.decode st.executionEnv.code st.pc with
      | none => simp [hdecode] at hready
      | some decoded =>
          rw [hdecode] at hready
          rcases hready with ⟨hsafe, hready⟩
          have hcheck := xPrecheck_ok_of_safe validJumps decoded.1 st hsafe
          cases hstep : EVM.step (fuel + suffixFuel) (checkedCost st decoded.1) (some decoded)
              (checkedState st decoded.1) with
          | error err =>
              rw [hstep] at hready
              contradiction
          | ok stepped =>
              rw [hstep] at hready
              rcases hready with ⟨hhalt, hrest⟩
              rw [Nat.succ_add]
              rw [X_step_of_precheck (fuel + suffixFuel) validJumps st
                (checkedState st decoded.1) stepped decoded
                (checkedCost st decoded.1) hdecode
                (by simpa [checkedState, checkedCost] using hcheck)
                hstep
                hhalt]
              exact ih stepped hrest

end Lsc.Compile.Bytecode.EvmYulBridge
