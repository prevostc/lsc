import Lsc.Compile.Bytecode.Encode

namespace Lsc.Compile.Bytecode

/-- Label-free structured instructions accepted by the straight-line simulator and emitted by the
proved view fragment. Embedded EVM PUSH operations are excluded because they must use `Instr.push`
so their immediate bytes are represented explicitly. -/
def PlainInstr : Instr → Prop
  | .push _ => True
  | .push32 _ => True
  | .op op => ¬ EvmYul.Operation.isPush op
  | _ => False

def PlainInstrs (instrs : List Instr) : Prop :=
  ∀ instr ∈ instrs, PlainInstr instr

theorem PlainInstrs.nil : PlainInstrs [] := by
  intro instr h
  cases h

theorem PlainInstrs.cons {instr : Instr} {rest : List Instr}
    (head : PlainInstr instr) (tail : PlainInstrs rest) :
    PlainInstrs (instr :: rest) := by
  intro candidate hmem
  simp only [List.mem_cons] at hmem
  rcases hmem with hEq | hmem
  · subst candidate
    exact head
  · exact tail candidate hmem

theorem PlainInstrs.tail {instr : Instr} {rest : List Instr}
    (h : PlainInstrs (instr :: rest)) : PlainInstrs rest :=
  fun candidate hmem => h candidate (List.mem_cons_of_mem instr hmem)

/-- Every symbolic label reference resolves in the selected production layout and no EVM PUSH is
smuggled through `Instr.op`. Generated contract instruction streams satisfy this condition. -/
def ResolvableInstrs (labels : List (String × Nat)) : List Instr → Prop
  | [] => True
  | .op op :: rest => ¬ EvmYul.Operation.isPush op ∧ ResolvableInstrs labels rest
  | .push _ :: rest => ResolvableInstrs labels rest
  | .push32 _ :: rest => ResolvableInstrs labels rest
  | .pushLabel lbl :: rest
  | .jump lbl :: rest
  | .jumpi lbl :: rest =>
      (∃ pc, lookupLabel labels lbl = .ok pc) ∧ ResolvableInstrs labels rest
  | .jumpDest _ :: rest => ResolvableInstrs labels rest

theorem resolveInstrs_succeeds (labels : List (String × Nat)) (instrs : List Instr)
    (h : ResolvableInstrs labels instrs) :
    ∃ resolved, resolveInstrs labels instrs = .ok resolved := by
  induction instrs with
  | nil => exact ⟨[], rfl⟩
  | cons instr rest ih =>
      cases instr with
      | op op =>
          rcases h with ⟨_, hr⟩
          obtain ⟨resolved, hresolved⟩ := ih hr
          exact ⟨.op op :: resolved,
            by simp [resolveInstrs, resolveInstr, hresolved, Bind.bind, Except.bind]⟩
      | push n =>
          obtain ⟨resolved, hresolved⟩ := ih h
          exact ⟨.push n :: resolved,
            by simp [resolveInstrs, resolveInstr, hresolved, Bind.bind, Except.bind]⟩
      | push32 n =>
          obtain ⟨resolved, hresolved⟩ := ih h
          exact ⟨.push32 n :: resolved,
            by simp [resolveInstrs, resolveInstr, hresolved, Bind.bind, Except.bind]⟩
      | pushLabel lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := ih hr
          exact ⟨.push32 pc :: resolved,
            by simp [resolveInstrs, resolveInstr, hpc, hresolved, Bind.bind, Except.bind]⟩
      | jump lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := ih hr
          exact ⟨[.push32 pc, .op .JUMP] ++ resolved,
            by simp [resolveInstrs, resolveInstr, hpc, hresolved, Bind.bind, Except.bind]⟩
      | jumpi lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := ih hr
          exact ⟨[.push32 pc, .op .JUMPI] ++ resolved,
            by simp [resolveInstrs, resolveInstr, hpc, hresolved, Bind.bind, Except.bind]⟩
      | jumpDest lbl =>
          obtain ⟨resolved, hresolved⟩ := ih h
          exact ⟨.op .JUMPDEST :: resolved,
            by simp [resolveInstrs, resolveInstr, hresolved, Bind.bind, Except.bind]⟩

/-- Production label emission is byte-for-byte equal to first exposing the resolved plain
instruction stream and then invoking the same production emitter. -/
theorem emitInstrs_eq_resolve (labels : List (String × Nat)) (instrs : List Instr)
    (h : ResolvableInstrs labels instrs) :
    emitInstrs labels instrs = (do
      let resolved ← resolveInstrs labels instrs
      emitInstrs [] resolved) := by
  induction instrs with
  | nil => rfl
  | cons instr rest ih =>
      cases instr with
      | op op =>
          rcases h with ⟨hop, hr⟩
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest hr
          have hi := ih hr
          simp [emitInstrs, resolveInstrs, resolveInstr, hop, hresolved, hi,
            Bind.bind, Except.bind]
      | push n =>
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest h
          have hi := ih h
          simp [emitInstrs, resolveInstrs, resolveInstr, hresolved, hi,
            Bind.bind, Except.bind]
      | push32 n =>
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest h
          have hi := ih h
          simp [emitInstrs, resolveInstrs, resolveInstr, hresolved, hi,
            Bind.bind, Except.bind]
      | pushLabel lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest hr
          have hi := ih hr
          simp [emitInstrs, emitPushLabel, resolveInstrs, resolveInstr, hpc, hresolved, hi,
            Bind.bind, Except.bind]
      | jump lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest hr
          have hi := ih hr
          simp [emitInstrs, emitPushLabel, resolveInstrs, resolveInstr, hpc, hresolved,
            hi, Bind.bind, Except.bind, EvmYul.Operation.isPush, ByteArray.append_assoc]
          cases emitInstrs [] resolved <;> simp
      | jumpi lbl =>
          rcases h with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest hr
          have hi := ih hr
          simp [emitInstrs, emitPushLabel, resolveInstrs, resolveInstr, hpc, hresolved,
            hi, Bind.bind, Except.bind, EvmYul.Operation.isPush, ByteArray.append_assoc]
          cases emitInstrs [] resolved <;> simp
      | jumpDest lbl =>
          obtain ⟨resolved, hresolved⟩ := resolveInstrs_succeeds labels rest h
          have hi := ih h
          simp [emitInstrs, resolveInstrs, resolveInstr, hresolved, hi,
            Bind.bind, Except.bind, EvmYul.Operation.isPush]

theorem resolvable_of_emitInstrs_ok (labels : List (String × Nat)) (instrs : List Instr)
    (code : ByteArray) (h : emitInstrs labels instrs = .ok code) :
    ResolvableInstrs labels instrs := by
  induction instrs generalizing code with
  | nil => trivial
  | cons instr rest ih =>
      cases instr with
      | op op =>
          by_cases hop : EvmYul.Operation.isPush op
          · simp [emitInstrs, hop, Bind.bind, Except.bind] at h
          · refine ⟨hop, ?_⟩
            cases htail : emitInstrs labels rest with
            | error err =>
                simp [emitInstrs, hop, htail, Bind.bind, Except.bind] at h
            | ok tail =>
                exact ih tail htail
      | push n =>
          cases htail : emitInstrs labels rest with
          | error err =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at h
          | ok tail =>
              exact ih tail htail
      | push32 n =>
          cases htail : emitInstrs labels rest with
          | error err =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at h
          | ok tail =>
              exact ih tail htail
      | pushLabel lbl =>
          cases hlookup : lookupLabel labels lbl with
          | error err =>
              simp [emitInstrs, emitPushLabel, hlookup, Bind.bind, Except.bind] at h
          | ok pc =>
              refine ⟨⟨pc, hlookup⟩, ?_⟩
              cases htail : emitInstrs labels rest with
              | error err =>
                  simp [emitInstrs, emitPushLabel, hlookup, htail,
                    Bind.bind, Except.bind] at h
              | ok tail => exact ih tail htail
      | jump lbl =>
          cases hlookup : lookupLabel labels lbl with
          | error err =>
              simp [emitInstrs, emitPushLabel, hlookup, Bind.bind, Except.bind] at h
          | ok pc =>
              refine ⟨⟨pc, hlookup⟩, ?_⟩
              cases htail : emitInstrs labels rest with
              | error err =>
                  simp [emitInstrs, emitPushLabel, hlookup, htail,
                    Bind.bind, Except.bind] at h
              | ok tail => exact ih tail htail
      | jumpi lbl =>
          cases hlookup : lookupLabel labels lbl with
          | error err =>
              simp [emitInstrs, emitPushLabel, hlookup, Bind.bind, Except.bind] at h
          | ok pc =>
              refine ⟨⟨pc, hlookup⟩, ?_⟩
              cases htail : emitInstrs labels rest with
              | error err =>
                  simp [emitInstrs, emitPushLabel, hlookup, htail,
                    Bind.bind, Except.bind] at h
              | ok tail => exact ih tail htail
      | jumpDest lbl =>
          cases htail : emitInstrs labels rest with
          | error err =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at h
          | ok tail => exact ih tail htail

/-- Any successful production `encode` has a successful byte-identical label-free resolution.
Thus exact label PCs and PUSH widths are inherited from `fixpointLabels`/`emitPush`, rather than
recomputed by a proof-only encoder. -/
theorem encode_resolves_byte_identically (instrs resolved : List Instr) (code : ByteArray)
    (hencode : encode instrs = .ok code)
    (hresolve : resolveInstrs (fixpointLabels instrs) instrs = .ok resolved) :
    emitInstrs [] resolved = .ok code := by
  have hemit : emitInstrs (fixpointLabels instrs) instrs = .ok code := by
    simp only [encode] at hencode
    cases hdup : checkDuplicateLabels instrs with
    | error err => simp [hdup, Bind.bind, Except.bind] at hencode
    | ok _ =>
        simpa [hdup, Bind.bind, Except.bind] using hencode
  have hres := resolvable_of_emitInstrs_ok _ _ _ hemit
  have heq := emitInstrs_eq_resolve _ _ hres
  rw [hemit, hresolve] at heq
  simpa using heq.symm

theorem resolveInstrs_plain (labels : List (String × Nat)) (instrs resolved : List Instr)
    (hresolvable : ResolvableInstrs labels instrs)
    (hresolve : resolveInstrs labels instrs = .ok resolved) :
    PlainInstrs resolved := by
  induction instrs generalizing resolved with
  | nil =>
      simp [resolveInstrs] at hresolve
      subst resolved
      exact PlainInstrs.nil
  | cons instr rest ih =>
      cases instr with
      | op op =>
          rcases hresolvable with ⟨hop, hr⟩
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hr
          simp [resolveInstrs, resolveInstr, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by simpa [PlainInstr] using hop) (ih tail hr htail)
      | push n =>
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hresolvable
          simp [resolveInstrs, resolveInstr, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by trivial) (ih tail hresolvable htail)
      | push32 n =>
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hresolvable
          simp [resolveInstrs, resolveInstr, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by trivial) (ih tail hresolvable htail)
      | pushLabel lbl =>
          rcases hresolvable with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hr
          simp [resolveInstrs, resolveInstr, hpc, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by trivial) (ih tail hr htail)
      | jump lbl =>
          rcases hresolvable with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hr
          simp [resolveInstrs, resolveInstr, hpc, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by trivial)
            (PlainInstrs.cons (by simp [PlainInstr, EvmYul.Operation.isPush])
              (ih tail hr htail))
      | jumpi lbl =>
          rcases hresolvable with ⟨⟨pc, hpc⟩, hr⟩
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hr
          simp [resolveInstrs, resolveInstr, hpc, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by trivial)
            (PlainInstrs.cons (by simp [PlainInstr, EvmYul.Operation.isPush])
              (ih tail hr htail))
      | jumpDest lbl =>
          obtain ⟨tail, htail⟩ := resolveInstrs_succeeds labels rest hresolvable
          simp [resolveInstrs, resolveInstr, htail, Bind.bind, Except.bind] at hresolve
          subst resolved
          exact PlainInstrs.cons (by simp [PlainInstr, EvmYul.Operation.isPush])
            (ih tail hresolvable htail)

theorem resolveInstrs_preserves_byteSize
    (labels : List (String × Nat)) (instrs resolved : List Instr)
    (hresolve : resolveInstrs labels instrs = .ok resolved) :
    (resolved.map (instrByteSize [])).sum =
      (instrs.map (instrByteSize labels)).sum := by
  induction instrs generalizing resolved with
  | nil =>
      simp [resolveInstrs] at hresolve
      subst resolved
      rfl
  | cons instr rest ih =>
      cases hrest : resolveInstrs labels rest with
      | error err =>
          cases instr with
          | pushLabel label | jump label | jumpi label =>
              cases hlookup : lookupLabel labels label <;>
                simp [resolveInstrs, resolveInstr, hlookup, hrest,
                  Bind.bind, Except.bind] at hresolve
          | op op | push n | push32 n | jumpDest label =>
              simp [resolveInstrs, resolveInstr, hrest, Bind.bind, Except.bind] at hresolve
      | ok resolvedRest =>
          have ihRest := ih resolvedRest hrest
          cases instr with
          | op op =>
              simp [resolveInstrs, resolveInstr, hrest, Bind.bind, Except.bind] at hresolve
              subst resolved
              simp [instrByteSize, ihRest]
          | push n =>
              simp [resolveInstrs, resolveInstr, hrest, Bind.bind, Except.bind] at hresolve
              subst resolved
              simp [instrByteSize, ihRest]
          | push32 n =>
              simp [resolveInstrs, resolveInstr, hrest, Bind.bind, Except.bind] at hresolve
              subst resolved
              simp [instrByteSize, ihRest]
          | pushLabel label =>
              cases hlookup : lookupLabel labels label with
              | error err =>
                  simp [resolveInstrs, resolveInstr, hlookup,
                    Bind.bind, Except.bind] at hresolve
              | ok pc =>
                  simp [resolveInstrs, resolveInstr, hlookup, hrest,
                    Bind.bind, Except.bind] at hresolve
                  subst resolved
                  simp [instrByteSize, ihRest]
          | jump label | jumpi label =>
              cases hlookup : lookupLabel labels label with
              | error err =>
                  simp [resolveInstrs, resolveInstr, hlookup,
                    Bind.bind, Except.bind] at hresolve
              | ok pc =>
                  simp [resolveInstrs, resolveInstr, hlookup, hrest,
                    Bind.bind, Except.bind] at hresolve
                  subst resolved
                  simp [instrByteSize, ihRest]
                  omega
          | jumpDest label =>
              simp [resolveInstrs, resolveInstr, hrest, Bind.bind, Except.bind] at hresolve
              subst resolved
              simp [instrByteSize, ihRest]

/-- Successful production encoding yields an existential plain stream using exactly the same bytes.
This is the reusable entrypoint for decoder and control-flow proofs. -/
theorem encode_has_byte_identical_plain_resolution (instrs : List Instr) (code : ByteArray)
    (hencode : encode instrs = .ok code) :
    ∃ resolved,
      resolveInstrs (fixpointLabels instrs) instrs = .ok resolved ∧
      PlainInstrs resolved ∧
      emitInstrs [] resolved = .ok code := by
  have hemit : emitInstrs (fixpointLabels instrs) instrs = .ok code := by
    simp only [encode] at hencode
    cases hdup : checkDuplicateLabels instrs with
    | error err => simp [hdup, Bind.bind, Except.bind] at hencode
    | ok _ => simpa [hdup, Bind.bind, Except.bind] using hencode
  have hresolvable := resolvable_of_emitInstrs_ok _ _ _ hemit
  obtain ⟨resolved, hresolve⟩ :=
    resolveInstrs_succeeds (fixpointLabels instrs) instrs hresolvable
  exact ⟨resolved, hresolve,
    resolveInstrs_plain _ _ _ hresolvable hresolve,
    encode_resolves_byte_identically instrs resolved code hencode hresolve⟩

theorem jumpDestLabelsRaw_plain (instrs : List Instr) (h : PlainInstrs instrs) :
    jumpDestLabelsRaw instrs = [] := by
  induction instrs with
  | nil => rfl
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr := PlainInstrs.tail h
      cases instr with
      | op op => simpa [jumpDestLabelsRaw] using ih hr
      | push n => simpa [jumpDestLabelsRaw] using ih hr
      | push32 n => simpa [jumpDestLabelsRaw] using ih hr
      | pushLabel label => contradiction
      | jump label => contradiction
      | jumpi label => contradiction
      | jumpDest label => contradiction

private theorem layoutLabelsFrom_plain (hints : List (String × Nat)) (pc : Nat)
    (instrs : List Instr) (acc : List (String × Nat)) (h : PlainInstrs instrs) :
    layoutLabelsFrom hints pc instrs acc = acc := by
  induction instrs generalizing pc acc with
  | nil => rfl
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr := PlainInstrs.tail h
      cases instr <;> simp [PlainInstr] at hi
      all_goals
        simp only [layoutLabelsFrom]
        exact ih _ _ hr

theorem layoutLabels_plain (instrs : List Instr) (h : PlainInstrs instrs)
    (hints : List (String × Nat)) :
    layoutLabels instrs hints = [] := by
  exact layoutLabelsFrom_plain hints 0 instrs [] h

theorem fixpointLabels_plain (instrs : List Instr) (h : PlainInstrs instrs) :
    fixpointLabels instrs = [] := by
  exact layoutLabels_plain instrs h []

theorem layoutLabelsFrom_append (hints : List (String × Nat))
    (pc : Nat) (first rest : List Instr) (acc : List (String × Nat)) :
    layoutLabelsFrom hints pc (first ++ rest) acc =
      layoutLabelsFrom hints
        (pc + (first.map (instrByteSize hints)).sum) rest
        (layoutLabelsFrom hints pc first acc) := by
  induction first generalizing pc acc with
  | nil => simp [layoutLabelsFrom]
  | cons instr first ih =>
      cases instr with
      | jumpDest label =>
          simp only [List.cons_append, layoutLabelsFrom, List.map_cons, List.sum_cons,
            instrByteSize]
          simpa [Nat.add_assoc] using ih (pc + 1) ((label, pc) :: acc)
      | op op =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.op op)) acc
      | push n =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.push n)) acc
      | push32 n =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.push32 n)) acc
      | pushLabel label =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.pushLabel label)) acc
      | jump label =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.jump label)) acc
      | jumpi label =>
          simpa [layoutLabelsFrom, Nat.add_assoc] using
            ih (pc + instrByteSize hints (.jumpi label)) acc

theorem layoutLabelsFrom_filter_absent (hints : List (String × Nat))
    (target : String) (pc : Nat) (instrs : List Instr)
    (acc : List (String × Nat))
    (habsent : target ∉ jumpDestLabelsRaw instrs) :
    (layoutLabelsFrom hints pc instrs acc).filter (·.1 == target) =
      acc.filter (·.1 == target) := by
  induction instrs generalizing pc acc with
  | nil => rfl
  | cons instr rest ih =>
      cases instr with
      | jumpDest label =>
          simp only [jumpDestLabelsRaw, List.filterMap_cons, List.mem_cons] at habsent
          have hne : label ≠ target := by
            intro heq
            apply habsent
            exact Or.inl heq.symm
          have hrest : target ∉ jumpDestLabelsRaw rest := by
            intro hmem
            exact habsent (Or.inr hmem)
          simp only [layoutLabelsFrom]
          rw [ih (pc := pc + 1) (acc := (label, pc) :: acc) hrest]
          simp [hne]
      | op op | push n | push32 n | pushLabel label | jump label | jumpi label =>
          simp only [jumpDestLabelsRaw, List.filterMap_cons] at habsent
          simp only [layoutLabelsFrom]
          exact ih _ _ habsent

theorem lookupLabel_layoutLabels_of_decomposition
    (before after : List Instr) (label : String)
    (hbefore : label ∉ jumpDestLabelsRaw before)
    (hafter : label ∉ jumpDestLabelsRaw after) :
    lookupLabel (layoutLabels (before ++ .jumpDest label :: after) []) label =
      .ok ((before.map (instrByteSize [])).sum) := by
  simp only [layoutLabels]
  rw [layoutLabelsFrom_append]
  simp only [layoutLabelsFrom]
  have hb := layoutLabelsFrom_filter_absent [] label 0 before [] hbefore
  have ha := layoutLabelsFrom_filter_absent [] label
    ((before.map (instrByteSize [])).sum + 1) after
    ((label, (before.map (instrByteSize [])).sum) :: layoutLabelsFrom [] 0 before [])
    hafter
  simp only [Nat.zero_add, lookupLabel]
  rw [ha]
  simp [hb]

theorem nodup_jumpDestLabelsRaw_of_checkDuplicateLabels
    (instrs : List Instr) (hcheck : checkDuplicateLabels instrs = .ok ()) :
    (jumpDestLabelsRaw instrs).Nodup := by
  simp only [checkDuplicateLabels] at hcheck
  split at hcheck
  · assumption
  · rename_i hdup
    split at hcheck <;> simp at hcheck

theorem lookupLabel_layoutLabels_exact
    (before after : List Instr) (label : String)
    (hcheck :
      checkDuplicateLabels (before ++ .jumpDest label :: after) = .ok ()) :
    lookupLabel
        (layoutLabels (before ++ .jumpDest label :: after) []) label =
      .ok ((before.map (instrByteSize [])).sum) := by
  have hnodup := nodup_jumpDestLabelsRaw_of_checkDuplicateLabels _ hcheck
  simp only [jumpDestLabelsRaw, List.filterMap_append, List.filterMap_cons] at hnodup
  have hparts := List.nodup_append.mp hnodup
  have hbefore : label ∉ jumpDestLabelsRaw before := by
    intro hmem
    exact hparts.2.2 label hmem label (by simp) rfl
  have hafter : label ∉ jumpDestLabelsRaw after := by
    exact (List.nodup_cons.mp hparts.2.1).1
  exact lookupLabel_layoutLabels_of_decomposition before after label hbefore hafter

theorem encode_forward_label_uses_push32 :
    encode [.pushLabel "target", .jumpDest "target"] =
      .ok (emitPush32 33 ++
        ByteArray.mk #[EvmYul.EVM.serializeInstr EvmYul.Operation.JUMPDEST]) := by
  native_decide


theorem checkDuplicateLabels_plain (instrs : List Instr) (h : PlainInstrs instrs) :
    checkDuplicateLabels instrs = .ok () := by
  simp [checkDuplicateLabels, jumpDestLabelsRaw_plain instrs h]

/-- Label resolution is the identity layout step for the proved pure view fragment. -/
theorem encode_plain (instrs : List Instr) (h : PlainInstrs instrs) :
    encode instrs = emitInstrs [] instrs := by
  simp [encode, checkDuplicateLabels_plain instrs h, layoutLabels_plain instrs h,
    Bind.bind, Except.bind]

theorem emitInstrs_plain_succeeds (instrs : List Instr) (h : PlainInstrs instrs) :
    ∃ bytes, emitInstrs [] instrs = .ok bytes := by
  induction instrs with
  | nil => exact ⟨ByteArray.empty, rfl⟩
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr := PlainInstrs.tail h
      obtain ⟨tail, htail⟩ := ih hr
      cases instr with
      | op op =>
          refine ⟨ByteArray.mk #[EvmYul.EVM.serializeInstr op] ++ tail, ?_⟩
          simp [PlainInstr] at hi
          simp [emitInstrs, hi, htail, Bind.bind, Except.bind]
      | push n =>
          exact ⟨emitPush n ++ tail,
            by simp [emitInstrs, htail, Bind.bind, Except.bind]⟩
      | push32 n =>
          exact ⟨emitPush32 n ++ tail,
            by simp [emitInstrs, htail, Bind.bind, Except.bind]⟩
      | pushLabel label => contradiction
      | jump label => contradiction
      | jumpi label => contradiction
      | jumpDest label => contradiction

theorem encode_plain_succeeds (instrs : List Instr) (h : PlainInstrs instrs) :
    ∃ bytes, encode instrs = .ok bytes := by
  rw [encode_plain instrs h]
  exact emitInstrs_plain_succeeds instrs h

theorem natToLittleEndianBytes_length (n width : Nat) :
    (natToLittleEndianBytes n width).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ width ih => simp [natToLittleEndianBytes, ih]

theorem fromBytes'_natToLittleEndianBytes (n width : Nat)
    (h : n < 256 ^ width) :
    EvmYul.fromBytes' (natToLittleEndianBytes n width) = n := by
  induction width generalizing n with
  | zero =>
      simp at h
      subst n
      rfl
  | succ width ih =>
      have hdiv : n / 256 < 256 ^ width := by
        apply Nat.div_lt_of_lt_mul
        simpa [pow_succ, Nat.mul_comm] using h
      simp only [natToLittleEndianBytes, EvmYul.fromBytes']
      rw [ih (n / 256) hdiv]
      change (UInt8.ofNat (n % 256)).toNat + 2 ^ 8 * (n / 256) = n
      have hbyte : (UInt8.ofNat (n % 256)).toNat = (n % 256) % 256 := by
        rfl
      rw [hbyte]
      norm_num
      exact Nat.mod_add_div n 256

theorem lt_pow_pushWidth (n : Nat) (hn : n ≠ 0) :
    n < 256 ^ pushWidth n := by
  rw [pushWidth, if_neg (by simpa using hn)]
  have hmod := Nat.mod_lt (Nat.log2 n) (by decide : 0 < 8)
  have hl : Nat.log2 n < 8 * (Nat.log2 n / 8 + 1) := by omega
  have hp := (Nat.log2_lt hn).mp hl
  simpa [show 256 = 2 ^ 8 by norm_num, pow_mul] using hp

theorem decode_natToBigEndianBytes (n : Nat) (hn : n ≠ 0) :
    EvmYul.uInt256OfByteArray (natToBigEndianBytes n (pushWidth n)) =
      EvmYul.UInt256.ofNat n := by
  simp [EvmYul.uInt256OfByteArray, natToBigEndianBytes,
    fromBytes'_natToLittleEndianBytes, lt_pow_pushWidth n hn]

theorem decode_natToBigEndianBytes_32 (n : Nat) (hn : n < 2 ^ 256) :
    EvmYul.uInt256OfByteArray (natToBigEndianBytes n 32) =
      EvmYul.UInt256.ofNat n := by
  have hbase : n < 256 ^ 32 := by
    norm_num [show 256 = 2 ^ 8 by norm_num, pow_mul] at hn ⊢
    exact hn
  simp [EvmYul.uInt256OfByteArray, natToBigEndianBytes,
    fromBytes'_natToLittleEndianBytes n 32 hbase]

theorem extract_emitPush_zero (n : Nat) (tail : ByteArray)
    (hwidth : pushWidth n ≤ 32) :
    (emitPush n ++ tail).extract' 1 (1 + pushWidth n) =
      natToBigEndianBytes n (pushWidth n) := by
  have hlt : 1 + pushWidth n < 2^64 := by omega
  have hs : (natToBigEndianBytes n (pushWidth n)).size = pushWidth n := by
    change (natToLittleEndianBytes n (pushWidth n)).reverse.length = pushWidth n
    simp [natToLittleEndianBytes_length]
  have hcond :
      (decide (1 < 2^64) && decide (1 + pushWidth n < 2^64)) = true := by
    norm_num at hlt ⊢
    omega
  have hh :
      (ByteArray.mk #[EvmYul.EVM.serializeInstr (pushOp (pushWidth n))]).extract
        1 (1 + pushWidth n) = ByteArray.empty := by
    apply ByteArray.ext
    simp
  have hhs :
      (ByteArray.mk #[EvmYul.EVM.serializeInstr (pushOp (pushWidth n))]).size = 1 := rfl
  have hi :
      (natToBigEndianBytes n (pushWidth n)).extract 0 (pushWidth n) =
        natToBigEndianBytes n (pushWidth n) := by
    simpa only [hs] using
      (ByteArray.extract_zero_size (b := natToBigEndianBytes n (pushWidth n)))
  rw [ByteArray.extract', if_pos hcond]
  rw [show emitPush n =
      ByteArray.mk #[EvmYul.EVM.serializeInstr (pushOp (pushWidth n))] ++
        natToBigEndianBytes n (pushWidth n) by rfl]
  rw [ByteArray.extract_append, ByteArray.extract_append, hh]
  simp only [ByteArray.size_append, hs, hhs]
  norm_num
  exact hi

theorem extract_emitPush32_zero (n : Nat) (tail : ByteArray) :
    (emitPush32 n ++ tail).extract' 1 33 = natToBigEndianBytes n 32 := by
  have hs : (natToBigEndianBytes n 32).size = 32 := by
    change (natToLittleEndianBytes n 32).reverse.length = 32
    simp [natToLittleEndianBytes_length]
  have hcond : (decide (1 < 2^64) && decide (33 < 2^64)) = true := by norm_num
  have hh :
      (ByteArray.mk #[EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32]).extract
        1 33 = ByteArray.empty := by
    apply ByteArray.ext
    simp
  have hi :
      (natToBigEndianBytes n 32).extract 0 32 = natToBigEndianBytes n 32 := by
    simpa only [hs] using
      (ByteArray.extract_zero_size (b := natToBigEndianBytes n 32))
  have hhs :
      (ByteArray.mk #[EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32]).size = 1 := rfl
  rw [ByteArray.extract', if_pos hcond]
  rw [show emitPush32 n =
      ByteArray.mk #[EvmYul.EVM.serializeInstr EvmYul.Operation.PUSH32] ++
        natToBigEndianBytes n 32 by rfl]
  rw [ByteArray.extract_append, ByteArray.extract_append, hh]
  simp only [ByteArray.size_append, hs, hhs]
  norm_num
  exact hi

theorem emitPush_size (n : Nat) :
    (emitPush n).size = instrByteSize [] (.push n) := by
  rw [show emitPush n =
      ByteArray.mk #[EvmYul.EVM.serializeInstr (pushOp (pushWidth n))] ++
        natToBigEndianBytes n (pushWidth n) by rfl]
  rw [ByteArray.size_append]
  change 1 + (natToLittleEndianBytes n (pushWidth n)).reverse.length =
    1 + pushWidth n
  simp [natToLittleEndianBytes_length]

theorem emitPush32_size (n : Nat) :
    (emitPush32 n).size = instrByteSize [] (.push32 n) := by
  rw [show emitPush32 n =
      ByteArray.mk #[EvmYul.EVM.serializeInstr .PUSH32] ++
        natToBigEndianBytes n 32 by rfl]
  rw [ByteArray.size_append]
  change 1 + (natToLittleEndianBytes n 32).reverse.length = 33
  simp [natToLittleEndianBytes_length]

theorem emitInstrs_plain_size (instrs : List Instr) (h : PlainInstrs instrs)
    (bytes : ByteArray) (hemit : emitInstrs [] instrs = .ok bytes) :
    bytes.size = (instrs.map (instrByteSize [])).sum := by
  induction instrs generalizing bytes with
  | nil =>
      simp [emitInstrs] at hemit
      subst bytes
      rfl
  | cons instr rest ih =>
      have hi := h instr (by simp)
      have hr := PlainInstrs.tail h
      cases instr with
      | op op =>
          simp [PlainInstr] at hi
          cases htail : emitInstrs [] rest with
          | error err =>
              simp [emitInstrs, hi, htail, Bind.bind, Except.bind] at hemit
          | ok tail =>
              simp [emitInstrs, hi, htail, Bind.bind, Except.bind] at hemit
              subst bytes
              rw [ByteArray.size_append, ih hr tail htail]
              change 1 + (List.map (instrByteSize []) rest).sum =
                1 + (List.map (instrByteSize []) rest).sum
              rfl
      | push n =>
          cases htail : emitInstrs [] rest with
          | error err =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at hemit
          | ok tail =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at hemit
              subst bytes
              rw [ByteArray.size_append, emitPush_size, ih hr tail htail]
              rfl
      | push32 n =>
          cases htail : emitInstrs [] rest with
          | error err =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at hemit
          | ok tail =>
              simp [emitInstrs, htail, Bind.bind, Except.bind] at hemit
              subst bytes
              rw [ByteArray.size_append, emitPush32_size, ih hr tail htail]
              rfl
      | pushLabel label => contradiction
      | jump label => contradiction
      | jumpi label => contradiction
      | jumpDest label => contradiction

/-- Encoded bytes and the structured PC model have the same length for the proved fragment. -/
theorem encode_plain_size (instrs : List Instr) (h : PlainInstrs instrs)
    (bytes : ByteArray) (hencode : encode instrs = .ok bytes) :
    bytes.size = (instrs.map (instrByteSize [])).sum := by
  rw [encode_plain instrs h] at hencode
  exact emitInstrs_plain_size instrs h bytes hencode

end Lsc.Compile.Bytecode
