module

public import WordRAM.Coins

/-!
# Bit locality and measurability of machine runs

Properties of `Runs` and `EndsAsContract` with respect to the random bit stream `ω`:

* `Runs.pos_le`, `Runs.exists_pos_eq`, `Runs.pos_dvd`: a terminating run advances `st.pos`
  monotonically by a multiple of the word size `w`.
* `Runs.congr_bits`, `Runs.congr_bits_ge`: a run depends only on the random bits
  `ω i` for `st.pos ≤ i < st'.pos`.
* `Runs.shift_iff`, `Runs.shift`: shifting `st.pos` by `q` corresponds to shifting `ω` by `q`.
* `dependsOn_runs`, `dependsOn_exists_runs`, `dependsOn_endsAsContract`,
  `measurableSet_runs`, `measurableSet_exists_runs`, `measurableSet_endsAsContract`:
  dependence and measurability of events defined by machine runs.
-/

public section

namespace WordRAM

open MeasureTheory

private theorem expr_eval_with_pos (e : Expr) (w : ℕ) (st : State) (q : ℕ) :
    e.eval w { st with pos := q } = e.eval w st := by
  induction e with
  | const _ => rfl
  | reg _ => rfl
  | load a ih => simp [Expr.eval, ih]
  | bin _ a b iha ihb => simp [Expr.eval, iha, ihb]

private theorem evalArgs_with_pos (es : List Expr) (w : ℕ) (st : State) (q : ℕ) :
    evalArgs w { st with pos := q } es = evalArgs w st es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [evalArgs, expr_eval_with_pos, ih]

private theorem exec_pos_bound :
    ∀ (fuel : ℕ) (w : ℕ) (p : Program) (ω : ℕ → Bool) (s : Stmt) (st : State)
      {o : Outcome} {st' : State} {c : ℕ},
      exec w p ω fuel s st = some (o, st', c) →
      (∃ k, st'.pos = st.pos + k * w) ∧ st'.pos ≤ st.pos + w * 2 ^ fuel
  | 0, _, _, _, _, _, _, _, _, h => by simp [exec] at h
  | fuel + 1, w, p, ω, s, st, o, st', c, h => by
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, _⟩
      exact ⟨⟨0, by simp⟩, Nat.le_add_right _ _⟩
    | assign r e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl, _⟩
        exact ⟨⟨0, by simp⟩, Nat.le_add_right _ _⟩
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st <;> cases he : e.eval w st <;> simp [ha, he] at h
      rcases h with ⟨_, rfl, _⟩
      exact ⟨⟨0, by simp⟩, Nat.le_add_right _ _⟩
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨_, rfl, _⟩
      refine ⟨⟨1, by simp⟩, ?_⟩
      have hpow : 1 ≤ 2 ^ (fuel + 1) := Nat.one_le_two_pow
      calc
        st.pos + w = st.pos + w * 1 := by simp
        _ ≤ st.pos + w * 2 ^ (fuel + 1) := by gcongr
    | seq s t =>
      simp only [exec] at h
      cases hs : exec w p ω fuel s st with
      | none => simp [hs] at h
      | some res =>
        rcases res with ⟨o₁, st₁, c₁⟩
        have ⟨⟨k₁, hk₁⟩, hle₁⟩ := exec_pos_bound fuel w p ω s st hs
        cases o₁ with
        | returned v =>
          simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl, _⟩
          have hpow : 2 ^ fuel ≤ 2 ^ (fuel + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ fuel)
          exact ⟨⟨k₁, hk₁⟩, le_trans hle₁ (by gcongr)⟩
        | normal =>
          simp only [hs] at h
          cases ht : exec w p ω fuel t st₁ with
          | none => simp [ht] at h
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨_, rfl, _⟩
            have ⟨⟨k₂, hk₂⟩, hle₂⟩ := exec_pos_bound fuel w p ω t st₁ ht
            refine ⟨⟨k₁ + k₂, ?_⟩, ?_⟩
            · rw [hk₂, hk₁, Nat.add_mul, add_assoc]
            · calc
                st₂.pos ≤ st₁.pos + w * 2 ^ fuel := hle₂
                _ ≤ (st.pos + w * 2 ^ fuel) + w * 2 ^ fuel := by gcongr
                _ = st.pos + w * 2 ^ (fuel + 1) := by
                  rw [Nat.pow_succ]; ring
    | cond e s t =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        cases hc : exec w p ω fuel (if v = 0 then t else s) st with
        | none => simp [hc] at h
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl, _⟩
          have ⟨hk, hle⟩ := exec_pos_bound fuel w p ω (if v = 0 then t else s) st hc
          have hpow : 2 ^ fuel ≤ 2 ^ (fuel + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ fuel)
          exact ⟨hk, le_trans hle (by gcongr)⟩
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        split_ifs at h with hv
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl, _⟩
          exact ⟨⟨0, by simp⟩, Nat.le_add_right _ _⟩
        · cases hb : exec w p ω fuel body st with
          | none => simp [hb] at h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            have ⟨⟨k₁, hk₁⟩, hle₁⟩ := exec_pos_bound fuel w p ω body st hb
            cases o₁ with
            | returned u =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨_, rfl, _⟩
              have hpow : 2 ^ fuel ≤ 2 ^ (fuel + 1) :=
                Nat.pow_le_pow_right (by decide) (Nat.le_succ fuel)
              exact ⟨⟨k₁, hk₁⟩, le_trans hle₁ (by gcongr)⟩
            | normal =>
              simp only [hb] at h
              cases hl : exec w p ω fuel (.loop e body) st₁ with
              | none => simp [hl] at h
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨_, rfl, _⟩
                have ⟨⟨k₂, hk₂⟩, hle₂⟩ := exec_pos_bound fuel w p ω (.loop e body) st₁ hl
                refine ⟨⟨k₁ + k₂, ?_⟩, ?_⟩
                · rw [hk₂, hk₁, Nat.add_mul, add_assoc]
                · calc
                    st₂.pos ≤ st₁.pos + w * 2 ^ fuel := hle₂
                    _ ≤ (st.pos + w * 2 ^ fuel) + w * 2 ^ fuel := by gcongr
                    _ = st.pos + w * 2 ^ (fuel + 1) := by
                      rw [Nat.pow_succ]; ring
    | call r f args =>
      simp only [exec] at h
      cases ha : evalArgs w st args <;> cases hf : p.procs[f]? <;> simp only [ha, hf] at h
      · simp at h
      · simp at h
      · simp at h
      · rename_i vs body
        cases hc : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
        | none => simp only [hc] at h; contradiction
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨_, rfl, _⟩
          have ⟨hk, hle⟩ :=
            exec_pos_bound fuel w p ω body { st with regs := fun i => vs.getD i 0 } hc
          have hpow : 2 ^ fuel ≤ 2 ^ (fuel + 1) :=
            Nat.pow_le_pow_right (by decide) (Nat.le_succ fuel)
          exact ⟨hk, le_trans hle (by gcongr)⟩
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨_, rfl, _⟩
        exact ⟨⟨0, by simp⟩, Nat.le_add_right _ _⟩

private theorem exec_congr_bits :
    ∀ (fuel : ℕ) (w : ℕ) (p : Program) (ω ω' : ℕ → Bool) (s : Stmt) (st : State)
      {o : Outcome} {st' : State} {c : ℕ},
      exec w p ω fuel s st = some (o, st', c) →
      (∀ i, st.pos ≤ i → i < st'.pos → ω' i = ω i) →
      exec w p ω' fuel s st = some (o, st', c)
  | 0, _, _, _, _, _, _, _, _, _, h, _ => by simp [exec] at h
  | fuel + 1, w, p, ω, ω', s, st, o, st', c, h, heq => by
    cases s with
    | nop => simpa [exec] using h
    | assign r e => simpa [exec] using h
    | store a e => simpa [exec] using h
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      have hread : readWord ω' st.pos w = readWord ω st.pos w := by
        apply readWord_congr
        intro i hi₁ hi₂
        dsimp only at heq
        exact heq i hi₁ hi₂
      simp [exec, hread]
    | seq s t =>
      simp only [exec] at h ⊢
      cases hs : exec w p ω fuel s st with
      | none => simp [hs] at h
      | some res =>
        rcases res with ⟨o₁, st₁, c₁⟩
        have ⟨⟨k₁, hk₁⟩, _⟩ := exec_pos_bound fuel w p ω s st hs
        have hle₁ : st.pos ≤ st₁.pos := by omega
        cases o₁ with
        | returned v =>
          simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [exec_congr_bits fuel w p ω ω' s st hs heq]
        | normal =>
          simp only [hs] at h
          cases ht : exec w p ω fuel t st₁ with
          | none => simp [ht] at h
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl⟩
            have ⟨⟨k₂, hk₂⟩, _⟩ := exec_pos_bound fuel w p ω t st₁ ht
            have hle₂ : st₁.pos ≤ st₂.pos := by omega
            have hs' := exec_congr_bits fuel w p ω ω' s st hs
              fun i hi₁ hi₂ => heq i hi₁ (lt_of_lt_of_le hi₂ hle₂)
            have ht' := exec_congr_bits fuel w p ω ω' t st₁ ht
              fun i hi₁ hi₂ => heq i (le_trans hle₁ hi₁) hi₂
            simp only [hs', ht']
    | cond e s t =>
      simp only [exec] at h ⊢
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h ⊢
        cases hc : exec w p ω fuel (if v = 0 then t else s) st with
        | none => simp [hc] at h
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [exec_congr_bits fuel w p ω ω' (if v = 0 then t else s) st hc heq]
    | loop e body =>
      simp only [exec] at h ⊢
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h ⊢
        split_ifs at h ⊢ with hv
        · exact h
        · cases hb : exec w p ω fuel body st with
          | none => simp [hb] at h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            have ⟨⟨k₁, hk₁⟩, _⟩ := exec_pos_bound fuel w p ω body st hb
            have hle₁ : st.pos ≤ st₁.pos := by omega
            cases o₁ with
            | returned u =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              rw [exec_congr_bits fuel w p ω ω' body st hb heq]
            | normal =>
              simp only [hb] at h
              cases hl : exec w p ω fuel (.loop e body) st₁ with
              | none => simp [hl] at h
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [hl, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl, rfl⟩
                have ⟨⟨k₂, hk₂⟩, _⟩ := exec_pos_bound fuel w p ω (.loop e body) st₁ hl
                have hle₂ : st₁.pos ≤ st₂.pos := by omega
                have hb' := exec_congr_bits fuel w p ω ω' body st hb
                  fun i hi₁ hi₂ => heq i hi₁ (lt_of_lt_of_le hi₂ hle₂)
                have hl' := exec_congr_bits fuel w p ω ω' (.loop e body) st₁ hl
                  fun i hi₁ hi₂ => heq i (le_trans hle₁ hi₁) hi₂
                simp only [hb', hl']
    | call r f args =>
      simp only [exec] at h ⊢
      cases ha : evalArgs w st args <;> cases hf : p.procs[f]? <;> simp only [ha, hf] at h ⊢
      · exact h
      · exact h
      · exact h
      · rename_i vs body
        cases hc : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
        | none => simp only [hc] at h; contradiction
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          rw [exec_congr_bits fuel w p ω ω' body { st with regs := fun i => vs.getD i 0 } hc heq]
    | ret e => simpa [exec] using h

private theorem exec_shift :
    ∀ (fuel : ℕ) (w : ℕ) (p : Program) (ω : ℕ → Bool) (q : ℕ) (s : Stmt) (st : State),
      exec w p ω fuel s { st with pos := q + st.pos } =
        (exec w p (fun i => ω (q + i)) fuel s st).map
          (fun r => (r.1, { r.2.1 with pos := q + r.2.1.pos }, r.2.2))
  | 0, _, _, _, _, _, _ => rfl
  | fuel + 1, w, p, ω, q, s, st => by
    cases s with
    | nop => rfl
    | assign r e =>
      simp only [exec, expr_eval_with_pos]
      cases e.eval w st <;> rfl
    | store a e =>
      simp only [exec, expr_eval_with_pos]
      cases a.eval w st <;> cases e.eval w st <;> rfl
    | rand r =>
      simp only [exec, Option.map_some]
      rw [readWord_shift]
      have hpos : q + st.pos + w = q + (st.pos + w) := by omega
      simp [hpos]
    | seq s t =>
      simp only [exec]
      rw [exec_shift fuel w p ω q s st]
      cases exec w p (fun i => ω (q + i)) fuel s st with
      | none => rfl
      | some res =>
        rcases res with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v => rfl
        | normal =>
          dsimp only
          change (match exec w p ω fuel t { st₁ with pos := q + st₁.pos } with
            | none => none
            | some (o, st'', c') => some (o, st'', c₁ + c' + 1)) = _
          rw [exec_shift fuel w p ω q t st₁]
          cases exec w p (fun i => ω (q + i)) fuel t st₁ <;> rfl
    | cond e s t =>
      simp only [exec, expr_eval_with_pos]
      cases e.eval w st with
      | none => rfl
      | some v =>
        dsimp only
        rw [exec_shift fuel w p ω q (if v = 0 then t else s) st]
        cases exec w p (fun i => ω (q + i)) fuel (if v = 0 then t else s) st <;> rfl
    | loop e body =>
      simp only [exec, expr_eval_with_pos]
      cases e.eval w st with
      | none => rfl
      | some v =>
        dsimp only
        split_ifs with hv
        · rfl
        · rw [exec_shift fuel w p ω q body st]
          cases exec w p (fun i => ω (q + i)) fuel body st with
          | none => rfl
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u => rfl
            | normal =>
              dsimp only
              change (match exec w p ω fuel (.loop e body) { st₁ with pos := q + st₁.pos } with
                | none => none
                | some (o, st'', c') => some (o, st'', e.size + c₁ + c' + 1)) = _
              rw [exec_shift fuel w p ω q (.loop e body) st₁]
              cases exec w p (fun i => ω (q + i)) fuel (.loop e body) st₁ <;> rfl
    | call r f args =>
      simp only [exec, evalArgs_with_pos]
      cases ha : evalArgs w st args <;> cases hf : p.procs[f]? <;> try rfl
      rename_i vs body
      simp only []
      have hst : { { st with pos := q + st.pos } with regs := fun i => vs.getD i 0 } =
          { { st with regs := fun i => vs.getD i 0 } with pos := q + st.pos } := rfl
      rw [hst, exec_shift fuel w p ω q body { st with regs := fun i => vs.getD i 0 }]
      cases exec w p (fun i => ω (q + i)) fuel body { st with regs := fun i => vs.getD i 0 } <;> rfl
    | ret e =>
      simp only [exec, expr_eval_with_pos]
      cases e.eval w st <;> rfl

/-- Every run increases `st.pos` by a multiple of the word size `w`. -/
theorem Runs.exists_pos_eq {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c) : ∃ k, st'.pos = st.pos + k * w := by
  obtain ⟨fuel, hfuel⟩ := h
  exact (exec_pos_bound fuel w p ω s st hfuel).1

/-- A run never decreases the bit-stream position `pos`. -/
theorem Runs.pos_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c) : st.pos ≤ st'.pos := by
  obtain ⟨k, hk⟩ := h.exists_pos_eq
  omega

/-- The number of random bits consumed by a run is divisible by the word size `w`. -/
theorem Runs.pos_dvd {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c) : w ∣ st'.pos - st.pos := by
  obtain ⟨k, hk⟩ := h.exists_pos_eq
  exact ⟨k, by rw [hk, Nat.add_sub_cancel_left, Nat.mul_comm]⟩

/-- A run depends only on the bits `ω i` for `st.pos ≤ i < st'.pos`. -/
theorem Runs.congr_bits {w : ℕ} {p : Program} {ω ω' : ℕ → Bool} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c)
    (heq : ∀ i, st.pos ≤ i → i < st'.pos → ω' i = ω i) :
    Runs w p ω' s st o st' c := by
  obtain ⟨fuel, hfuel⟩ := h
  exact ⟨fuel, exec_congr_bits fuel w p ω ω' s st hfuel heq⟩

/-- A run depends only on the tail of the bit stream starting at `st.pos`. -/
theorem Runs.congr_bits_ge {w : ℕ} {p : Program} {ω ω' : ℕ → Bool} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c)
    (heq : ∀ i, st.pos ≤ i → ω' i = ω i) :
    Runs w p ω' s st o st' c :=
  h.congr_bits fun i hi _ => heq i hi

/-- Shifting both the initial and final positions by `q` corresponds to shifting `ω` by `q`. -/
theorem Runs.shift_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {q : ℕ} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω s { st with pos := q + st.pos } o { st' with pos := q + st'.pos } c ↔
      Runs w p (fun i => ω (q + i)) s st o st' c := by
  constructor
  · rintro ⟨fuel, hfuel⟩
    rw [exec_shift fuel w p ω q s st] at hfuel
    cases h : exec w p (fun i => ω (q + i)) fuel s st with
    | none => simp [h] at hfuel
    | some res =>
      rcases res with ⟨o₁, st₁, c₁⟩
      simp only [h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hfuel
      rcases hfuel with ⟨rfl, hst, rfl⟩
      have hmem := congrArg State.mem hst
      have hregs := congrArg State.regs hst
      have hpos := congrArg State.pos hst
      simp only at hmem hregs hpos
      have hpos' : st₁.pos = st'.pos := Nat.add_left_cancel hpos
      have hst_eq : st₁ = st' := by
        cases st₁; cases st'; subst hmem hregs hpos'; rfl
      subst hst_eq
      exact ⟨fuel, h⟩
  · rintro ⟨fuel, hfuel⟩
    refine ⟨fuel, ?_⟩
    rw [exec_shift fuel w p ω q s st, hfuel]
    rfl

/-- Shifting a run from `fun i => ω (q + i)` gives a run from position `q + st.pos` on `ω`. -/
theorem Runs.shift {w : ℕ} {p : Program} {ω : ℕ → Bool} {q : ℕ} {s : Stmt} {st : State}
    {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p (fun i => ω (q + i)) s st o st' c) :
    Runs w p ω s { st with pos := q + st.pos } o { st' with pos := q + st'.pos } c :=
  Runs.shift_iff.mpr h

/-- A single run depends only on the random bits in `[st.pos, st'.pos)`. -/
theorem dependsOn_runs (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (o : Outcome) (st' : State) (c : ℕ) :
    DependsOn {ω | Runs w p ω s st o st' c} (Set.Ico st.pos st'.pos) := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · intro h
    exact h.congr_bits fun i hi₁ hi₂ => (heq i ⟨hi₁, hi₂⟩).symm
  · intro h
    exact h.congr_bits fun i hi₁ hi₂ => heq i ⟨hi₁, hi₂⟩

/-- Any existentially quantified property of runs from `st` depends only on bits `≥ st.pos`. -/
theorem dependsOn_exists_runs (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (P : Outcome → State → ℕ → Prop) :
    DependsOn {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ P o st' c} {i | st.pos ≤ i} := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · rintro ⟨o, st', c, hrun, hp⟩
    exact ⟨o, st', c, hrun.congr_bits_ge fun i hi => (heq i hi).symm, hp⟩
  · rintro ⟨o, st', c, hrun, hp⟩
    exact ⟨o, st', c, hrun.congr_bits_ge fun i hi => heq i hi, hp⟩

/-- `EndsAsContract w p f C args mem pos` depends only on bits `≥ pos`. -/
theorem dependsOn_endsAsContract (w : ℕ) (p : Program) (f : ℕ) (C : Contract)
    (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) :
    DependsOn {ω | EndsAsContract w p f C args mem pos ω} {i | pos ≤ i} := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · rintro ⟨body, hbody, o, st', c, hrun, hpost, hcost⟩
    refine ⟨body, hbody, o, st', c, hrun.congr_bits_ge fun i hi => (heq i hi).symm, hpost, hcost⟩
  · rintro ⟨body, hbody, o, st', c, hrun, hpost, hcost⟩
    refine ⟨body, hbody, o, st', c, hrun.congr_bits_ge fun i hi => heq i hi, hpost, hcost⟩

/-- An existentially quantified property of terminating runs is measurable with respect to `coins`. -/
theorem measurableSet_exists_runs (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (P : Outcome → State → ℕ → Prop) :
    MeasurableSet {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ P o st' c} := by
  have hunion :
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ P o st' c} =
        ⋃ fuel : ℕ, {ω | ∃ o st' c, exec w p ω fuel s st = some (o, st', c) ∧ P o st' c} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Runs]
    constructor
    · rintro ⟨o, st', c, ⟨fuel, hfuel⟩, hp⟩
      exact ⟨fuel, o, st', c, hfuel, hp⟩
    · rintro ⟨fuel, o, st', c, hfuel, hp⟩
      exact ⟨o, st', c, ⟨fuel, hfuel⟩, hp⟩
  rw [hunion]
  refine MeasurableSet.iUnion fun fuel => ?_
  refine measurableSet_of_dependsOn_finite (Finset.finite_toSet (Finset.range (st.pos + w * 2 ^ fuel))) ?_
  intro ω₁ ω₂ heq
  apply propext
  have hhalf : ∀ ωa ωb,
      (∀ i ∈ (↑(Finset.range (st.pos + w * 2 ^ fuel)) : Set ℕ), ωa i = ωb i) →
      (∃ o st' c, exec w p ωa fuel s st = some (o, st', c) ∧ P o st' c) →
      (∃ o st' c, exec w p ωb fuel s st = some (o, st', c) ∧ P o st' c) := by
    rintro ωa ωb hab ⟨o, st', c, hrun, hp⟩
    have ⟨_, hle⟩ := exec_pos_bound fuel w p ωa s st hrun
    refine ⟨o, st', c, exec_congr_bits fuel w p ωa ωb s st hrun ?_, hp⟩
    intro i _ hi₂
    have hi_lt : i < st.pos + w * 2 ^ fuel := lt_of_lt_of_le hi₂ hle
    exact (hab i (Finset.mem_coe.mpr (Finset.mem_range.mpr hi_lt))).symm
  exact ⟨hhalf ω₁ ω₂ heq, hhalf ω₂ ω₁ fun i hi => (heq i hi).symm⟩

/-- A fixed machine run predicate `{ω | Runs w p ω s st o st' c}` is measurable. -/
theorem measurableSet_runs (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (o : Outcome) (st' : State) (c : ℕ) :
    MeasurableSet {ω | Runs w p ω s st o st' c} := by
  have heq : {ω | Runs w p ω s st o st' c} =
      {ω | ∃ o₁ st₁ c₁, Runs w p ω s st o₁ st₁ c₁ ∧ (o₁ = o ∧ st₁ = st' ∧ c₁ = c)} := by
    ext ω
    simp
  rw [heq]
  exact measurableSet_exists_runs w p s st _

/-- `EndsAsContract w p f C args mem pos` is measurable with respect to `coins`. -/
theorem measurableSet_endsAsContract (w : ℕ) (p : Program) (f : ℕ) (C : Contract)
    (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) :
    MeasurableSet {ω | EndsAsContract w p f C args mem pos ω} := by
  cases hf : p.procs[f]? with
  | none =>
    have heq : {ω | EndsAsContract w p f C args mem pos ω} = ∅ := by
      ext ω
      simp [EndsAsContract, hf]
    rw [heq]
    exact MeasurableSet.empty
  | some body =>
    have heq : {ω | EndsAsContract w p f C args mem pos ω} =
        {ω | ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
          C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem} := by
      ext ω
      simp [EndsAsContract, hf]
    rw [heq]
    exact measurableSet_exists_runs w p body (startState args mem pos) _

end WordRAM
