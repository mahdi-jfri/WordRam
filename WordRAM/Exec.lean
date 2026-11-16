module

public import WordRAM.Contract

/-!
# Basic properties of `exec` and `Runs`

This file proves the core operational properties of the word RAM evaluator `exec` and the
big-step predicate `Runs`:

* `exec_fuel_mono`: increasing fuel preserves successful `exec` evaluations.
* `Runs.det`: `Runs` is deterministic (outcome, final state, and cost are unique).
* `runs_nop_iff`, `runs_assign_iff`, `runs_store_iff`, `runs_rand_iff`, `runs_seq_iff`,
  `runs_cond_iff`, `runs_loop_iff`, `runs_call_iff`, `runs_ret_iff`: exact structural
  characterizations of `Runs` for each statement constructor.
* `runs_call_of_meetsContract`: executing `Stmt.call` on a procedure satisfying `MeetsContract`.
-/

public section

namespace WordRAM

/-- Increasing fuel preserves any terminating `exec` result. -/
theorem exec_fuel_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {f f' : ℕ}
    {s : Stmt} {st : State} {r : Outcome × State × ℕ}
    (h : exec w p ω f s st = some r) (hle : f ≤ f') :
    exec w p ω f' s st = some r := by
  induction f generalizing f' s st r with
  | zero => simp [exec] at h
  | succ f ih =>
    cases f' with
    | zero => omega
    | succ f' =>
      have hle' : f ≤ f' := Nat.le_of_succ_le_succ hle
      cases s with
      | nop => simpa [exec] using h
      | assign reg e => simpa [exec] using h
      | store a e => simpa [exec] using h
      | rand reg => simpa [exec] using h
      | seq s₁ s₂ =>
        simp only [exec] at h ⊢
        cases hs₁ : exec w p ω f s₁ st with
        | none => simp [hs₁] at h
        | some res₁ =>
          rw [ih hs₁ hle']
          rcases res₁ with ⟨o₁, st₁, c₁⟩
          cases o₁ with
          | returned v => simpa [hs₁] using h
          | normal =>
            simp only [hs₁] at h ⊢
            cases hs₂ : exec w p ω f s₂ st₁ with
            | none => simp [hs₂] at h
            | some res₂ =>
              rw [ih hs₂ hle']
              simpa [hs₂] using h
      | cond e s₁ s₂ =>
        simp only [exec] at h ⊢
        cases he : e.eval w st with
        | none => simp [he] at h
        | some v =>
          simp only [he] at h ⊢
          cases hbr : exec w p ω f (if v = 0 then s₂ else s₁) st with
          | none => simp [hbr] at h
          | some res =>
            rw [ih hbr hle']
            simpa [hbr] using h
      | loop e body =>
        simp only [exec] at h ⊢
        cases he : e.eval w st with
        | none => simp [he] at h
        | some v =>
          simp only [he] at h ⊢
          by_cases hv : v = 0
          · simpa [hv] using h
          · simp only [hv, ↓reduceIte] at h ⊢
            cases hbody : exec w p ω f body st with
            | none => simp [hbody] at h
            | some res₁ =>
              rw [ih hbody hle']
              rcases res₁ with ⟨o₁, st₁, c₁⟩
              cases o₁ with
              | returned u => simpa [hbody] using h
              | normal =>
                simp only [hbody] at h ⊢
                cases hloop : exec w p ω f (.loop e body) st₁ with
                | none => simp [hloop] at h
                | some res₂ =>
                  rw [ih hloop hle']
                  simpa [hloop] using h
      | call reg fn args =>
        simp only [exec] at h ⊢
        cases hargs : evalArgs w st args with
        | none => simp [hargs] at h
        | some vs =>
          cases hproc : p.procs[fn]? with
          | none => simp [hargs, hproc] at h
          | some body =>
            simp only [hargs, hproc] at h ⊢
            cases hbody : exec w p ω f body { st with regs := fun i => vs.getD i 0 } with
            | none => simp only [hbody] at h; cases h
            | some res =>
              rw [ih hbody hle']
              simpa only [hbody] using h
      | ret e => simpa [exec] using h

/-- Every terminating `exec` has positive cost. -/
theorem exec_cost_pos {w : ℕ} {p : Program} {ω : ℕ → Bool} {f : ℕ}
    {s : Stmt} {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : exec w p ω f s st = some (o, st', c)) : 1 ≤ c := by
  cases f with
  | zero => simp [exec] at h
  | succ f =>
    cases s with
    | nop => simp [exec] at h; omega
    | assign reg e =>
      simp only [exec] at h
      cases he : e.eval w st <;> simp [he] at h
      omega
    | store a e =>
      simp only [exec] at h
      cases ha : a.eval w st <;> cases he : e.eval w st <;> simp [ha, he] at h
      omega
    | rand reg => simp [exec] at h; omega
    | seq s₁ s₂ =>
      simp only [exec] at h
      cases hs₁ : exec w p ω f s₁ st with
      | none => simp [hs₁] at h
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v => simp [hs₁] at h; omega
        | normal =>
          simp only [hs₁] at h
          cases hs₂ : exec w p ω f s₂ st₁ with
          | none => simp [hs₂] at h
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp [hs₂] at h
            omega
    | cond e s₁ s₂ =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        cases hbr : exec w p ω f (if v = 0 then s₂ else s₁) st with
        | none => simp [hbr] at h
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp [hbr] at h
          omega
    | loop e body =>
      simp only [exec] at h
      cases he : e.eval w st with
      | none => simp [he] at h
      | some v =>
        simp only [he] at h
        by_cases hv : v = 0
        · simp [hv] at h; omega
        · simp only [hv, ↓reduceIte] at h
          cases hbody : exec w p ω f body st with
          | none => simp [hbody] at h
          | some res₁ =>
            rcases res₁ with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u => simp [hbody] at h; omega
            | normal =>
              simp only [hbody] at h
              cases hloop : exec w p ω f (.loop e body) st₁ with
              | none => simp [hloop] at h
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp [hloop] at h
                omega
    | call reg fn args =>
      simp only [exec] at h
      cases hargs : evalArgs w st args with
      | none => simp [hargs] at h
      | some vs =>
        cases hproc : p.procs[fn]? with
        | none => simp [hargs, hproc] at h
        | some body =>
          simp only [hargs, hproc] at h
          cases hbody : exec w p ω f body { st with regs := fun i => vs.getD i 0 } with
          | none => simp only [hbody] at h; cases h
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [hbody, Option.some.injEq, Prod.mk.injEq] at h
            omega
    | ret e =>
      simp only [exec] at h
      cases he : e.eval w st <;> simp [he] at h
      omega

/-- Every `Runs` has positive cost. -/
theorem Runs.cost_pos {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {s : Stmt} {st : State} {o : Outcome} {st' : State} {c : ℕ}
    (h : Runs w p ω s st o st' c) : 1 ≤ c := by
  rcases h with ⟨_, hf⟩
  exact exec_cost_pos hf

/-- `Runs` is deterministic: the outcome, final state, and cost are uniquely determined. -/
theorem Runs.det {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {o₁ o₂ : Outcome} {st₁ st₂ : State} {c₁ c₂ : ℕ}
    (h₁ : Runs w p ω s st o₁ st₁ c₁) (h₂ : Runs w p ω s st o₂ st₂ c₂) :
    o₁ = o₂ ∧ st₁ = st₂ ∧ c₁ = c₂ := by
  rcases h₁ with ⟨f₁, hf₁⟩
  rcases h₂ with ⟨f₂, hf₂⟩
  have h₁' := exec_fuel_mono hf₁ (Nat.le_max_left f₁ f₂)
  have h₂' := exec_fuel_mono hf₂ (Nat.le_max_right f₁ f₂)
  rw [h₁'] at h₂'
  cases h₂'
  exact ⟨rfl, rfl, rfl⟩

/-- Characterization of `Runs` for `Stmt.nop`. -/
theorem runs_nop_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω .nop st o st' c ↔ o = .normal ∧ st' = st ∧ c = 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hf
      exact ⟨hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨1, rfl⟩

/-- Characterization of `Runs` for `Stmt.assign`. -/
theorem runs_assign_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.assign r e) st o st' c ↔
      ∃ v, e.eval w st = some v ∧
        o = .normal ∧ st' = { st with regs := Function.update st.regs r v } ∧ c = e.size + 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases he : e.eval w st with
      | none => simp [he] at hf
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hf
        exact ⟨v, rfl, hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
  · rintro ⟨v, he, rfl, rfl, rfl⟩
    exact ⟨1, by simp [exec, he]⟩

/-- Characterization of `Runs` for `Stmt.store`. -/
theorem runs_store_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.store a e) st o st' c ↔
      ∃ x v, a.eval w st = some x ∧ e.eval w st = some v ∧
        o = .normal ∧ st' = { st with mem := Function.update st.mem x v } ∧
        c = a.size + e.size + 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases ha : a.eval w st with
      | none => simp [ha] at hf
      | some x =>
        cases he : e.eval w st with
        | none => simp [ha, he] at hf
        | some v =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at hf
          exact ⟨x, v, rfl, rfl, hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
  · rintro ⟨x, v, ha, he, rfl, rfl, rfl⟩
    exact ⟨1, by simp [exec, ha, he]⟩

/-- Characterization of `Runs` for `Stmt.rand`. -/
theorem runs_rand_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.rand r) st o st' c ↔
      o = .normal ∧
      st' = { st with regs := Function.update st.regs r (readWord ω st.pos w), pos := st.pos + w } ∧
      c = 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hf
      exact ⟨hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨1, rfl⟩

/-- Characterization of `Runs` for `Stmt.seq`. -/
theorem runs_seq_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.seq s t) st o st' c ↔
      (∃ v c₁, Runs w p ω s st (.returned v) st' c₁ ∧ o = .returned v ∧ c = c₁ + 1) ∨
      (∃ st₁ c₁ c₂, Runs w p ω s st .normal st₁ c₁ ∧ Runs w p ω t st₁ o st' c₂ ∧
        c = c₁ + c₂ + 1) := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases hs : exec w p ω f s st with
      | none => simp [hs] at hf
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v =>
          simp only [hs, Option.some.injEq, Prod.mk.injEq] at hf
          refine Or.inl ⟨v, c₁, ?_, hf.1.symm, hf.2.2.symm⟩
          rw [← hf.2.1]
          exact ⟨f, hs⟩
        | normal =>
          simp only [hs] at hf
          cases ht : exec w p ω f t st₁ with
          | none => simp [ht] at hf
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [ht, Option.some.injEq, Prod.mk.injEq] at hf
            refine Or.inr ⟨st₁, c₁, c₂, ⟨f, hs⟩, ?_, hf.2.2.symm⟩
            rw [← hf.1, ← hf.2.1]
            exact ⟨f, ht⟩
  · rintro (⟨v, c₁, ⟨f₁, hf₁⟩, rfl, rfl⟩ | ⟨st₁, c₁, c₂, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩, rfl⟩)
    · exact ⟨f₁ + 1, by simp [exec, hf₁]⟩
    · refine ⟨max f₁ f₂ + 1, ?_⟩
      have hf₁' := exec_fuel_mono hf₁ (Nat.le_max_left f₁ f₂)
      have hf₂' := exec_fuel_mono hf₂ (Nat.le_max_right f₁ f₂)
      simp [exec, hf₁', hf₂']

/-- Characterization of `Runs` for `Stmt.cond`. -/
theorem runs_cond_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s t : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.cond e s t) st o st' c ↔
      ∃ v c₁, e.eval w st = some v ∧
        Runs w p ω (if v = 0 then t else s) st o st' c₁ ∧
        c = e.size + c₁ + 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases he : e.eval w st with
      | none => simp [he] at hf
      | some v =>
        simp only [he] at hf
        cases hbr : exec w p ω f (if v = 0 then t else s) st with
        | none => simp [hbr] at hf
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hbr, Option.some.injEq, Prod.mk.injEq] at hf
          refine ⟨v, c₁, rfl, ?_, hf.2.2.symm⟩
          rw [← hf.1, ← hf.2.1]
          exact ⟨f, hbr⟩
  · rintro ⟨v, c₁, he, ⟨f, hf⟩, rfl⟩
    exact ⟨f + 1, by simp [exec, he, hf]⟩

/-- Characterization of `Runs` for `Stmt.loop` (one unfolding). -/
theorem runs_loop_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {body : Stmt}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.loop e body) st o st' c ↔
      (e.eval w st = some 0 ∧ o = .normal ∧ st' = st ∧ c = e.size + 1) ∨
      (∃ v u c₁, e.eval w st = some v ∧ v ≠ 0 ∧
        Runs w p ω body st (.returned u) st' c₁ ∧ o = .returned u ∧ c = e.size + c₁ + 1) ∨
      (∃ v st₁ c₁ c₂, e.eval w st = some v ∧ v ≠ 0 ∧
        Runs w p ω body st .normal st₁ c₁ ∧ Runs w p ω (.loop e body) st₁ o st' c₂ ∧
        c = e.size + c₁ + c₂ + 1) := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases he : e.eval w st with
      | none => simp [he] at hf
      | some v =>
        simp only [he] at hf
        by_cases hv : v = 0
        · subst hv
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hf
          exact Or.inl ⟨rfl, hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
        · simp only [hv, ↓reduceIte] at hf
          cases hbody : exec w p ω f body st with
          | none => simp [hbody] at hf
          | some res₁ =>
            rcases res₁ with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u =>
              simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hf
              refine Or.inr (Or.inl ⟨v, u, c₁, rfl, hv, ?_, hf.1.symm, hf.2.2.symm⟩)
              rw [← hf.2.1]
              exact ⟨f, hbody⟩
            | normal =>
              simp only [hbody] at hf
              cases hloop : exec w p ω f (.loop e body) st₁ with
              | none => simp [hloop] at hf
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [hloop, Option.some.injEq, Prod.mk.injEq] at hf
                refine Or.inr (Or.inr ⟨v, st₁, c₁, c₂, rfl, hv, ⟨f, hbody⟩, ?_, hf.2.2.symm⟩)
                rw [← hf.1, ← hf.2.1]
                exact ⟨f, hloop⟩
  · rintro (⟨he, rfl, rfl, rfl⟩ | ⟨v, u, c₁, he, hv, ⟨f, hf⟩, rfl, rfl⟩ |
        ⟨v, st₁, c₁, c₂, he, hv, ⟨f₁, hf₁⟩, ⟨f₂, hf₂⟩, rfl⟩)
    · exact ⟨1, by simp [exec, he]⟩
    · exact ⟨f + 1, by simp [exec, he, hv, hf]⟩
    · refine ⟨max f₁ f₂ + 1, ?_⟩
      have hf₁' := exec_fuel_mono hf₁ (Nat.le_max_left f₁ f₂)
      have hf₂' := exec_fuel_mono hf₂ (Nat.le_max_right f₁ f₂)
      simp [exec, he, hv, hf₁', hf₂']

/-- Characterization of `Runs` for `Stmt.call`. -/
theorem runs_call_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.call r f args) st o st' c ↔
      ∃ vs body o₁ st₁ c₁,
        evalArgs w st args = some vs ∧
        p.procs[f]? = some body ∧
        Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁ ∧
        o = .normal ∧
        st' = { st₁ with regs := Function.update st.regs r o₁.value } ∧
        c = argsSize args + c₁ + 1 := by
  constructor
  · rintro ⟨fuel, hf⟩
    cases fuel with
    | zero => simp [exec] at hf
    | succ fuel =>
      simp only [exec] at hf
      cases hargs : evalArgs w st args with
      | none => simp [hargs] at hf
      | some vs =>
        cases hproc : p.procs[f]? with
        | none => simp [hargs, hproc] at hf
        | some body =>
          simp only [hargs, hproc] at hf
          change (match exec w p ω fuel body (startState vs st.mem st.pos) with
            | none => none
            | some (o_1, st', c) =>
              some (Outcome.normal, { st' with regs := Function.update st.regs r o_1.value },
                argsSize args + c + 1)) = some (o, st', c) at hf
          cases hbody : exec w p ω fuel body (startState vs st.mem st.pos) with
          | none => simp [hbody] at hf
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hf
            refine ⟨vs, body, o₁, st₁, c₁, rfl, rfl, ⟨fuel, hbody⟩, hf.1.symm, ?_, hf.2.2.symm⟩
            rw [← hf.2.1]
  · rintro ⟨vs, body, o₁, st₁, c₁, hargs, hproc, ⟨fuel, hbody⟩, rfl, rfl, rfl⟩
    refine ⟨fuel + 1, ?_⟩
    have hbody' : exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } =
        some (o₁, st₁, c₁) := hbody
    simp only [exec, hargs, hproc, hbody']
    cases o₁ <;> rfl

/-- Characterization of `Runs` for `Stmt.ret`. -/
theorem runs_ret_iff {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {st : State} {o : Outcome} {st' : State} {c : ℕ} :
    Runs w p ω (.ret e) st o st' c ↔
      ∃ v, e.eval w st = some v ∧ o = .returned v ∧ st' = st ∧ c = e.size + 1 := by
  constructor
  · rintro ⟨f, hf⟩
    cases f with
    | zero => simp [exec] at hf
    | succ f =>
      simp only [exec] at hf
      cases he : e.eval w st with
      | none => simp [he] at hf
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hf
        exact ⟨v, rfl, hf.1.symm, hf.2.1.symm, hf.2.2.symm⟩
  · rintro ⟨v, he, rfl, rfl, rfl⟩
    exact ⟨1, by simp [exec, he]⟩

/-- Evaluating an expression on a state whose registers and memory hold words yields a word. -/
theorem Expr.eval_lt {w : ℕ} {st : State} {e : Expr} {v : ℕ}
    (hregs : ∀ r, st.regs r < 2 ^ w) (hmem : ∀ a, st.mem a < 2 ^ w)
    (he : e.eval w st = some v) : v < 2 ^ w := by
  induction e generalizing v with
  | const k =>
    simp only [Expr.eval] at he
    split_ifs at he with hk
    cases he
    exact hk
  | reg r =>
    simp only [Expr.eval, Option.some.injEq] at he
    subst he
    exact hregs r
  | load a _ =>
    simp only [Expr.eval, Option.map_eq_some_iff] at he
    rcases he with ⟨x, _, rfl⟩
    exact hmem x
  | bin op a b _ _ =>
    simp only [Expr.eval] at he
    cases ha : a.eval w st <;> cases hb : b.eval w st <;> simp [ha, hb] at he
    exact he.2 ▸ he.1

/-- Evaluating argument expressions on a state whose registers and memory hold words yields words. -/
theorem evalArgs_lt {w : ℕ} {st : State} {args : List Expr} {vs : List ℕ}
    (hregs : ∀ r, st.regs r < 2 ^ w) (hmem : ∀ a, st.mem a < 2 ^ w)
    (hargs : evalArgs w st args = some vs) : ∀ v ∈ vs, v < 2 ^ w := by
  induction args generalizing vs with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at hargs
    subst hargs
    intro _ hmem
    cases hmem
  | cons e es ih =>
    simp only [evalArgs] at hargs
    cases he : e.eval w st <;> cases hes : evalArgs w st es <;> simp [he, hes] at hargs
    subst hargs
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact Expr.eval_lt hregs hmem he
    · exact ih hes v hv'

/-- Running `Stmt.call` on a procedure that meets contract `C` succeeds with the contracted
postcondition, register update, and cost bound. -/
theorem runs_call_of_meetsContract {w : ℕ} {p : Program}
    {r f : ℕ} {args : List Expr} {C : Contract} {st : State} {vs : List ℕ}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem) :
    ∀ ω, ∃ st' c v,
      Runs w p ω (.call r f args) st .normal st' c ∧
      C.post vs st.mem v st'.mem ∧
      st'.regs r = v ∧
      (∀ r', r' ≠ r → st'.regs r' = st.regs r') ∧
      c ≤ argsSize args + C.cost vs st.mem + 1 := by
  intro ω
  rcases hf vs st.mem st.pos ω hwords hpre with
    ⟨body, hproc, o₁, st₁, c₁, hrun_body, hpost, hcost⟩
  refine ⟨{ st₁ with regs := Function.update st.regs r o₁.value },
    argsSize args + c₁ + 1, o₁.value, ?_, hpost, ?_, ?_, ?_⟩
  · exact runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hrun_body, rfl, rfl, rfl⟩
  · simp
  · intro r' hr'
    simp [hr']
  · omega

end WordRAM
