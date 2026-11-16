module

public import WordRAM.Logic

/-!
# Symbolic execution

Tactics that step through a procedure body statement by statement, so that a proof states only
loop invariants, what calls need and give, and the final postcondition and cost.

They work on goals in the forward form of `WordRAM/Logic.lean`,

  `∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T`,

where `k` is the cost of the statements already executed. `wram_enter` reaches this form from a
`MeetsContract` or `Triple` goal.

* `wram_step` executes the first statement of `s`. It evaluates every expression with
  `eval_expr`, so the bounds `x < 2 ^ w` of the arithmetic must follow from the context by
  `omega`. A conditional splits the goal in two, with the test as a hypothesis `hcond`; a branch
  whose test contradicts the context is closed. A call uses a `MeetsContract` hypothesis for the
  called procedure, leaves the callee's precondition as a goal, and continues with its
  postcondition as a hypothesis. Definitions such as loops (`forRange`) and the user's own
  procedures are not unfolded: a loop is executed with `runs_seq_triple_le` and a `Triple` for it.
* `wram_run` repeats `wram_step` in every goal, as long as it applies.
* `wram_cost` proves the remaining cost inequality: it computes the sizes of expressions and
  calls `omega`.

`meetsContract_of_rec` proves the contract of a recursive procedure: each call made by the body
may use the contract for arguments of smaller measure.
-/

@[expose] public section

namespace WordRAM

/-! ### Stepping lemmas -/

/-- A sequence whose first part is a sequence: reassociate. The early-return case costs one
more step, which `k + 1` pays for. -/
theorem runs_seq_assoc_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {a b t : Stmt} {st : State}
    {k T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω (.seq a (.seq b t)) st o st' c ∧ Q o st' ∧ (k + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.seq a b) t) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := h
  rcases runs_seq_iff.mp hr with ⟨v, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩
  · exact ⟨.returned v, st', c₁ + 1 + 1,
      runs_seq_iff.mpr (Or.inl ⟨v, c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨v, c₁, hr₁, rfl, rfl⟩),
        rfl, rfl⟩), hq, by omega⟩
  · rcases runs_seq_iff.mp hr₂ with ⟨v, c₃, hr₃, rfl, rfl⟩ | ⟨st₂, c₃, c₄, hr₃, hr₄, rfl⟩
    · exact ⟨.returned v, st', c₁ + c₃ + 1 + 1,
        runs_seq_iff.mpr (Or.inl ⟨v, c₁ + c₃ + 1,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₃, hr₁, hr₃, rfl⟩), rfl, rfl⟩), hq, by omega⟩
    · exact ⟨o, st', c₁ + c₃ + 1 + c₄ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₂, c₁ + c₃ + 1, c₄,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₃, hr₁, hr₃, rfl⟩), hr₄, rfl⟩), hq, by omega⟩

/-- A conditional at the end of a statement. -/
theorem runs_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω s₁ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω s₂ st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.cond e s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · obtain ⟨o, st', c, hr, hq, hc⟩ := hF hv
    exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩,
      hq, by omega⟩
  · obtain ⟨o, st', c, hr, hq, hc⟩ := hT hv
    exact ⟨o, st', e.size + c + 1, runs_cond_iff.mpr ⟨v, c, he, by simpa [hv] using hr, rfl⟩,
      hq, by omega⟩

/-- A call at the end of a statement, using the callee's contract. -/
theorem runs_call_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {st : State} {vs : List ℕ} {k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C) (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w) (hpre : C.pre vs st.mem)
    (hpost : ∀ v mem' pos', C.post vs st.mem v mem' →
      Q .normal { mem := mem', regs := Function.update st.regs r v, pos := pos' } ∧
        k + argsSize args + C.cost vs st.mem + 1 ≤ T) :
    ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨st', c, v, hrun, hcpost, hr, hother, hcost⟩ :=
    runs_call_of_meetsContract (r := r) hf hargs hwords hpre ω
  have hst' : st' = { mem := st'.mem, regs := Function.update st.regs r v, pos := st'.pos } := by
    cases st'
    dsimp only at hr hother ⊢
    congr 1
    funext r'
    by_cases hr' : r' = r
    · subst hr'; simp [hr]
    · simp [hr', hother r' hr']
  obtain ⟨hq, hc⟩ := hpost v st'.mem st'.pos hcpost
  exact ⟨.normal, st', c, hrun, hst' ▸ hq, by omega⟩

/-! ### Recursive procedures -/

/-- The contract `C` for the calls whose measure `μ args mem` is below `n`. -/
def Contract.below (C : Contract) (μ : List ℕ → (ℕ → ℕ) → ℕ) (n : ℕ) : Contract :=
  { C with pre := fun args mem => C.pre args mem ∧ μ args mem < n }

/-- The contract of a recursive procedure: prove that the body meets `C` on arguments of
measure `n`, assuming that procedure `f` meets `C` on every call of smaller measure. -/
theorem meetsContract_of_rec {w : ℕ} {p : Program} {f : ℕ} {C : Contract} {body : Stmt}
    (μ : List ℕ → (ℕ → ℕ) → ℕ) (hproc : p.procs[f]? = some body)
    (hbody : ∀ n, MeetsContract w p f (C.below μ n) →
      ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem → μ args mem = n →
        ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
          C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem) :
    MeetsContract w p f C := by
  have hall : ∀ n, MeetsContract w p f (C.below μ n) := by
    intro n
    induction n with
    | zero =>
      intro _ _ _ _ _ hpre
      exact absurd hpre.2 (Nat.not_lt_zero _)
    | succ n ih =>
      refine meetsContract_of_runs hproc fun args mem pos ω hw hpre => ?_
      have ih' : MeetsContract w p f (C.below μ (μ args mem)) :=
        fun args' mem' pos' ω' hw' hpre' =>
          ih args' mem' pos' ω' hw' ⟨hpre'.1, by have := hpre.2; have := hpre'.2; omega⟩
      exact hbody _ ih' args mem pos ω hw hpre.1 rfl
  intro args mem pos ω hw hpre
  exact hall (μ args mem + 1) args mem pos ω hw ⟨hpre, Nat.lt_succ_self _⟩

/-! ### Tactics -/

/-- Prove `∀ v ∈ [x₁, …, xₙ], v < 2 ^ w` from bounds in the context. -/
syntax "wram_words" : tactic
macro_rules
  | `(tactic| wram_words) =>
    `(tactic| (simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq, imp_false, not_false_eq_true, implies_true, and_true]; omega))

/-- After a conditional, turn the test value into the test, and close the branch if the test
contradicts the context. -/
syntax "wram_branch" : tactic
macro_rules
  | `(tactic| wram_branch) =>
    `(tactic| (intro $(Lean.mkIdent `hcond):ident;
               (try simp only [ne_eq, ite_eq_right_iff, ite_eq_left_iff, one_ne_zero,
                 zero_ne_one, imp_false, Decidable.not_not, not_true_eq_false,
                 not_false_eq_true] at $(Lean.mkIdent `hcond):ident);
               try (exfalso; omega)))

open Lean Meta Elab Tactic in
/-- Fail unless the goal has the form `∃ o st' c, Runs w p ω s st o st' c ∧ _`, so that
`wram_step` leaves other goals alone. -/
elab "wram_guard" : tactic => do
  let rec peel : ℕ → Lean.Expr → MetaM Bool
    | 0, e => do
      match (← whnfR e).and? with
      | some (lhs, _) => return lhs.isAppOf ``WordRAM.Runs
      | none => return false
    | k + 1, e => do
      match (← whnfR e).app2? ``Exists with
      | some (_, .lam n ty b bi) =>
        withLocalDecl n bi ty fun x => peel k (b.instantiate1 x)
      | _ => return false
  unless ← peel 3 (← getMainTarget) do
    throwError "wram_guard: the goal is not a forward execution goal"

/-- Execute the first statement of the program in a goal
`∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T`. -/
syntax "wram_step" : tactic
macro_rules
  | `(tactic| wram_step) =>
    `(tactic|
      wram_guard;
      first
      | with_reducible refine runs_seq_assoc_le ?_
      | with_reducible refine runs_seq_nop_le ?_
      | with_reducible refine runs_seq_assign_le (by eval_expr) ?_
      | with_reducible refine runs_seq_store_le (by eval_expr) (by eval_expr) ?_
      | (with_reducible refine runs_seq_cond_le (by eval_expr) ?_ ?_) <;> wram_branch
      | ((with_reducible apply runs_seq_call_le); (focus assumption); (focus eval_expr);
         try (focus wram_words))
      | with_reducible refine runs_nop_le ?_ ?_
      | with_reducible refine runs_assign_le (by eval_expr) ?_ ?_
      | with_reducible refine runs_store_le (by eval_expr) (by eval_expr) ?_ ?_
      | with_reducible refine runs_ret_le (by eval_expr) ?_ ?_
      | (with_reducible refine runs_cond_le (by eval_expr) ?_ ?_) <;> wram_branch
      | ((with_reducible apply runs_call_le); (focus assumption); (focus eval_expr);
         try (focus wram_words)))

/-- Execute statements with `wram_step`, in every goal, as long as one applies. -/
syntax "wram_run" : tactic
macro_rules
  | `(tactic| wram_run) => `(tactic| repeat (any_goals wram_step))

/-- Prove a cost inequality left by `wram_step`: compute expression sizes, then `omega`. -/
syntax "wram_cost" : tactic
macro_rules
  | `(tactic| wram_cost) =>
    `(tactic| (simp only [Expr.size_const, Expr.size_reg, Expr.size_load, Expr.size_bin,
        argsSize_cons, argsSize_nil] at *; omega))

/-- Turn a `Triple` goal into the forward form, for a state `st` and random bits `ω` with the
precondition `hpre`. -/
syntax "wram_enter" : tactic
macro_rules
  | `(tactic| wram_enter) =>
    `(tactic| (intro $(Lean.mkIdent `st):ident $(Lean.mkIdent `ω):ident
                 $(Lean.mkIdent `hpre):ident; refine runs_start_le ?_))

end WordRAM
