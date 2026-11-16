module

public import WordRAM.Exec
public import WordRAM.Expr
public import WordRAM.Memory

/-!
# Program logic with cost bounds for Word-RAM programs

This file defines a Hoare-style triple `Triple` with explicit upper bounds on execution cost,
structured rules for all `Stmt` constructors, general and counter-based loop rules, forward
sequence-stepping lemmas (`runs_seq_*_le`) that accumulate prefix cost without `ℕ` subtraction, and
bridges (`meetsContract_of_triple`, `meetsContract_of_runs`) to `MeetsContract`.

## How to prove a procedure

Suppose you want to verify a procedure body `myProc : Stmt` placed in a program `p` via `Program.HasAt`
against a `Contract`.

1. **Specify the contract.** Define a `Contract` with `pre args mem`, `post args mem v mem'`, and
   `cost args mem`. Usually `pre` specifies argument-list shape (`args = [...]`), memory layout
   (`ListAt`, `ZeroFrom`), and word-size bounds (`< 2 ^ w`).
2. **Enter the procedure body.** Use `meetsContract_of_runs` (together with `p.HasAt.get`) to turn
   `MeetsContract w p f C` into a goal of the form
   `∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧ C.post ... ∧ c ≤ C.cost ...`.
   Alternatively, use `meetsContract_of_triple` together with `Triple` rules.
3. **Step through straight-line code.** Replace `c ≤ T` by `0 + c ≤ T` (`runs_start_le` or
   `runs_triple_le`), then apply `runs_seq_assign_le`, `runs_seq_store_le`, `runs_seq_nop_le`,
   `runs_seq_rand_le`, `runs_seq_cond_le`, and `runs_seq_call_le` in sequence, finishing with
   `runs_ret_le` (or another terminal `runs_*_le` lemma). Each step uses `eval_expr` to evaluate
   subexpressions and accumulate the prefix cost `k` monotonically.
4. **Verify loops modularly.** Prove a `Triple` for each loop separately using `Triple.forUp` /
   `Triple.forUp_le` / `Triple.forRange_le` / `Triple.forRange_const` (for counter loops from
   `lo` to `hi`, with `rangeCost` or a uniform per-step bound), `Triple.loop_measure` (for
   arbitrary decreasing measure and potential function), `Triple.loop_const`, `Triple.loop_inv`,
   or `Triple.loop_list`. Then splice the loop into a larger sequence with `runs_seq_triple_le`
   (or `Triple.seq_normal`).
5. **Preserve memory frames.** Use `ListAt.update_outside`, `ListAt.update_lt`, `ListAt.update_ge`,
   `ListAt.set`, `ZeroFrom.update_lt`, `ZeroFrom.update_head`, and `ZeroFrom.update_zero` from
   `WordRAM.Memory`.

### Small complete example

```lean
open WordRAM

@[expose] def fillZero : Stmt :=
  forRange 2 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)) ;;
  .ret (.bin .add (.reg 0) (.reg 1))

def fillZeroContract : Contract where
  pre args _ := ∃ a len, args = [a, len]
  post args mem v mem' :=
    ∃ a len, args = [a, len] ∧ v = a + len ∧
      ListAt mem' a (List.replicate len 0) ∧ ∀ x, x < a ∨ a + len ≤ x → mem' x = mem x
  cost args _ := match args with | [_, len] => 14 * len + 12 | _ => 0

def fillZeroPre (w : ℕ) (args : List ℕ) (_mem : ℕ → ℕ) : Prop :=
  ∃ a len, args = [a, len] ∧ 1 < 2 ^ w ∧ a + len < 2 ^ w

theorem fillZeroBodyTriple {w a len : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2 ^ w) (hbound : a + len < 2 ^ w) :
    Triple w p (fun st => st = startState [a, len] mem₀ pos)
      (forRange 2 (.const 0) (.reg 1) (.store (.bin .add (.reg 0) (.reg 2)) (.const 0)))
      (normalPost fun st' => st'.regs 0 = a ∧ st'.regs 1 = len ∧
        ListAt st'.mem a (List.replicate len 0) ∧
        ∀ x, x < a ∨ a + len ≤ x → st'.mem x = mem₀ x)
      (fun _ => 14 * len + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 2) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 0) (.reg 2)) (.const 0))
    (P := fun st => st = startState [a, len] mem₀ pos)
    (Inv := fun i st => st.regs 0 = a ∧ st.regs 1 = len ∧ st.regs 2 = i ∧
      ListAt st.mem a (List.replicate i 0) ∧ ∀ x, x < a ∨ a + i ≤ x → st.mem x = mem₀ x)
    5 0 len (Nat.zero_le len) hw (fun _ => by omega)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, listAt_nil _ _, fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = len := hi.2.1
      eval_expr)
    (fun i hi₀ hilt => by
      intro st ω hst
      rcases hst with ⟨h0, h1, h2, hlist, hframe⟩
      refine ⟨.normal, { st with mem := Function.update st.mem (a + i) 0 }, 5, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr ⟨a + i, 0, by eval_expr, by eval_expr, rfl, rfl, by simp⟩
      · refine ⟨⟨h0, h1, by simp, ?_, ?_⟩, h2⟩
        · rw [List.replicate_succ']
          simpa [List.length_replicate] using hlist.snoc 0
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned u => exact False.elim h
    | normal => exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

theorem fillZero_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [fillZero]) :
    MeetsContract w p b ⟨fillZeroPre w, fillZeroContract.post, fillZeroContract.cost⟩ := by
  refine meetsContract_of_runs hp.head fun args mem pos ω _ hpre => ?_
  rcases hpre with ⟨a, len, rfl, hw, hbound⟩
  refine runs_start_le ?_
  dsimp only [fillZero]
  refine runs_seq_triple_le (fillZeroBodyTriple p mem pos hw hbound) rfl ?_
  intro st₁ ⟨h0, h1, hlist, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨a, len, rfl, rfl, hlist, hframe⟩ ?_
  dsimp [fillZeroContract]
  omega
```
-/

public section

namespace WordRAM

/-- Sequential composition shorthand for machine statements. -/
scoped infixr:40 " ;; " => Stmt.seq

private theorem readWord_lt_pow (ω : ℕ → Bool) (pos w : ℕ) :
    readWord ω pos w < 2 ^ w := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih =>
    have hrest := ih (pos + 1)
    simp only [readWord, pow_succ']
    split_ifs <;> omega

/-! ### Postconditions and costed Hoare triples -/

/-- Postcondition requiring normal termination with final state satisfying `Q`. -/
@[expose] def normalPost (Q : State → Prop) : Outcome → State → Prop
  | .normal, st => Q st
  | .returned _, _ => False

@[simp] theorem normalPost_normal (Q : State → Prop) (st : State) :
    normalPost Q .normal st ↔ Q st := Iff.rfl

@[simp] theorem normalPost_returned (Q : State → Prop) (v : ℕ) (st : State) :
    normalPost Q (.returned v) st ↔ False := Iff.rfl

/-- Postcondition requiring return (`ret`) with value and final state satisfying `Q`. -/
@[expose] def retPost (Q : ℕ → State → Prop) : Outcome → State → Prop
  | .normal, _ => False
  | .returned v, st => Q v st

@[simp] theorem retPost_normal (Q : ℕ → State → Prop) (st : State) :
    retPost Q .normal st ↔ False := Iff.rfl

@[simp] theorem retPost_returned (Q : ℕ → State → Prop) (v : ℕ) (st : State) :
    retPost Q (.returned v) st ↔ Q v st := Iff.rfl

/-- A total-correctness and cost triple for `Stmt`: from any state satisfying `P`, and for every
random tape `ω`, executing `s` at word size `w` in program `p` terminates in some outcome `o` and
state `st'` satisfying `Q o st'` with total cost at most `T st`. -/
@[expose] def Triple (w : ℕ) (p : Program) (P : State → Prop) (s : Stmt)
    (Q : Outcome → State → Prop) (T : State → ℕ) : Prop :=
  ∀ st ω, P st → ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ c ≤ T st

theorem Triple.runs {w : ℕ} {p : Program} {P : State → Prop} {s : Stmt}
    {Q : Outcome → State → Prop} {T : State → ℕ}
    (ht : Triple w p P s Q T) {st : State} (ω : ℕ → Bool) (hP : P st) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ c ≤ T st :=
  ht st ω hP

/-! ### Structural rules -/

theorem Triple.conseq {w : ℕ} {p : Program}
    {P P' : State → Prop} {s : Stmt} {Q Q' : Outcome → State → Prop} {T T' : State → ℕ}
    (ht : Triple w p P s Q T)
    (hP : ∀ st, P' st → P st)
    (hQ : ∀ o st', Q o st' → Q' o st')
    (hT : ∀ st, P' st → T st ≤ T' st) :
    Triple w p P' s Q' T' := by
  intro st ω hP'
  rcases ht st ω (hP st hP') with ⟨o, st', c, hrun, hq, hc⟩
  exact ⟨o, st', c, hrun, hQ o st' hq, Nat.le_trans hc (hT st hP')⟩

theorem Triple.weaken_pre {w : ℕ} {p : Program}
    {P P' : State → Prop} {s : Stmt} {Q : Outcome → State → Prop} {T : State → ℕ}
    (ht : Triple w p P s Q T) (hP : ∀ st, P' st → P st) :
    Triple w p P' s Q T :=
  ht.conseq hP (fun _ _ h => h) (fun _ _ => Nat.le_refl _)

theorem Triple.strengthen_post {w : ℕ} {p : Program}
    {P : State → Prop} {s : Stmt} {Q Q' : Outcome → State → Prop} {T : State → ℕ}
    (ht : Triple w p P s Q T) (hQ : ∀ o st', Q o st' → Q' o st') :
    Triple w p P s Q' T :=
  ht.conseq (fun _ h => h) hQ (fun _ _ => Nat.le_refl _)

theorem Triple.mono_cost {w : ℕ} {p : Program}
    {P : State → Prop} {s : Stmt} {Q : Outcome → State → Prop} {T T' : State → ℕ}
    (ht : Triple w p P s Q T) (hT : ∀ st, P st → T st ≤ T' st) :
    Triple w p P s Q T' :=
  ht.conseq (fun _ h => h) (fun _ _ h => h) hT

theorem Triple.pure_pre {w : ℕ} {p : Program} {φ : Prop}
    {P : State → Prop} {s : Stmt} {Q : Outcome → State → Prop} {T : State → ℕ}
    (ht : φ → Triple w p P s Q T) :
    Triple w p (fun st => φ ∧ P st) s Q T :=
  fun st ω ⟨hφ, hP⟩ => ht hφ st ω hP

theorem Triple.exists_pre {w : ℕ} {p : Program} {α : Sort*}
    {P : α → State → Prop} {s : Stmt} {Q : Outcome → State → Prop} {T : State → ℕ}
    (ht : ∀ x, Triple w p (P x) s Q T) :
    Triple w p (fun st => ∃ x, P x st) s Q T :=
  fun st ω ⟨x, hP⟩ => ht x st ω hP

/-! ### Rules for primitive statements, sequencing, conditionals, and calls -/

theorem Triple.nop {w : ℕ} {p : Program} {P : State → Prop} {Q : State → Prop}
    (hPQ : ∀ st, P st → Q st) :
    Triple w p P .nop (normalPost Q) (fun _ => 1) := by
  intro st ω hP
  exact ⟨.normal, st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, hPQ st hP, Nat.le_refl _⟩

theorem Triple.assign {w : ℕ} {p : Program} {P : State → Prop} {r : ℕ} {e : Expr}
    {val : State → ℕ} {Q : State → Prop}
    (he : ∀ st, P st → e.eval w st = some (val st))
    (hpost : ∀ st, P st → Q { st with regs := Function.update st.regs r (val st) }) :
    Triple w p P (.assign r e) (normalPost Q) (fun _ => e.size + 1) := by
  intro st ω hP
  exact ⟨.normal, { st with regs := Function.update st.regs r (val st) }, e.size + 1,
    runs_assign_iff.mpr ⟨val st, he st hP, rfl, rfl, rfl⟩, hpost st hP, Nat.le_refl _⟩

theorem Triple.store {w : ℕ} {p : Program} {P : State → Prop} {a e : Expr}
    {addr val : State → ℕ} {Q : State → Prop}
    (ha : ∀ st, P st → a.eval w st = some (addr st))
    (hv : ∀ st, P st → e.eval w st = some (val st))
    (hpost : ∀ st, P st → Q { st with mem := Function.update st.mem (addr st) (val st) }) :
    Triple w p P (.store a e) (normalPost Q) (fun _ => a.size + e.size + 1) := by
  intro st ω hP
  exact ⟨.normal, { st with mem := Function.update st.mem (addr st) (val st) },
    a.size + e.size + 1,
    runs_store_iff.mpr ⟨addr st, val st, ha st hP, hv st hP, rfl, rfl, rfl⟩,
    hpost st hP, Nat.le_refl _⟩

theorem Triple.rand {w : ℕ} {p : Program} {P : State → Prop} {r : ℕ} {Q : State → Prop}
    (hpost : ∀ st v, P st → v < 2 ^ w →
      Q { st with regs := Function.update st.regs r v, pos := st.pos + w }) :
    Triple w p P (.rand r) (normalPost Q) (fun _ => 1) := by
  intro st ω hP
  refine ⟨.normal,
    { st with regs := Function.update st.regs r (readWord ω st.pos w), pos := st.pos + w },
    1, runs_rand_iff.mpr ⟨rfl, rfl, rfl⟩, ?_, Nat.le_refl _⟩
  exact hpost st (readWord ω st.pos w) hP (readWord_lt_pow ω st.pos w)

theorem Triple.ret {w : ℕ} {p : Program} {P : State → Prop} {e : Expr}
    {val : State → ℕ} {Q : ℕ → State → Prop}
    (he : ∀ st, P st → e.eval w st = some (val st))
    (hpost : ∀ st, P st → Q (val st) st) :
    Triple w p P (.ret e) (retPost Q) (fun _ => e.size + 1) := by
  intro st ω hP
  exact ⟨.returned (val st), st, e.size + 1,
    runs_ret_iff.mpr ⟨val st, he st hP, rfl, rfl, rfl⟩, hpost st hP, Nat.le_refl _⟩

theorem Triple.seq {w : ℕ} {p : Program}
    {P : State → Prop} {s₁ s₂ : Stmt}
    {Q₁ Q : Outcome → State → Prop} {T₁ T₂ T : State → ℕ}
    (h₁ : Triple w p P s₁ Q₁ T₁)
    (h₂ : Triple w p (Q₁ .normal) s₂ Q T₂)
    (hret : ∀ u st', Q₁ (.returned u) st' → Q (.returned u) st')
    (hcost_ret : ∀ st u st', P st → Q₁ (.returned u) st' → T₁ st + 1 ≤ T st)
    (hcost_norm : ∀ st st₁, P st → Q₁ .normal st₁ → T₁ st + T₂ st₁ + 1 ≤ T st) :
    Triple w p P (.seq s₁ s₂) Q T := by
  intro st ω hP
  rcases h₁ st ω hP with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  cases o₁ with
  | returned u =>
    refine ⟨.returned u, st₁, c₁ + 1,
      runs_seq_iff.mpr (Or.inl ⟨u, c₁, hr₁, rfl, rfl⟩), hret u st₁ hq₁, ?_⟩
    exact Nat.le_trans (Nat.add_le_add_right hc₁ 1) (hcost_ret st u st₁ hP hq₁)
  | normal =>
    rcases h₂ st₁ ω hq₁ with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
    refine ⟨o₂, st₂, c₁ + c₂ + 1,
      runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq₂, ?_⟩
    exact Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add hc₁ hc₂) 1) (hcost_norm st st₁ hP hq₁)

theorem Triple.seq_normal {w : ℕ} {p : Program}
    {P R : State → Prop} {s₁ s₂ : Stmt} {Q : Outcome → State → Prop} {T₁ T₂ T : State → ℕ}
    (h₁ : Triple w p P s₁ (normalPost R) T₁)
    (h₂ : Triple w p R s₂ Q T₂)
    (hcost : ∀ st st₁, P st → R st₁ → T₁ st + T₂ st₁ + 1 ≤ T st) :
    Triple w p P (.seq s₁ s₂) Q T :=
  Triple.seq h₁ h₂ (fun _ _ h => False.elim h)
    (fun _ _ _ _ h => False.elim h) hcost

theorem Triple.seq_normal_const {w : ℕ} {p : Program}
    {P R : State → Prop} {s₁ s₂ : Stmt} {Q : Outcome → State → Prop} {c₁ c₂ : ℕ}
    (h₁ : Triple w p P s₁ (normalPost R) (fun _ => c₁))
    (h₂ : Triple w p R s₂ Q (fun _ => c₂)) :
    Triple w p P (.seq s₁ s₂) Q (fun _ => c₁ + c₂ + 1) :=
  Triple.seq_normal h₁ h₂ (fun _ _ _ _ => Nat.le_refl _)

theorem Triple.cond {w : ℕ} {p : Program}
    {P : State → Prop} {e : Expr} {s t : Stmt} {Q : Outcome → State → Prop}
    {val T_t T_f : State → ℕ}
    (he : ∀ st, P st → e.eval w st = some (val st))
    (htrue : Triple w p (fun st => P st ∧ val st ≠ 0) s Q T_t)
    (hfalse : Triple w p (fun st => P st ∧ val st = 0) t Q T_f) :
    Triple w p P (.cond e s t) Q
      (fun st => e.size + (if val st = 0 then T_f st else T_t st) + 1) := by
  intro st ω hP
  by_cases hv : val st = 0
  · rcases hfalse st ω ⟨hP, hv⟩ with ⟨o, st', c₁, hr, hq, hc⟩
    refine ⟨o, st', e.size + c₁ + 1, runs_cond_iff.mpr ⟨0, c₁, hv ▸ he st hP, ?_, rfl⟩, hq, ?_⟩
    · simpa using hr
    · simp only [hv, ↓reduceIte]; omega
  · rcases htrue st ω ⟨hP, hv⟩ with ⟨o, st', c₁, hr, hq, hc⟩
    refine ⟨o, st', e.size + c₁ + 1,
      runs_cond_iff.mpr ⟨val st, c₁, he st hP, ?_, rfl⟩, hq, ?_⟩
    · simpa [hv] using hr
    · simp only [hv, ↓reduceIte]; omega

theorem Triple.cond_const {w : ℕ} {p : Program}
    {P : State → Prop} {e : Expr} {s t : Stmt} {Q : Outcome → State → Prop}
    {val : State → ℕ} {c_t c_f : ℕ}
    (he : ∀ st, P st → e.eval w st = some (val st))
    (htrue : Triple w p (fun st => P st ∧ val st ≠ 0) s Q (fun _ => c_t))
    (hfalse : Triple w p (fun st => P st ∧ val st = 0) t Q (fun _ => c_f)) :
    Triple w p P (.cond e s t) Q (fun _ => e.size + max c_t c_f + 1) :=
  (Triple.cond he htrue hfalse).mono_cost fun st _ => by split_ifs <;> omega

theorem Triple.call {w : ℕ} {p : Program}
    {P : State → Prop} {r f : ℕ} {args : List Expr} {C : Contract}
    {vs : State → List ℕ} {Q : State → Prop}
    (hf : MeetsContract w p f C)
    (hargs : ∀ st, P st → evalArgs w st args = some (vs st))
    (hwords : ∀ st, P st → ∀ v ∈ vs st, v < 2 ^ w)
    (hpre : ∀ st, P st → C.pre (vs st) st.mem)
    (hpost : ∀ st v mem' pos', P st → C.post (vs st) st.mem v mem' →
      Q { mem := mem', regs := Function.update st.regs r v, pos := pos' }) :
    Triple w p P (.call r f args) (normalPost Q)
      (fun st => argsSize args + C.cost (vs st) st.mem + 1) := by
  intro st ω hP
  rcases runs_call_of_meetsContract (r := r) hf (hargs st hP) (hwords st hP) (hpre st hP) ω with
    ⟨st', c, v, hrun, hcpost, hr, hother, hcost⟩
  have hst' : st' = { mem := st'.mem, regs := Function.update st.regs r v, pos := st'.pos } := by
    cases st'
    dsimp only at hr hother
    simp only [State.mk.injEq, true_and, and_true]
    funext r'
    by_cases hr' : r' = r
    · subst hr'; simp [hr]
    · simp [hr', hother r' hr']
  refine ⟨.normal, st', c, hrun, ?_, hcost⟩
  rw [normalPost_normal, hst']
  exact hpost st v st'.mem st'.pos hP hcpost

/-! ### Loop rules -/

/-- General loop rule using a state invariant `Inv`, a decreasing termination measure `m`, and a
remaining-cost potential `rem` bounding the sum of future iteration costs plus the final exit
check. Supports early `ret` inside the loop body and `ω`-dependent steps. -/
theorem Triple.loop_measure {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {Inv : State → Prop} {Q : Outcome → State → Prop}
    {m rem : State → ℕ} {condVal : State → ℕ}
    (hcond : ∀ st, Inv st → e.eval w st = some (condVal st))
    (hexit : ∀ st, Inv st → condVal st = 0 → Q .normal st ∧ e.size + 1 ≤ rem st)
    (hstep : ∀ st, Inv st → condVal st ≠ 0 →
      ∃ stepCost, Triple w p (fun s => s = st) body
        (fun o s' => match o with
          | .returned u => Q (.returned u) s' ∧ e.size + stepCost + 1 ≤ rem st
          | .normal => Inv s' ∧ m s' < m st ∧ e.size + stepCost + rem s' + 1 ≤ rem st)
        (fun _ => stepCost)) :
    Triple w p Inv (.loop e body) Q rem := by
  intro st ω hInv
  suffices ∀ k st, m st ≤ k → Inv st →
      ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q o st' ∧ c ≤ rem st from
    this (m st) st (Nat.le_refl _) hInv
  intro k
  induction k with
  | zero =>
    intro st hm hInv
    by_cases hv : condVal st = 0
    · rcases hexit st hInv hv with ⟨hq, hrem⟩
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond st hInv, rfl, rfl, rfl⟩), hq, hrem⟩
    · rcases hstep st hInv hv with ⟨stepCost, hbody⟩
      rcases hbody st ω rfl with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
      dsimp only at hc₁
      cases o₁ with
      | returned u =>
        rcases hq₁ with ⟨hq, hrem⟩
        refine ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond st hInv, hv, hr₁, rfl, rfl⟩)),
          hq, ?_⟩
        omega
      | normal =>
        rcases hq₁ with ⟨_, hm₁, _⟩
        omega
  | succ k ih =>
    intro st hm hInv
    by_cases hv : condVal st = 0
    · rcases hexit st hInv hv with ⟨hq, hrem⟩
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond st hInv, rfl, rfl, rfl⟩), hq, hrem⟩
    · rcases hstep st hInv hv with ⟨stepCost, hbody⟩
      rcases hbody st ω rfl with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
      dsimp only at hc₁
      cases o₁ with
      | returned u =>
        rcases hq₁ with ⟨hq, hrem⟩
        refine ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond st hInv, hv, hr₁, rfl, rfl⟩)),
          hq, ?_⟩
        omega
      | normal =>
        rcases hq₁ with ⟨hInv₁, hm₁, hrem⟩
        rcases ih st₁ (by omega) hInv₁ with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
        refine ⟨o₂, st₂, e.size + c₁ + c₂ + 1,
          runs_loop_iff.mpr
            (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hcond st hInv, hv, hr₁, hr₂, rfl⟩)),
          hq₂, ?_⟩
        omega

/-- Loop rule with a uniform per-iteration body cost bound `bodyBound` and decreasing measure `m`
(requiring `1 ≤ m st` whenever the loop guard holds, so early return on the last step fits in
`m st` iterations). Total cost is at most `(e.size + bodyBound + 1) * m st + e.size + 1`. -/
theorem Triple.loop_const {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {Inv : State → Prop} {Q : Outcome → State → Prop}
    (m : State → ℕ) (condVal : State → ℕ) (bodyBound : ℕ)
    (hcond : ∀ st, Inv st → e.eval w st = some (condVal st))
    (hexit : ∀ st, Inv st → condVal st = 0 → Q .normal st)
    (hpos : ∀ st, Inv st → condVal st ≠ 0 → 1 ≤ m st)
    (hstep : ∀ st, Inv st → condVal st ≠ 0 →
      Triple w p (fun s => s = st) body
        (fun o s' => match o with
          | .returned u => Q (.returned u) s'
          | .normal => Inv s' ∧ m s' < m st)
        (fun _ => bodyBound)) :
    Triple w p Inv (.loop e body) Q
      (fun st => (e.size + bodyBound + 1) * m st + e.size + 1) := by
  refine Triple.loop_measure (m := m)
    (rem := fun st => (e.size + bodyBound + 1) * m st + e.size + 1) hcond ?_ ?_
  · intro st hInv hv
    exact ⟨hexit st hInv hv, by omega⟩
  · intro st hInv hv
    refine ⟨bodyBound, (hstep st hInv hv).conseq (fun _ h => h) ?_ (fun _ _ => Nat.le_refl _)⟩
    intro o s' hq
    cases o with
    | returned u =>
      have hm1 : 1 ≤ m st := hpos st hInv hv
      have hmul : (e.size + bodyBound + 1) * 1 ≤ (e.size + bodyBound + 1) * m st :=
        Nat.mul_le_mul_left _ hm1
      exact ⟨hq, by nlinarith⟩
    | normal =>
      rcases hq with ⟨hInv', hm'⟩
      have hmul : (e.size + bodyBound + 1) * (m s' + 1) ≤ (e.size + bodyBound + 1) * m st :=
        Nat.mul_le_mul_left _ hm'
      refine ⟨hInv', hm', by linarith⟩

/-- Normal-termination specialization of `Triple.loop_const` without an explicit `1 ≤ m st`
hypothesis, since normal body termination `m s' < m st` already implies `1 ≤ m st`. -/
theorem Triple.loop_const_normal {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {Inv Q : State → Prop}
    (m : State → ℕ) (condVal : State → ℕ) (bodyBound : ℕ)
    (hcond : ∀ st, Inv st → e.eval w st = some (condVal st))
    (hexit : ∀ st, Inv st → condVal st = 0 → Q st)
    (hstep : ∀ st, Inv st → condVal st ≠ 0 →
      Triple w p (fun s => s = st) body
        (normalPost fun s' => Inv s' ∧ m s' < m st)
        (fun _ => bodyBound)) :
    Triple w p Inv (.loop e body) (normalPost Q)
      (fun st => (e.size + bodyBound + 1) * m st + e.size + 1) := by
  refine Triple.loop_measure (m := m)
    (rem := fun st => (e.size + bodyBound + 1) * m st + e.size + 1) hcond ?_ ?_
  · intro st hInv hv
    exact ⟨hexit st hInv hv, by omega⟩
  · intro st hInv hv
    refine ⟨bodyBound, (hstep st hInv hv).conseq (fun _ h => h) ?_ (fun _ _ => Nat.le_refl _)⟩
    intro o s' hq
    cases o with
    | returned u => exact False.elim hq
    | normal =>
      rcases hq with ⟨hInv', hm'⟩
      have hmul : (e.size + bodyBound + 1) * (m s' + 1) ≤ (e.size + bodyBound + 1) * m st :=
        Nat.mul_le_mul_left _ hm'
      refine ⟨hInv', hm', by linarith⟩

/-- Indexed loop rule where a ghost index `a : α` tracks the remaining cost bound `rem a` and
decreasing measure `m a`. Useful when loop bounds and per-step costs depend on a logical index. -/
theorem Triple.loop_inv {w : ℕ} {p : Program} {α : Type*} {e : Expr} {body : Stmt}
    {Inv : α → State → Prop} {Q : Outcome → State → Prop}
    (m rem : α → ℕ) {condVal : State → ℕ}
    (hcond : ∀ a st, Inv a st → e.eval w st = some (condVal st))
    (hexit : ∀ a st, Inv a st → condVal st = 0 → Q .normal st ∧ e.size + 1 ≤ rem a)
    (hstep : ∀ a st, Inv a st → condVal st ≠ 0 →
      ∃ stepCost, Triple w p (fun s => s = st) body
        (fun o s' => match o with
          | .returned u => Q (.returned u) s' ∧ e.size + stepCost + 1 ≤ rem a
          | .normal => ∃ a', Inv a' s' ∧ m a' < m a ∧
              e.size + stepCost + rem a' + 1 ≤ rem a)
        (fun _ => stepCost))
    (a₀ : α) :
    Triple w p (Inv a₀) (.loop e body) Q (fun _ => rem a₀) := by
  intro st ω hInv
  suffices ∀ k a st, m a ≤ k → Inv a st →
      ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q o st' ∧ c ≤ rem a from
    this (m a₀) a₀ st (Nat.le_refl _) hInv
  intro k
  induction k with
  | zero =>
    intro a st hm hInv
    by_cases hv : condVal st = 0
    · rcases hexit a st hInv hv with ⟨hq, hrem⟩
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond a st hInv, rfl, rfl, rfl⟩), hq, hrem⟩
    · rcases hstep a st hInv hv with ⟨stepCost, hbody⟩
      rcases hbody st ω rfl with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
      dsimp only at hc₁
      cases o₁ with
      | returned u =>
        rcases hq₁ with ⟨hq, hrem⟩
        refine ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond a st hInv, hv, hr₁, rfl, rfl⟩)),
          hq, ?_⟩
        omega
      | normal =>
        rcases hq₁ with ⟨_, _, hm', _⟩
        omega
  | succ k ih =>
    intro a st hm hInv
    by_cases hv : condVal st = 0
    · rcases hexit a st hInv hv with ⟨hq, hrem⟩
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv ▸ hcond a st hInv, rfl, rfl, rfl⟩), hq, hrem⟩
    · rcases hstep a st hInv hv with ⟨stepCost, hbody⟩
      rcases hbody st ω rfl with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
      dsimp only at hc₁
      cases o₁ with
      | returned u =>
        rcases hq₁ with ⟨hq, hrem⟩
        refine ⟨.returned u, st₁, e.size + c₁ + 1,
          runs_loop_iff.mpr (Or.inr (Or.inl ⟨condVal st, u, c₁, hcond a st hInv, hv, hr₁, rfl, rfl⟩)),
          hq, ?_⟩
        omega
      | normal =>
        rcases hq₁ with ⟨a', hInv', hm', hrem⟩
        rcases ih a' st₁ (by omega) hInv' with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
        refine ⟨o₂, st₂, e.size + c₁ + c₂ + 1,
          runs_loop_iff.mpr
            (Or.inr (Or.inr ⟨condVal st, st₁, c₁, c₂, hcond a st hInv, hv, hr₁, hr₂, rfl⟩)),
          hq₂, ?_⟩
        omega

/-- Loop rule indexed by a remaining worklist `xs : List β`, bounding the total cost directly by the
sum of per-element body costs `(xs.map bodyCost).sum` plus loop overhead. -/
theorem Triple.loop_list {w : ℕ} {p : Program} {β : Type*} {e : Expr} {body : Stmt}
    {Inv : List β → State → Prop} {Q : Outcome → State → Prop}
    (bodyCost : β → ℕ)
    (hnil : ∀ st, Inv [] st → e.eval w st = some 0 ∧ Q .normal st)
    (hcons : ∀ x xs st, Inv (x :: xs) st →
      ∃ v, e.eval w st = some v ∧ v ≠ 0 ∧
        Triple w p (fun s => s = st) body
          (fun o s' => match o with
            | .returned u => Q (.returned u) s'
            | .normal => Inv xs s')
          (fun _ => bodyCost x))
    (xs₀ : List β) :
    Triple w p (Inv xs₀) (.loop e body) Q
      (fun _ => (xs₀.map bodyCost).sum + xs₀.length * (e.size + 1) + e.size + 1) := by
  intro st ω hInv
  induction xs₀ generalizing st with
  | nil =>
    rcases hnil st hInv with ⟨he, hq⟩
    exact ⟨.normal, st, e.size + 1,
      runs_loop_iff.mpr (Or.inl ⟨he, rfl, rfl, rfl⟩), hq, by simp⟩
  | cons x xs ih =>
    rcases hcons x xs st hInv with ⟨v, he, hv, hbody⟩
    rcases hbody st ω rfl with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
    dsimp only at hc₁
    cases o₁ with
    | returned u =>
      refine ⟨.returned u, st₁, e.size + c₁ + 1,
        runs_loop_iff.mpr (Or.inr (Or.inl ⟨v, u, c₁, he, hv, hr₁, rfl, rfl⟩)), hq₁, ?_⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
    | normal =>
      rcases ih st₁ hq₁ with ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
      refine ⟨o₂, st₂, e.size + c₁ + c₂ + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, he, hv, hr₁, hr₂, rfl⟩)), hq₂, ?_⟩
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_one_mul] at hc₂ ⊢
      omega

/-! ### Sum of per-iteration costs and counter-based `for` loops -/

/-- Sum of `f i` for `lo ≤ i < hi`. Equals `0` when `hi ≤ lo`. -/
@[expose] def rangeCost (f : ℕ → ℕ) (lo hi : ℕ) : ℕ :=
  ((List.range' lo (hi - lo)).map f).sum

@[simp] theorem rangeCost_self (f : ℕ → ℕ) (n : ℕ) : rangeCost f n n = 0 := by
  simp [rangeCost]

theorem rangeCost_of_le {f : ℕ → ℕ} {lo hi : ℕ} (h : hi ≤ lo) : rangeCost f lo hi = 0 := by
  simp [rangeCost, Nat.sub_eq_zero_of_le h]

theorem rangeCost_step {f : ℕ → ℕ} {lo hi : ℕ} (h : lo < hi) :
    rangeCost f lo hi = f lo + rangeCost f (lo + 1) hi := by
  have hsub : hi - lo = (hi - (lo + 1)) + 1 := by omega
  simp only [rangeCost, hsub, List.range'_succ, List.map_cons, List.sum_cons]

theorem rangeCost_add (f g : ℕ → ℕ) (lo hi : ℕ) :
    rangeCost (fun i => f i + g i) lo hi = rangeCost f lo hi + rangeCost g lo hi := by
  suffices ∀ n s, ((List.range' s n).map fun i => f i + g i).sum =
      ((List.range' s n).map f).sum + ((List.range' s n).map g).sum from
    this (hi - lo) lo
  intro n
  induction n with
  | zero => intro s; simp
  | succ n ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, List.sum_cons, ih (s + 1)]
    omega

theorem rangeCost_mono {f g : ℕ → ℕ} {lo hi : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → f i ≤ g i) :
    rangeCost f lo hi ≤ rangeCost g lo hi := by
  suffices ∀ k a, lo ≤ a → a + k = hi →
      ((List.range' a k).map f).sum ≤ ((List.range' a k).map g).sum by
    by_cases hle : lo ≤ hi
    · simpa [rangeCost] using this (hi - lo) lo (Nat.le_refl _) (by omega)
    · simp [rangeCost_of_le (by omega : hi ≤ lo)]
  intro k
  induction k with
  | zero => intro a _ _; simp
  | succ k ih =>
    intro a ha hak
    simp only [List.range'_succ, List.map_cons, List.sum_cons]
    have hfa : f a ≤ g a := h a ha (by omega)
    have htail : ((List.range' (a + 1) k).map f).sum ≤ ((List.range' (a + 1) k).map g).sum :=
      ih (a + 1) (by omega) (by omega)
    omega

@[simp] theorem rangeCost_const (c lo hi : ℕ) :
    rangeCost (fun _ => c) lo hi = (hi - lo) * c := by
  suffices ∀ k s, ((List.range' s k).map fun _ => c).sum = k * c from
    this (hi - lo) lo
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
    intro s
    simp only [List.range'_succ, List.map_cons, List.sum_cons, ih (s + 1), Nat.add_one_mul]
    omega

theorem rangeCost_le_mul {f : ℕ → ℕ} {lo hi c : ℕ}
    (h : ∀ i, lo ≤ i → i < hi → f i ≤ c) :
    rangeCost f lo hi ≤ (hi - lo) * c := by
  simpa using rangeCost_mono (g := fun _ => c) h

theorem rangeCost_zero_eq_range (f : ℕ → ℕ) (n : ℕ) :
    rangeCost f 0 n = ((List.range n).map f).sum := by
  simp [rangeCost, List.range'_eq_map_range]

/-- Counter loop `while r < hi { body; r := r + 1 }`. -/
@[expose] def forUp (r : ℕ) (hi : Expr) (body : Stmt) : Stmt :=
  .loop (.bin .lt (.reg r) hi) (body ;; .assign r (.bin .add (.reg r) (.const 1)))

/-- Counter loop `r := lo; while r < hi { body; r := r + 1 }`. -/
@[expose] def forRange (r : ℕ) (lo hi : Expr) (body : Stmt) : Stmt :=
  .seq (.assign r lo) (forUp r hi body)

/-- Rule for `forUp r hi body` starting at counter `i₀ ≤ hiVal` or `hiVal < i₀`, summing
per-iteration body bounds `stepCost i` via `rangeCost` and supporting early `ret` via `Q_ret`. -/
theorem Triple.forUp {w : ℕ} {p : Program} {r : ℕ} {hi : Expr} {body : Stmt}
    {Inv : ℕ → State → Prop} {Q_ret : ℕ → State → Prop}
    (stepCost : ℕ → ℕ) (i₀ hiVal : ℕ)
    (hw : 1 < 2 ^ w)
    (hhi_word : i₀ < hiVal → hiVal < 2 ^ w)
    (hreg : ∀ i st, i₀ ≤ i → (i = i₀ ∨ i ≤ hiVal) → Inv i st → st.regs r = i)
    (hhi : ∀ i st, i₀ ≤ i → (i = i₀ ∨ i ≤ hiVal) → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i, i₀ ≤ i → i < hiVal →
      Triple w p (Inv i) body
        (fun o st₁ => match o with
          | .returned u => Q_ret u st₁
          | .normal =>
            Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
              st₁.regs r = i)
        (fun _ => stepCost i)) :
    Triple w p (Inv i₀) (forUp r hi body)
      (fun o st' => match o with
        | .returned u => Q_ret u st'
        | .normal => Inv (max i₀ hiVal) st')
      (fun _ => rangeCost stepCost i₀ hiVal + (hiVal - i₀) * (hi.size + 8) + (hi.size + 3)) := by
  intro st ω hInv
  suffices ∀ k i st, hiVal - i = k → i₀ ≤ i → (i = i₀ ∨ i ≤ hiVal) → Inv i st →
      ∃ o st' c, Runs w p ω (WordRAM.forUp r hi body) st o st' c ∧
        (match o with | .returned u => Q_ret u st' | .normal => Inv (max i hiVal) st') ∧
        c ≤ rangeCost stepCost i hiVal + (hiVal - i) * (hi.size + 8) + (hi.size + 3) from
    this (hiVal - i₀) i₀ st rfl (Nat.le_refl _) (Or.inl rfl) hInv
  intro k
  induction k with
  | zero =>
    intro i st hk hi₀ hcase hInv
    have hle : hiVal ≤ i := by omega
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 :=
      Expr.eval_lt_false (by simp [Expr.eval, hreg i st hi₀ hcase hInv])
        (hhi i st hi₀ hcase hInv) hle hw
    have hcost : (.bin .lt (.reg r) hi : Expr).size + 1 = hi.size + 3 := by simp; omega
    refine ⟨.normal, st, hi.size + 3,
      runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, hcost.symm⟩), ?_, ?_⟩
    · simpa [Nat.max_eq_left hle] using hInv
    · simp [rangeCost_of_le hle, Nat.sub_eq_zero_of_le hle]
  | succ k ih =>
    intro i st hk hi₀ hcase hInv
    have hlt : i < hiVal := by omega
    have hiw : i < 2 ^ w := Nat.lt_trans hlt (hhi_word (Nat.lt_of_le_of_lt hi₀ hlt))
    have hi1w : i + 1 < 2 ^ w := Nat.lt_of_le_of_lt hlt (hhi_word (Nat.lt_of_le_of_lt hi₀ hlt))
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 :=
      Expr.eval_lt_true (by simp [Expr.eval, hreg i st hi₀ hcase hInv])
        (hhi i st hi₀ hcase hInv) hlt hw
    have hcondSize : (Expr.bin .lt (.reg r) hi : Expr).size = hi.size + 2 := by simp; omega
    rcases hbody i hi₀ hlt st ω hInv with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
    cases o₁ with
    | returned u =>
      dsimp only at hc₁
      have hseq : Runs w p ω (body ;; .assign r (.bin .add (.reg r) (.const 1))) st
          (.returned u) st₁ (c₁ + 1) :=
        runs_seq_iff.mpr (Or.inl ⟨u, c₁, hr₁, rfl, rfl⟩)
      refine ⟨.returned u, st₁, hi.size + c₁ + 4, ?_, hq₁, ?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inl ⟨1, u, c₁ + 1, hcond, by decide, hseq, rfl,
          by omega⟩))
      · rw [rangeCost_step hlt]
        have hmul : 1 * (hi.size + 8) ≤ (hiVal - i) * (hi.size + 8) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    | normal =>
      rcases hq₁ with ⟨hInv₁, hreg₁⟩
      have hincEval : (Expr.bin .add (.reg r) (.const 1)).eval w st₁ = some (i + 1) :=
        Expr.eval_add (by simp [Expr.eval, hreg₁]) (Expr.eval_const hw) hi1w
      have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal
          { st₁ with regs := Function.update st₁.regs r (i + 1) } 4 :=
        runs_assign_iff.mpr ⟨i + 1, hincEval, rfl, rfl, by simp⟩
      have hseq : Runs w p ω (body ;; .assign r (.bin .add (.reg r) (.const 1))) st .normal
          { st₁ with regs := Function.update st₁.regs r (i + 1) } (c₁ + 5) :=
        runs_seq_iff.mpr (Or.inr ⟨_, c₁, 4, hr₁, hinc, by omega⟩)
      rcases ih (i + 1) _ (by omega) (by omega) (Or.inr hlt) hInv₁ with
        ⟨o₂, st₂, c₂, hr₂, hq₂, hc₂⟩
      dsimp only at hc₁ hc₂
      refine ⟨o₂, st₂, hi.size + c₁ + c₂ + 8, ?_, ?_, ?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, c₁ + 5, c₂, hcond, by decide, hseq, hr₂,
          by omega⟩))
      · cases o₂ with
        | returned u => exact hq₂
        | normal =>
          have hmax : max (i + 1) hiVal = max i hiVal := by omega
          simpa [hmax] using hq₂
      · rw [rangeCost_step hlt, show hiVal - i = (hiVal - (i + 1)) + 1 by omega, Nat.add_one_mul]
        omega

/-- Normal-termination specialization of `Triple.forUp` when `i₀ ≤ hiVal` and `body` never
returns early. -/
theorem Triple.forUp_le {w : ℕ} {p : Program} {r : ℕ} {hi : Expr} {body : Stmt}
    {Inv : ℕ → State → Prop}
    (stepCost : ℕ → ℕ) (i₀ hiVal : ℕ)
    (hle : i₀ ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : i₀ < hiVal → hiVal < 2 ^ w)
    (hreg : ∀ i st, i₀ ≤ i → i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi : ∀ i st, i₀ ≤ i → i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i, i₀ ≤ i → i < hiVal →
      Triple w p (Inv i) body
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
            st₁.regs r = i)
        (fun _ => stepCost i)) :
    Triple w p (Inv i₀) (WordRAM.forUp r hi body) (normalPost (Inv hiVal))
      (fun _ => rangeCost stepCost i₀ hiVal + (hiVal - i₀) * (hi.size + 8) + (hi.size + 3)) := by
  have h := Triple.forUp (r := r) (hi := hi) (body := body) (Inv := Inv)
    (Q_ret := fun _ _ => False) stepCost i₀ hiVal hw hhi_word
    (fun i st hi₀ hcase hInv => hreg i st hi₀ (by omega) hInv)
    (fun i st hi₀ hcase hInv => hhi i st hi₀ (by omega) hInv)
    (fun i hi₀ hlt => (hbody i hi₀ hlt).strengthen_post fun o s' hq => by
      cases o with
      | returned u => exact False.elim hq
      | normal => exact hq)
  refine h.strengthen_post fun o s' hq => ?_
  cases o with
  | returned u => exact False.elim hq
  | normal => simpa [Nat.max_eq_right hle] using hq

/-- Uniform-step-cost specialization of `Triple.forUp_le`. -/
theorem Triple.forUp_const {w : ℕ} {p : Program} {r : ℕ} {hi : Expr} {body : Stmt}
    {Inv : ℕ → State → Prop}
    (stepBound i₀ hiVal : ℕ)
    (hle : i₀ ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : i₀ < hiVal → hiVal < 2 ^ w)
    (hreg : ∀ i st, i₀ ≤ i → i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi : ∀ i st, i₀ ≤ i → i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i, i₀ ≤ i → i < hiVal →
      Triple w p (Inv i) body
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
            st₁.regs r = i)
        (fun _ => stepBound)) :
    Triple w p (Inv i₀) (WordRAM.forUp r hi body) (normalPost (Inv hiVal))
      (fun _ => (hiVal - i₀) * (stepBound + hi.size + 8) + (hi.size + 3)) := by
  refine (Triple.forUp_le (fun _ => stepBound) i₀ hiVal hle hw hhi_word hreg hhi hbody).mono_cost ?_
  intro _ _
  rw [rangeCost_const, ← Nat.mul_add, ← Nat.add_assoc stepBound]

/-- Rule for `forRange r lo hi body` starting from precondition `P`, initializing register `r` to
`lo` (`= loVal ≤ hiVal`) and running `hiVal - loVal` iterations. -/
theorem Triple.forRange_le {w : ℕ} {p : Program} {P : State → Prop} {r : ℕ} {lo hi : Expr}
    {body : Stmt} {Inv : ℕ → State → Prop}
    (stepCost : ℕ → ℕ) (loVal hiVal : ℕ)
    (hle : loVal ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : loVal < hiVal → hiVal < 2 ^ w)
    (hinit : ∀ st, P st →
      lo.eval w st = some loVal ∧ Inv loVal { st with regs := Function.update st.regs r loVal })
    (hreg : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i, loVal ≤ i → i < hiVal →
      Triple w p (Inv i) body
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
            st₁.regs r = i)
        (fun _ => stepCost i)) :
    Triple w p P (forRange r lo hi body) (normalPost (Inv hiVal))
      (fun _ => rangeCost stepCost loVal hiVal + (hiVal - loVal) * (hi.size + 8) +
        (lo.size + hi.size + 5)) := by
  refine Triple.seq_normal
    (Triple.assign (val := fun _ => loVal) (fun st hP => (hinit st hP).1)
      (fun st hP => (hinit st hP).2))
    (Triple.forUp_le stepCost loVal hiVal hle hw hhi_word hreg hhi hbody) ?_
  intro _ _ _ _
  omega

/-- Uniform-step-cost specialization of `Triple.forRange_le`. -/
theorem Triple.forRange_const {w : ℕ} {p : Program} {P : State → Prop} {r : ℕ} {lo hi : Expr}
    {body : Stmt} {Inv : ℕ → State → Prop}
    (stepBound loVal hiVal : ℕ)
    (hle : loVal ≤ hiVal) (hw : 1 < 2 ^ w) (hhi_word : loVal < hiVal → hiVal < 2 ^ w)
    (hinit : ∀ st, P st →
      lo.eval w st = some loVal ∧ Inv loVal { st with regs := Function.update st.regs r loVal })
    (hreg : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi : ∀ i st, loVal ≤ i → i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i, loVal ≤ i → i < hiVal →
      Triple w p (Inv i) body
        (normalPost fun st₁ =>
          Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
            st₁.regs r = i)
        (fun _ => stepBound)) :
    Triple w p P (forRange r lo hi body) (normalPost (Inv hiVal))
      (fun _ => (hiVal - loVal) * (stepBound + hi.size + 8) + (lo.size + hi.size + 5)) := by
  refine (Triple.forRange_le (fun _ => stepBound) loVal hiVal hle hw hhi_word hinit hreg hhi hbody).mono_cost ?_
  intro _ _
  rw [rangeCost_const, ← Nat.mul_add, ← Nat.add_assoc stepBound]

/-! ### Contract bridges -/

/-- Prove `MeetsContract w p f C` directly from a run lemma for the procedure body `body`. -/
theorem meetsContract_of_runs {w : ℕ} {p : Program} {f : ℕ} {C : Contract} {body : Stmt}
    (hproc : p.procs[f]? = some body)
    (hbody : ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem →
      ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem) :
    MeetsContract w p f C := by
  intro args mem pos ω hwords hpre
  rcases hbody args mem pos ω hwords hpre with ⟨o, st', c, hrun, hpost, hcost⟩
  exact ⟨body, hproc, o, st', c, hrun, hpost, hcost⟩

/-- Prove `MeetsContract w p f C` from a `Triple` for the procedure body `body`. -/
theorem meetsContract_of_triple {w : ℕ} {p : Program} {f : ℕ} {C : Contract} {body : Stmt}
    (hproc : p.procs[f]? = some body)
    (htriple : ∀ args mem pos, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem →
      Triple w p (fun st => st = startState args mem pos) body
        (fun o st' => C.post args mem o.value st'.mem) (fun _ => C.cost args mem)) :
    MeetsContract w p f C :=
  meetsContract_of_runs hproc fun args mem pos ω hwords hpre =>
    htriple args mem pos hwords hpre (startState args mem pos) ω rfl

/-! ### Forward sequence-stepping lemmas with accumulated prefix cost -/

theorem runs_start_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {T : ℕ} {Q : Outcome → State → Prop}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ 0 + c ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ c ≤ T := by
  simpa using h

theorem runs_triple_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {P : State → Prop} {s : Stmt}
    {Q₀ Q : Outcome → State → Prop} {T₀ : State → ℕ} {st : State} {k T : ℕ}
    (ht : Triple w p P s Q₀ T₀) (hP : P st)
    (hpost : ∀ o st', Q₀ o st' → Q o st') (hcost : k + T₀ st ≤ T) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases ht st ω hP with ⟨o, st', c, hrun, hq, hc⟩
  exact ⟨o, st', c, hrun, hpost o st' hq, by omega⟩

theorem runs_nop_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {k T : ℕ}
    {Q : Outcome → State → Prop} (hq : Q .normal st) (hc : k + 1 ≤ T) :
    ∃ o st' c, Runs w p ω .nop st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.normal, st, 1, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, hq, hc⟩

theorem runs_assign_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hq : Q .normal { st with regs := Function.update st.regs r v })
    (hc : k + (e.size + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.assign r e) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.normal, { st with regs := Function.update st.regs r v }, e.size + 1,
    runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hq, hc⟩

theorem runs_store_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {st : State} {x v k T : ℕ} {Q : Outcome → State → Prop}
    (ha : a.eval w st = some x) (he : e.eval w st = some v)
    (hq : Q .normal { st with mem := Function.update st.mem x v })
    (hc : k + (a.size + e.size + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.store a e) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.normal, { st with mem := Function.update st.mem x v }, a.size + e.size + 1,
    runs_store_iff.mpr ⟨x, v, ha, he, rfl, rfl, rfl⟩, hq, hc⟩

theorem runs_rand_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hq : ∀ v < 2 ^ w, Q .normal { st with regs := Function.update st.regs r v, pos := st.pos + w })
    (hc : k + 1 ≤ T) :
    ∃ o st' c, Runs w p ω (.rand r) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.normal, { st with regs := Function.update st.regs r (readWord ω st.pos w), pos := st.pos + w },
    1, runs_rand_iff.mpr ⟨rfl, rfl, rfl⟩, hq _ (readWord_lt_pow ω st.pos w), hc⟩

theorem runs_ret_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v) (hq : Q (.returned v) st) (hc : k + (e.size + 1) ≤ T) :
    ∃ o st' c, Runs w p ω (.ret e) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  ⟨.returned v, st, e.size + 1, runs_ret_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hq, hc⟩

theorem runs_seq_nop_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hrest : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ (k + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq .nop s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', 1 + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨st, 1, c₂, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, hr₂, rfl⟩),
    hq, by omega⟩

theorem runs_seq_assign_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hrest : ∃ o st' c, Runs w p ω s { st with regs := Function.update st.regs r v } o st' c ∧
      Q o st' ∧ (k + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.assign r e) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', (e.size + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c₂,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr₂, rfl⟩),
    hq, by omega⟩

theorem runs_seq_store_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr}
    {s : Stmt} {st : State} {x v k T : ℕ} {Q : Outcome → State → Prop}
    (ha : a.eval w st = some x) (he : e.eval w st = some v)
    (hrest : ∃ o st' c, Runs w p ω s { st with mem := Function.update st.mem x v } o st' c ∧
      Q o st' ∧ (k + a.size + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.store a e) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', (a.size + e.size + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, a.size + e.size + 1, c₂,
      runs_store_iff.mpr ⟨x, v, ha, he, rfl, rfl, rfl⟩, hr₂, rfl⟩),
    hq, by omega⟩

theorem runs_seq_rand_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {s : Stmt}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (hrest : ∀ v < 2 ^ w, ∃ o st' c,
      Runs w p ω s { st with regs := Function.update st.regs r v, pos := st.pos + w } o st' c ∧
        Q o st' ∧ (k + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.rand r) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hrest (readWord ω st.pos w) (readWord_lt_pow ω st.pos w) with
    ⟨o, st', c₂, hr₂, hq, hc₂⟩
  exact ⟨o, st', 1 + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, 1, c₂, runs_rand_iff.mpr ⟨rfl, rfl, rfl⟩, hr₂, rfl⟩),
    hq, by omega⟩

theorem runs_seq_cond_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e : Expr} {s₁ s₂ s : Stmt}
    {st : State} {v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some v)
    (hT : v ≠ 0 → ∃ o st' c, Runs w p ω (.seq s₁ s) st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T)
    (hF : v = 0 → ∃ o st' c, Runs w p ω (.seq s₂ s) st o st' c ∧ Q o st' ∧ (k + e.size + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.cond e s₁ s₂) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  by_cases hv : v = 0
  · rcases hF hv with ⟨o, st', c, hr, hq, hc⟩
    rcases runs_seq_iff.mp hr with ⟨u, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩
    · refine ⟨.returned u, st', (e.size + c₁ + 1) + 1,
        runs_seq_iff.mpr (Or.inl ⟨u, e.size + c₁ + 1,
          runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, rfl, rfl⟩),
        hq, by omega⟩
    · refine ⟨o, st', (e.size + c₁ + 1) + c₂ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₁, e.size + c₁ + 1, c₂,
          runs_cond_iff.mpr ⟨0, c₁, hv ▸ he, by simpa using hr₁, rfl⟩, hr₂, rfl⟩),
        hq, by omega⟩
  · rcases hT hv with ⟨o, st', c, hr, hq, hc⟩
    rcases runs_seq_iff.mp hr with ⟨u, c₁, hr₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩
    · refine ⟨.returned u, st', (e.size + c₁ + 1) + 1,
        runs_seq_iff.mpr (Or.inl ⟨u, e.size + c₁ + 1,
          runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, rfl, rfl⟩),
        hq, by omega⟩
    · refine ⟨o, st', (e.size + c₁ + 1) + c₂ + 1,
        runs_seq_iff.mpr (Or.inr ⟨st₁, e.size + c₁ + 1, c₂,
          runs_cond_iff.mpr ⟨v, c₁, he, by simpa [hv] using hr₁, rfl⟩, hr₂, rfl⟩),
        hq, by omega⟩

theorem runs_seq_call_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {C : Contract} {s : Stmt} {st : State} {vs : List ℕ} {k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C)
    (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem)
    (hrest : ∀ v mem' pos', C.post vs st.mem v mem' →
      ∃ o st' c, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c ∧ Q o st' ∧ (k + argsSize args + C.cost vs st.mem + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases runs_call_of_meetsContract (r := r) hf hargs hwords hpre ω with
    ⟨st₁, c₁, v, hr₁, hcpost, hr, hother, hcost⟩
  have hst₁ : st₁ = { mem := st₁.mem, regs := Function.update st.regs r v, pos := st₁.pos } := by
    cases st₁
    dsimp only at hr hother
    simp only [State.mk.injEq, true_and, and_true]
    funext r'
    by_cases hr' : r' = r
    · subst hr'; simp [hr]
    · simp [hr', hother r' hr']
  rcases hrest v st₁.mem st₁.pos hcpost with ⟨o, st', c₂, hr₂, hq, hc₂⟩
  rw [← hst₁] at hr₂
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩), hq, by omega⟩

theorem runs_seq_triple_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {P : State → Prop} {s₁ s₂ : Stmt} {Q₁ : State → Prop} {T₁ : State → ℕ}
    {st : State} {k T : ℕ} {Q : Outcome → State → Prop}
    (ht : Triple w p P s₁ (normalPost Q₁) T₁) (hP : P st)
    (hrest : ∀ st₁, Q₁ st₁ →
      ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + T₁ st + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases ht st ω hP with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  cases o₁ with
  | returned u => exact False.elim hq₁
  | normal =>
    rcases hrest st₁ hq₁ with ⟨o₂, st', c₂, hr₂, hq₂, hc₂⟩
    exact ⟨o₂, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩),
      hq₂, by omega⟩

theorem runs_seq_triple_gen_le {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {P : State → Prop} {s₁ s₂ : Stmt} {Q₁ Q : Outcome → State → Prop} {T₁ : State → ℕ}
    {st : State} {k T : ℕ}
    (ht : Triple w p P s₁ Q₁ T₁) (hP : P st)
    (hret : ∀ u st', Q₁ (.returned u) st' → Q (.returned u) st' ∧ k + T₁ st + 1 ≤ T)
    (hrest : ∀ st₁, Q₁ .normal st₁ →
      ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + T₁ st + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases ht st ω hP with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  cases o₁ with
  | returned u =>
    rcases hret u st₁ hq₁ with ⟨hq, hc⟩
    exact ⟨.returned u, st₁, c₁ + 1, runs_seq_iff.mpr (Or.inl ⟨u, c₁, hr₁, rfl, rfl⟩),
      hq, by omega⟩
  | normal =>
    rcases hrest st₁ hq₁ with ⟨o₂, st', c₂, hr₂, hq₂, hc₂⟩
    exact ⟨o₂, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hr₁, hr₂, rfl⟩),
      hq₂, by omega⟩

end WordRAM

