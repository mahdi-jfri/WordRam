module

public import WordRAM.Logic

/-!
# Copying contiguous words in Word-RAM

This file defines and verifies `copyWords`, a Word-RAM procedure that takes arguments
`[src, dst, len]` for two non-overlapping ranges `[src, src + len)` and `[dst, dst + len)` and
copies `len` words from `src` to `dst` in `17 * len + 10` steps while leaving memory outside
`[dst, dst + len)` unchanged.
-/

public section

namespace WordRAM

/-- Copy `len` (`reg 2`) words from `src` (`reg 0`) to `dst` (`reg 1`), then return `0`. -/
@[expose] def copyWords : Stmt :=
  forRange 3 (.const 0) (.reg 2)
    (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))) ;;
  .ret (.const 0)

/-- Contract for `copyWords` at word size `w`. Arguments are `[src, dst, len]`, where both ranges
fit inside `[0, 2 ^ w)` and do not overlap (`dst + len ≤ src ∨ src + len ≤ dst`). -/
@[expose] def copyWordsContract (w : ℕ) : Contract where
  pre args _ :=
    ∃ src dst len, args = [src, dst, len] ∧
      1 < 2 ^ w ∧
      src + len ≤ 2 ^ w ∧
      dst + len ≤ 2 ^ w ∧
      (dst + len ≤ src ∨ src + len ≤ dst)
  post args mem v mem' :=
    ∃ src dst len, args = [src, dst, len] ∧
      v = 0 ∧
      (∀ i < len, mem' (dst + i) = mem (src + i)) ∧
      (∀ x, x < dst ∨ dst + len ≤ x → mem' x = mem x)
  cost args _ :=
    match args with
    | [_, _, len] => 17 * len + 10
    | _ => 0

/-- Helper transferring `ListAt mem src l` across `copyWordsContract`'s postcondition. -/
theorem copyWords_listAt {mem mem' : ℕ → ℕ} {src dst len : ℕ} {l : List ℕ}
    (hl : ListAt mem src l) (hlen : l.length = len)
    (hpost : ∀ i < len, mem' (dst + i) = mem (src + i)) :
    ListAt mem' dst l := by
  intro i hi
  rw [hpost i (hlen ▸ hi), hl i hi]

/-- Hoare triple for the copy loop inside `copyWords`. -/
theorem copyWordsLoop_triple {w src dst len : ℕ} (p : Program) (mem₀ : ℕ → ℕ) (pos : ℕ)
    (hw : 1 < 2 ^ w) (hlen : len < 2 ^ w)
    (hsrc : src + len ≤ 2 ^ w) (hdst : dst + len ≤ 2 ^ w)
    (hnov : dst + len ≤ src ∨ src + len ≤ dst) :
    Triple w p (fun st => st = startState [src, dst, len] mem₀ pos)
      (forRange 3 (.const 0) (.reg 2)
        (.store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3)))))
      (normalPost fun st' =>
        (∀ i < len, st'.mem (dst + i) = mem₀ (src + i)) ∧
        (∀ x, x < dst ∨ dst + len ≤ x → st'.mem x = mem₀ x))
      (fun _ => 17 * len + 7) := by
  have hloop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 1) (.reg 3)) (.load (.bin .add (.reg 0) (.reg 3))))
    (P := fun st => st = startState [src, dst, len] mem₀ pos)
    (Inv := fun i st =>
      st.regs 0 = src ∧ st.regs 1 = dst ∧ st.regs 2 = len ∧ st.regs 3 = i ∧
      (∀ j < i, st.mem (dst + j) = mem₀ (src + j)) ∧
      (∀ x, x < dst ∨ dst + i ≤ x → st.mem x = mem₀ x))
    8 0 len (Nat.zero_le len) hw (fun _ => hlen)
    (fun st hst => by
      subst hst
      refine ⟨by eval_expr, ?_, ?_, ?_, ?_, fun _ h => False.elim (Nat.not_lt_zero _ h),
        fun _ _ => rfl⟩ <;> simp [startState])
    (fun _ st _ _ hi => hi.2.2.2.1)
    (fun _ st _ _ hi => by
      have h2 : st.regs 2 = len := hi.2.2.1
      eval_expr)
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h2, h3, hcopied, hframe⟩
      have hsrc_word : src + i < 2 ^ w := by omega
      have hdst_word : dst + i < 2 ^ w := by omega
      have hsrc_mem : st.mem (src + i) = mem₀ (src + i) := hframe (src + i) (by omega)
      refine ⟨.normal, { st with mem := Function.update st.mem (dst + i) (mem₀ (src + i)) },
        8, ?_, ?_, by simp⟩
      · refine runs_store_iff.mpr
          ⟨dst + i, mem₀ (src + i), by eval_expr, ?_, rfl, rfl, by simp⟩
        rw [← hsrc_mem]
        eval_expr
      · refine ⟨⟨h0, h1, h2, by simp, ?_, ?_⟩, h3⟩
        · intro j hj
          dsimp only
          by_cases hji : j = i
          · subst hji
            rw [Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact hcopied j (by omega)
        · intro x hx
          dsimp only
          rw [Function.update_of_ne (by omega)]
          exact hframe x (by omega))
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' h
    cases o with
    | returned u => exact False.elim h
    | normal => exact h.2.2.2.2
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- `copyWords` placed at index `b` in `p` meets `copyWordsContract w`. -/
theorem copyWords_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [copyWords]) :
    MeetsContract w p b (copyWordsContract w) := by
  refine meetsContract_of_runs hp.head fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨src, dst, len, rfl, hw, hsrc, hdst, hnov⟩
  have hlen : len < 2 ^ w := hwords len (by simp)
  refine runs_start_le ?_
  dsimp only [copyWords]
  refine runs_seq_triple_le (copyWordsLoop_triple p mem pos hw hlen hsrc hdst hnov) rfl ?_
  intro st₁ ⟨hcopied, hframe⟩
  refine runs_ret_le (by eval_expr) ⟨src, dst, len, rfl, rfl, hcopied, hframe⟩ ?_
  dsimp [copyWordsContract]
  omega

end WordRAM
