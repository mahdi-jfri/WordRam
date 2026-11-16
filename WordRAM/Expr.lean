module

public import WordRAM.Model
public import WordRAM.Contract

/-!
# Expression evaluation lemmas

This file provides lemmas for evaluating `Expr.eval` and `evalArgs`, simplifying `Expr.size` and
`argsSize`, and discharging word-size bounds (`< 2 ^ w`) for each `BinOp`. It also provides a
lightweight tactic `eval_expr` that decomposes `Expr.eval` and `evalArgs` goals and tries `omega`
on the resulting word-size side conditions.
-/

public section

namespace WordRAM

/-! ### Sizes and `BinOp.eval` -/

@[simp] theorem Expr.size_const (k : ℕ) : (Expr.const k).size = 1 := rfl
@[simp] theorem Expr.size_reg (r : ℕ) : (Expr.reg r).size = 1 := rfl
@[simp] theorem Expr.size_load (a : Expr) : (Expr.load a).size = a.size + 1 := rfl
@[simp] theorem Expr.size_bin (op : BinOp) (a b : Expr) :
    (Expr.bin op a b).size = a.size + b.size + 1 := rfl

@[simp] theorem argsSize_nil : argsSize [] = 0 := rfl
@[simp] theorem argsSize_cons (e : Expr) (es : List Expr) :
    argsSize (e :: es) = e.size + argsSize es := rfl

@[simp] theorem BinOp.eval_add (a b : ℕ) : BinOp.eval .add a b = a + b := rfl
@[simp] theorem BinOp.eval_sub (a b : ℕ) : BinOp.eval .sub a b = a - b := rfl
@[simp] theorem BinOp.eval_mul (a b : ℕ) : BinOp.eval .mul a b = a * b := rfl
@[simp] theorem BinOp.eval_div (a b : ℕ) : BinOp.eval .div a b = a / b := rfl
@[simp] theorem BinOp.eval_mod (a b : ℕ) : BinOp.eval .mod a b = a % b := rfl
@[simp] theorem BinOp.eval_lt (a b : ℕ) : BinOp.eval .lt a b = if a < b then 1 else 0 := rfl
@[simp] theorem BinOp.eval_eq (a b : ℕ) : BinOp.eval .eq a b = if a = b then 1 else 0 := rfl
@[simp] theorem BinOp.eval_and (a b : ℕ) : BinOp.eval .and a b = a &&& b := rfl
@[simp] theorem BinOp.eval_or (a b : ℕ) : BinOp.eval .or a b = a ||| b := rfl
@[simp] theorem BinOp.eval_xor (a b : ℕ) : BinOp.eval .xor a b = a ^^^ b := rfl
@[simp] theorem BinOp.eval_shiftLeft (a b : ℕ) : BinOp.eval .shiftLeft a b = a <<< b := rfl
@[simp] theorem BinOp.eval_shiftRight (a b : ℕ) : BinOp.eval .shiftRight a b = a >>> b := rfl

/-! ### `Expr.eval` rules -/

theorem Expr.eval_eq_of_eq {w : ℕ} {st : State} {e : Expr} {v₁ v₂ : ℕ}
    (h₁ : e.eval w st = some v₁) (h₂ : v₁ = v₂) : e.eval w st = some v₂ :=
  h₂ ▸ h₁

theorem Expr.eval_const {w k : ℕ} {st : State} (hk : k < 2 ^ w) :
    (Expr.const k).eval w st = some k := by
  simp [Expr.eval, hk]

theorem Expr.eval_reg (w r : ℕ) (st : State) :
    (Expr.reg r).eval w st = some (st.regs r) := rfl

theorem Expr.eval_reg_of_eq {w r v : ℕ} {st : State} (h : st.regs r = v) :
    (Expr.reg r).eval w st = some v := by
  simp [Expr.eval, h]

theorem Expr.eval_load {w : ℕ} {st : State} {a : Expr} {x : ℕ}
    (ha : a.eval w st = some x) :
    (Expr.load a).eval w st = some (st.mem x) := by
  simp [Expr.eval, ha]

theorem Expr.eval_load_of_eq {w : ℕ} {st : State} {a : Expr} {x v : ℕ}
    (ha : a.eval w st = some x) (hm : st.mem x = v) :
    (Expr.load a).eval w st = some v := by
  simp [Expr.eval, ha, hm]

theorem Expr.eval_bin {w : ℕ} {st : State} {op : BinOp} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y)
    (hlt : op.eval x y < 2 ^ w) :
    (Expr.bin op a b).eval w st = some (op.eval x y) := by
  simp [Expr.eval, ha, hb, hlt]

theorem Expr.eval_add {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hlt : x + y < 2 ^ w) :
    (Expr.bin .add a b).eval w st = some (x + y) :=
  Expr.eval_bin ha hb hlt

theorem Expr.eval_sub {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hx : x < 2 ^ w) :
    (Expr.bin .sub a b).eval w st = some (x - y) :=
  Expr.eval_bin ha hb (by simpa using Nat.lt_of_le_of_lt (Nat.sub_le x y) hx)

theorem Expr.eval_mul {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hlt : x * y < 2 ^ w) :
    (Expr.bin .mul a b).eval w st = some (x * y) :=
  Expr.eval_bin ha hb hlt

theorem Expr.eval_div {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hx : x < 2 ^ w) :
    (Expr.bin .div a b).eval w st = some (x / y) :=
  Expr.eval_bin ha hb (by simpa using Nat.lt_of_le_of_lt (Nat.div_le_self x y) hx)

theorem Expr.eval_mod {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hx : x < 2 ^ w) :
    (Expr.bin .mod a b).eval w st = some (x % y) :=
  Expr.eval_bin ha hb (by simpa using Nat.lt_of_le_of_lt (Nat.mod_le x y) hx)

theorem Expr.eval_lt_op {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt a b).eval w st = some (if x < y then 1 else 0) :=
  Expr.eval_bin ha hb (by simp only [BinOp.eval_lt]; split_ifs <;> omega)

theorem Expr.eval_lt_true {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hxy : x < y) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt a b).eval w st = some 1 := by
  simpa [hxy] using Expr.eval_lt_op ha hb hw

theorem Expr.eval_lt_false {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hxy : y ≤ x) (hw : 1 < 2 ^ w) :
    (Expr.bin .lt a b).eval w st = some 0 := by
  have hnot : ¬ x < y := Nat.not_lt.mpr hxy
  simpa [hnot] using Expr.eval_lt_op ha hb hw

theorem Expr.eval_eq_op {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq a b).eval w st = some (if x = y then 1 else 0) :=
  Expr.eval_bin ha hb (by simp only [BinOp.eval_eq]; split_ifs <;> omega)

theorem Expr.eval_eq_true {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hxy : x = y) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq a b).eval w st = some 1 := by
  simpa [hxy] using Expr.eval_eq_op ha hb hw

theorem Expr.eval_eq_false {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hxy : x ≠ y) (hw : 1 < 2 ^ w) :
    (Expr.bin .eq a b).eval w st = some 0 := by
  simpa [hxy] using Expr.eval_eq_op ha hb hw

theorem Expr.eval_and {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hx : x < 2 ^ w) :
    (Expr.bin .and a b).eval w st = some (x &&& y) :=
  Expr.eval_bin ha hb (by simpa using Nat.lt_of_le_of_lt Nat.and_le_left hx)

theorem Expr.eval_and_right {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hy : y < 2 ^ w) :
    (Expr.bin .and a b).eval w st = some (x &&& y) :=
  Expr.eval_bin ha hb (by simpa using Nat.and_lt_two_pow x hy)

theorem Expr.eval_or {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y)
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    (Expr.bin .or a b).eval w st = some (x ||| y) :=
  Expr.eval_bin ha hb (by simpa using Nat.or_lt_two_pow hx hy)

theorem Expr.eval_xor {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y)
    (hx : x < 2 ^ w) (hy : y < 2 ^ w) :
    (Expr.bin .xor a b).eval w st = some (x ^^^ y) :=
  Expr.eval_bin ha hb (by simpa using Nat.xor_lt_two_pow hx hy)

theorem Expr.eval_shiftLeft {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hlt : x <<< y < 2 ^ w) :
    (Expr.bin .shiftLeft a b).eval w st = some (x <<< y) :=
  Expr.eval_bin ha hb hlt

theorem Expr.eval_shiftRight {w : ℕ} {st : State} {a b : Expr} {x y : ℕ}
    (ha : a.eval w st = some x) (hb : b.eval w st = some y) (hx : x < 2 ^ w) :
    (Expr.bin .shiftRight a b).eval w st = some (x >>> y) :=
  Expr.eval_bin ha hb (by
    simpa [BinOp.eval_shiftRight, Nat.shiftRight_eq_div_pow] using
      Nat.lt_of_le_of_lt (Nat.div_le_self x (2 ^ y)) hx)

@[simp]
theorem evalArgs_nil (w : ℕ) (st : State) : evalArgs w st [] = some [] := rfl

theorem evalArgs_cons {w : ℕ} {st : State} {e : Expr} {es : List Expr} {v : ℕ} {vs : List ℕ}
    (he : e.eval w st = some v) (hes : evalArgs w st es = some vs) :
    evalArgs w st (e :: es) = some (v :: vs) := by
  simp [evalArgs, he, hes]

/-- Deferred memory-read obligation used by `eval_expr` to collapse record projections on `st.mem`
only after the address expression has been evaluated. -/
@[expose, reducible]
def Expr.MemAt (st : State) (x v : ℕ) : Prop := st.mem x = v

theorem Expr.eval_load_mem {w : ℕ} {st : State} {a : Expr} {x v : ℕ}
    (ha : a.eval w st = some x) (hm : Expr.MemAt st x v) :
    (Expr.load a).eval w st = some v :=
  Expr.eval_load_of_eq ha hm

theorem Expr.memAt_of_eq {st : State} {x v : ℕ} (h : st.mem x = v) : Expr.MemAt st x v := h

/-- Resolve a register-read goal `(.reg r).eval w st = some v` using context hypotheses or
register-map simplification. -/
syntax "eval_reg_step" : tactic
macro_rules
  | `(tactic| eval_reg_step) =>
    `(tactic|
      ((with_reducible apply Expr.eval_reg_of_eq)
       first
       | assumption
       | (try (conv_lhs => simp only [Function.update_apply, List.getD_eq_getElem?_getD,
            List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
            Option.getD_some, Option.getD_none, Nat.reduceBeqDiff, Nat.reduceEqDiff,
            eq_self_iff_true, ↓reduceIte, startState])
          all_goals (first | assumption | rfl | omega))))

/-- Apply one structural `Expr.eval` or `evalArgs` evaluation rule without unfolding `Expr.eval`. -/
syntax "eval_expr_step" : tactic
macro_rules
  | `(tactic| eval_expr_step) =>
    `(tactic|
      first
      | (with_reducible exact evalArgs_nil _ _)
      | (with_reducible apply evalArgs_cons)
      | eval_reg_step
      | (with_reducible apply Expr.eval_const)
      | (with_reducible apply Expr.eval_load_mem)
      | (with_reducible apply Expr.eval_add)
      | (with_reducible apply Expr.eval_sub)
      | (with_reducible apply Expr.eval_mul)
      | (with_reducible apply Expr.eval_div)
      | (with_reducible apply Expr.eval_mod)
      | (with_reducible apply Expr.eval_lt_op)
      | (with_reducible apply Expr.eval_eq_op)
      | (with_reducible apply Expr.eval_and)
      | (with_reducible apply Expr.eval_or)
      | (with_reducible apply Expr.eval_xor)
      | (with_reducible apply Expr.eval_shiftLeft)
      | (with_reducible apply Expr.eval_shiftRight))

/-- Decompose an `Expr.eval` or `evalArgs` goal into subexpressions and resolve deferred memory
reads, leaving any word-size side conditions `< 2 ^ w` open. -/
syntax "eval_expr_raw" : tactic
macro_rules
  | `(tactic| eval_expr_raw) =>
    `(tactic|
      ((repeat (any_goals eval_expr_step))
       all_goals (try (
         (with_reducible apply Expr.memAt_of_eq)
         try (conv_lhs => dsimp only)
         all_goals (first | assumption | rfl)))))

/-- Evaluate an `Expr.eval` or `evalArgs` goal, simplifying register updates and discharging
linear word-size bounds (`< 2 ^ w`) automatically when possible. -/
syntax "eval_expr" : tactic
macro_rules
  | `(tactic| eval_expr) =>
    `(tactic|
      (eval_expr_raw
       all_goals (try (first | assumption | omega | exact Nat.one_lt_two_pow (by omega)))))

end WordRAM
