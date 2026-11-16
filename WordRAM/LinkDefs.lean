module

public import WordRAM.Contract

/-!
# Program relocation and runner definitions

This file defines `runner Q c b`, which embeds a standalone program `Q` (written for word size
`wordSize c x`) inside a host program starting at procedure index `b`. Procedure `b` takes
arguments `[a, len, h]` where `x` is stored at `a` (`len = x.length`) and `h` is the host heap
pointer: it computes `w' = wordSize c x`, copies `x` to `h + 1`, runs `Q` with addresses shifted by
`h + 1`, procedures shifted by `b + 1`, and random words masked to `w'` bits, stores the output
length at `h`, and returns the new heap pointer `h + 1 + 2 ^ w'`.

This file also provides the register-bound, word-size, bit-slicing, and memory-layout helpers
that `runner` uses.
-/

namespace WordRAM

public section

/-- Strict upper bound on all register indices referenced by an expression. -/
@[expose] def Expr.regBound : Expr → ℕ
  | .const _ => 0
  | .reg r => r + 1
  | .load a => a.regBound
  | .bin _ a b => max a.regBound b.regBound

/-- Strict upper bound on all register indices referenced by an argument list. -/
@[expose] def argsRegBound : List Expr → ℕ
  | [] => 0
  | e :: es => max e.regBound (argsRegBound es)

/-- Strict upper bound on all register indices and call arities in a statement. -/
@[expose] def Stmt.regBound : Stmt → ℕ
  | .nop => 0
  | .assign r e => max (r + 1) e.regBound
  | .store a e => max a.regBound e.regBound
  | .rand r => r + 1
  | .seq s t => max s.regBound t.regBound
  | .cond e s t => max e.regBound (max s.regBound t.regBound)
  | .loop e body => max e.regBound body.regBound
  | .call r _ args => max (r + 1) (max args.length (argsRegBound args))
  | .ret e => e.regBound

/-- Strict upper bound (at least `1`) on all register indices and call arities in program `Q`. -/
@[expose] def Program.regBound (Q : Program) : ℕ :=
  max 1 (Q.procs.foldr (fun s acc => max s.regBound acc) 0)

/-- Relocate an expression of `Q`, shifting every memory address by `reg R`. -/
@[expose] def relocExpr (R : ℕ) : Expr → Expr
  | .const k => .const k
  | .reg r => .reg r
  | .load addr => .load (.bin .add (.reg R) (relocExpr R addr))
  | .bin op a b => .bin op (relocExpr R a) (relocExpr R b)

/-- Relocate a statement of `Q` to procedure base `b + 1`, with `base = reg R` and
`2 ^ w' = reg (R + 1)`. Every procedure call pads its arguments to `R` with zeros and passes
`reg R` and `reg (R + 1)` in registers `R` and `R + 1`. -/
@[expose] def relocStmt (R b : ℕ) : Stmt → Stmt
  | .nop => .nop
  | .assign r e => .assign r (relocExpr R e)
  | .store a e => .store (.bin .add (.reg R) (relocExpr R a)) (relocExpr R e)
  | .rand r => .seq (.rand r) (.assign r (.bin .mod (.reg r) (.reg (R + 1))))
  | .seq s t => .seq (relocStmt R b s) (relocStmt R b t)
  | .cond e s t => .cond (relocExpr R e) (relocStmt R b s) (relocStmt R b t)
  | .loop e body => .loop (relocExpr R e) (relocStmt R b body)
  | .call r f args =>
    .call r (b + 1 + f)
      (args.map (relocExpr R) ++ List.replicate (R - args.length) (.const 0) ++
        [.reg R, .reg (R + 1)])
  | .ret e => .ret (relocExpr R e)

/-- Compute `w' = wordSize c x` into `wReg` and `W = 2 ^ w'` into `WReg`, reading input of length
`lenReg` at `aReg`. Uses `tmp1, tmp2, tmp3` as scratch registers. All 7 register indices must be
distinct. -/
@[expose] def computeWordSizeStmt (c aReg lenReg wReg WReg tmp1 tmp2 tmp3 : ℕ) : Stmt :=
  match c with
  | 0 =>
    .seq (.assign wReg (.const 0)) (.assign WReg (.const 1))
  | c' + 1 =>
    let scan :=
      .seq (.assign tmp1 (.const 0))
        (.seq (.assign tmp2 (.const 0))
          (.loop (.bin .lt (.reg tmp1) (.reg lenReg))
            (.seq (.assign tmp3 (.load (.bin .add (.reg aReg) (.reg tmp1))))
              (.seq (.cond (.bin .lt (.reg tmp2) (.reg tmp3))
                  (.assign tmp2 (.reg tmp3)) .nop)
                (.assign tmp1 (.bin .add (.reg tmp1) (.const 1)))))))
    let sumExpr := .bin .add (.bin .add (.reg lenReg) (.reg tmp2)) (.const 2)
    let logLoop :=
      .seq (.assign tmp1 sumExpr)
        (.seq (.assign tmp2 (.const 1))
          (.seq (.assign wReg (.const 0))
            (.seq
              (.loop (.bin .eq (.bin .lt (.reg tmp1) (.reg tmp2)) (.const 0))
                (.seq (.assign tmp2 (.bin .add (.reg tmp2) (.reg tmp2)))
                  (.assign wReg (.bin .add (.reg wReg) (.const 1)))))
              (.seq (.assign wReg (.bin .mul (.const (c' + 1)) (.reg wReg)))
                (.assign WReg (.bin .shiftLeft (.const 1) (.reg wReg)))))))
    .seq scan logLoop

/-- Copy `lenReg` words from `srcReg` to `dstReg` using `idxReg` as scratch index. -/
@[expose] def copyWordsStmt (srcReg dstReg lenReg idxReg : ℕ) : Stmt :=
  .seq (.assign idxReg (.const 0))
    (.loop (.bin .lt (.reg idxReg) (.reg lenReg))
      (.seq (.store (.bin .add (.reg dstReg) (.reg idxReg))
              (.load (.bin .add (.reg srcReg) (.reg idxReg))))
        (.assign idxReg (.bin .add (.reg idxReg) (.const 1)))))

/-- Entry procedure (at index `b`) of `runner Q c b`, taking arguments `[a, len, h]`. -/
@[expose] def runnerEntry (Q : Program) (c b : ℕ) : Stmt :=
  let R := Q.regBound
  let computeW := computeWordSizeStmt c 0 1 3 4 5 6 7
  let setBase := .assign 6 (.bin .add (.reg 2) (.const 1))
  let copyIn := copyWordsStmt 0 6 1 5
  let callArgs := [.reg 1] ++ List.replicate (R - 1) (.const 0) ++ [.reg 6, .reg 4]
  let runQ := .call 7 (b + 1) callArgs
  let storeLen := .store (.reg 2) (.reg 7)
  let retPtr := .ret (.bin .add (.reg 6) (.reg 4))
  .seq computeW (.seq setBase (.seq copyIn (.seq runQ (.seq storeLen retPtr))))

/-- Module for running `Q` (with word-size constant `c`) inside a host program starting at
procedure index `b`. Procedure `b` is the entry point (`[a, len, h]`) and `b + 1 + f` are the
relocated procedures of `Q`. -/
@[expose] def runner (Q : Program) (c b : ℕ) : List Stmt :=
  runnerEntry Q c b :: Q.procs.map (relocStmt Q.regBound b)

end

/-! ### Pure helper lemmas on `regBound`, `wordSize`, `readWord`, `subBits`, and memory -/

namespace Link

public theorem one_le_regBound (Q : Program) : 1 ≤ Q.regBound :=
  le_max_left 1 _

public theorem regBound_le_of_mem {Q : Program} {s : Stmt} (hs : s ∈ Q.procs) :
    s.regBound ≤ Q.regBound := by
  have hfold : ∀ (l : List Stmt), s ∈ l →
      s.regBound ≤ l.foldr (fun s acc => max s.regBound acc) 0 := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons x xs ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hl with rfl | hxs
      · exact le_max_left _ _
      · exact le_trans (ih hxs) (le_max_right _ _)
  exact le_trans (hfold Q.procs hs) (le_max_right 1 _)

public theorem argsRegBound_le_of_mem {e : Expr} {es : List Expr} (he : e ∈ es) :
    e.regBound ≤ argsRegBound es := by
  induction es with
  | nil => cases he
  | cons x xs ih =>
    rcases List.mem_cons.mp he with rfl | hxs
    · exact le_max_left _ _
    · exact le_trans (ih hxs) (le_max_right _ _)

public theorem relocExpr_size_le (R : ℕ) (e : Expr) :
    (relocExpr R e).size ≤ 3 * e.size := by
  induction e with
  | const _ => simp [relocExpr, Expr.size]
  | reg _ => simp [relocExpr, Expr.size]
  | load a ih =>
    simp only [relocExpr, Expr.size]
    omega
  | bin op a b iha ihb =>
    simp only [relocExpr, Expr.size]
    omega

public theorem argsSize_reloc_le (R : ℕ) (args : List Expr) :
    argsSize (args.map (relocExpr R)) ≤ 3 * argsSize args := by
  induction args with
  | nil => simp [argsSize]
  | cons e es ih =>
    simp only [List.map_cons, argsSize]
    have h1 := relocExpr_size_le R e
    omega

public theorem argsSize_replicate_const (n k : ℕ) :
    argsSize (List.replicate n (.const k)) = n := by
  induction n with
  | zero => simp [argsSize]
  | succ n ih => simp [List.replicate_succ, argsSize, Expr.size, ih]; omega

public theorem argsSize_append (xs ys : List Expr) :
    argsSize (xs ++ ys) = argsSize xs + argsSize ys := by
  induction xs with
  | nil => simp [argsSize]
  | cons e es ih => simp [argsSize, ih]; omega

public theorem elem_le_foldr_max {x : List ℕ} {v : ℕ} (hv : v ∈ x) :
    v ≤ x.foldr max 0 := by
  induction x with
  | nil => cases hv
  | cons y ys ih =>
    rcases List.mem_cons.mp hv with rfl | hys
    · exact le_max_left _ _
    · exact le_trans (ih hys) (le_max_right _ _)

public theorem foldr_max_take_succ {x : List ℕ} {i : ℕ} (hi : i < x.length) :
    (x.take (i + 1)).foldr max 0 = max ((x.take i).foldr max 0) x[i] := by
  rw [List.take_succ_eq_append_getElem hi]
  induction (x.take i) with
  | nil => simp
  | cons y ys ih =>
    simp only [List.cons_append, List.foldr_cons]
    rw [ih]
    omega

public theorem foldr_max_take_zero (x : List ℕ) :
    (x.take 0).foldr max 0 = 0 := by
  simp

public theorem two_le_wordSize_of_pos {c : ℕ} (hc : 1 ≤ c) (x : List ℕ) :
    2 ≤ wordSize c x := by
  have h2 : 2 ^ 1 ≤ x.length + x.foldr max 0 + 2 := by simp
  have hlog : 1 ≤ Nat.log 2 (x.length + x.foldr max 0 + 2) :=
    Nat.le_log_of_pow_le (by norm_num) h2
  have hmul : 1 * 2 ≤ c * (Nat.log 2 (x.length + x.foldr max 0 + 2) + 1) :=
    Nat.mul_le_mul hc (by omega)
  simpa [wordSize] using hmul

public theorem sum_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (x : List ℕ) :
    x.length + x.foldr max 0 + 2 < 2 ^ wordSize c x := by
  have hlt : x.length + x.foldr max 0 + 2 <
      2 ^ (Nat.log 2 (x.length + x.foldr max 0 + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : Nat.log 2 (x.length + x.foldr max 0 + 2) + 1 ≤ wordSize c x :=
    Nat.le_mul_of_pos_left (Nat.log 2 (x.length + x.foldr max 0 + 2) + 1) hc
  exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hle)

public theorem length_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (x : List ℕ) :
    x.length < 2 ^ wordSize c x := by
  have := sum_lt_two_pow_wordSize hc x
  omega

public theorem mem_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) {x : List ℕ} {v : ℕ}
    (hv : v ∈ x) : v < 2 ^ wordSize c x := by
  have h1 := elem_le_foldr_max hv
  have h2 := sum_lt_two_pow_wordSize hc x
  omega

public theorem c_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (x : List ℕ) :
    c < 2 ^ wordSize c x := by
  have hlog : 2 ≤ Nat.log 2 (x.length + x.foldr max 0 + 2) + 1 := by
    have h2 : 2 ^ 1 ≤ x.length + x.foldr max 0 + 2 := by simp
    have := Nat.le_log_of_pow_le (by norm_num) h2
    omega
  have hw : 2 * c ≤ wordSize c x := by
    simpa [wordSize, Nat.mul_comm] using Nat.mul_le_mul_left c hlog
  have hc2 : c < 2 ^ (2 * c) := by
    have h1 : c < 2 ^ c := Nat.lt_two_pow_self
    have h2 : 2 ^ c ≤ 2 ^ (2 * c) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact lt_of_lt_of_le hc2 (Nat.pow_le_pow_right (by norm_num) hw)

public theorem wordSize_lt_two_pow_wordSize (c : ℕ) (x : List ℕ) :
    wordSize c x < 2 ^ wordSize c x :=
  Nat.lt_two_pow_self

public theorem readWord_lt (ω : ℕ → Bool) (pos w : ℕ) :
    readWord ω pos w < 2 ^ w := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih =>
    simp only [readWord, Nat.pow_succ]
    have h := ih (pos + 1)
    cases ω pos <;> simp <;> omega

public theorem readWord_mod_two_pow (ω : ℕ → Bool) (pos w w' : ℕ) (hle : w' ≤ w) :
    readWord ω pos w % 2 ^ w' = readWord ω pos w' := by
  induction w' generalizing pos w with
  | zero => simp [readWord, Nat.mod_one]
  | succ w' ih =>
    cases w with
    | zero => omega
    | succ w =>
      have hle' : w' ≤ w := Nat.le_of_succ_le_succ hle
      have hr : readWord ω (pos + 1) w % 2 ^ w' = readWord ω (pos + 1) w' := ih (pos + 1) w hle'
      have hlt : readWord ω (pos + 1) w' < 2 ^ w' := readWord_lt ω (pos + 1) w'
      simp only [readWord]
      have hmod : ((if ω pos then 1 else 0) + 2 * readWord ω (pos + 1) w) % 2 ^ (w' + 1) =
          (if ω pos then 1 else 0) + 2 * (readWord ω (pos + 1) w % 2 ^ w') := by
        have hq := Nat.div_add_mod (readWord ω (pos + 1) w) (2 ^ w')
        set q := readWord ω (pos + 1) w / 2 ^ w'
        set r := readWord ω (pos + 1) w % 2 ^ w'
        have hr_lt : r < 2 ^ w' := Nat.mod_lt _ (Nat.two_pow_pos w')
        have hpow : 2 ^ (w' + 1) = 2 * 2 ^ w' := by rw [Nat.pow_succ, Nat.mul_comm]
        rw [hpow, ← hq]
        have hre : (if ω pos then 1 else 0) + 2 * (2 ^ w' * q + r) =
            ((if ω pos then 1 else 0) + 2 * r) + (2 * 2 ^ w') * q := by ring
        rw [hre, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
        cases ω pos <;> simp <;> omega
      rw [hmod, hr]

public theorem readWord_congr {ω₁ ω₂ : ℕ → Bool} {p₁ p₂ w : ℕ}
    (h : ∀ j < w, ω₁ (p₁ + j) = ω₂ (p₂ + j)) :
    readWord ω₁ p₁ w = readWord ω₂ p₂ w := by
  induction w generalizing p₁ p₂ with
  | zero => simp [readWord]
  | succ w ih =>
    simp only [readWord]
    have h0 := h 0 (Nat.zero_lt_succ w)
    simp only [Nat.add_zero] at h0
    rw [h0]
    congr 2
    apply ih
    intro j hj
    have hj' := h (j + 1) (Nat.succ_lt_succ hj)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hj'

public theorem readWord_subBits (w w' pos k : ℕ) (ω : ℕ → Bool) (hle : w' ≤ w) :
    readWord (subBits w w' pos ω) (k * w') w' = readWord ω (pos + k * w) w % 2 ^ w' := by
  rw [readWord_mod_two_pow ω (pos + k * w) w w' hle]
  apply readWord_congr
  intro j hj
  simp only [subBits]
  have hdiv : (k * w' + j) / w' = k := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ (lt_of_le_of_lt (Nat.zero_le j) hj),
      Nat.div_eq_of_lt hj, Nat.zero_add]
  have hmod : (k * w' + j) % w' = j := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [hdiv, hmod, Nat.add_assoc]

public theorem listAt_ext {mem : ℕ → ℕ} {a : ℕ} {x y : List ℕ}
    (hx : ListAt mem a x) (hy : ListAt mem a y) (hlen : x.length = y.length) :
    x = y := by
  apply List.ext_getElem hlen
  intro i hi1 hi2
  rw [← hx i hi1, ← hy i hi2]

public theorem listAt_update_outside {mem : ℕ → ℕ} {a : ℕ} {x : List ℕ}
    (hx : ListAt mem a x) {addr val : ℕ} (h : addr < a ∨ a + x.length ≤ addr) :
    ListAt (Function.update mem addr val) a x := by
  intro i hi
  have hne : a + i ≠ addr := by omega
  simp [Function.update, hne, hx i hi]

public theorem zeroFrom_update_lt {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) {addr val : ℕ} (hlt : addr < h) :
    ZeroFrom (Function.update mem addr val) h := by
  intro a ha
  have hne : a ≠ addr := by omega
  simp [Function.update, hne, hz a ha]

public theorem listAt_range_map {f : ℕ → ℕ} (a n : ℕ) (mem : ℕ → ℕ)
    (h : ∀ i < n, mem (a + i) = f i) :
    ListAt mem a ((List.range n).map f) := by
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  simp only [List.getElem_map, List.getElem_range]
  exact h i hi

end Link

end WordRAM
