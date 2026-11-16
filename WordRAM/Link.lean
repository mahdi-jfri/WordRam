module

public import WordRAM.LinkDefs
import WordRAM.Exec

/-!
# Verification of the runner module

This file proves `runner_spec`, showing that `runner Q c b` correctly executes any program `Q`
(written for its own word size `w' = wordSize c x`) inside a host program of word size `w`
satisfying `h + 2 ^ (w' + 1) + 2 ≤ 2 ^ w`.

Procedure `b` computes `w' = wordSize c x` and `2 ^ w'`, copies `x` from `a` to `h + 1`, executes
the relocated procedures of `Q` (mapping addresses `e ↦ h + 1 + e`, procedure indices
`f ↦ b + 1 + f`, and `rand` to host `rand` modulo `2 ^ w'`, which matches `subBits w w' pos ω`),
stores the output length at `h`, leaves memory below `h` unchanged and memory from `h + 1 + 2 ^ w'`
zero, returns `h + 1 + 2 ^ w'`, and runs in cost `≤ runnerScale Q * (cost + len + w' + 1)`.
-/

namespace WordRAM

/-- Constant factor in the cost bound of `runner Q c`. -/
@[expose] public def runnerScale (Q : Program) : ℕ :=
  Q.regBound + 80

namespace Link

private theorem two_pow_lt_two_pow_of_lt {a b : ℕ} (h : 2 ^ a < 2 ^ b) : a < b := by
  by_contra hle
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_of_not_lt hle)
  omega

private theorem log_eq_of_bounds {n L : ℕ} (hL : 1 ≤ L) (h1 : 2 ^ (L - 1) ≤ n)
    (h2 : n < 2 ^ L) : L = Nat.log 2 n + 1 := by
  have hpos : 0 < 2 ^ (L - 1) := Nat.two_pow_pos _
  have hlog : Nat.log 2 n = L - 1 := by
    apply Nat.eq_of_le_of_lt_succ
    · exact Nat.le_log_of_pow_le (by norm_num) h1
    · rw [Nat.sub_add_cancel hL]
      exact Nat.log_lt_of_lt_pow (by omega) h2
  omega

/-- The scan loop in `computeWordSizeStmt` computes `x.foldr max 0` in register `tmp2`. -/
private theorem scan_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {aReg lenReg wReg tmp1 tmp2 tmp3 : ℕ}
    (hd : [aReg, lenReg, wReg, tmp1, tmp2, tmp3].Nodup)
    {a : ℕ} {x : List ℕ} {st : State}
    (ha : st.regs aReg = a) (hlen : st.regs lenReg = x.length)
    (hlist : ListAt st.mem a x)
    (hal : a + x.length < 2 ^ w) (h4 : 4 ≤ 2 ^ w)
    {i : ℕ} (hi : i ≤ x.length)
    (hi_reg : st.regs tmp1 = i) (hmx_reg : st.regs tmp2 = (x.take i).foldr max 0) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.reg tmp1) (.reg lenReg))
          (.seq (.assign tmp3 (.load (.bin .add (.reg aReg) (.reg tmp1))))
            (.seq (.cond (.bin .lt (.reg tmp2) (.reg tmp3))
                (.assign tmp2 (.reg tmp3)) .nop)
              (.assign tmp1 (.bin .add (.reg tmp1) (.const 1))))))
        st .normal st' c ∧
      st'.regs tmp1 = x.length ∧
      st'.regs tmp2 = x.foldr max 0 ∧
      st'.regs aReg = a ∧
      st'.regs lenReg = x.length ∧
      st'.mem = st.mem ∧
      st'.pos = st.pos ∧
      (∀ r, r ≠ tmp1 → r ≠ tmp2 → r ≠ tmp3 → st'.regs r = st.regs r) ∧
      c ≤ 25 * (x.length - i + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨_, _, ha_t1, ha_t2, ha_t3⟩,
    ⟨_, hl_t1, hl_t2, hl_t3⟩, _, ⟨ht1_t2, ht1_t3⟩, ht2_t3, _⟩
  have hlt1 : 1 < 2 ^ w := by omega
  suffices hrem : ∀ rem i (st : State), i ≤ x.length → x.length - i = rem →
      st.regs aReg = a → st.regs lenReg = x.length → ListAt st.mem a x →
      st.regs tmp1 = i → st.regs tmp2 = (x.take i).foldr max 0 →
      ∃ st' c, Runs w p ω _ st .normal st' c ∧
        st'.regs tmp1 = x.length ∧ st'.regs tmp2 = x.foldr max 0 ∧
        st'.regs aReg = a ∧ st'.regs lenReg = x.length ∧
        st'.mem = st.mem ∧ st'.pos = st.pos ∧
        (∀ r, r ≠ tmp1 → r ≠ tmp2 → r ≠ tmp3 → st'.regs r = st.regs r) ∧
        c ≤ 25 * (rem + 1) by
    exact hrem (x.length - i) i st hi rfl ha hlen hlist hi_reg hmx_reg
  intro rem
  induction rem with
  | zero =>
    intro i st hi hrem ha hlen hlist hi_reg hmx_reg
    have hieq : i = x.length := by omega
    subst hieq
    have hcond : (Expr.bin .lt (.reg tmp1) (.reg lenReg)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hi_reg, hlen]
    refine ⟨st, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, rfl⟩),
      hi_reg, ?_, ha, hlen, rfl, rfl, fun _ _ _ _ => rfl, by omega⟩
    simpa [List.take_length] using hmx_reg
  | succ rem ih =>
    intro i st hi hrem ha hlen hlist hi_reg hmx_reg
    have hilt : i < x.length := by omega
    have hcond : (Expr.bin .lt (.reg tmp1) (.reg lenReg)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hi_reg, hlen, hilt, hlt1]
    have hadd_ai : a + i < 2 ^ w := by omega
    have he1 : (Expr.load (.bin .add (.reg aReg) (.reg tmp1))).eval w st = some (x[i]) := by
      simp [Expr.eval, BinOp.eval, ha, hi_reg, hadd_ai, hlist i hilt]
    set st1 : State := { st with regs := Function.update st.regs tmp3 x[i] }
    have hs1 : Runs w p ω (.assign tmp3 (.load (.bin .add (.reg aReg) (.reg tmp1))))
        st .normal st1 5 := by
      rw [runs_assign_iff]
      exact ⟨x[i], he1, rfl, rfl, by simp [Expr.size]⟩
    have hst1_t1 : st1.regs tmp1 = i := by
      dsimp only [st1]; rw [Function.update_of_ne ht1_t3, hi_reg]
    have hst1_t2 : st1.regs tmp2 = (x.take i).foldr max 0 := by
      dsimp only [st1]; rw [Function.update_of_ne ht2_t3, hmx_reg]
    have hst1_t3 : st1.regs tmp3 = x[i] := by simp [st1]
    have hst1_a : st1.regs aReg = a := by
      dsimp only [st1]; rw [Function.update_of_ne ha_t3, ha]
    have hst1_l : st1.regs lenReg = x.length := by
      dsimp only [st1]; rw [Function.update_of_ne hl_t3, hlen]
    have he_lt : (Expr.bin .lt (.reg tmp2) (.reg tmp3)).eval w st1 =
        some (if (x.take i).foldr max 0 < x[i] then 1 else 0) := by
      simp only [Expr.eval, BinOp.eval, hst1_t2, hst1_t3]
      by_cases hcmp : (x.take i).foldr max 0 < x[i] <;> simp [hcmp, hlt1]
    have hcond_s : ∃ st2 c2,
        Runs w p ω (.cond (.bin .lt (.reg tmp2) (.reg tmp3)) (.assign tmp2 (.reg tmp3)) .nop)
          st1 .normal st2 c2 ∧
        st2.regs tmp2 = (x.take (i + 1)).foldr max 0 ∧
        st2.regs tmp1 = i ∧ st2.regs aReg = a ∧ st2.regs lenReg = x.length ∧
        st2.mem = st.mem ∧ st2.pos = st.pos ∧
        (∀ r, r ≠ tmp1 → r ≠ tmp2 → r ≠ tmp3 → st2.regs r = st.regs r) ∧
        c2 ≤ 6 := by
      by_cases hlt_mx : (x.take i).foldr max 0 < x[i]
      · refine ⟨{ st1 with regs := Function.update st1.regs tmp2 x[i] }, 6, ?_,
          ?_, ?_, ?_, ?_, rfl, rfl, ?_, by omega⟩
        · rw [runs_cond_iff]
          refine ⟨1, 2, ?_, ?_, by simp [Expr.size]⟩
          · simpa [hlt_mx] using he_lt
          · simp only [Nat.one_ne_zero, ↓reduceIte]
            rw [runs_assign_iff]
            exact ⟨x[i], by simp [Expr.eval, hst1_t3], rfl, rfl, by simp [Expr.size]⟩
        · simp [foldr_max_take_succ hilt, Nat.max_eq_right (le_of_lt hlt_mx)]
        · dsimp only; rw [Function.update_of_ne ht1_t2, hst1_t1]
        · simp [ha_t2, hst1_a]
        · simp [hl_t2, hst1_l]
        · intro r hr1 hr2 hr3
          simp [st1, hr2, hr3]
      · refine ⟨st1, 5, ?_, ?_, hst1_t1, hst1_a, hst1_l, rfl, rfl, ?_, by omega⟩
        · rw [runs_cond_iff]
          refine ⟨0, 1, ?_, ?_, by simp [Expr.size]⟩
          · simpa [hlt_mx] using he_lt
          · simp only [↓reduceIte]
            exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
        · rw [foldr_max_take_succ hilt, hst1_t2, Nat.max_eq_left (Nat.le_of_not_lt hlt_mx)]
        · intro r _ _ hr3
          simp [st1, hr3]
    rcases hcond_s with ⟨st2, c2, hs2, hst2_t2, hst2_t1, hst2_a, hst2_l, hst2_m, hst2_p, hst2_r, hc2⟩
    have hi1_lt : i + 1 < 2 ^ w := by omega
    have he_inc : (Expr.bin .add (.reg tmp1) (.const 1)).eval w st2 = some (i + 1) := by
      simp [Expr.eval, BinOp.eval, hst2_t1, hlt1, hi1_lt]
    set st3 : State := { st2 with regs := Function.update st2.regs tmp1 (i + 1) }
    have hs3 : Runs w p ω (.assign tmp1 (.bin .add (.reg tmp1) (.const 1))) st2 .normal st3 4 := by
      rw [runs_assign_iff]
      exact ⟨i + 1, he_inc, rfl, rfl, by simp [Expr.size]⟩
    have hbody_r2 := runs_seq_iff.mpr (Or.inr ⟨st2, c2, 4, hs2, hs3, rfl⟩)
    have hbody_r := runs_seq_iff.mpr (Or.inr ⟨st1, 5, c2 + 4 + 1, hs1, hbody_r2, rfl⟩)
    set c_b := 5 + (c2 + 4 + 1) + 1
    have hc_b : c_b ≤ 17 := by omega
    have hst3_a : st3.regs aReg = a := by simp [st3, ha_t1, hst2_a]
    have hst3_l : st3.regs lenReg = x.length := by simp [st3, hl_t1, hst2_l]
    have hst3_t1 : st3.regs tmp1 = i + 1 := by simp [st3]
    have hst3_t2 : st3.regs tmp2 = (x.take (i + 1)).foldr max 0 := by
      dsimp only [st3]
      rw [Function.update_of_ne (Ne.symm ht1_t2), hst2_t2]
    have hst3_m : ListAt st3.mem a x := by simpa [st3, hst2_m] using hlist
    have ih_r := ih (i + 1) st3 (by omega) (by omega) hst3_a hst3_l hst3_m hst3_t1 hst3_t2
    rcases ih_r with ⟨st', c_rest, hrest, hr1, hr2, hra, hrl, hrm, hrp, hrr, hcrest⟩
    refine ⟨st', 3 + c_b + c_rest + 1, ?_, hr1, hr2, hra, hrl, ?_, ?_, ?_, by omega⟩
    · rw [runs_loop_iff]
      exact Or.inr (Or.inr ⟨1, st3, c_b, c_rest, hcond, by omega, hbody_r, hrest,
        by simp [Expr.size]⟩)
    · simpa [st3, hst2_m] using hrm
    · simpa [st3, hst2_p] using hrp
    · intro r hr1' hr2' hr3'
      rw [hrr r hr1' hr2' hr3']
      simp [st3, hr1', hst2_r r hr1' hr2' hr3']

/-- The doubling loop in `computeWordSizeStmt` computes `Nat.log 2 n + 1` in register `wReg`. -/
private theorem log_loop_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {wReg tmp1 tmp2 : ℕ} (hd : [wReg, tmp1, tmp2].Nodup)
    {n w' : ℕ} (hn2 : 2 ≤ n) (hn_lt : 2 * n < 2 ^ w) (hlog_le : Nat.log 2 n + 1 ≤ w')
    (hw'_lt : w' < 2 ^ w) (h4 : 4 ≤ 2 ^ w) :
    ∀ {L : ℕ} {st : State},
      L ≤ Nat.log 2 n + 1 →
      (L = 0 ∨ 2 ^ (L - 1) ≤ n) →
      st.regs tmp1 = n →
      st.regs tmp2 = 2 ^ L →
      st.regs wReg = L →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .eq (.bin .lt (.reg tmp1) (.reg tmp2)) (.const 0))
            (.seq (.assign tmp2 (.bin .add (.reg tmp2) (.reg tmp2)))
              (.assign wReg (.bin .add (.reg wReg) (.const 1)))))
          st .normal st' c ∧
        st'.regs wReg = Nat.log 2 n + 1 ∧
        st'.mem = st.mem ∧
        st'.pos = st.pos ∧
        (∀ r, r ≠ wReg → r ≠ tmp2 → st'.regs r = st.regs r) ∧
        c ≤ 16 * (Nat.log 2 n + 1 - L + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hw_t1, hw_t2⟩, ht1_t2, _⟩
  have hlt1 : 1 < 2 ^ w := by omega
  intro L st hL hpow hn ht2 hw
  suffices hrem : ∀ rem L (st : State),
      L ≤ Nat.log 2 n + 1 → (Nat.log 2 n + 1) - L = rem →
      (L = 0 ∨ 2 ^ (L - 1) ≤ n) →
      st.regs tmp1 = n → st.regs tmp2 = 2 ^ L → st.regs wReg = L →
      ∃ st' c, Runs w p ω _ st .normal st' c ∧
        st'.regs wReg = Nat.log 2 n + 1 ∧
        st'.mem = st.mem ∧ st'.pos = st.pos ∧
        (∀ r, r ≠ wReg → r ≠ tmp2 → st'.regs r = st.regs r) ∧
        c ≤ 16 * (rem + 1) by
    exact hrem (Nat.log 2 n + 1 - L) L st hL rfl hpow hn ht2 hw
  intro rem
  induction rem with
  | zero =>
    intro L st hL hrem hpow hn ht2 hw
    have hLeq : L = Nat.log 2 n + 1 := by omega
    have hn_lt_p : n < 2 ^ L := by
      rw [hLeq]
      exact Nat.lt_pow_succ_log_self (by norm_num) n
    have hcond : (Expr.bin .eq (.bin .lt (.reg tmp1) (.reg tmp2)) (.const 0)).eval w st =
        some 0 := by
      simp [Expr.eval, BinOp.eval, hn, ht2, hn_lt_p, hlt1]
    refine ⟨st, 6, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]⟩),
      by omega, rfl, rfl, fun _ _ _ => rfl, by omega⟩
  | succ rem ih =>
    intro L st hL hrem hpow hn ht2 hw
    have hLlt : L ≤ Nat.log 2 n := by omega
    have hp_le_n : 2 ^ L ≤ n := Nat.pow_le_of_le_log (by omega) hLlt
    have hcond : (Expr.bin .eq (.bin .lt (.reg tmp1) (.reg tmp2)) (.const 0)).eval w st =
        some 1 := by
      have hnot : ¬ n < 2 ^ L := by omega
      simp [Expr.eval, BinOp.eval, hn, ht2, hnot, hlt1]
    have hpow2 : 2 ^ L + 2 ^ L = 2 ^ (L + 1) := by rw [Nat.pow_succ]; omega
    have hp2_lt : 2 ^ (L + 1) < 2 ^ w := by rw [← hpow2]; omega
    have hL1_lt : L + 1 < 2 ^ w := by omega
    have he1 : (Expr.bin .add (.reg tmp2) (.reg tmp2)).eval w st = some (2 ^ (L + 1)) := by
      simp [Expr.eval, BinOp.eval, ht2, hp2_lt, hpow2]
    set st1 : State := { st with regs := Function.update st.regs tmp2 (2 ^ (L + 1)) }
    have hs1 : Runs w p ω (.assign tmp2 (.bin .add (.reg tmp2) (.reg tmp2))) st .normal st1 4 := by
      rw [runs_assign_iff]
      exact ⟨2 ^ (L + 1), he1, rfl, rfl, by simp [Expr.size]⟩
    have hst1_w : st1.regs wReg = L := by simp [st1, hw_t2, hw]
    have he2 : (Expr.bin .add (.reg wReg) (.const 1)).eval w st1 = some (L + 1) := by
      simp [Expr.eval, BinOp.eval, hst1_w, hlt1, hL1_lt]
    set st2 : State := { st1 with regs := Function.update st1.regs wReg (L + 1) }
    have hs2 : Runs w p ω (.assign wReg (.bin .add (.reg wReg) (.const 1))) st1 .normal st2 4 := by
      rw [runs_assign_iff]
      exact ⟨L + 1, he2, rfl, rfl, by simp [Expr.size]⟩
    have hbody := runs_seq_iff.mpr (Or.inr ⟨st1, 4, 4, hs1, hs2, rfl⟩)
    have hst2_t1 : st2.regs tmp1 = n := by
      dsimp only [st2, st1]
      rw [Function.update_of_ne (Ne.symm hw_t1), Function.update_of_ne ht1_t2, hn]
    have hst2_t2 : st2.regs tmp2 = 2 ^ (L + 1) := by
      dsimp only [st2, st1]
      rw [Function.update_of_ne (Ne.symm hw_t2), Function.update_self]
    have hst2_w : st2.regs wReg = L + 1 := by simp [st2]
    have ih_r := ih (L + 1) st2 (by omega) (by omega) (Or.inr (by simpa using hp_le_n))
      hst2_t1 hst2_t2 hst2_w
    rcases ih_r with ⟨st', c_rest, hrest, hrw, hrm, hrp, hrr, hcrest⟩
    refine ⟨st', 5 + 9 + c_rest + 1, ?_, hrw, ?_, ?_, ?_, by omega⟩
    · rw [runs_loop_iff]
      exact Or.inr (Or.inr ⟨1, st2, 9, c_rest, hcond, by omega, hbody, hrest,
        by simp [Expr.size]⟩)
    · simpa [st2, st1] using hrm
    · simpa [st2, st1] using hrp
    · intro r hrw' hrt2'
      rw [hrr r hrw' hrt2']
      simp [st2, st1, hrw', hrt2']

/-- `computeWordSizeStmt` computes `w' = wordSize c x` in `wReg` and `2 ^ w'` in `WReg`. -/
public theorem computeWordSize_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {c aReg lenReg wReg WReg tmp1 tmp2 tmp3 : ℕ}
    (hd : [aReg, lenReg, wReg, WReg, tmp1, tmp2, tmp3].Nodup)
    {a : ℕ} {x : List ℕ} {st : State}
    (ha : st.regs aReg = a) (hlen : st.regs lenReg = x.length)
    (hlist : ListAt st.mem a x)
    (hal : a + x.length < 2 ^ w)
    (hw_bound : 2 ^ (wordSize c x + 1) + 2 ≤ 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (computeWordSizeStmt c aReg lenReg wReg WReg tmp1 tmp2 tmp3) st .normal st' cost ∧
      st'.regs wReg = wordSize c x ∧
      st'.regs WReg = 2 ^ wordSize c x ∧
      st'.mem = st.mem ∧
      st'.pos = st.pos ∧
      (∀ r, r ≠ wReg → r ≠ WReg → r ≠ tmp1 → r ≠ tmp2 → r ≠ tmp3 → st'.regs r = st.regs r) ∧
      cost ≤ 40 * (x.length + wordSize c x + 1) := by
  have h4 : 4 ≤ 2 ^ w := by
    have : 2 ≤ 2 ^ (wordSize c x + 1) := by
      have : 1 ≤ 2 ^ wordSize c x := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    omega
  have hlt1 : 1 < 2 ^ w := by omega
  have hlt2 : 2 < 2 ^ w := by omega
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨ha_l, ha_w, ha_W, ha_t1, ha_t2, ha_t3⟩,
    ⟨hl_w, hl_W, hl_t1, hl_t2, hl_t3⟩,
    ⟨hw_W, hw_t1, hw_t2, hw_t3⟩,
    ⟨hW_t1, hW_t2, hW_t3⟩,
    ⟨ht1_t2, ht1_t3⟩, ht2_t3, _⟩
  cases c with
  | zero =>
    simp only [computeWordSizeStmt]
    set st1 : State := { st with regs := Function.update st.regs wReg 0 }
    set st2 : State := { st1 with regs := Function.update st1.regs WReg 1 }
    have hs1 : Runs w p ω (.assign wReg (.const 0)) st .normal st1 2 := by
      rw [runs_assign_iff]
      exact ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
    have hs2 : Runs w p ω (.assign WReg (.const 1)) st1 .normal st2 2 := by
      rw [runs_assign_iff]
      exact ⟨1, by simp [Expr.eval, hlt1], rfl, rfl, by simp [Expr.size]⟩
    refine ⟨st2, 5, runs_seq_iff.mpr (Or.inr ⟨st1, 2, 2, hs1, hs2, rfl⟩),
      ?_, ?_, rfl, rfl, ?_, ?_⟩
    · simp [st2, st1, hw_W, wordSize]
    · simp [st2, wordSize]
    · intro r hrw hrW _ _ _
      simp [st2, st1, hrw, hrW]
    · simp [wordSize]; omega
  | succ c' =>
    have hc : 1 ≤ c' + 1 := Nat.succ_pos c'
    set w' := wordSize (c' + 1) x
    have hw_bound' : 2 ^ (w' + 1) + 2 ≤ 2 ^ w := hw_bound
    have hsum_lt_w' : x.length + x.foldr max 0 + 2 < 2 ^ w' := sum_lt_two_pow_wordSize hc x
    have h2sum_lt_w : 2 * (x.length + x.foldr max 0 + 2) < 2 ^ w := by
      have : 2 * 2 ^ w' = 2 ^ (w' + 1) := by rw [Nat.pow_succ]; omega
      omega
    have h2w'_lt : 2 ^ w' < 2 ^ w := by
      have : 2 ^ w' ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hc_lt : c' + 1 < 2 ^ w :=
      lt_of_lt_of_le (c_lt_two_pow_wordSize hc x) (le_of_lt h2w'_lt)
    have hw'_lt : w' < 2 ^ w :=
      lt_of_lt_of_le (wordSize_lt_two_pow_wordSize (c' + 1) x) (le_of_lt h2w'_lt)
    simp only [computeWordSizeStmt]
    -- Step 1: scan
    set st1 : State := { st with regs := Function.update st.regs tmp1 0 }
    set st2 : State := { st1 with regs := Function.update st1.regs tmp2 0 }
    have hs_t1 : Runs w p ω (.assign tmp1 (.const 0)) st .normal st1 2 := by
      rw [runs_assign_iff]
      exact ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
    have hs_t2 : Runs w p ω (.assign tmp2 (.const 0)) st1 .normal st2 2 := by
      rw [runs_assign_iff]
      exact ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
    have hnodup_scan : [aReg, lenReg, wReg, tmp1, tmp2, tmp3].Nodup := by
      simp [List.nodup_cons, ha_l, ha_w, ha_t1, ha_t2, ha_t3,
        hl_w, hl_t1, hl_t2, hl_t3, hw_t1, hw_t2, hw_t3, ht1_t2, ht1_t3, ht2_t3]
    have hscan_loop := scan_loop_runs (p := p) (ω := ω) hnodup_scan
      (show st2.regs aReg = a by simp [st2, st1, ha_t1, ha_t2, ha])
      (show st2.regs lenReg = x.length by simp [st2, st1, hl_t1, hl_t2, hlen])
      (show ListAt st2.mem a x by simpa [st2, st1] using hlist)
      hal h4 (Nat.zero_le x.length)
      (show st2.regs tmp1 = 0 by simp [st2, st1, ht1_t2])
      (show st2.regs tmp2 = (x.take 0).foldr max 0 by simp [st2])
    rcases hscan_loop with ⟨st3, c_scan, hscan_r, _, hst3_mx, hst3_a, hst3_l, hst3_m, hst3_p,
      hst3_r, hc_scan⟩
    have hscan_r2 := runs_seq_iff.mpr (Or.inr ⟨st2, 2, c_scan, hs_t2, hscan_r, rfl⟩)
    have hscan_full_r := runs_seq_iff.mpr (Or.inr ⟨st1, 2, 2 + c_scan + 1, hs_t1, hscan_r2, rfl⟩)
    set c_s := 2 + (2 + c_scan + 1) + 1
    have hc_s : c_s ≤ 25 * x.length + 31 := by omega
    -- Step 2: sumExpr, p=1, L=0
    set n := x.length + x.foldr max 0 + 2
    have hn2 : 2 ≤ n := by omega
    have hsum_eval : (Expr.bin .add (.bin .add (.reg lenReg) (.reg tmp2)) (.const 2)).eval w st3 =
        some n := by
      have h1 : x.length + x.foldr max 0 < 2 ^ w := by omega
      have h2 : n < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, hst3_l, hst3_mx, h1, hlt2, h2, n]
    set st4 : State := { st3 with regs := Function.update st3.regs tmp1 n }
    have hs4 : Runs w p ω
        (.assign tmp1 (.bin .add (.bin .add (.reg lenReg) (.reg tmp2)) (.const 2)))
        st3 .normal st4 6 := by
      rw [runs_assign_iff]
      exact ⟨n, hsum_eval, rfl, rfl, by simp [Expr.size]⟩
    set st5 : State := { st4 with regs := Function.update st4.regs tmp2 1 }
    have hs5 : Runs w p ω (.assign tmp2 (.const 1)) st4 .normal st5 2 := by
      rw [runs_assign_iff]
      exact ⟨1, by simp [Expr.eval, hlt1], rfl, rfl, by simp [Expr.size]⟩
    set st6 : State := { st5 with regs := Function.update st5.regs wReg 0 }
    have hs6 : Runs w p ω (.assign wReg (.const 0)) st5 .normal st6 2 := by
      rw [runs_assign_iff]
      exact ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
    have hnodup_log : [wReg, tmp1, tmp2].Nodup := by
      simp [List.nodup_cons, hw_t1, hw_t2, ht1_t2]
    have hlog_le_w' : Nat.log 2 n + 1 ≤ w' :=
      Nat.le_mul_of_pos_left (Nat.log 2 n + 1) hc
    have hlog := log_loop_runs (p := p) (ω := ω) hnodup_log hn2 h2sum_lt_w hlog_le_w' hw'_lt h4
      (L := 0) (st := st6) (Nat.zero_le _) (Or.inl rfl)
      (by simp [st6, st5, st4, Ne.symm hw_t1, ht1_t2])
      (by simp [st6, st5, Ne.symm hw_t2])
      (by simp [st6])
    rcases hlog with ⟨st7, c_log, hlog_r, hst7_w, hst7_m, hst7_p, hst7_r, hc_log⟩
    -- Step 3: multiply by c'+1 and compute 1 <<< w'
    have he_mul : (Expr.bin .mul (.const (c' + 1)) (.reg wReg)).eval w st7 = some w' := by
      have hmul_eq : (c' + 1) * (Nat.log 2 n + 1) = w' := rfl
      simp [Expr.eval, BinOp.eval, hc_lt, hst7_w, hmul_eq, hw'_lt]
    set st8 : State := { st7 with regs := Function.update st7.regs wReg w' }
    have hs8 : Runs w p ω (.assign wReg (.bin .mul (.const (c' + 1)) (.reg wReg)))
        st7 .normal st8 4 := by
      rw [runs_assign_iff]
      exact ⟨w', he_mul, rfl, rfl, by simp [Expr.size]⟩
    have he_shl : (Expr.bin .shiftLeft (.const 1) (.reg wReg)).eval w st8 = some (2 ^ w') := by
      have hshl : (1 : ℕ) <<< w' = 2 ^ w' := by simp [Nat.shiftLeft_eq]
      simp [Expr.eval, BinOp.eval, hlt1, hshl, h2w'_lt, st8]
    set st9 : State := { st8 with regs := Function.update st8.regs WReg (2 ^ w') }
    have hs9 : Runs w p ω (.assign WReg (.bin .shiftLeft (.const 1) (.reg wReg)))
        st8 .normal st9 4 := by
      rw [runs_assign_iff]
      exact ⟨2 ^ w', he_shl, rfl, rfl, by simp [Expr.size]⟩
    -- Compose everything
    have hr_89 := runs_seq_iff.mpr (Or.inr ⟨st8, 4, 4, hs8, hs9, rfl⟩)
    have hr_79 := runs_seq_iff.mpr (Or.inr ⟨st7, c_log, 4 + 4 + 1, hlog_r, hr_89, rfl⟩)
    have hr_69 := runs_seq_iff.mpr (Or.inr ⟨st6, 2, c_log + (4 + 4 + 1) + 1, hs6, hr_79, rfl⟩)
    have hr_59 := runs_seq_iff.mpr (Or.inr ⟨st5, 2, 2 + (c_log + (4 + 4 + 1) + 1) + 1, hs5, hr_69, rfl⟩)
    have hlog_seq_r := runs_seq_iff.mpr (Or.inr ⟨st4, 6, 2 + (2 + (c_log + (4 + 4 + 1) + 1) + 1) + 1, hs4, hr_59, rfl⟩)
    set c_l := 6 + (2 + (2 + (c_log + (4 + 4 + 1) + 1) + 1) + 1) + 1
    have hc_l : c_l ≤ 16 * w' + 40 := by
      have : c_log ≤ 16 * (w' + 1) := by
        have : Nat.log 2 n + 1 - 0 + 1 ≤ w' + 1 := by omega
        calc c_log ≤ 16 * (Nat.log 2 n + 1 - 0 + 1) := hc_log
          _ ≤ 16 * (w' + 1) := Nat.mul_le_mul_left 16 this
      omega
    refine ⟨st9, c_s + c_l + 1, runs_seq_iff.mpr (Or.inr ⟨st3, c_s, c_l, hscan_full_r, hlog_seq_r, rfl⟩),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [st9, st8, hw_W]
    · simp [st9]
    · simpa [st9, st8, st6, st5, st4, hst7_m] using hst3_m
    · simpa [st9, st8, st6, st5, st4, hst7_p] using hst3_p
    · intro r hrw hrW hrt1 hrt2 hrt3
      have hr8 : st8.regs r = st7.regs r := by simp [st8, hrw]
      have hr9 : st9.regs r = st8.regs r := by simp [st9, hrW]
      have hr7 : st7.regs r = st6.regs r := hst7_r r hrw hrt2
      have hr6 : st6.regs r = st5.regs r := by simp [st6, hrw]
      have hr5 : st5.regs r = st4.regs r := by simp [st5, hrt2]
      have hr4 : st4.regs r = st3.regs r := by simp [st4, hrt1]
      have hr3 : st3.regs r = st2.regs r := hst3_r r hrt1 hrt2 hrt3
      have hr2 : st2.regs r = st1.regs r := by simp [st2, hrt2]
      have hr1 : st1.regs r = st.regs r := by simp [st1, hrt1]
      omega
    · have : c_s + c_l + 1 ≤ 40 * (x.length + w' + 1) := by
        have hw'2 : 2 ≤ w' := two_le_wordSize_of_pos hc x
        omega
      exact this

/-- `copyWordsStmt` copies `len` words from `src` to `dst` when `src + len ≤ dst` and `dst + len < 2 ^ w`. -/
public theorem copyWords_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    {srcReg dstReg lenReg idxReg : ℕ}
    (hd : [srcReg, dstReg, lenReg, idxReg].Nodup)
    {src dst : ℕ} {x : List ℕ} {st : State}
    (hsrc : st.regs srcReg = src) (hdst : st.regs dstReg = dst) (hlen : st.regs lenReg = x.length)
    (hlist : ListAt st.mem src x)
    (hdisj : src + x.length ≤ dst) (hdst_lt : dst + x.length < 2 ^ w) (h4 : 4 ≤ 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (copyWordsStmt srcReg dstReg lenReg idxReg) st .normal st' cost ∧
      ListAt st'.mem dst x ∧
      (∀ addr, addr < dst ∨ dst + x.length ≤ addr → st'.mem addr = st.mem addr) ∧
      st'.pos = st.pos ∧
      (∀ r, r ≠ idxReg → st'.regs r = st.regs r) ∧
      cost ≤ 17 * (x.length + 1) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hd
  rcases hd with ⟨⟨hs_d, hs_l, hs_i⟩, ⟨hd_l, hd_i⟩, hl_i, _⟩
  have hlt1 : 1 < 2 ^ w := by omega
  set st0 : State := { st with regs := Function.update st.regs idxReg 0 }
  have hs0 : Runs w p ω (.assign idxReg (.const 0)) st .normal st0 2 := by
    rw [runs_assign_iff]
    exact ⟨0, by simp [Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  suffices hrem : ∀ rem i (st_c : State) (hi : i ≤ x.length), x.length - i = rem →
      st_c.regs srcReg = src → st_c.regs dstReg = dst → st_c.regs lenReg = x.length →
      st_c.regs idxReg = i →
      (∀ j (hj : j < i), st_c.mem (dst + j) = x[j]'(lt_of_lt_of_le hj hi)) →
      (∀ addr, addr < dst ∨ dst + i ≤ addr → st_c.mem addr = st.mem addr) →
      st_c.pos = st.pos →
      ∃ st' c, Runs w p ω
        (.loop (.bin .lt (.reg idxReg) (.reg lenReg))
          (.seq (.store (.bin .add (.reg dstReg) (.reg idxReg))
                  (.load (.bin .add (.reg srcReg) (.reg idxReg))))
            (.assign idxReg (.bin .add (.reg idxReg) (.const 1)))))
        st_c .normal st' c ∧
        ListAt st'.mem dst x ∧
        (∀ addr, addr < dst ∨ dst + x.length ≤ addr → st'.mem addr = st.mem addr) ∧
        st'.pos = st.pos ∧
        (∀ r, r ≠ idxReg → st'.regs r = st_c.regs r) ∧
        c ≤ 17 * rem + 4 by
    have hr := hrem x.length 0 st0 (Nat.zero_le _) (by omega)
      (by simp [st0, hs_i, hsrc]) (by simp [st0, hd_i, hdst]) (by simp [st0, hl_i, hlen])
      (by simp [st0]) (fun _ hj => absurd hj (Nat.not_lt_zero _)) (fun _ _ => rfl) rfl
    rcases hr with ⟨st', c_l, hl_r, hlist', hmem', hpos', hregs', hc_l⟩
    refine ⟨st', 2 + c_l + 1, runs_seq_iff.mpr (Or.inr ⟨st0, 2, c_l, hs0, hl_r, rfl⟩),
      hlist', hmem', hpos', ?_, by omega⟩
    intro r hr
    rw [hregs' r hr]
    simp [st0, hr]
  intro rem
  induction rem with
  | zero =>
    intro i st_c hi hrem hs hd_r hl_r hi_r hpre houts hp
    have hieq : i = x.length := by omega
    subst hieq
    have hcond : (Expr.bin .lt (.reg idxReg) (.reg lenReg)).eval w st_c = some 0 := by
      simp [Expr.eval, BinOp.eval, hi_r, hl_r]
    refine ⟨st_c, 4, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, by simp [Expr.size]⟩),
      fun j hj => hpre j hj, houts, hp, fun _ _ => rfl, by omega⟩
  | succ rem ih =>
    intro i st_c hi hrem hs hd_r hl_r hi_r hpre houts hp
    have hilt : i < x.length := by omega
    have hcond : (Expr.bin .lt (.reg idxReg) (.reg lenReg)).eval w st_c = some 1 := by
      simp [Expr.eval, BinOp.eval, hi_r, hl_r, hilt, hlt1]
    have hdst_i : dst + i < 2 ^ w := by omega
    have hsrc_i : src + i < 2 ^ w := by omega
    have hsrc_mem : st_c.mem (src + i) = x[i] := by
      rw [houts (src + i) (Or.inl (by omega))]
      exact hlist i hilt
    have he_addr : (Expr.bin .add (.reg dstReg) (.reg idxReg)).eval w st_c = some (dst + i) := by
      simp [Expr.eval, BinOp.eval, hd_r, hi_r, hdst_i]
    have he_val : (Expr.load (.bin .add (.reg srcReg) (.reg idxReg))).eval w st_c = some (x[i]) := by
      simp [Expr.eval, BinOp.eval, hs, hi_r, hsrc_i, hsrc_mem]
    set st1 : State := { st_c with mem := Function.update st_c.mem (dst + i) (x[i]) }
    have hstore : Runs w p ω
        (.store (.bin .add (.reg dstReg) (.reg idxReg))
          (.load (.bin .add (.reg srcReg) (.reg idxReg))))
        st_c .normal st1 8 := by
      rw [runs_store_iff]
      exact ⟨dst + i, x[i], he_addr, he_val, rfl, rfl, by simp [Expr.size]⟩
    have hi1_lt : i + 1 < 2 ^ w := by omega
    have he_inc : (Expr.bin .add (.reg idxReg) (.const 1)).eval w st1 = some (i + 1) := by
      simp [Expr.eval, BinOp.eval, st1, hi_r, hlt1, hi1_lt]
    set st2 : State := { st1 with regs := Function.update st1.regs idxReg (i + 1) }
    have hinc : Runs w p ω (.assign idxReg (.bin .add (.reg idxReg) (.const 1)))
        st1 .normal st2 4 := by
      rw [runs_assign_iff]
      exact ⟨i + 1, he_inc, rfl, rfl, by simp [Expr.size]⟩
    have hbody := runs_seq_iff.mpr (Or.inr ⟨st1, 8, 4, hstore, hinc, rfl⟩)
    have hpre' : ∀ j (hj : j < i + 1), st2.mem (dst + j) = x[j]'(lt_of_lt_of_le hj (by omega)) := by
      intro j hj
      by_cases hj_eq : j = i
      · subst hj_eq; simp [st2, st1]
      · have hne : dst + j ≠ dst + i := by omega
        dsimp only [st2, st1]
        rw [Function.update_of_ne hne]
        exact hpre j (by omega)
    have houts' : ∀ addr, addr < dst ∨ dst + (i + 1) ≤ addr → st2.mem addr = st.mem addr := by
      intro addr haddr
      have hne : addr ≠ dst + i := by omega
      simp [st2, st1, hne, houts addr (by omega)]
    have ih_r := ih (i + 1) st2 (by omega) (by omega)
      (by simp [st2, st1, hs_i, hs]) (by simp [st2, st1, hd_i, hd_r]) (by simp [st2, st1, hl_i, hl_r])
      (by simp [st2]) hpre' houts' hp
    rcases ih_r with ⟨st', c_rest, hrest, hlist', hmem', hpos', hregs', hc_rest⟩
    refine ⟨st', 3 + 13 + c_rest + 1, ?_, hlist', hmem', hpos', ?_, by omega⟩
    · rw [runs_loop_iff]
      exact Or.inr (Or.inr ⟨1, st2, 13, c_rest, hcond, by omega, hbody, hrest,
        by simp [Expr.size]⟩)
    · intro r hr
      rw [hregs' r hr]
      simp [st2, st1, hr]

/-- Evaluating a relocated expression in host state `st_H` matches evaluating `e` in `Q`-state `st_Q`. -/
private theorem eval_relocExpr {w w' R h : ℕ} {e : Expr} {st_Q st_H : State} {v : ℕ}
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w)
    (he_reg : e.regBound ≤ R)
    (hregs : ∀ r < R, st_H.regs r = st_Q.regs r)
    (hbase : st_H.regs R = h + 1)
    (hq_regs : ∀ r, st_Q.regs r < 2 ^ w')
    (hq_mem : ∀ a, st_Q.mem a < 2 ^ w')
    (hmem : ∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a)
    (he : e.eval w' st_Q = some v) :
    (relocExpr R e).eval w st_H = some v ∧ v < 2 ^ w' := by
  have hpow_le : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw_le
  induction e generalizing v with
  | const k =>
    simp only [Expr.eval] at he
    split_ifs at he with hk
    cases he
    have hk_w : k < 2 ^ w := lt_of_lt_of_le hk hpow_le
    simp [relocExpr, Expr.eval, hk_w, hk]
  | reg r =>
    simp only [Expr.eval, Option.some.injEq] at he
    subst he
    have hr : r < R := by simpa [Expr.regBound] using he_reg
    simp [relocExpr, Expr.eval, hregs r hr, hq_regs r]
  | load addr ih =>
    simp only [Expr.eval, Option.map_eq_some_iff] at he
    rcases he with ⟨addr_val, ha_eval, rfl⟩
    have ha_ih := ih (by simpa [Expr.regBound] using he_reg) ha_eval
    rcases ha_ih with ⟨ha_H, ha_lt⟩
    have hsum_lt : h + 1 + addr_val < 2 ^ w := by omega
    simp only [relocExpr, Expr.eval, BinOp.eval, hbase, ha_H, hsum_lt, ↓reduceIte,
      Option.map_some]
    exact ⟨congrArg some (hmem addr_val ha_lt), hq_mem addr_val⟩
  | bin op a b iha ihb =>
    simp only [Expr.eval] at he
    cases ha : a.eval w' st_Q with
    | none => simp [ha] at he
    | some x =>
      cases hb : b.eval w' st_Q with
      | none => simp [ha, hb] at he
      | some y =>
        simp only [ha, hb] at he
        split_ifs at he with hxy
        cases he
        simp only [Expr.regBound, max_le_iff] at he_reg
        rcases iha he_reg.1 ha with ⟨ha_H, _⟩
        rcases ihb he_reg.2 hb with ⟨hb_H, _⟩
        have hxy_w : op.eval x y < 2 ^ w := lt_of_lt_of_le hxy hpow_le
        simp [relocExpr, Expr.eval, ha_H, hb_H, hxy_w, hxy]

/-- Evaluating relocated call arguments in `st_H` matches evaluating `args` in `st_Q`. -/
private theorem evalArgs_reloc {w w' R h : ℕ} {args : List Expr} {st_Q st_H : State}
    {vs : List ℕ}
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w)
    (hargs_reg : argsRegBound args ≤ R)
    (hregs : ∀ r < R, st_H.regs r = st_Q.regs r)
    (hbase : st_H.regs R = h + 1)
    (hq_regs : ∀ r, st_Q.regs r < 2 ^ w')
    (hq_mem : ∀ a, st_Q.mem a < 2 ^ w')
    (hmem : ∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a)
    (hargs : evalArgs w' st_Q args = some vs) :
    evalArgs w st_H (args.map (relocExpr R)) = some vs ∧ vs.length = args.length ∧
      (∀ v ∈ vs, v < 2 ^ w') := by
  induction args generalizing vs with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at hargs
    subst hargs
    simp [evalArgs]
  | cons e es ih =>
    simp only [evalArgs] at hargs
    cases he : e.eval w' st_Q with
    | none => simp [he] at hargs
    | some x =>
      cases hes : evalArgs w' st_Q es with
      | none => simp [he, hes] at hargs
      | some xs =>
        simp only [he, hes, Option.some.injEq] at hargs
        subst hargs
        simp only [argsRegBound, max_le_iff] at hargs_reg
        rcases eval_relocExpr hw_le hh hargs_reg.1 hregs hbase hq_regs hq_mem hmem he with
          ⟨he_H, hx_lt⟩
        rcases ih hargs_reg.2 hes with ⟨hes_H, hlen, hxs_lt⟩
        refine ⟨by simp [evalArgs, he_H, hes_H], by simp [hlen], ?_⟩
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv'
        · exact hx_lt
        · exact hxs_lt v hv'

public theorem evalArgs_append {w : ℕ} {st : State} {xs ys : List Expr}
    {vxs vys : List ℕ}
    (hxs : evalArgs w st xs = some vxs) (hys : evalArgs w st ys = some vys) :
    evalArgs w st (xs ++ ys) = some (vxs ++ vys) := by
  induction xs generalizing vxs with
  | nil =>
    simp only [evalArgs, Option.some.injEq] at hxs
    subst hxs
    simpa using hys
  | cons e es ih =>
    simp only [evalArgs] at hxs
    cases he : e.eval w st with
    | none => simp [he] at hxs
    | some v =>
      cases hes : evalArgs w st es with
      | none => simp [he, hes] at hxs
      | some vs =>
        simp only [he, hes, Option.some.injEq] at hxs
        subst hxs
        simp only [List.cons_append, evalArgs, he, ih hes]

public theorem evalArgs_replicate_zero {w n : ℕ} {st : State} :
    evalArgs w st (List.replicate n (.const 0)) = some (List.replicate n 0) := by
  induction n with
  | zero => simp [evalArgs]
  | succ n ih =>
    simp [List.replicate_succ, evalArgs, Expr.eval, ih]

/-- Relocated statements simulate source execution inside region `[h + 1, h + 1 + 2 ^ w')` under
the low `w'` bits `subBits w w' pos₀ ω`. -/
public theorem runs_relocStmt {w w' h b : ℕ} {Q p : Program} {ω : ℕ → Bool} {pos₀ : ℕ}
    (hp : ∀ f body, Q.procs[f]? = some body →
      p.procs[b + 1 + f]? = some (relocStmt Q.regBound b body))
    (hw_le : w' ≤ w) (hh : h + 1 + 2 ^ w' ≤ 2 ^ w) (_h4 : 4 ≤ 2 ^ w) :
    ∀ fuel s st_Q st_H k o st_Q' c_Q,
      s.regBound ≤ Q.regBound →
      st_H.regs Q.regBound = h + 1 →
      st_H.regs (Q.regBound + 1) = 2 ^ w' →
      (∀ r < Q.regBound, st_H.regs r = st_Q.regs r) →
      (∀ r, st_Q.regs r < 2 ^ w') →
      (∀ a, st_Q.mem a < 2 ^ w') →
      (∀ a < 2 ^ w', st_H.mem (h + 1 + a) = st_Q.mem a) →
      st_Q.pos = k * w' →
      st_H.pos = pos₀ + k * w →
      exec w' Q (subBits w w' pos₀ ω) fuel s st_Q = some (o, st_Q', c_Q) →
      ∃ st_H' c_H k',
        Runs w p ω (relocStmt Q.regBound b s) st_H o st_H' c_H ∧
        c_H ≤ (Q.regBound + 6) * c_Q ∧
        o.value < 2 ^ w' ∧
        st_H'.regs Q.regBound = h + 1 ∧
        st_H'.regs (Q.regBound + 1) = 2 ^ w' ∧
        (∀ r < Q.regBound, st_H'.regs r = st_Q'.regs r) ∧
        (∀ r, st_Q'.regs r < 2 ^ w') ∧
        (∀ a, st_Q'.mem a < 2 ^ w') ∧
        (∀ a < 2 ^ w', st_H'.mem (h + 1 + a) = st_Q'.mem a) ∧
        (∀ addr, addr < h + 1 ∨ h + 1 + 2 ^ w' ≤ addr → st_H'.mem addr = st_H.mem addr) ∧
        st_Q'.pos = k' * w' ∧
        st_H'.pos = pos₀ + k' * w := by
  set R := Q.regBound
  have h1R : 1 ≤ R := one_le_regBound Q
  have hpow_le : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw_le
  have hw'_pos : 0 < 2 ^ w' := Nat.two_pow_pos w'
  intro fuel
  induction fuel with
  | zero =>
    intro s st_Q st_H k o st_Q' c_Q
    simp [exec]
  | succ fuel ih =>
    intro s st_Q st_H k o st_Q' c_Q hs_reg hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hex
    cases s with
    | nop =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hex
      rcases hex with ⟨rfl, rfl, rfl⟩
      refine ⟨st_H, 1, k, runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by omega, hw'_pos,
        hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl, hq_pos, hH_pos⟩
    | assign r e =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hex
        rcases hex with ⟨rfl, rfl, rfl⟩
        simp only [Stmt.regBound, max_le_iff] at hs_reg
        rcases eval_relocExpr hw_le hh hs_reg.2 hregs hbase hq_regs hq_mem hmem he with
          ⟨he_H, hv_lt⟩
        set st_H' : State := { st_H with regs := Function.update st_H.regs r v }
        have hr_R : r < R := by omega
        have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
          have h1 := relocExpr_size_le R e
          have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
          have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
          omega
        refine ⟨st_H', (relocExpr R e).size + 1, k,
          runs_assign_iff.mpr ⟨v, he_H, rfl, rfl, rfl⟩,
          hc_eq, hw'_pos, ?_, ?_, ?_, ?_, hq_mem, hmem, fun _ _ => rfl, hq_pos, hH_pos⟩
        · simp [st_H', hbase, show R ≠ r by omega]
        · simp [st_H', hW, show R + 1 ≠ r by omega]
        · intro r' hr'
          by_cases hrr' : r' = r
          · subst hrr'; simp [st_H']
          · simp [st_H', hrr', hregs r' hr']
        · intro r'
          by_cases hrr' : r' = r
          · subst hrr'; simpa using hv_lt
          · simp [Function.update, hrr', hq_regs r']
    | store a e =>
      simp only [exec] at hex
      cases ha : a.eval w' st_Q with
      | none => simp [ha] at hex
      | some addr_v =>
        cases he : e.eval w' st_Q with
        | none => simp [ha, he] at hex
        | some val_v =>
          simp only [ha, he, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          simp only [Stmt.regBound, max_le_iff] at hs_reg
          rcases eval_relocExpr hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem ha with
            ⟨ha_H, haddr_lt⟩
          rcases eval_relocExpr hw_le hh hs_reg.2 hregs hbase hq_regs hq_mem hmem he with
            ⟨he_H, hval_lt⟩
          have hsum_lt : h + 1 + addr_v < 2 ^ w := by omega
          have haddr_H : (Expr.bin .add (.reg R) (relocExpr R a)).eval w st_H =
              some (h + 1 + addr_v) := by
            simp [Expr.eval, BinOp.eval, hbase, ha_H, hsum_lt]
          set st_H' : State := { st_H with mem := Function.update st_H.mem (h + 1 + addr_v) val_v }
          have hc_eq : (Expr.bin .add (.reg R) (relocExpr R a)).size + (relocExpr R e).size + 1 ≤
              (R + 6) * (a.size + e.size + 1) := by
            have h1 := relocExpr_size_le R a
            have h2 := relocExpr_size_le R e
            have h3 : 3 * a.size ≤ (R + 6) * a.size := Nat.mul_le_mul_right a.size (by omega)
            have h4 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            have hmul : (R + 6) * (a.size + e.size + 1) =
                (R + 6) * a.size + (R + 6) * e.size + (R + 6) := by ring
            simp only [Expr.size]
            omega
          refine ⟨st_H', (Expr.bin .add (.reg R) (relocExpr R a)).size + (relocExpr R e).size + 1, k,
            runs_store_iff.mpr ⟨h + 1 + addr_v, val_v, haddr_H, he_H, rfl, rfl, rfl⟩,
            hc_eq, hw'_pos, hbase, hW, hregs, hq_regs, ?_, ?_, ?_, hq_pos, hH_pos⟩
          · intro addr'
            by_cases ha' : addr' = addr_v
            · subst ha'; simpa using hval_lt
            · simp [Function.update, ha', hq_mem addr']
          · intro addr' haddr'
            by_cases ha' : addr' = addr_v
            · subst ha'; simp [st_H']
            · have hne : h + 1 + addr' ≠ h + 1 + addr_v := by omega
              simp [st_H', Function.update, ha', hmem addr' haddr']
          · intro addr' houts
            have hne : addr' ≠ h + 1 + addr_v := by omega
            simp [st_H', hne]
    | rand r =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hex
      rcases hex with ⟨rfl, rfl, rfl⟩
      have hr_R : r < R := by simpa [Stmt.regBound] using hs_reg
      set rnd := readWord ω st_H.pos w
      set rnd' := rnd % 2 ^ w'
      have hrnd'_eq : readWord (subBits w w' pos₀ ω) st_Q.pos w' = rnd' := by
        dsimp only [rnd', rnd]
        rw [hq_pos, hH_pos]
        exact readWord_subBits w w' pos₀ k ω hw_le
      have hrnd'_lt : rnd' < 2 ^ w' := Nat.mod_lt _ hw'_pos
      set st_H1 : State := { st_H with regs := Function.update st_H.regs r rnd, pos := st_H.pos + w }
      have hs1 : Runs w p ω (.rand r) st_H .normal st_H1 1 :=
        runs_rand_iff.mpr ⟨rfl, rfl, rfl⟩
      have he_mod : (Expr.bin .mod (.reg r) (.reg (R + 1))).eval w st_H1 = some rnd' := by
        have hW1 : st_H1.regs (R + 1) = 2 ^ w' := by simp [st_H1, hW, show R + 1 ≠ r by omega]
        have hr1 : st_H1.regs r = rnd := by simp [st_H1]
        have hrnd'_w : rnd' < 2 ^ w := lt_of_lt_of_le hrnd'_lt hpow_le
        simp [Expr.eval, BinOp.eval, hr1, hW1, hrnd'_w, rnd']
      set st_H2 : State := { st_H1 with regs := Function.update st_H1.regs r rnd' }
      have hs2 : Runs w p ω (.assign r (.bin .mod (.reg r) (.reg (R + 1)))) st_H1 .normal st_H2 4 := by
        rw [runs_assign_iff]
        exact ⟨rnd', he_mod, rfl, rfl, by simp [Expr.size]⟩
      refine ⟨st_H2, 6, k + 1, runs_seq_iff.mpr (Or.inr ⟨st_H1, 1, 4, hs1, hs2, rfl⟩),
        by omega, hw'_pos, ?_, ?_, ?_, ?_, hq_mem, hmem, fun _ _ => rfl, ?_, ?_⟩
      · simp [st_H2, st_H1, hbase, show R ≠ r by omega]
      · simp [st_H2, st_H1, hW, show R + 1 ≠ r by omega]
      · intro r' hr'
        by_cases hrr' : r' = r
        · subst hrr'; simp [st_H2, hrnd'_eq]
        · simp [st_H2, st_H1, hrr', hregs r' hr']
      · intro r'
        by_cases hrr' : r' = r
        · subst hrr'; simpa using readWord_lt (subBits w w' pos₀ ω) st_Q.pos w'
        · simp [Function.update, hrr', hq_regs r']
      · rw [hq_pos]; ring
      · dsimp only [st_H2, st_H1]; rw [hH_pos]; ring
    | seq s₁ s₂ =>
      simp only [exec] at hex
      simp only [Stmt.regBound, max_le_iff] at hs_reg
      cases hs₁ : exec w' Q (subBits w w' pos₀ ω) fuel s₁ st_Q with
      | none => simp [hs₁] at hex
      | some res₁ =>
        rcases res₁ with ⟨o₁, st₁, c₁⟩
        cases o₁ with
        | returned v =>
          simp only [hs₁, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          rcases ih s₁ st_Q st_H k (.returned v) st₁ c₁
            hs_reg.1 hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hs₁ with
            ⟨st_H', c_H1, k', hr1, hc1, hv_lt, hb', hW', hregs', hqr', hqm', hmm', houts',
              hqpos', hHpos'⟩
          refine ⟨st_H', c_H1 + 1, k',
            runs_seq_iff.mpr (Or.inl ⟨v, c_H1, hr1, rfl, rfl⟩),
            ?_, hv_lt, hb', hW', hregs', hqr', hqm', hmm', houts', hqpos', hHpos'⟩
          have : (R + 6) * (c₁ + 1) = (R + 6) * c₁ + (R + 6) := by ring
          omega
        | normal =>
          simp only [hs₁] at hex
          cases hs₂ : exec w' Q (subBits w w' pos₀ ω) fuel s₂ st₁ with
          | none => simp [hs₂] at hex
          | some res₂ =>
            rcases res₂ with ⟨o₂, st₂, c₂⟩
            simp only [hs₂, Option.some.injEq, Prod.mk.injEq] at hex
            rcases hex with ⟨rfl, rfl, rfl⟩
            rcases ih s₁ st_Q st_H k .normal st₁ c₁
              hs_reg.1 hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hs₁ with
              ⟨st_H1, c_H1, k₁, hr1, hc1, _, hb1, hW1, hregs1, hqr1, hqm1, hmm1, houts1,
                hqpos1, hHpos1⟩
            rcases ih s₂ st₁ st_H1 k₁ o₂ st₂ c₂
              hs_reg.2 hb1 hW1 hregs1 hqr1 hqm1 hmm1 hqpos1 hHpos1 hs₂ with
              ⟨st_H', c_H2, k', hr2, hc2, ho', hb', hW', hregs', hqr', hqm', hmm', houts',
                hqpos', hHpos'⟩
            refine ⟨st_H', c_H1 + c_H2 + 1, k',
              runs_seq_iff.mpr (Or.inr ⟨st_H1, c_H1, c_H2, hr1, hr2, rfl⟩),
              ?_, ho', hb', hW', hregs', hqr', hqm', hmm', ?_, hqpos', hHpos'⟩
            · have : (R + 6) * (c₁ + c₂ + 1) = (R + 6) * c₁ + (R + 6) * c₂ + (R + 6) := by ring
              omega
            · intro addr haddr
              rw [houts' addr haddr, houts1 addr haddr]
    | cond e s₁ s₂ =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he] at hex
        cases hbr : exec w' Q (subBits w w' pos₀ ω) fuel (if v = 0 then s₂ else s₁) st_Q with
        | none => simp [hbr] at hex
        | some res =>
          rcases res with ⟨o₁, st₁, c₁⟩
          simp only [hbr, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          simp only [Stmt.regBound, max_le_iff] at hs_reg
          rcases eval_relocExpr hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem he with
            ⟨he_H, _⟩
          have hbr_reg : (if v = 0 then s₂ else s₁).regBound ≤ R := by
            split_ifs <;> [exact hs_reg.2.2; exact hs_reg.2.1]
          have hbr_reloc : relocStmt R b (if v = 0 then s₂ else s₁) =
              if v = 0 then relocStmt R b s₂ else relocStmt R b s₁ := by
            split_ifs <;> rfl
          rcases ih (if v = 0 then s₂ else s₁) st_Q st_H k o₁ st₁ c₁
            hbr_reg hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hbr with
            ⟨st_H', c_H1, k', hr_br, hc1, ho', hb', hW', hregs', hqr', hqm', hmm', houts',
              hqpos', hHpos'⟩
          rw [hbr_reloc] at hr_br
          have hc_eq : (relocExpr R e).size + c_H1 + 1 ≤ (R + 6) * (e.size + c₁ + 1) := by
            have h1 := relocExpr_size_le R e
            have h2 : (R + 6) * (e.size + c₁ + 1) = (R + 6) * e.size + (R + 6) * c₁ + (R + 6) := by
              ring
            have h3 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            have h4 : c₁ ≤ (R + 6) * c₁ := Nat.le_mul_of_pos_left c₁ (by omega)
            omega
          refine ⟨st_H', (relocExpr R e).size + c_H1 + 1, k',
            runs_cond_iff.mpr ⟨v, c_H1, he_H, hr_br, rfl⟩,
            hc_eq, ho', hb', hW', hregs', hqr', hqm', hmm', houts', hqpos', hHpos'⟩
    | loop e body =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he] at hex
        have hs_reg' := hs_reg
        simp only [Stmt.regBound, max_le_iff] at hs_reg
        rcases eval_relocExpr hw_le hh hs_reg.1 hregs hbase hq_regs hq_mem hmem he with
          ⟨he_H, _⟩
        by_cases hv : v = 0
        · subst hv
          simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hex
          rcases hex with ⟨rfl, rfl, rfl⟩
          have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
            have h1 := relocExpr_size_le R e
            have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
            have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
            omega
          refine ⟨st_H, (relocExpr R e).size + 1, k,
            runs_loop_iff.mpr (Or.inl ⟨he_H, rfl, rfl, rfl⟩),
            hc_eq, hw'_pos, hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl,
            hq_pos, hH_pos⟩
        · simp only [hv, ↓reduceIte] at hex
          cases hbody : exec w' Q (subBits w w' pos₀ ω) fuel body st_Q with
          | none => simp [hbody] at hex
          | some res₁ =>
            rcases res₁ with ⟨o₁, st₁, c₁⟩
            cases o₁ with
            | returned u =>
              simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hex
              rcases hex with ⟨rfl, rfl, rfl⟩
              rcases ih body st_Q st_H k (.returned u) st₁ c₁
                hs_reg.2 hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hbody with
                ⟨st_H', c_H1, k', hr1, hc1, hu_lt, hb', hW', hregs', hqr', hqm', hmm', houts',
                  hqpos', hHpos'⟩
              have hc_eq : (relocExpr R e).size + c_H1 + 1 ≤ (R + 6) * (e.size + c₁ + 1) := by
                have h1 := relocExpr_size_le R e
                have h2 : (R + 6) * (e.size + c₁ + 1) =
                    (R + 6) * e.size + (R + 6) * c₁ + (R + 6) := by ring
                have h3 : (R + 6) * c₁ ≥ c₁ := Nat.le_mul_of_pos_left c₁ (by omega)
                have h4 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
                omega
              refine ⟨st_H', (relocExpr R e).size + c_H1 + 1, k',
                runs_loop_iff.mpr (Or.inr (Or.inl ⟨v, u, c_H1, he_H, hv, hr1, rfl, rfl⟩)),
                hc_eq, hu_lt, hb', hW', hregs', hqr', hqm', hmm', houts', hqpos', hHpos'⟩
            | normal =>
              simp only [hbody] at hex
              cases hloop : exec w' Q (subBits w w' pos₀ ω) fuel (.loop e body) st₁ with
              | none => simp [hloop] at hex
              | some res₂ =>
                rcases res₂ with ⟨o₂, st₂, c₂⟩
                simp only [hloop, Option.some.injEq, Prod.mk.injEq] at hex
                rcases hex with ⟨rfl, rfl, rfl⟩
                rcases ih body st_Q st_H k .normal st₁ c₁
                  hs_reg.2 hbase hW hregs hq_regs hq_mem hmem hq_pos hH_pos hbody with
                  ⟨st_H1, c_H1, k₁, hr1, hc1, _, hb1, hW1, hregs1, hqr1, hqm1, hmm1, houts1,
                    hqpos1, hHpos1⟩
                rcases ih (.loop e body) st₁ st_H1 k₁ o₂ st₂ c₂
                  hs_reg' hb1 hW1 hregs1 hqr1 hqm1 hmm1 hqpos1 hHpos1 hloop with
                  ⟨st_H', c_H2, k', hr2, hc2, ho', hb', hW', hregs', hqr', hqm', hmm', houts',
                    hqpos', hHpos'⟩
                have hc_eq : (relocExpr R e).size + c_H1 + c_H2 + 1 ≤
                    (R + 6) * (e.size + c₁ + c₂ + 1) := by
                  have h1 := relocExpr_size_le R e
                  have h2 : (R + 6) * (e.size + c₁ + c₂ + 1) =
                      (R + 6) * e.size + (R + 6) * c₁ + (R + 6) * c₂ + (R + 6) := by ring
                  have h3 : (R + 6) * c₁ ≥ c₁ := Nat.le_mul_of_pos_left c₁ (by omega)
                  have h4 : (R + 6) * c₂ ≥ c₂ := Nat.le_mul_of_pos_left c₂ (by omega)
                  have h5 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
                  omega
                refine ⟨st_H', (relocExpr R e).size + c_H1 + c_H2 + 1, k',
                  runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st_H1, c_H1, c_H2, he_H, hv, hr1, hr2, rfl⟩)),
                  hc_eq, ho', hb', hW', hregs', hqr', hqm', hmm', ?_, hqpos', hHpos'⟩
                intro addr haddr
                rw [houts' addr haddr, houts1 addr haddr]
    | call r f args =>
      simp only [exec] at hex
      cases hargs : evalArgs w' st_Q args with
      | none => simp [hargs] at hex
      | some vs =>
        cases hproc : Q.procs[f]? with
        | none => simp [hargs, hproc] at hex
        | some body =>
          simp only [hargs, hproc] at hex
          cases hbody : exec w' Q (subBits w w' pos₀ ω) fuel body
              { st_Q with regs := fun i => vs.getD i 0 } with
          | none => simp only [hbody] at hex; cases hex
          | some res =>
            rcases res with ⟨o₁, st₁, c₁⟩
            simp only [hbody, Option.some.injEq, Prod.mk.injEq] at hex
            rcases hex with ⟨rfl, rfl, rfl⟩
            simp only [Stmt.regBound, max_le_iff] at hs_reg
            rcases hs_reg with ⟨hr_R, hargs_len, hargs_rb⟩
            rcases evalArgs_reloc hw_le hh hargs_rb hregs hbase hq_regs hq_mem hmem hargs with
              ⟨hargs_H, hvs_len, hvs_lt⟩
            have hf_lt : f < Q.procs.length := by
              rw [List.getElem?_eq_some_iff] at hproc
              exact hproc.1
            have hbody_mem : body ∈ Q.procs := by
              rw [List.getElem?_eq_some_iff] at hproc
              rcases hproc with ⟨hf_lt', rfl⟩
              exact List.getElem_mem hf_lt'
            have hbody_rb : body.regBound ≤ R := regBound_le_of_mem hbody_mem
            have hproc_H : p.procs[b + 1 + f]? = some (relocStmt R b body) :=
              hp f body hproc
            let pad : List Expr := List.replicate (R - args.length) (.const 0)
            let extra : List Expr := [.reg R, .reg (R + 1)]
            let fullArgs : List Expr := args.map (relocExpr R) ++ pad ++ extra
            have hpad_eval : evalArgs w st_H pad = some (List.replicate (R - args.length) 0) :=
              evalArgs_replicate_zero (w := w)
            have hextra_eval : evalArgs w st_H extra = some [h + 1, 2 ^ w'] := by
              simp [extra, evalArgs, Expr.eval, hbase, hW]
            have hfull_eval : evalArgs w st_H fullArgs =
                some (vs ++ List.replicate (R - args.length) 0 ++ [h + 1, 2 ^ w']) :=
              evalArgs_append (evalArgs_append hargs_H hpad_eval) hextra_eval
            set vs_H := vs ++ List.replicate (R - args.length) 0 ++ [h + 1, 2 ^ w']
            set st_Q_call : State := { st_Q with regs := fun i => vs.getD i 0 }
            set st_H_call : State := startState vs_H st_H.mem st_H.pos
            have hbase_call : st_H_call.regs R = h + 1 := by
              have hlen1 : (vs ++ List.replicate (R - args.length) 0).length = R := by
                simp [hvs_len]; omega
              simp only [st_H_call, startState, vs_H, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (le_of_eq hlen1), hlen1, Nat.sub_self]
              simp
            have hW_call : st_H_call.regs (R + 1) = 2 ^ w' := by
              have hlen1 : (vs ++ List.replicate (R - args.length) 0).length = R := by
                simp [hvs_len]; omega
              simp only [st_H_call, startState, vs_H, List.getD_eq_getElem?_getD]
              rw [List.getElem?_append_right (by rw [hlen1]; omega), hlen1,
                show R + 1 - R = 1 by omega]
              simp
            have hregs_call : ∀ i < R, st_H_call.regs i = st_Q_call.regs i := by
              intro i hi
              simp only [st_H_call, startState, st_Q_call, vs_H, List.getD_eq_getElem?_getD]
              by_cases hivs : i < vs.length
              · have hi' : i < (vs ++ List.replicate (R - args.length) 0).length := by
                  simp [hvs_len]; omega
                rw [List.getElem?_append_left hi', List.getElem?_append_left hivs]
              · have hi_ge : vs.length ≤ i := Nat.le_of_not_lt hivs
                have hi' : i < (vs ++ List.replicate (R - args.length) 0).length := by
                  simp [hvs_len]; omega
                rw [List.getElem?_append_left hi', List.getElem?_append_right hi_ge]
                have hnone : vs[i]? = none := List.getElem?_eq_none (by omega)
                have hzero : (List.replicate (R - args.length) 0)[i - vs.length]? = some 0 := by
                  rw [List.getElem?_replicate]
                  simp [show i - vs.length < R - args.length by omega]
                simp [hnone, hzero]
            have hq_regs_call : ∀ i, st_Q_call.regs i < 2 ^ w' := by
              intro i
              simp only [st_Q_call, List.getD_eq_getElem?_getD]
              cases hget : vs[i]? with
              | none => simp [hw'_pos]
              | some v =>
                exact hvs_lt v (List.mem_of_getElem? hget)
            rcases ih body st_Q_call st_H_call k o₁ st₁ c₁
              hbody_rb hbase_call hW_call hregs_call hq_regs_call hq_mem hmem hq_pos hH_pos hbody with
              ⟨st_H1, c_H1, k', hr_body, hc_body, ho1_lt, _, _, _, hqr1, hqm1, hmm1, houts1,
                hqpos1, hHpos1⟩
            set st_H' : State := { st_H1 with regs := Function.update st_H.regs r o₁.value }
            have hr_R' : r < R := by omega
            have hargs_bound : argsSize fullArgs ≤ 3 * argsSize args + R + 2 := by
              have h1 := argsSize_reloc_le R args
              have h2 : argsSize pad = R - args.length := argsSize_replicate_const _ _
              have h3 : argsSize extra = 2 := by simp [extra, argsSize, Expr.size]
              simp only [fullArgs, argsSize_append, h2, h3]
              omega
            have hc_eq : argsSize fullArgs + c_H1 + 1 ≤ (R + 6) * (argsSize args + c₁ + 1) := by
              have hmul : (R + 6) * (argsSize args + c₁ + 1) =
                  (R + 6) * argsSize args + (R + 6) * c₁ + (R + 6) := by ring
              have h1 : 3 * argsSize args ≤ (R + 6) * argsSize args :=
                Nat.mul_le_mul_right (argsSize args) (by omega)
              have h2 : c₁ ≤ (R + 6) * c₁ := Nat.le_mul_of_pos_left c₁ (by omega)
              omega
            refine ⟨st_H', argsSize fullArgs + c_H1 + 1, k',
              runs_call_iff.mpr ⟨vs_H, relocStmt R b body, o₁, st_H1, c_H1,
                hfull_eval, hproc_H, hr_body, rfl, rfl, rfl⟩,
              hc_eq, hw'_pos, ?_, ?_, ?_, ?_, hqm1, hmm1, houts1, hqpos1, hHpos1⟩
            · simp [st_H', hbase, show R ≠ r by omega]
            · simp [st_H', hW, show R + 1 ≠ r by omega]
            · intro i hi
              by_cases hir : i = r
              · subst hir; simp [st_H', Outcome.value]; rfl
              · simp [st_H', hir, hregs i hi]
            · intro i
              by_cases hir : i = r
              · subst hir; simp only [Function.update_self]; exact ho1_lt
              · simp only [Function.update_of_ne hir]; exact hq_regs i
    | ret e =>
      simp only [exec] at hex
      cases he : e.eval w' st_Q with
      | none => simp [he] at hex
      | some v =>
        simp only [he, Option.some.injEq, Prod.mk.injEq] at hex
        rcases hex with ⟨rfl, rfl, rfl⟩
        have he_rb : e.regBound ≤ R := by simpa [Stmt.regBound] using hs_reg
        rcases eval_relocExpr hw_le hh he_rb hregs hbase hq_regs hq_mem hmem he with
          ⟨he_H, hv_lt⟩
        have hc_eq : (relocExpr R e).size + 1 ≤ (R + 6) * (e.size + 1) := by
          have h1 := relocExpr_size_le R e
          have h2 : 3 * e.size ≤ (R + 6) * e.size := Nat.mul_le_mul_right e.size (by omega)
          have hmul : (R + 6) * (e.size + 1) = (R + 6) * e.size + (R + 6) := by ring
          omega
        refine ⟨st_H, (relocExpr R e).size + 1, k,
          runs_ret_iff.mpr ⟨v, he_H, rfl, rfl, rfl⟩,
          hc_eq, hv_lt, hbase, hW, hregs, hq_regs, hq_mem, hmem, fun _ _ => rfl, hq_pos, hH_pos⟩

end Link

/-- **Main specification of `runner Q c`** (`runner_spec`).
If `p.HasAt b (runner Q c b)`, `x` is stored at `[a, a + len)` with `a + len ≤ h`, `ZeroFrom mem h`,
`h + 2 ^ (w' + 1) + 2 ≤ 2 ^ w` where `w' = wordSize c x`, and `RunsTo w' Q x (subBits w w' pos ω) out cost`,
then procedure `b` of `p` runs from `startState [a, len, h] mem pos` and terminates with:
- return value `h + 1 + 2 ^ w'`,
- `mem' h = out.length` and `ListAt mem' (h + 1) out`,
- memory below `h` unchanged,
- `ZeroFrom mem' (h + 1 + 2 ^ w')`, and
- cost at most `runnerScale Q * (cost + len + w' + 1)`. -/
public theorem runner_spec {w : ℕ} {p : Program} {Q : Program} {c b a len h pos : ℕ}
    {mem : ℕ → ℕ} {x out : List ℕ} {cost : ℕ} {ω : ℕ → Bool}
    (hp : p.HasAt b (runner Q c b))
    (hpos : a + len ≤ h)
    (hlen : len = x.length)
    (hlist : ListAt mem a x)
    (hzero : ZeroFrom mem h)
    (hw : h + 2 ^ (wordSize c x + 1) + 2 ≤ 2 ^ w)
    (hrun : RunsTo (wordSize c x) Q x (subBits w (wordSize c x) pos ω) out cost) :
    ∃ body o st' c_H,
      p.procs[b]? = some body ∧
      Runs w p ω body (startState [a, len, h] mem pos) o st' c_H ∧
      o.value = h + 1 + 2 ^ wordSize c x ∧
      st'.mem h = out.length ∧
      ListAt st'.mem (h + 1) out ∧
      (∀ j < h, st'.mem j = mem j) ∧
      ZeroFrom st'.mem (h + 1 + 2 ^ wordSize c x) ∧
      c_H ≤ runnerScale Q * (cost + len + wordSize c x + 1) := by
  set w' := wordSize c x
  have h4 : 4 ≤ 2 ^ w := by
    have : 2 ≤ 2 ^ (w' + 1) := by
      have : 1 ≤ 2 ^ w' := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    omega
  have hlt1 : 1 < 2 ^ w := by omega
  have hhw' : h + 1 + 2 ^ w' ≤ 2 ^ w := by
    have : 1 + 2 ^ w' ≤ 2 ^ (w' + 1) := by
      have : 1 ≤ 2 ^ w' := Nat.one_le_two_pow
      rw [Nat.pow_succ]; omega
    omega
  have hw_le : w' ≤ w := by
    have : 2 ^ w' < 2 ^ w := by omega
    exact le_of_lt (Link.two_pow_lt_two_pow_of_lt this)
  have h2w' : 2 ^ (w' + 1) + 2 ≤ 2 ^ w := by omega
  -- Unpack RunsTo w' Q
  rcases hrun with ⟨fuel, hrun_eq⟩
  simp only [run] at hrun_eq
  cases hex_top : exec w' Q (subBits w w' pos ω) fuel (.call 0 0 [.const x.length])
      { mem := initMem x, regs := fun _ => 0, pos := 0 } with
  | none => simp [hex_top] at hrun_eq
  | some res_top =>
    rcases res_top with ⟨o_top, st_top, c_top⟩
    simp only [hex_top, Option.some.injEq, Prod.mk.injEq] at hrun_eq
    rcases hrun_eq with ⟨hout_eq, hcost_eq⟩
    have hruns_top : Runs w' Q (subBits w w' pos ω) (.call 0 0 [.const x.length])
        { mem := initMem x, regs := fun _ => 0, pos := 0 } o_top st_top c_top :=
      ⟨fuel, hex_top⟩
    rw [runs_call_iff] at hruns_top
    rcases hruns_top with ⟨vs_top, body0, o0, st0, c0, hargs_top, hproc0, hrun0, _, rfl, rfl⟩
    simp only [Function.update_self] at hout_eq
    simp only [evalArgs, Expr.eval] at hargs_top
    have hlen_lt_w' : x.length < 2 ^ w' := by
      by_contra hnot
      simp [hnot] at hargs_top
    simp only [hlen_lt_w', ↓reduceIte, Option.some.injEq] at hargs_top
    subst hargs_top
    have hx_mem_lt : ∀ v ∈ x, v < 2 ^ w' := by
      intro v hv
      cases c with
      | zero =>
        simp only [w', wordSize, Nat.zero_mul, pow_zero] at hlen_lt_w'
        have hxnil : x = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hxnil; cases hv
      | succ c' =>
        exact Link.mem_lt_two_pow_wordSize (Nat.succ_pos c') hv
    have hq_mem0 : ∀ addr, initMem x addr < 2 ^ w' := by
      intro addr
      simp only [initMem, List.getD_eq_getElem?_getD]
      cases hget : x[addr]? with
      | none => simp
      | some v => exact hx_mem_lt v (List.mem_of_getElem? hget)
    have hq_regs0 : ∀ r, (startState [x.length] (initMem x) 0).regs r < 2 ^ w' := by
      intro r
      rcases r with _ | r
      · simpa [startState] using hlen_lt_w'
      · simp [startState]
    have hal : a + x.length < 2 ^ w := by omega
    have hbody0_mem : body0 ∈ Q.procs := by
      rw [List.getElem?_eq_some_iff] at hproc0
      rcases hproc0 with ⟨h0_lt, rfl⟩
      exact List.getElem_mem h0_lt
    have hproc0_len : 0 < Q.procs.length := by
      rw [List.getElem?_eq_some_iff] at hproc0; exact hproc0.1
    have hproc_entry : p.procs[b]? = some (runnerEntry Q c b) := by
      simpa [runner] using hp 0 (by simp [runner])
    have hproc_b1 : p.procs[b + 1]? = some (relocStmt Q.regBound b body0) := by
      have hhas := hp 1 (by simp [runner]; exact hproc0_len)
      rw [List.getElem?_eq_some_iff] at hproc0
      rcases hproc0 with ⟨_, rfl⟩
      simpa [runner] using hhas
    set st_start := startState [a, len, h] mem pos
    have hnodup_cw : ([0, 1, 3, 4, 5, 6, 7] : List ℕ).Nodup := by decide
    have hcw := Link.computeWordSize_runs (p := p) (ω := ω) hnodup_cw
      (show st_start.regs 0 = a by simp [st_start, startState])
      (show st_start.regs 1 = x.length by simp [st_start, startState, hlen])
      (show ListAt st_start.mem a x by simpa [st_start, startState] using hlist)
      hal h2w'
    rcases hcw with ⟨st1, c_cw, hcw_r, hst1_w', hst1_W, hst1_m, hst1_p, hst1_regs, hc_cw⟩
    have hst1_a : st1.regs 0 = a := by
      rw [hst1_regs 0 (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [st_start, startState]
    have hst1_len : st1.regs 1 = x.length := by
      rw [hst1_regs 1 (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [st_start, startState, hlen]
    have hst1_h : st1.regs 2 = h := by
      rw [hst1_regs 2 (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp [st_start, startState]
    -- setBase: assign 6 (.bin .add (.reg 2) (.const 1))
    have hh1_lt : h + 1 < 2 ^ w := by omega
    have he_base : (Expr.bin .add (.reg 2) (.const 1)).eval w st1 = some (h + 1) := by
      simp [Expr.eval, BinOp.eval, hst1_h, hlt1, hh1_lt]
    set st2 : State := { st1 with regs := Function.update st1.regs 6 (h + 1) }
    have hsetBase : Runs w p ω (.assign 6 (.bin .add (.reg 2) (.const 1))) st1 .normal st2 4 := by
      rw [runs_assign_iff]
      exact ⟨h + 1, he_base, rfl, rfl, by simp [Expr.size]⟩
    -- copyWordsStmt 0 6 1 5
    have hnodup_cp : ([0, 6, 1, 5] : List ℕ).Nodup := by decide
    have hdst_lt : (h + 1) + x.length < 2 ^ w := by omega
    have hcp := Link.copyWords_runs (p := p) (ω := ω) hnodup_cp
      (show st2.regs 0 = a by simp [st2, hst1_a])
      (show st2.regs 6 = h + 1 by simp [st2])
      (show st2.regs 1 = x.length by simp [st2, hst1_len])
      (show ListAt st2.mem a x by rw [show st2.mem = mem from hst1_m]; exact hlist)
      (show a + x.length ≤ h + 1 by omega)
      hdst_lt h4
    rcases hcp with ⟨st3, c_cp, hcp_r, hst3_list, hst3_outs, hst3_pos, hst3_regs, hc_cp⟩
    -- Call relocated proc 0
    set R := Q.regBound
    have h1R : 1 ≤ R := Link.one_le_regBound Q
    set callArgs : List Expr :=
      [.reg 1] ++ List.replicate (R - 1) (.const 0) ++ [.reg 6, .reg 4]
    have hst3_1 : st3.regs 1 = x.length := by rw [hst3_regs 1 (by omega)]; simp [st2, hst1_len]
    have hst3_2 : st3.regs 2 = h := by rw [hst3_regs 2 (by omega)]; simp [st2, hst1_h]
    have hst3_4 : st3.regs 4 = 2 ^ w' := by rw [hst3_regs 4 (by omega)]; simp [st2, hst1_W, w']
    have hst3_6 : st3.regs 6 = h + 1 := by rw [hst3_regs 6 (by omega)]; simp [st2]
    have hcall_eval : evalArgs w st3 callArgs =
        some ([x.length] ++ List.replicate (R - 1) 0 ++ [h + 1, 2 ^ w']) := by
      have ha1 : evalArgs w st3 [.reg 1] = some [x.length] := by simp [evalArgs, Expr.eval, hst3_1]
      have ha2 : evalArgs w st3 (List.replicate (R - 1) (.const 0)) =
          some (List.replicate (R - 1) 0) := Link.evalArgs_replicate_zero
      have ha3 : evalArgs w st3 [.reg 6, .reg 4] = some [h + 1, 2 ^ w'] := by
        simp [evalArgs, Expr.eval, hst3_6, hst3_4]
      exact Link.evalArgs_append (Link.evalArgs_append ha1 ha2) ha3
    set vs_call := [x.length] ++ List.replicate (R - 1) 0 ++ [h + 1, 2 ^ w']
    set st_H_call : State := startState vs_call st3.mem st3.pos
    have hbase_call : st_H_call.regs R = h + 1 := by
      have hlen1 : ([x.length] ++ List.replicate (R - 1) 0).length = R := by simp; omega
      simp only [st_H_call, startState, vs_call, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (le_of_eq hlen1), hlen1, Nat.sub_self]
      simp
    have hW_call : st_H_call.regs (R + 1) = 2 ^ w' := by
      have hlen1 : ([x.length] ++ List.replicate (R - 1) 0).length = R := by simp; omega
      simp only [st_H_call, startState, vs_call, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hlen1, show R + 1 - R = 1 by omega]
      simp
    have hregs_call : ∀ r < R, st_H_call.regs r = (startState [x.length] (initMem x) 0).regs r := by
      intro r hr
      simp only [st_H_call, startState, vs_call, List.getD_eq_getElem?_getD]
      have hlen1 : ([x.length] ++ List.replicate (R - 1) 0).length = R := by simp; omega
      rw [List.getElem?_append_left (by omega)]
      cases r with
      | zero => simp
      | succ r' =>
        have hr' : r' < R - 1 := by omega
        simp [hr']
    have hmem_call : ∀ addr < 2 ^ w', st_H_call.mem (h + 1 + addr) = initMem x addr := by
      intro addr _
      simp only [st_H_call, startState, initMem, List.getD_eq_getElem?_getD]
      by_cases had : addr < x.length
      · rw [hst3_list addr had, List.getElem?_eq_getElem had]; rfl
      · have haddr_ge : x.length ≤ addr := Nat.le_of_not_lt had
        rw [hst3_outs (h + 1 + addr) (Or.inr (by omega))]
        rw [hst1_m]
        have hststart_mem_eq : st_start.mem = mem := rfl
        rw [hststart_mem_eq, hzero (h + 1 + addr) (by omega), List.getElem?_eq_none haddr_ge]
        rfl
    rcases hrun0 with ⟨fuel0, hex0⟩
    have hp_reloc : ∀ f body, Q.procs[f]? = some body →
        p.procs[b + 1 + f]? = some (relocStmt Q.regBound b body) := by
      intro f body hfq
      rw [List.getElem?_eq_some_iff] at hfq
      rcases hfq with ⟨hf, rfl⟩
      have hhas := hp (f + 1) (by simp [runner]; exact hf)
      simpa [runner, show b + (f + 1) = b + 1 + f by omega] using hhas
    have hreloc := Link.runs_relocStmt hp_reloc hw_le hhw' h4 fuel0 body0
      (startState [x.length] (initMem x) 0) st_H_call 0 o0 st0 c0
      (Link.regBound_le_of_mem hbody0_mem)
      hbase_call hW_call hregs_call hq_regs0 hq_mem0 hmem_call
      (by simp [startState])
      (by simp [st_H_call, startState, hst3_pos, st2, hst1_p, st_start]) hex0
    rcases hreloc with ⟨st_H1, c_H1, k', hr_body, hc_H1, ho0_lt, _, _, _, _, _, hmem1, houts1,
      _, _⟩
    set st4 : State := { st_H1 with regs := Function.update st3.regs 7 o0.value }
    have hcall_r : Runs w p ω (.call 7 (b + 1) callArgs) st3 .normal st4
        (argsSize callArgs + c_H1 + 1) :=
      runs_call_iff.mpr ⟨vs_call, relocStmt R b body0, o0, st_H1, c_H1,
        hcall_eval, hproc_b1, hr_body, rfl, rfl, rfl⟩
    -- Store length at h, and ret h + 1 + 2^w'
    have hlen_out_eq : out.length = o0.value := by
      rw [← hout_eq]
      simp
    have ho0_lt_w : o0.value < 2 ^ w := by
      have : 2 ^ w' ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw_le
      omega
    have hh_lt : h < 2 ^ w := by omega
    have hstore_r : Runs w p ω (.store (.reg 2) (.reg 7)) st4 .normal
        { st4 with mem := Function.update st4.mem h o0.value } 3 := by
      rw [runs_store_iff]
      refine ⟨h, o0.value, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
      · simp [Expr.eval, st4, hst3_2]
      · simp [Expr.eval, st4]
    set st5 : State := { st4 with mem := Function.update st4.mem h o0.value }
    have hret_r : Runs w p ω (.ret (.bin .add (.reg 6) (.reg 4))) st5
        (.returned (h + 1 + 2 ^ w')) st5 4 := by
      rw [runs_ret_iff]
      refine ⟨h + 1 + 2 ^ w', ?_, rfl, rfl, by simp [Expr.size]⟩
      have h5_6 : st5.regs 6 = h + 1 := by simp [st5, st4, hst3_6]
      have h5_4 : st5.regs 4 = 2 ^ w' := by simp [st5, st4, hst3_4]
      have hsum_lt : (h + 1) + 2 ^ w' < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, h5_6, h5_4, hsum_lt]
    -- Combine runnerEntry
    have hargs_sz : argsSize callArgs = R + 2 := by
      simp only [callArgs, Link.argsSize_append, Link.argsSize_replicate_const]
      simp [argsSize, Expr.size]; omega
    set c_rest := argsSize callArgs + c_H1 + 1 + (3 + 4 + 1) + 1
    have hseq_tail :=
      runs_seq_iff.mpr (Or.inr ⟨st4, argsSize callArgs + c_H1 + 1, 3 + 4 + 1, hcall_r,
        runs_seq_iff.mpr (Or.inr ⟨st5, 3, 4, hstore_r, hret_r, rfl⟩), rfl⟩)
    have hseq3 :=
      runs_seq_iff.mpr (Or.inr ⟨st3, c_cp, c_rest, hcp_r, hseq_tail, rfl⟩)
    have hseq2 :=
      runs_seq_iff.mpr (Or.inr ⟨st2, 4, c_cp + c_rest + 1, hsetBase, hseq3, rfl⟩)
    set c_tot := c_cw + (4 + (c_cp + c_rest + 1) + 1) + 1
    have hseq1 : Runs w p ω (runnerEntry Q c b) st_start (.returned (h + 1 + 2 ^ w')) st5 c_tot := by
      have htmp := runs_seq_iff.mpr (Or.inr ⟨st1, c_cw, 4 + (c_cp + c_rest + 1) + 1, hcw_r, hseq2, rfl⟩)
      simpa [runnerEntry, callArgs, R] using htmp
    refine ⟨runnerEntry Q c b, .returned (h + 1 + 2 ^ w'), st5, c_tot,
      hproc_entry, hseq1, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · simp [st5, hlen_out_eq]
    · intro i hi
      have hlen_o : i < o0.value := by rw [hlen_out_eq] at hi; exact hi
      have hne : h + 1 + i ≠ h := by omega
      simp only [st5, st4, Function.update_apply, hne, ↓reduceIte]
      rw [hmem1 i (by omega)]
      have hout_i : out[i] = st0.mem i := by
        calc out[i] = out.getD i 0 := by simp [List.getD_eq_getElem?_getD, hi]
        _ = ((List.range o0.value).map st0.mem).getD i 0 := by rw [← hout_eq]
        _ = st0.mem i := by simp [List.getD_eq_getElem?_getD, hlen_o]
      exact hout_i.symm
    · intro j hj
      have hne : j ≠ h := by omega
      have hlt_h1 : j < h + 1 := by omega
      simp only [st5, st4, Function.update_apply, hne, ↓reduceIte]
      rw [houts1 j (Or.inl hlt_h1), show st_H_call.mem = st3.mem from rfl,
        hst3_outs j (Or.inl hlt_h1), show st2.mem = st1.mem from rfl, hst1_m]
      rfl
    · intro addr ha
      have hne : addr ≠ h := by omega
      simp only [st5, st4, Function.update_apply, hne, ↓reduceIte]
      rw [houts1 addr (Or.inr ha), show st_H_call.mem = st3.mem from rfl,
        hst3_outs addr (Or.inr (by omega)), show st2.mem = st1.mem from rfl, hst1_m]
      exact hzero addr (by omega)
    · have hc_cost : c0 + 2 = cost := by
        rw [← hcost_eq]; simp [argsSize, Expr.size]; omega
      have : c_tot ≤ (R + 80) * (cost + len + w' + 1) := by
        have hcost_ge : 2 ≤ cost := by omega
        have hc0_eq : cost = c0 + 2 := hc_cost.symm
        have hc_H1' : c_H1 ≤ (R + 6) * c0 := hc_H1
        have hm1 : (R + 6) * c0 ≤ (R + 80) * c0 := Nat.mul_le_mul_right c0 (by omega)
        have hmul_sum : (R + 80) * (cost + len + w' + 1) =
            (R + 80) * c0 + 2 * (R + 80) + (R + 80) * len + (R + 80) * w' + (R + 80) := by
          rw [hc0_eq]; ring
        have hlen_m : 57 * len ≤ (R + 80) * len := Nat.mul_le_mul_right len (by omega)
        have hw'_m : 40 * w' ≤ (R + 80) * w' := Nat.mul_le_mul_right w' (by omega)
        omega
      exact this

end WordRAM
