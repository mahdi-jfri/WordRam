module

public import WordRAM.Contract
public import Mathlib.Logic.Function.DependsOn
public import Mathlib.MeasureTheory.Constructions.Cylinders
public import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Probability.Independence.InfinitePi

/-!
# Random bits and random words

Properties of `readWord`, `coins`, and `subBits` from `WordRAM/Model.lean` and
`WordRAM/Contract.lean`:

* Range, bit-extraction, truncation, and coordinate locality of `readWord`.
* Under `coins`, `readWord · pos w` is uniform on `{0, …, 2 ^ w - 1}`, and words read from
  disjoint bit ranges are independent.
* Measure preservation of `coins` under injective coordinate maps (`coins_map_of_injective`),
  shifts (`coins_map_shift`), and `subBits` (`coins_map_subBits`).
* Independence of sets depending on disjoint bit ranges, in particular bits `< q` and bits `≥ q`.
-/

public section

namespace WordRAM

open MeasureTheory ProbabilityTheory

section ReadWord

@[simp]
theorem readWord_zero (ω : ℕ → Bool) (pos : ℕ) : readWord ω pos 0 = 0 := rfl

theorem readWord_succ (ω : ℕ → Bool) (pos w : ℕ) :
    readWord ω pos (w + 1) = (if ω pos then 1 else 0) + 2 * readWord ω (pos + 1) w := rfl

/-- `readWord ω pos w` is strictly less than `2 ^ w`. -/
theorem readWord_lt (ω : ℕ → Bool) (pos w : ℕ) : readWord ω pos w < 2 ^ w := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih =>
    rw [readWord_succ, pow_succ']
    have := ih (pos + 1)
    cases ω pos <;> simp <;> omega

/-- `readWord ω pos w` depends only on the bits of `ω` in `[pos, pos + w)`. -/
theorem readWord_congr {ω ω' : ℕ → Bool} {pos w : ℕ}
    (h : ∀ i, pos ≤ i → i < pos + w → ω i = ω' i) :
    readWord ω pos w = readWord ω' pos w := by
  induction w generalizing pos with
  | zero => rfl
  | succ w ih =>
    rw [readWord_succ, readWord_succ, h pos le_rfl (by omega)]
    congr 2
    exact ih fun i hi₁ hi₂ => h i (by omega) (by omega)

/-- `readWord · pos w` depends only on the coordinate set `Set.Ico pos (pos + w)`. -/
theorem dependsOn_readWord (pos w : ℕ) :
    DependsOn (fun ω => readWord ω pos w) (Set.Ico pos (pos + w)) :=
  fun _ _ h => readWord_congr fun i hi₁ hi₂ => h i ⟨hi₁, hi₂⟩

/-- Reading `a + b` bits splits into the low `a` bits and `2 ^ a` times the next `b` bits. -/
theorem readWord_add (ω : ℕ → Bool) (pos a b : ℕ) :
    readWord ω pos (a + b) = readWord ω pos a + 2 ^ a * readWord ω (pos + a) b := by
  induction a generalizing pos with
  | zero => simp [readWord]
  | succ a ih =>
    rw [Nat.succ_add, readWord_succ, readWord_succ, ih (pos + 1), pow_succ']
    have hpos : pos + 1 + a = pos + (a + 1) := by omega
    rw [hpos]
    ring

/-- Truncating `readWord ω pos w` to `w' ≤ w` bits gives `readWord ω pos w'`. -/
theorem readWord_mod (ω : ℕ → Bool) (pos : ℕ) {w' w : ℕ} (hw : w' ≤ w) :
    readWord ω pos w % 2 ^ w' = readWord ω pos w' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hw
  rw [readWord_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (readWord_lt ω pos w')]

/-- Shifting the starting position by `q` corresponds to shifting the bit sequence `ω` by `q`. -/
theorem readWord_shift (ω : ℕ → Bool) (q pos w : ℕ) :
    readWord ω (q + pos) w = readWord (fun i => ω (q + i)) pos w := by
  induction w generalizing pos with
  | zero => rfl
  | succ w ih =>
    rw [readWord_succ, readWord_succ]
    have hpos : q + pos + 1 = q + (pos + 1) := by omega
    rw [hpos, ih (pos + 1)]

/-- Reading word `k` of `subBits w w' pos ω` at word size `w'` equals reading `w'` bits at
`pos + k * w` from `ω`. -/
theorem readWord_subBits (ω : ℕ → Bool) (w w' pos k : ℕ) :
    readWord (subBits w w' pos ω) (k * w') w' = readWord ω (pos + k * w) w' := by
  have haux : ∀ t m, m + t = w' →
      readWord (subBits w w' pos ω) (k * w' + m) t =
        readWord ω (pos + k * w + m) t := by
    intro t
    induction t with
    | zero => intro m _; rfl
    | succ t ih =>
      intro m hm
      have hm_lt : m < w' := by omega
      rw [readWord_succ, readWord_succ]
      have hbit : subBits w w' pos ω (k * w' + m) = ω (pos + k * w + m) := by
        simp only [subBits]
        have hdiv : (k * w' + m) / w' = k := by
          rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hm_lt, zero_add]
        have hmod : (k * w' + m) % w' = m := by
          rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hm_lt]
        rw [hdiv, hmod]
      rw [hbit]
      have hih := ih (m + 1) (by omega)
      have h1 : k * w' + m + 1 = k * w' + (m + 1) := by omega
      have h2 : pos + k * w + m + 1 = pos + k * w + (m + 1) := by omega
      rw [h1, h2, hih]
  simpa using haux w' 0 (Nat.zero_add w')

/-- Bit `i` of `readWord ω pos w` is `ω (pos + i)` when `i < w`, and `false` otherwise. -/
theorem readWord_testBit (ω : ℕ → Bool) (pos w i : ℕ) :
    (readWord ω pos w).testBit i = (decide (i < w) && ω (pos + i)) := by
  induction w generalizing pos i with
  | zero => simp [readWord]
  | succ w ih =>
    cases i with
    | zero =>
      rw [readWord_succ]
      cases ω pos <;> simp [Nat.testBit_zero]
    | succ i =>
      rw [readWord_succ, Nat.testBit_succ]
      have hdiv : ((if ω pos then 1 else 0) + 2 * readWord ω (pos + 1) w) / 2 =
          readWord ω (pos + 1) w := by
        rw [add_comm, Nat.mul_add_div (by decide)]
        cases ω pos <;> simp
      rw [hdiv, ih (pos + 1) i]
      have hadd : pos + (i + 1) = pos + 1 + i := by omega
      have hlt : decide (i + 1 < w + 1) = decide (i < w) := by simp
      rw [hadd, hlt]

/-- For `k < 2 ^ w`, `readWord ω pos w = k` iff the `w` bits starting at `pos` match the low `w`
bits of `k`. -/
theorem readWord_eq_iff_bits {ω : ℕ → Bool} {pos w k : ℕ} (hk : k < 2 ^ w) :
    readWord ω pos w = k ↔ ∀ i < w, ω (pos + i) = k.testBit i := by
  constructor
  · intro h i hi
    rw [← h, readWord_testBit]
    simp [hi]
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [readWord_testBit]
    by_cases hi : i < w
    · simp [hi, h i hi]
    · have hk_lt : k < 2 ^ i := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) (by omega))
      simp [hi, Nat.testBit_eq_false_of_lt hk_lt]

end ReadWord

section CoinsMeasure

/-- `coins` is a probability measure. -/
instance isProbabilityMeasure_coins : IsProbabilityMeasure coins := by
  unfold coins
  infer_instance

/-- Each individual bit under `coins` is uniformly distributed on `Bool`. -/
theorem coins_map_eval (i : ℕ) :
    coins.map (fun ω => ω i) = (PMF.uniformOfFintype Bool).toMeasure :=
  Measure.infinitePi_map_eval _ i

/-- Each individual bit equals `b` with probability `1 / 2`. -/
theorem coins_bit (i : ℕ) (b : Bool) :
    coins {ω | ω i = b} = (2 : ENNReal)⁻¹ := by
  have hev : {ω : ℕ → Bool | ω i = b} = (fun ω => ω i) ⁻¹' {b} := rfl
  rw [hev, ← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton b),
    coins_map_eval i, (PMF.uniformOfFintype Bool).toMeasure_apply_singleton b
      (measurableSet_singleton b), PMF.uniformOfFintype_apply]
  simp

/-- Pushing `coins` forward along `fun ω i => ω (g i)` for any injective `g` gives `coins`. -/
theorem coins_map_of_injective {g : ℕ → ℕ} (hg : Function.Injective g) :
    coins.map (fun ω i => ω (g i)) = coins := by
  unfold coins
  exact Measure.map_infinitePi_infinitePi_of_inj hg

/-- Shifting the bit sequence by `q` preserves `coins`. -/
theorem coins_map_shift (q : ℕ) :
    coins.map (fun ω i => ω (q + i)) = coins :=
  coins_map_of_injective fun _ _ h => Nat.add_left_cancel h

/-- `subBits w w' pos` preserves `coins` when `0 < w' ≤ w`. -/
theorem coins_map_subBits {w w' : ℕ} (pos : ℕ) (hw' : 0 < w') (hw : w' ≤ w) :
    coins.map (subBits w w' pos) = coins := by
  refine coins_map_of_injective fun i j hij => ?_
  have heq : i / w' * w + i % w' = j / w' * w + j % w' := by omega
  have him : i % w' < w := lt_of_lt_of_le (Nat.mod_lt i hw') hw
  have hjm : j % w' < w := lt_of_lt_of_le (Nat.mod_lt j hw') hw
  have hdiv : i / w' = j / w' := by
    have := congrArg (· / w) heq
    rwa [add_comm (i / w' * w), Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt him,
      zero_add, add_comm (j / w' * w), Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt hjm, zero_add] at this
  have hmod : i % w' = j % w' := by
    have := congrArg (· % w) heq
    rwa [add_comm (i / w' * w), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt him,
      add_comm (j / w' * w), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjm] at this
  have hi := Nat.div_add_mod i w'
  have hj := Nat.div_add_mod j w'
  rw [← hi, ← hj, hdiv, hmod]

/-- Pulling back any set (even non-measurable) along a measure-preserving map does not increase
its `coins` measure. -/
theorem coins_preimage_le_of_map_eq {f : (ℕ → Bool) → ℕ → Bool} (hf : Measurable f)
    (hmap : coins.map f = coins) (s : Set (ℕ → Bool)) :
    coins (f ⁻¹' s) ≤ coins s := by
  obtain ⟨t, hst, htm, hteq⟩ := exists_measurable_superset coins s
  calc
    coins (f ⁻¹' s) ≤ coins (f ⁻¹' t) := measure_mono (Set.preimage_mono hst)
    _ = (coins.map f) t := (Measure.map_apply hf htm).symm
    _ = coins t := by rw [hmap]
    _ = coins s := hteq

/-- Shifting by `q` does not increase the `coins` measure of a preimage. -/
theorem coins_shift_preimage_le (q : ℕ) (s : Set (ℕ → Bool)) :
    coins {ω | (fun i => ω (q + i)) ∈ s} ≤ coins s :=
  coins_preimage_le_of_map_eq (measurable_pi_iff.mpr fun i => measurable_pi_apply (q + i))
    (coins_map_shift q) s

/-- Pulling back a measurable set along the shift by `q` preserves its `coins` measure. -/
theorem coins_shift_preimage_eq (q : ℕ) {s : Set (ℕ → Bool)} (hs : MeasurableSet s) :
    coins {ω | (fun i => ω (q + i)) ∈ s} = coins s := by
  have hm : Measurable (fun (ω : ℕ → Bool) i => ω (q + i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (q + i)
  change coins ((fun ω i => ω (q + i)) ⁻¹' s) = coins s
  rw [← Measure.map_apply hm hs, coins_map_shift]

end CoinsMeasure

section LocalityAndMeasurability

/-- `readWord · pos w` is measurable with respect to `cylinderEvents (Set.Ico pos (pos + w))`. -/
theorem measurable_readWord_cylinderEvents (pos w : ℕ) :
    Measurable[cylinderEvents (Set.Ico pos (pos + w))] (fun ω => readWord ω pos w) := by
  induction w generalizing pos with
  | zero => simp [readWord]
  | succ w ih =>
    have hmem : pos ∈ Set.Ico pos (pos + (w + 1)) := Set.mem_Ico.mpr ⟨le_rfl, by omega⟩
    have hbit : Measurable[cylinderEvents (Set.Ico pos (pos + (w + 1)))]
        (fun ω : ℕ → Bool => if ω pos then 1 else 0) :=
      Measurable.ite (measurableSet_eq_fun (measurable_cylinderEvent_apply hmem)
        measurable_const) measurable_const measurable_const
    have hsub : Set.Ico (pos + 1) (pos + 1 + w) ⊆ Set.Ico pos (pos + (w + 1)) := by
      intro i hi
      rw [Set.mem_Ico] at hi ⊢
      omega
    have hrest : Measurable[cylinderEvents (Set.Ico pos (pos + (w + 1)))]
        (fun ω => readWord ω (pos + 1) w) :=
      (ih (pos + 1)).mono (cylinderEvents_mono hsub) le_rfl
    simp only [readWord_succ]
    exact hbit.add (hrest.const_mul 2)

/-- `readWord · pos w` is measurable on `ℕ → Bool`. -/
@[fun_prop]
theorem measurable_readWord (pos w : ℕ) : Measurable (fun ω => readWord ω pos w) :=
  (measurable_readWord_cylinderEvents pos w).mono cylinderEvents_le_pi le_rfl

/-- Any set depending only on a finite coordinate set `S` is `cylinderEvents S`-measurable. -/
theorem measurableSet_cylinderEvents_of_finite {S : Set ℕ} (hS : S.Finite)
    {A : Set (ℕ → Bool)} (hA : DependsOn A S) :
    MeasurableSet[cylinderEvents S] A := by
  let _ : Fintype S := hS.fintype
  let T : Set (∀ i : S, Bool) := S.domRestrict '' A
  have hpre : A = S.domRestrict ⁻¹' T := by
    ext ω
    constructor
    · exact fun hω => ⟨ω, hω, rfl⟩
    · rintro ⟨ω', hω', heq⟩
      have heq' : ∀ i ∈ S, ω' i = ω i := fun i hi => congr_fun heq ⟨i, hi⟩
      exact (hA heq').mp hω'
  rw [hpre]
  exact MeasurableSet.of_discrete.preimage (measurable_restrict_cylinderEvents S)

/-- Any set depending only on a finite coordinate set `S` is measurable. -/
theorem measurableSet_of_dependsOn_finite {S : Set ℕ} (hS : S.Finite)
    {A : Set (ℕ → Bool)} (hA : DependsOn A S) :
    MeasurableSet A :=
  cylinderEvents_le_pi _ (measurableSet_cylinderEvents_of_finite hS hA)

/-- Any measurable set depending only on coordinates in `S` is `cylinderEvents S`-measurable. -/
theorem measurableSet_cylinderEvents_of_dependsOn {S : Set ℕ}
    {A : Set (ℕ → Bool)} (hm : MeasurableSet A) (hA : DependsOn A S) :
    MeasurableSet[cylinderEvents S] A := by
  classical
  let proj : (ℕ → Bool) → ℕ → Bool := fun ω i => if i ∈ S then ω i else false
  have hproj_meas : @Measurable _ _ (cylinderEvents S) inferInstance proj := by
    rw [@measurable_pi_iff _ _ _ (cylinderEvents S)]
    intro i
    by_cases hi : i ∈ S
    · simp only [proj, hi, ↓reduceIte]; exact measurable_cylinderEvent_apply hi
    · simp only [proj, hi, ↓reduceIte]; exact measurable_const
  have hpre : A = proj ⁻¹' A := by
    ext ω
    have heq : ∀ i ∈ S, ω i = proj ω i := fun i hi => by simp [proj, hi]
    exact (hA heq).to_iff
  rw [hpre]
  exact hm.preimage hproj_meas

/-- The cylinder fixing the first `q` bits to `b` has `coins` measure `2⁻¹ ^ q`. -/
theorem coins_prefix_cylinder (q : ℕ) (b : Fin q → Bool) :
    coins {ω | ∀ i : Fin q, ω i.1 = b i} = (2⁻¹ : ENNReal) ^ q := by
  have hset : {ω : ℕ → Bool | ∀ i : Fin q, ω i.1 = b i} =
      (Finset.range q : Set ℕ).pi (fun i => if h : i < q then {b ⟨i, h⟩} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
    constructor
    · intro h i hi
      simpa [hi] using h ⟨i, hi⟩
    · intro h i
      simpa [i.isLt] using h i.1 i.isLt
  rw [hset]
  unfold coins
  rw [Measure.infinitePi_pi _ (fun _ _ => MeasurableSet.of_discrete)]
  calc
    ∏ i ∈ Finset.range q, (PMF.uniformOfFintype Bool).toMeasure
        (if h : i < q then {b ⟨i, h⟩} else Set.univ)
      = ∏ i ∈ Finset.range q, (2⁻¹ : ENNReal) := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          simp only [hi, ↓reduceDIte]
          rw [(PMF.uniformOfFintype Bool).toMeasure_apply_singleton _ (measurableSet_singleton _),
            PMF.uniformOfFintype_apply]
          simp
    _ = (2⁻¹ : ENNReal) ^ q := by simp

end LocalityAndMeasurability

section UniformReadWord

/-- Under `coins`, `readWord · pos w` takes each value `k < 2 ^ w` with probability `(2 ^ w)⁻¹`. -/
theorem coins_readWord_eq (pos w k : ℕ) (hk : k < 2 ^ w) :
    coins {ω | readWord ω pos w = k} = (2 ^ w : ENNReal)⁻¹ := by
  let s : Finset ℕ := (Finset.range w).image (pos + ·)
  let t : ℕ → Set Bool := fun j => {k.testBit (j - pos)}
  have hset : {ω : ℕ → Bool | readWord ω pos w = k} = Set.pi (s : Set ℕ) t := by
    ext ω
    rw [Set.mem_ofPred_eq, readWord_eq_iff_bits hk, Set.mem_pi]
    simp only [s, t, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    · intro h i hi
      simpa [Nat.add_sub_cancel_left] using h i hi
    · intro h i hi
      simpa [Nat.add_sub_cancel_left] using h i hi
  rw [hset]
  unfold coins
  rw [Measure.infinitePi_pi _ (fun _ _ => measurableSet_singleton _)]
  have hprod : ∀ j ∈ s,
      (PMF.uniformOfFintype Bool).toMeasure (t j) = (2⁻¹ : ENNReal) := by
    intro j _
    rw [(PMF.uniformOfFintype Bool).toMeasure_apply_singleton _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply]
    simp
  rw [Finset.prod_congr rfl hprod, Finset.prod_const]
  have hcard : s.card = w := by
    rw [Finset.card_image_of_injective _ (fun _ _ h => by omega), Finset.card_range]
  rw [hcard, ENNReal.inv_pow]

/-- `readWord · pos w` takes values `≥ 2 ^ w` with probability `0`. -/
theorem coins_readWord_eq_of_ge (pos w k : ℕ) (hk : 2 ^ w ≤ k) :
    coins {ω | readWord ω pos w = k} = 0 := by
  have hempty : {ω : ℕ → Bool | readWord ω pos w = k} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    exact absurd (h ▸ readWord_lt ω pos w) (not_lt.mpr hk)
  rw [hempty, measure_empty]

/-- For `k ≤ 2 ^ w`, `readWord · pos w < k` holds with probability `k / 2 ^ w`. -/
theorem coins_readWord_lt (pos w k : ℕ) (hk : k ≤ 2 ^ w) :
    coins {ω | readWord ω pos w < k} = (k : ENNReal) / (2 ^ w : ENNReal) := by
  have hset : {ω : ℕ → Bool | readWord ω pos w < k} =
      ⋃ j ∈ Finset.range k, {ω | readWord ω pos w = j} := by
    ext ω
    simp [Finset.mem_range]
  rw [hset, measure_biUnion_finset]
  · calc
      ∑ j ∈ Finset.range k, coins {ω | readWord ω pos w = j}
        = ∑ j ∈ Finset.range k, (2 ^ w : ENNReal)⁻¹ := by
            refine Finset.sum_congr rfl fun j hj => ?_
            exact coins_readWord_eq pos w j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
      _ = (k : ENNReal) * (2 ^ w : ENNReal)⁻¹ := by simp
      _ = (k : ENNReal) / (2 ^ w : ENNReal) := by rw [div_eq_mul_inv]
  · intro i _ j _ hij
    exact Set.disjoint_left.mpr fun ω hi hj => hij (hi.symm.trans hj)
  · intro j _
    exact (measurable_readWord pos w) (measurableSet_singleton j)

/-- The `Fin (2 ^ w)`-valued random word at `(pos, w)` has the uniform distribution on
`Fin (2 ^ w)`. -/
theorem coins_map_readWord_fin (pos w : ℕ) :
    coins.map (fun ω => (⟨readWord ω pos w, readWord_lt ω pos w⟩ : Fin (2 ^ w))) =
      (PMF.uniformOfFintype (Fin (2 ^ w))).toMeasure := by
  rw [Measure.ext_iff_singleton]
  intro k
  have hm : Measurable (fun ω => (⟨readWord ω pos w, readWord_lt ω pos w⟩ : Fin (2 ^ w))) := by
    intro s _
    have hpre : (fun ω => (⟨readWord ω pos w, readWord_lt ω pos w⟩ : Fin (2 ^ w))) ⁻¹' s =
        (fun ω => readWord ω pos w) ⁻¹' (Fin.val '' s) := by
      ext ω
      exact ⟨fun h => ⟨_, h, rfl⟩,
        fun ⟨x, hx, heq⟩ => by
          have : x = ⟨readWord ω pos w, readWord_lt ω pos w⟩ := Fin.ext heq
          rwa [Set.mem_preimage, ← this]⟩
    rw [hpre]
    exact (measurable_readWord pos w) MeasurableSet.of_discrete
  rw [Measure.map_apply hm (measurableSet_singleton k),
    (PMF.uniformOfFintype (Fin (2 ^ w))).toMeasure_apply_singleton k (measurableSet_singleton k),
    PMF.uniformOfFintype_apply, Fintype.card_fin]
  have hpre : (fun ω => (⟨readWord ω pos w, readWord_lt ω pos w⟩ : Fin (2 ^ w))) ⁻¹' {k} =
      {ω | readWord ω pos w = k.1} := by
    ext ω
    simp [Fin.ext_iff]
  rw [hpre, coins_readWord_eq pos w k.1 k.isLt]
  norm_cast

/-- Under `coins`, `readWord · pos w` is uniformly distributed on `Finset.range (2 ^ w)`. -/
theorem coins_map_readWord (pos w : ℕ) :
    coins.map (fun ω => readWord ω pos w) =
      (PMF.uniformOfFinset (Finset.range (2 ^ w))
        (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos w).ne')).toMeasure := by
  rw [Measure.ext_iff_singleton]
  intro k
  rw [Measure.map_apply (measurable_readWord pos w) (measurableSet_singleton k),
    (PMF.uniformOfFinset (Finset.range (2 ^ w))
      (Finset.nonempty_range_iff.mpr (Nat.two_pow_pos w).ne')).toMeasure_apply_singleton k
      (measurableSet_singleton k), PMF.uniformOfFinset_apply]
  by_cases hk : k < 2 ^ w
  · have hpre : (fun ω => readWord ω pos w) ⁻¹' {k} = {ω | readWord ω pos w = k} := rfl
    rw [hpre, coins_readWord_eq pos w k hk]
    simp [Finset.mem_range, hk]
  · have hpre : (fun ω => readWord ω pos w) ⁻¹' {k} = {ω | readWord ω pos w = k} := rfl
    rw [hpre, coins_readWord_eq_of_ge pos w k (not_lt.mp hk)]
    simp [Finset.mem_range, hk]

end UniformReadWord

section Independence

/-- Under `coins`, the σ-algebras generated by disjoint coordinate sets are independent. -/
theorem indep_cylinderEvents_of_disjoint {S T : Set ℕ} (hST : Disjoint S T) :
    Indep (cylinderEvents S) (cylinderEvents T) coins := by
  have hind : iIndep (fun (i : ℕ) => MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance)
      coins :=
    iIndepFun_infinitePi (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  have hle : ∀ i : ℕ, MeasurableSpace.comap (fun ω : ℕ → Bool => ω i) inferInstance ≤
      MeasurableSpace.pi :=
    fun i => (measurable_pi_apply i).comap_le
  simpa only [cylinderEvents] using indep_iSup_of_disjoint hle hind hST

/-- Under `coins`, a family of σ-algebras on pairwise disjoint coordinate sets is mutually
independent. -/
theorem iIndep_cylinderEvents_of_pairwise_disjoint {ι : Type*} {S : ι → Set ℕ}
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) :
    iIndep (fun i => cylinderEvents (X := fun _ => Bool) (S i)) coins := by
  rw [iIndep_iff]
  intro s f hf
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
    have hdisj : Disjoint (S k) (⋃ j ∈ s, S j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact hS (fun h => hks (h ▸ hj))
    have hmk : MeasurableSet[cylinderEvents (S k)] (f k) := hf k (Finset.mem_insert_self k s)
    have hms : MeasurableSet[cylinderEvents (⋃ j ∈ s, S j)] (⋂ j ∈ s, f j) := by
      refine MeasurableSet.biInter s.countable_toSet fun j hj => ?_
      exact cylinderEvents_mono (Set.subset_biUnion_of_mem hj) _
        (hf j (Finset.mem_insert_of_mem hj))
    have hind : Indep (cylinderEvents (S k)) (cylinderEvents (⋃ j ∈ s, S j)) coins :=
      indep_cylinderEvents_of_disjoint hdisj
    rw [Finset.set_biInter_insert, (hind.indepSet_of_measurableSet hmk hms).measure_inter_eq_mul,
      Finset.prod_insert hks, ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- Measurable sets depending on disjoint coordinate sets are independent under `coins`. -/
theorem indepSet_of_disjoint {S T : Set ℕ} (hST : Disjoint S T) {A B : Set (ℕ → Bool)}
    (hmA : MeasurableSet A) (hA : DependsOn A S)
    (hmB : MeasurableSet B) (hB : DependsOn B T) :
    IndepSet A B coins :=
  (indep_cylinderEvents_of_disjoint hST).indepSet_of_measurableSet
    (measurableSet_cylinderEvents_of_dependsOn hmA hA)
    (measurableSet_cylinderEvents_of_dependsOn hmB hB)

/-- Under `coins`, a set depending only on bits `< q` and a measurable set depending only on bits
`≥ q` are independent. -/
theorem indepSet_lt_ge (q : ℕ) {A B : Set (ℕ → Bool)}
    (hA : DependsOn A {i | i < q})
    (hmB : MeasurableSet B) (hB : DependsOn B {i | q ≤ i}) :
    IndepSet A B coins :=
  indepSet_of_disjoint (S := {i | i < q}) (T := {i | q ≤ i})
    (Set.disjoint_left.mpr fun _ hi₁ hi₂ => absurd (Set.mem_ofPred_eq.mp hi₁)
      (not_lt.mpr (Set.mem_ofPred_eq.mp hi₂)))
    (measurableSet_of_dependsOn_finite (Set.finite_lt_nat q) hA) hA hmB hB

private theorem coins_inter_le_mul_lt_ge (q : ℕ) {A B : Set (ℕ → Bool)}
    (hA : DependsOn A {i | i < q}) (hB : DependsOn B {i | q ≤ i}) :
    coins (A ∩ B) ≤ coins A * coins B := by
  let s : Finset ℕ := Finset.range q
  have hBsc : DependsOn B (s : Set ℕ)ᶜ := hB.mono fun i hi => by simpa [s] using hi
  obtain ⟨G, hBG, hmG, hGeq⟩ := exists_measurable_superset coins B
  let updatePrefix : (ℕ → Bool) → (Fin q → Bool) → ℕ → Bool :=
    fun ω b i => if h : i < q then b ⟨i, h⟩ else ω i
  let G' : Set (ℕ → Bool) := ⋂ b : Fin q → Bool, {ω | updatePrefix ω b ∈ G}
  have hm_upd : ∀ b : Fin q → Bool, Measurable (fun ω => updatePrefix ω b) := by
    intro b
    rw [measurable_pi_iff]
    intro i
    by_cases hi : i < q
    · simp [updatePrefix, hi]
    · simpa [updatePrefix, hi] using measurable_pi_apply i
  have hmG' : MeasurableSet G' :=
    MeasurableSet.iInter fun b => hmG.preimage (hm_upd b)
  have hG'dep : DependsOn G' {i | q ≤ i} := by
    intro ω₁ ω₂ heq
    have hsub : ∀ ω₁ ω₂ : ℕ → Bool, (∀ i, q ≤ i → ω₁ i = ω₂ i) →
        ω₁ ∈ G' → ω₂ ∈ G' := by
      intro x y hxy hx
      rw [Set.mem_iInter] at hx ⊢
      intro b
      have hupd : updatePrefix x b = updatePrefix y b := by
        ext i
        by_cases hi : i < q
        · simp [updatePrefix, hi]
        · simp [updatePrefix, hi, hxy i (not_lt.mp hi)]
      simpa [hupd] using hx b
    exact propext ⟨hsub ω₁ ω₂ (fun i hi => heq i hi), hsub ω₂ ω₁ (fun i hi => (heq i hi).symm)⟩
  have hBG' : B ⊆ G' := by
    intro ω hω
    rw [Set.mem_iInter]
    intro b
    have heq : ∀ i ∈ (s : Set ℕ)ᶜ, ω i = updatePrefix ω b i := by
      intro i hi
      simp only [s, Finset.coe_range, Set.mem_compl_iff, Set.mem_Iio, not_lt] at hi
      simp [updatePrefix, not_lt.mpr hi]
    exact hBG ((hBsc heq).mp hω)
  have hG'_le : coins G' ≤ coins B := by
    let C : (Fin q → Bool) → Set (ℕ → Bool) := fun b => {ω | ∀ i : Fin q, ω i.1 = b i}
    have hC_dep : ∀ b, DependsOn (C b) {i | i < q} := by
      intro b ω₁ ω₂ heq
      apply propext
      constructor
      · intro h i
        rw [← heq i.1 i.isLt, h i]
      · intro h i
        rw [heq i.1 i.isLt, h i]
    have hC_meas : ∀ b, MeasurableSet (C b) :=
      fun b => measurableSet_of_dependsOn_finite (Set.finite_lt_nat q) (hC_dep b)
    have hC_disj :
        ((Finset.univ : Finset (Fin q → Bool)) : Set (Fin q → Bool)).PairwiseDisjoint C := by
      intro b₁ _ b₂ _ hne
      rw [Function.onFun, Set.disjoint_left]
      intro ω h₁ h₂
      apply hne
      funext i
      exact (h₁ i).symm.trans (h₂ i)
    have hC_union : (⋃ b ∈ (Finset.univ : Finset (Fin q → Bool)), C b) = Set.univ := by
      ext ω
      simp only [Set.mem_iUnion, Finset.mem_univ, Set.mem_univ, iff_true]
      exact ⟨fun i => ω i.1, trivial, fun _ => rfl⟩
    have hC_sum : ∑ b : Fin q → Bool, coins (C b) = 1 := by
      rw [← measure_biUnion_finset hC_disj (fun b _ => hC_meas b), hC_union, measure_univ]
    have hCG_union : (⋃ b ∈ (Finset.univ : Finset (Fin q → Bool)), C b ∩ G) = G := by
      rw [← Set.iUnion₂_inter, hC_union, Set.univ_inter]
    have hCG_sum : ∑ b : Fin q → Bool, coins (C b ∩ G) = coins G := by
      rw [← measure_biUnion_finset (fun b₁ _ b₂ _ h =>
          (hC_disj (Finset.mem_coe.mpr (Finset.mem_univ b₁))
            (Finset.mem_coe.mpr (Finset.mem_univ b₂)) h).mono
            Set.inter_subset_left Set.inter_subset_left)
          (fun b _ => (hC_meas b).inter hmG), hCG_union]
    have hslice : ∀ b : Fin q → Bool,
        coins (C b) * coins G' ≤ coins (C b ∩ G) := by
      intro b
      let Gb : Set (ℕ → Bool) := {ω | updatePrefix ω b ∈ G}
      have hmGb : MeasurableSet Gb := hmG.preimage (hm_upd b)
      have hGb_dep : DependsOn Gb {i | q ≤ i} := by
        intro ω₁ ω₂ heq
        have hupd : updatePrefix ω₁ b = updatePrefix ω₂ b := by
          ext i
          by_cases hi : i < q
          · simp [updatePrefix, hi]
          · simp [updatePrefix, hi, heq i (not_lt.mp hi)]
        show (updatePrefix ω₁ b ∈ G) = (updatePrefix ω₂ b ∈ G)
        rw [hupd]
      have hinter : C b ∩ Gb = C b ∩ G := by
        ext ω
        constructor
        · rintro ⟨hωC, hωGb⟩
          refine ⟨hωC, ?_⟩
          have hupd : updatePrefix ω b = ω := by
            ext i
            by_cases hi : i < q
            · simp [updatePrefix, hi, hωC ⟨i, hi⟩]
            · simp [updatePrefix, hi]
          simpa [Gb, hupd] using hωGb
        · rintro ⟨hωC, hωG⟩
          refine ⟨hωC, ?_⟩
          have hupd : updatePrefix ω b = ω := by
            ext i
            by_cases hi : i < q
            · simp [updatePrefix, hi, hωC ⟨i, hi⟩]
            · simp [updatePrefix, hi]
          simpa [Gb, hupd] using hωG
      have hG'sub : G' ⊆ Gb := fun ω hω => (Set.mem_iInter.mp hω) b
      calc
        coins (C b) * coins G' ≤ coins (C b) * coins Gb := by gcongr
        _ = coins (C b ∩ Gb) :=
            (indepSet_lt_ge q (hC_dep b) hmGb hGb_dep).measure_inter_eq_mul.symm
        _ = coins (C b ∩ G) := by rw [hinter]
    calc
      coins G' = (∑ b : Fin q → Bool, coins (C b)) * coins G' := by rw [hC_sum, one_mul]
      _ = ∑ b : Fin q → Bool, coins (C b) * coins G' := Finset.sum_mul _ _ _
      _ ≤ ∑ b : Fin q → Bool, coins (C b ∩ G) := Finset.sum_le_sum fun b _ => hslice b
      _ = coins G := hCG_sum
      _ = coins B := hGeq
  have hmA : MeasurableSet A := measurableSet_of_dependsOn_finite (Set.finite_lt_nat q) hA
  calc
    coins (A ∩ B) ≤ coins (A ∩ G') := measure_mono (Set.inter_subset_inter_right A hBG')
    _ = coins A * coins G' := (indepSet_lt_ge q hA hmG' hG'dep).measure_inter_eq_mul
    _ ≤ coins A * coins B := by gcongr

/-- Under `coins`, a set depending only on bits `< q` and any set (even non-measurable) depending
only on bits `≥ q` satisfy `coins (A ∩ B) = coins A * coins B`. -/
theorem coins_inter_eq_mul_lt_ge (q : ℕ) {A B : Set (ℕ → Bool)}
    (hA : DependsOn A {i | i < q}) (hB : DependsOn B {i | q ≤ i}) :
    coins (A ∩ B) = coins A * coins B := by
  have hmA : MeasurableSet A := measurableSet_of_dependsOn_finite (Set.finite_lt_nat q) hA
  have hAc : DependsOn Aᶜ {i | i < q} := fun ω₁ ω₂ heq => propext (not_congr (iff_of_eq (hA heq)))
  have h1 : coins (A ∩ B) ≤ coins A * coins B := coins_inter_le_mul_lt_ge q hA hB
  have h2 : coins (Aᶜ ∩ B) ≤ coins Aᶜ * coins B := coins_inter_le_mul_lt_ge q hAc hB
  have hsum_eq : coins A * coins B + coins Aᶜ * coins B = coins B := by
    rw [← add_mul, measure_add_measure_compl hmA, measure_univ, one_mul]
  have hB_le : coins B ≤ coins (A ∩ B) + coins (Aᶜ ∩ B) := by
    calc
      coins B = coins ((A ∩ B) ∪ (Aᶜ ∩ B)) := by
          congr 1; ext ω; by_cases h : ω ∈ A <;> simp [h]
      _ ≤ coins (A ∩ B) + coins (Aᶜ ∩ B) := measure_union_le _ _
  have hsum_le : coins A * coins B + coins Aᶜ * coins B ≤ coins (A ∩ B) + coins (Aᶜ ∩ B) :=
    hsum_eq.symm ▸ hB_le
  have hne : coins (Aᶜ ∩ B) ≠ ⊤ := measure_ne_top coins _
  have hsum_eq2 : coins (A ∩ B) + coins (Aᶜ ∩ B) = coins A * coins B + coins Aᶜ * coins B :=
    le_antisymm (add_le_add h1 h2) hsum_le
  have hge : coins A * coins B ≤ coins (A ∩ B) := by
    by_contra hlt
    rw [not_le] at hlt
    have : coins (A ∩ B) + coins (Aᶜ ∩ B) < coins A * coins B + coins Aᶜ * coins B :=
      ENNReal.add_lt_add_of_lt_of_le hne hlt h2
    exact ne_of_lt this hsum_eq2
  exact le_antisymm h1 hge

/-- Words read by `readWord` from pairwise disjoint bit ranges are mutually independent under
`coins`. -/
theorem iIndepFun_readWord {ι : Type*} {pos w : ι → ℕ}
    (hdisj : Pairwise fun i j =>
      Disjoint (Set.Ico (pos i) (pos i + w i)) (Set.Ico (pos j) (pos j + w j))) :
    iIndepFun (fun i ω => readWord ω (pos i) (w i)) coins := by
  have hind : iIndep (fun i => cylinderEvents (X := fun _ => Bool)
      (Set.Ico (pos i) (pos i + w i))) coins :=
    iIndep_cylinderEvents_of_pairwise_disjoint hdisj
  refine iIndep_of_iIndep_of_le hind fun i => ?_
  exact (measurable_readWord_cylinderEvents (pos i) (w i)).comap_le

/-- Consecutive words of width `w` starting at `pos` are mutually independent under `coins`. -/
theorem iIndepFun_readWord_blocks (pos w : ℕ) :
    iIndepFun (fun k ω => readWord ω (pos + k * w) w) coins := by
  refine iIndepFun_readWord fun i j hij => ?_
  dsimp only
  rw [Set.Ico_disjoint_Ico]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have : i + 1 ≤ j := hlt
    have : (i + 1) * w ≤ j * w := Nat.mul_le_mul_right w this
    rw [Nat.succ_mul] at this
    omega
  · have : j + 1 ≤ i := hgt
    have : (j + 1) * w ≤ i * w := Nat.mul_le_mul_right w this
    rw [Nat.succ_mul] at this
    omega

/-- Two `readWord` values read from disjoint bit ranges are independent under `coins`. -/
theorem indepFun_readWord {pos₁ w₁ pos₂ w₂ : ℕ}
    (hdisj : pos₁ + w₁ ≤ pos₂ ∨ pos₂ + w₂ ≤ pos₁) :
    IndepFun (fun ω => readWord ω pos₁ w₁) (fun ω => readWord ω pos₂ w₂) coins := by
  have hind : iIndepFun (fun b : Bool => if b then (fun ω => readWord ω pos₁ w₁)
      else (fun ω => readWord ω pos₂ w₂)) coins := by
    let pos : Bool → ℕ := fun b => if b then pos₁ else pos₂
    let w : Bool → ℕ := fun b => if b then w₁ else w₂
    have hpair : Pairwise fun i j : Bool =>
        Disjoint (Set.Ico (pos i) (pos i + w i)) (Set.Ico (pos j) (pos j + w j)) := by
      intro i j hij
      cases i <;> cases j <;> simp_all [pos, w] <;> omega
    convert iIndepFun_readWord hpair using 1
    ext b ω
    cases b <;> rfl
  exact hind.indepFun (by decide : true ≠ false)

end Independence

end WordRAM
