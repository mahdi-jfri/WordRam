module

public import WordRAM.Coins

/-!
# Fresh conditional randomness

Fresh conditional randomness: if a first stage
inspects only a prefix of the random bits `ω` (formally, `τ : (ℕ → Bool) → Option (ℕ × α)` is
prefix-determined: `τ ω = some (q, x)` is preserved when `ω'` agrees with `ω` below `q`), and
for each `(q, x)` in its range the second-stage event `E q x` depends only on bits at positions
`≥ q` and has probability at most `δ`, then the event `∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x`
has probability at most `coins {ω | (τ ω).isSome} * δ ≤ δ`.

We prove both the tail-event form (`coins_fresh_bits`, `coins_fresh_bits_mul`) and the shifted
form (`coins_fresh_bits_shift`, `coins_fresh_bits_shift_mul`), without requiring measurability
assumptions on `τ` or `E`.
-/

public section

namespace WordRAM

open MeasureTheory

/-- `τ : (ℕ → Bool) → Option (ℕ × α)` is prefix-determined if whenever `τ ω = some (q, x)` and
`ω'` agrees with `ω` on all bits `< q`, we also have `τ ω' = some (q, x)`. -/
@[expose]
def PrefixDetermined {α : Type*} (τ : (ℕ → Bool) → Option (ℕ × α)) : Prop :=
  ∀ ⦃ω ω' : ℕ → Bool⦄ ⦃q : ℕ⦄ ⦃x : α⦄,
    τ ω = some (q, x) → (∀ i < q, ω' i = ω i) → τ ω' = some (q, x)

/-- Filtering a prefix-determined map by a predicate on its value preserves `PrefixDetermined`. -/
theorem PrefixDetermined.guard {α : Type*} {τ : (ℕ → Bool) → Option (ℕ × α)}
    (hτ : PrefixDetermined τ) (P : ℕ → α → Prop) [∀ q x, Decidable (P q x)] :
    PrefixDetermined (fun ω =>
      match τ ω with
      | none => none
      | some (q, x) => if P q x then some (q, x) else none) := by
  intro ω ω' q x hω heq
  cases hτ_ω : τ ω with
  | none => simp [hτ_ω] at hω
  | some qx =>
    rcases qx with ⟨q₀, x₀⟩
    simp only [hτ_ω] at hω
    split_ifs at hω with hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hω
      rcases hω with ⟨rfl, rfl⟩
      have hω' := hτ hτ_ω heq
      simp [hω', hp]

/-- Mapping the second component of a prefix-determined map preserves `PrefixDetermined`. -/
theorem PrefixDetermined.mapVal {α β : Type*} {τ : (ℕ → Bool) → Option (ℕ × α)}
    (hτ : PrefixDetermined τ) (f : ℕ → α → β) :
    PrefixDetermined (fun ω => (τ ω).map fun qx => (qx.1, f qx.1 qx.2)) := by
  intro ω ω' q y hω heq
  cases hτ_ω : τ ω with
  | none => simp [hτ_ω] at hω
  | some qx =>
    rcases qx with ⟨q₀, x₀⟩
    simp only [hτ_ω, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hω
    rcases hω with ⟨rfl, rfl⟩
    have hω' := hτ hτ_ω heq
    simp [hω']

private def prefixExtend (q : ℕ) (b : Fin q → Bool) : ℕ → Bool :=
  fun i => if h : i < q then b ⟨i, h⟩ else false

private def prefixCyl (q : ℕ) (b : Fin q → Bool) : Set (ℕ → Bool) :=
  {ω | ∀ i : Fin q, ω i.1 = b i}

private theorem prefixCyl_dependsOn (q : ℕ) (b : Fin q → Bool) :
    DependsOn (prefixCyl q b) {i | i < q} := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · intro h i
    rw [← heq i.1 i.isLt, h i]
  · intro h i
    rw [heq i.1 i.isLt, h i]

private theorem prefixCyl_measurable (q : ℕ) (b : Fin q → Bool) :
    MeasurableSet (prefixCyl q b) :=
  measurableSet_of_dependsOn_finite (Set.finite_lt_nat q) (prefixCyl_dependsOn q b)

/-- Multiplicative fresh-bits bound: if `τ` is prefix-determined and each `E q x` depends only on
bits `≥ q` with `coins (E q x) ≤ δ` whenever `τ` can produce `(q, x)`, then the combined event
has measure at most `coins {ω | (τ ω).isSome} * δ`. -/
theorem coins_fresh_bits_mul {α : Type*} (τ : (ℕ → Bool) → Option (ℕ × α))
    (hτ : PrefixDetermined τ) (E : ℕ → α → Set (ℕ → Bool))
    (hE_dep : ∀ q x, DependsOn (E q x) {i | q ≤ i})
    {δ : ENNReal}
    (hE_prob : ∀ ω q x, τ ω = some (q, x) → coins (E q x) ≤ δ) :
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x} ≤
      coins {ω | (τ ω).isSome} * δ := by
  let I := Σ q : ℕ, (Fin q → Bool)
  let good (p : I) : Prop := ∃ x, τ (prefixExtend p.1 p.2) = some (p.1, x)
  let piece (p : {p : I // good p}) : Set (ℕ → Bool) := prefixCyl p.1.1 p.1.2
  have hpiece_meas : ∀ p, MeasurableSet (piece p) :=
    fun p => prefixCyl_measurable p.1.1 p.1.2
  have hpiece_disj : Pairwise fun p₁ p₂ => Disjoint (piece p₁) (piece p₂) := by
    intro p₁ p₂ hne
    rw [Set.disjoint_left]
    intro ω h₁ h₂
    rcases p₁ with ⟨⟨q₁, b₁⟩, x₁, hx₁⟩
    rcases p₂ with ⟨⟨q₂, b₂⟩, x₂, hx₂⟩
    have hτ₁ : τ ω = some (q₁, x₁) := hτ hx₁ fun i hi => by
      have : ω i = b₁ ⟨i, hi⟩ := h₁ ⟨i, hi⟩
      simp [prefixExtend, hi, this]
    have hτ₂ : τ ω = some (q₂, x₂) := hτ hx₂ fun i hi => by
      have : ω i = b₂ ⟨i, hi⟩ := h₂ ⟨i, hi⟩
      simp [prefixExtend, hi, this]
    have hq : q₁ = q₂ := by
      have heq := hτ₁.symm.trans hτ₂
      injection heq with hprod
      exact congrArg Prod.fst hprod
    apply hne
    ext
    · exact hq
    · subst hq
      apply heq_of_eq
      funext i
      exact (h₁ i).symm.trans (h₂ i)
  have hpiece_union : (⋃ p : {p : I // good p}, piece p) = {ω | (τ ω).isSome} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Option.isSome_iff_exists]
    constructor
    · rintro ⟨⟨⟨q, b⟩, x, hx⟩, hω⟩
      refine ⟨(q, x), hτ hx fun i hi => ?_⟩
      simp [prefixExtend, hi, hω ⟨i, hi⟩]
    · rintro ⟨⟨q, x⟩, hω⟩
      let b : Fin q → Bool := fun i => ω i.1
      have hgood : good ⟨q, b⟩ := ⟨x, hτ hω fun i hi => by simp [prefixExtend, hi, b]⟩
      exact ⟨⟨⟨q, b⟩, hgood⟩, fun _ => rfl⟩
  have hsum_pieces :
      (∑' p : {p : I // good p}, coins (piece p)) = coins {ω | (τ ω).isSome} := by
    rw [← hpiece_union, measure_iUnion hpiece_disj hpiece_meas]
  choose val hval using fun p : {p : I // good p} => p.2
  have hsub : {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x} ⊆
      ⋃ p : {p : I // good p}, (piece p ∩ E p.1.1 (val p)) := by
    rintro ω ⟨q, x, hω, hE⟩
    let b : Fin q → Bool := fun i => ω i.1
    have hp2 : τ (prefixExtend q b) = some (q, x) :=
      hτ hω fun i hi => by simp [prefixExtend, hi, b]
    have hgood : good ⟨q, b⟩ := ⟨x, hp2⟩
    let p : {p : I // good p} := ⟨⟨q, b⟩, hgood⟩
    have hx_eq : val p = x := by
      have hp1 : τ (prefixExtend q b) = some (q, val p) := hval p
      have heq := hp1.symm.trans hp2
      injection heq with hprod
      exact congrArg Prod.snd hprod
    refine Set.mem_iUnion.mpr ⟨p, ?_⟩
    exact ⟨fun _ => rfl, hx_eq ▸ hE⟩
  calc
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x}
      ≤ coins (⋃ p : {p : I // good p}, (piece p ∩ E p.1.1 (val p))) := measure_mono hsub
    _ ≤ ∑' p : {p : I // good p}, coins (piece p ∩ E p.1.1 (val p)) := measure_iUnion_le _
    _ = ∑' p : {p : I // good p}, coins (piece p) * coins (E p.1.1 (val p)) := by
        congr 1 with p
        exact coins_inter_eq_mul_lt_ge p.1.1 (prefixCyl_dependsOn _ _) (hE_dep _ _)
    _ ≤ ∑' p : {p : I // good p}, coins (piece p) * δ := by
        refine ENNReal.tsum_le_tsum fun p => ?_
        gcongr
        exact hE_prob (prefixExtend p.1.1 p.1.2) p.1.1 (val p) (hval p)
    _ = (∑' p : {p : I // good p}, coins (piece p)) * δ := ENNReal.tsum_mul_right
    _ = coins {ω | (τ ω).isSome} * δ := by rw [hsum_pieces]

/-- Fresh-bits lemma (tail-event form): if `τ` is prefix-determined and each `E q x` depends only
on bits `≥ q` with `coins (E q x) ≤ δ` whenever `τ` can produce `(q, x)`, then
`coins {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x} ≤ δ`. -/
theorem coins_fresh_bits {α : Type*} (τ : (ℕ → Bool) → Option (ℕ × α))
    (hτ : PrefixDetermined τ) (E : ℕ → α → Set (ℕ → Bool))
    (hE_dep : ∀ q x, DependsOn (E q x) {i | q ≤ i})
    {δ : ENNReal}
    (hE_prob : ∀ ω q x, τ ω = some (q, x) → coins (E q x) ≤ δ) :
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x} ≤ δ := by
  calc
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ ω ∈ E q x}
      ≤ coins {ω | (τ ω).isSome} * δ := coins_fresh_bits_mul τ hτ E hE_dep hE_prob
    _ ≤ 1 * δ := by gcongr; exact prob_le_one
    _ = δ := one_mul δ

/-- Multiplicative fresh-bits lemma (shifted form): if `τ` is prefix-determined and each
`F q x` has `coins (F q x) ≤ δ` whenever `τ` can produce `(q, x)`, then the event
`∃ q x, τ ω = some (q, x) ∧ (fun i => ω (q + i)) ∈ F q x` has probability at most
`coins {ω | (τ ω).isSome} * δ`. -/
theorem coins_fresh_bits_shift_mul {α : Type*} (τ : (ℕ → Bool) → Option (ℕ × α))
    (hτ : PrefixDetermined τ) (F : ℕ → α → Set (ℕ → Bool))
    {δ : ENNReal}
    (hF_prob : ∀ ω q x, τ ω = some (q, x) → coins (F q x) ≤ δ) :
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ (fun i => ω (q + i)) ∈ F q x} ≤
      coins {ω | (τ ω).isSome} * δ := by
  let E : ℕ → α → Set (ℕ → Bool) := fun q x => {ω | (fun i => ω (q + i)) ∈ F q x}
  have hE_dep : ∀ q x, DependsOn (E q x) {i | q ≤ i} := by
    intro q x ω₁ ω₂ heq
    have hshift : (fun i => ω₁ (q + i)) = (fun i => ω₂ (q + i)) := by
      ext i
      exact heq (q + i) (Nat.le_add_right q i)
    show ((fun i => ω₁ (q + i)) ∈ F q x) = ((fun i => ω₂ (q + i)) ∈ F q x)
    rw [hshift]
  have hE_prob : ∀ ω q x, τ ω = some (q, x) → coins (E q x) ≤ δ := by
    intro ω q x hω
    exact le_trans (coins_shift_preimage_le q (F q x)) (hF_prob ω q x hω)
  exact coins_fresh_bits_mul τ hτ E hE_dep hE_prob

/-- Fresh-bits lemma (shifted form): if `τ` is prefix-determined and each `F q x` has
`coins (F q x) ≤ δ` whenever `τ` can produce `(q, x)`, then
`coins {ω | ∃ q x, τ ω = some (q, x) ∧ (fun i => ω (q + i)) ∈ F q x} ≤ δ`. -/
theorem coins_fresh_bits_shift {α : Type*} (τ : (ℕ → Bool) → Option (ℕ × α))
    (hτ : PrefixDetermined τ) (F : ℕ → α → Set (ℕ → Bool))
    {δ : ENNReal}
    (hF_prob : ∀ ω q x, τ ω = some (q, x) → coins (F q x) ≤ δ) :
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ (fun i => ω (q + i)) ∈ F q x} ≤ δ := by
  calc
    coins {ω | ∃ q x, τ ω = some (q, x) ∧ (fun i => ω (q + i)) ∈ F q x}
      ≤ coins {ω | (τ ω).isSome} * δ := coins_fresh_bits_shift_mul τ hτ F hF_prob
    _ ≤ 1 * δ := by gcongr; exact prob_le_one
    _ = δ := one_mul δ

end WordRAM
