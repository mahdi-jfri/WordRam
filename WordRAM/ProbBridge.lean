module

public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import WordRAM.CoinsFresh
public import WordRAM.ProbRuns
public import WordRAM.Prob
import WordRAM.Exec

/-!
# Bridge from machine coin measures to Mathlib `PMF` laws

Connects randomized machine runs (`Runs`) under the uniform bit-stream measure `coins` to abstract
`PMF` distributions and their outer measures / measures:

* `SubLaw`, `ExactSubLaw`, `ProcSubLaw`, `ProcExactSubLaw`: sub-probability law specifications
  stating that every reachable outcome `a : α` occurs with `coins`-probability at most `μ st a`
  (or `(1 - φ st) * μ st a`).
* `SubLaw.toOuterMeasure_le`, `SubLaw.toMeasure_le`: lifting pointwise bounds over countable
  output types `[Countable α]` to arbitrary events `E : Set α` (`≤ (μ st).toOuterMeasure E` and
  `≤ (μ st).toMeasure E`).
* `ExactSubLaw.toOuterMeasure_eq`, `ExactSubLaw.toMeasure_eq`: exact event probability
  `(1 - φ st) * (μ st).toOuterMeasure E` when outcome predicates are measurable and disjoint
  across distinct `a : α`.
* `SubLaw.seq_bind`, `SubLaw.seq_normal_bind`, `SubLaw.seq_map`: sequential composition (`PMF.bind`
  and `PMF.map`) via `coins_fresh_bits_mul` and run locality (`Runs.congr_bits`).
* `SubLaw.call`, `SubLaw.cond`: procedure calls and conditional branching.
* `SubLaw.loop_rec`, `listBindM`, `SubLaw.loop_fold`: well-founded loops and list-indexed
  `PMF.bind` chains, pairing naturally with `ProbTriple.loop` / `ProbTriple.loop_bound` for failure
  probabilities.
-/

public section

namespace WordRAM

open MeasureTheory

/-! ## Sub-law specifications -/

/-- A statement `s` at word size `w` and program `p` satisfies a `SubLaw` wrt state precondition
`P`, outcome relation `R`, and distribution family `μ : State → PMF α` when from every start state
`st` satisfying `P st`, every value `a : α` occurs with probability at most `μ st a`. -/
@[expose]
def SubLaw (w : ℕ) (p : Program) (s : Stmt) {α : Type*}
    (P : State → Prop) (R : State → α → Outcome → State → ℕ → Prop)
    (μ : State → PMF α) : Prop :=
  ∀ st, P st → ∀ a : α,
    coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} ≤ μ st a

/-- Exact sub-probability law: every value `a : α` occurs with probability `(1 - φ st) * μ st a`
for some state-dependent failure rate `φ st`. -/
@[expose]
def ExactSubLaw (w : ℕ) (p : Program) (s : Stmt) {α : Type*}
    (P : State → Prop) (R : State → α → Outcome → State → ℕ → Prop)
    (μ : State → PMF α) (φ : State → ENNReal) : Prop :=
  ∀ st, P st → ∀ a : α,
    coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} = (1 - φ st) * μ st a

/-- Procedure-level `SubLaw` specification over start states `startState args mem pos`. -/
@[expose]
def ProcSubLaw (w : ℕ) (p : Program) (f : ℕ) {α : Type*}
    (Pre : List ℕ → (ℕ → ℕ) → Prop)
    (Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop)
    (μ : List ℕ → (ℕ → ℕ) → PMF α) : Prop :=
  ∃ body, p.procs[f]? = some body ∧
    ∀ args mem pos, (∀ a ∈ args, a < 2 ^ w) → Pre args mem →
      ∀ a : α,
        coins {ω | ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
          Dec args mem a o.value st'.mem c} ≤ μ args mem a

/-- Procedure-level `ExactSubLaw` specification over start states `startState args mem pos`. -/
@[expose]
def ProcExactSubLaw (w : ℕ) (p : Program) (f : ℕ) {α : Type*}
    (Pre : List ℕ → (ℕ → ℕ) → Prop)
    (Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop)
    (μ : List ℕ → (ℕ → ℕ) → PMF α)
    (φ : List ℕ → (ℕ → ℕ) → ENNReal) : Prop :=
  ∃ body, p.procs[f]? = some body ∧
    ∀ args mem pos, (∀ a ∈ args, a < 2 ^ w) → Pre args mem →
      ∀ a : α,
        coins {ω | ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
          Dec args mem a o.value st'.mem c} = (1 - φ args mem) * μ args mem a

/-- An exact sub-probability law `(1 - φ st) * μ st a` yields a `SubLaw` `≤ μ st a`. -/
theorem ExactSubLaw.toSubLaw {w : ℕ} {p : Program} {s : Stmt} {α : Type*}
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    {μ : State → PMF α} {φ : State → ENNReal}
    (h : ExactSubLaw w p s P R μ φ) : SubLaw w p s P R μ := by
  intro st hP a
  rw [h st hP a]
  exact mul_le_of_le_one_left zero_le tsub_le_self

/-- A procedure-level exact sub-probability law yields a `ProcSubLaw`. -/
theorem ProcExactSubLaw.toProcSubLaw {w : ℕ} {p : Program} {f : ℕ} {α : Type*}
    {Pre : List ℕ → (ℕ → ℕ) → Prop}
    {Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop}
    {μ : List ℕ → (ℕ → ℕ) → PMF α} {φ : List ℕ → (ℕ → ℕ) → ENNReal}
    (h : ProcExactSubLaw w p f Pre Dec μ φ) : ProcSubLaw w p f Pre Dec μ := by
  rcases h with ⟨body, hproc, hbound⟩
  refine ⟨body, hproc, fun args mem pos hwords hpre a => ?_⟩
  rw [hbound args mem pos hwords hpre a]
  exact mul_le_of_le_one_left zero_le tsub_le_self

/-- Strengthening preconditions and postconditions in a `SubLaw`. -/
theorem SubLaw.mono {w : ℕ} {p : Program} {s : Stmt} {α : Type*}
    {P P' : State → Prop} {R R' : State → α → Outcome → State → ℕ → Prop}
    {μ μ' : State → PMF α}
    (h : SubLaw w p s P R μ)
    (hP : ∀ st, P' st → P st)
    (hR : ∀ st a o st' c, P' st → R' st a o st' c → R st a o st' c)
    (hμ : ∀ st a, P' st → μ st a ≤ μ' st a) :
    SubLaw w p s P' R' μ' := by
  intro st hP' a
  have hsub :
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R' st a o st' c} ⊆
        {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} := by
    rintro ω ⟨o, st', c, hrun, hr'⟩
    exact ⟨o, st', c, hrun, hR st a o st' c hP' hr'⟩
  exact le_trans (measure_mono hsub) (le_trans (h st (hP st hP') a) (hμ st a hP'))

/-! ## Event bounds from pointwise `SubLaw` bounds -/

private theorem tsum_subtype_eq_toOuterMeasure {α : Type*} (μ : PMF α) (E : Set α) :
    (∑' a : E, μ a.1) = μ.toOuterMeasure E := by
  classical
  rw [μ.toOuterMeasure_apply E, ← tsum_subtype E (fun x => μ x)]

/-- Event bound: if a statement satisfies `SubLaw` over a countable output type `α`, then for every
start state satisfying `P st` and every event `E : Set α`, succeeding with a value in `E` has `coins`
probability at most `(μ st).toOuterMeasure E`. -/
theorem SubLaw.toOuterMeasure_le {w : ℕ} {p : Program} {s : Stmt} {α : Type*} [Countable α]
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop} {μ : State → PMF α}
    (h : SubLaw w p s P R μ) {st : State} (hP : P st) (E : Set α) :
    coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} ≤
      (μ st).toOuterMeasure E := by
  have heq :
      {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} =
        ⋃ a : E, {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a.1 o st' c} := by
    ext ω
    simp [Set.mem_iUnion]
  rw [heq]
  calc
    coins (⋃ a : E, {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a.1 o st' c})
      ≤ ∑' a : E, coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a.1 o st' c} :=
        measure_iUnion_le _
    _ ≤ ∑' a : E, μ st a.1 := ENNReal.tsum_le_tsum fun a => h st hP a.1
    _ = (μ st).toOuterMeasure E := tsum_subtype_eq_toOuterMeasure (μ st) E

/-- Functional-decoder corollary of `SubLaw.toOuterMeasure_le`: if `decode st o st' c ∈ E` along a
good outcome predicate `Good st o st' c`, its probability is at most `(μ st).toOuterMeasure E`. -/
theorem SubLaw.toOuterMeasure_decode_le {w : ℕ} {p : Program} {s : Stmt} {α : Type*} [Countable α]
    {P : State → Prop} {Good : State → Outcome → State → ℕ → Prop}
    {decode : State → Outcome → State → ℕ → α} {μ : State → PMF α}
    (h : SubLaw w p s P (fun st a o st' c => Good st o st' c ∧ decode st o st' c = a) μ)
    {st : State} (hP : P st) (E : Set α) :
    coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ Good st o st' c ∧ decode st o st' c ∈ E} ≤
      (μ st).toOuterMeasure E := by
  have hsub :
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ Good st o st' c ∧ decode st o st' c ∈ E} ⊆
        {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ Good st o st' c ∧
          decode st o st' c = a} := by
    rintro ω ⟨o, st', c, hrun, hgood, hmem⟩
    exact ⟨decode st o st' c, hmem, o, st', c, hrun, hgood, rfl⟩
  exact le_trans (measure_mono hsub) (h.toOuterMeasure_le hP E)

/-- Measure version of `SubLaw.toOuterMeasure_le`: for any `[MeasurableSpace α]` and `E : Set α`,
the success event has probability at most `(μ st).toMeasure E`. -/
theorem SubLaw.toMeasure_le {w : ℕ} {p : Program} {s : Stmt} {α : Type*}
    [Countable α] [MeasurableSpace α]
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop} {μ : State → PMF α}
    (h : SubLaw w p s P R μ) {st : State} (hP : P st) (E : Set α) :
    coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} ≤
      (μ st).toMeasure E :=
  le_trans (h.toOuterMeasure_le hP E) ((μ st).toOuterMeasure_apply_le_toMeasure_apply E)

/-- Procedure-level event bound against `toOuterMeasure`. -/
theorem ProcSubLaw.toOuterMeasure_le {w : ℕ} {p : Program} {f : ℕ} {α : Type*} [Countable α]
    {Pre : List ℕ → (ℕ → ℕ) → Prop}
    {Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop}
    {μ : List ℕ → (ℕ → ℕ) → PMF α}
    (h : ProcSubLaw w p f Pre Dec μ)
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : Pre args mem) (E : Set α) :
    ∃ body, p.procs[f]? = some body ∧
      coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        Dec args mem a o.value st'.mem c} ≤ (μ args mem).toOuterMeasure E := by
  rcases h with ⟨body, hproc, hbound⟩
  refine ⟨body, hproc, ?_⟩
  have hsub : SubLaw w p body
      (fun st => st = startState args mem pos)
      (fun _ a o st' c => Dec args mem a o.value st'.mem c)
      (fun _ => μ args mem) := by
    rintro _ rfl a
    exact hbound args mem pos hwords hpre a
  exact hsub.toOuterMeasure_le rfl E

/-- Procedure-level event bound against `toMeasure`. -/
theorem ProcSubLaw.toMeasure_le {w : ℕ} {p : Program} {f : ℕ} {α : Type*}
    [Countable α] [MeasurableSpace α]
    {Pre : List ℕ → (ℕ → ℕ) → Prop}
    {Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop}
    {μ : List ℕ → (ℕ → ℕ) → PMF α}
    (h : ProcSubLaw w p f Pre Dec μ)
    {args : List ℕ} {mem : ℕ → ℕ} (pos : ℕ)
    (hwords : ∀ a ∈ args, a < 2 ^ w) (hpre : Pre args mem) (E : Set α) :
    ∃ body, p.procs[f]? = some body ∧
      coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
        Dec args mem a o.value st'.mem c} ≤ (μ args mem).toMeasure E := by
  rcases h.toOuterMeasure_le pos hwords hpre E with ⟨body, hproc, hle⟩
  exact ⟨body, hproc, le_trans hle ((μ args mem).toOuterMeasure_apply_le_toMeasure_apply E)⟩

/-- Exact outer-measure equality for an `ExactSubLaw` when distinct `a : α` yield disjoint,
measurable outcome events (for instance when `R st` uniquely determines `a` via `Runs.det`). -/
theorem ExactSubLaw.toOuterMeasure_eq {w : ℕ} {p : Program} {s : Stmt} {α : Type*} [Countable α]
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    {μ : State → PMF α} {φ : State → ENNReal}
    (h : ExactSubLaw w p s P R μ φ) {st : State} (hP : P st)
    (hfunc : ∀ a₁ a₂ o st' c, R st a₁ o st' c → R st a₂ o st' c → a₁ = a₂)
    (hm : ∀ a : α, MeasurableSet {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c})
    (E : Set α) :
    coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} =
      (1 - φ st) * (μ st).toOuterMeasure E := by
  have heq :
      {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} =
        ⋃ a : E, {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a.1 o st' c} := by
    ext ω
    simp [Set.mem_iUnion]
  have hdisj : Pairwise (fun a₁ a₂ : E => Disjoint
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a₁.1 o st' c}
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a₂.1 o st' c}) := by
    rintro ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩ hne
    rw [Set.disjoint_left]
    rintro ω ⟨o₁, st₁, c₁, hrun₁, hr₁⟩ ⟨o₂, st₂, c₂, hrun₂, hr₂⟩
    rcases hrun₁.det hrun₂ with ⟨rfl, rfl, rfl⟩
    exact hne (Subtype.ext (hfunc a₁ a₂ o₁ st₁ c₁ hr₁ hr₂))
  rw [heq, measure_iUnion hdisj fun a => hm a.1]
  have hcongr :
      (∑' a : E, coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a.1 o st' c}) =
        ∑' a : E, (1 - φ st) * μ st a.1 :=
    tsum_congr fun a => h st hP a.1
  rw [hcongr, ENNReal.tsum_mul_left, tsum_subtype_eq_toOuterMeasure]

/-- Exact measure equality when `[MeasurableSpace α]` and `E` is measurable. -/
theorem ExactSubLaw.toMeasure_eq {w : ℕ} {p : Program} {s : Stmt} {α : Type*}
    [Countable α] [MeasurableSpace α]
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    {μ : State → PMF α} {φ : State → ENNReal}
    (h : ExactSubLaw w p s P R μ φ) {st : State} (hP : P st)
    (hfunc : ∀ a₁ a₂ o st' c, R st a₁ o st' c → R st a₂ o st' c → a₁ = a₂)
    (hm : ∀ a : α, MeasurableSet {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c})
    {E : Set α} (hE : MeasurableSet E) :
    coins {ω | ∃ a ∈ E, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} =
      (1 - φ st) * (μ st).toMeasure E := by
  rw [h.toOuterMeasure_eq hP hfunc hm E, (μ st).toMeasure_apply_eq_toOuterMeasure_apply hE]

/-! ## Deterministic, map, call, and branch rules -/

/-- A deterministic step producing value `f st` satisfies `SubLaw` with respect to `PMF.pure`. -/
theorem SubLaw.pure {w : ℕ} {p : Program} {s : Stmt} {α : Type*}
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    (f : State → α)
    (hf : ∀ st a o st' c, P st → R st a o st' c → a = f st) :
    SubLaw w p s P R (fun st => PMF.pure (f st)) := by
  intro st hP a
  by_cases ha : a = f st
  · subst ha
    simpa using (measure_mono (Set.subset_univ _ : _ ⊆ Set.univ)).trans_eq measure_univ
  · have hempty : {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
      intro o st' c _ hr
      exact ha (hf st a o st' c hP hr)
    simp [hempty, ha]

/-- Mapping a countable-output `SubLaw` by `f : State → α → β`. -/
theorem SubLaw.map {w : ℕ} {p : Program} {s : Stmt} {α β : Type*} [Countable α]
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    {μ : State → PMF α} (h : SubLaw w p s P R μ) (f : State → α → β) :
    SubLaw w p s P
      (fun st b o st' c => ∃ a, R st a o st' c ∧ f st a = b)
      (fun st => (μ st).map (f st)) := by
  intro st hP b
  have hsub :
      {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ ∃ a, R st a o st' c ∧ f st a = b} ⊆
        {ω | ∃ a ∈ f st ⁻¹' {b}, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} := by
    rintro ω ⟨o, st', c, hrun, a, hr, hfa⟩
    exact ⟨a, hfa, o, st', c, hrun, hr⟩
  calc
    coins {ω | ∃ o st' c, Runs w p ω s st o st' c ∧ ∃ a, R st a o st' c ∧ f st a = b}
      ≤ coins {ω | ∃ a ∈ f st ⁻¹' {b}, ∃ o st' c, Runs w p ω s st o st' c ∧ R st a o st' c} :=
        measure_mono hsub
    _ ≤ (μ st).toOuterMeasure (f st ⁻¹' {b}) := h.toOuterMeasure_le hP (f st ⁻¹' {b})
    _ = ((μ st).map (f st)).toOuterMeasure {b} := by
        rw [PMF.toOuterMeasure_map_apply]
    _ = ((μ st).map (f st)) b := PMF.toOuterMeasure_apply_singleton _ b

/-- Procedure call rule for `SubLaw`: calling a procedure meeting `ProcSubLaw` yields a `SubLaw`
for `Stmt.call r f args`. -/
theorem SubLaw.call {w : ℕ} {p : Program} {r f : ℕ} {args : List Expr} {α : Type*}
    {P : State → Prop}
    {Pre : List ℕ → (ℕ → ℕ) → Prop}
    {Dec : List ℕ → (ℕ → ℕ) → α → ℕ → (ℕ → ℕ) → ℕ → Prop}
    {μ : List ℕ → (ℕ → ℕ) → PMF α}
    (hf : ProcSubLaw w p f Pre Dec μ)
    (hargs : ∀ st, P st → ∃ vs, evalArgs w st args = some vs ∧
      (∀ v ∈ vs, v < 2 ^ w) ∧ Pre vs st.mem)
    (μ' : State → PMF α)
    (hμ : ∀ st vs, P st → evalArgs w st args = some vs → μ vs st.mem = μ' st) :
    SubLaw w p (.call r f args) P
      (fun st a o st' c =>
        ∃ vs c₁, evalArgs w st args = some vs ∧ o = .normal ∧
          Dec vs st.mem a (st'.regs r) st'.mem c₁ ∧ c = argsSize args + c₁ + 1)
      μ' := by
  rcases hf with ⟨body, hproc, hbound⟩
  intro st hP a
  rcases hargs st hP with ⟨vs, hvs, hwords, hpre⟩
  rw [← hμ st vs hP hvs]
  have hsub :
      {ω | ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧
        ∃ vs' c₁, evalArgs w st args = some vs' ∧ o = .normal ∧
          Dec vs' st.mem a (st'.regs r) st'.mem c₁ ∧ c = argsSize args + c₁ + 1} ⊆
      {ω | ∃ o₁ st₁ c₁, Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁ ∧
        Dec vs st.mem a o₁.value st₁.mem c₁} := by
    rintro ω ⟨o, st', c, hrun, vs', c₁, hvs', rfl, hdec, hc⟩
    rw [hvs] at hvs'
    injection hvs' with hvs_eq
    subst hvs_eq
    rcases runs_call_iff.mp hrun with ⟨vs'', body', o₁, st₁, c₁', hvs'', hproc', hbody, _, rfl, hc'⟩
    rw [hvs] at hvs''
    injection hvs'' with hvs_eq
    subst hvs_eq
    rw [hproc] at hproc'
    injection hproc' with hbody_eq
    subst hbody_eq
    have hc_eq : c₁' = c₁ := by omega
    subst hc_eq
    have hreg : (Function.update st.regs r o₁.value) r = o₁.value := by simp
    refine ⟨o₁, st₁, c₁', hbody, ?_⟩
    simpa [hreg] using hdec
  exact le_trans (measure_mono hsub) (hbound vs st.mem st.pos hwords hpre a)

/-- Conditional branching rule for `SubLaw` when `e` deterministically evaluates. -/
theorem SubLaw.cond {w : ℕ} {p : Program} {e : Expr} {s t : Stmt} {α : Type*}
    {P : State → Prop} {R : State → α → Outcome → State → ℕ → Prop}
    {μ : State → PMF α}
    (heval : ∀ st, P st → ∃ v, e.eval w st = some v)
    (hs : SubLaw w p s (fun st => P st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0)
      (fun st a o st' c => R st a o st' (e.size + c + 1)) μ)
    (ht : SubLaw w p t (fun st => P st ∧ e.eval w st = some 0)
      (fun st a o st' c => R st a o st' (e.size + c + 1)) μ) :
    SubLaw w p (.cond e s t) P R μ := by
  intro st hP a
  obtain ⟨v, hv⟩ := heval st hP
  by_cases hv0 : v = 0
  · subst hv0
    have hsub :
        {ω | ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ R st a o st' c} ⊆
          {ω | ∃ o st' c₁, Runs w p ω t st o st' c₁ ∧ R st a o st' (e.size + c₁ + 1)} := by
      rintro ω ⟨o, st', c, hrun, hr⟩
      rcases runs_cond_iff.mp hrun with ⟨v', c₁, hv', hrun₁, rfl⟩
      rw [hv] at hv'
      injection hv' with hv_eq
      subst hv_eq
      exact ⟨o, st', c₁, by simpa using hrun₁, hr⟩
    exact le_trans (measure_mono hsub) (ht st ⟨hP, hv⟩ a)
  · have hsub :
        {ω | ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ R st a o st' c} ⊆
          {ω | ∃ o st' c₁, Runs w p ω s st o st' c₁ ∧ R st a o st' (e.size + c₁ + 1)} := by
      rintro ω ⟨o, st', c, hrun, hr⟩
      rcases runs_cond_iff.mp hrun with ⟨v', c₁, hv', hrun₁, rfl⟩
      rw [hv] at hv'
      injection hv' with hv_eq
      subst hv_eq
      exact ⟨o, st', c₁, by simpa [hv0] using hrun₁, hr⟩
    exact le_trans (measure_mono hsub) (hs st ⟨hP, v, hv, hv0⟩ a)

/-! ## Fresh-bits sequential and loop composition (`PMF.bind`) -/

private noncomputable def normalStepPrefix (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (M : State → ℕ → Prop) (ω : ℕ → Bool) : Option (ℕ × (State × ℕ)) := by
  classical
  exact if h : ∃ res : State × ℕ, Runs w p ω s st .normal res.1 res.2 ∧ M res.1 res.2 then
    let res := Classical.choose h
    some (res.1.pos, res)
  else none

private theorem normalStepPrefix_some {w : ℕ} {p : Program} {s : Stmt} {st : State}
    {M : State → ℕ → Prop} {ω : ℕ → Bool} {q : ℕ} {res : State × ℕ}
    (hω : normalStepPrefix w p s st M ω = some (q, res)) :
    q = res.1.pos ∧ Runs w p ω s st .normal res.1 res.2 ∧ M res.1 res.2 := by
  classical
  rw [normalStepPrefix] at hω
  split_ifs at hω with h
  simp only [Option.some.injEq, Prod.mk.injEq] at hω
  rcases hω with ⟨rfl, rfl⟩
  exact ⟨rfl, Classical.choose_spec h⟩

private theorem prefixDetermined_normalStepPrefix (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (M : State → ℕ → Prop) :
    PrefixDetermined (normalStepPrefix w p s st M) := by
  classical
  intro ω ω' q res hω heq
  obtain ⟨hq, hrun, hM⟩ := normalStepPrefix_some hω
  have hrun' : Runs w p ω' s st .normal res.1 res.2 :=
    hrun.congr_bits fun i _ hi₂ => heq i (hq ▸ hi₂)
  rw [normalStepPrefix]
  split_ifs with hcond
  · let res₁ := Classical.choose hcond
    have hspec₁ := Classical.choose_spec hcond
    rcases hspec₁.1.det hrun' with ⟨_, hst_eq, hc_eq⟩
    simp [hst_eq, hc_eq, hq, Prod.ext_iff]
  · exact False.elim (hcond ⟨res, hrun', hM⟩)

private theorem normalStepPrefix_spec {w : ℕ} {p : Program} {s : Stmt} {st : State}
    {M : State → ℕ → Prop} {ω : ℕ → Bool} {st₁ : State} {c₁ : ℕ}
    (hrun : Runs w p ω s st .normal st₁ c₁) (hM : M st₁ c₁) :
    normalStepPrefix w p s st M ω = some (st₁.pos, (st₁, c₁)) := by
  classical
  rw [normalStepPrefix]
  split_ifs with h
  · let res₁ := Classical.choose h
    have hspec₁ := Classical.choose_spec h
    rcases hspec₁.1.det hrun with ⟨_, hst_eq, hc_eq⟩
    simp [hst_eq, hc_eq, Prod.ext_iff]
  · exact False.elim (h ⟨(st₁, c₁), hrun, hM⟩)

private theorem tailSucc_dependsOn (w : ℕ) (p : Program) (u : Stmt)
    (q : ℕ) (st₁ : State) (Q : Outcome → State → ℕ → Prop) :
    DependsOn {ω | q ≤ st₁.pos ∧ ∃ o₂ st₂ c₂, Runs w p ω u st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ c₂}
      {i | q ≤ i} := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · rintro ⟨hq, o₂, st₂, c₂, hrun, hq₂⟩
    exact ⟨hq, o₂, st₂, c₂, hrun.congr_bits_ge fun i hi => (heq i (le_trans hq hi)).symm, hq₂⟩
  · rintro ⟨hq, o₂, st₂, c₂, hrun, hq₂⟩
    exact ⟨hq, o₂, st₂, c₂, hrun.congr_bits_ge fun i hi => heq i (le_trans hq hi), hq₂⟩

/-- Sequential composition of `SubLaw` steps via `PMF.bind`: if each successful outcome of
`Stmt.seq s₁ s₂` factors through an intermediate `.normal` state `st₁` witnessing `a : α` (where
`α` is countable), and `s₂` satisfies `SubLaw` wrt `κ st a` from such `st₁`, then `Stmt.seq s₁ s₂`
satisfies `SubLaw` wrt `(μ₁ st).bind (κ st)`. -/
theorem SubLaw.seq_bind {w : ℕ} {p : Program} {s₁ s₂ : Stmt} {α β : Type*} [Countable α]
    {P₁ : State → Prop}
    {M : State → α → State → ℕ → Prop}
    {R₂ : State → β → Outcome → State → ℕ → Prop}
    {R : State → β → Outcome → State → ℕ → Prop}
    {μ₁ : State → PMF α} {κ : State → α → PMF β}
    (hs₁ : SubLaw w p s₁ P₁ (fun st a o st₁ c₁ => o = .normal ∧ M st a st₁ c₁) μ₁)
    (hs₂ : ∀ st a st₁ c₁, P₁ st → M st a st₁ c₁ → ∀ b : β,
      coins {ω | ∃ o₂ st₂ c₂, Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} ≤ κ st a b)
    (hsplit : ∀ ω st o st' c b, P₁ st →
      Runs w p ω (.seq s₁ s₂) st o st' c → R st b o st' c →
      ∃ st₁ c₁ c₂ a, Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
        Runs w p ω s₂ st₁ o st' c₂ ∧ c = c₁ + c₂ + 1 ∧ R₂ st₁ b o st' c₂) :
    SubLaw w p (.seq s₁ s₂) P₁ R (fun st => (μ₁ st).bind (κ st)) := by
  intro st hP b
  have hsub_union :
      {ω | ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ R st b o st' c} ⊆
        ⋃ a : α, {ω | ∃ st₁ c₁ c₂ o₂ st₂,
          Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
            Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} := by
    rintro ω ⟨o, st', c, hrun, hr⟩
    obtain ⟨st₁, c₁, c₂, a, hrun₁, hm, hrun₂, _, hr₂⟩ := hsplit ω st o st' c b hP hrun hr
    exact Set.mem_iUnion.mpr ⟨a, st₁, c₁, c₂, o, st', hrun₁, hm, hrun₂, hr₂⟩
  have hstep : ∀ a : α,
      coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
        Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
          Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} ≤ μ₁ st a * κ st a b := by
    intro a
    let τ := normalStepPrefix w p s₁ st (M st a)
    let E : ℕ → State × ℕ → Set (ℕ → Bool) := fun q res =>
      {ω | q ≤ res.1.pos ∧ ∃ o₂ st₂ c₂, Runs w p ω s₂ res.1 o₂ st₂ c₂ ∧ R₂ res.1 b o₂ st₂ c₂}
    have hτ : PrefixDetermined τ := prefixDetermined_normalStepPrefix w p s₁ st (M st a)
    have hE_dep : ∀ q res, DependsOn (E q res) {i | q ≤ i} :=
      fun q res => tailSucc_dependsOn w p s₂ q res.1 fun o₂ st₂ c₂ => R₂ res.1 b o₂ st₂ c₂
    have hE_prob : ∀ ω q res, τ ω = some (q, res) → coins (E q res) ≤ κ st a b := by
      intro ω q res hτ_ω
      obtain ⟨_, _, hm⟩ := normalStepPrefix_some hτ_ω
      have hsub : E q res ⊆
          {ω' | ∃ o₂ st₂ c₂, Runs w p ω' s₂ res.1 o₂ st₂ c₂ ∧ R₂ res.1 b o₂ st₂ c₂} :=
        fun _ hmem => hmem.2
      exact le_trans (measure_mono hsub) (hs₂ st a res.1 res.2 hP hm b)
    have hsub_τ :
        {ω | ∃ st₁ c₁ c₂ o₂ st₂,
          Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
            Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} ⊆
          {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res} := by
      rintro ω ⟨st₁, c₁, c₂, o₂, st₂, hrun₁, hm, hrun₂, hr₂⟩
      exact ⟨st₁.pos, (st₁, c₁), normalStepPrefix_spec hrun₁ hm, le_rfl, o₂, st₂, c₂, hrun₂, hr₂⟩
    have hτ_le : coins {ω | (τ ω).isSome} ≤ μ₁ st a := by
      have hsub_pref :
          {ω | (τ ω).isSome} ⊆
            {ω | ∃ o st' c, Runs w p ω s₁ st o st' c ∧ o = .normal ∧ M st a st' c} := by
        intro ω hsome
        rcases Option.isSome_iff_exists.mp hsome with ⟨⟨q, res⟩, hqres⟩
        obtain ⟨_, hrun₁, hm⟩ := normalStepPrefix_some hqres
        exact ⟨.normal, res.1, res.2, hrun₁, rfl, hm⟩
      exact le_trans (measure_mono hsub_pref) (hs₁ st hP a)
    calc
      coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
          Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
            Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂}
        ≤ coins {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res} := measure_mono hsub_τ
      _ ≤ coins {ω | (τ ω).isSome} * κ st a b :=
          coins_fresh_bits_mul τ hτ E hE_dep hE_prob
      _ ≤ μ₁ st a * κ st a b := mul_le_mul_left hτ_le (κ st a b)
  calc
    coins {ω | ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ R st b o st' c}
      ≤ coins (⋃ a : α, {ω | ∃ st₁ c₁ c₂ o₂ st₂,
          Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
            Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂}) := measure_mono hsub_union
    _ ≤ ∑' a : α, coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
          Runs w p ω s₁ st .normal st₁ c₁ ∧ M st a st₁ c₁ ∧
            Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} := measure_iUnion_le _
    _ ≤ ∑' a : α, μ₁ st a * κ st a b := ENNReal.tsum_le_tsum hstep
    _ = ((μ₁ st).bind (κ st)) b := by rw [PMF.bind_apply]

/-- Convenience form of `SubLaw.seq_bind` when early returns of `s₁` cannot witness `R`
(for example when `R` holds only for `.normal` termination or a return sentinel distinct from any
early abort of `s₁`). -/
theorem SubLaw.seq_normal_bind {w : ℕ} {p : Program} {s₁ s₂ : Stmt} {α β : Type*} [Countable α]
    {P₁ : State → Prop}
    {M : State → α → State → ℕ → Prop}
    {R₂ : State → β → Outcome → State → ℕ → Prop}
    {R : State → β → Outcome → State → ℕ → Prop}
    {μ₁ : State → PMF α} {κ : State → α → PMF β}
    (hs₁ : SubLaw w p s₁ P₁ (fun st a o st₁ c₁ => o = .normal ∧ M st a st₁ c₁) μ₁)
    (hs₂ : ∀ st a st₁ c₁, P₁ st → M st a st₁ c₁ → ∀ b : β,
      coins {ω | ∃ o₂ st₂ c₂, Runs w p ω s₂ st₁ o₂ st₂ c₂ ∧ R₂ st₁ b o₂ st₂ c₂} ≤ κ st a b)
    (hno_ret : ∀ ω st v st' c₁ b, P₁ st →
      Runs w p ω s₁ st (.returned v) st' c₁ → ¬ R st b (.returned v) st' (c₁ + 1))
    (hjoin : ∀ ω st o st' c b st₁ c₁ c₂, P₁ st →
      Runs w p ω s₁ st .normal st₁ c₁ → Runs w p ω s₂ st₁ o st' c₂ →
      c = c₁ + c₂ + 1 → R st b o st' c →
      ∃ a, M st a st₁ c₁ ∧ R₂ st₁ b o st' c₂) :
    SubLaw w p (.seq s₁ s₂) P₁ R (fun st => (μ₁ st).bind (κ st)) := by
  refine SubLaw.seq_bind hs₁ hs₂ ?_
  intro ω st o st' c b hP hrun hr
  rcases runs_seq_iff.mp hrun with
      ⟨v, c₁, hret₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hrun₁, hrun₂, rfl⟩
  · exact False.elim (hno_ret ω st v st' c₁ b hP hret₁ hr)
  · obtain ⟨a, hm, hr₂⟩ := hjoin ω st o st' (c₁ + c₂ + 1) b st₁ c₁ c₂ hP hrun₁ hrun₂ rfl hr
    exact ⟨st₁, c₁, c₂, a, hrun₁, hm, hrun₂, rfl, hr₂⟩

/-- Sequential composition where `s₂` preserves/transforms a value from `s₁` into `(μ₁ st).map (f st)`. -/
theorem SubLaw.seq_map {w : ℕ} {p : Program} {s₁ s₂ : Stmt} {α β : Type*} [Countable α]
    {P₁ : State → Prop}
    {M : State → α → State → ℕ → Prop}
    {R : State → β → Outcome → State → ℕ → Prop}
    {μ₁ : State → PMF α} (f : State → α → β)
    (hs₁ : SubLaw w p s₁ P₁ (fun st a o st₁ c₁ => o = .normal ∧ M st a st₁ c₁) μ₁)
    (hno_ret : ∀ ω st v st' c₁ b, P₁ st →
      Runs w p ω s₁ st (.returned v) st' c₁ → ¬ R st b (.returned v) st' (c₁ + 1))
    (hjoin : ∀ ω st o st' c b st₁ c₁ c₂, P₁ st →
      Runs w p ω s₁ st .normal st₁ c₁ → Runs w p ω s₂ st₁ o st' c₂ →
      c = c₁ + c₂ + 1 → R st b o st' c → ∃ a, M st a st₁ c₁ ∧ b = f st a) :
    SubLaw w p (.seq s₁ s₂) P₁ R (fun st => (μ₁ st).map (f st)) := by
  intro st hP b
  have hsub :
      {ω | ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ R st b o st' c} ⊆
        {ω | ∃ a ∈ f st ⁻¹' {b}, ∃ o st₁ c₁,
          Runs w p ω s₁ st o st₁ c₁ ∧ o = .normal ∧ M st a st₁ c₁} := by
    rintro ω ⟨o, st', c, hrun, hr⟩
    rcases runs_seq_iff.mp hrun with
        ⟨v, c₁, hret₁, rfl, rfl⟩ | ⟨st₁, c₁, c₂, hrun₁, hrun₂, rfl⟩
    · exact False.elim (hno_ret ω st v st' c₁ b hP hret₁ hr)
    · obtain ⟨a, hm, hfab⟩ := hjoin ω st o st' (c₁ + c₂ + 1) b st₁ c₁ c₂ hP hrun₁ hrun₂ rfl hr
      exact ⟨a, hfab.symm, .normal, st₁, c₁, hrun₁, rfl, hm⟩
  calc
    coins {ω | ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ R st b o st' c}
      ≤ coins {ω | ∃ a ∈ f st ⁻¹' {b}, ∃ o st₁ c₁,
          Runs w p ω s₁ st o st₁ c₁ ∧ o = .normal ∧ M st a st₁ c₁} := measure_mono hsub
    _ ≤ (μ₁ st).toOuterMeasure (f st ⁻¹' {b}) := hs₁.toOuterMeasure_le hP (f st ⁻¹' {b})
    _ = ((μ₁ st).map (f st)) b := by
        rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]

/-- General well-founded loop rule for `SubLaw`: if `Inv g st` tracks an abstract state `g : γ`
with decreasing metric `wf g`, single steps of `body` stay in `stepPMF g`, and `(stepPMF g).bind Law ≤ Law g`
at active states, then `Stmt.loop e body` satisfies `SubLaw` with respect to `Law g`. -/
theorem SubLaw.loop_rec {w : ℕ} {p : Program} {e : Expr} {body : Stmt} {γ α : Type*} [Countable γ]
    {Inv : γ → State → Prop} {wf : γ → ℕ}
    {M : γ → State → γ → State → ℕ → Prop}
    {R : State → α → Outcome → State → ℕ → Prop}
    {stepPMF : γ → PMF γ} {Law : γ → PMF α}
    (heval : ∀ g st, Inv g st → ∃ v, e.eval w st = some v)
    (hdone : ∀ g st a, Inv g st → e.eval w st = some 0 →
      R st a .normal st (e.size + 1) → (1 : ENNReal) ≤ Law g a)
    (hstep_wf : ∀ g g', (∃ st, Inv g st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0) →
      g' ∈ (stepPMF g).support → wf g' < wf g)
    (hstep_inv : ∀ g st g' st₁ c₁, Inv g st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      M g st g' st₁ c₁ → Inv g' st₁)
    (hbody : ∀ g st, Inv g st → (∃ v, e.eval w st = some v ∧ v ≠ 0) → ∀ g',
      coins {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁} ≤ stepPMF g g')
    (hno_ret : ∀ ω g st u st₁ c₁ a, Inv g st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      Runs w p ω body st (.returned u) st₁ c₁ → ¬ R st a (.returned u) st₁ (e.size + c₁ + 1))
    (hjoin : ∀ ω g st o st' a st₁ c₁ c₂, Inv g st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      Runs w p ω body st .normal st₁ c₁ → Runs w p ω (.loop e body) st₁ o st' c₂ →
      R st a o st' (e.size + c₁ + c₂ + 1) →
      ∃ g', M g st g' st₁ c₁ ∧ R st₁ a o st' c₂)
    (hlaw : ∀ g, (∃ st, Inv g st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0) →
      ∀ a : α, ((stepPMF g).bind Law) a ≤ Law g a) :
    ∀ g st, Inv g st → ∀ a : α,
      coins {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st a o st' c} ≤ Law g a := by
  have hmain : ∀ n g st, wf g = n → Inv g st → ∀ a : α,
      coins {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st a o st' c} ≤ Law g a := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rintro g st rfl hInv a
      obtain ⟨v, hv⟩ := heval g st hInv
      by_cases hv0 : v = 0
      · subst hv0
        by_cases hR : R st a .normal st (e.size + 1)
        · have hle1 : coins {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧
              R st a o st' c} ≤ 1 :=
            (measure_mono (Set.subset_univ _ : _ ⊆ Set.univ)).trans_eq measure_univ
          exact le_trans hle1 (hdone g st a hInv hv hR)
        · have hempty :
              {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st a o st' c} = ∅ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
            intro o st' c hrun hr
            rcases runs_loop_iff.mp hrun with
                ⟨_, rfl, rfl, rfl⟩ | ⟨v', u, c₁, hv', hv'0, _⟩ | ⟨v', st₁, c₁, c₂, hv', hv'0, _⟩
            · exact hR hr
            · rw [hv] at hv'; cases hv'; exact hv'0 rfl
            · rw [hv] at hv'; cases hv'; exact hv'0 rfl
          simp [hempty]
      · have hsub_union :
            {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st a o st' c} ⊆
              ⋃ g' : γ, {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                  Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂} := by
          rintro ω ⟨o, st', c, hrun, hr⟩
          rcases runs_loop_iff.mp hrun with
              ⟨hv', _⟩ | ⟨v', u, c₁, hv', _, hret₁, rfl, rfl⟩ |
              ⟨v', st₁, c₁, c₂, hv', _, hbody₁, hloop₂, rfl⟩
          · rw [hv] at hv'; cases hv'; exact False.elim (hv0 rfl)
          · exact False.elim (hno_ret ω g st u st' c₁ a hInv ⟨v, hv, hv0⟩ hret₁ hr)
          · obtain ⟨g', hm, hr₂⟩ :=
              hjoin ω g st o st' a st₁ c₁ c₂ hInv ⟨v, hv, hv0⟩ hbody₁ hloop₂ hr
            exact Set.mem_iUnion.mpr ⟨g', st₁, c₁, c₂, o, st', hbody₁, hm, hloop₂, hr₂⟩
        have hstep_g : ∀ g' : γ,
            coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
              Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂} ≤
              stepPMF g g' * Law g' a := by
          intro g'
          by_cases hsupp : g' ∈ (stepPMF g).support
          · let τ := normalStepPrefix w p body st (M g st g')
            let E : ℕ → State × ℕ → Set (ℕ → Bool) := fun q res =>
              {ω | q ≤ res.1.pos ∧
                ∃ o₂ st₂ c₂, Runs w p ω (.loop e body) res.1 o₂ st₂ c₂ ∧ R res.1 a o₂ st₂ c₂}
            have hτ : PrefixDetermined τ :=
              prefixDetermined_normalStepPrefix w p body st (M g st g')
            have hE_dep : ∀ q res, DependsOn (E q res) {i | q ≤ i} :=
              fun q res => tailSucc_dependsOn w p (.loop e body) q res.1
                fun o₂ st₂ c₂ => R res.1 a o₂ st₂ c₂
            have hE_prob : ∀ ω q res, τ ω = some (q, res) → coins (E q res) ≤ Law g' a := by
              intro ω q res hτ_ω
              obtain ⟨_, _, hm⟩ := normalStepPrefix_some hτ_ω
              have hInv' := hstep_inv g st g' res.1 res.2 hInv ⟨v, hv, hv0⟩ hm
              have hsub : E q res ⊆
                  {ω' | ∃ o₂ st₂ c₂,
                    Runs w p ω' (.loop e body) res.1 o₂ st₂ c₂ ∧ R res.1 a o₂ st₂ c₂} :=
                fun _ hmem => hmem.2
              exact le_trans (measure_mono hsub)
                (ih (wf g') (hstep_wf g g' ⟨st, hInv, v, hv, hv0⟩ hsupp) g' res.1 rfl hInv' a)
            have hsub_τ :
                {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                  Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                    Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂} ⊆
                  {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res} := by
              rintro ω ⟨st₁, c₁, c₂, o₂, st₂, hbody₁, hm, hloop₂, hr₂⟩
              exact ⟨st₁.pos, (st₁, c₁), normalStepPrefix_spec hbody₁ hm,
                le_rfl, o₂, st₂, c₂, hloop₂, hr₂⟩
            have hτ_le : coins {ω | (τ ω).isSome} ≤ stepPMF g g' := by
              have hsub_pref :
                  {ω | (τ ω).isSome} ⊆
                    {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁} := by
                intro ω hsome
                rcases Option.isSome_iff_exists.mp hsome with ⟨⟨q, res⟩, hqres⟩
                obtain ⟨_, hbody₁, hm⟩ := normalStepPrefix_some hqres
                exact ⟨res.1, res.2, hbody₁, hm⟩
              exact le_trans (measure_mono hsub_pref) (hbody g st hInv ⟨v, hv, hv0⟩ g')
            calc
              coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                  Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                    Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂}
                ≤ coins {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res} := measure_mono hsub_τ
              _ ≤ coins {ω | (τ ω).isSome} * Law g' a :=
                  coins_fresh_bits_mul τ hτ E hE_dep hE_prob
              _ ≤ stepPMF g g' * Law g' a := mul_le_mul_left hτ_le (Law g' a)
          · have hzero : stepPMF g g' = 0 := (PMF.apply_eq_zero_iff (stepPMF g) g').mpr hsupp
            have hsub0 :
                {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                  Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                    Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂} ⊆
                  {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁} := by
              rintro ω ⟨st₁, c₁, _, _, _, hbody₁, hm, _⟩
              exact ⟨st₁, c₁, hbody₁, hm⟩
            have hle0 := le_trans (measure_mono hsub0) (hbody g st hInv ⟨v, hv, hv0⟩ g')
            simpa [hzero] using hle0
        calc
          coins {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st a o st' c}
            ≤ coins (⋃ g' : γ, {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                  Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂}) :=
                measure_mono hsub_union
          _ ≤ ∑' g' : γ, coins {ω | ∃ st₁ c₁ c₂ o₂ st₂,
                Runs w p ω body st .normal st₁ c₁ ∧ M g st g' st₁ c₁ ∧
                  Runs w p ω (.loop e body) st₁ o₂ st₂ c₂ ∧ R st₁ a o₂ st₂ c₂} :=
                measure_iUnion_le _
          _ ≤ ∑' g' : γ, stepPMF g g' * Law g' a := ENNReal.tsum_le_tsum hstep_g
          _ = ((stepPMF g).bind Law) a := by rw [PMF.bind_apply]
          _ ≤ Law g a := hlaw g ⟨st, hInv, v, hv, hv0⟩ a
  exact fun g st hInv a => hmain (wf g) g st rfl hInv a

/-- Pure `PMF.bind` fold along a list `xs : List ι` from initial value `init : α`. -/
@[expose]
noncomputable def listBindM {α ι : Type*} (step : α → ι → PMF α) : α → List ι → PMF α
  | a, [] => PMF.pure a
  | a, x :: xs => (step a x).bind fun a' => listBindM step a' xs

/-- List-indexed `SubLaw` loop rule: when invariant `Inv a xs st` unfolds step-by-step along
`x :: xs` via `step a x : PMF α`, `Stmt.loop e body` satisfies `SubLaw` wrt `listBindM step a xs`. -/
theorem SubLaw.loop_fold {w : ℕ} {p : Program} {e : Expr} {body : Stmt} {α ι : Type*}
    [Countable α] [Countable ι]
    {Inv : α → List ι → State → Prop}
    {M : State → α → State → ℕ → Prop}
    {R : State → α → Outcome → State → ℕ → Prop}
    {step : α → ι → PMF α}
    (heval : ∀ a xs st, Inv a xs st → ∃ v, e.eval w st = some v)
    (hzero : ∀ a st, Inv a [] st → e.eval w st = some 0)
    (hdone : ∀ a xs st b, Inv a xs st → e.eval w st = some 0 →
      R st b .normal st (e.size + 1) → xs = [] ∧ b = a)
    (hstep_inv : ∀ a x xs st a' st₁ c₁, Inv a (x :: xs) st →
      (∃ v, e.eval w st = some v ∧ v ≠ 0) → M st a' st₁ c₁ → Inv a' xs st₁)
    (hbody : ∀ a x xs st, Inv a (x :: xs) st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      ∀ a', coins {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ M st a' st₁ c₁} ≤ step a x a')
    (hno_ret : ∀ ω a xs st u st₁ c₁ b, Inv a xs st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      Runs w p ω body st (.returned u) st₁ c₁ → ¬ R st b (.returned u) st₁ (e.size + c₁ + 1))
    (hjoin : ∀ ω a x xs st o st' b st₁ c₁ c₂, Inv a (x :: xs) st →
      (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      Runs w p ω body st .normal st₁ c₁ → Runs w p ω (.loop e body) st₁ o st' c₂ →
      R st b o st' (e.size + c₁ + c₂ + 1) →
      ∃ a', M st a' st₁ c₁ ∧ R st₁ b o st' c₂) :
    ∀ a xs st, Inv a xs st → ∀ b : α,
      coins {ω | ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ R st b o st' c} ≤
        listBindM step a xs b := by
  let Inv' : α × List ι → State → Prop := fun g st => Inv g.1 g.2 st
  let wf : α × List ι → ℕ := fun g => g.2.length
  let M' : α × List ι → State → α × List ι → State → ℕ → Prop := fun g st g' st₁ c₁ =>
    g'.2 = g.2.tail ∧ M st g'.1 st₁ c₁
  let stepPMF : α × List ι → PMF (α × List ι) := fun g =>
    match g.2 with
    | [] => PMF.pure g
    | x :: xs => (step g.1 x).map fun a' => (a', xs)
  let Law : α × List ι → PMF α := fun g => listBindM step g.1 g.2
  have hrec := SubLaw.loop_rec (w := w) (p := p) (e := e) (body := body)
    (Inv := Inv') (wf := wf) (M := M') (R := R) (stepPMF := stepPMF) (Law := Law)
    (fun g st hg => heval g.1 g.2 st hg)
    (fun g st b hg h0 hr => by
      obtain ⟨hxs, rfl⟩ := hdone g.1 g.2 st b hg h0 hr
      simp [Law, hxs, listBindM])
    (fun g g' ⟨st, hg, v, hv, hv0⟩ hsupp => by
      rcases g with ⟨a, xs⟩
      cases xs with
      | nil =>
        rw [hzero a st hg] at hv
        injection hv with hveq
        exact False.elim (hv0 hveq.symm)
      | cons x xs' =>
        simp only [stepPMF, PMF.support_map, Set.mem_image] at hsupp
        rcases hsupp with ⟨a', _, rfl⟩
        simp [wf])
    (fun g st g' st₁ c₁ hg hv ⟨htail, hm⟩ => by
      rcases g with ⟨a, xs⟩
      rcases g' with ⟨a', ys⟩
      cases xs with
      | nil =>
        obtain ⟨v, hv', hv0'⟩ := hv
        rw [hzero a st hg] at hv'
        injection hv' with hveq
        exact False.elim (hv0' hveq.symm)
      | cons x xs' =>
        dsimp only at htail
        rcases htail with rfl
        exact hstep_inv a x ys st a' st₁ c₁ hg hv hm)
    (fun g st hg ⟨v, hv, hv0⟩ g' => by
      rcases g with ⟨a, xs⟩
      cases xs with
      | nil =>
        rw [hzero a st hg] at hv
        injection hv with hveq
        exact False.elim (hv0 hveq.symm)
      | cons x xs' =>
        rcases g' with ⟨a', ys⟩
        by_cases hys : ys = xs'
        · subst hys
          have hsub :
              {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧
                  M' (a, x :: ys) st (a', ys) st₁ c₁} ⊆
                {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧ M st a' st₁ c₁} := by
            rintro ω ⟨st₁, c₁, hrun, _, hm⟩
            exact ⟨st₁, c₁, hrun, hm⟩
          have hpmf : stepPMF (a, x :: ys) (a', ys) = step a x a' := by
            dsimp only [stepPMF]
            rw [PMF.map_apply, tsum_eq_single a']
            · simp
            · intro y hy
              simp [Ne.symm hy]
          rw [hpmf]
          exact le_trans (measure_mono hsub) (hbody a x ys st hg ⟨v, hv, hv0⟩ a')
        · have hempty :
              {ω | ∃ st₁ c₁, Runs w p ω body st .normal st₁ c₁ ∧
                  M' (a, x :: xs') st (a', ys) st₁ c₁} = ∅ := by
            ext ω
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
            intro st₁ c₁ _ ⟨htail, _⟩
            exact hys htail
          simp [hempty])
    (fun ω g st u st₁ c₁ b hg hv => hno_ret ω g.1 g.2 st u st₁ c₁ b hg hv)
    (fun ω g st o st' b st₁ c₁ c₂ hg hv hbody₁ hloop₂ hr => by
      rcases g with ⟨a, xs⟩
      cases xs with
      | nil =>
        obtain ⟨v, hv', hv0'⟩ := hv
        rw [hzero a st hg] at hv'
        injection hv' with hveq
        exact False.elim (hv0' hveq.symm)
      | cons x xs' =>
        obtain ⟨a', hm, hr₂⟩ :=
          hjoin ω a x xs' st o st' b st₁ c₁ c₂ hg hv hbody₁ hloop₂ hr
        exact ⟨(a', xs'), ⟨rfl, hm⟩, hr₂⟩)
    (fun g ⟨st, hg, v, hv, hv0⟩ b => by
      rcases g with ⟨a, xs⟩
      cases xs with
      | nil =>
        rw [hzero a st hg] at hv
        injection hv with hveq
        exact False.elim (hv0 hveq.symm)
      | cons x xs' =>
        simp [stepPMF, Law, listBindM, PMF.bind_map, Function.comp_def])
  intro a xs st hInv b
  exact hrec (a, xs) st hInv b

end WordRAM
