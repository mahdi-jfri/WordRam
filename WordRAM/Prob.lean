module

public import WordRAM.CoinsFresh
public import WordRAM.ProbRuns
import WordRAM.Exec

/-!
# Compositional rules for probabilistic contracts and runs

Rules for composing randomized machine programs and bounding failure probabilities under `coins`:

* `MeetsContract.toProbContract`: any deterministic `MeetsContract` gives a `MeetsProbContract`
  with failure probability `0`.
* `ProbTriple`: Hoare-style probabilistic specification
  `∀ st, P st → coins {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' c} ≤ δ`.
* `MeetsProbContract.of_probTriple`: bridges `ProbTriple` on procedure bodies to
  `MeetsProbContract`.
* `ProbTriple.seq`, `ProbTriple.seq_normal`: sequential composition adds failure bounds (`δ₁ + δ₂`)
  using the fresh-bits lemma (`coins_fresh_bits`) and run locality (`Runs.congr_bits`).
* `runs_call_of_meetsProbContract`, `ProbTriple.call`, `ProbTriple.call_seq`: procedure calls using
  a callee's `MeetsProbContract`, standalone or sequentially composed.
* `ProbTriple.cond`: conditional branching with error `max δ₁ δ₂`.
* `ProbTriple.loop`, `ProbTriple.loop_bound`: bounded-iteration loops with error `T * δ`.
-/

public section

namespace WordRAM

open MeasureTheory

/-- Any deterministic contract holds with failure probability `0`. -/
theorem MeetsContract.toProbContract {w : ℕ} {p : Program} {f : ℕ} {C : Contract}
    (h : MeetsContract w p f C) :
    MeetsProbContract w p f C (fun _ _ => 0) := by
  intro args mem pos hwords hpre
  have hempty : {ω | ¬ EndsAsContract w p f C args mem pos ω} = ∅ := by
    ext ω
    simp [h args mem pos ω hwords hpre]
  rw [hempty, measure_empty]

/-- Weakening the failure bound of a `MeetsProbContract`. -/
theorem MeetsProbContract.mono {w : ℕ} {p : Program} {f : ℕ} {C : Contract}
    {δ₁ δ₂ : List ℕ → (ℕ → ℕ) → ENNReal}
    (h : MeetsProbContract w p f C δ₁)
    (hle : ∀ args mem, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem → δ₁ args mem ≤ δ₂ args mem) :
    MeetsProbContract w p f C δ₂ :=
  fun args mem pos hwords hpre =>
    le_trans (h args mem pos hwords hpre) (hle args mem hwords hpre)

/-- A probabilistic Hoare-style specification for statement `s` at word size `w` and program `p`:
starting from any state `st` satisfying `P st`, a run fails to terminate cleanly with `Q st` with
probability at most `δ`. Because `P` holds across bit-stream positions, this composes sequentially
and across loops. -/
@[expose]
def ProbTriple (w : ℕ) (p : Program) (s : Stmt)
    (P : State → Prop) (Q : State → Outcome → State → ℕ → Prop) (δ : ENNReal) : Prop :=
  ∀ st, P st → coins {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' c} ≤ δ

/-- Strengthening the precondition, weakening the postcondition, and relaxing the failure bound
of a `ProbTriple`. -/
theorem ProbTriple.conseq {w : ℕ} {p : Program} {s : Stmt}
    {P P' : State → Prop} {Q Q' : State → Outcome → State → ℕ → Prop} {δ δ' : ENNReal}
    (hs : ProbTriple w p s P Q δ)
    (hP : ∀ st, P' st → P st)
    (hQ : ∀ st o st' c, P' st → Q st o st' c → Q' st o st' c)
    (hδ : δ ≤ δ') :
    ProbTriple w p s P' Q' δ' := by
  intro st hP'
  have hsub :
      {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q' st o st' c} ⊆
        {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' c} := by
    intro ω hnot ⟨o, st', c, hrun, hq⟩
    exact hnot ⟨o, st', c, hrun, hQ st o st' c hP' hq⟩
  exact le_trans (measure_mono hsub) (le_trans (hs st (hP st hP')) hδ)

/-- Every deterministic run guarantee gives a `ProbTriple` with failure probability `0`. -/
theorem ProbTriple.of_runs {w : ℕ} {p : Program} {s : Stmt}
    {P : State → Prop} {Q : State → Outcome → State → ℕ → Prop}
    (h : ∀ st ω, P st → ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' c) :
    ProbTriple w p s P Q 0 := by
  intro st hP
  have hempty : {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' c} = ∅ := by
    ext ω
    simp [h st ω hP]
  rw [hempty, measure_empty]

/-- Conjoin two postconditions on the same statement; failure probabilities add via `Runs.det`. -/
theorem ProbTriple.and {w : ℕ} {p : Program} {s : Stmt}
    {P : State → Prop} {Q₁ Q₂ : State → Outcome → State → ℕ → Prop} {δ₁ δ₂ : ENNReal}
    (h₁ : ProbTriple w p s P Q₁ δ₁) (h₂ : ProbTriple w p s P Q₂ δ₂) :
    ProbTriple w p s P (fun st o st' c => Q₁ st o st' c ∧ Q₂ st o st' c) (δ₁ + δ₂) := by
  intro st hP
  let B₁ : Set (ℕ → Bool) := {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q₁ st o st' c}
  let B₂ : Set (ℕ → Bool) := {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q₂ st o st' c}
  have hsub :
      {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q₁ st o st' c ∧ Q₂ st o st' c} ⊆ B₁ ∪ B₂ := by
    intro ω hnot
    by_cases hω₁ : ∃ o₁ st₁ c₁, Runs w p ω s st o₁ st₁ c₁ ∧ Q₁ st o₁ st₁ c₁
    · by_cases hω₂ : ∃ o₂ st₂ c₂, Runs w p ω s st o₂ st₂ c₂ ∧ Q₂ st o₂ st₂ c₂
      · exfalso
        rcases hω₁ with ⟨o₁, st₁, c₁, hrun₁, hq₁⟩
        rcases hω₂ with ⟨o₂, st₂, c₂, hrun₂, hq₂⟩
        rcases hrun₁.det hrun₂ with ⟨rfl, rfl, rfl⟩
        exact hnot ⟨o₁, st₁, c₁, hrun₁, hq₁, hq₂⟩
      · exact Or.inr hω₂
    · exact Or.inl hω₁
  calc
    coins {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q₁ st o st' c ∧ Q₂ st o st' c}
      ≤ coins (B₁ ∪ B₂) := measure_mono hsub
    _ ≤ coins B₁ + coins B₂ := measure_union_le B₁ B₂
    _ ≤ δ₁ + δ₂ := add_le_add (h₁ st hP) (h₂ st hP)

/-- Derive a `MeetsProbContract` for procedure `f` from a `ProbTriple` on its body. -/
theorem MeetsProbContract.of_probTriple {w : ℕ} {p : Program} {f : ℕ}
    {C : Contract} {δ : List ℕ → (ℕ → ℕ) → ENNReal} {body : Stmt}
    (hproc : p.procs[f]? = some body)
    (htriple : ∀ args mem, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem →
      ProbTriple w p body (fun st => st.mem = mem ∧ st.regs = fun i => args.getD i 0)
        (fun _ o st' c => C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem)
        (δ args mem)) :
    MeetsProbContract w p f C δ := by
  intro args mem pos hwords hpre
  have hst := htriple args mem hwords hpre (startState args mem pos) ⟨rfl, rfl⟩
  have hsub :
      {ω | ¬ EndsAsContract w p f C args mem pos ω} ⊆
        {ω | ¬ ∃ o st' c, Runs w p ω body (startState args mem pos) o st' c ∧
          C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem} := by
    intro ω hnot ⟨o, st', c, hrun, hpost, hcost⟩
    exact hnot ⟨body, hproc, o, st', c, hrun, hpost, hcost⟩
  exact le_trans (measure_mono hsub) hst

private noncomputable def normalRunPrefix (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (M : State → ℕ → Prop) (ω : ℕ → Bool) : Option (ℕ × (State × ℕ)) := by
  classical
  exact if h : ∃ res : State × ℕ, Runs w p ω s st .normal res.1 res.2 ∧ M res.1 res.2 then
    let res := Classical.choose h
    some (res.1.pos, res)
  else none

private theorem normalRunPrefix_some {w : ℕ} {p : Program} {s : Stmt} {st : State}
    {M : State → ℕ → Prop} {ω : ℕ → Bool} {q : ℕ} {res : State × ℕ}
    (hω : normalRunPrefix w p s st M ω = some (q, res)) :
    q = res.1.pos ∧ Runs w p ω s st .normal res.1 res.2 ∧ M res.1 res.2 := by
  classical
  rw [normalRunPrefix] at hω
  split_ifs at hω with h
  simp only [Option.some.injEq, Prod.mk.injEq] at hω
  rcases hω with ⟨rfl, rfl⟩
  exact ⟨rfl, Classical.choose_spec h⟩

private theorem prefixDetermined_normalRunPrefix (w : ℕ) (p : Program) (s : Stmt) (st : State)
    (M : State → ℕ → Prop) :
    PrefixDetermined (normalRunPrefix w p s st M) := by
  classical
  intro ω ω' q res hω heq
  obtain ⟨hq, hrun, hM⟩ := normalRunPrefix_some hω
  have hrun' : Runs w p ω' s st .normal res.1 res.2 :=
    hrun.congr_bits fun i _ hi₂ => heq i (hq ▸ hi₂)
  rw [normalRunPrefix]
  split_ifs with hcond
  · let res₁ := Classical.choose hcond
    have hspec₁ := Classical.choose_spec hcond
    rcases hspec₁.1.det hrun' with ⟨_, hst_eq, hc_eq⟩
    simp [hst_eq, hc_eq, hq, Prod.ext_iff]
  · exact False.elim (hcond ⟨res, hrun', hM⟩)

private theorem normalRunPrefix_spec {w : ℕ} {p : Program} {s : Stmt} {st : State}
    {M : State → ℕ → Prop} {ω : ℕ → Bool} {st₁ : State} {c₁ : ℕ}
    (hrun : Runs w p ω s st .normal st₁ c₁) (hM : M st₁ c₁) :
    normalRunPrefix w p s st M ω = some (st₁.pos, (st₁, c₁)) := by
  classical
  rw [normalRunPrefix]
  split_ifs with h
  · let res₁ := Classical.choose h
    have hspec₁ := Classical.choose_spec h
    rcases hspec₁.1.det hrun with ⟨_, hst_eq, hc_eq⟩
    simp [hst_eq, hc_eq, Prod.ext_iff]
  · exact False.elim (h ⟨(st₁, c₁), hrun, hM⟩)

private theorem tailRunFail_dependsOn (w : ℕ) (p : Program) (u : Stmt)
    (q : ℕ) (st₁ : State) (Q : Outcome → State → ℕ → Prop) :
    DependsOn {ω | q ≤ st₁.pos ∧ ¬ ∃ o₂ st₂ c₂, Runs w p ω u st₁ o₂ st₂ c₂ ∧ Q o₂ st₂ c₂}
      {i | q ≤ i} := by
  intro ω₁ ω₂ heq
  apply propext
  constructor
  · rintro ⟨hq, hnot⟩
    refine ⟨hq, fun ⟨o₂, st₂, c₂, hrun, hq₂⟩ => hnot ?_⟩
    exact ⟨o₂, st₂, c₂, hrun.congr_bits_ge fun i hi => heq i (le_trans hq hi), hq₂⟩
  · rintro ⟨hq, hnot⟩
    refine ⟨hq, fun ⟨o₂, st₂, c₂, hrun, hq₂⟩ => hnot ?_⟩
    exact ⟨o₂, st₂, c₂, hrun.congr_bits_ge fun i hi => (heq i (le_trans hq hi)).symm, hq₂⟩

/-- Sequential composition of probabilistic triples: the failure probabilities add (`δ₁ + δ₂`).
Handles both early return from `s` and normal transition from `s` into `t`. -/
theorem ProbTriple.seq {w : ℕ} {p : Program} {s t : Stmt}
    {P : State → Prop} {Q₁ : State → Outcome → State → ℕ → Prop}
    {Q : State → Outcome → State → ℕ → Prop} {δ₁ δ₂ : ENNReal}
    (hs : ProbTriple w p s P Q₁ δ₁)
    (hret : ∀ st v st₁ c₁, P st → Q₁ st (.returned v) st₁ c₁ →
      Q st (.returned v) st₁ (c₁ + 1))
    (ht : ∀ st st₁ c₁, P st → Q₁ st .normal st₁ c₁ →
      ProbTriple w p t (fun st' => st' = st₁)
        (fun _ o₂ st₂ c₂ => Q st o₂ st₂ (c₁ + c₂ + 1)) δ₂) :
    ProbTriple w p (.seq s t) P Q (δ₁ + δ₂) := by
  intro st hP
  let τ := normalRunPrefix w p s st (fun st₁ c₁ => Q₁ st .normal st₁ c₁)
  let E : ℕ → State × ℕ → Set (ℕ → Bool) := fun q res =>
    {ω | q ≤ res.1.pos ∧
      ¬ ∃ o₂ st₂ c₂, Runs w p ω t res.1 o₂ st₂ c₂ ∧ Q st o₂ st₂ (res.2 + c₂ + 1)}
  have hτ : PrefixDetermined τ :=
    prefixDetermined_normalRunPrefix w p s st (fun st₁ c₁ => Q₁ st .normal st₁ c₁)
  have hE_dep : ∀ q res, DependsOn (E q res) {i | q ≤ i} :=
    fun q res => tailRunFail_dependsOn w p t q res.1 fun o₂ st₂ c₂ => Q st o₂ st₂ (res.2 + c₂ + 1)
  have hE_prob : ∀ ω q res, τ ω = some (q, res) → coins (E q res) ≤ δ₂ := by
    intro ω q res hτ_ω
    obtain ⟨_, _, hq₁⟩ := normalRunPrefix_some hτ_ω
    have hsub : E q res ⊆
        {ω' | ¬ ∃ o₂ st₂ c₂, Runs w p ω' t res.1 o₂ st₂ c₂ ∧ Q st o₂ st₂ (res.2 + c₂ + 1)} :=
      fun _ hmem => hmem.2
    exact le_trans (measure_mono hsub) (ht st res.1 res.2 hP hq₁ res.1 rfl)
  let B₁ : Set (ℕ → Bool) := {ω | ¬ ∃ o₁ st₁ c₁, Runs w p ω s st o₁ st₁ c₁ ∧ Q₁ st o₁ st₁ c₁}
  let B₂ : Set (ℕ → Bool) := {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res}
  have hsub : {ω | ¬ ∃ o st' c, Runs w p ω (.seq s t) st o st' c ∧ Q st o st' c} ⊆ B₁ ∪ B₂ := by
    intro ω hnot
    by_cases h₁ : ∃ o₁ st₁ c₁, Runs w p ω s st o₁ st₁ c₁ ∧ Q₁ st o₁ st₁ c₁
    · rcases h₁ with ⟨o₁, st₁, c₁, hrun₁, hq₁⟩
      cases o₁ with
      | returned v =>
        exfalso
        exact hnot ⟨.returned v, st₁, c₁ + 1,
          runs_seq_iff.mpr (Or.inl ⟨v, c₁, hrun₁, rfl, rfl⟩), hret st v st₁ c₁ hP hq₁⟩
      | normal =>
        refine Or.inr ⟨st₁.pos, (st₁, c₁), normalRunPrefix_spec hrun₁ hq₁, le_rfl, ?_⟩
        intro ⟨o₂, st₂, c₂, hrun₂, hq₂⟩
        exact hnot ⟨o₂, st₂, c₁ + c₂ + 1,
          runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, hrun₁, hrun₂, rfl⟩), hq₂⟩
    · exact Or.inl h₁
  calc
    coins {ω | ¬ ∃ o st' c, Runs w p ω (.seq s t) st o st' c ∧ Q st o st' c}
      ≤ coins (B₁ ∪ B₂) := measure_mono hsub
    _ ≤ coins B₁ + coins B₂ := measure_union_le B₁ B₂
    _ ≤ δ₁ + δ₂ := add_le_add (hs st hP) (coins_fresh_bits τ hτ E hE_dep hE_prob)

/-- Sequential composition when the first statement always completes with `.normal`. -/
theorem ProbTriple.seq_normal {w : ℕ} {p : Program} {s t : Stmt}
    {P : State → Prop} {M : State → State → ℕ → Prop}
    {Q : State → Outcome → State → ℕ → Prop} {δ₁ δ₂ : ENNReal}
    (hs : ProbTriple w p s P (fun st o st₁ c₁ => o = .normal ∧ M st st₁ c₁) δ₁)
    (ht : ∀ st st₁ c₁, P st → M st st₁ c₁ →
      ProbTriple w p t (fun st' => st' = st₁)
        (fun _ o₂ st₂ c₂ => Q st o₂ st₂ (c₁ + c₂ + 1)) δ₂) :
    ProbTriple w p (.seq s t) P Q (δ₁ + δ₂) :=
  ProbTriple.seq hs
    (fun _ _ _ _ _ ⟨h, _⟩ => by cases h)
    (fun st st₁ c₁ hP ⟨_, hM⟩ => ht st st₁ c₁ hP hM)

/-- Running `Stmt.call` on a procedure satisfying `MeetsProbContract` succeeds with the contracted
postcondition, register update, and cost bound, except with probability at most `δ vs st.mem`. -/
theorem runs_call_of_meetsProbContract {w : ℕ} {p : Program}
    {r f : ℕ} {args : List Expr} {C : Contract} {δ : List ℕ → (ℕ → ℕ) → ENNReal}
    {st : State} {vs : List ℕ}
    (hf : MeetsProbContract w p f C δ)
    (hargs : evalArgs w st args = some vs)
    (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem) :
    coins {ω | ¬ ∃ st' c v,
      Runs w p ω (.call r f args) st .normal st' c ∧
      C.post vs st.mem v st'.mem ∧
      st'.regs r = v ∧
      (∀ r', r' ≠ r → st'.regs r' = st.regs r') ∧
      c ≤ argsSize args + C.cost vs st.mem + 1} ≤ δ vs st.mem := by
  have hsub :
      {ω | ¬ ∃ st' c v,
        Runs w p ω (.call r f args) st .normal st' c ∧
        C.post vs st.mem v st'.mem ∧
        st'.regs r = v ∧
        (∀ r', r' ≠ r → st'.regs r' = st.regs r') ∧
        c ≤ argsSize args + C.cost vs st.mem + 1} ⊆
      {ω | ¬ EndsAsContract w p f C vs st.mem st.pos ω} := by
    intro ω hnot ⟨body, hproc, o₁, st₁, c₁, hrun_body, hpost, hcost⟩
    refine hnot ⟨{ st₁ with regs := Function.update st.regs r o₁.value },
      argsSize args + c₁ + 1, o₁.value,
      runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hrun_body, rfl, rfl, rfl⟩,
      hpost, ?_, ?_, ?_⟩
    · simp
    · intro r' hr'
      simp [hr']
    · omega
  exact le_trans (measure_mono hsub) (hf vs st.mem st.pos hwords hpre)

/-- `ProbTriple` rule for `Stmt.call` using a procedure's `MeetsProbContract`. -/
theorem ProbTriple.call {w : ℕ} {p : Program}
    {r f : ℕ} {args : List Expr} {C : Contract} {δ : List ℕ → (ℕ → ℕ) → ENNReal}
    {P : State → Prop} {Q : State → Outcome → State → ℕ → Prop} {δ₀ : ENNReal}
    (hf : MeetsProbContract w p f C δ)
    (hargs : ∀ st, P st → ∃ vs, evalArgs w st args = some vs ∧
      (∀ v ∈ vs, v < 2 ^ w) ∧ C.pre vs st.mem ∧ δ vs st.mem ≤ δ₀)
    (hpost : ∀ st vs st' c v, P st → evalArgs w st args = some vs →
      C.post vs st.mem v st'.mem → st'.regs r = v →
      (∀ r', r' ≠ r → st'.regs r' = st.regs r') →
      c ≤ argsSize args + C.cost vs st.mem + 1 →
      Q st .normal st' c) :
    ProbTriple w p (.call r f args) P Q δ₀ := by
  intro st hP
  rcases hargs st hP with ⟨vs, hvs, hwords, hpre, hδ⟩
  have hsub :
      {ω | ¬ ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q st o st' c} ⊆
        {ω | ¬ ∃ st' c v,
          Runs w p ω (.call r f args) st .normal st' c ∧
          C.post vs st.mem v st'.mem ∧
          st'.regs r = v ∧
          (∀ r', r' ≠ r → st'.regs r' = st.regs r') ∧
          c ≤ argsSize args + C.cost vs st.mem + 1} := by
    intro ω hnot ⟨st', c, v, hrun, hp, hr, hother, hcost⟩
    exact hnot ⟨.normal, st', c, hrun, hpost st vs st' c v hP hvs hp hr hother hcost⟩
  exact le_trans (measure_mono hsub) (le_trans (runs_call_of_meetsProbContract hf hvs hwords hpre) hδ)

/-- Sequential composition of `Stmt.call` on a `MeetsProbContract` callee with a continuation `t`. -/
theorem ProbTriple.call_seq {w : ℕ} {p : Program}
    {r f : ℕ} {args : List Expr} {C : Contract} {δ_f : List ℕ → (ℕ → ℕ) → ENNReal}
    {t : Stmt} {P : State → Prop} {Q : State → Outcome → State → ℕ → Prop} {δ₁ δ₂ : ENNReal}
    (hf : MeetsProbContract w p f C δ_f)
    (hargs : ∀ st, P st → ∃ vs, evalArgs w st args = some vs ∧
      (∀ v ∈ vs, v < 2 ^ w) ∧ C.pre vs st.mem ∧ δ_f vs st.mem ≤ δ₁)
    (ht : ∀ st vs st₁ c₁ v, P st → evalArgs w st args = some vs →
      C.post vs st.mem v st₁.mem → st₁.regs r = v →
      (∀ r', r' ≠ r → st₁.regs r' = st.regs r') →
      c₁ ≤ argsSize args + C.cost vs st.mem + 1 →
      ProbTriple w p t (fun st' => st' = st₁)
        (fun _ o₂ st₂ c₂ => Q st o₂ st₂ (c₁ + c₂ + 1)) δ₂) :
    ProbTriple w p (.seq (.call r f args) t) P Q (δ₁ + δ₂) := by
  refine ProbTriple.seq_normal (M := fun st st₁ c₁ =>
      ∃ vs v, evalArgs w st args = some vs ∧
        C.post vs st.mem v st₁.mem ∧ st₁.regs r = v ∧
        (∀ r', r' ≠ r → st₁.regs r' = st.regs r') ∧
        c₁ ≤ argsSize args + C.cost vs st.mem + 1) ?_ ?_
  · exact ProbTriple.call hf hargs fun st vs st' c v _ hvs hp hr hother hcost =>
      ⟨rfl, vs, v, hvs, hp, hr, hother, hcost⟩
  · rintro st st₁ c₁ hP ⟨vs, v, hvs, hp, hr, hother, hcost⟩
    exact ht st vs st₁ c₁ v hP hvs hp hr hother hcost

/-- Conditional branching: if `e` always evaluates, the failure bound is `max δ₁ δ₂`. -/
theorem ProbTriple.cond {w : ℕ} {p : Program} {e : Expr} {s t : Stmt}
    {P : State → Prop} {Q : State → Outcome → State → ℕ → Prop} {δ₁ δ₂ : ENNReal}
    (heval : ∀ st, P st → ∃ v, e.eval w st = some v)
    (hs : ProbTriple w p s (fun st => P st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0)
      (fun st o st' c => Q st o st' (e.size + c + 1)) δ₁)
    (ht : ProbTriple w p t (fun st => P st ∧ e.eval w st = some 0)
      (fun st o st' c => Q st o st' (e.size + c + 1)) δ₂) :
    ProbTriple w p (.cond e s t) P Q (max δ₁ δ₂) := by
  intro st hP
  obtain ⟨v, hv⟩ := heval st hP
  by_cases hv0 : v = 0
  · subst hv0
    have hsub :
        {ω | ¬ ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ Q st o st' c} ⊆
          {ω | ¬ ∃ o st' c, Runs w p ω t st o st' c ∧ Q st o st' (e.size + c + 1)} := by
      intro ω hnot ⟨o, st', c, hrun, hq⟩
      exact hnot ⟨o, st', e.size + c + 1,
        runs_cond_iff.mpr ⟨0, c, hv, by simpa using hrun, rfl⟩, hq⟩
    exact le_trans (measure_mono hsub) (le_trans (ht st ⟨hP, hv⟩) (le_max_right δ₁ δ₂))
  · have hsub :
        {ω | ¬ ∃ o st' c, Runs w p ω (.cond e s t) st o st' c ∧ Q st o st' c} ⊆
          {ω | ¬ ∃ o st' c, Runs w p ω s st o st' c ∧ Q st o st' (e.size + c + 1)} := by
      intro ω hnot ⟨o, st', c, hrun, hq⟩
      exact hnot ⟨o, st', e.size + c + 1,
        runs_cond_iff.mpr ⟨v, c, hv, by simp [hv0, hrun], rfl⟩, hq⟩
    exact le_trans (measure_mono hsub) (le_trans (hs st ⟨hP, v, hv, hv0⟩) (le_max_left δ₁ δ₂))

/-- Bounded-iteration loop rule: if each body step from invariant `I` strictly decreases variant `V`
with failure probability at most `δ`, then starting with `V st ≤ T` fails with probability at most
`T * δ`. -/
theorem ProbTriple.loop {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {I : State → Prop} {V : State → ℕ}
    {M : State → Outcome → State → ℕ → Prop}
    {Q : State → Outcome → State → ℕ → Prop}
    {T : ℕ} {δ : ENNReal}
    (heval : ∀ st, I st → ∃ v, e.eval w st = some v)
    (hdone : ∀ st, I st → e.eval w st = some 0 → Q st .normal st (e.size + 1))
    (hpos : ∀ st v, I st → e.eval w st = some v → v ≠ 0 → 0 < V st)
    (hbody : ProbTriple w p body
      (fun st => I st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0) M δ)
    (hret : ∀ st u st₁ c₁, I st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      M st (.returned u) st₁ c₁ → Q st (.returned u) st₁ (e.size + c₁ + 1))
    (hstep : ∀ st st₁ c₁, I st → (∃ v, e.eval w st = some v ∧ v ≠ 0) →
      M st .normal st₁ c₁ →
      I st₁ ∧ V st₁ < V st ∧
        ∀ o₂ st₂ c₂, Q st₁ o₂ st₂ c₂ → Q st o₂ st₂ (e.size + c₁ + c₂ + 1)) :
    ProbTriple w p (.loop e body) (fun st => I st ∧ V st ≤ T) Q ((T : ENNReal) * δ) := by
  induction T with
  | zero =>
    intro st ⟨hI, hV⟩
    obtain ⟨v, hv⟩ := heval st hI
    have hv0 : v = 0 := by
      by_contra hne
      have hlt := hpos st v hI hv hne
      omega
    subst hv0
    have hempty :
        {ω | ¬ ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q st o st' c} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨.normal, st, e.size + 1,
        runs_loop_iff.mpr (Or.inl ⟨hv, rfl, rfl, rfl⟩), hdone st hI hv⟩
    rw [hempty, measure_empty]
    exact zero_le
  | succ T ih =>
    intro st ⟨hI, hV⟩
    obtain ⟨v, hv⟩ := heval st hI
    by_cases hv0 : v = 0
    · subst hv0
      have hempty :
          {ω | ¬ ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q st o st' c} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
        exact ⟨.normal, st, e.size + 1,
          runs_loop_iff.mpr (Or.inl ⟨hv, rfl, rfl, rfl⟩), hdone st hI hv⟩
      rw [hempty, measure_empty]
      exact zero_le
    · let τ := normalRunPrefix w p body st (fun st₁ c₁ => M st .normal st₁ c₁)
      let E : ℕ → State × ℕ → Set (ℕ → Bool) := fun q res =>
        {ω | q ≤ res.1.pos ∧
          ¬ ∃ o₂ st₂ c₂, Runs w p ω (.loop e body) res.1 o₂ st₂ c₂ ∧ Q res.1 o₂ st₂ c₂}
      have hτ : PrefixDetermined τ :=
        prefixDetermined_normalRunPrefix w p body st (fun st₁ c₁ => M st .normal st₁ c₁)
      have hE_dep : ∀ q res, DependsOn (E q res) {i | q ≤ i} :=
        fun q res => tailRunFail_dependsOn w p (.loop e body) q res.1 (Q res.1)
      have hE_prob : ∀ ω q res, τ ω = some (q, res) → coins (E q res) ≤ (T : ENNReal) * δ := by
        intro ω q res hτ_ω
        obtain ⟨_, _, hm₀⟩ := normalRunPrefix_some hτ_ω
        obtain ⟨hI₁, hV_lt, _⟩ := hstep st res.1 res.2 hI ⟨v, hv, hv0⟩ hm₀
        have hV₁ : V res.1 ≤ T := by omega
        have hsub : E q res ⊆
            {ω' | ¬ ∃ o₂ st₂ c₂, Runs w p ω' (.loop e body) res.1 o₂ st₂ c₂ ∧ Q res.1 o₂ st₂ c₂} :=
          fun _ hmem => hmem.2
        exact le_trans (measure_mono hsub) (ih res.1 ⟨hI₁, hV₁⟩)
      let B₁ : Set (ℕ → Bool) :=
        {ω | ¬ ∃ o₁ st₁ c₁, Runs w p ω body st o₁ st₁ c₁ ∧ M st o₁ st₁ c₁}
      let B₂ : Set (ℕ → Bool) := {ω | ∃ q res, τ ω = some (q, res) ∧ ω ∈ E q res}
      have hsub :
          {ω | ¬ ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q st o st' c} ⊆ B₁ ∪ B₂ := by
        intro ω hnot
        by_cases h₁ : ∃ o₁ st₁ c₁, Runs w p ω body st o₁ st₁ c₁ ∧ M st o₁ st₁ c₁
        · rcases h₁ with ⟨o₁, st₁, c₁, hrun₁, hm₁⟩
          cases o₁ with
          | returned u =>
            exfalso
            exact hnot ⟨.returned u, st₁, e.size + c₁ + 1,
              runs_loop_iff.mpr (Or.inr (Or.inl ⟨v, u, c₁, hv, hv0, hrun₁, rfl, rfl⟩)),
              hret st u st₁ c₁ hI ⟨v, hv, hv0⟩ hm₁⟩
          | normal =>
            refine Or.inr ⟨st₁.pos, (st₁, c₁), normalRunPrefix_spec hrun₁ hm₁, le_rfl, ?_⟩
            intro ⟨o₂, st₂, c₂, hrun₂, hq₂⟩
            obtain ⟨_, _, hQstep⟩ := hstep st st₁ c₁ hI ⟨v, hv, hv0⟩ hm₁
            exact hnot ⟨o₂, st₂, e.size + c₁ + c₂ + 1,
              runs_loop_iff.mpr (Or.inr (Or.inr ⟨v, st₁, c₁, c₂, hv, hv0, hrun₁, hrun₂, rfl⟩)),
              hQstep o₂ st₂ c₂ hq₂⟩
        · exact Or.inl h₁
      calc
        coins {ω | ¬ ∃ o st' c, Runs w p ω (.loop e body) st o st' c ∧ Q st o st' c}
          ≤ coins (B₁ ∪ B₂) := measure_mono hsub
        _ ≤ coins B₁ + coins B₂ := measure_union_le B₁ B₂
        _ ≤ δ + (T : ENNReal) * δ :=
            add_le_add (hbody st ⟨hI, v, hv, hv0⟩) (coins_fresh_bits τ hτ E hE_dep hE_prob)
        _ = ((T + 1 : ℕ) : ENNReal) * δ := by
            rw [Nat.cast_succ, add_mul, one_mul, add_comm]

/-- Bounded-iteration loop rule specialized to a uniform per-iteration cost bound `bodyCost` and
normal termination. -/
theorem ProbTriple.loop_bound {w : ℕ} {p : Program} {e : Expr} {body : Stmt}
    {I : State → Prop} {V : State → ℕ} {bodyCost T : ℕ} {δ : ENNReal}
    (heval : ∀ st, I st → ∃ v, e.eval w st = some v)
    (hpos : ∀ st v, I st → e.eval w st = some v → v ≠ 0 → 0 < V st)
    (hbody : ProbTriple w p body
      (fun st => I st ∧ ∃ v, e.eval w st = some v ∧ v ≠ 0)
      (fun st o st₁ c₁ => o = .normal ∧ I st₁ ∧ V st₁ < V st ∧ c₁ ≤ bodyCost) δ) :
    ProbTriple w p (.loop e body) (fun st => I st ∧ V st ≤ T)
      (fun st o st' c =>
        o = .normal ∧ I st' ∧ e.eval w st' = some 0 ∧
        c ≤ V st * (e.size + bodyCost + 1) + (e.size + 1))
      ((T : ENNReal) * δ) := by
  refine ProbTriple.loop heval
    (fun st hI hv => ⟨rfl, hI, hv, Nat.le_add_left _ _⟩)
    hpos hbody
    (fun _ _ _ _ _ _ ⟨h, _⟩ => by cases h)
    (fun st st₁ c₁ _ _ ⟨_, hI₁, hV_lt, hc₁⟩ => ⟨hI₁, hV_lt, fun o₂ st₂ c₂ ⟨ho₂, hI₂, hv₂, hc₂⟩ => ?_⟩)
  refine ⟨ho₂, hI₂, hv₂, ?_⟩
  have hstep : e.size + c₁ + c₂ + 1 ≤
      (V st₁ + 1) * (e.size + bodyCost + 1) + (e.size + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have hmul : (V st₁ + 1) * (e.size + bodyCost + 1) ≤ V st * (e.size + bodyCost + 1) :=
    Nat.mul_le_mul_right _ hV_lt
  omega

end WordRAM
