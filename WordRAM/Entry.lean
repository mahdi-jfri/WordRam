module

public import WordRAM.Logic

/-!
# Whole programs: from procedure `0` to `RunsTo`

A statement about a whole program uses `RunsTo` from `WordRAM/Model.lean`. Proofs work with the
body of procedure `0` instead. This file connects the two, and gives the facts about the initial
memory and the word size that such proofs need.

* `runsTo_iff_exists_runs`: `RunsTo` is a run of the entry call `call 0 0 [len]`.
* `runsTo_of_entry`: if the body of procedure `0` returns `len` and leaves `out` (of length `len`)
  at address `0`, then the program `RunsTo` output `out`, in two more steps.
* `listAt_initMem`, `zeroFrom_initMem`: the input is at address `0`, and memory after it is zero.
* `pow_lt_two_pow_wordSize`, `length_lt_two_pow_wordSize`, `lt_two_pow_wordSize_of_mem`: what fits
  in a word at word size `wordSize c input`.
-/

@[expose] public section

namespace WordRAM

/-- `RunsTo w p input ω out cost` holds exactly when the entry call of procedure `0` runs with
cost `cost` and leaves `out` as its output slice. -/
theorem runsTo_iff_exists_runs {w : ℕ} {p : Program} {input : List ℕ} {ω : ℕ → Bool}
    {out : List ℕ} {cost : ℕ} :
    RunsTo w p input ω out cost ↔
      ∃ o st,
        Runs w p ω (.call 0 0 [.const input.length])
          { mem := initMem input, regs := fun _ => 0, pos := 0 } o st cost ∧
        (List.range (st.regs 0)).map st.mem = out := by
  constructor
  · rintro ⟨fuel, hfuel⟩
    simp only [run] at hfuel
    cases hx : exec w p ω fuel (.call 0 0 [.const input.length])
        { mem := initMem input, regs := fun _ => 0, pos := 0 } with
    | none => simp [hx] at hfuel
    | some res =>
      rcases res with ⟨o, st, c⟩
      simp only [hx, Option.some.injEq, Prod.mk.injEq] at hfuel
      rcases hfuel with ⟨rfl, rfl⟩
      exact ⟨o, st, ⟨fuel, hx⟩, rfl⟩
  · rintro ⟨o, st, ⟨fuel, hfuel⟩, rfl⟩
    refine ⟨fuel, ?_⟩
    simp [run, hfuel]

/-- If the body of procedure `0`, started on `[input.length]` with the input in memory, returns
`len` and leaves `out` (of length `len`) at address `0`, in `cost` steps, then the program
`RunsTo` output `out` in `cost + 2` steps: the entry call adds its argument and itself. -/
theorem runsTo_of_entry {w : ℕ} {p : Program} {body : Stmt} {input out : List ℕ}
    {ω : ℕ → Bool} {len cost : ℕ} {st : State}
    (hentry : p.procs[0]? = some body) (hw : input.length < 2 ^ w)
    (hrun : Runs w p ω body (startState [input.length] (initMem input) 0) (.returned len) st cost)
    (hlen : out.length = len) (hout : ListAt st.mem 0 out) :
    RunsTo w p input ω out (cost + 2) := by
  refine runsTo_iff_exists_runs.mpr ⟨.normal, { st with regs := Function.update (fun _ => 0) 0 len },
    runs_call_iff.mpr ⟨[input.length], body, .returned len, st, cost,
      by simp [evalArgs, Expr.eval, hw], hentry, hrun, rfl, rfl, by simp [argsSize]; omega⟩, ?_⟩
  simp only [Function.update_self]
  refine List.ext_getElem (by simp [hlen]) fun i hi _ => ?_
  simp only [List.getElem_map, List.getElem_range]
  simpa using hout i (by simp at hi; omega)

/-- The input is stored at address `0` of the initial memory. -/
theorem listAt_initMem (input : List ℕ) : ListAt (initMem input) 0 input := by
  intro i hi
  simp [initMem, List.getElem?_eq_getElem hi]

/-- The initial memory is zero after the input. -/
theorem zeroFrom_initMem (input : List ℕ) : ZeroFrom (initMem input) input.length := by
  intro a ha
  simp [initMem, List.getElem?_eq_none ha]

/-- Every power `(len + max + 2) ^ c` of the input size fits in a word of size
`wordSize c input`. -/
theorem pow_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (input : List ℕ) :
    (input.length + input.foldr max 0 + 2) ^ c < 2 ^ wordSize c input := by
  unfold wordSize
  set m := input.length + input.foldr max 0 + 2
  have hm : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self one_lt_two m
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_lt_pow_left hm (by omega)

/-- The length of the input fits in a word. -/
theorem length_lt_two_pow_wordSize {c : ℕ} (hc : 1 ≤ c) (input : List ℕ) :
    input.length < 2 ^ wordSize c input := by
  have h := pow_lt_two_pow_wordSize hc input
  have : input.length + input.foldr max 0 + 2 ≤ (input.length + input.foldr max 0 + 2) ^ c :=
    Nat.le_self_pow (by omega) _
  omega

/-- Every number of the input fits in a word. -/
theorem lt_two_pow_wordSize_of_mem {c : ℕ} (hc : 1 ≤ c) {input : List ℕ} {x : ℕ}
    (hx : x ∈ input) : x < 2 ^ wordSize c input := by
  have hmax : x ≤ input.foldr max 0 := by
    clear hc
    induction input with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.mem_cons] at hx
      simp only [List.foldr_cons]
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact le_trans (ih hx) (le_max_right _ _)
  have h := pow_lt_two_pow_wordSize hc input
  have : input.length + input.foldr max 0 + 2 ≤ (input.length + input.foldr max 0 + 2) ^ c :=
    Nat.le_self_pow (by omega) _
  omega

end WordRAM
