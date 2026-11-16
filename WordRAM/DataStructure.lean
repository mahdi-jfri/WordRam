module

public import WordRAM.Layout

/-!
# Data structures

A data structure is a group of procedures that keep a state in memory between calls: an
initialization, which creates a state, and operations, numbered `0, 1, …`, which change it or
answer questions about it. The user of a data structure sees only its abstract state, an element
of a type `σ` chosen by the specification (a graph under deletions, a forest, a set, …).
`DataStructure σ` says, in terms of this state, what each call may assume, what it must achieve,
and what it may cost. How the state is kept in memory is the implementation's choice and stays
hidden: `DSRep σ` gives the representation, the potential and the footprint, and
`DSRep.Implements` says that procedures of a program meet the specification with it.

**Handles.** A state is named by its handle: the heap pointer with which the initialization that
created it was called. Every operation takes the handle as its first argument.

**Memory.** Every call follows the heap discipline of `WordRAM/Layout.lean`: its last argument is
the heap pointer `h`, memory from `h` on is zero, and it returns a new heap pointer `h'` with
`h ≤ h' ≤ h + space` (the space bound of the call), leaving memory from `h'` on zero. Its answer,
if it has one, is in memory where the specification says. The state occupies a set of cells, its
footprint, which lies below the heap pointer. A call writes only to the footprint of the state it
starts from and to the new cells from `h` to `h'`, and the new footprint lies in these cells. So
the data a user keeps in cells it allocated itself is never changed by a call, and a state
survives everything the user writes to its own cells (`DSRep.Local`). Several states, of the same
or of different data structures, can live in one memory.

**Cost.** Bounds are amortized against the potential, a number that depends on the state and the
memory: the cost of a call plus the potential after it is at most the bound of the call plus the
potential before it, and the initialization starts from potential `0`. So the total cost of an
initialization and the calls after it is at most the sum of their bounds. With potential `0` the
bounds are worst case. A bound on the total time of all calls is the case where the
initialization's bound pays for everything and the other bounds are `0`.

**Randomness.** As for `MeetsContract`, a call must end as specified for every sequence of random
bits. A deterministic data structure is one whose procedures have no `rand` statement.
-/

@[expose] public section

namespace WordRAM

/-- The specification of a data structure whose abstract states have type `σ`. The arguments
`args` of every call end with the heap pointer (`heapArg args`), and those of an operation start
with the handle of its state.
* `initPre args mem`: when the initialization may be called.
* `initPost args mem s mem'`: the state `s` it creates, and its answer in the new memory `mem'`.
* `pre i s args mem`: when operation `i` may be called on state `s`.
* `post i s args mem s' mem'`: the state `s'` it leaves, and its answer in `mem'`.
* `initCost`, `cost i`: the amortized bounds on the cost of the calls.
* `initSpace`, `space i`: the bounds on the number of new cells of the calls. -/
structure DataStructure (σ : Type) where
  initPre : List ℕ → (ℕ → ℕ) → Prop
  initPost : List ℕ → (ℕ → ℕ) → σ → (ℕ → ℕ) → Prop
  initCost : List ℕ → (ℕ → ℕ) → ℕ
  initSpace : List ℕ → (ℕ → ℕ) → ℕ
  pre : ℕ → σ → List ℕ → (ℕ → ℕ) → Prop
  post : ℕ → σ → List ℕ → (ℕ → ℕ) → σ → (ℕ → ℕ) → Prop
  cost : ℕ → σ → List ℕ → (ℕ → ℕ) → ℕ
  space : ℕ → σ → List ℕ → (ℕ → ℕ) → ℕ

/-- How an implementation keeps states in memory: `rep b s mem` says that memory `mem` holds state
`s` with handle `b`, `phi b s mem` is its potential, and `foot b s` is the set of cells that hold
it. -/
structure DSRep (σ : Type) where
  rep : ℕ → σ → (ℕ → ℕ) → Prop
  phi : ℕ → σ → (ℕ → ℕ) → ℕ
  foot : ℕ → σ → ℕ → Prop

namespace DSRep

variable {σ : Type}

/-- A state and its potential depend only on the cells of its footprint. -/
def Local (R : DSRep σ) : Prop :=
  ∀ b s mem mem', (∀ a, R.foot b s a → mem a = mem' a) →
    (R.rep b s mem → R.rep b s mem') ∧ R.phi b s mem = R.phi b s mem'

/-- A call that starts with heap pointer `h` in memory `mem`, where the cells `old` hold the state
it starts from, and ends with the state `s'` of handle `b` in memory `mem'`, returning the new heap pointer
`h'`, respects memory: `h ≤ h' ≤ h + space`, memory from `h'` on is zero, cells below `h` outside
`old` are unchanged, and the new footprint lies in `old` and the new cells. -/
def Respects (R : DSRep σ) (old : ℕ → Prop) (h space : ℕ) (mem : ℕ → ℕ) (h' b : ℕ) (s' : σ)
    (mem' : ℕ → ℕ) : Prop :=
  h ≤ h' ∧ h' ≤ h + space ∧ ZeroFrom mem' h' ∧ (∀ a < h, ¬ old a → mem' a = mem a) ∧
    ∀ a, R.foot b s' a → old a ∨ (h ≤ a ∧ a < h')

/-- Procedures `init` and `op 0, op 1, …` of program `p` implement the data structure `D` at
word size `w` with the representation `R`. States are local (`Local`). From memory that meets the
precondition, with memory from the heap pointer on zero and room for the space bound below
`2 ^ w`, every call ends, for every sequence of random bits, in a state `s'` that memory holds,
meeting the postcondition, respecting memory, and within its amortized bound. The state created
by the initialization has the heap pointer of the call as its handle. An operation, called with
the handle `b` of its state as first argument, also assumes that memory holds the state and that
its footprint lies below the heap pointer. -/
def Implements (R : DSRep σ) (w : ℕ) (p : Program) (init : ℕ) (op : ℕ → ℕ)
    (D : DataStructure σ) : Prop :=
  R.Local ∧
  (∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → D.initPre args mem →
    ZeroFrom mem (heapArg args) → heapArg args + D.initSpace args mem < 2 ^ w →
    ∃ body, p.procs[init]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧ ∃ s',
        R.rep (heapArg args) s' st'.mem ∧ D.initPost args mem s' st'.mem ∧
        R.Respects (fun _ => False) (heapArg args) (D.initSpace args mem) mem o.value
          (heapArg args) s' st'.mem ∧
        c + R.phi (heapArg args) s' st'.mem ≤ D.initCost args mem) ∧
  (∀ i b s args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → args.head? = some b → R.rep b s mem →
    D.pre i s args mem → (∀ a, R.foot b s a → a < heapArg args) → ZeroFrom mem (heapArg args) →
    heapArg args + D.space i s args mem < 2 ^ w →
    ∃ body, p.procs[op i]? = some body ∧ ∃ o st' c,
      Runs w p ω body (startState args mem pos) o st' c ∧ ∃ s',
        R.rep b s' st'.mem ∧ D.post i s args mem s' st'.mem ∧
        R.Respects (R.foot b s) (heapArg args) (D.space i s args mem) mem o.value b s'
          st'.mem ∧
        c + R.phi b s' st'.mem ≤ D.cost i s args mem + R.phi b s mem)

end DSRep

end WordRAM
