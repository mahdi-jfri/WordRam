module

public import WordRAM.Model

/-!
# Contracts of procedures

A large algorithm becomes the procedures of one machine program. This file fixes how one states
what a procedure does, so that procedures proved separately fit together.

**Modules.** A program is assembled from modules: lists of procedure bodies placed at known
indices (`Program.HasAt`). A body calls other procedures by index, so a module is written for
given indices of itself and of the procedures it calls, and its theorems hold for every program
that has these bodies at these indices.

**Contracts.** A procedure is specified by a `Contract`: a precondition on its arguments and the
memory, a postcondition on the arguments, the memory before, the returned value and the memory
after, and a bound on the cost. The body starts with the arguments in registers `0, 1, …` (as a
`call` puts them), with any random position.
* `MeetsContract w p f C`: for every sequence of random bits, procedure `f` of `p` ends as `C`
  says. Deterministic procedures are stated this way, and so are randomized procedures that
  report a failure instead of a wrong answer, when their cost bound holds for every outcome.
* `MeetsProbContract w p f C δ`: from every start, the probability over the random bits that
  procedure `f` does not end as `C` says is at most `δ`. Only the bits from the start position
  on are read, so the bits before it play no role.

**Memory.** `ListAt mem a l` says that the list `l` is stored at addresses `a, a + 1, …`.
`ZeroFrom mem h` says that every cell at address `h` or above is zero. A procedure that needs new
memory takes a *heap pointer* `h` with `ZeroFrom mem h`, writes only at addresses `h` or above
(and where its contract says), and gives back a new heap pointer `h'` with `ZeroFrom mem' h'`.
Memory is never freed, so new memory is always zero, and the memory used is at most the time.

**Programs inside programs.** A program proved on its own, for example one given by a cited
theorem, is a whole `Program` with its own word size `w'`, run inside a host program at a larger
word size `w` (see `WordRAM/LinkDefs.lean`). Each random word it asks for is the lowest `w'`
bits of a random word of the host, so it sees the random bits `subBits w w' pos ω`, where `pos`
is the host's random position when it starts.
-/

@[expose] public section

namespace WordRAM

/-- `Runs w p ω s st o st' c`: at word size `w`, with random bits `ω`, statement `s` of program
`p` started in state `st` ends with outcome `o` in state `st'`, at cost `c`. -/
def Runs (w : ℕ) (p : Program) (ω : ℕ → Bool) (s : Stmt) (st : State) (o : Outcome)
    (st' : State) (c : ℕ) : Prop :=
  ∃ fuel, exec w p ω fuel s st = some (o, st', c)

/-- The value a procedure gives back to its caller: the value of its `ret`, or 0. -/
def Outcome.value : Outcome → ℕ
  | .returned v => v
  | .normal => 0

/-- The state in which a called procedure starts: memory `mem`, the arguments `args` in
registers `0, 1, …`, zero in the other registers, and random position `pos`. -/
def startState (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) : State :=
  { mem := mem, regs := fun i => args.getD i 0, pos := pos }

/-- The list `l` is stored at addresses `a, a + 1, …, a + l.length - 1`. -/
def ListAt (mem : ℕ → ℕ) (a : ℕ) (l : List ℕ) : Prop :=
  ∀ i (h : i < l.length), mem (a + i) = l[i]

/-- Every memory cell at address `h` or above is zero. -/
def ZeroFrom (mem : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ a, h ≤ a → mem a = 0

/-- Program `p` has the procedure bodies `bodies` at indices `b, b + 1, …`. -/
def Program.HasAt (p : Program) (b : ℕ) (bodies : List Stmt) : Prop :=
  ∀ i (h : i < bodies.length), p.procs[b + i]? = some bodies[i]

/-- What a procedure does.
* `pre args mem`: the condition on the arguments and the memory at the call.
* `post args mem v mem'`: the condition on the returned value `v` and the memory `mem'` at the
  end, given the arguments and the memory at the call.
* `cost args mem`: a bound on the cost of the body. -/
structure Contract where
  pre : List ℕ → (ℕ → ℕ) → Prop
  post : List ℕ → (ℕ → ℕ) → ℕ → (ℕ → ℕ) → Prop
  cost : List ℕ → (ℕ → ℕ) → ℕ

/-- The body of procedure `f`, started with arguments `args`, memory `mem` and random position
`pos`, ends as the contract `C` says: its returned value and final memory satisfy `C.post`, and
its cost is at most `C.cost`. -/
def EndsAsContract (w : ℕ) (p : Program) (f : ℕ) (C : Contract) (args : List ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) (ω : ℕ → Bool) : Prop :=
  ∃ body, p.procs[f]? = some body ∧ ∃ o st' c,
    Runs w p ω body (startState args mem pos) o st' c ∧
    C.post args mem o.value st'.mem ∧ c ≤ C.cost args mem

/-- Procedure `f` of `p` meets contract `C` at word size `w`, for every sequence of random bits:
whenever its arguments are words and the precondition holds, it ends as `C` says. -/
def MeetsContract (w : ℕ) (p : Program) (f : ℕ) (C : Contract) : Prop :=
  ∀ args mem pos ω, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem →
    EndsAsContract w p f C args mem pos ω

/-- Procedure `f` of `p` meets contract `C` at word size `w` except with probability `δ`:
whenever its arguments are words and the precondition holds, the random bits for which it does
not end as `C` says have probability at most `δ args mem`, whatever the random position. -/
def MeetsProbContract (w : ℕ) (p : Program) (f : ℕ) (C : Contract)
    (δ : List ℕ → (ℕ → ℕ) → ENNReal) : Prop :=
  ∀ args mem pos, (∀ a ∈ args, a < 2 ^ w) → C.pre args mem →
    coins {ω | ¬ EndsAsContract w p f C args mem pos ω} ≤ δ args mem

/-- The random bits seen by a program run inside a host program: the host reads words of `w` bits
from position `pos` on, and the inner program, of word size `w'`, keeps the lowest `w'` bits of
each word. Bit `i` of the inner sequence is bit `i % w'` of the host's word number `i / w'`. -/
def subBits (w w' pos : ℕ) (ω : ℕ → Bool) : ℕ → Bool :=
  fun i => ω (pos + i / w' * w + i % w')

end WordRAM
