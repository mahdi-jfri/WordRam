module

public import WordRAM.Contract

/-!
# Layouts: storing data in memory

Procedures pass data to each other through memory. This file gives the usual forms.

* A **list** `l` is stored at `a` as its elements at `a, a + 1, …` (`ListAt mem a l`), when its
  length is known to the reader, or as a **length-prefixed list** (`SeqAt mem a l`) otherwise.
* A **function on `0, …, len - 1`** is stored as the list of its values, `tab len f`.

**Procedures** that allocate follow the heap discipline of `WordRAM/Contract.lean` in the form
`heapContract`: the last argument is the heap pointer `h`; the procedure writes its output
starting at `h`, leaves memory below `h` unchanged, and returns the new heap pointer. So the
caller knows where the output is (at the old `h`) and where free memory starts (the returned
value). A procedure that changes a structure in place states its own contract instead.
-/

@[expose] public section

namespace WordRAM

/-- A length-prefixed list: the length of `l` at address `a`, then the elements of `l` at
`a + 1, …, a + l.length`. -/
def SeqAt (mem : ℕ → ℕ) (a : ℕ) (l : List ℕ) : Prop :=
  mem a = l.length ∧ ListAt mem (a + 1) l

/-- The values `f 0, …, f (len - 1)`. -/
def tab (len : ℕ) (f : ℕ → ℕ) : List ℕ :=
  (List.range len).map f

/-- The heap pointer of a call: the last argument. -/
def heapArg (args : List ℕ) : ℕ :=
  args.getLastD 0

/-- A contract in the heap discipline, at word size `w`. The last argument is the heap pointer
`h`. The procedure may assume `pre`, that memory from `h` on is zero, and that
`h + space < 2 ^ w`. It must return a new heap pointer `h'` with `h ≤ h' ≤ h + space`, leave
memory below `h` unchanged, leave memory from `h'` on zero, satisfy `post`, and cost at most
`cost`. The space is separate from the cost because a whole program run inside a procedure
(`WordRAM/LinkDefs.lean`) gets a region of `2 ^ w'` cells, however little of it it uses. -/
def heapContract (w : ℕ) (pre : List ℕ → (ℕ → ℕ) → Prop)
    (post : List ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop) (cost space : List ℕ → (ℕ → ℕ) → ℕ) :
    Contract where
  pre args mem :=
    pre args mem ∧ ZeroFrom mem (heapArg args) ∧ heapArg args + space args mem < 2 ^ w
  post args mem v mem' :=
    heapArg args ≤ v ∧ v ≤ heapArg args + space args mem ∧
    (∀ x < heapArg args, mem' x = mem x) ∧ ZeroFrom mem' v ∧ post args mem mem'
  cost := cost

end WordRAM
