module

public import Mathlib.Data.Nat.Log
public import Mathlib.Data.List.GetD
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Uniform

/-!
# The machine model

A statement that an algorithm exists and runs within a time bound needs a model of computation.
This file is the model. It is the part of the library a reader must check to know what such a
statement says; everything else in the library is proved from it.

The model is a randomized word RAM. Programs are data, every step is counted, and every value is
a word.

* **Words.** A run has a word size `w`. Every value that the program computes or stores must be
  less than `2 ^ w`; an operation whose result does not fit stops the run with no answer. So
  memory addresses are also less than `2 ^ w`. The word size of a run on an input is
  `wordSize c input`, which is `c` times the number of bits needed to write the length of the
  input or any of its numbers. Each statement about running times picks its own constant `c`.
* **Unit cost.** Each operation on words costs one, whatever the values are, as in the standard
  word RAM of algorithm design. A log-cost RAM would charge `log n` for each operation instead.
* **Memory.** One global memory `ℕ → ℕ`, which starts with the input at addresses
  `0, …, len - 1` and zero elsewhere. A program writes its output at the start of memory.
* **Procedures.** A program is a list of procedures, and procedure 0 is the entry point. Each
  running procedure has its own registers, which start with the arguments of the call and zero
  elsewhere. A register is named by a constant in the program text, so each procedure uses a
  fixed number of registers, and a call costs as much as a constant-size stack frame.
* **Randomness.** A run reads an infinite sequence `ω : ℕ → Bool` of random bits. The statement
  `rand r` puts a random word into register `r`, made of the next `w` bits, at unit cost.
  Probabilities are taken for `ω` drawn from `coins`, under which the bits are independent and
  uniform, so each random word is uniform on `0, …, 2 ^ w - 1` and independent of the others.
  A program with no `rand` statement is deterministic (`Program.IsDeterministic`).

The semantics `exec` is a function with fuel. Fuel only bounds the depth of the evaluation, so
that the definition terminates; it does not limit the running time, which is the cost.
-/

@[expose] public section

namespace WordRAM

/-- Binary operations on words. Comparisons give 1 for true and 0 for false. Subtraction stops at
0, and division or remainder by 0 gives 0, as for `ℕ` in Lean. The bitwise operations and shifts
are those of the standard word RAM. -/
inductive BinOp
  | add | sub | mul | div | mod | lt | eq | and | or | xor | shiftLeft | shiftRight
  deriving DecidableEq, Repr

/-- The value of a binary operation, before the check that it fits in a word. -/
def BinOp.eval : BinOp → ℕ → ℕ → ℕ
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .mod, a, b => a % b
  | .lt, a, b => if a < b then 1 else 0
  | .eq, a, b => if a = b then 1 else 0
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b
  | .shiftLeft, a, b => a <<< b
  | .shiftRight, a, b => a >>> b

/-- Expressions. `reg r` reads register `r` of the running procedure, and `load a` reads the
memory cell whose address is the value of `a`. -/
inductive Expr
  | const (k : ℕ)
  | reg (r : ℕ)
  | load (addr : Expr)
  | bin (op : BinOp) (a b : Expr)
  deriving Repr

/-- The number of operations in an expression. Evaluating it costs this much. -/
def Expr.size : Expr → ℕ
  | .const _ => 1
  | .reg _ => 1
  | .load a => a.size + 1
  | .bin _ a b => a.size + b.size + 1

/-- The memory and the registers of the running procedure, and the position of the next random
bit to be read. -/
structure State where
  mem : ℕ → ℕ
  regs : ℕ → ℕ
  pos : ℕ

/-- The value of an expression at word size `w`, or `none` if a constant or the result of an
operation is not less than `2 ^ w`. Registers and memory hold only words, since everything stored
there passed this check or came from the input. -/
def Expr.eval (w : ℕ) (st : State) : Expr → Option ℕ
  | .const k => if k < 2 ^ w then some k else none
  | .reg r => some (st.regs r)
  | .load a => (a.eval w st).map st.mem
  | .bin op a b =>
    match a.eval w st, b.eval w st with
    | some x, some y => if op.eval x y < 2 ^ w then some (op.eval x y) else none
    | _, _ => none

/-- The values of a list of expressions, or `none` if one of them has no value. -/
def evalArgs (w : ℕ) (st : State) : List Expr → Option (List ℕ)
  | [] => some []
  | e :: es =>
    match e.eval w st, evalArgs w st es with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- The total size of a list of expressions. -/
def argsSize : List Expr → ℕ
  | [] => 0
  | e :: es => e.size + argsSize es

/-- Statements.
* `assign r e` puts the value of `e` in register `r`.
* `store a e` puts the value of `e` in the memory cell at the value of `a`.
* `rand r` puts the next random word in register `r` (see `readWord`).
* `cond e s t` runs `s` if `e` is nonzero and `t` otherwise.
* `loop e s` runs `s` while `e` is nonzero.
* `call r f args` runs procedure `f`. Its registers start with the values of `args` in
  registers `0, 1, …` and 0 everywhere else. Its return value goes to register `r`.
* `ret e` ends the running procedure with the value of `e`. A procedure that ends without
  `ret` returns 0. -/
inductive Stmt
  | nop
  | assign (r : ℕ) (e : Expr)
  | store (addr val : Expr)
  | rand (r : ℕ)
  | seq (s t : Stmt)
  | cond (e : Expr) (s t : Stmt)
  | loop (e : Expr) (body : Stmt)
  | call (r : ℕ) (f : ℕ) (args : List Expr)
  | ret (e : Expr)
  deriving Repr

/-- A program: the bodies of its procedures. Procedure 0 is the entry point. -/
structure Program where
  procs : List Stmt
  deriving Repr

/-- `s` contains no `rand` statement. -/
def Stmt.NoRand : Stmt → Prop
  | .rand _ => False
  | .seq s t => s.NoRand ∧ t.NoRand
  | .cond _ s t => s.NoRand ∧ t.NoRand
  | .loop _ body => body.NoRand
  | _ => True

/-- `p` is deterministic: none of its procedures contains a `rand` statement, so it never reads
the random bits. `Checks/StatementExamples.lean` proves that its runs are then the same for every
sequence of random bits (`runsTo_iff_of_isDeterministic`). -/
def Program.IsDeterministic (p : Program) : Prop :=
  ∀ s ∈ p.procs, s.NoRand

/-- The word whose binary digits are the `w` bits `ω pos, …, ω (pos + w - 1)`, lowest digit
first. It is less than `2 ^ w`. -/
def readWord (ω : ℕ → Bool) (pos : ℕ) : ℕ → ℕ
  | 0 => 0
  | w + 1 => (if ω pos then 1 else 0) + 2 * readWord ω (pos + 1) w

/-- How a statement ended: normally, or by `ret` with a value. -/
inductive Outcome
  | normal
  | returned (v : ℕ)
  deriving DecidableEq, Repr

/-- Run statement `s` of program `p` from state `st`, at word size `w`, with random bits `ω`. The
result is how the statement ended, the new state, and the cost. Every statement costs one plus
the sizes of the expressions it evaluates, plus the costs of the statements it runs.

The result is `none` when a value does not fit in a word, when a call names a procedure that
does not exist, or when the run needs more than `fuel` levels of evaluation. Fuel bounds only the
depth of the evaluation, so that this function terminates: more fuel never changes a result
that is not `none`. -/
def exec (w : ℕ) (p : Program) (ω : ℕ → Bool) : ℕ → Stmt → State → Option (Outcome × State × ℕ)
  | 0, _, _ => none
  | fuel + 1, s, st =>
    match s with
    | .nop => some (.normal, st, 1)
    | .assign r e =>
      match e.eval w st with
      | none => none
      | some v => some (.normal, { st with regs := Function.update st.regs r v }, e.size + 1)
    | .store a e =>
      match a.eval w st, e.eval w st with
      | some x, some v =>
        some (.normal, { st with mem := Function.update st.mem x v }, a.size + e.size + 1)
      | _, _ => none
    | .rand r =>
      some (.normal,
        { st with regs := Function.update st.regs r (readWord ω st.pos w), pos := st.pos + w }, 1)
    | .seq s t =>
      match exec w p ω fuel s st with
      | none => none
      | some (.returned v, st', c) => some (.returned v, st', c + 1)
      | some (.normal, st', c) =>
        match exec w p ω fuel t st' with
        | none => none
        | some (o, st'', c') => some (o, st'', c + c' + 1)
    | .cond e s t =>
      match e.eval w st with
      | none => none
      | some v =>
        match exec w p ω fuel (if v = 0 then t else s) st with
        | none => none
        | some (o, st', c) => some (o, st', e.size + c + 1)
    | .loop e body =>
      match e.eval w st with
      | none => none
      | some v =>
        if v = 0 then some (.normal, st, e.size + 1) else
        match exec w p ω fuel body st with
        | none => none
        | some (.returned u, st', c) => some (.returned u, st', e.size + c + 1)
        | some (.normal, st', c) =>
          match exec w p ω fuel (.loop e body) st' with
          | none => none
          | some (o, st'', c') => some (o, st'', e.size + c + c' + 1)
    | .call r f args =>
      match evalArgs w st args, p.procs[f]? with
      | some vs, some body =>
        match exec w p ω fuel body { st with regs := fun i => vs.getD i 0 } with
        | none => none
        | some (o, st', c) =>
          let u := match o with
            | .returned u => u
            | .normal => 0
          some (.normal, { st' with regs := Function.update st.regs r u }, argsSize args + c + 1)
      | _, _ => none
    | .ret e =>
      match e.eval w st with
      | none => none
      | some v => some (.returned v, st, e.size + 1)

/-- The memory at the start of a run: the input at addresses `0, …, len - 1`, and zero
elsewhere. -/
def initMem (input : List ℕ) (a : ℕ) : ℕ :=
  input.getD a 0

/-- Run program `p` at word size `w` with random bits `ω` on `input`, by calling procedure 0 with
the length of the input as its argument. If procedure 0 returns `ℓ`, the output is the contents
of memory cells `0, …, ℓ - 1`. The result is the output and the total cost, or `none` as for
`exec`. -/
def run (w : ℕ) (p : Program) (ω : ℕ → Bool) (input : List ℕ) (fuel : ℕ) :
    Option (List ℕ × ℕ) :=
  match exec w p ω fuel (.call 0 0 [.const input.length])
      { mem := initMem input, regs := fun _ => 0, pos := 0 } with
  | none => none
  | some (_, st, c) => some ((List.range (st.regs 0)).map st.mem, c)

/-- `RunsTo w p input ω out cost`: at word size `w` and with random bits `ω`, program `p` halts
on `input` with output `out` after `cost` steps. -/
def RunsTo (w : ℕ) (p : Program) (input : List ℕ) (ω : ℕ → Bool) (out : List ℕ) (cost : ℕ) :
    Prop :=
  ∃ fuel, run w p ω input fuel = some (out, cost)

/-- The word size for `input` with constant `c`: `c` times the number of bits of
`len + max + 2`, where `len` is the length of the input and `max` is its largest number. Every
number of the input, and every address of the input, is less than `2 ^ wordSize c input` when
`c ≥ 1`. -/
def wordSize (c : ℕ) (input : List ℕ) : ℕ :=
  c * (Nat.log 2 (input.length + input.foldr max 0 + 2) + 1)

/-- The distribution of the random bits: independent bits, each 0 or 1 with probability `1/2`. -/
noncomputable def coins : MeasureTheory.Measure (ℕ → Bool) :=
  MeasureTheory.Measure.infinitePi fun _ => (PMF.uniformOfFintype Bool).toMeasure

end WordRAM
