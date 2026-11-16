# WordRAM

A randomized word RAM in Lean 4, with a program logic for proving that programs are correct and
how long they run.

The model is small enough to read in one sitting (`WordRAM/Model.lean`, about 270 lines), and it is
the only part a reader has to trust: a statement such as "there is a program that solves this
problem in `O(m log m)` steps" is stated against it, and everything else in the library is proved
from it. The rest of the library is the tooling for proving such statements about large
algorithms: contracts for procedures, a Hoare-style logic with cost bounds, linking of programs
proved separately, and probability over the random bits.

## The model

* **Words.** A run has a word size `w`. Every value the program computes or stores must be less
  than `2 ^ w`; an operation whose result does not fit stops the run with no answer. The word size
  of a run on an input is `wordSize c input`, that is `c` times the number of bits of the input's
  length and largest number, for a constant `c` that each statement picks.
* **Unit cost.** Each operation on words costs one: `+ - * / %`, comparisons, bitwise
  operations and shifts. Subtraction stops at `0`, and division by `0` gives `0`.
* **Memory.** One memory `ℕ → ℕ`. It starts with the input at addresses `0, …, len - 1` and zero
  elsewhere, and the program writes its output at the start of memory.
* **Procedures.** A program is a list of procedures; procedure `0` is the entry point. Each
  running procedure has its own registers, named by constants in the program text, so a call costs
  as much as a constant-size stack frame. Statements are `assign`, `store`, `rand`, sequencing,
  `cond`, `loop`, `call` and `ret`, over expressions built from constants, registers, `load` and
  binary operations.
* **Randomness.** A run reads an infinite sequence of random bits; `rand r` puts the next `w` of
  them into register `r` as one word, at unit cost. Probabilities are taken under `coins`, the
  product of fair coins. A program with no `rand` statement is deterministic
  (`Program.IsDeterministic`).

`RunsTo w p input ω out cost` says that program `p`, at word size `w` and with random bits `ω`,
halts on `input` with output `out` after `cost` steps.

## What the library provides

| File | Contents |
| --- | --- |
| `WordRAM/Model.lean` | the model: `Expr`, `Stmt`, `Program`, `exec`, `run`, `RunsTo`, `wordSize`, `coins` |
| `WordRAM/Contract.lean` | `Contract`, `MeetsContract` (for every outcome of the random bits), `MeetsProbContract` (with a failure probability), `Program.HasAt` for programs assembled from modules |
| `WordRAM/Exec.lean`, `Expr.lean`, `Memory.lean` | execution lemmas, expression evaluation, memory layouts (`ListAt`, `ZeroFrom`) |
| `WordRAM/Logic.lean` | `Triple`, a Hoare triple with a cost bound; rules for every statement, counter and measure loops (`forRange`, `forUp`, `Triple.loop_measure`), and the bridges `meetsContract_of_triple` and `meetsContract_of_runs`. Its header is a guide to proving a procedure. |
| `WordRAM/Entry.lean` | from procedure `0` to `RunsTo` (`runsTo_of_entry`), the initial memory, and what fits in a word at `wordSize c input` |
| `WordRAM/Tactic.lean` | symbolic execution: `wram_step` and `wram_run` step through a body (expressions, overflow side conditions, branches, calls by contract), `wram_cost` closes the cost inequality; `meetsContract_of_rec` for recursive procedures |
| `WordRAM/DataStructure.lean` | data structures: an abstract state, a hidden representation in memory with a footprint and a potential, and calls in the heap discipline with amortized bounds (`DataStructure`, `DSRep.Implements`) |
| `WordRAM/Layout.lean` | length-prefixed lists, tables, and `heapContract` for procedures that allocate |
| `WordRAM/CopyWords.lean` | a verified procedure that copies a block of memory |
| `WordRAM/LinkDefs.lean`, `Link.lean` | `runner Q c b`: run a whole program `Q`, proved on its own, as a procedure of a larger program (`runner_spec`) |
| `WordRAM/Coins.lean`, `CoinsFresh.lean` | random words are uniform and independent under `coins` |
| `WordRAM/ProbRuns.lean`, `Prob.lean` | `ProbTriple`, a Hoare triple with a failure probability, and rules for sequencing and calls |
| `WordRAM/ProbBridge.lean` | the law of a program's results as a Mathlib `PMF` (`SubLaw`, `ExactSubLaw`) |

A procedure is specified by a contract and proved with the logic. For example,
`WordRAM/CopyWords.lean` proves

```lean
theorem copyWords_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.HasAt b [copyWords]) :
    MeetsContract w p b (copyWordsContract w)
```

which holds in every program `p` that has `copyWords` at procedure `b`. Theorems about modules
are stated this way, so that a program can be assembled from modules proved separately.

## Using it

Add the package to your `lakefile.toml`:

```toml
[[require]]
name = "wordram"
git = "https://github.com/mahdi-jfri/WordRam.git"
rev = "main"
```

and `import WordRAM`. The package uses Lean `v4.35.0-rc3` and Mathlib at commit `b63f6e8`;
a project that requires it must use the same versions.

To build it on its own:

```sh
lake exe cache get
lake build
```

Every declaration uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## License

Apache 2.0; see `LICENSE`.
