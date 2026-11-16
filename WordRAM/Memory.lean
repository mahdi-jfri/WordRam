module

public import WordRAM.Contract

/-!
# Memory and module placement lemmas

This file provides framing, splitting, concatenation, and update lemmas for `ListAt` and
`ZeroFrom`, along with lookup lemmas for `Program.HasAt`.

* `ListAt`: splitting and joining (`listAt_cons`, `listAt_append`, `ListAt.take`, `ListAt.drop`),
  persistence across stores elsewhere (`ListAt.update_outside`, `ListAt.update_lt`,
  `ListAt.update_ge`, `ListAt.of_agree_below`), point updates (`ListAt.set`, `ListAt.snoc`),
  and uniqueness (`ListAt.ext`).
* `ZeroFrom`: monotonicity (`ZeroFrom.mono`), persistence across stores below `h`
  (`ZeroFrom.update_lt`), extending past a store (`ZeroFrom.update_at`, `ZeroFrom.update_head`),
  and zero-filled slices (`ZeroFrom.listAt_replicate`, `ZeroFrom.of_listAt_zeros`).
* `Program.HasAt`: indexing procedure bodies (`Program.HasAt.get`, `Program.HasAt.head`).
-/

public section

namespace WordRAM

/-! ### `Program.HasAt` -/

theorem Program.HasAt.get {p : Program} {b : ℕ} {bodies : List Stmt}
    (h : p.HasAt b bodies) {i : ℕ} (hi : i < bodies.length) :
    p.procs[b + i]? = some bodies[i] :=
  h i hi

theorem Program.HasAt.head {p : Program} {b : ℕ} {body : Stmt} {rest : List Stmt}
    (h : p.HasAt b (body :: rest)) : p.procs[b]? = some body := by
  have h0 := h 0 (by simp)
  simpa using h0

/-! ### `ListAt` -/

@[simp]
theorem listAt_nil (mem : ℕ → ℕ) (a : ℕ) : ListAt mem a [] := by
  intro i hi
  simp at hi

theorem listAt_singleton {mem : ℕ → ℕ} {a x : ℕ} :
    ListAt mem a [x] ↔ mem a = x := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h i hi
    simp only [List.length_singleton, Nat.lt_one_iff] at hi
    subst hi
    simpa using h

theorem listAt_cons {mem : ℕ → ℕ} {a x : ℕ} {xs : List ℕ} :
    ListAt mem a (x :: xs) ↔ mem a = x ∧ ListAt mem (a + 1) xs := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have h0 := h 0 (by simp)
      simpa using h0
    · intro i hi
      have h' := h (i + 1) (by simpa using Nat.succ_lt_succ hi)
      rw [List.getElem_cons_succ] at h'
      rwa [show a + (i + 1) = a + 1 + i by omega] at h'
  · rintro ⟨hx, hxs⟩ i hi
    cases i with
    | zero => simpa using hx
    | succ i =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
      rw [List.getElem_cons_succ, show a + (i + 1) = a + 1 + i by omega]
      exact hxs i hi

theorem listAt_append {mem : ℕ → ℕ} {a : ℕ} {l₁ l₂ : List ℕ} :
    ListAt mem a (l₁ ++ l₂) ↔ ListAt mem a l₁ ∧ ListAt mem (a + l₁.length) l₂ := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have h' := h i (by simp [Nat.lt_add_right l₂.length hi])
      rwa [List.getElem_append_left hi] at h'
    · intro i hi
      have h' := h (l₁.length + i) (by simp [hi])
      rw [← Nat.add_assoc, List.getElem_append_right (Nat.le_add_right _ _)] at h'
      simpa [Nat.add_sub_cancel_left] using h'
  · rintro ⟨h₁, h₂⟩ i hi
    by_cases hlt : i < l₁.length
    · rw [List.getElem_append_left hlt]
      exact h₁ i hlt
    · have hle : l₁.length ≤ i := Nat.not_lt.mp hlt
      rw [List.getElem_append_right hle]
      have hi₂ : i - l₁.length < l₂.length := by
        rw [List.length_append] at hi
        omega
      have h' := h₂ (i - l₁.length) hi₂
      rwa [show a + l₁.length + (i - l₁.length) = a + i by omega] at h'

theorem ListAt.getElem {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {i : ℕ} (hi : i < l.length) :
    mem (a + i) = l[i] :=
  h i hi

theorem ListAt.getElem_of_eq {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {k i : ℕ} (hk : k = a + i) (hi : i < l.length) :
    mem k = l[i] := by
  subst hk
  exact h i hi

theorem ListAt.take {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) (k : ℕ) : ListAt mem a (l.take k) := by
  intro i hi
  rw [List.length_take] at hi
  have hi_l : i < l.length := lt_of_lt_of_le hi (Nat.min_le_right _ _)
  rw [List.getElem_take]
  exact h i hi_l

theorem ListAt.drop {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) (k : ℕ) : ListAt mem (a + k) (l.drop k) := by
  intro i hi
  rw [List.length_drop] at hi
  rw [List.getElem_drop, Nat.add_assoc]
  exact h (k + i) (by omega)

theorem ListAt.congr {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l)
    (heq : ∀ k, a ≤ k → k < a + l.length → mem' k = mem k) :
    ListAt mem' a l := by
  intro i hi
  rw [heq (a + i) (by omega) (by omega)]
  exact h i hi

theorem ListAt.of_agree_below {mem mem' : ℕ → ℕ} {a h₀ : ℕ} {l : List ℕ}
    (h : ListAt mem a l) (hb : a + l.length ≤ h₀)
    (heq : ∀ k < h₀, mem' k = mem k) :
    ListAt mem' a l :=
  h.congr fun k _ hk => heq k (lt_of_lt_of_le hk hb)

theorem ListAt.update_outside {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {x v : ℕ} (hx : x < a ∨ a + l.length ≤ x) :
    ListAt (Function.update mem x v) a l :=
  h.congr fun k hk₁ hk₂ => Function.update_of_ne (by omega) v mem

theorem ListAt.update_lt {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {x v : ℕ} (hx : x < a) :
    ListAt (Function.update mem x v) a l :=
  h.update_outside (Or.inl hx)

theorem ListAt.update_ge {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {x v : ℕ} (hx : a + l.length ≤ x) :
    ListAt (Function.update mem x v) a l :=
  h.update_outside (Or.inr hx)

theorem ListAt.set {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {i v : ℕ} (hi : i < l.length) :
    ListAt (Function.update mem (a + i) v) a (l.set i v) := by
  intro j hj
  rw [List.length_set] at hj
  by_cases hji : j = i
  · subst hji
    simp [List.getElem_set_self (h := hj)]
  · rw [Function.update_of_ne (by omega), List.getElem_set_ne (Ne.symm hji)]
    exact h j hj

theorem ListAt.set_eq {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) {x i v : ℕ} (hx : x = a + i) (hi : i < l.length) :
    ListAt (Function.update mem x v) a (l.set i v) := by
  subst hx
  exact h.set hi

theorem ListAt.snoc {mem : ℕ → ℕ} {a : ℕ} {l : List ℕ}
    (h : ListAt mem a l) (x : ℕ) :
    ListAt (Function.update mem (a + l.length) x) a (l ++ [x]) := by
  rw [listAt_append]
  refine ⟨h.update_ge le_rfl, listAt_singleton.mpr ?_⟩
  simp

theorem ListAt.ext {mem : ℕ → ℕ} {a : ℕ} {l₁ l₂ : List ℕ}
    (h₁ : ListAt mem a l₁) (h₂ : ListAt mem a l₂) (hlen : l₁.length = l₂.length) :
    l₁ = l₂ := by
  refine List.ext_getElem hlen fun i hi₁ hi₂ => ?_
  rw [← h₁ i hi₁, h₂ i hi₂]

theorem listAt_replicate {mem : ℕ → ℕ} {a n v : ℕ} :
    ListAt mem a (List.replicate n v) ↔ ∀ i < n, mem (a + i) = v := by
  constructor
  · intro h i hi
    have h' := h i (by simpa using hi)
    simpa [List.getElem_replicate] using h'
  · intro h i hi
    rw [List.length_replicate] at hi
    rw [List.getElem_replicate]
    exact h i hi

theorem ListAt.words_lt {mem : ℕ → ℕ} {a w : ℕ} {l : List ℕ}
    (h : ListAt mem a l) (hw : ∀ x ∈ l, x < 2 ^ w) {i : ℕ} (hi : i < l.length) :
    mem (a + i) < 2 ^ w := by
  rw [h i hi]
  exact hw _ (List.getElem_mem hi)

/-! ### `ZeroFrom` -/

theorem ZeroFrom.get {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) {a : ℕ} (ha : h ≤ a) : mem a = 0 :=
  hz a ha

theorem ZeroFrom.mono {mem : ℕ → ℕ} {h h' : ℕ}
    (hz : ZeroFrom mem h) (hle : h ≤ h') : ZeroFrom mem h' :=
  fun a ha => hz a (le_trans hle ha)

theorem ZeroFrom.congr {mem mem' : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) (heq : ∀ a, h ≤ a → mem' a = mem a) : ZeroFrom mem' h :=
  fun a ha => (heq a ha).trans (hz a ha)

theorem ZeroFrom.update_lt {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) {x v : ℕ} (hx : x < h) :
    ZeroFrom (Function.update mem x v) h := by
  intro a ha
  rw [Function.update_of_ne (by omega)]
  exact hz a ha

theorem ZeroFrom.update_at {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) (x v : ℕ) :
    ZeroFrom (Function.update mem x v) (max h (x + 1)) := by
  intro a ha
  rw [Function.update_of_ne (by omega)]
  exact hz a (le_trans (le_max_left _ _) ha)

theorem ZeroFrom.update_head {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) (v : ℕ) :
    ZeroFrom (Function.update mem h v) (h + 1) := by
  simpa using hz.update_at h v

theorem ZeroFrom.update_zero {mem : ℕ → ℕ} {h : ℕ}
    (hz : ZeroFrom mem h) (x : ℕ) :
    ZeroFrom (Function.update mem x 0) h := by
  intro a ha
  by_cases hax : a = x
  · subst hax; simp
  · rw [Function.update_of_ne hax]
    exact hz a ha

theorem ZeroFrom.listAt_replicate {mem : ℕ → ℕ} {h a n : ℕ}
    (hz : ZeroFrom mem h) (ha : h ≤ a) :
    ListAt mem a (List.replicate n 0) :=
  WordRAM.listAt_replicate.mpr fun i _ => hz (a + i) (by omega)

theorem ZeroFrom.of_listAt_zeros {mem : ℕ → ℕ} {h n : ℕ}
    (hl : ListAt mem h (List.replicate n 0)) (hz : ZeroFrom mem (h + n)) :
    ZeroFrom mem h := by
  intro a ha
  by_cases hlt : a < h + n
  · have h' := hl (a - h) (by rw [List.length_replicate]; omega)
    rw [List.getElem_replicate, show h + (a - h) = a by omega] at h'
    exact h'
  · exact hz a (Nat.not_lt.mp hlt)

end WordRAM
