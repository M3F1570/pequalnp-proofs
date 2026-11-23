import Mathlib
import PEqualNP.Defs

/-!
  The edge function of the paw (edges 01, 02, 12, 03) has fan-in-two AND/OR/NOT circuits with
  `s` gates exactly when `5 ≤ s`.

  Upper bound: `x0 ∧ (x1 ∨ x2 ∨ x3) ∨ x1 ∧ x2`, five gates.

  Lower bound: every wire is tracked on seven fixed input rows as a bit table (bit `k` is its
  value on row `k`). The table of a gate is determined by the tables of the wires it reads, so the
  tables reachable with at most four gates are enumerated by a checked search (`good`), which
  finds no wire whose table is the table of the paw function.
-/

namespace PEqualNP.Outside.L_meta_138_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- The paw edge function. -/
def f : (Fin 4 → Bool) → Bool :=
  fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)

/-! Rows and tables -/

/-- Number of rows used. -/
def m : ℕ := 7

/-- The rows: row `k` is the input whose bit `i` is `testBit (R.getD k 0) i`. -/
def R : List ℕ := [1, 2, 3, 4, 5, 6, 9]

/-- The all-ones table. -/
def M : ℕ := 127

/-- The tables of the four input wires. -/
def S0 : List ℕ := [85, 38, 56, 64]

/-- The table of `f`. -/
def T : ℕ := 116

/-- The input on row `k`. -/
def row (k : ℕ) : Fin 4 → Bool := fun i => (R.getD k 0).testBit i

/-- The table of a gate from the tables it reads. -/
def tv : GateOp → List ℕ → ℕ
  | .and, [] => M
  | .and, [a] => a
  | .and, [a, b] => a &&& b
  | .or, [] => 0
  | .or, [a] => a
  | .or, [a, b] => a ||| b
  | .not, l => M ^^^ l.headD 0
  | _, _ => 0

/-- One gate added to a list of wire tables. -/
def step (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [tv g.op (g.inputs.map fun i => w.getD i 0)]

/-- The gates allowed by `FanInTwo`. -/
def ok (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

/-! Bits of gate tables -/

theorem M_bit (k : ℕ) (hk : k < m) : M.testBit k = true := by
  simp only [m] at hk
  interval_cases k <;> decide

theorem tv_bit (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (l : List ℕ)
    (hl : l.length ≤ 2) (k : ℕ) (hk : k < m) :
    (tv op l).testBit k = op.eval (l.map fun a => a.testBit k) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [tv, GateOp.eval, M_bit k hk]
  · rcases hop with rfl | rfl | rfl <;> simp [tv, GateOp.eval, Nat.testBit_xor, M_bit k hk]
  · rcases hop with rfl | rfl | rfl <;>
      simp [tv, GateOp.eval, Nat.testBit_land, Nat.testBit_lor, Nat.testBit_xor, M_bit k hk]
  · simp at hl

theorem getD_snoc {α : Type} (l : List α) (x d : α) (i : ℕ) :
    (l ++ [x]).getD i d = if i < l.length then l.getD i d else if i = l.length then x else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    have : i - l.length ≠ 0 := by omega
    simp [List.getElem?_singleton, this]

/-- On row `k`, every Boolean wire is bit `k` of the matching table. -/
theorem wires_bit (k : ℕ) (hk : k < m) :
    ∀ (gs : List Gate) (w : List Bool) (wt : List ℕ), (∀ g ∈ gs, ok g) →
      w.length = wt.length → (∀ i, w.getD i false = (wt.getD i 0).testBit k) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
          i false = ((gs.foldl step wt).getD i 0).testBit k := by
  intro gs
  induction gs with
  | nil => intro w wt _ _ h i; exact h i
  | cons g gs ih =>
    intro w wt hok hlen h
    simp only [List.foldl_cons]
    apply ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · intro i
      have hg := hok g (List.mem_cons_self ..)
      have hmap : g.inputs.map (fun i => w.getD i false)
          = (g.inputs.map fun i => wt.getD i 0).map fun a => a.testBit k := by
        rw [List.map_map]
        exact List.map_congr_left (fun i _ => h i)
      rw [step, getD_snoc, getD_snoc, hlen]
      split_ifs
      · exact h i
      · rw [tv_bit g.op hg.1 _ (by simpa using hg.2) k hk, hmap]
      · simp

/-! The search -/

/-- All `a &&& b` and `a ||| b` for `a`, `b` in the list. -/
def pairsUp : List ℕ → List ℕ
  | [] => []
  | a :: t => (a :: t).flatMap (fun b => [a &&& b, a ||| b]) ++ pairsUp t

/-- Every table one allowed gate can produce from the tables `S` (and the missing wire, `0`). -/
def opts (S : List ℕ) : List ℕ :=
  [M, 0] ++ (0 :: S).map (M ^^^ ·) ++ (0 :: S) ++ pairsUp (0 :: S)

/-- One more gate on the tables `S` cannot produce `T`. -/
def leaf (S : List ℕ) : Bool :=
  T != M && T != 0 && (0 :: S).all fun c => (M ^^^ c) != T && c != T &&
    (c &&& T != T || (0 :: S).all fun d => c &&& d != T) &&
    (c ||| T != T || (0 :: S).all fun d => c ||| d != T)

/-- Two more gates on the tables `S` cannot produce `T`. -/
def two (S : List ℕ) : Bool :=
  leaf S && (opts S).all fun a => a != (M ^^^ T) &&
    (a &&& T != T || (0 :: (S ++ [a])).all fun c => a &&& c != T) &&
    (a ||| T != T || (0 :: (S ++ [a])).all fun c => a ||| c != T)

/-- At most `k` more gates on the tables `S` cannot produce `T`. Tables already present are not
  added again. -/
def good : List ℕ → ℕ → Bool
  | _, 0 => true
  | S, 1 => leaf S
  | S, 2 => two S
  | S, k + 3 => (opts S).all fun a => a != T && (S.contains a || good (S ++ [a]) (k + 2))

theorem mem_pairsUp : ∀ (L : List ℕ) (a b : ℕ), a ∈ L → b ∈ L →
    a &&& b ∈ pairsUp L ∧ a ||| b ∈ pairsUp L := by
  intro L
  induction L with
  | nil => intro a b ha; simp at ha
  | cons c t ih =>
    intro a b ha hb
    simp only [pairsUp, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false]
    rcases List.mem_cons.1 ha with rfl | ha'
    · exact ⟨Or.inl ⟨b, List.mem_cons.1 hb, Or.inl rfl⟩,
             Or.inl ⟨b, List.mem_cons.1 hb, Or.inr rfl⟩⟩
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact ⟨Or.inl ⟨a, List.mem_cons.1 ha, Or.inl (Nat.land_comm _ _)⟩,
               Or.inl ⟨a, List.mem_cons.1 ha, Or.inr (Nat.lor_comm _ _)⟩⟩
      · exact ⟨Or.inr (ih a b ha' hb').1, Or.inr (ih a b ha' hb').2⟩

theorem pairsUp_cases : ∀ (L : List ℕ) (x : ℕ), x ∈ pairsUp L →
    ∃ c ∈ L, ∃ d ∈ L, x = c &&& d ∨ x = c ||| d := by
  intro L
  induction L with
  | nil => intro x hx; simp [pairsUp] at hx
  | cons c t ih =>
    intro x hx
    simp only [pairsUp, List.mem_append, List.mem_flatMap, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with ⟨b, hb, h⟩ | hx
    · exact ⟨c, List.mem_cons_self .., b, List.mem_cons.2 hb, h⟩
    · obtain ⟨c', hc', d, hd, h⟩ := ih x hx
      exact ⟨c', List.mem_cons_of_mem _ hc', d, List.mem_cons_of_mem _ hd, h⟩

theorem and_absorb (c d : ℕ) : c &&& (c &&& d) = c &&& d := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases Nat.testBit c i <;> cases Nat.testBit d i <;> rfl
theorem and_absorb' (c d : ℕ) : d &&& (c &&& d) = c &&& d := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_land]
  cases Nat.testBit c i <;> cases Nat.testBit d i <;> rfl
theorem or_absorb (c d : ℕ) : c ||| (c ||| d) = c ||| d := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases Nat.testBit c i <;> cases Nat.testBit d i <;> rfl
theorem or_absorb' (c d : ℕ) : d ||| (c ||| d) = c ||| d := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_lor]
  cases Nat.testBit c i <;> cases Nat.testBit d i <;> rfl
theorem xor_cancel (a b : ℕ) : a ^^^ (a ^^^ b) = b := by
  apply Nat.eq_of_testBit_eq; intro i; simp only [Nat.testBit_xor]
  cases Nat.testBit a i <;> cases Nat.testBit b i <;> rfl

theorem memM (S : List ℕ) : M ∈ opts S := by simp [opts]
theorem mem0 (S : List ℕ) : 0 ∈ opts S := by simp [opts]
theorem memW {S : List ℕ} {c : ℕ} (hc : c ∈ 0 :: S) : c ∈ opts S := by
  simp only [opts, List.mem_append]; exact Or.inl (Or.inr hc)
theorem memX {S : List ℕ} {c : ℕ} (hc : c ∈ 0 :: S) : M ^^^ c ∈ opts S := by
  simp only [opts, List.mem_append, List.mem_map]
  exact Or.inl (Or.inl (Or.inr ⟨c, hc, rfl⟩))
theorem memAnd {S : List ℕ} {c d : ℕ} (hc : c ∈ 0 :: S) (hd : d ∈ 0 :: S) :
    c &&& d ∈ opts S := by
  simp only [opts, List.mem_append]; exact Or.inr (mem_pairsUp _ c d hc hd).1
theorem memOr {S : List ℕ} {c d : ℕ} (hc : c ∈ 0 :: S) (hd : d ∈ 0 :: S) :
    c ||| d ∈ opts S := by
  simp only [opts, List.mem_append]; exact Or.inr (mem_pairsUp _ c d hc hd).2

theorem opts_cases {S : List ℕ} {x : ℕ} (hx : x ∈ opts S) :
    x = M ∨ x = 0 ∨ (∃ c ∈ 0 :: S, x = M ^^^ c) ∨ x ∈ 0 :: S ∨
      ∃ c ∈ 0 :: S, ∃ d ∈ 0 :: S, x = c &&& d ∨ x = c ||| d := by
  simp only [opts, List.mem_append, List.mem_map] at hx
  rcases hx with ((hx | ⟨c, hc, rfl⟩) | hx) | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hx)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (pairsUp_cases _ x hx))))

theorem tv_mem (op : GateOp) (hop : op = .and ∨ op = .or ∨ op = .not) (S : List ℕ)
    (l : List ℕ) (hl : l.length ≤ 2) (hS : ∀ a ∈ l, a ∈ 0 :: S) : tv op l ∈ opts S := by
  have h0 : (0 : ℕ) ∈ 0 :: S := List.mem_cons_self ..
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact memM S
    · exact mem0 S
    · simpa [tv] using memX h0
  · have ha := hS a (by simp)
    rcases hop with rfl | rfl | rfl
    · exact memW ha
    · exact memW ha
    · simpa [tv] using memX ha
  · have ha := hS a (by simp)
    have hb := hS b (by simp)
    rcases hop with rfl | rfl | rfl
    · exact memAnd ha hb
    · exact memOr ha hb
    · simpa [tv] using memX ha
  · simp at hl

theorem leaf_sound (S : List ℕ) (h : leaf S = true) : ∀ x ∈ opts S, x ≠ T := by
  simp only [leaf, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨hTM, hT0⟩, hall⟩ := h
  intro x hx
  rcases opts_cases hx with rfl | rfl | ⟨c, hc, rfl⟩ | hc | ⟨c, hc, d, hd, rfl | rfl⟩
  · exact fun h => hTM h.symm
  · exact fun h => hT0 h.symm
  · exact (hall c hc).1.1.1
  · exact (hall x hc).1.1.2
  · intro h
    rcases (hall c hc).1.2 with h1 | h1
    · apply h1; rw [← h, and_absorb]
    · exact h1 d hd h
  · intro h
    rcases (hall c hc).2 with h1 | h1
    · apply h1; rw [← h, or_absorb]
    · exact h1 d hd h

theorem two_sound (S : List ℕ) (h : two S = true) :
    ∀ a ∈ opts S, ∀ x ∈ opts (S ++ [a]), x ≠ T := by
  simp only [two, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq,
    Bool.or_eq_true] at h
  obtain ⟨hleaf, hall⟩ := h
  have hl := leaf_sound S hleaf
  intro a ha x hx
  obtain ⟨⟨haX, hA⟩, hO⟩ := hall a ha
  have hW : ∀ c ∈ 0 :: (S ++ [a]), c ∈ 0 :: S ∨ c = a := by
    intro c hc
    simp only [List.mem_cons, List.mem_append, List.mem_singleton] at hc ⊢
    tauto
  rcases opts_cases hx with rfl | rfl | ⟨c, hc, rfl⟩ | hc | ⟨c, hc, d, hd, rfl | rfl⟩
  · exact hl _ (memM S)
  · exact hl _ (mem0 S)
  · rcases hW c hc with hc' | hca
    · exact hl _ (memX hc')
    · subst hca
      intro h
      apply haX
      rw [← h, xor_cancel]
  · rcases hW x hc with hc' | hxa
    · exact hl _ (memW hc')
    · subst hxa; exact hl _ ha
  · rcases hW c hc with hc' | hca
    · rcases hW d hd with hd' | hda
      · exact hl _ (memAnd hc' hd')
      · subst hda
        intro h
        rcases hA with h1 | h1
        · apply h1; rw [← h, and_absorb']
        · exact h1 c hc (by rw [Nat.land_comm]; exact h)
    · subst hca
      intro h
      rcases hA with h1 | h1
      · apply h1; rw [← h, and_absorb]
      · exact h1 d hd h
  · rcases hW c hc with hc' | hca
    · rcases hW d hd with hd' | hda
      · exact hl _ (memOr hc' hd')
      · subst hda
        intro h
        rcases hO with h1 | h1
        · apply h1; rw [← h, or_absorb']
        · exact h1 c hc (by rw [Nat.lor_comm]; exact h)
    · subst hca
      intro h
      rcases hO with h1 | h1
      · apply h1; rw [← h, or_absorb]
      · exact h1 d hd h

theorem step_mem (g : Gate) (hg : ok g) (S wt : List ℕ) (hw : ∀ x ∈ wt, x ∈ S) :
    tv g.op (g.inputs.map fun i => wt.getD i 0) ∈ opts S := by
  apply tv_mem g.op hg.1 S _ (by simpa using hg.2)
  intro b hb
  simp only [List.mem_map] at hb
  obtain ⟨i, -, rfl⟩ := hb
  simp only [List.getD_eq_getElem?_getD]
  cases h : wt[i]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (hw v (List.mem_of_getElem? h))

theorem mem_step {wt : List ℕ} {g : Gate} {x : ℕ} :
    x ∈ step wt g ↔ x ∈ wt ∨ x = tv g.op (g.inputs.map fun i => wt.getD i 0) := by
  simp [step]

theorem one_safe (S wt : List ℕ) (gs : List Gate) (hS : ∀ x ∈ opts S, x ≠ T)
    (hw : ∀ x ∈ wt, x ∈ S) (hT : T ∉ S) (hk : gs.length ≤ 1) (hok : ∀ g ∈ gs, ok g) :
    ∀ y ∈ gs.foldl step wt, y ≠ T := by
  match gs, hk, hok with
  | [], _, _ => intro y hy h; exact hT (h ▸ hw y hy)
  | [g], _, hok =>
    intro y hy
    simp only [List.foldl_cons, List.foldl_nil] at hy
    rcases mem_step.1 hy with hy | rfl
    · intro h; exact hT (h ▸ hw y hy)
    · exact hS _ (step_mem g (hok g (by simp)) S wt hw)
  | _ :: _ :: _, hk, _ => simp at hk

theorem sound : ∀ (gs : List Gate) (k : ℕ) (S wt : List ℕ), good S k = true →
    (∀ x ∈ wt, x ∈ S) → T ∉ S → gs.length ≤ k → (∀ g ∈ gs, ok g) →
    ∀ y ∈ gs.foldl step wt, y ≠ T := by
  intro gs
  induction gs with
  | nil => intro k S wt _ hw hT _ _ y hy h; exact hT (h ▸ hw y hy)
  | cons g gs ih =>
    intro k S wt hgood hw hT hk hok
    have hg := hok g (List.mem_cons_self ..)
    have hok' : ∀ g' ∈ gs, ok g' := fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')
    have hmem := step_mem g hg S wt hw
    match k, hgood, hk with
    | 0, _, hk => simp at hk
    | 1, hgood, hk => exact one_safe S wt (g :: gs) (leaf_sound S hgood) hw hT hk hok
    | 2, hgood, hk =>
      have h2 : two S = true := hgood
      have hleaf : leaf S = true := by
        simp only [two, Bool.and_eq_true] at h2; exact h2.1
      have hl := leaf_sound S hleaf
      simp only [List.foldl_cons]
      apply one_safe _ (step wt g) gs (two_sound S h2 _ hmem) _ _ (by simp at hk; omega) hok'
      · intro x hx
        simp only [List.mem_append, List.mem_singleton]
        rcases mem_step.1 hx with hx | hx
        · exact Or.inl (hw x hx)
        · exact Or.inr hx
      · simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hT, fun h => hl _ hmem h.symm⟩
    | k + 3, hgood, hk =>
      have hg3 : good S (k + 3) = (opts S).all fun a =>
          a != T && (S.contains a || good (S ++ [a]) (k + 2)) := rfl
      have hgood' := hgood
      rw [hg3] at hgood'
      simp only [List.all_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true,
        List.contains_iff_mem] at hgood'
      obtain ⟨haT, hrest⟩ := hgood' _ hmem
      have hk' : gs.length ≤ k + 2 := by simp at hk; omega
      simp only [List.foldl_cons]
      rcases hrest with hin | hnext
      · apply ih (k + 3) S (step wt g) hgood _ hT (by omega) hok'
        intro x hx
        rcases mem_step.1 hx with hx | rfl
        · exact hw x hx
        · exact hin
      · apply ih (k + 2) _ (step wt g) hnext _ _ hk' hok'
        · intro x hx
          simp only [List.mem_append, List.mem_singleton]
          rcases mem_step.1 hx with hx | hx
          · exact Or.inl (hw x hx)
          · exact Or.inr hx
        · simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hT, fun h => haT h.symm⟩

/-! Bounds -/

theorem tv_lt (op : GateOp) (l : List ℕ) (hl : ∀ a ∈ l, a < 2 ^ m) : tv op l < 2 ^ m := by
  have hM : M < 2 ^ m := by decide
  have h0 : (0 : ℕ) < 2 ^ m := by positivity
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · cases op <;> first | exact hM | exact h0
  · have ha : a < 2 ^ m := hl a (List.mem_cons_self ..)
    cases op <;> first | exact ha | exact h0 | exact Nat.xor_lt_two_pow hM ha
  · have ha : a < 2 ^ m := hl a (List.mem_cons_self ..)
    have hb : b < 2 ^ m := hl b (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    cases op <;> first
      | exact Nat.and_lt_two_pow _ hb
      | exact Nat.or_lt_two_pow ha hb
      | exact Nat.xor_lt_two_pow hM ha
      | exact h0
  · have ha : a < 2 ^ m := hl a (List.mem_cons_self ..)
    cases op <;> first | exact h0 | exact Nat.xor_lt_two_pow hM ha

theorem bound : ∀ (gs : List Gate) (wt : List ℕ), (∀ x ∈ wt, x < 2 ^ m) →
    ∀ y ∈ gs.foldl step wt, y < 2 ^ m := by
  intro gs
  induction gs with
  | nil => intro wt h; exact h
  | cons g gs ih =>
    intro wt hw
    apply ih
    intro x hx
    rcases mem_step.1 hx with hx | rfl
    · exact hw x hx
    · apply tv_lt
      intro b hb
      simp only [List.mem_map] at hb
      obtain ⟨i, -, rfl⟩ := hb
      simp only [List.getD_eq_getElem?_getD]
      cases h : wt[i]? with
      | none => simp
      | some v => exact hw v (List.mem_of_getElem? h)

/-! Finite facts -/

theorem good4 : good S0 4 = true := by decide +kernel

theorem S0_bits : ∀ k < m, ∀ i : ℕ,
    (List.ofFn (row k)).getD i false = (S0.getD i 0).testBit k := by
  intro k hk i
  simp only [m] at hk
  rcases Nat.lt_or_ge i 4 with hi | hi
  · interval_cases k <;> interval_cases i <;> decide
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp [S0]; omega)]
    simp

theorem T_bits : ∀ k < m, f (row k) = T.testBit k := by
  intro k hk
  simp only [m] at hk
  interval_cases k <;> decide

theorem T_ne : T ∉ S0 := by decide

theorem T_ne_zero : T ≠ 0 := by decide

theorem T_lt : T < 2 ^ m := by decide

theorem S0_lt : ∀ x ∈ S0, x < 2 ^ m := by decide

/-! The two directions -/

theorem lower (C : Circuit) (hC : FanInTwo C) (hs : C.size ≤ 4)
    (hf : ∀ x : Fin 4 → Bool, C.eval (List.ofFn x) = f x) : False := by
  have hok : ∀ g ∈ C.gates, ok g := by
    intro g hg
    have := hC g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
    exact this
  have hbits : ∀ k < m, ((C.gates.foldl step S0).getD C.output 0).testBit k = T.testBit k := by
    intro k hk
    have := hf (row k)
    rw [T_bits k hk] at this
    rw [← this, Circuit.eval, Circuit.wires]
    exact (wires_bit k hk C.gates _ S0 hok (by simp [S0]) (S0_bits k hk) C.output).symm
  have hylt : (C.gates.foldl step S0).getD C.output 0 < 2 ^ m := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : (C.gates.foldl step S0)[C.output]? with
    | none => simp
    | some v => exact bound _ _ S0_lt v (List.mem_of_getElem? h)
  have hyT : (C.gates.foldl step S0).getD C.output 0 = T := by
    apply Nat.eq_of_testBit_eq
    intro i
    rcases Nat.lt_or_ge i m with hi | hi
    · exact hbits i hi
    · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hylt (Nat.pow_le_pow_right (by norm_num) hi)),
        Nat.testBit_lt_two_pow (lt_of_lt_of_le T_lt (Nat.pow_le_pow_right (by norm_num) hi))]
  simp only [List.getD_eq_getElem?_getD] at hyT
  cases h : (C.gates.foldl step S0)[C.output]? with
  | none => rw [h] at hyT; exact T_ne_zero (by simpa using hyT.symm)
  | some v =>
    rw [h] at hyT
    exact sound C.gates 4 S0 S0 good4 (fun x hx => hx) T_ne hs hok v
      (List.mem_of_getElem? h) (by simpa using hyT)

/-- `x0 ∧ (x1 ∨ x2 ∨ x3) ∨ x1 ∧ x2`. -/
def C5 : Circuit :=
  { gates := [⟨.or, [1, 2]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩],
    output := 8 }

theorem upper : HasCircuitSize 4 f 5 := by
  refine ⟨C5, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C5, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
  · decide

end PEqualNP.Outside.L_meta_138_aux

open PEqualNP.Outside.L_meta_138_aux in
theorem PEqualNP.Outside.L_meta_138 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 4 (fun x : Fin 4 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2) || (x 0 && x 3)) s ↔ 5 ≤ s := by
  intro s
  constructor
  · rintro ⟨C, hC, hs, hf⟩
    by_contra h
    exact lower C hC (by omega) hf
  · intro hs
    obtain ⟨C, hC, hs5, hf⟩ := upper
    exact ⟨C, hC, le_trans hs5 hs, hf⟩
