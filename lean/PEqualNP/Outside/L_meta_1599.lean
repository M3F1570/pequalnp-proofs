import Mathlib
import PEqualNP.Defs

-- If no AND gate were true at the input 1_uv, every wire true there would be true at 1_uu or
-- at 1_vv (induction on the wires: an OR gate passes a true input on, an AND gate is false).
-- Those two inputs hold no edge, so the circuit would be false at 1_uv, a contradiction. The
-- first AND gate true at 1_uv then owns uv: every AND gate below it is false there.

namespace PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_prefix (gs : List Gate) (w : List Bool) : ∃ t, gs.foldl step w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: t, ?_⟩
    rw [List.foldl_cons, ht]
    simp [step]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_prefix (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_stable (gs : List Gate) (w : List Bool) (k i : ℕ) (hi : i < w.length + k)
    (hk : k ≤ gs.length) :
    (gs.foldl step w).getD i false = ((gs.take k).foldl step w).getD i false := by
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  obtain ⟨t, ht⟩ := foldl_prefix (gs.drop k) ((gs.take k).foldl step w)
  have hlen : ((gs.take k).foldl step w).length = w.length + k := by
    rw [foldl_length, List.length_take]; omega
  conv_lhs => rw [hsplit, List.foldl_append, ht]
  exact getD_prefix _ _ _ (by omega)

lemma getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => ((gs.take j).foldl step w).getD i false) := by
  rw [getD_stable gs w (j + 1) (w.length + j) (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  have hlen : ((gs.take j).foldl step w).length = w.length + j := by
    rw [foldl_length, List.length_take]; omega
  simp only [List.foldl_cons, List.foldl_nil, step]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp [hlen]

lemma getD_out (gs : List Gate) (w : List Bool) (i : ℕ) (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [foldl_length]; omega)]
  rfl

lemma key (gs : List Gate) (a b c : List Bool) (ha : a.length = c.length)
    (hb : b.length = c.length)
    (hin : ∀ i < c.length, c.getD i false = true → a.getD i false = true ∨ b.getD i false = true)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hand : ∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and →
      (gs.foldl step c).getD (c.length + j) false = false) :
    ∀ i, (gs.foldl step c).getD i false = true →
      (gs.foldl step a).getD i false = true ∨ (gs.foldl step b).getD i false = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro h
  by_cases hi : i < c.length
  · rw [getD_stable gs c 0 i (by omega) (by omega)] at h
    rw [getD_stable gs a 0 i (by omega) (by omega), getD_stable gs b 0 i (by omega) (by omega)]
    simpa using hin i hi (by simpa using h)
  · obtain ⟨j, rfl⟩ : ∃ j, i = c.length + j := ⟨i - c.length, by omega⟩
    by_cases hj : j < gs.length
    · rcases hops gs[j] (List.getElem_mem hj) with hop | hop
      · rw [hand j hj hop] at h
        exact absurd h (by simp)
      · rw [getD_gate gs c j hj, hop] at h
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at h
        obtain ⟨k, hk, hkv⟩ := h
        have hklt : k < c.length + j := by
          by_contra hge
          have : ((gs.take j).foldl step c).getD k false = false :=
            getD_out _ _ _ (by rw [List.length_take]; omega)
          rw [this] at hkv
          exact absurd hkv (by simp)
        rw [← getD_stable gs c j k hklt (by omega)] at hkv
        have hab := ih k (by omega) hkv
        have hka : k < a.length + j := by omega
        have hkb : k < b.length + j := by omega
        rw [getD_stable gs a j k hka (by omega), getD_stable gs b j k hkb (by omega)] at hab
        have ga := getD_gate gs a j hj
        have gb := getD_gate gs b j hj
        rw [ha] at ga
        rw [hb] at gb
        rw [ga, gb, hop]
        simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
        rcases hab with h1 | h1
        · exact Or.inl ⟨k, hk, h1⟩
        · exact Or.inr ⟨k, hk, h1⟩
    · rw [getD_out gs c _ (by omega)] at h
      exact absurd h (by simp)

end PEqualNP.Outside.L_meta_1599

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership

theorem PEqualNP.Outside.L_meta_1599 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned n G C := by
  intro n G _ C hops hfun u v huv
  classical

  have hw : ∀ x : Fin n → Bool, C.wires (List.ofFn x) = C.gates.foldl PEqualNP.Outside.L_meta_1599.step (List.ofFn x) :=
    fun _ => rfl
  have hval : ∀ (x : Fin n → Bool) (j : ℕ), gateVal n C j x =
      (C.gates.foldl PEqualNP.Outside.L_meta_1599.step (List.ofFn x)).getD ((List.ofFn x).length + j) false := by
    intro x j
    simp [gateVal, hw]
  have hsingle : ∀ w : Fin n, PEqualNP.MetaComplexity.circuitFun n C (pairInput w w) = false := by
    intro w
    rw [hfun]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun, pairInput]
  have hex : ∃ j, j < C.gates.length ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.and ∧
      gateVal n C j (pairInput u v) = true := by
    by_contra hno
    push Not at hno
    have hout : PEqualNP.MetaComplexity.circuitFun n C (pairInput u v) = true := by
      rw [hfun]
      simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
        decide_eq_true_eq]
      exact Or.inr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hk := PEqualNP.Outside.L_meta_1599.key C.gates (List.ofFn (pairInput u u)) (List.ofFn (pairInput v v))
      (List.ofFn (pairInput u v)) (by simp) (by simp)
      (by
        intro i hi hc
        simp only [List.length_ofFn] at hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, Option.getD_some,
          dite_true, pairInput, decide_eq_true_eq] at hc ⊢
        rcases hc with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h))
      (fun g hg => hops g hg)
      (by
        intro j hj hop
        have h1 := hno j hj (by
          simp [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hj, hop])
        rw [hval] at h1
        simpa using h1)
      C.output (by simpa [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, hw] using hout)
    have hu := hsingle u
    have hv := hsingle v
    simp only [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, hw] at hu hv
    rcases hk with h | h
    · rw [hu] at h; exact absurd h (by simp)
    · rw [hv] at h; exact absurd h (by simp)
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).1, (Nat.find_spec hex).2.1,
    (Nat.find_spec hex).2.2, ?_⟩
  intro i hi _ hop
  by_contra hne
  have hmin := Nat.find_min hex hi
  apply hmin
  exact ⟨by have := (Nat.find_spec hex).1; omega, hop, by simpa using hne⟩
