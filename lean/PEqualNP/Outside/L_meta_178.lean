import Mathlib
import PEqualNP.Defs

/-!
L-meta-178. A graph `H` that embeds (as an induced subgraph) into a labelled `2k`-fold
subdivision `Gh` inherits the girth bound of `Gh`, and every vertex of `H` with three distinct
neighbours is sent to a hub (a vertex at position `0`), because every vertex at a nonzero
position has exactly the two neighbours `a` and `b`.
-/

theorem PEqualNP.Outside.L_meta_178 :
    ∀ (k N : ℕ) (Gh : SimpleGraph (Fin N)) (pos : Fin N → ℕ), (∀ u v : Fin N, Gh.Adj u v → pos u ≠ 0 ∨ pos v ≠ 0) → (∀ v : Fin N, pos v ≠ 0 → pos v ≤ 2 * k ∧ ∃ a b : Fin N, (∀ w : Fin N, Gh.Adj v w ↔ w = a ∨ w = b) ∧ pos a + 1 = pos v ∧ pos b = (pos v + 1) % (2 * k + 1)) → (∀ (L : ℕ) (c : ℕ → Fin N), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → Gh.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) → ∀ (m : ℕ) (H : SimpleGraph (Fin m)) (e : RelEmbedding H.Adj Gh.Adj), (∀ (L : ℕ) (c : ℕ → Fin m), 3 ≤ L → (∀ i j : ℕ, i < L → j < L → c i = c j → i = j) → (∀ i : ℕ, i < L → H.Adj (c i) (c ((i + 1) % L))) → 6 * k + 3 ≤ L) ∧ ∀ u x y z : Fin m, H.Adj u x → H.Adj u y → H.Adj u z → x ≠ y → x ≠ z → y ≠ z → pos (e u) = 0 := by
  intro k N Gh pos _hedge hsub hcyc m H e
  refine ⟨?_, ?_⟩
  · intro L c hL hinj hadj
    refine hcyc L (fun i => e (c i)) hL ?_ ?_
    · intro i j hi hj hij
      exact hinj i j hi hj (e.injective hij)
    · intro i hi
      exact e.map_rel_iff.mpr (hadj i hi)
  · intro u x y z hx hy hz hxy hxz hyz
    by_contra hne
    obtain ⟨_, a, b, hab, _, _⟩ := hsub (e u) hne
    have hx' := (hab (e x)).mp (e.map_rel_iff.mpr hx)
    have hy' := (hab (e y)).mp (e.map_rel_iff.mpr hy)
    have hz' := (hab (e z)).mp (e.map_rel_iff.mpr hz)
    have hxy' : e x ≠ e y := fun h => hxy (e.injective h)
    have hxz' : e x ≠ e z := fun h => hxz (e.injective h)
    have hyz' : e y ≠ e z := fun h => hyz (e.injective h)
    rcases hx' with h1 | h1 <;> rcases hy' with h2 | h2 <;> rcases hz' with h3 | h3 <;>
      first
        | exact hxy' (h1.trans h2.symm)
        | exact hxz' (h1.trans h3.symm)
        | exact hyz' (h2.trans h3.symm)
