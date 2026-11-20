module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import Mathlib.Topology.Subpath

@[expose] public section

/-! # Induction over paths subordinate to an open cover

A property of paths which is invariant under endpoint-fixed homotopy and
closed under concatenation can be checked on paths in single cover members.
This proves the generation part of the open-cover argument; it makes no
claim about the relations between those generators.
-/

namespace FiniteChains.OpenCoverPaths

open Set
open scoped unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X]

theorem property_cast_iff (P : ∀ {a b : X}, Path a b → Prop)
    {a b a' b' : X} (p : Path a b) (ha : a' = a) (hb : b' = b) :
    P (p.cast ha hb) ↔ P p := by
  subst a'; subst b'
  rfl

theorem path_induction {ι : Type v} (U : ι → Set X)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (P : ∀ {a b : X}, Path a b → Prop)
    (hrefl : ∀ a, P (Path.refl a))
    (htrans : ∀ {a b c} (p : Path a b) (q : Path b c), P p → P q → P (p.trans q))
    (hhomotopy : ∀ {a b} {p q : Path a b}, p.Homotopic q → P p → P q)
    (hlocal : ∀ {a b} (p : Path a b), (∃ i, Set.range p ⊆ U i) → P p)
    {a b : X} (p : Path a b) : P p := by
  obtain ⟨t, h₀, ht, ⟨n, h₁⟩, hU'⟩ := exists_monotone_Icc_subset_open_cover_unitInterval
    (fun i => (hU i).preimage p.continuous) (fun s _ => mem_iUnion.mpr (hcover (p s)))
  have h (k : ℕ) : P (p.subpath (t 0) (t k)) := by
    induction k with
    | zero => simpa using hrefl (p (t 0))
    | succ k ih =>
      apply hhomotopy (Path.Homotopic.subpath_trans_subpath p _ _ _) (htrans _ _ ih ?_)
      obtain ⟨i, hi⟩ := hU' k
      exact hlocal _ ⟨i, by
        rw [p.range_subpath_of_le _ _ (ht (Nat.le_succ k)), image_subset_iff]
        exact hi⟩
  have hn := h n
  rw [h₀, h₁ n le_rfl, Path.subpath_zero_one] at hn
  exact (property_cast_iff P p p.source p.target).mp hn

end FiniteChains.OpenCoverPaths
