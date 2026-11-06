module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologyPaths.PathSubdivision

@[expose] public section

/-! # Induction over paths subordinate to an open cover

A property of paths which is invariant under endpoint-fixed homotopy and
closed under concatenation can be checked on paths in single cover members.
This proves the generation part of the open-cover argument; it makes no
claim about the relations between those generators.
-/

namespace FiniteChains.OpenCoverPaths

open Set Topology CategoryTheory
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
  obtain ⟨t,N,ht0,htN,_,ht⟩ := PathSubdivision.exists_subdivision p U hU
    (fun s => hcover (p s))
  have hall : ∀ k ≤ N, P (PathSubdivision.concatenateCuts p t k) := by
    intro k
    induction k with
    | zero => intro _; exact hrefl _
    | succ k ih =>
      intro hk
      exact htrans _ _ (ih (by omega)) (hlocal _ (ht k (by omega)))
  have hend := hhomotopy (PathSubdivision.concatenateCuts_homotopic p t N) (hall N le_rfl)
  rw [ht0,htN] at hend
  have hp := hhomotopy (PathSubdivision.cut_zero_one_homotopic p) hend
  exact (property_cast_iff P p p.source p.target).mp hp

end FiniteChains.OpenCoverPaths
