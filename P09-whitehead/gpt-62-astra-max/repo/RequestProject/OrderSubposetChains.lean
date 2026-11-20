module

public import Mathlib.LinearAlgebra.Finsupp.Supported
public import RequestProject.StrictOrderChains
public import RequestProject.UnivCoverIncl

@[expose] public section

/-! Finite chains and cycles on an actual induced subposet. -/
namespace FiniteChains.Comb
universe u
variable {P : Type u} (r : P → P → Prop) [Trans r r r] (S : Set P)

local instance : Trans (fun a b : S => r a b) (fun a b : S => r a b) (fun a b : S => r a b) :=
  ⟨fun h => Trans.trans h⟩

abbrev inducedIncl : Hom (relSkeleton (fun a b : S => r a b)) (relSkeleton r) :=
  relSkeletonMap Subtype.val (fun {_ _} h => h)

theorem inducedIncl_edges : Function.Injective (inducedIncl r S).onE := by
  rintro ⟨⟨a,b⟩, h⟩ ⟨⟨c,d⟩, k⟩ e
  simpa [inducedIncl, relSkeletonMap, Subtype.ext_iff] using e

/-- Every chain supported on the induced subcomplex comes from a chain there. -/
theorem inducedIncl_lift (c : RelTriangle r →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S) :
    c ∈ LinearMap.range (chain2 (inducedIncl r S)) := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (inducedIncl r S).onF Set.univ
  simp only [Finsupp.supported_univ, Submodule.map_top, Set.image_univ] at h
  rw [chain2, h]
  intro t ht
  obtain ⟨ha,hb,hc⟩ := hs t ht
  exact ⟨⟨(⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩), t.2⟩, rfl⟩

/-- Since the inclusion is injective on edges, a lift of a cycle is itself a cycle. -/
theorem inducedIncl_cycle (c : RelTriangle r →₀ ℤ)
    (hs : ∀ t ∈ c.support, t.1.1 ∈ S ∧ t.1.2.1 ∈ S ∧ t.1.2.2 ∈ S)
    (hc : bdry2 (relSkeleton r) c = 0) :
    ∃ d, chain2 (inducedIncl r S) d = c ∧ bdry2 _ d = 0 := by
  obtain ⟨d, rfl⟩ := inducedIncl_lift r S c hs
  refine ⟨d, rfl, Finsupp.mapDomain_injective (inducedIncl_edges r S) ?_⟩
  rw [Finsupp.mapDomain_zero]
  exact (bdry2_chain2 (inducedIncl r S) d).symm.trans hc

abbrev ordSubposetIncl [PartialOrder P] := inducedIncl (· ≤ ·) S

end FiniteChains.Comb
