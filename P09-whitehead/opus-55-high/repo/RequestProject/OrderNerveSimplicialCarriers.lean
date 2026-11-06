import RequestProject.OrderNerveSingularInverseMap
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

noncomputable abbrev orderSimplicialBoundary (P : Type) [PartialOrder P] (n : ℕ) :=
  (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom

theorem orderSimplicialBoundary_squared n (c : ComposableArrows P (n + 2) →₀ ℤ) :
    orderSimplicialBoundary P n (orderSimplicialBoundary P (n + 1) c) = 0 := by
  apply orderNerveGradedEncode_injective n
  simp [orderNerveGradedEncode_boundary, Nerve.bdry_bdry, map_zero]

theorem orderNerveGradedEncode_length n (c : ComposableArrows P n →₀ ℤ) :
    Nerve.lengthProjection (n + 1) (orderNerveGradedEncode n c) = orderNerveGradedEncode n c := by
  lin_ind c s r =>
    simp [orderNerveGradedEncode_single, map_zsmul, Nerve.lengthProjection_of, if_pos (orderNerveVertexList_length s)]

theorem orderNerveGradedEncode_single_supported n (s : ComposableArrows P n) :
    orderNerveGradedEncode n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  rwd [orderNerveGradedEncode_single, one_smul]
  apply Nerve.of_mem_incOn (orderNerveVertexList_chain s)
  intro p hp
  exact List.mem_ofFn.mp hp

theorem orderNerveSimplexCarrier_acyclic (s : ComposableArrows P n) :
    Nerve.AcyclicIn (Set.range s.obj) := by
  apply Nerve.acyclicIn_of_subtype _ (by tauto)
  intro c hc hz
  apply orderNerve_cycle_bounds_of_comparable ⟨s.obj 0, ⟨0, rfl⟩⟩ ?_ hc hz
  rintro ⟨p, ⟨i, rfl⟩⟩
  exact Or.inr (s.monotone i.zero_le)

theorem orderNerveSimplexCarrier_face (s : ComposableArrows P (n + 1))
    i : Set.range ((nerve P).δ i s).obj ⊆ Set.range s.obj := by
  rintro p ⟨j, rfl⟩
  aesop

theorem orderSimplicialBoundary_map_carrier
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    (s : ComposableArrows P (n + 1)) :
    f (orderSimplicialBoundary P n (Finsupp.single s 1)) ∈ Nerve.IncOn (Set.range s.obj) := by
  rwd [mathlibOrderNerve_d_single, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  rwd [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderNerveSimplexCarrier_face s i hp) (hf _)

theorem orderSimplicialMap_mem_inc
    (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
    c : f c ∈ Nerve.Inc P := by
  lin_ind c with c d hc hd => simpa [map_add] using (Nerve.Inc P).add_mem hc hd
  | s r =>
    rwd [show Finsupp.single s r = r • Finsupp.single s 1 by simp, map_smul]
    exact (Nerve.Inc P).zsmul_mem (Nerve.incOn_le_inc _ (hf s)) r
