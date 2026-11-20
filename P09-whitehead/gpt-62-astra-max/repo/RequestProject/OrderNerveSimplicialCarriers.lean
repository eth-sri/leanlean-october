module

public import RequestProject.OrderNerveSingularInverseMap

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular
open scoped Simplicial
variable {P : Type} [PartialOrder P]

noncomputable abbrev orderSimplicialBoundary (P : Type) [PartialOrder P] (n : ℕ) :=
  (AlternatingFaceMapComplex.objD (mathlibOrderNerveModule P) n).hom

variable (n : ℕ)

theorem orderSimplicialBoundary_squared (c : ComposableArrows P _ →₀ ℤ) :
    orderSimplicialBoundary P n (orderSimplicialBoundary P (n + 1) c) = 0 := by
  apply orderNerveGradedEncode_injective n
  simp_all [orderNerveGradedEncode_boundary, Nerve.bdry_bdry]

theorem orderNerveGradedEncode_length (c : ComposableArrows P n →₀ ℤ) :
    Nerve.lengthProjection (n + 1) (orderNerveGradedEncode n c) = orderNerveGradedEncode n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp_all
  | single s r =>
    erw [orderNerveGradedEncode_single, map_zsmul, Nerve.lengthProjection_of,
      if_pos (orderNerveVertexList_length s)]

theorem orderNerveGradedEncode_single_supported (s : ComposableArrows P n) :
    orderNerveGradedEncode n (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj) := by
  erw [orderNerveGradedEncode_single, one_smul]
  apply Nerve.of_mem_incOn (orderNerveVertexList_chain s)
  intro p hp
  exact List.mem_ofFn.mp hp

variable {n : ℕ}

theorem orderNerveSimplexCarrier_acyclic (s : ComposableArrows P n) :
    Nerve.AcyclicIn (Set.range s.obj) := by
  apply Nerve.acyclicIn_of_subtype _ ⟨s.obj 0, ⟨0, rfl⟩⟩
  intro c hc hz
  apply orderNerve_cycle_bounds_of_comparable (⟨s.obj 0, ⟨0, rfl⟩⟩) ?_ hc hz
  rintro ⟨p, ⟨i, rfl⟩⟩
  exact Or.inr (s.monotone (Fin.zero_le i))

theorem orderNerveSimplexCarrier_face (s : ComposableArrows P _)
    (i : Fin (n + 2)) : Set.range ((nerve P).δ i s).obj ⊆ Set.range s.obj := by
  rintro p ⟨j, rfl⟩ <;> aesop

variable (f : (ComposableArrows P n →₀ ℤ) →ₗ[ℤ] Nerve.Ch P)
    (hf : ∀ s : ComposableArrows P n, f (Finsupp.single s 1) ∈ Nerve.IncOn (Set.range s.obj))
include hf

theorem orderSimplicialBoundary_map_carrier
    (s : ComposableArrows P _) :
    f (orderSimplicialBoundary P n (Finsupp.single s 1)) ∈ Nerve.IncOn (Set.range s.obj) := by
  erw [mathlibOrderNerve_d_single, map_sum]
  apply AddSubgroup.sum_mem
  intro i _
  erw [map_smul]
  apply AddSubgroup.zsmul_mem
  exact Nerve.incOn_mono (fun _ hp => orderNerveSimplexCarrier_face s i hp) (hf _)

theorem orderSimplicialMap_mem_inc
    (c : ComposableArrows P n →₀ ℤ) : f c ∈ Nerve.Inc P := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add] using (Nerve.Inc P).add_mem hc hd
  | single s r =>
    erw [show Finsupp.single s r = r • Finsupp.single s 1 by simp, map_smul]
    exact (Nerve.Inc P).zsmul_mem (Nerve.incOn_le_inc _ (hf s)) r

end FiniteChains.Comb
