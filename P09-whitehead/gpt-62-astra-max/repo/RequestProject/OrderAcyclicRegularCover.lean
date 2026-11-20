module

public import RequestProject.OrderTwoDimensionalAcyclicity
public import RequestProject.OrderUniversalRealizationCover
public import RequestProject.OrderNerveCoverDimension
public import RequestProject.OrderUniversalRealizationSimplyConnected
public import RequestProject.TopologicalSingular.HurewiczIsomorphismConsequences


@[expose] public section

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular Topology
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

section

variable (hfill : ∀ c : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) c = 0 → ∃ b : StrictOrdTri P →₀ ℤ, bdry2 (strictOrderCx P) b = c)
include hfill

/-- Actual strict edge-cycle fillings give genuine singular one-cycle fillings. -/
theorem orderRealization_oneCycle_bounds_of_strict_fillings
    (c : Chain (orderNerveRealization P) 1) (hc : boundary 0 c = 0) :
    ∃ b : Chain (orderNerveRealization P) 2, boundary 1 b = c := by
  obtain ⟨z, hz, hd, hz0, b, hb⟩ := orderNerveRealization_cycle_nerveRepresentative 0 c hc
  obtain ⟨a, ha, ha0⟩ := nerve_oneCycle_filling_of_strict hfill z hz hd hz0
  refine ⟨b + orderNerveGradedRealize P 2 a, ?_⟩
  simp_all [orderNerveGradedRealize_boundary]

theorem orderRealization_homology_one_isZero_of_strict_fillings :
    Limits.IsZero (((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj
      (ModuleCat.of ℤ ℤ)).obj (orderNerveRealization P)) := by
  have he : (complex (orderNerveRealization P)).ExactAt 1 := by
    rw [HomologicalComplex.exactAt_iff' (K := complex (orderNerveRealization P))
      (i := 2) (j := 1) (k := 0) (ChainComplex.prev ℕ 1) (ChainComplex.next_nat_succ 0)]
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    apply orderRealization_oneCycle_bounds_of_strict_fillings <;> assumption
  exact he.isZero_homology.of_iso (homologyMathlibIso (orderNerveRealization P) 1).symm

end

/-- Acyclicity of the actual strict cellular complex implies the exact singular
acyclicity of Challenge, for every two-dimensional order realization. -/
theorem orderRealization_acyclic_of_strict_isAcyclic [(nerve P).HasDimensionLE 2]
    (hP : IsAcyclic (strictOrderCx P)) : Whitehead.Acyclic (orderNerveRealization P) := by
  apply (orderRealization_acyclic_iff_homology_one_two P).mpr
  refine ⟨orderRealization_homology_one_isZero_of_strict_fillings hP.h1,
    orderRealization_homology_two_isZero_of_strict_cycles_zero P ?_⟩
  intro c hc
  apply hP.h2 <;> assumption

namespace IsPosetCover

/-- A connected acyclic strict cellular cover with transitive order deck maps
realizes to a genuine acyclic regular cover. The cover need not be universal. -/
theorem hasAcyclicRegularCover [Nonempty Q] [(nerve Q).HasDimensionLE 2]
    {f : P → Q} (hf : IsPosetCover f)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q))
    (hdeck : ∀ v w : P, f v = f w →
      ∃ e : P ≃o P, (∀ p, f (e p) = f p) ∧ e v = w)
    (hacyc : IsAcyclic (strictOrderCx P)) :
    Whitehead.HasAcyclicRegularCover (orderNerveTwoComplex Q hQ) := by
  classical
  obtain ⟨q⟩ := (inferInstance : Nonempty Q)
  obtain ⟨p, _⟩ := hf.surj q
  letI : Nonempty P := ⟨p⟩
  letI := hf.realization_hasDimensionLE 2
  letI := orderNerveRealization_pathConnectedSpace P hP
  exact ⟨orderNerveRealization P, inferInstance,
    ⟨orderNerveRealizationMap f hf.mono, (orderNerveRealizationMap f hf.mono).hom.continuous⟩,
    hf.realizationMap_isCoveringMap, hf.realizationMap_surjective,
    inferInstance, hf.realizationMap_regular hdeck,
    orderRealization_acyclic_of_strict_isAcyclic hacyc⟩

end IsPosetCover
end FiniteChains.Comb
