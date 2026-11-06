/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.ForMathlib.StandardExponents
public import CCDN.Hilbert.FilteredIntersection
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Standard monomials in a filtered coordinate ring

Degree lexicographic standard representatives (`Ideal.exists_standard_representative_degLex`)
preserve the total-degree filtration, giving an exact combinatorial model for the dimensions
of the filtered coordinate spaces.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The filtered Hilbert function counts the standard monomials of bounded degree. -/
theorem filteredCoordinateSpace_finrank_eq_standard_card {K σ : Type*} [Field K]
    [LinearOrder σ] [WellFoundedGT σ] (I : Ideal (MvPolynomial σ K)) (N : ℕ) :
    Module.finrank K (filteredCoordinateSpace I N) =
      Nat.card (Ideal.boundedStandardExponents I MonomialOrder.degLex N) := by
  let V := restrictSupport K (Ideal.boundedStandardExponents I MonomialOrder.degLex N)
  let φ := (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype
  have hinj : Function.Injective φ := fun f g h => by
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine Ideal.eq_zero_of_mem_restrictSupport_standardExponents I MonomialOrder.degLex
      (Submodule.sub_mem _ (restrictSupport_mono K (fun _ ha => ha.1) f.property)
        (restrictSupport_mono K (fun _ ha => ha.1) g.property)) ?_
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change (Ideal.Quotient.mkₐ K I) (f.val - g.val) = 0
    rwa [map_sub, sub_eq_zero]
  /- Standard representatives describe precisely each filtered coordinate space. -/
  have hrange : φ.range = filteredCoordinateSpace I N := by
    rw [show φ = (Ideal.Quotient.mkₐ K I).toLinearMap.comp V.subtype from rfl,
      LinearMap.range_comp, Submodule.range_subtype]
    refine le_antisymm (Submodule.map_mono (restrictSupport_mono K fun _ ha => ha.2)) ?_
    rintro y ⟨f, hf, rfl⟩
    obtain ⟨r, hr, hdegree, hI⟩ := Ideal.exists_standard_representative_degLex I f
    refine Submodule.mem_map.mpr ⟨r, fun a ha =>
      ⟨hr ha, (le_totalDegree ha).trans (hdegree.trans ((mem_restrictTotalDegree σ N f).mp hf))⟩, ?_⟩
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hI
    rwa [map_sub, sub_eq_zero, eq_comm] at hq
  rw [← hrange, LinearMap.finrank_range_of_inj hinj]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

end
end CCDN
