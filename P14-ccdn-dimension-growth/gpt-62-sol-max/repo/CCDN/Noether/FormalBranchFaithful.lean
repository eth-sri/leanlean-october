/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Noether.FormalPlaneBranch
import CCDN.Determinant.FormalBranchMultiplicity
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-! A formal plane parameterization with a free coordinate has exactly the
curve equation as its kernel. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The substitution map attached to a chosen formal branch. -/
private def formalPlaneBranchMap {K : Type*} [Field K]
    (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K) :
    MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPolynomial.aeval (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev))

section

variable {K : Type*} [Field K]
  (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K)
include K z j g

private lemma formalPlaneBranchMap_parameter :
    formalPlaneBranchMap z j g (X j.rev - C (z j.rev)) = PowerSeries.X := by
  fin_cases j <;> simp [formalPlaneBranchMap, PowerSeries.algebraMap_eq]

private lemma formalPlaneBranchMap_constant
    (hg : PowerSeries.constantCoeff g = z j) (f : MvPolynomial (Fin 2) K) :
    PowerSeries.constantCoeff (formalPlaneBranchMap z j g f) = eval z f := by
  change PowerSeries.constantCoeff (aeval _ f) = _
  rw [map_aeval]
  change eval₂ _ _ f = _
  conv_rhs => rw [← plane_coordinate_cases z j]
  congr 1
  funext k; by_cases h : k = j <;> simp_all

end

/-- Every nonsingular point on an irreducible plane curve gives a
faithful formal branch, with the original point as its constant evaluation. -/
theorem exists_faithful_formal_plane_branch {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) (z : Fin 2 → K) (j : Fin 2)
    (hz : eval z f = 0) (hj : eval z (pderiv j f) ≠ 0) :
    ∃ ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K,
      (∀ h, PowerSeries.constantCoeff (ψ h) = eval z h) ∧
      ψ (X j.rev - C (z j.rev)) = PowerSeries.X ∧
      ∀ h, ψ h = 0 ↔ f ∣ h := by
  obtain ⟨g, hg⟩ := exists_formal_plane_branch f z j hz hj
  let ψ := formalPlaneBranchMap z j g
  have hψ : ψ f = 0 := by
    simpa only [ψ, formalPlaneBranchMap, MvPolynomial.aeval_def, PowerSeries.algebraMap_eq] using
      hg.2
  have hconst := formalPlaneBranchMap_constant z j g hg.1
  have hparam := formalPlaneBranchMap_parameter z j g
  refine ⟨ψ, hconst, hparam, fun h => ⟨?_, ?_⟩⟩
  · intro hz
    by_contra hnd
    have := formal_plane_vanishing_order_bound f hf z ψ hψ hconst j.rev hparam h hnd
      (N := f.totalDegree * h.totalDegree + 1) (hz ▸ dvd_zero _)
    omega
  · rintro ⟨g, rfl⟩
    simp [hψ]

end
end CCDN
