/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Projection.PlaneProjectionKernel
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.SectionImageRank
import CCDN.ForMathlib.PowerSeries
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.FormalPlaneBranch
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal

/-! A formal plane parameterization with a free coordinate has exactly the
curve equation as its kernel. The proof uses the section-image rank bound
and arbitrarily many independent powers of the formal parameter. -/

namespace CCDN
noncomputable section
open MvPolynomial

section
variable {K : Type*} [Field K] (z : Fin 2 → K) (j : Fin 2) (g : PowerSeries K)

/-- The substitution map attached to a chosen formal branch. -/
def formalPlaneBranchMap
    :
    MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPolynomial.aeval (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev))

lemma formalPlaneBranchMap_parameter
    :
    formalPlaneBranchMap z j g (X j.rev - C (z j.rev)) = PowerSeries.X := by
  fin_cases j <;> simp [formalPlaneBranchMap, PowerSeries.algebraMap_eq]

lemma formalPlaneBranchMap_constant
    (hg : PowerSeries.constantCoeff g = z j) (f : MvPolynomial (Fin 2) K) :
    PowerSeries.constantCoeff (formalPlaneBranchMap z j g f) = eval z f := by
  have he : PowerSeries.constantCoeff.comp (formalPlaneBranchMap z j g).toRingHom = eval z := by
    apply MvPolynomial.ringHom_ext
    · simp_all
    · intro k
      simp [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        formalPlaneBranchMap, aeval_X]
      by_cases hk : k = j
      · simp_all
      · simp [ite_eq_right hk, map_add, PowerSeries.constantCoeff_X,
          PowerSeries.constantCoeff_C, zero_add]
        have hh := congrFun (plane_coordinate_cases z j) k
        simp_all
  exact RingHom.congr_fun he f

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
  obtain ⟨g, hg⟩ : ∃ g : PowerSeries K, PowerSeries.constantCoeff g = z j ∧
      MvPolynomial.eval₂ PowerSeries.C
        (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev)) f = 0 := by
    let F := formalPlanePolynomial j (z j.rev) f
    have hder : (F.derivative.map PowerSeries.constantCoeff).eval (z j) ≠ 0 := by
      rw [formalPlanePolynomial_derivative, formalPlanePolynomial_constant_eval,
        plane_coordinate_cases]
      exact hj
    obtain ⟨g, hg, hfg⟩ := exists_formal_simple_root F (z j) (by
      rwa [formalPlanePolynomial_constant_eval, plane_coordinate_cases]) hder
    exact ⟨g, hg, by rwa [formalPlanePolynomial_eval] at hfg⟩
  let ψ := formalPlaneBranchMap z j g
  refine ⟨ψ, formalPlaneBranchMap_constant z j g hg.1, formalPlaneBranchMap_parameter z j g, ?_⟩
  intro h
  exact plane_map_eq_zero_iff_dvd f hf ψ (by aesop) _ (fun N => by
    rw [formalPlaneBranchMap_parameter z j g]
    exact PowerSeries.linearIndependent_of_order_injective _ Fin.val Fin.val_injective
      (fun i => PowerSeries.order_X_pow i.val)) h

