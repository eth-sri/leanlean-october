/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
import CCDN.Algebra.SectionImageRank
import CCDN.Noether.FormalBranchOrder
import CCDN.Hilbert.PlaneHilbert
import CCDN.Noether.FormalPlaneBranch
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.SimpleRing.Principal

/-! A formal plane parameterization with a free coordinate has exactly the
curve equation as its kernel. The proof uses the section-image rank bound
and arbitrarily many independent powers of the formal parameter. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) (hf : Irreducible f) (z : Fin 2 → K)
    (j : Fin 2) (g : PowerSeries K)

include hf in
/-- A formal map of an irreducible plane curve, with one coordinate equal to
X+a, kills precisely the multiples of its defining equation. -/
private theorem formal_plane_map_eq_zero_iff_dvd
    (ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K) (hψ : ψ f = 0)
    (j : Fin 2) (a : K) (hparam : ψ (X j - C a) = PowerSeries.X)
    (g : MvPolynomial (Fin 2) K) : ψ g = 0 ↔ f ∣ g := by
  constructor
  · intro hg
    by_contra hnd
    have := formal_plane_vanishing_order_bound f hf ψ hψ j a hparam g hnd (N := f.totalDegree*g.totalDegree+1) (hg ▸ dvd_zero _)
    omega
  · rintro ⟨q, rfl⟩
    grind

/-- The substitution map attached to a chosen formal branch. -/
private def formalPlaneBranchMap :
    MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPolynomial.aeval (fun k => if k = j then g else PowerSeries.X + PowerSeries.C (z j.rev))

private lemma formalPlaneBranchMap_parameter :
    formalPlaneBranchMap z j g (X j.rev - C (z j.rev)) = PowerSeries.X := by
  fin_cases j <;> simp [formalPlaneBranchMap, PowerSeries.algebraMap_eq]

private lemma formalPlaneBranchMap_constant
    (hg : PowerSeries.constantCoeff g = z j) (f : MvPolynomial (Fin 2) K) :
    PowerSeries.constantCoeff (formalPlaneBranchMap z j g f) = eval z f := by
  have he : PowerSeries.constantCoeff.comp (formalPlaneBranchMap z j g).toRingHom = eval z := by
    apply MvPolynomial.ringHom_ext
    simp
    · intro k
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        formalPlaneBranchMap, aeval_X]
      by_cases hk : k = j
      simp_all
      simpa [*] using (congrFun (plane_coordinate_cases z j) k)
  exact RingHom.congr_fun he f

include hf in
/-- Every nonsingular point on an irreducible plane curve gives a
faithful formal branch, with the original point as its constant evaluation. -/
theorem exists_faithful_formal_plane_branch
    (hz : eval z f = 0) (hj : eval z (pderiv j f) ≠ 0) :
    ∃ ψ : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K,
      (∀ h, PowerSeries.constantCoeff (ψ h) = eval z h) ∧
      ψ (X j.rev - C (z j.rev)) = PowerSeries.X ∧
      ∀ h, ψ h = 0 ↔ f ∣ h := by
  obtain ⟨g, hg⟩ := exists_formal_plane_branch f z j hz hj
  let ψ := formalPlaneBranchMap z j g
  have hψ := by
    exact hg.2
  refine ⟨ψ, formalPlaneBranchMap_constant z j g hg.1, formalPlaneBranchMap_parameter z j g, ?_⟩
  intro h
  exact formal_plane_map_eq_zero_iff_dvd f hf ψ hψ j.rev (z j.rev)
    (formalPlaneBranchMap_parameter z j g) h

end
end CCDN
