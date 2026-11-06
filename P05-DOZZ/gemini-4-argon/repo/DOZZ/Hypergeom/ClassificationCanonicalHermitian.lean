/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianRepresentation
public import DOZZ.Hypergeom.BasisSpanning
import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! The Cramer Hermitian representation specialized to the canonical zero basis. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Every real Gauss solution has a Hermitian quadratic representation in the canonical zero basis
on the common cut plane. This is the direct input to the classification of real solutions, before
its monodromy constraints. -/
theorem realGaussSolution_canonical_hermitian_representation
    {H} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    T (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ, ∃ β : ℂ, ∀ z ∈ gaussCutPlane,
      (T z : ℂ) =
        gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
            star ((α : ℂ) * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
              β * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
          gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
            star (star β * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
              (δ : ℂ) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
  have hzero := gauss_local_basis_zero hH (a : ℂ) (b : ℂ) (c : ℂ) (by intro n hn; apply hc n; exact_mod_cast hn)
  have hW : ∀ z ∈ gaussCutPlane,
      gaussCramerWronskian
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) z ≠ 0 := by
    intro z hz
    have hzreg := gaussCutPlane_subset_regularPlane hz
    change gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
        deriv (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) z -
      deriv (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) z *
        gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z ≠ 0
    rw [((hzero.2.2.1 z hz).2.2)]
    exact mul_ne_zero (mul_ne_zero (by intro he; apply hc 1; exact_mod_cast (sub_eq_zero.mp he).symm) (Complex.cpow_ne_zero_iff.mpr (Or.inl hzreg.1))) (Complex.cpow_ne_zero_iff.mpr (Or.inl (by intro he; apply hzreg.2; exact (sub_eq_zero.mp he).symm)))
  exact realGaussCramer_hermitian_representation a b c T hT (hzero.1.analyticOnNhd gaussCutPlane_isOpen) (hzero.2.1.analyticOnNhd gaussCutPlane_isOpen)
    (by intro z hz; exact (hzero.2.2.1 z hz).1) (by intro z hz; exact (hzero.2.2.1 z hz).2.1) hW

end DOZZ.Proofs
