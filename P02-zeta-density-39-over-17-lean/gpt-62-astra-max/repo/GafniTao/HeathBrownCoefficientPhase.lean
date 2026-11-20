module
public import GafniTao.HeathBrownCellDisplacement

@[expose] public section

/-!
# The literal coefficient-change phase

For a coefficient vector `α` in a Heath-Brown cell, this file identifies the
exact real polynomial whose exponential changes the cell centre monomial into
the monomial at `α`.  This is the weight used in the second Abel summation.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownDisplacementPolynomial
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (x : ℝ) : ℝ :=
  ∑ j : Fin (k - 1),
    heathBrownCoefficientDisplacement c α j * x ^ ((j : ℕ) + 1)

theorem fourier_add_point (m : ℤ) (x y : UnitAddCircle) :
    fourier m (x + y) = fourier m x * fourier m y := by
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
      induction y using QuotientAddGroup.induction_on with
      | _ y =>
          rw [← AddCircle.coe_add, fourier_coe_apply, fourier_coe_apply,
            fourier_coe_apply, ← Complex.exp_add]
          congr 1
          push_cast
          ring

noncomputable def heathBrownCoefficientWeight
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (q : ℕ) : ℂ :=
  heathBrownPhase (-heathBrownDisplacementPolynomial c α q)

theorem norm_heathBrownCoefficientWeight
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (q : ℕ) :
    ‖heathBrownCoefficientWeight c α q‖ = 1 := by
  exact norm_heathBrownPhase _

end

end GafniTao
