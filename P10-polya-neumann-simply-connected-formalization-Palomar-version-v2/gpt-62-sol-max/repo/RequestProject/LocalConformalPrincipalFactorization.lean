module

public import RequestProject.LocalConformalPrincipalModes

/-!
# Compactness of the actual normalized Neumann principal remainder

The nonzero weak mode equations give a factorization through one Sobolev
derivative. The constant Fourier coefficient is retained by the genuine
rank-one projection. All operators below use the supplied physical conformal
coordinates and the actual Neumann resolvent.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric

/-- The bounded symbol `(1 + |n|) / |n|`, with its zero mode removed. -/
def normalizedInverseAbsSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0 else ((sobWeight n / |(n : ℝ)| : ℝ) : ℂ)

theorem norm_normalizedInverseAbsSymbol_le (n : ℤ) : ‖normalizedInverseAbsSymbol n‖ ≤ 2 := by
  by_cases hn : n = 0
  · simp [normalizedInverseAbsSymbol, hn]
  have h : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn
  rw [normalizedInverseAbsSymbol, if_neg hn,
    Complex.norm_of_nonneg (div_nonneg (sobWeight_pos n).le (abs_nonneg _)),
    div_le_iff₀ (by linarith : 0 < |(n : ℝ)|), sobWeight]
  linarith

/-- The bounded diagonal operator for the inverse absolute frequency symbol. -/
def normalizedInverseAbsOperator : L2Z →L[ℂ] L2Z :=
  diagOp normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le

@[simp] theorem normalizedInverseAbsOperator_apply (b : L2Z) (n : ℤ) :
    normalizedInverseAbsOperator b n = normalizedInverseAbsSymbol n * b n :=
  diagOp_apply normalizedInverseAbsSymbol 2 norm_normalizedInverseAbsSymbol_le b n

/-- The rank-one projection onto the constant Fourier coefficient. -/
def zeroModeProjection : L2Z →L[ℂ] L2Z :=
  diagOp (fun n : ℤ => if n = 0 then (1 : ℂ) else 0) 1
    (fun n => by aesop)

@[simp] theorem zeroModeProjection_apply (b : L2Z) (n : ℤ) :
    zeroModeProjection b n = (if n = 0 then 1 else 0) * b n :=
  diagOp_apply _ _ _ b n

theorem zeroModeProjection_eq_single (b : L2Z) :
    zeroModeProjection b = lp.single 2 0 (b 0) := by
  apply lp.ext
  funext n
  rw [lp.single_apply]
  by_cases hn : n = 0
  simp_all
  simp_all

theorem isCompactOperator_zeroModeProjection : IsCompactOperator zeroModeProjection := by
  unfold zeroModeProjection
  apply isCompactOperator_diagOp_of_finite _ _ _ ({0} : Finset ℤ)
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp_all


end PolyaNeumann

end
