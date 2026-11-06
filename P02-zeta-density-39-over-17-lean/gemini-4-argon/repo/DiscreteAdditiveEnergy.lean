module
public import SmallGcdCubicEnergy

@[expose] public section

set_option autoImplicit false
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Exact absorption of the square-root energy term; V is strictly positive. -/
theorem discrete_energy_absorb {E A B V : ℝ} (hE : 0 ≤ E) (hV : 0 < V)
    (h : E*V^2 ≤ A*Real.sqrt E+B) :
    E ≤ A^2/V^4+2*B/V^2 := by
  have he : (V^2*Real.sqrt E)^2=V^4*E := by
    rw [mul_pow,Real.sq_sqrt hE]
    ring
  have hy : 2*A*Real.sqrt E*V^2 ≤ E*V^4+A^2 := by
    have hh := sq_nonneg (V^2*Real.sqrt E-A)
    nlinarith [he]
  have hh := mul_le_mul_of_nonneg_right h (sq_nonneg V)
  have hb : E*V^4 ≤ A^2+2*B*V^2 := by nlinarith
  calc
    E ≤ (A^2+2*B*V^2)/V^4 := (le_div_iff₀ (pow_pos hV 4)).mpr hb
    _ = _ := by field_simp


