module
public import DensityEnergyGM.SharpCountEnergyExpansion

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Montgomery.RationalMoment

/-- Real power substitution, retaining every amplitude-loss factor. -/
theorem gmExpandedTerm_log_identity {T R : ℝ} (hT : 0 < T) (hR : 0 < R)
    (σ x δ ell A B g d u v w r : ℝ) :
    (T^x)^3*T^A*(T^ell)^B*R^g*
      ((T^x)^u*T^v*(T^(σ*x-2*δ))^w*R^r)^d =
    T^(3*x+A+ell*B+(x*u+v+(σ*x-2*δ)*w)*d)*R^(g+r*d) := by
  rw [Real.mul_rpow (by positivity : 0 ≤ (T^x)^u*T^v*(T^(σ*x-2*δ))^w) (by positivity : 0 ≤ R^r),
    Real.mul_rpow (by positivity : 0 ≤ (T^x)^u*T^v) (by positivity),
    Real.mul_rpow (by positivity : 0 ≤ (T^x)^u) (by positivity)]
  simp only [← Real.rpow_mul hT.le,← Real.rpow_mul hR.le]
  rw [← Real.rpow_mul_natCast hT.le]
  norm_num only [Nat.cast_ofNat]
  have he :
      T^(x*3)*T^A*T^(ell*B)*R^g*
        (T^(x*u*d)*T^(v*d)*T^((σ*x-2*δ)*w*d)*R^(r*d)) =
      (T^(x*3)*T^A*T^(ell*B)*T^(x*u*d)*T^(v*d)*T^((σ*x-2*δ)*w*d))*
        (R^g*R^(r*d)) := by ring
  rw [he]
  repeat rw [← Real.rpow_add hT]
  rw [← Real.rpow_add hR]
  congr 2
  ring


