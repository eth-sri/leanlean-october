module
public import TwoTermScaleInequalities
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- Scalar absorption of the actual energy and signed-amplifier inequalities.
Every analytic input is explicit; this lemma is used only after proving them. -/
theorem two_term_scalar_absorption {N L T V R E S Q Λ A B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hT : 0 < T) (hV : 0 < V)
    (hS : 0 < S) (hSR : S ≤ R) (hQ : 1 ≤ Q) (hΛ : 1 ≤ Λ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (henergy : E ≤ B*Λ*(N^4*R/V^4+N*R^3/V^2))
    (hcubic : R^3*V^6 ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2))
    (h1 : (N*L)^3 ≤ Q*S^3*V^6)
    (h2 : (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12)
    (h3 : N^12*T^2 ≤ Q^2*S^4*V^16)
    (h4 : N^9*T^2 ≤ Q^2*S^2*V^14)
    (h5 : N^4*L ≤ Q*S*V^6) :
    R ≤ A*(4+2*B)*Λ^2*Q*S := by
  have hR : 0 < R := hS.trans_le hSR
  pm_255 hq Q hl Λ
  let Y := Q*S*R^2*V^6
  pm_61 hy Y
  pm_62
  have he3 : N^12*T^2*R^2/V^4 ≤ Q^2*S^2*R^4*V^12 := by
    calc
      _ ≤ (Q^2*S^4*V^16)*R^2/V^4 := by gcongr
      _ = (Q^2*S^2*R^2*V^12)*S^2 := by field_simp
      _ ≤ (Q^2*S^2*R^2*V^12)*R^2 := mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = _ := by ring
  have he4 : N^9*T^2*R^4/V^2 ≤ Q^2*S^2*R^4*V^12 := by
    calc
      _ ≤ (Q^2*S^2*V^14)*R^4/V^2 := by gcongr
      _ = _ := by field_simp
  have hesq : (N^4*T*Real.sqrt R*Real.sqrt E)^2 ≤ 2*B*Λ*Y^2 := by
    calc
      _ = N^8*T^2*R*E := by
        rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt hR.le,Real.sq_sqrt hE]; ring
      _ ≤ N^8*T^2*R*(B*Λ*(N^4*R/V^4+N*R^3/V^2)) := by gcongr
      _ = B*Λ*(N^12*T^2*R^2/V^4+N^9*T^2*R^4/V^2) := by ring
      _ ≤ B*Λ*(2*(Q^2*S^2*R^4*V^12)) := by gcongr; linarith only [he3,he4]
      _ = _ := by dsimp [Y]; ring
  have hbE : N^4*T*Real.sqrt R*Real.sqrt E ≤ (1+2*B)*Λ*Y := by
    pm_4563
    have hcoef : 2*B*Λ ≤ ((1+2*B)*Λ)^2 := by
      have hh : 2*B ≤ (1+2*B)^2 := by nlinarith [sq_nonneg B]
      have hh' : Λ ≤ Λ^2 := by nlinarith
      calc
        _ ≤ (1+2*B)^2*Λ := mul_le_mul_of_nonneg_right hh hl
        _ ≤ (1+2*B)^2*Λ^2 := mul_le_mul_of_nonneg_left hh' (by positivity)
        _ = _ := by ring
    exact hesq.trans (by have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg Y); nlinarith only [hh])
  have hsum : (N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2 ≤ (4+2*B)*Λ*Y := by
    pm_1144
  have hh : R*(R^2*V^6) ≤ (A*(4+2*B)*Λ^2*Q*S)*(R^2*V^6) := by
    calc
      _ = R^3*V^6 := by ring
      _ ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
          N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2) := hcubic
      _ ≤ A*Λ*((4+2*B)*Λ*Y) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [Y]; ring
  exact le_of_mul_le_mul_right hh (by positivity)

end Montgomery.RationalMoment
