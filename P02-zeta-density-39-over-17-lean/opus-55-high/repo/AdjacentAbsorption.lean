module
public import AdjacentWindow
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- Scalar absorption of the actual energy and signed-amplifier inequalities.
Every analytic input is explicit; this lemma is used only after proving them. -/
theorem adjacent_scalar_absorption {N L T V R E S Q Λ A B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hT : 0 < T) (hV : 0 < V)
    (hS : 0 < S) (hSR : S ≤ R) (hQ : 1 ≤ Q) (hΛ : 1 ≤ Λ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (henergy : E ≤ B*Λ*(N^4*R/V^4+(N*R^3+T*R^((5:ℝ)/2)+N*T^((1:ℝ)/4)*R^((31:ℝ)/12))/V^2))
    (hcubic : R^3*V^6 ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2))
    (h1 : (N*L)^3 ≤ Q*S^3*V^6)
    (h2 : (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12)
    (h3 : N^12*T^2 ≤ Q^2*S^4*V^16)
    (h4 : N^9*T^2 ≤ Q^2*S^2*V^14)
    (h5 : N^4*L ≤ Q*S*V^6)
    (h6 : N^8*T^3 ≤ Q^2*S^((5:ℝ)/2)*V^14)
    (h7 : N^9*T^((9:ℝ)/4) ≤ Q^2*S^((29:ℝ)/12)*V^14) :
    R ≤ A*(4+4*B)*Λ^2*Q*S := by
  have hR : 0 < R := hS.trans_le hSR
  pm_255 hq Q hl Λ
  let Y := Q*S*R^2*V^6
  pm_61 hy Y
  pm_62
  pm_57
  pm_65
  have hbE : N^4*T*Real.sqrt R*Real.sqrt E ≤ (1+4*B)*Λ*Y := by
    pm_4563
    pm_129
  have hsum : (N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2 ≤ (4+4*B)*Λ*Y := by
    pm_1144
  have hh : R*(R^2*V^6) ≤ (A*(4+4*B)*Λ^2*Q*S)*(R^2*V^6) := by
    calc
      _ = R^3*V^6 := by ring
      _ ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
          N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2) := hcubic
      _ ≤ A*Λ*((4+4*B)*Λ*Y) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [Y]; ring
  exact le_of_mul_le_mul_right hh (by positivity)

end Montgomery.RationalMoment
