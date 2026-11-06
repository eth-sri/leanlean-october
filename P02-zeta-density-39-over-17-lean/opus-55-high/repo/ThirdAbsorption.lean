module
public import ThirdWindow
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 1200000
namespace Montgomery.RationalMoment

/-- Scalar absorption of the actual energy and signed-amplifier inequalities.
Every analytic input is explicit; this lemma is used only after proving them. -/
theorem third_scalar_absorption {N L T V R E S Q Λ A B : ℝ}
    (hN : 0 < N) (hL : 0 < L) (hT : 0 < T) (hV : 0 < V)
    (hS : 0 < S) (hSR : S ≤ R) (hQ : 1 ≤ Q) (hΛ : 1 ≤ Λ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (henergy : E ≤ B*Λ*(N^4*R/V^4+(N*R^3+T*R^((5:ℝ)/2)+N*T^((1:ℝ)/4)*R^((31:ℝ)/12))/V^2))
    (hcubic : R^3*V^6 ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2+N^4*T*R^((7:ℝ)/4)+N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40)))
    (h1 : (N*L)^3 ≤ Q*S^3*V^6)
    (h2 : (N^4*T^2/L)^2 ≤ Q^2*S^3*V^12)
    (h3 : N^12*T^2 ≤ Q^2*S^4*V^16)
    (h4 : N^9*T^2 ≤ Q^2*S^2*V^14)
    (h5 : N^4*L ≤ Q*S*V^6)
    (h6 : N^8*T^3 ≤ Q^2*S^((5:ℝ)/2)*V^14)
    (h7 : N^9*T^((9:ℝ)/4) ≤ Q^2*S^((29:ℝ)/12)*V^14)
    (h8 : N^4*T ≤ Q*S^((5:ℝ)/4)*V^6)
    (h9 : N^4*L*T^((1:ℝ)/8) ≤ Q*S^((49:ℝ)/40)*V^6) :
    R ≤ A*(6+4*B)*Λ^2*Q*S := by
  have hR : 0 < R := hS.trans_le hSR
  pm_255 hq Q hl Λ
  let Y := Q*S*R^2*V^6
  pm_61 hy Y
  pm_62
  have hpowabs (g c : ℝ) (hg : g ≤ 2) (hc : c ≤ Q*S^(3-g)*V^6) :
      c*R^g ≤ Y := by
    have hs : S^(3-g)=S*S^(2-g) := by
      calc
        _ = S^((1:ℝ)+(2-g)) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add hS,Real.rpow_one]
    have hr : R^(2-g)*R^g=R^2 := by rw [← Real.rpow_add hR]; norm_num
    calc
      _ ≤ (Q*S^(3-g)*V^6)*R^g := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (Q*S*V^6)*(S^(2-g)*R^g) := by rw [hs]; ring
      _ ≤ (Q*S*V^6)*(R^(2-g)*R^g) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hS.le hSR (by linarith)) (by positivity)
      _ = Y := by rw [hr]; dsimp [Y]; ring
  have hb8 : N^4*T*R^((7:ℝ)/4) ≤ Y := by
    apply hpowabs ((7:ℝ)/4) (N^4*T) (by norm_num)
    norm_num
    exact h8
  have hb9 : N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40) ≤ Y := by
    apply hpowabs ((71:ℝ)/40) (N^4*L*T^((1:ℝ)/8)) (by norm_num)
    norm_num
    exact h9
  pm_57
  pm_65
  have hbE : N^4*T*Real.sqrt R*Real.sqrt E ≤ (1+4*B)*Λ*Y := by
    pm_4563
    pm_129
  have hsum : (N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
      N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2+N^4*T*R^((7:ℝ)/4)+N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40) ≤ (6+4*B)*Λ*Y := by
    have hyl : Y ≤ Λ*Y := le_mul_of_one_le_left hy hΛ
    nlinarith only [hb1,hb2,hbE,hb5,hb8,hb9,hyl]
  have hh : R*(R^2*V^6) ≤ (A*(6+4*B)*Λ^2*Q*S)*(R^2*V^6) := by
    calc
      _ = R^3*V^6 := by ring
      _ ≤ A*Λ*((N*L)^3+(N^4*T^2/L)*R*Real.sqrt R+
          N^4*T*Real.sqrt R*Real.sqrt E+N^4*L*R^2+N^4*T*R^((7:ℝ)/4)+N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40)) := hcubic
      _ ≤ A*Λ*((6+4*B)*Λ*Y) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by dsimp [Y]; ring
  exact le_of_mul_le_mul_right hh (by positivity)

end Montgomery.RationalMoment
