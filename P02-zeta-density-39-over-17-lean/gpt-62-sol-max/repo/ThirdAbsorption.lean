module
public import AdjacentAbsorption
public import GeneralAdditiveEnergy
public import GeneralCubicLargeValues
public import GeneralDetectorCover
public import DensityDetectorWindows

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
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
  have hR := hS.trans_le hSR
  have hq : 0 ≤ Q := by linarith
  let Y := Q*S*R^2*V^6
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
  have h := cubic_absorption_of_energy_budget hN hL hT hV hS hSR hQ hΛ hA
    (b := 4*B) (k := 2) (U := N^4*T*R^((7:ℝ)/4)+N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40)) (by positivity) (by norm_num) hE
    (by simpa only [add_assoc] using hcubic) h1 h2 h5
    (extended_squared_energy hN hT hV hS hSR hB hΛ hE henergy h3 h4 h6 h7)
    (show N^4*T*R^((7:ℝ)/4)+N^4*L*T^((1:ℝ)/8)*R^((71:ℝ)/40) ≤ 2*Y by linarith only [hb8,hb9])
  convert h using 1 <;> ring

end Montgomery.RationalMoment
