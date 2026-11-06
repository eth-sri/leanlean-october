module
public import AdjacentMomentEnvelope

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

/-- Normalize a proved dual moment by one common constant. -/
theorem adjacent_scaled_dual {S R T H Z C η : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (_hS : 0 ≤ S) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (hH : 0 ≤ H) (hZ : 1 ≤ Z) (_hC : 0 ≤ C)
    (hc : C*H^η ≤ Z)
    (hm : S^k ≤ R^(2*k-1)*(C*(T+H^(2*k))*H^η)) :
    (S/Z)^k ≤ (T+H^(2*k))*R^(2*k-1) := by
  have hZ0 : 0 < Z := by linarith
  rw [div_pow]
  apply (div_le_iff₀ (pow_pos hZ0 k)).mpr
  have hz : Z ≤ Z^k := by simpa using pow_le_pow_right₀ hZ hk
  calc
    _ ≤ R^(2*k-1)*(C*(T+H^(2*k))*H^η) := hm
    _ = (C*H^η)*((T+H^(2*k))*R^(2*k-1)) := by ring
    _ ≤ Z^k*((T+H^(2*k))*R^(2*k-1)) := by gcongr; exact hc.trans hz
    _ = _ := by ring


