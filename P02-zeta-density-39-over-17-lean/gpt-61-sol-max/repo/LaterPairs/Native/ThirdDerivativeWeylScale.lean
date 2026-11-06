module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.SecondDerivativeScale

@[expose] public section
set_option maxHeartbeats 0


                                                                            


namespace TaoTrudgianYang2025

theorem third_derivative_weyl_normalize {S N H C μ : ℝ}
    (hN : 0 ≤ N) (hH : 0 < H) (hHN : H ≤ N) (hC : 0 ≤ C) (hμ : 0 < μ)
    (hb : H^2*S^2 ≤ (N+H)*(H*N+
      24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+4*Real.sqrt H/Real.sqrt μ))) :
    S^2 ≤ 2*N^2/H+48*C*N^2*Real.sqrt μ*Real.sqrt H+
      192*N/(Real.sqrt H*Real.sqrt μ) := by
  have hinner : 0 ≤ H*N+
      24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+4*Real.sqrt H/Real.sqrt μ) := by positivity
  have hbound := hb.trans (mul_le_mul_of_nonneg_right
    (show N+H ≤ 2*N by linarith) hinner)
  have hd := (le_div_iff₀ (sq_pos_of_pos hH)).mpr
    (show S^2*H^2 ≤ _ by simpa only [mul_comm (H^2) (S^2)] using hbound)
  have hid :
      (2*N*(H*N+24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+
        4*Real.sqrt H/Real.sqrt μ)))/H^2 =
      2*N^2/H+48*C*N^2*Real.sqrt μ*Real.sqrt H+
        192*N/(Real.sqrt H*Real.sqrt μ) := by grind
  exact hd.trans_eq hid


