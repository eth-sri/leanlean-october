module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# A terminal-window bound uniform in the inner-ball approximation index

Both constants and the transported-radius threshold are chosen before the approximation
error and curve. All support and radius premises of the finite-domain core are discharged.
-/

 public section



namespace HypoellipticAleksandrov.KineticAleksandrov



/-- Decreasing the diffused radius improves the relative collar-gap condition. -/
theorem terminal_window_ratio_le_of_radius_le {r r0 d : ℝ} (hr : 0 < r)
    (hdr : d < r) (hd : 0 ≤ d) (hrr0 : r ≤ r0) :
    (r - d) ^ 2 / r ^ 2 ≤ (r0 - d) ^ 2 / r0 ^ 2 := by

  have hf := div_le_div_of_nonneg_left hd hr hrr0


  have hs := pow_le_pow_left₀ (sub_nonneg.mpr ((div_le_one hr).mpr hdr.le)) (show 1 - d / r ≤ 1 - d / r0 by linarith) 2
  simpa only [← div_pow, sub_div, div_self hr.ne', div_self (hr.trans_le hrr0).ne'] using hs

end HypoellipticAleksandrov.KineticAleksandrov
