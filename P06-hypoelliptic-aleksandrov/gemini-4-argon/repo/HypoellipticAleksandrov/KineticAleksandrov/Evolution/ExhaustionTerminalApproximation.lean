module

public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionTerminal
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExhaustionCauchyRadius

/-!
# A terminal-window bound uniform in the inner-ball approximation index

Both constants and the transported-radius threshold are chosen before the approximation
error and curve. All support and radius premises of the finite-domain core are discharged.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Set

/-- Decreasing the diffused radius improves the relative collar-gap condition. -/
theorem terminal_window_ratio_le_of_radius_le {r r0 d : ℝ} (hr : 0 < r)
    (hdr : d < r) (hd : 0 ≤ d) (hrr0 : r ≤ r0) :
    (r - d) ^ 2 / r ^ 2 ≤ (r0 - d) ^ 2 / r0 ^ 2 := by
  have hr0 : 0 < r0 := hr.trans_le hrr0
  have hf := div_le_div_of_nonneg_left hd hr hrr0
  have hl : 0 ≤ 1 - d / r := sub_nonneg.mpr ((div_le_one hr).mpr hdr.le)
  have hm : 1 - d / r ≤ 1 - d / r0 := by linarith
  simpa only [← div_pow, sub_div, div_self hr.ne', div_self hr0.ne'] using (pow_le_pow_left₀ hl hm 2)

end HypoellipticAleksandrov.KineticAleksandrov
