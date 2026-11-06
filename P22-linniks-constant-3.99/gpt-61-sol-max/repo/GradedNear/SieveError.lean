import GradedNear.Tactics

import Mathlib

/-!
# The sieve error terms tend to zero

For fixed `h_k, t_k, λ_k = level k > 0` with `λ_k < t_k`, and constants `CB, CC, κ > 0`,
`Σ_{k<m} h_k [CB t_{k+1}²/(λ_k² 𝓛) + CB/(λ_k² 𝓛³) + |CC| q^{-κ}/𝓛 + 2 λ_k q^{λ_k - t_k}] → 0`.
-/

open Filter Topology

namespace GradedNear

lemma tendsto_log_nat_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_inv_log_nat : Tendsto (fun q : ℕ => (Real.log q)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop

lemma tendsto_rpow_neg_nat {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ (-κ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop

end GradedNear
