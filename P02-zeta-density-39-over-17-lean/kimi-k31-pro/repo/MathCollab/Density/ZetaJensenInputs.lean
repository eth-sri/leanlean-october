module
public import GuthMaynard.NativeSource.GuthMaynard.ZeroCount
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.ZetaCounting

@[expose] public section
open Complex Filter MeromorphicOn
open scoped Topology ArithmeticFunction.Moebius ComplexOrder
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.ZetaGrowth

export GuthMaynard.NativeMoment (
  zeta_jensen_sphere_bound moebius_coeff_norm_le_one
  moebius_LSeries_norm_lt_five_thirds euler_product_lower_bound_2)

theorem finset_analyticOrderNatAt_le_finsum_divisor {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsCompact U) (hpre : IsPreconnected U)
    {c : ℂ} (hc : c ∈ U) (hcOrder : analyticOrderAt f c ≠ ⊤)
    (S : Finset ℂ) (hSU : ∀ u ∈ S, u ∈ U) :
    ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor f U u : ℤ) : ℝ) :=
  GuthMaynard.NativeMoment.finset_analyticVanishingOrder_le_finsum_divisor hf hU hpre hc hcOrder S hSU

end MathCollab.Density.ZetaGrowth
