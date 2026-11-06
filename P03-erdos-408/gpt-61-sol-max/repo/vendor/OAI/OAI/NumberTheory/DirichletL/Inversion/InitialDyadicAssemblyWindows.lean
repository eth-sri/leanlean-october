module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly

@[expose] public section

namespace OAI



open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_norm_le  i  x  : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support  i  :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simp_all [cutoff]
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
     k (hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper  C η (_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  nlinarith

end SevenEighths.InverseInitialDyadicAssembly



end OAI
