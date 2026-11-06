module
public import OAI.NumberTheory.DirichletL.Moments.ReflectionTails
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤ s)
    (hcap : Q*R≤C*Z ^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z ^(xi/2)) :
    s*(Q*d/(Z ^n*h))≤C*Z ^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  pm_3773 hn Z n hz
  have hp : Q*d≤C*Z ^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z ^n*h)≤C*Z ^M/Z ^n := by
    calc
      _≤Q*d/Z ^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z ^M/Z ^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z ^(xi/2)*(C*Z ^M/Z ^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z ^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
