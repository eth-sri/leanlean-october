module

public import MathCollab.Density.ZetaCounting
public import GuthMaynard.Improvement.CurveUniformization
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal

@[expose] public section

namespace LewkoDensityPalomar

/-- Analytic multiplicity of an actual global zeta zero in the closed height window.
The critical strip is open; the density and height cutoffs are closed. -/
noncomputable def zeroWeight (σ T : ℝ) (ρ : ℂ) : ℝ≥0∞ := by
  classical
  exact if riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T
    then (analyticOrderNatAt riemannZeta ρ : ℝ≥0∞) else 0

/-- The full count of actual zeta zeros with analytic multiplicity and both signs
of the ordinate. This is a genuine nonnegative extended-real sum. -/
noncomputable def zeroCount (σ T : ℝ) : ℝ≥0∞ := ∑' ρ : ℂ, zeroWeight σ T ρ

open MathCollab.Density

/-- Evaluate the infinite sum on its exact finite support. -/
theorem zeroCount_eq (σ T : ℝ) : zeroCount σ T = (zetaDensityCount σ T : ℝ≥0∞) := by
  classical
  let F := zetaZeroFinset σ (-T) T
  have hF (ρ : ℂ) : ρ ∈ F ↔ riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    simpa only [IsNontrivialZetaZero,and_assoc] using mem_zetaDensityFinset (σ:=σ) (T:=T) (ρ:=ρ)
  rw [zeroCount, tsum_eq_sum (s := F)]
  · unfold zetaDensityCount zetaSlabCount
    push_cast
    apply Finset.sum_congr rfl
    intro ρ h
    simp only [zeroWeight,if_pos ((hF ρ).mp h),zetaMultiplicity]
  · intro ρ h
    exact if_neg (mt (hF ρ).mpr h)

abbrev Estimate (σ p ε : ℝ) := ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
  zeroCount σ T ≤ ENNReal.ofReal (C*T^(p+ε))

abbrev Curve (lo hi : ℝ → Prop) (A : ℝ → ℝ) := ∀ {σ ε : ℝ},
  lo σ → hi σ → 0 < ε → Estimate σ (A σ*(1-σ)) ε
abbrev Closed (l u : ℝ) := Curve (l ≤ ·) (· ≤ u)
abbrev Uniform (l u : ℝ) (p : ℝ → ℝ) (ε : ℝ) := ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ,
  l ≤ σ → σ ≤ u → 2 ≤ T → zeroCount σ T ≤ ENNReal.ofReal (C*T^(p σ+ε))

private theorem count_le {σ T b : ℝ} (hb : 0 ≤ b) : zeroCount σ T ≤ ENNReal.ofReal b ↔ (zetaDensityCount σ T:ℝ) ≤ b := by
  rw [zeroCount_eq, ← ENNReal.ofReal_natCast, ENNReal.ofReal_le_ofReal_iff hb]

theorem estimate_iff {σ p ε : ℝ} : Estimate σ p ε ↔ ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
    (zetaDensityCount σ T:ℝ) ≤ C*T^(p+ε) := by
  unfold Estimate
  apply exists_congr; intro C
  apply and_congr_right; intro hc
  apply forall_congr'; intro T
  apply forall_congr'; intro ht
  have : 0<T := by linarith
  exact count_le (by positivity)

theorem Estimate.weaken {σ p q e : ℝ} (h : Estimate σ p e) (hpq : p ≤ q) : Estimate σ q e := by
  obtain ⟨C,hC,h⟩ := h
  refine ⟨C,hC,fun T ht => (h T ht).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have : 1 ≤ T := by linarith
  gcongr

/-- Uniformize a rational power curve on a closed interval. After clearing
the denominators, its one-sided modulus just involves their product. -/
theorem uniform_fraction {l u n q c ε : ℝ} (hlu : l < u) (hε : 0 < ε)
    (hK : 0 ≤ n*(q+c)) (hd : ∀ s, l ≤ s → s ≤ u → 1 ≤ q*s+c)
    (h : Closed l u (fun s => n/(q*s+c))) : Uniform l u (fun s => n/(q*s+c)*(1-s)) ε := by
  have hmod (x y : ℝ) (hx : l≤x) (h : x≤y) (hy : y≤u) :
      n/(q*x+c)*(1-x) ≤ n/(q*y+c)*(1-y)+(n*(q+c)+1)*(y-x) := by
    have h1 := hd x hx (h.trans hy)
    have h2 := hd y (hx.trans h) hy
    have hp : 1 ≤ (q*x+c)*(q*y+c) := one_le_mul_of_one_le_of_one_le h1 h2
    have he : n/(q*x+c)*(1-x)-n/(q*y+c)*(1-y) = n*(q+c)*(y-x)/((q*x+c)*(q*y+c)) := by
      field_simp; ring
    have hh := div_le_self (mul_nonneg hK (sub_nonneg.mpr h)) hp
    rw [← he] at hh
    linarith only [h,hh]
  obtain ⟨C,hC,hb⟩ := GuthMaynard.Improvement.density_curve_uniform_on_interval hlu
    (by linarith : 0 < n*(q+c)+1) hmod (fun _ hl hr _ he => estimate_iff.mp (h hl hr he)) hε
  refine ⟨C,hC,fun σ T hl hr ht => (count_le ?_).mpr (hb σ T hl hr ht)⟩
  have : 0<T := by linarith
  positivity

end LewkoDensityPalomar
