module
public import MathCollab.Density.Stronger.DyadicMoment
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped Interval
namespace Montgomery.CriticalPeak
open MathCollab.Density.Stronger

/-- Two dyadic powers, with a vanishing initial integral, retain uniform constants. -/
theorem integral_zero_le_of_two_dyadic_powers (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : ∀ t, 0 ≤ f t) {p r B T A D : ℝ}
    (hp : 1 ≤ p) (hr : 1 ≤ r) (hB : 1 ≤ B) (hT : B ≤ T)
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hprefix : (∫ t in 0..B,f t)=0)
    (hdyad : ∀ H : ℝ, B ≤ H → H ≤ T →
      (∫ t in H..2*H,f t) ≤ A*H^p+D*H^r) :
    (∫ t in 0..T,f t) ≤ A*(2:ℝ)^p*T^p+D*(2:ℝ)^r*T^r := by
  pm_4945 hBp B hTp T hBp.trans_le hT
  pm_5477 htwoP p hp
  pm_5477 htwoR r hr
  have hstep : ∀ m : ℕ, (2:ℝ)^m*B ≤ 2*T →
      (∫ t in 0..(2:ℝ)^m*B,f t) ≤ A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r := by
    intro m
    induction m with
    | zero =>
      intro _
      simp only [pow_zero,one_mul,hprefix]
      positivity
    | succ m ih =>
      intro hupper
      have hm : B ≤ (2:ℝ)^m*B := by
        pm_394 hh m
        nlinarith
      have hX : 0 ≤ (2:ℝ)^m*B := by positivity
      have heq : (2:ℝ)^(m+1)*B=2*((2:ℝ)^m*B) := by rw [pow_succ']; ring
      rw [heq] at hupper ⊢
      have hXT : (2:ℝ)^m*B ≤ T := by linarith
      have hih := ih (by linarith)
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hf.intervalIntegrable 0 ((2:ℝ)^m*B))
        (hf.intervalIntegrable ((2:ℝ)^m*B) (2*((2:ℝ)^m*B)))]
      calc
        _ ≤ (A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r)+
            (A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r) :=
          add_le_add hih (hdyad _ hm hXT)
        _ = A*2*((2:ℝ)^m*B)^p+D*2*((2:ℝ)^m*B)^r := by ring
        _ ≤ A*(2:ℝ)^p*((2:ℝ)^m*B)^p+D*(2:ℝ)^r*((2:ℝ)^m*B)^r := by
          gcongr
        _ = _ := by
          pm_1470 hX
  obtain ⟨m,hlo,hhi⟩ := exists_dyadic_cutoff ((le_div_iff₀ hBp).mpr (by simpa using hT))
  have hlo' : T ≤ (2:ℝ)^m*B := (div_le_iff₀ hBp).mp hlo
  have hhi' : (2:ℝ)^m*B ≤ 2*T := by
    have hh := (mul_le_mul_iff_left₀ hBp).mpr hhi
    field_simp at hh
    nlinarith
  calc
    _ ≤ ∫ t in 0..(2:ℝ)^m*B,f t := by
      pm_8293 hTp.le
    _ ≤ A*((2:ℝ)^m*B)^p+D*((2:ℝ)^m*B)^r := hstep m hhi'
    _ ≤ A*(2*T)^p+D*(2*T)^r := by gcongr
    _ = _ := by
      pm_1470 hTp.le
end Montgomery.CriticalPeak
