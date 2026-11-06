module

public import Mathlib

public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.OriginContinuationCharts

@[expose] public section


noncomputable section
open Filter
open scoped NumberField Classical ContDiff Topology

namespace DedekindZetaZeroFree.LargeSieve.Vendor

def originMellinShift (s : ℂ)  :=
  Nat.ceil (max 0 (-s.re)) + 1

theorem originMellinShift_spec (s : ℂ) :
    -(originMellinShift s : ℝ) < s.re := by
  have hceil : max 0 (-s.re) ≤ ((Nat.ceil (max 0 (-s.re)) : ℕ) : ℝ) := Nat.le_ceil _
  have hcast : ((originMellinShift s : ℕ) : ℝ) =
      ((Nat.ceil (max 0 (-s.re)) : ℕ) : ℝ) + 1 := by
    rw [originMellinShift, Nat.cast_add, Nat.cast_one]
  have hmax : -s.re ≤ max 0 (-s.re) := le_max_right _ _
  linarith

def originMellinQ (h : ℝ → ℂ) (s : ℂ)  :=
  originMellinChart h (originMellinShift s) s

section
variable (h : ℝ → ℂ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h)
include h hh hc
private theorem originMellinChart_eq_of_lt   {m n : ℕ} {s : ℂ}
    (hm : -(m : ℝ) < s.re) (hn : -(n : ℝ) < s.re) :
    originMellinChart h m s = originMellinChart h n s := by
  suffices key : ∀ n m : ℕ, m ≤ n → -(m : ℝ) < s.re → -(n : ℝ) < s.re →
      originMellinChart h n s = originMellinChart h m s by
    grind
  intro n
  induction n with
  | zero =>
      intro m hm _ _
      rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro m hm hms hns
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · rfl
      · have hmn  := Nat.lt_succ_iff.mp hlt
        have hn' : -(n : ℝ) < s.re := by
          have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
          linarith
        rw [originMellinChart_succ h hh hc n s hn']
        apply ih <;> assumption

theorem originMellinQ_differentiable   :
    Differentiable ℂ (originMellinQ h) := by
  intro s
  have hn  := originMellinShift_spec s
  have hchart  :=
    originMellinChart_differentiableAt h hh hc (originMellinShift s) s hn
  refine hchart.congr_of_eventuallyEq ?_
  have hmem : {z : ℂ | -((originMellinShift s : ℕ) : ℝ) < z.re} ∈ 𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hn
  filter_upwards [hmem] with z hz
  exact originMellinChart_eq_of_lt h hh hc (originMellinShift_spec z) hz

theorem originMellinQ_eq_chart   (n : ℕ) (s : ℂ)
    (hs : -(n : ℝ) < s.re) :
    originMellinQ h s = originMellinChart h n s := originMellinChart_eq_of_lt h hh hc (originMellinShift_spec s) hs

theorem originMellinQ_eq_mellin_div_Gammaℂ   (s : ℂ) (hs : 0 < s.re) :
    originMellinQ h s = mellin h s / Complex.Gammaℂ s := by
  rw [originMellinQ_eq_chart h hh hc 0 s (by simpa using hs)]
  simp [originMellinChart, div_eq_mul_inv]
end


end DedekindZetaZeroFree.LargeSieve.Vendor

end
