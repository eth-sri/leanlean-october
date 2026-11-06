module
public import OAI.NumberTheory.DirichletL.Hecke.DyadicControl
public import OAI.NumberTheory.DirichletL.Hecke.DyadicJoins
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric Complex
namespace SevenEighths.HeckeDyadic
open HeckeFamily HeckeLogarithmic HeckeReciprocalGrowth

theorem presentationComplexity_mono_height (χ : Character) {t H : ℝ}
    (ht : |t|≤H) : presentationComplexity χ t≤presentationComplexity χ H := by
  unfold presentationComplexity complexity
  have hH : 0≤H := (abs_nonneg t).trans ht
  rw [abs_of_nonneg hH]
  gcongr

theorem buffered_rectangle_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (hχ : ∀ j, (χ j).residue≠1) (T a : ℝ) (i : ℕ),
      2<T → 51/100≤a → a≤1 →
      HeckeDetectorZeros.zeroMaximum χ hχ (3*(i+1 : ℕ)*T)<a+2*e →
      ∀ (j : ι) (z : ℂ), a+6*e≤z.re → z.re≤2 →
      |z.im|≤(3*i+2 : ℕ)*T →
      LFunction (χ j) z≠0 ∧
      ‖LFunction (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
        C*(presentationComplexity (χ j) ((3*i+2 : ℕ)*T))^ε := by
  pm_3547 C hC hbound HeckeDyadicControl.buffered_original_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ hχ T a i hT ha ha' hmax j z hzl hzr hzi
  have hz6 : z ∈ closedBall ((2 : ℂ)+z.im*I) (2-a-6*e) := by
    pm_271
  pm_228
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow
  · unfold presentationComplexity complexity
    positivity
  · exact presentationComplexity_mono_height _ hzi
  · exact hε.le

theorem translated_rectangle_mem {a e σ freq l r H T : ℝ}
    (hl : a+6*e≤l+σ) (hr : r+σ≤2) (hlr : l≤ r) (hT : 0≤T)
    (hfreq : |freq|+T≤H) {s : ℂ} (hs : s ∈ (uIcc l r ×ℂ uIcc (-T) T)) :
    a+6*e≤(s+shift σ freq).re ∧ (s+shift σ freq).re≤2 ∧
      |(s+shift σ freq).im|≤H := by
  have hs' : s.re ∈ Icc l r ∧ s.im ∈ Icc (-T) T := by
    change s.re ∈ uIcc l r ∧ s.im ∈ uIcc (-T) T at hs
    simpa [uIcc_of_le hlr,uIcc_of_le (by linarith : -T≤T)] using hs
  have hsi : |s.im|≤T := abs_le.mpr hs'.2
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.1]
  constructor
  · simp only [add_re,shift_re]
    linarith [hs'.1.2]
  · have hi : (s+shift σ freq).im=s.im-freq := by simp [shift,sub_eq_add_neg]
    pm_515 hi abs_sub

end SevenEighths.HeckeDyadic

end

end OAI
