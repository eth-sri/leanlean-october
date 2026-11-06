module
public import Mathlib.Tactic

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import OAI.NumberTheory.DirichletL.Inversion.KernelSourceUniform
public import OAI.NumberTheory.DirichletL.CompactProfileFamily
public import OAI.NumberTheory.DirichletL.Descent.ActualProfiles
public import OAI.NumberTheory.DirichletL.Descent.DescentHeight

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
namespace SevenEighths.InverseClippingProfiles

def logWindow (v : ℝ → ℂ) (L ρ : ℝ) (y : ℝ)  := v ((y + ρ) / L)

def rootedWindow (v : ℝ → ℂ) (L ρ a H : ℝ) (y : ℝ)  :=
  (Real.exp (a * y - H * L) : ℂ) * logWindow v L ρ y

section
variable (v : ℝ → ℂ) (hv : ContDiff ℝ ∞ v) (M B L ρ a H : ℝ) (hL : 0 < L) (hρ : |ρ| ≤ B * L)

include hv in
lemma logWindow_contDiff       :
    ContDiff ℝ ∞ (logWindow v L ρ) := hv.comp ((contDiff_id.add contDiff_const).div_const L)

include hv in
lemma rootedWindow_contDiff       :
    ContDiff ℝ ∞ (rootedWindow v L ρ a H) := by
  apply ContDiff.mul _ (logWindow_contDiff v hv L ρ)
  exact Complex.ofRealCLM.contDiff.comp
    (Real.contDiff_exp.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

include hL hρ in
lemma logWindow_support    
       
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    Function.support (logWindow v L ρ) ⊆ Set.Icc (-(M+B)*L) ((M+B)*L) := by
  intro y hy
  have hy' := hv hy
  change -M ≤ (y+ρ)/L ∧ (y+ρ)/L ≤ M at hy'
  have hl := (le_div_iff₀ hL).mp hy'.1
  have hu := (div_le_iff₀ hL).mp hy'.2
  have hr := abs_le.mp hρ
  constructor <;> nlinarith

include hL hρ in
lemma rootedWindow_compact    
       
    (hv : Function.support v ⊆ Set.Icc (-M) M) :
    HasCompactSupport (rootedWindow v L ρ a H) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro y hy
  apply logWindow_support v M B L ρ hL hρ hv
  exact (mul_ne_zero_iff.mp hy).2

end

def rootSchwartz (v : 𝓢(ℝ, ℂ)) (M B L ρ a H : ℝ)
    (hL : 0 < L) (hρ : |ρ| ≤ B * L)
    (hv : Function.support v ⊆ Set.Icc (-M) M)  :=
  (rootedWindow_compact v M B L ρ a H hL hρ hv).toSchwartzMap
    (rootedWindow_contDiff v (v.smooth ⊤) L ρ a H)



def rootDerivativeBound (v : 𝓢(ℝ, ℂ)) (a : ℝ) (n : ℕ)  :=
  ∑ i ∈ Finset.range (n+1), (2:ℝ)^i * (1+|a|)^i * derivativeSeminormSum v 0 i

def momentOrder (J : ℕ)  := J + (volume : Measure ℝ).integrablePower

theorem clipping_ratio_of_column_witness (w : ℝ → ℂ) (Z N q a b : ℝ)
    (hZ : 1 < Z) (hq : 1 ≤ q) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hwitness : w (q / Z^N) ≠ 0) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  have hz : 0 < Z := by linarith
  have hn : 0 ≤ max 0 N-N := sub_nonneg.mpr (le_max_right _ _)
  refine ⟨Real.one_le_rpow hZ.le hn, ?_⟩
  by_cases hN : 0 ≤ N
  · simpa [max_eq_right hN] using hb
  · have hN' : N ≤ 0 := le_of_lt (lt_of_not_ge hN)
    rw [max_eq_left hN', zero_sub, Real.rpow_neg hz.le]
    have hsupport := (hw hwitness).2
    calc
      _ = 1 / Z^N := (one_div _).symm
      _ ≤ q / Z^N := div_le_div_of_nonneg_right hq (Real.rpow_nonneg hz.le _)
      _ ≤ b := hsupport

open InverseMoment

def firstRootExponent (y : Fin 9 → ℝ)  :=
  -y 3-y 4/2-y 5-(y 7+y 8)/2

def secondRootExponent (y : Fin 6 → ℝ)  :=
  -y 1-y 2-(y 4+y 5)/2

def firstRootSlope : Fin 9 → ℝ := ![0,0,0,-1,-(1/2),-1,0,-(1/2),-(1/2)]
def secondRootSlope : Fin 6 → ℝ := ![0,-1,-1,0,-(1/2),-(1/2)]

section
variable (V : ℝ → ℂ) (y : ℝ)

lemma inverseNormWindow_exp     :
    inverseNormWindow V y = (Real.exp (-y) : ℂ)*V y := by
  simp only [inverseNormWindow, Real.exp_neg, Complex.ofReal_inv, div_eq_mul_inv]
  ring

lemma inverseRootWindow_exp     :
    inverseRootWindow V y = (Real.exp (-(y/2)) : ℂ)*V y := by
  rw [inverseRootWindow, ← Real.exp_half, Real.exp_neg, Complex.ofReal_inv]
  ring

end

section
variable (V : Fin 9 → ℝ → ℂ) (f : ℝ → ℂ) (ρ θ t : ℝ)

theorem firstRootWindows_exp    i   y  :
    firstRootWindows V i y = (Real.exp (firstRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [firstRootWindows, firstRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem secondRootWindows_exp  V   i   y  :
    secondRootWindows V i y = (Real.exp (secondRootSlope i*y) : ℂ)*V i y := by
  fin_cases i <;> simp [secondRootWindows, secondRootSlope, inverseNormWindow_exp,
    inverseRootWindow_exp, neg_mul]
  all_goals left; congr 1; ring

theorem firstRootWindows_prod    y  :
    (∏ i, firstRootWindows V i (y i)) =
      (Real.exp (firstRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [firstRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [firstRootSlope, firstRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem secondRootWindows_prod  V   y  :
    (∏ i, secondRootWindows V i (y i)) =
      (Real.exp (secondRootExponent y) : ℂ) * ∏ i, V i (y i) := by
  simp_rw [secondRootWindows_exp]
  rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  simp only [secondRootSlope, secondRootExponent, Fin.sum_univ_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one]
  norm_num
  ring

theorem fourier_phase_shift     :
    (𝓕 (fun y => logPhase θ y * f y)) t = (𝓕 f) (t-θ) := by
  simp only [Real.fourier_eq', logPhase, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translate     :
    (𝓕 (fun y => f (y+ρ))) t = logPhase t ρ * (𝓕 f) t := by
  have h := congrFun
    (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f ρ) t
  change _ = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t at h
  have h' : (𝓕 (fun y => f (y+ρ))) t = Real.fourierChar (inner ℝ ρ t) • (𝓕 f) t := by
    assumption
  rw [h']
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, logPhase]
  congr 2
  simp only [RCLike.inner_apply, conj_trivial]
  push_cast
  ring

theorem fourier_translated_twist     :
    (𝓕 (fun y => logPhase θ y * f (y+ρ))) t =
      logPhase (t-θ) ρ * (𝓕 f) (t-θ) := by
  rw [fourier_phase_shift, fourier_translate]

theorem norm_fourier_translated_twist     :
    ‖(𝓕 (fun y => logPhase θ y * f (y+ρ))) t‖ = ‖(𝓕 f) (t-θ)‖ := by
  rw [fourier_translated_twist, norm_mul, logPhase_norm, one_mul]

end

theorem translated_twist_moment_uniform (g : 𝓢(ℝ, ℂ))  J  :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ θ : ℝ,
      Integrable (fun t : ℝ => (1+‖t‖)^J *
        ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ∧
      (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖) ≤
        C*(1+‖θ‖)^(momentOrder J) := by
  obtain ⟨C, hC, hb⟩ := InverseMoment.frequencyTwist_fourier_moment J g
  refine ⟨C, hC, ?_⟩
  intro ρ θ
  have he (t : ℝ) : ‖(𝓕 (fun y => logPhase θ y * g (y+ρ))) t‖ =
      ‖(𝓕 (frequencyTwist g θ)) t‖ := by
    rw [norm_fourier_translated_twist, congrFun (SchwartzMap.fourier_coe _) t]
    have hf : (frequencyTwist g θ : ℝ → ℂ) = fun y => logPhase θ y * g y := by
      funext y
      exact frequencyTwist_apply g θ y
    rw [hf, fourier_phase_shift]
  simp_rw [he]
  exact ⟨AnalyticBridge.schwartz_fourier_one_plus_integrable _ _, hb θ⟩

def firstBalancedSlope : Fin 9 → ℝ := ![1/2,1/2,1,-1,-(1/2),0,0,0,0]
def secondBalancedSlope : Fin 6 → ℝ := ![1,-1,0,0,0,0]

end SevenEighths.InverseClippingProfiles

end

end OAI
