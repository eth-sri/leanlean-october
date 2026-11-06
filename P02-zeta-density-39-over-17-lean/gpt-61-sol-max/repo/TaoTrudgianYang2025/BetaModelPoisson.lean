module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaDualScales
public import Mathlib.Analysis.Fourier.PoissonSummation

@[expose] public section

/-!
# Smooth model-phase kernels and exact Poisson summation

The kernel is the actual weighted exponential chi(x/N)*e(T*F(x/N)).
Smoothness uses only the original phase on the cutoff's support.
The Poisson identity is exact; no stationary-phase approximation or
sharp-endpoint replacement is included in this module.
-/

noncomputable section

open Set Expdb Filter MeasureTheory
open scoped Topology ContDiff FourierTransform BigOperators

namespace TaoTrudgianYang2025


section
variable (χ F : ℝ → ℝ)
include χ F

def modelPhaseWeightedKernel  (T N x : ℝ) : ℂ :=
  (χ (x/N) : ℂ) * (𝐞 (T*F (x/N)) : ℂ)

def modelPhaseFourierMode  (T N r : ℝ) : ℂ :=
  ∫ x : ℝ, (χ (x/N) : ℂ) * (𝐞 (modelPhaseFrequencyPhase F T N r x) : ℂ)
end


section
variable {χ F : ℝ → ℝ}
include χ F

theorem modelPhaseWeightedKernel_contDiff
     {σ δ : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (T N : ℝ) :
    ContDiff ℝ ∞ (modelPhaseWeightedKernel χ F T N) := by
  have hg : ContDiff ℝ ∞ (fun u => (χ u : ℂ)*(𝐞 (T*F u) : ℂ)) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu : u ∈ tsupport χ
    · have hFu := approximateModelPhase_contDiffAt hF (hs hu)
      have he : ContDiffAt ℝ ∞ (fun v => (𝐞 (T*F v) : ℂ)) u := by
        simp only [Real.fourierChar_apply]
        have hg : ContDiffAt ℝ ∞ (fun v => 2*Real.pi*(T*F v)) u :=
          contDiffAt_const.mul (contDiffAt_const.mul hFu)
        exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp u hg).mul contDiffAt_const).cexp
      exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u hχ.contDiffAt).mul he
    · have he : (fun v => (χ v : ℂ)*(𝐞 (T*F v) : ℂ)) =ᶠ[𝓝 u] (fun _ => 0) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with v hv
        simp only [hv,Pi.zero_apply,Complex.ofReal_zero,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  exact hg.comp (contDiff_id.div_const N)

theorem modelPhaseWeightedKernel_zero_of_not_mem
     {N x : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N)
    (hx : x ∉ Icc N (2*N)) (T : ℝ) :
    modelPhaseWeightedKernel χ F T N x = 0 := by
  have hnot : x/N ∉ tsupport χ := by
    intro h
    have hu := hs h
    apply hx
    exact ⟨by simpa only [one_mul] using ((lt_div_iff₀ hN).mp hu.1).le,
      ((div_lt_iff₀ hN).mp hu.2).le⟩
  simp only [modelPhaseWeightedKernel,image_eq_zero_of_notMem_tsupport hnot,
    Complex.ofReal_zero,zero_mul]

theorem modelPhaseWeightedKernel_hasCompactSupport
     {N : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N) (T : ℝ) :
    HasCompactSupport (modelPhaseWeightedKernel χ F T N) :=
  HasCompactSupport.intro isCompact_Icc
    (fun _ hx => modelPhaseWeightedKernel_zero_of_not_mem hs hN hx T)

section
variable {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N)
include σ δ N P hχ hs hF hN

def modelPhaseWeightedSchwartz
     (T : ℝ) :
    SchwartzMap ℝ ℂ :=
  (modelPhaseWeightedKernel_hasCompactSupport hs hN T).toSchwartzMap
    (modelPhaseWeightedKernel_contDiff hχ hs hF T N)

theorem modelPhaseWeightedSchwartz_apply
     (T x : ℝ) :
    modelPhaseWeightedSchwartz hχ hs hF hN T x =
      modelPhaseWeightedKernel χ F T N x := rfl

theorem modelPhaseWeightedSchwartz_fourier
     (T r : ℝ) :
    𝓕 (modelPhaseWeightedSchwartz hχ hs hF hN T) r =
      modelPhaseFourierMode χ F T N r := by
  rw [SchwartzMap.fourier_coe,Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards [] with x
  change 𝐞 (-(r*x)) • modelPhaseWeightedKernel χ F T N x =
    (χ (x/N) : ℂ)*(𝐞 (modelPhaseFrequencyPhase F T N r x) : ℂ)
  simp only [Circle.smul_def,smul_eq_mul,modelPhaseWeightedKernel,
    modelPhaseFrequencyPhase]
  rw [show T*F (x/N)-r*x = -(r*x)+T*F (x/N) by ring,
    AddChar.map_add_eq_mul,Circle.coe_mul]
  ring
end


theorem modelPhaseWeightedKernel_tsum_eq_finite
     {N : ℝ}
    (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2) (hN : 0 < N) (T : ℝ) :
    (∑' n : ℤ, modelPhaseWeightedKernel χ F T N n) =
      ∑ n ∈ Finset.Icc ⌈N⌉ ⌊2*N⌋, modelPhaseWeightedKernel χ F T N n := by
  apply tsum_eq_sum
  intro n hn
  apply modelPhaseWeightedKernel_zero_of_not_mem hs hN
  intro h
  apply hn
  exact Finset.mem_Icc.mpr ⟨Int.ceil_le.mpr h.1,Int.le_floor.mpr h.2⟩

theorem modelPhase_weighted_poisson
     {σ δ N : ℝ} {P : ℕ}
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ Ioo (1 : ℝ) 2)
    (hF : IsApproximateModelPhaseFunction F σ P δ) (hN : 0 < N) (T : ℝ) :
    (∑ n ∈ Finset.Icc ⌈N⌉ ⌊2*N⌋, modelPhaseWeightedKernel χ F T N n) =
      ∑' r : ℤ, modelPhaseFourierMode χ F T N r := by
  rw [← modelPhaseWeightedKernel_tsum_eq_finite hs hN T]
  have h := SchwartzMap.tsum_eq_tsum_fourier (modelPhaseWeightedSchwartz hχ hs hF hN T) 0
  simpa only [zero_add,AddCircle.coe_zero,fourier_eval_zero,mul_one,
    modelPhaseWeightedSchwartz_fourier,modelPhaseWeightedSchwartz_apply] using h
end



