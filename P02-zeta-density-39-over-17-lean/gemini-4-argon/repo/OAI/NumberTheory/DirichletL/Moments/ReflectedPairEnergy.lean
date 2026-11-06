module
public import OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure

lemma plain_frequency_control (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    intro I hI
    have hi := (ConcretePrimeRowBridge.mem_idealsUpTo.mp hI).1
    intro hz
    subst I
    simp at hi
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    have hh := HeckeInverseAmplification.scaleSupport_cover (logWindow V)
      (Real.exp (-M)) (Real.exp M) (Real.log X) (Real.log X) (Real.exp_pos M).le
      (logWindow_support V M hV) le_rfl
    simpa only [Real.exp_log hX] using hh
  have he (v : ℝ) : HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)=
      (X:ℂ)^(-(1/2:ℂ))*∑I∈S,HeckeDyadic.coefficient η false I*
        logWindow V ((I.absNorm:ℝ)/X)*logPhase v (Real.log ((I.absNorm:ℝ)/X)) := by
    rw [HeckeDetectorDyadicBridge.polynomial_eq_finite η false _ X 0 (2*Real.pi*v) S hc]
    congr 1
    apply Finset.sum_congr rfl
    intro I hI
    have hm := HeckeDetectorDyadicBridge.norm_phase (I.absNorm:ℝ) X
      (by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hs I hI))) hX 0 v
    simp only [neg_zero,Complex.cpow_zero,one_mul,Complex.zero_re,Complex.zero_im,sub_zero] at hm
    rw [hm]
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    rw [he,norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X)
    (hV : ∀y,V y≠0 → |y|≤M) (η : Character) (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  obtain ⟨hc,K,hK⟩ := plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)
