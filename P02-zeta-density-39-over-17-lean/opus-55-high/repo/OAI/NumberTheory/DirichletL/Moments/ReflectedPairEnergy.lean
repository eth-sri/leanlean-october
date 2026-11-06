module
public import OAI.NumberTheory.DirichletL.Moments.ReflectedProfileMeasure
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory
namespace SevenEighths.CenteredMomentReflectedPairEnergy
open HeckeFamily FourierBridge CenteredMomentReflectedProfileMeasure
local notation "O" => HeckeFamily.O

section
variable (V : ℝ→ℂ) (M X : ℝ) (hX : 0<X) (hV : ∀y,V y≠0 → |y|≤M) (η : Character)
include V M X hX hV η
lemma plain_frequency_control :
    Continuous (fun v : ℝ=>HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) ∧
    ∃K : ℝ,∀v : ℝ,‖HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)‖≤K := by
  let S := HeckeInverseAmplification.scaleSupport (Real.log X) (Real.exp M)
  have hs : ∀I∈S,I≠0 := by
    pm_6951
    grind
  have hc : ∀I : Ideal O,I≠0 → logWindow V ((I.absNorm:ℝ)/X)≠0 → I∈S := by
    pm_2894
  pm_2893 he hs
  constructor
  · simp_rw [he]
    exact continuous_const.mul (continuous_finsetSum S (fun I _=>
      continuous_const.mul (logPhase_continuous_left _)))
  · refine ⟨‖(X:ℂ)^(-(1/2:ℂ))‖*∑I∈S,
      ‖HeckeDyadic.coefficient η false I*logWindow V ((I.absNorm:ℝ)/X)‖,?_⟩
    intro v
    pm_860 he
    pm_3719 I hI
    rw [norm_mul,logPhase_norm,mul_one]

lemma plain_density_integrable (density : 𝓢(ℝ,ℂ)) :
    Integrable (fun v : ℝ=>density v*HeckeDyadic.polynomial η false (logWindow V) X 0 (2*Real.pi*v)) := by
  pm_957 hc K hK plain_frequency_control V M X hX hV η
  exact (density.integrable (μ:=volume)).mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall hK)
end

end SevenEighths.CenteredMomentReflectedPairEnergy

end

end OAI
