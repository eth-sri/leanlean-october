module

public import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
public import OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by
  intro x hx
  have hn : annulus x≠0 := by simpa using hx
  exact ⟨(lt_of_not_ge (fun h=>hn (annulus_zero_low x h))).le,
    (lt_of_not_ge (fun h=>hn (annulus_zero_high x h))).le⟩

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI
