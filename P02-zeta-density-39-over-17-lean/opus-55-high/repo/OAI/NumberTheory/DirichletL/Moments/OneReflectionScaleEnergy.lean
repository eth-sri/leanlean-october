module
public import OAI.NumberTheory.DirichletL.Moments.ReflectedNormalization
public import OAI.NumberTheory.DirichletL.Moments.FrequencyScaleSupremum
public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set MeasureTheory
namespace SevenEighths.CenteredMomentOneReflectionScaleEnergy
open HeckeFamily HeckeDyadic CenteredMomentSectorLocalization
open CenteredMomentReflectedUniformPair CenteredMomentReflectedNormalization
open CenteredMomentScaleSupremum (scaleTest)

lemma annulus_complex_support :
    Function.support (fun x : ℝ=>(annulus x:ℂ))⊆Icc (1/4) 1 := by pm_2952

lemma annulus_complex_smooth : ContDiff ℝ ∞ (fun x : ℝ=>(annulus x:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

end SevenEighths.CenteredMomentOneReflectionScaleEnergy

end

end OAI
