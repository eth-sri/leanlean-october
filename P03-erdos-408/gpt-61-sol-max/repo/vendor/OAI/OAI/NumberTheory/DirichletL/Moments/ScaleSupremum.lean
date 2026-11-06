module

public import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationScaleSup

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace SevenEighths.CenteredMomentScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)

def scaleTest (W : ℝ→ℂ) (j : Fin 2)  :=
  if j=0 then W else scaleProfile W

lemma scaleTest_continuous  W  (hW : ContDiff ℝ ∞ W)  j  :
    Continuous (scaleTest W j) := by
  unfold scaleTest
  split
  · exact hW.continuous
  · exact scaleProfile_continuous W hW

lemma scaleTest_support  W   a b 
    (hs : Function.support W⊆Icc a b)  j  :
    Function.support (scaleTest W j)⊆Icc a b := by
  unfold scaleTest
  split
  · exact hs
  · exact scaleProfile_support W a b hs

end SevenEighths.CenteredMomentScaleSupremum

end

end OAI
