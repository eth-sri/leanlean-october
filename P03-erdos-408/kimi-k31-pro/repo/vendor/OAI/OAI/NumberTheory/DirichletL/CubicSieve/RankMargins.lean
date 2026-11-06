module

public import OAI.NumberTheory.DirichletL.RowCompletion.PolynomialHeight
public import OAI.NumberTheory.DirichletL.CubicSieve.DensityBudgets

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics Ideal NumberField
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap



namespace CompletedHeight

section

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open FourierBridge JointLogSeparation

def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))

lemma fixedLogReturnCLM_apply (a b : ℝ) (ha : 0 < a) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    fixedLogReturnCLM a b ha g x = positiveCutoff a b ha x •
      g (patchedLog (a/2) (max a b+a/2) (by linarith) x) := by
  rw [fixedLogReturnCLM,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      ((positiveCutoff a b ha).hasCompactSupport.hasTemperateGrowth (positiveCutoff a b ha).contDiff)]
  rfl

lemma positiveCutoff_support_bounds (a b : ℝ) (ha : 0 < a) (x : ℝ)
    (hx : positiveCutoff a b ha x ≠ 0) : x ∈ Icc (a/2) (max a b+a/2) := by
  have hm : x ∈ Function.support (positiveCutoff a b ha) := hx
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  constructor <;> linarith [hm.1,hm.2]

def uniformTwistedSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  fixedLogReturnCLM a b ha (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) t)

lemma uniformTwistedSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    uniformTwistedSchwartz W a b ha hs hW t x = normTwistedSource W t x := by
  rw [uniformTwistedSchwartz,fixedLogReturnCLM_apply,frequencyTwist_apply,
    CubicReflectionKernel.logSchwartz_apply]
  by_cases hc : positiveCutoff a b ha x=0
  · have hx : W x=0 := by
      by_contra hx
      have := positiveCutoff_one a b ha x (hs hx)
      exact zero_ne_one (hc.symm.trans this)
    simp only [hc,zero_smul,normTwistedSource,hx,mul_zero]
  · have hb := positiveCutoff_support_bounds a b ha x hc
    have hx : 0 < x := by linarith [hb.1]
    rw [patchedLog_eq_log _ _ _ x hb,Real.exp_log hx]
    by_cases hw : W x=0
    · simp only [hw,mul_zero,smul_zero,normTwistedSource]
    · rw [positiveCutoff_one a b ha x (hs hw),one_smul]
      rfl

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

end CompletedHeight

open MeasureTheory


end

end OAI
