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
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    
open ActualEisensteinCubic
 
open   RationalPrimeExtraction ShortDraftLatticeCount
 
 
 
open EisensteinEmbedding ConcreteTraceCRT  
 
 
open scoped LSeries.notation ArithmeticFunction.Moebius
 
 
 
 
 
 
 
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal      
 
 
 
 
 
 
 
 
 
 
 
 
 
 
 
open scoped ContDiff    
 
 
 
 
 
 
 
 
 
 
 
 
 
open   Set
 
 
 
 
 
 
 
 

namespace SecondPassArithmetic

end SecondPassArithmetic

 
namespace CanonicalRowCompletion
 
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
open SecondPassArithmetic hiding O
open FirstPassCubeLabels hiding O

end CanonicalRowCompletion

namespace CompletedHeight

section

 
 
open FourierBridge JointLogSeparation

def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a)  :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))

lemma fixedLogReturnCLM_apply  a b   ha   g   x  :
    fixedLogReturnCLM a b ha g x = positiveCutoff a b ha x •
      g (patchedLog (a/2) (max a b+a/2) (by linarith) x) := by
  rw [fixedLogReturnCLM,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      ((positiveCutoff a b ha).hasCompactSupport.hasTemperateGrowth (positiveCutoff a b ha).contDiff)]
  rfl

lemma positiveCutoff_support_bounds (a b : ℝ) (ha : 0 < a)  x 
    (hx : positiveCutoff a b ha x ≠ 0) : x ∈ Icc (a/2) (max a b+a/2) := by
  have hm : x ∈ Function.support (positiveCutoff a b ha) := hx
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  constructor <;> linarith [hm.1,hm.2]

def uniformTwistedSchwartz (W : ℝ→ℂ) (a b ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ)  :=
  fixedLogReturnCLM a b ha (frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) t)

lemma uniformTwistedSchwartz_apply  W   a b   ha 
     hs   hW   t x  :
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

 
 
open CompletedGauss

end CompletedHeight

 
 
namespace CompletedHeight
open CompletedGauss hiding O
 
open CanonicalQuadraticSieve hiding O

end CompletedHeight

 
 
namespace CompletedHeight
open CompletedGauss hiding O
open   CompletedDyadic
open CanonicalQuadraticSieve hiding O

end CompletedHeight

end

end OAI
