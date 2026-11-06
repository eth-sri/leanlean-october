module
public import OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
public import OAI.NumberTheory.DirichletL.PrimeRows.SelectedFirst
public import OAI.NumberTheory.DirichletL.Detector.CompensatedRows
public import OAI.NumberTheory.DirichletL.PrimeRows.WeightedTuple
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma calibrated_physicalRow_first_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  pm_410
  simp_all
  · have hp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    apply DifferentiableAt.const_mul
    unfold physicalCompensatedRow continuedCompensatedRow
    apply DifferentiableAt.mul
    · exact ((HeckeOrigin.continued_differentiableAt _ (Or.inr hp)).const_mul _).mul_const _
    · apply DifferentiableAt.mul
      pm_3457 continuedCorrection_first_boundary_w
      · apply DifferentiableAt.fun_finsetProd
        intro P hP
        exact (continuedCompensatedLocal_first_differentiable_w η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z
          (by linarith) (by linarith)) w

alias contourTupleOutside := OAI.SevenEighths.ProbeHighRowFamily.tupleOutside

def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z)

theorem continuedPhysicalRowKernel_initial {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (t : ProbeMellinBoundary.HeightSpace) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)=
    compensatedRowOnLines η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z ⟨u.val,u.property.1⟩ t := by
  unfold continuedPhysicalRowKernel physicalCompensatedRow compensatedRowOnLines
  rw [continuedCompensatedRow_eq_indexed S hS P hP hPS η u _ _ _
    (by norm_num) (by norm_num) (by norm_num)]
  ring

lemma sourceMellinWeight_differentiable_w (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) :
    Differentiable ℂ (fun w=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hm : Differentiable ℂ (mellin W1) := fun w=>
    CubicReflectionKernel.compact_source_mellin_differentiable W1 a b ha hW (W1.smooth (⊤:ℕ∞)) w
  pm_3058 hy Y hY.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hy)

theorem continuedPhysicalRowKernel_differentiableAt_w {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) w := by
  exact (((sourceMellinWeight_differentiable_w W0 W1 a b ha hW X Y Z hY x z) w).mul_const _ |>.mul_const _).mul
    (calibrated_physicalRow_first_w eps heps S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu x w z hx hw hz hxw)

end SevenEighths.ProbeHighRowFamily

end

end OAI
