module
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstJoint
public import OAI.NumberTheory.DirichletL.PrimeRows.DiskControl
public import OAI.NumberTheory.DirichletL.PrimeRows.BufferedBin
public import OAI.NumberTheory.DirichletL.Hecke.StripActual
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_height_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    : ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|H|)^2*(3+|w.im|)^2 := by
  pm_3449
  pm_3447
  pm_5101 Cr hCr hreciprocal buffered_rectangle_reciprocal_bound
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) 0)/9
  pm_6488
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  pm_1113
  pm_3461
  pm_3446
  pm_541
  intro a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  pm_174
  pm_3460
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R*(3+|H|)^2 := by
    have hr := hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
    have hscale : Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)=R*(3+|H|)^2 := by
      dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
      rw [Real.rpow_one]
      ring
    simpa only [sourceDetectorFamily_denominator,hscale] using hr
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    pm_3448
    pm_462
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(R*(3+|H|)^2))*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      pm_3463
      pm_6163 hn'
      pm_3464
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
