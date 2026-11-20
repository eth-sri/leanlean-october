module

public import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalShift
public import OAI.NumberTheory.DirichletL.Detector.PrincipalSplit
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (l : ℝ) (hl : (1/2:ℝ)≤l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u mw.left mw.right X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) mw.left mw.right X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u mw.left mw.right X Y Z l q ∂(volume.prod volume) := by
  let p : Fin K→O := fun i=>CompletedGauss.primaryGenerator (P i).val
  have hp : ∀i,p i≠0 := fun i=>(supported_primeGenerator_prime (P i)
    (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun v : NonzeroFrequency=>v.val) h)
  have hF := compensatedRows_counting_product_integrable e he η S (calibrationForSet S hmax) p hp
    mw X Y Z hX hY hZ
  have hi : Integrable (compensatedRowOnLines η S (calibrationForSet S hmax) p mw.left mw.right X Y Z (e u))
      heightMeasure := (Measure.ae_count_iff.mp hF.prod_right_ae) u
  have heq (q : ℝ×ℝ) :
      (∫t : ℝ,compensatedRowOnLines η S (calibrationForSet S hmax) p mw.left mw.right X Y Z (e u) (q,t))=
        shiftedRowInner S hS hmax P hPS η u mw.left mw.right X Y Z l q := by
    have hs := nonprincipal_w_integral_eq eps heps S hS hfirst hmax P hPS η u hu mw.left mw.right
      mw.rightLo mw.rightHi mw.right_pos mw.right_support X Y Z hY ((3:ℂ)+q.1*I) ((2:ℂ)+q.2*I) l 3 hl3 hl
      (by norm_num) (by norm_num) (by norm_num;linarith)
    unfold shiftedRowInner
    rw [hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>(continuedPhysicalRowKernel_initial S hS hmax P hP hPS
      η u mw.left mw.right X Y Z (q,t)).symm)
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall heq)
  · unfold rowIntegral
    rw [integral_prod _ hi]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall heq)

end SevenEighths.ProbeHighRowFamily

end

end OAI
