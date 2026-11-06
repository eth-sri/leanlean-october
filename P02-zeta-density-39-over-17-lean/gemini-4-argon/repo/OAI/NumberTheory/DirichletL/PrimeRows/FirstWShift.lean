module
public import OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary
public import OAI.NumberTheory.DirichletL.PrimeRows.FirstWGrowth

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

lemma physicalRow_first_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,l≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z l hx hl hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by unfold height;nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_first_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr hx hl hz hxw
    (fun v hv t=>hbound v hv.1 t)
