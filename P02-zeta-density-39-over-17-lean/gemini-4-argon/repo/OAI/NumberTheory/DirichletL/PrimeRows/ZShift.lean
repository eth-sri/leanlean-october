module
public import OAI.NumberTheory.DirichletL.PrimeRows.ZBoundary

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary

theorem first_z_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hx hw (by linarith) hl
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro z hz
  exact (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hX hZ x w z hx hw (hl.trans hz.1) hxw).differentiableWithinAt
