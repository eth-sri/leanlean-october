module
public import OAI.NumberTheory.DirichletL.PrimeRows.UniformError
public import OAI.NumberTheory.DirichletL.PrimeRows.CentralWTail

public section

namespace OAI

open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_z_height_tail (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ H < |t.1.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by pf_11 t.1.2 Or.inl

end SevenEighths.ProbeHighRowFamily


end OAI
