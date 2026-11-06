module
public import OAI.NumberTheory.DirichletL.Detector.TupleRows
public import OAI.NumberTheory.DirichletL.Detector.CompensationActual
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma span_tupleProduct {K : ℕ} (p : Fin K→ O) (J : Finset (Fin K)) :
    Ideal.span {∏i∈J,p i}=∏i∈J,Ideal.span {p i} := by
  induction J using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Ideal.span_singleton_one,Ideal.one_eq_top]
  | @insert i J hi ih =>
    rw [Finset.prod_insert hi,←Ideal.span_singleton_mul_span_singleton,ih,Finset.prod_insert hi]

lemma primaryTuple_norm (P : PrimeIdeal) (hP : Supported P.val) :
    elementNorm (primaryGenerator P.val)=(Ideal.absNorm P.val:ℝ) := by
  unfold elementNorm
  rw [span_primaryGenerator_of_supported P.val hP]

theorem indexedCompensatedHigh_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (P : Fin K→ PrimeIdeal) (hP : Function.Injective P) (hs : ∀i,Supported (P i).val)
    (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      spectralCompensatedHigh S (Finset.univ.image P) η x w z
        (fun Q=>star (HeckeFamily.idealCoeff η Q.val)*(Ideal.absNorm Q.val:ℂ)^x)
        (fun Q=>(Ideal.absNorm Q.val:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedHigh
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  pm_6279
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (primaryGenerator (P i).val):ℂ)=(Ideal.absNorm (P i).val:ℂ) := by
    pm_7518
  pm_3878 HeckeFamily.elementCoeff primaryGenerator HeckeFamily.idealCoeff

end SevenEighths.ProbePhysical
end

end OAI
