module

public import OAI.NumberTheory.DirichletL.Detector.CanonicalSlots
public import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
public import OAI.NumberTheory.DirichletL.Detector.MellinWindows

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        compensatedTuple η C W0 W1 (fun i=>primaryGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=>compensatedTuple η C W0 W1 p X Y Z)

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (mw : MellinWindows)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) mw.left mw.right
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) mw.left mw.right X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryGenerator (P i).val.val≠0 :=
    supported_primaryGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) mw.left mw.right X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) mw X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ mw.left mw.right T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) mw.left mw.right X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne mw
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) mw X Y Z hX hY hZ]
        exact tsum_mul_left.symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=>hs P)).symm

end SevenEighths.ProbePhysical
end

end OAI
