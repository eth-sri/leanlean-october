module

public import OAI.NumberTheory.DirichletL.Detector.PhysicalFourier

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

def calibratedNumerator (C : CalibrationData) (A m : O)  :=
  C.residueMonoid m * idealRowHom m (Ideal.span {A})

lemma calibratedNumerator_congr  C   A m n 
    (h : m-n ∈ (Ideal.span {C.generator*A} : Ideal O)) :
    calibratedNumerator C A m = calibratedNumerator C A n := by
  have hd : C.generator*A ∣ m-n := Ideal.mem_span_singleton.mp h
  have hb : Ideal.Quotient.mk (Ideal.span {C.generator}) m =
      Ideal.Quotient.mk (Ideal.span {C.generator}) n := by
    apply Ideal.Quotient.eq.mpr
    exact Ideal.mem_span_singleton.mpr ((dvd_mul_right C.generator A).trans hd)
  have hA : m-n ∈ (Ideal.span {A} : Ideal O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_left A C.generator).trans hd)
  unfold calibratedNumerator CalibrationData.residueMonoid
  simp only [MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, hb, idealRowHom_congr_mod (Ideal.span {A}) m n hA]

def calibratedQuotient (C : CalibrationData) (A )
    (m : O ⧸ Ideal.span {C.generator*A})  :=
  calibratedNumerator C A (representative (C.generator*A) m)

lemma calibratedQuotient_mk  C   A m  :
    calibratedQuotient C A (Ideal.Quotient.mk _ m) = calibratedNumerator C A m := by
  apply calibratedNumerator_congr
  exact Ideal.Quotient.eq.mp (representative_spec _ _)

def outerQuotient (s : O) (d : O ⧸ Ideal.span {s})  :=
  idealRowHom (representative s d) (Ideal.span {s})

lemma rawFourier_outer  s   hs   h  :
    rawFourier s hs (outerQuotient s) h = sexticGauss s hs h := rfl

def actualCongruenceCoefficient (C : CalibrationData) (A s : O) (hA : A≠0) (H : O)  :=
  congruenceCoefficient (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA)
    (calibratedQuotient C A) (outerQuotient s) H

def actualPhysicalFourier (C : CalibrationData) (A s : O) (hA : A≠0) (hs : s≠0) (H : O)  :=
  ∑' m : O ⧸ Ideal.span {(C.generator*A)*s},
    calibratedNumerator C A (representative ((C.generator*A)*s) m) *
    sexticGauss s hs (-representative ((C.generator*A)*s) m) *
    quotientTrace ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
      (Ideal.Quotient.mk _ H*m)

theorem actualPhysicalFourier_eq  C   A s   hA   hs   H  :
    actualPhysicalFourier C A s hA hs H =
      (Ideal.absNorm (Ideal.span {s}):ℂ) * actualCongruenceCoefficient C A s hA H := by
  unfold actualCongruenceCoefficient
  rw [← fullFourier_eq_congruence (C.generator*A) s (mul_ne_zero C.generator_ne_zero hA) hs]
  unfold actualPhysicalFourier fullFourier
  apply tsum_congr
  intro m
  rw [rawFourier_outer]
  have he : conductorReduction (C.generator*A) s m =
      Ideal.Quotient.mk (Ideal.span {C.generator*A}) (representative ((C.generator*A)*s) m) := by
    conv_lhs => rw [← representative_spec ((C.generator*A)*s) m]
    rfl
  rw [he, calibratedQuotient_mk]

lemma calibratedNumerator_norm_le  C   A m  :
    ‖calibratedNumerator C A m‖≤1 := by
  let := ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hC : ‖C.residueMonoid m‖≤1 :=
    QuadraticInitialBound.norm_finite_character_le_one C.residue _
  rw [calibratedNumerator, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hC).trans (idealRowHom_norm _ _)

theorem actualCongruenceCoefficient_norm_le  C   A s 
     hA  (hs : s≠0)  H  :
    ‖actualCongruenceCoefficient C A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ) *
        (Ideal.absNorm (Ideal.span {C.generator*A}):ℝ) := by
  apply congruenceCoefficient_norm_le _ _ _ hs
  · intro m
    exact calibratedNumerator_norm_le C A _
  · intro d
    exact idealRowHom_norm _ _

end SevenEighths.ProbePhysical
end

end OAI
