module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Detector.CalibrationCRT
public import OAI.NumberTheory.DirichletL.Detector.PhysicalPoisson

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CubicEisenstein GaussianShiftedPartition CanonicalRowCompletion
open CenteredMomentCommonSupport CenteredMomentFourier


def elementFourier (c : ActualEisensteinCubic.O) (hc : c≠0) (f : ActualEisensteinCubic.O → ℂ) (H : ActualEisensteinCubic.O)  :=
  ∑' x : Residue c, f (representative c x) * quotientTrace c hc (Ideal.Quotient.mk _ H*x)

lemma elementFourier_congr  c d   hc   hd   f   H 
    (he : c=d) : elementFourier c hc f H = elementFourier d hd f H := by
  subst d
  rfl

def movingQuotient (A s : ActualEisensteinCubic.O) (hs : s≠0) (x : Residue (A*s))  :=
  idealRowHom (representative (A*s) x) (Ideal.span {A}) *
    sexticGauss s hs (-representative (A*s) x)

section
variable (C : CalibrationData) (S : Finset (Ideal ActualEisensteinCubic.O)) (hS : ∀ P∈S, P.IsMaximal) (A s : ActualEisensteinCubic.O) (hA : A≠0) (hs : s≠0) (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (H : ActualEisensteinCubic.O) (hH : ¬IsCoprime (calibrationForSet S hS).generator H)

lemma movingQuotient_mk      m  :
    movingQuotient A s hs (Ideal.Quotient.mk _ m) =
      idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m) := by
  have hd : A*s ∣ representative (A*s) (Ideal.Quotient.mk _ m)-m :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (representative_spec _ _))
  have hA : representative (A*s) (Ideal.Quotient.mk _ m)-m ∈ (Ideal.span {A}:Ideal ActualEisensteinCubic.O) :=
    Ideal.mem_span_singleton.mpr ((dvd_mul_right A s).trans hd)
  have hs' : -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) ∈ (Ideal.span {s}:Ideal ActualEisensteinCubic.O) := by
    apply Ideal.mem_span_singleton.mpr
    rw [show -representative (A*s) (Ideal.Quotient.mk _ m)-(-m) =
      -(representative (A*s) (Ideal.Quotient.mk _ m)-m) by ring]
    exact dvd_neg.mpr ((dvd_mul_left s A).trans hd)
  unfold movingQuotient
  rw [idealRowHom_congr_mod _ _ _ hA, sexticGauss_frequency_congr s hs _ (-m) hs']

lemma physicalFourier_eq_element           :
    actualPhysicalFourier C A s hA hs H =
      elementFourier (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
        (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H := by
  change elementFourier ((C.generator*A)*s) (mul_ne_zero (mul_ne_zero C.generator_ne_zero hA) hs)
    (fun m => C.residueMonoid m * idealRowHom m (Ideal.span {A}) * sexticGauss s hs (-m)) H = _
  apply elementFourier_congr
  exact mul_assoc _ _ _

lemma physicalFourier_eq_mixed           :
    actualPhysicalFourier C A s hA hs H =
      ∑' x : Residue (C.generator*(A*s)),
        C.residue (frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x) *
          movingQuotient A s hs (frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x) *
          quotientTrace (C.generator*(A*s)) (mul_ne_zero C.generator_ne_zero (mul_ne_zero hA hs))
            (Ideal.Quotient.mk _ H*x) := by
  rw [physicalFourier_eq_element]
  unfold elementFourier
  apply tsum_congr
  intro x
  have he : Ideal.Quotient.mk (Ideal.span {C.generator*(A*s)})
      (representative (C.generator*(A*s)) x) = x := representative_spec _ _
  have hrA : frequencyReduction C.generator (C.generator*(A*s)) (dvd_mul_right _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  have hrB : frequencyReduction (A*s) (C.generator*(A*s)) (dvd_mul_left _ _) x =
      Ideal.Quotient.mk _ (representative (C.generator*(A*s)) x) := by
    conv_lhs => rw [← he]
    rfl
  rw [hrA, hrB, movingQuotient_mk]
  change _ = (C.residueMonoid _ * (_ * _)) * _

  ring

include hcop hH in
theorem actualPhysicalFourier_zero_off_calibration  
           
       
      :
    actualPhysicalFourier (calibrationForSet S hS) A s hA hs H=0 := by
  rw [physicalFourier_eq_mixed]
  exact calibration_mixed_fourier_zero S hS (A*s) (mul_ne_zero hA hs) hcop (movingQuotient A s hs) H hH

include hs hcop hH in
theorem actualCongruenceCoefficient_zero_off_calibration  
           
       
      :
    actualCongruenceCoefficient (calibrationForSet S hS) A s hA H=0 := by
  have he := actualPhysicalFourier_zero_off_calibration S hS A s hA hs hcop H hH
  rw [actualPhysicalFourier_eq] at he
  simp_all

end

end SevenEighths.ProbePhysical
end

end OAI
