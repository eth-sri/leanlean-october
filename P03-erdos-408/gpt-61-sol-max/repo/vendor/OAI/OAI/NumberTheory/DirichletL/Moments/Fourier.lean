module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.Support
public import OAI.NumberTheory.DirichletL.Detector.Physical

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentFourier
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation

def frequencyReduction (d m : ActualEisensteinCubic.O) (h : d ∣ m)  :=
  Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr h)

@[simp] theorem frequencyReduction_mk  d m   h   x  :
    frequencyReduction d m h (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

theorem quotientTrace_scaled  d a m   hm 
     hd  (ha : a ≠ 0)  hm0 
     h   x  :
    quotientTrace m hm0 (h * scaledResidue d a m hm x) =
      quotientTrace d hd (frequencyReduction d m (hm ▸ dvd_mul_right d a) h * x) := by
  subst m
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective h
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht := quotientTrace_conductor_scale d a h hd ha (Ideal.Quotient.mk _ x)
  simp only [scaledResidue_mk, frequencyReduction_mk, ← map_mul]
  simpa only [← map_mul, conductorReduction, Ideal.Quotient.factor_mk, mul_assoc,
    mul_left_comm, mul_comm] using ht

def residueGauss (d : ActualEisensteinCubic.O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d)  :=
  ∑' x : Residue d, χ x * quotientTrace d hd (h * x)

theorem residueGauss_supported_mk  d 
     hd   h  :
    residueGauss d (supported_element_ne_zero d hd) (supportedModulusCharacter d hd)
      (Ideal.Quotient.mk _ h) = ProbePhysical.sexticGauss d (supported_element_ne_zero d hd) h := by
  apply tsum_congr
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [supportedModulusCharacter_mk, ProbePhysical.sexticGauss_coefficient_mk]

theorem fourierSum_scaled (d a m : ActualEisensteinCubic.O) (hm : m = d * a)
    (hd : d ≠ 0) (ha : a ≠ 0) (hm0 : m ≠ 0)
    [Fintype (Residue d)] (χ : MulChar (Residue d) ℂ)  h  :
    fourierSum (quotientTrace m hm0) (scaledResidue d a m hm) χ h =
      residueGauss d hd χ (frequencyReduction d m (hm ▸ dvd_mul_right d a) h) := by
  simp_all [fourierSum, residueGauss, quotientTrace_scaled]

theorem actual_gauss_correlation  u v   hu   hv 
    [Fintype (Residue u)] [Fintype (Residue v)] [Fintype (Residue (u * v))]
     χu   χv   j  :
    (∑ h : Residue (u * v),
      residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
        star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h)) *
          quotientTrace (u * v) (mul_ne_zero hu hv) (-(h * Ideal.Quotient.mk _ j))) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv j := by
  have h := fullModulusCorrelation_fourier u v χu χv j
    (quotientTrace (u * v) (mul_ne_zero hu hv))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive _ _)
  simp_rw [fourierSum_scaled u v (u * v) rfl hu hv (mul_ne_zero hu hv),
    fourierSum_scaled v u (u * v) (mul_comm u v) hv hu (mul_ne_zero hu hv)] at h
  exact h

def normalizedResidueGauss (d : ActualEisensteinCubic.O) (hd : d ≠ 0) (χ : MulChar (Residue d) ℂ)
    (h : Residue d)  :=
  residueGauss d hd χ h / (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)

end SevenEighths.CenteredMomentFourier
end

end OAI
