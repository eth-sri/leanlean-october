module

public import OAI.NumberTheory.DirichletL.Detector.CalibrationCRT

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentFirstMixed
open CubicEisenstein
open CenteredMomentCommonSupport CenteredMomentFourier

theorem frequencyReduction_comp (d n M : ActualEisensteinCubic.O) (hd : d∣n) (hn : n∣M) (x : Residue M) :
    frequencyReduction d n hd (frequencyReduction n M hn x)=frequencyReduction d M (hd.trans hn) x := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

theorem three_factor_mixed_fourier (a b c : ActualEisensteinCubic.O) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (habc : IsCoprime a (b*c)) (hbc : IsCoprime b c)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue c)]
    [Fintype (Residue (b*c))] [Fintype (Residue (a*(b*c)))]
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ) (G : Residue c → ℂ)
    (h : Residue (a*(b*c))) :
    (∑ x : Residue (a*(b*c)),
      χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) x)*
      χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) x)*
      G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) x)*
        quotientTrace (a*(b*c)) (mul_ne_zero ha (mul_ne_zero hb hc)) (h*x)) =
      χa (Ideal.Quotient.mk _ (b*c))*χb (Ideal.Quotient.mk _ (a*c))*
        residueGauss a ha χa (frequencyReduction a (a*(b*c)) (dvd_mul_right _ _) h)*
        residueGauss b hb χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_right _ _) _) h)*
        (∑ y : Residue c,G (Ideal.Quotient.mk _ (a*b)*y)*
          quotientTrace c hc (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (dvd_mul_left _ _) _) h*y)) := by
  let F : Residue (b*c) → ℂ := fun y =>
    χb (frequencyReduction b (b*c) (by simp) y)*
      G (frequencyReduction c (b*c) (by simp) y)
  let h' := frequencyReduction (b*c) (a*(b*c)) (by simp) h
  have he (x : Residue (a*(b*c))) :
      χa (frequencyReduction a (a*(b*c)) (by simp) x)*
        F (frequencyReduction (b*c) (a*(b*c)) (by simp) x) =
      χa (frequencyReduction a (a*(b*c)) (by simp) x)*
        χb (frequencyReduction b (a*(b*c)) (dvd_mul_of_dvd_right (by simp) _) x)*
        G (frequencyReduction c (a*(b*c)) (dvd_mul_of_dvd_right (by simp) _) x) := by
    dsimp only [F]
    rw [frequencyReduction_comp,frequencyReduction_comp]
    ring
  simp_rw [← he]
  rw [ProbePhysical.coprime_mixed_fourier a (b*c) ha (by positivity) habc χa F h]
  have hf (y : Residue (b*c)) : F (Ideal.Quotient.mk _ a*y)=
      χb (Ideal.Quotient.mk _ a)*
        (χb (frequencyReduction b (b*c) (by simp) y)*
          G (Ideal.Quotient.mk _ a*frequencyReduction c (b*c) (by simp) y)) := by
    simp only [F,map_mul,frequencyReduction_mk]
    ring
  simp_rw [hf,mul_assoc]
  rw [← Finset.mul_sum]
  have hh := ProbePhysical.coprime_mixed_fourier b c hb hc hbc χb
    (fun y => G (Ideal.Quotient.mk _ a*y)) h'
  simp only [mul_assoc] at hh
  rw [hh]
  simp only [h',frequencyReduction_comp,map_mul,mul_assoc]
  ring

end SevenEighths.CenteredMomentFirstMixed

end

end OAI
