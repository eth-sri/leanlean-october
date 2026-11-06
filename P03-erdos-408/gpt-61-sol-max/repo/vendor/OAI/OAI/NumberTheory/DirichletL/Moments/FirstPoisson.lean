module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.Moments.Poisson

@[expose] public section

namespace OAI


open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstPoisson
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentFourier

section
variable (a b : ActualEisensteinCubic.O)

lemma principalCRT_scaled_left    hcop  (x : Residue a) :
    principalCRT a b hcop (scaledResidue a b (a * b) rfl x) =
      (Ideal.Quotient.mk _ b * x, 0) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp_all

lemma principalCRT_scaled_right    hcop   y  :
    principalCRT a b hcop (scaledResidue b a (a * b) (mul_comm a b) y) =
      (0, Ideal.Quotient.mk _ a * y) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  simp_all

theorem coprime_character_fourier    ha   hb 
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
     χa   χb 
     h  :
    (∑ x : Residue (a * b),
      χa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        χb (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          quotientTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      χa (Ideal.Quotient.mk _ b) * χb (Ideal.Quotient.mk _ a) *
        residueGauss a ha χa (frequencyReduction a (a * b) (dvd_mul_right a b) h) *
        residueGauss b hb χb (frequencyReduction b (a * b) (dvd_mul_left b a) h) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    aesop
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    aesop
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [map_mul, he, mul_add, AddChar.map_add_eq_mul,
    quotientTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    quotientTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, residueGauss, tsum_fintype]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

end

theorem residueGauss_inverse  d   hd 
     χ   h  :
    residueGauss d hd χ⁻¹ h = star (residueGauss d hd χ (-h)) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  have htrace (x : Residue d) : star (quotientTrace d hd x) = quotientTrace d hd (-x) := by
    rw [Complex.star_def, ← Complex.inv_eq_conj ((quotientTrace d hd).norm_apply x),
      AddChar.map_neg_eq_inv]
  simp only [residueGauss, tsum_fintype, star_sum, star_mul, MulChar.star_apply', htrace,
    neg_mul, neg_neg]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

end SevenEighths.CenteredMomentFirstPoisson


end OAI
