module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.GaussSum.GaussianFiberMass

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
 
open Filter Asymptotics MeasureTheory
open scoped Topology
open   Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
 
open Filter    

namespace GaussianMoment

theorem x_exp_neg_le  x  (_hx : 0 ≤ x) :
    x * Real.exp (-x) ≤ 2 * Real.exp (-(x / 2)) := by
  have hlin : x / 2 ≤ Real.exp (x / 2) := by
    have h := Real.add_one_le_exp (x / 2)
    linarith
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-x)).le
  calc
    x * Real.exp (-x) = 2 * ((x / 2) * Real.exp (-x)) := by ring
    _ ≤ 2 * (Real.exp (x / 2) * Real.exp (-x)) := by
      gcongr
    _ = 2 * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf

theorem gaussian_moment_term_bound  q t  (hq : 0 ≤ q) (ht : 0 < t) :
    q * Real.exp (-t * q) ≤
      (2 / t) * Real.exp (-(t * q / 2)) := by
  have h := x_exp_neg_le (t * q) (mul_nonneg ht.le hq)
  have hpos : 0 ≤ t := ht.le
  calc
    q * Real.exp (-t * q) =
        ((t * q) * Real.exp (-(t * q))) / t := by
          field_simp
    _ ≤ (2 * Real.exp (-(t * q / 2))) / t :=
      div_le_div_of_nonneg_right h hpos
    _ = (2 / t) * Real.exp (-(t * q / 2)) := by ring

end GaussianMoment
namespace ActualEisensteinCubic

section

open ShortDraftLatticeCount

section
variable (r : ℕ)

theorem rational_qNat   (hr : r ≠ 0) :
    qNat (r : O) = r ^ 2 := by
  calc
    qNat (r : O) = Ideal.absNorm (Ideal.span {(r : O)}) :=
      qNat_eq_absNorm_span _
    _ = Nat.card (O ⧸ Ideal.span {(r : O)}) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    _ = r ^ 2 := rational_modulus_card r hr

theorem rational_qNat_eq_one_iff  x  : qNat x = 1 ↔ IsUnit x := by
  rw [qNat_eq_absNorm_span, Ideal.absNorm_eq_one_iff,
    Ideal.span_singleton_eq_top]

theorem rational_prime_factor_cases   (hr : r.Prime) :
    (Ideal.span {(r : O)} : Ideal O).IsMaximal ∨
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧ (r : O) = a * b ∧
      qNat a = r ∧ qNat b = r ∧
      (Ideal.span {a} : Ideal O).IsMaximal ∧
      (Ideal.span {b} : Ideal O).IsMaximal := by
  have hru : ¬ IsUnit (r : O) := by
    rw [← rational_qNat_eq_one_iff, rational_qNat r hr.ne_zero]
    have htwo := hr.two_le
    nlinarith
  rcases irreducible_or_factor hru with hirr | ⟨a, b, hna, hnb, hab⟩
  · left
    exact PrincipalIdealRing.isMaximal_of_irreducible hirr
  · right
    have hqa1 : qNat a ≠ 1 := by
      simp_all [rational_qNat_eq_one_iff]
    have hqb1 : qNat b ≠ 1 := by
      simp_all [rational_qNat_eq_one_iff]
    have hqprod : qNat a * qNat b = r ^ 2 := by
      rw [← qNat_mul, ← hab, rational_qNat r hr.ne_zero]
    obtain ⟨hqa, hqb⟩ := (hr.mul_eq_prime_sq_iff hqa1 hqb1).mp hqprod
    have ha0 : a ≠ 0 := by
      aesop
    have hb0 : b ≠ 0 := by
      aesop
    have hpa : Prime a := by
      apply Ideal.prime_of_irreducible_absNorm_span ha0
      rw [← qNat_eq_absNorm_span, hqa]
      exact hr.prime.irreducible
    have hpb : Prime b := by
      apply Ideal.prime_of_irreducible_absNorm_span hb0
      rw [← qNat_eq_absNorm_span, hqb]
      exact hr.prime.irreducible
    exact ⟨a, b, ha0, hb0, hab, hqa, hqb,
      PrincipalIdealRing.isMaximal_of_irreducible hpa.irreducible,
      PrincipalIdealRing.isMaximal_of_irreducible hpb.irreducible⟩

theorem maximal_ideal_eq_span_of_mem
    (Q : Ideal O) (hQ : Q.IsMaximal)  a 
    (ha : (Ideal.span {a} : Ideal O).IsMaximal) (hamem : a ∈ Q) :
    Q = Ideal.span {a} := by
  have hle : (Ideal.span {a} : Ideal O) ≤ Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr hamem
  exact (ha.eq_of_le hQ.ne_top hle).symm

theorem rational_prime_ideal_cover   (hr : r.Prime) :
    ∃ a b : O, a ≠ 0 ∧ b ≠ 0 ∧
      r ≤ qNat a ∧ r ≤ qNat b ∧
      ∀ (Q : Ideal O), Q.IsMaximal → (r : O) ∈ Q →
        Q = Ideal.span {a} ∨ Q = Ideal.span {b} := by
  rcases rational_prime_factor_cases r hr with hmax |
      ⟨a, b, ha0, hb0, hab, hqa, hqb, hma, hmb⟩
  · have hr0 : (r : O) ≠ 0 := by exact_mod_cast hr.ne_zero
    have hq : qNat (r : O) = r ^ 2 := rational_qNat r hr.ne_zero
    have hrle : r ≤ r ^ 2 := by nlinarith [hr.two_le]
    refine ⟨(r : O), (r : O), hr0, hr0, ?_, ?_, ?_⟩
    · rw [hq]; exact hrle
    · rw [hq]; exact hrle
    aesop (add safe [maximal_ideal_eq_span_of_mem, O])
  · refine ⟨a, b, ha0, hb0, ?_, ?_, ?_⟩
    · rw [hqa]
    · rw [hqb]
    · intro Q hQ hrQ
      rw [hab] at hrQ
      rcases hQ.isPrime.mem_or_mem hrQ with haQ | hbQ
      · exact Or.inl (maximal_ideal_eq_span_of_mem Q hQ a hma haQ)
      · exact Or.inr (maximal_ideal_eq_span_of_mem Q hQ b hmb hbQ)

end

end

end ActualEisensteinCubic

open ActualEisensteinCubic

namespace RationalPrimeExtraction

noncomputable def selected (Y : ℝ)  :=
  (Finset.Ioc ⌊Y / 3⌋₊ ⌊Y⌋₊).filter Nat.Prime

end RationalPrimeExtraction

namespace OscSpecial

section
variable {a b d : ℂ} {R : ℝ} (ha : a ≠ 0) (hdet : a * d - b ^ 2 = (R : ℂ))

private theorem real_quadratic_lower {u v w : ℝ}
    (hu : 0 < u) (hv : 0 < v) (_hdet : 0 < u * v - w ^ 2)
     x y  :
    ((u * v - w ^ 2) / (u + v)) * (x ^ 2 + y ^ 2) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 := by
  have hsum : 0 < u + v := add_pos hu hv
  
  have hsq := add_nonneg (sq_nonneg (u * x - w * y))
    (sq_nonneg (w * x - v * y))
  have hnum : (u * v - w ^ 2) * (x ^ 2 + y ^ 2) ≤
      (u + v) * (u * x ^ 2 - 2 * w * x * y + v * y ^ 2) := by
    linarith
  have h : ((u * v - w ^ 2) * (x ^ 2 + y ^ 2)) / (u + v) ≤
      u * x ^ 2 - 2 * w * x * y + v * y ^ 2 :=
    (div_le_iff₀ hsum).2 (by simpa only [mul_comm] using hnum)
  simpa only [div_mul_eq_mul_div] using h

include ha hdet in
private theorem schur_eq_real_det_div    
        :
    RankTwoComplex.schur a b d = (R : ℂ) / a := by
  unfold RankTwoComplex.schur
  rw [← hdet]
  field_simp [ha]

include hdet in
private theorem determinant_real_components    
      :
    a.re * d.re - a.im * d.im - b.re ^ 2 + b.im ^ 2 = R ∧
    a.re * d.im + a.im * d.re - 2 * b.re * b.im = 0 := by
  constructor
  · have h := congrArg Complex.re hdet
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re] at h
    have hb : (b ^ 2).re = b.re ^ 2 - b.im ^ 2 := by
      rw [pow_two, Complex.mul_re]
      ring
    rw [hb] at h
    linarith
  · have h := congrArg Complex.im hdet
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im] at h
    have hb : (b ^ 2).im = 2 * b.re * b.im := by
      rw [pow_two, Complex.mul_im]
      ring
    rw [hb] at h
    linarith

include ha hdet in
private theorem first_real_coefficients    
        :
    (a⁻¹).re = a.re / Complex.normSq a ∧
    (RankTwoComplex.schur a b d).re = R * a.re / Complex.normSq a ∧
    (Complex.I * b / a).re =
      (b.re * a.im - b.im * a.re) / Complex.normSq a := by
  constructor
  · exact Complex.inv_re a
  constructor
  · rw [schur_eq_real_det_div ha hdet]
    simp [Complex.div_re]
  · rw [Complex.div_re]
    simp [Complex.mul_re, Complex.mul_im]
    ring

include ha hdet in
private theorem first_real_determinant    
        :
    (a.re / Complex.normSq a) * (R * a.re / Complex.normSq a) -
      ((b.re * a.im - b.im * a.re) / Complex.normSq a) ^ 2 =
      (a.re * d.re - b.re ^ 2) / Complex.normSq a := by
  have hN : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  obtain ⟨hr, hi⟩ := determinant_real_components hdet
  have hid :
      R * a.re ^ 2 - (b.re * a.im - b.im * a.re) ^ 2 =
      (a.re ^ 2 + a.im ^ 2) * (a.re * d.re - b.re ^ 2) -
        a.im * a.re * (a.re * d.im + a.im * d.re - 2 * b.re * b.im) := by
    rw [← hr]
    ring
  rw [hi, mul_zero, sub_zero] at hid
  simp only [Complex.normSq_apply] at hN ⊢
  grind

end

private noncomputable def middleForm (a b d : ℂ) (z : ℤ × ℤ)  :=
  a⁻¹ * (z.1 : ℂ) ^ 2 -
    2 * (Complex.I * b / a) * (z.1 : ℂ) * (z.2 : ℂ) +
    RankTwoComplex.schur a b d * (z.2 : ℂ) ^ 2

section
variable (a b d : ℂ) (z : ℤ × ℤ)

private theorem middleForm_real     :
    (middleForm a b d z).re =
      (a⁻¹).re * (z.1 : ℝ) ^ 2 -
      2 * (Complex.I * b / a).re * (z.1 : ℝ) * (z.2 : ℝ) +
      (RankTwoComplex.schur a b d).re * (z.2 : ℝ) ^ 2 := by
  simp [middleForm, Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two]

private theorem middleForm_exp     :
    RankTwoComplex.firstGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * middleForm a b d z) := by
  simp only [RankTwoComplex.firstGaussian, middleForm]
  rw [← Complex.exp_add]
  congr 1
  simp [div_eq_mul_inv]
  ring

end

private theorem firstGaussian_summable  {a b d}  {R : ℝ}
    (ha : 0 < a.re) (hR : 0 < R)
    (hdet : a * d - b ^ 2 = (R : ℂ))
    (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.firstGaussian a b d) := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  let u : ℝ := a.re / Complex.normSq a
  let v : ℝ := R * a.re / Complex.normSq a
  let w : ℝ := (b.re * a.im - b.im * a.re) / Complex.normSq a
  have hu : 0 < u := div_pos ha hN
  have hv : 0 < v := div_pos (mul_pos hR ha) hN
  have hq : 0 < u * v - w ^ 2 := by
    dsimp [u, v, w]
    rw [first_real_determinant ha0 hdet]
    exact div_pos hpd hN
  let eps : ℝ := (u * v - w ^ 2) / (u + v)
  have heps : 0 < eps := div_pos hq (add_pos hu hv)
  have hcoeff := first_real_coefficients ha0 hdet
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (middleForm a b d z).re := by
    rw [middleForm_real, hcoeff.1, hcoeff.2.1, hcoeff.2.2]
    solve_by_elim [real_quadratic_lower]
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (middleForm a b d) heps hbound).congr (fun z => (middleForm_exp a b d z).symm)

private noncomputable def originalForm (a b d : ℂ) (z : ℤ × ℤ)  :=
  a * (z.1 : ℂ) ^ 2 + 2 * b * (z.1 : ℂ) * (z.2 : ℂ) + d * (z.2 : ℂ) ^ 2

private theorem originalForm_real (a b d : ℂ) (z : ℤ × ℤ) :
    (originalForm a b d z).re =
      a.re * (z.1 : ℝ) ^ 2 + 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
      d.re * (z.2 : ℝ) ^ 2 := by
  simp [originalForm, Complex.add_re, Complex.mul_re, pow_two]

private theorem originalGaussian_summable  {a b d} 
    (ha : 0 < a.re) (hpd : 0 < a.re * d.re - b.re ^ 2) :
    Summable (RankTwoComplex.binaryGaussian a b d) := by
  have hd : 0 < d.re := by
    by_contra h
    have h' : d.re ≤ 0 := le_of_not_gt h
    have hm := mul_nonpos_of_nonneg_of_nonpos ha.le h'
    nlinarith [sq_nonneg b.re]
  let eps : ℝ := (a.re * d.re - b.re ^ 2) / (a.re + d.re)
  have heps : 0 < eps := div_pos hpd (add_pos ha hd)
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (originalForm a b d z).re := by
    rw [originalForm_real]
    dsimp [eps]
    convert real_quadratic_lower (w := -b.re) ha hd (by simpa using hpd)
      (z.1 : ℝ) (z.2 : ℝ) using 1 <;> ring
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (originalForm a b d) heps hbound).congr (fun z => rfl)

noncomputable def inverseForm (a b d : ℂ) (R : ℝ) (z : ℤ × ℤ)  :=
  (d * (z.1 : ℂ) ^ 2 - 2 * b * (z.1 : ℂ) * (z.2 : ℂ) +
    a * (z.2 : ℂ) ^ 2) / (R : ℂ)

private theorem inverseForm_real  a b d   {R}  (hR : R ≠ 0)  z  :
    (inverseForm a b d R z).re =
      (d.re * (z.1 : ℝ) ^ 2 - 2 * b.re * (z.1 : ℝ) * (z.2 : ℝ) +
        a.re * (z.2 : ℝ) ^ 2) / R := by
  simp [inverseForm, Complex.div_re, Complex.add_re, Complex.sub_re,
    Complex.mul_re, Complex.normSq_apply, pow_two]
  field_simp [hR]

theorem dualGaussian_inverseForm {a b d : ℂ} {R : ℝ}
    (ha : a ≠ 0) (hR : R ≠ 0)
    (hdet : a * d - b ^ 2 = (R : ℂ))  z  :
    RankTwoComplex.dualGaussian a b d z =
      Complex.exp (-(Real.pi : ℂ) * inverseForm a b d R z) := by
  unfold RankTwoComplex.dualGaussian
  rw [← Complex.exp_add]
  congr 1
  rw [schur_eq_real_det_div ha hdet]
  dsimp [inverseForm]
  have hdet0 : a * d - b ^ 2 ≠ 0 := by rw [hdet]; exact_mod_cast hR
  rw [← hdet]
  field_simp [ha, hdet0] ; ring

section
variable {a b d : ℂ} {R : ℝ} (ha : 0 < a.re) (hR : 0 < R) (hdet : a * d - b ^ 2 = (R : ℂ)) (hpd : 0 < a.re * d.re - b.re ^ 2)

include ha hR hdet hpd in
private theorem dualGaussian_summable    
       
     
      :
    Summable (RankTwoComplex.dualGaussian a b d) := by
  have hd : 0 < d.re := by
    nlinarith
  let eps : ℝ := ((d.re * a.re - b.re ^ 2) / (d.re + a.re)) / R
  have heps : 0 < eps := div_pos (div_pos (by nlinarith [hpd]) (add_pos hd ha)) hR
  have hbound (z : ℤ × ℤ) :
      eps * ((z.1 : ℝ) ^ 2 + (z.2 : ℝ) ^ 2) ≤
      (inverseForm a b d R z).re := by
    rw [inverseForm_real a b d hR.ne']
    have hbase := real_quadratic_lower (u := d.re) (v := a.re) (w := b.re)
      hd ha (by nlinarith [hpd]) (z.1 : ℝ) (z.2 : ℝ)
    have hdivide := div_le_div_of_nonneg_right hbase hR.le
    grind
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  exact (RankTwoComplex.lattice_gaussian_summable_of_re_bound
    (inverseForm a b d R) heps hbound).congr
      (fun z => (dualGaussian_inverseForm ha0 hR.ne' hdet z).symm)

include ha hR hdet hpd in
theorem binary_gaussian_poisson_real_det    
       
     
      :
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.mpr ha0
  have hδ : 0 < (RankTwoComplex.schur a b d).re := by
    rw [schur_eq_real_det_div ha0 hdet]
    simpa [Complex.div_re] using div_pos (mul_pos hR ha) hN
  have hO := originalGaussian_summable ha hpd
  have hM := firstGaussian_summable ha hR hdet hpd
  have hD := dualGaussian_summable ha hR hdet hpd
  calc
    (∑' z : ℤ × ℤ, RankTwoComplex.binaryGaussian a b d z) =
      (1 / a ^ (1 / 2 : ℂ)) *
        (1 / (RankTwoComplex.schur a b d) ^ (1 / 2 : ℂ)) *
        ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z :=
      RankTwoComplex.binary_gaussian_poisson ha hδ hO hM hD
    _ = (1 / ((R : ℂ) ^ (1 / 2 : ℂ))) *
          ∑' z : ℤ × ℤ, RankTwoComplex.dualGaussian a b d z := by
      rw [schur_eq_real_det_div ha0 hdet,
        SqrtBranch.prefactor_product ha hR]

end

noncomputable def q (a b : ℝ)  := a ^ 2 - a * b + b ^ 2
noncomputable def A (η a b : ℝ)  :=
  (η : ℂ) + 2 * Complex.I * (b : ℂ) / (q a b : ℂ)
noncomputable def B (η a b : ℝ)  :=
  -(η : ℂ) / 2 - 2 * Complex.I * (a : ℂ) / (q a b : ℂ)
noncomputable def D (η a b : ℝ)  :=
  (η : ℂ) + 2 * Complex.I * ((a-b : ℝ) : ℂ) / (q a b : ℂ)
noncomputable def R (η a b : ℝ)  := 4 / q a b + 3 * η ^ 2 / 4

section
variable (η a b : ℝ)

theorem coefficient_re   (_hq : q a b ≠ 0) :
    (A η a b).re = η ∧ (B η a b).re = -η / 2 ∧ (D η a b).re = η := by
  simp [A, B, D, Complex.div_re, Complex.normSq_apply]

theorem oscillatory_determinant   (hq : q a b ≠ 0) :
    A η a b * D η a b - (B η a b) ^ 2 = (R η a b : ℂ) := by
  have hqc : (q a b : ℂ) ≠ 0 := by exact_mod_cast hq
  have hqexpr : (q a b : ℂ) = (a : ℂ) ^ 2 - (a : ℂ) * (b : ℂ) + (b : ℂ) ^ 2 := by
    simp [q]
  have hRcast : (R η a b : ℂ) = 4 / (q a b : ℂ) + 3 * (η : ℂ) ^ 2 / 4 := by
    simp [R]
  rw [hRcast]
  dsimp [A, B, D]
  field_simp [hqc]
  rw [hqexpr]
  ring_nf
  simp [Complex.I_sq]
  ring

end

theorem real_positive_definite  {η a b}  (hη : 0 < η) (hq : q a b ≠ 0) :
    0 < (A η a b).re * (D η a b).re - (B η a b).re ^ 2 := by
  obtain ⟨hA, hB, hD⟩ := coefficient_re η a b hq
  rw [hA, hB, hD]
  nlinarith [sq_pos_of_pos hη]

end OscSpecial

end

end OAI
