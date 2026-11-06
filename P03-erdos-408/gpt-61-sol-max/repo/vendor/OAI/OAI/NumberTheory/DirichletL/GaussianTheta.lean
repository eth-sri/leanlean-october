module
public import Mathlib.Tactic

public import OAI.NumberTheory.DirichletL.TraceConductor
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace SevenEighths.GaussianTheta

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def gaussian (a : ℝ) (z : ℂ)  :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ)  := (x : ℂ) + (y : ℂ) * omega3

theorem omega3_re : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]

theorem coordinate_norm_sq  x y  :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, omega3_im, zero_mul, zero_add,
    add_zero, sub_zero]
  grind [RankTwoEisShift.Q]

theorem exists_coordinate  w  : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv omega3 omega3_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv omega3 omega3_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase  x y   p  :
    paperE (coordinate x y * eisEmbedding (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  rw [paperE_eq_exp, dualFrequencyEquiv_coordinates]
  simp only [coordinate, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, omega3_re, omega3_im,
    zero_mul, zero_add, add_zero, sub_zero, complexPoint]
  unfold RankTwoEisShift.dualPhase
  congr 1
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    simp_all
  push_cast
  field_simp
  ring

theorem gaussian_coordinate_shift  a x y   p  :
    gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [eisEmbedding_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

section
variable (a : ℝ)
include a

theorem gaussian_dual_coordinate    p  :
    gaussian a (eisEmbedding (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  unfold gaussian
  rw [← Complex.ofReal_pow, dualFrequencyEquiv_norm_sq]
  unfold RankTwoPoisson.eisQ
  congr 1
  push_cast
  ring

section
variable (ha : 0 < a)
include ha

theorem shifted_prefactor     :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson      w  :
    (∑' z : O, gaussian a (eisEmbedding z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * eisEmbedding h) *
          gaussian (4 / (3 * a)) (eisEmbedding h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      grind [coordinate_dual_phase, gaussian_dual_coordinate]

end

theorem gaussian_mul    z w  :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable   (ha : 0 < a) :
    Summable (fun z : O => gaussian a (eisEmbedding z)) := eis_gaussian_summable ha

end

theorem paperE_norm  z  : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ)  a  (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (eisEmbedding z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson  a  (ha : 0 < a)  c  (hc : c ≠ 0)  r  :
    (∑' z : O, gaussian a (eisEmbedding (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (eisEmbedding r * eisEmbedding h / eisEmbedding c) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hc' := eisEmbedding_ne_zero hc
  have hscale : 0 < a * ‖eisEmbedding c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : eisEmbedding (r + c * z) =
      eisEmbedding c * (eisEmbedding z + eisEmbedding r / eisEmbedding c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ)  K  :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * eisEmbedding h)) *
        gaussian a (eisEmbedding h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
     a  (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (eisEmbedding z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (eisEmbedding z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖eisEmbedding c‖ ^ 2)) := div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) hd
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r) / eisEmbedding c) P
    (((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, eisTraceModChar_frequency]
  convert h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson  χ 
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ)  a  (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ)  := 2 * t / (Real.sqrt 3 * ‖eisEmbedding c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ)  :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (eisEmbedding z)

section
variable (t : ℝ) (ht : 0 < t)
include t ht

theorem parameter_pos     : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))

theorem parameter_dual     :
    4 / (3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) = parameter c (1 / t) := by
  grind [eisEmbedding, Real.sqrt, parameter]

theorem parameter_prefactor     :
    2 / (Real.sqrt 3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) =
      1 / (‖eisEmbedding c‖ * t) := by
  grind [eisEmbedding, Real.sqrt, parameter]

end

section
variable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : FiniteFourier.IsPrimitiveOnIdeals χ)
include χ hχ

section
variable (t : ℝ) (ht : 0 < t)
include t ht

theorem theta_functional_equation  
          :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖eisEmbedding c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

theorem theta_inversion  
          :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  simp_all [theta_functional_equation]

end

theorem theta_root_nonzero  
      : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  aesop

end

end SevenEighths.GaussianTheta

end

end OAI
