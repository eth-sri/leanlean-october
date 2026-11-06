module

public import GradedNear.Defs

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius ComplexConjugate
noncomputable section

namespace GradedNear

section
open Complex

def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast (show 1 < q by omega))

lemma tn_nonneg (q n : ℕ) (hq : 2 ≤ q) : 0 ≤ tn q n :=
  div_nonneg (Real.log_natCast_nonneg n) (log_q_pos hq).le

lemma eventually_loglog_ge (K : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    K ≤ Real.sqrt (Real.log (Real.log q)) ∧ K ≤ Real.log (Real.log q) ∧ 2 ≤ q := by
  set M : ℝ := max (K ^ 2) K + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (Real.exp M))
  refine ⟨max N 2, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := (le_max_right _ _).trans hq
  have h1 : Real.exp (Real.exp M) < q := hN.trans_le (by exact_mod_cast (le_max_left _ _).trans hq)
  have h2 := (Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < q by omega))).2 h1
  have h3 := (Real.lt_log_iff_exp_lt ((Real.exp_pos M).trans h2)).2 h2
  refine ⟨Real.le_sqrt_of_sq_le (by linarith [le_max_left (K ^ 2) K]),
    by linarith [le_max_right (K ^ 2) K], hq2⟩

lemma natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (A γ : ℝ) :
    (n : ℂ) ^ (-((A : ℂ) + (γ : ℂ) * I)) =
      (Real.exp (-A * Real.log n) : ℂ) * cexp (-((γ * Real.log n : ℝ) : ℂ) * I) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hn), ← natCast_log, ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma tn_ge_of_gt {q n : ℕ} (hq : 2 ≤ q) {X : ℝ} (hn : ⌊(q : ℝ) ^ X⌋₊ < n) : X ≤ tn q n := by
  have hℓ := log_q_pos hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h2 : ((⌊(q : ℝ) ^ X⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have h3 := Real.log_lt_log (Real.rpow_pos_of_pos hq0 X)
    ((Nat.lt_floor_add_one ((q : ℝ) ^ X)).trans_le h2)
  rw [Real.log_rpow hq0] at h3
  unfold tn; rw [le_div_iff₀ hℓ]; linarith

lemma primeSum_eq_sum {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) {X : ℝ}
    (hf : ∀ t, X ≤ t → f t = 0) (s : ℂ) :
    primeSum χ f s = ∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊,
      (Λ n : ℂ) * χ n * (n : ℂ) ^ (-s) * (f (tn q n) : ℂ) := by
  unfold primeSum
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · obtain rfl : n = 0 := by omega
    simp
  · have := hf _ (tn_ge_of_gt hq hn)
    simp [tn] at this
    simp [this]

variable {q : ℕ} {ι : Type*} [Fintype ι]

lemma prime_term (F : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter ℂ q) (σ γ : ℝ) :
    (Λ n : ℂ) * χ n * (n : ℂ) ^ (-((((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I)) *
        (F (tn q n) : ℂ) =
      ((Λ n / n * Real.exp (σ * tn q n) * F (tn q n) : ℝ) : ℂ) *
        (χ n * cexp (-((γ * Real.log n : ℝ) : ℂ) * I)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [natCast_cpow_neg (by omega), show Real.exp (-(1 - σ / Real.log q) * Real.log n) =
      (1 / n) * Real.exp (σ * tn q n) by
    rw [one_div, ← Real.exp_log hnpos, ← Real.exp_neg, Real.exp_log hnpos, ← Real.exp_add]
    congr 1; unfold tn; ring]
  push_cast; ring

def ycomp (E : Entries q ι) (a : ι → ℝ) (j : ι) (n : ℕ) : ℂ :=
  (a j : ℂ) * ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

def Yn (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ := ∑ j, ycomp E a j n

omit [Fintype ι] in
lemma ycomp_mul_conj (E : Entries q ι) (a : ι → ℝ) (j k : ι) (n : ℕ) :
    ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n) =
      ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) *
        ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)) := by
  unfold ycomp
  have hχ : (starRingEnd ℂ) (E.χ k n) = (E.χ k)⁻¹ n := by rw [← MulChar.star_apply']; rfl
  have hexp : (starRingEnd ℂ) (cexp (-((E.γ k * Real.log n : ℝ) : ℂ) * I)) =
      cexp (((E.γ k * Real.log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]; congr 1
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring
  have e1 : cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I) *
      cexp (((E.γ k * Real.log n : ℝ) : ℂ) * I) =
      cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2 : ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) =
      (a j : ℂ) * (a k : ℂ) * (Real.exp (-(E.δ j) * tn q n) : ℂ) *
        (Real.exp (-(E.δ k) * tn q n) : ℂ) := by
    rw [show -(E.δ j + E.δ k) * tn q n = -(E.δ j) * tn q n + -(E.δ k) * tn q n by ring, Real.exp_add]
    push_cast; ring
  simp only [map_mul, Complex.conj_ofReal, hχ, hexp]
  rw [e2, ← e1, MulChar.coeToFun_mul, Pi.mul_apply]; ring

lemma norm_Yn_sq (E : Entries q ι) (a : ι → ℝ) (n : ℕ) :
    ‖Yn E a n‖ ^ 2 = ∑ j, ∑ k, (ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n)).re := by
  rw [← Complex.ofReal_re (‖Yn E a n‖ ^ 2), ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
    Yn, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  simp_rw [Complex.re_sum]

def sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  (((1 - (D.s₁ - E.δ j - E.δ k) / Real.log q : ℝ)) : ℂ) + ((E.γ j - E.γ k : ℝ) : ℂ) * I

end

section
open MeasureTheory Set

lemma laplace_eq_intervalIntegral {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (z : ℂ) :
    laplace f z = ∫ t in (0 : ℝ)..x₀, (f t : ℂ) * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hf.pos.le, laplace]
  exact setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self fun t ht => by
      simp [hf.vanish t (not_lt.1 fun h => ht.2 ⟨ht.1, h.le⟩)]

theorem laplace_decay {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f ((x : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ ε := by
  have hx₀ := hf.pos
  have hmid : x₀ / 2 ∈ Ioo (0 : ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf.bound _ hmid)
  set K := max (|deriv f (x₀ / 2)| + B * x₀) |deriv f x₀|
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (le_max_right _ _)
  have hK (t : ℝ) (ht : t ∈ Ioc 0 x₀) : |deriv f t| ≤ K := by
    rcases eq_or_lt_of_le ht.2 with rfl | h
    · exact le_max_right _ _
    · have htm : t ∈ Ioo (0 : ℝ) x₀ := ⟨ht.1, h⟩
      have hd1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 x₀) := hf.smooth.deriv_of_isOpen isOpen_Ioo (by norm_num)
      have hmv := (convex_Ioo (0 : ℝ) x₀).norm_image_sub_le_of_norm_deriv_le
        (fun s hs => (hd1.differentiableOn (by norm_num) s hs).differentiableAt (isOpen_Ioo.mem_nhds hs))
        (fun s hs => by rw [Real.norm_eq_abs]; exact hf.bound s hs) hmid htm
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
      have h2 : |t - x₀ / 2| ≤ x₀ := abs_le.2 ⟨by linarith [htm.1], by linarith [htm.2]⟩
      exact le_trans (by linarith [abs_sub_abs_le_abs_sub (deriv f t) (deriv f (x₀ / 2)),
        mul_le_mul_of_nonneg_left h2 hB]) (le_max_left _ _)
  set C := |f 0| + K * Real.exp (X * x₀) * x₀
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C / ε + 1, by positivity, fun x hx Y hY => ?_⟩
  set z : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I
  have hibp : z * laplace f z =
      (f 0 : ℂ) + ∫ t in (0 : ℝ)..x₀, ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t)) := by
    have hu : ContinuousOn (fun t : ℝ => (f t : ℂ)) (uIcc 0 x₀) := by
      rw [uIcc_of_le hx₀.le]
      exact Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self)
    have hu' : IntervalIntegrable (fun t : ℝ => ((deriv f t : ℝ) : ℂ)) volume 0 x₀ := by
      refine (intervalIntegrable_const (c := K)).mono_fun'
        (Complex.measurable_ofReal.comp (measurable_deriv f)).aestronglyMeasurable ?_
      rw [uIoc_of_le hx₀.le]
      exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by simpa using hK t ht
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * t))).continuousOn
      (fun t ht => by
        rw [min_eq_left hx₀.le, max_eq_right hx₀.le] at ht
        exact ((hf.smooth.differentiableOn (by norm_num) t ht).differentiableAt
          (isOpen_Ioo.mem_nhds ht)).hasDerivAt.ofReal_comp)
      (fun t _ => by
        have h1 : HasDerivAt (fun t : ℝ => -(z * (t : ℂ))) (-z) t := by
          convert ((hasDerivAt_id' t).ofReal_comp).const_mul (-z) using 1
          · ext y; ring
          · simp
        exact h1.cexp.congr_deriv (mul_comm _ _))
      hu' ((by fun_prop : Continuous fun t : ℝ => -z * Complex.exp (-(z * t))).intervalIntegrable _ _)
    have hlhs : (∫ t in (0 : ℝ)..x₀, (f t : ℂ) * (-z * Complex.exp (-(z * t)))) = -z * laplace f z := by
      rw [laplace_eq_intervalIntegral hf, ← intervalIntegral.integral_const_mul]
      congr 1; ext t; ring
    rw [hlhs, hf.vanish x₀ le_rfl] at h
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one, zero_sub] at h
    linear_combination -h
  have hbound : ‖z‖ * ‖laplace f z‖ ≤ C := by
    rw [← norm_mul, hibp]
    refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x₀)
      (C := K * Real.exp (X * x₀))
      (f := fun t : ℝ => ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t))) fun t ht => ?_
    · rwa [sub_zero, abs_of_pos hx₀] at h
    · rw [uIoc_of_le hx₀.le] at ht
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      refine mul_le_mul (hK t ht) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le hK0
      simp [z]; nlinarith [ht.1, ht.2, hx.1, hx.2]
  have hMz : C / ε + 1 ≤ ‖z‖ := hY.trans (by simpa [z] using Complex.abs_im_le_norm z)
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hMz
  have h1 : ε * (C / ε + 1) = C + ε := by field_simp
  have h2 := mul_le_mul_of_nonneg_left hMz hε.le
  exact le_of_mul_le_mul_left (hbound.trans (by linarith)) hzpos

end

section
open Complex NearData Filter Topology MeasureTheory Finset

lemma sum_Ioc_ite_dvd {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 0 < l)
    (a b : ℕ) :
    ∑ k ∈ Ioc a b, (if l ∣ k then f k else 0) = ∑ m ∈ Ioc (a / l) (b / l), f (l * m) := by
  rw [← sum_filter, ← sum_image fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hl h]
  congr 1; ext n; simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, m, rfl⟩
    exact ⟨m, ⟨(Nat.div_lt_iff_lt_mul hl).2 (by linarith),
      (Nat.le_div_iff_mul_le hl).2 (by linarith)⟩, rfl⟩
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨by linarith [(Nat.div_lt_iff_lt_mul hl).1 h1],
      by linarith [(Nat.le_div_iff_mul_le hl).1 h2]⟩, dvd_mul_right l m⟩

lemma sum_Ioc_period_eq_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (a : ℕ) : ∑ n ∈ Ioc a (a + q), ψ n = 0 := by
  rw [← Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show a + q + 1 - (a + 1) = q by omega, ← MulChar.sum_eq_zero_of_ne_one hψ]
  refine sum_nbij (fun k : ℕ => ((a + 1 + k : ℕ) : ZMod q))
    (fun _ _ => mem_univ _) (fun k hk k' hk' h => ?_)
    (fun x _ => ⟨(x - (a + 1 : ℕ)).val, by simpa using ZMod.val_lt _, by simp⟩)
    (fun _ _ => rfl)
  simp only [coe_range, Set.mem_Iio] at hk hk'
  simp only [Nat.cast_add, add_right_inj, ZMod.natCast_eq_natCast_iff'] at h
  rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at h

theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  set ε' := ε / 2
  have hε' : 0 < ε' := half_pos hε
  obtain ⟨C₁, hC₁⟩ := hB ε' hε'
  set K : ℕ := ⌈(2 : ℝ) ^ (1 / ε')⌉₊
  have hK : (2 : ℝ) ^ (1 / ε') ≤ K := Nat.le_ceil _
  set b : ℝ := (2 : ℝ) ^ ε'
  set M : ℝ := max 1 (1 / (b - 1))
  have hM1 : 1 ≤ M := le_max_left _ _
  have hτ (n : ℕ) (hn : n ≠ 0) : (n.divisors.card : ℝ) ≤ M ^ K * (n : ℝ) ^ ε' := by
    set g : ℕ → ℝ := fun p => if p < K then M else 1
    have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]; push_cast; rfl
    have hn' : (n : ℝ) ^ ε' = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε') ^ (n.factorization p) := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
      push_cast
      rw [← Real.finsetProd_rpow _ _ fun _ _ => by positivity]
      exact prod_congr rfl fun p _ => by rw [Real.rpow_pow_comm (by positivity)]
    have hgK : ∏ p ∈ n.primeFactors, g p ≤ M ^ K := by
      dsimp [g]
      rw [prod_ite, prod_const_one, mul_one, prod_const]
      exact pow_le_pow_right₀ hM1 ((card_le_card fun p hp => by
        simpa using (mem_filter.1 hp).2).trans_eq (card_range K))
    rw [hcard]
    refine (prod_le_prod₀ (g := fun p => g p * ((p : ℝ) ^ ε') ^ (n.factorization p))
      (fun _ _ => by positivity) fun p hp => ?_).trans (by rw [prod_mul_distrib, ← hn']; gcongr)
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    set a := n.factorization p
    dsimp [g]
    split_ifs with hpK
    · have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) hε'
      have hb' : 0 < b - 1 := by linarith
      have hMb : 1 ≤ M * (b - 1) := by
        calc (1 : ℝ) = 1 / (b - 1) * (b - 1) := by field_simp
          _ ≤ M * (b - 1) := mul_le_mul_of_nonneg_right (le_max_right _ _) hb'.le
      have hbern : 1 + (a : ℝ) * (b - 1) ≤ b ^ a := by
        simpa using one_add_mul_le_pow (show (-2 : ℝ) ≤ b - 1 by linarith) a
      have hbp : b ≤ (p : ℝ) ^ ε' := Real.rpow_le_rpow (by norm_num) hp2 hε'.le
      calc (a : ℝ) + 1 ≤ M * (1 + a * (b - 1)) := by nlinarith [a.cast_nonneg (α := ℝ)]
        _ ≤ M * b ^ a := by gcongr
        _ ≤ M * ((p : ℝ) ^ ε') ^ a := by gcongr
    · have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε' := by
        rw [show (2 : ℝ) = ((2 : ℝ) ^ (1 / ε')) ^ ε' by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε'.ne', Real.rpow_one]]
        exact Real.rpow_le_rpow (by positivity) (hK.trans (Nat.cast_le.2 (not_lt.mp hpK))) hε'.le
      have hbern := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) a
      norm_num at hbern
      rw [one_mul]
      exact (by linarith : (a : ℝ) + 1 ≤ 2 ^ a).trans (by gcongr)
  set C₁' := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨C₁' * M ^ K, fun q χ hχ N H hH hHq => ?_⟩
  have hq1 : 1 ≤ q := hH.trans hHq
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  set ψ := χ.primitiveCharacter
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : ψ ≠ 1 := fun h => hχ (by
    rw [← χ.changeLevel_primitiveCharacter, show χ.primitiveCharacter = 1 from h, map_one])
  have hψprim : ψ.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hprim_all (a h : ℕ) :
      ‖∑ n ∈ Ioc a (a + h), ψ n‖ ≤ C₁' * (χ.conductor : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) * (h : ℝ) ^ ((2 : ℝ) / 3) := by
    have hqc : 0 < χ.conductor := Nat.pos_of_ne_zero χ.conductor_ne_zero
    induction h using Nat.strong_induction_on generalizing a with
    | _ h ih =>
      rcases Nat.eq_zero_or_pos h with rfl | hh
      · simp
      · by_cases hhq : h ≤ χ.conductor
        · have e1 := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a χ.conductor)
            (Nat.le_add_right (a + χ.conductor) h)
          have e2 := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a h)
            (Nat.le_add_right (a + h) χ.conductor)
          rw [sum_Ioc_period_eq_zero ψ hψ1 a, zero_add] at e1
          rw [sum_Ioc_period_eq_zero ψ hψ1 (a + h), add_zero, show a + h + χ.conductor = a + χ.conductor + h by ring] at e2
          rw [e2, ← e1]
          exact (hC₁ χ.conductor hqc ψ hψprim (a + χ.conductor) h (by omega) hh hhq).trans
            (by gcongr; exact le_max_left _ _)
        · have hsplit := sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a χ.conductor)
            (show a + χ.conductor ≤ a + h by omega)
          rw [← hsplit, sum_Ioc_period_eq_zero ψ hψ1 a, zero_add,
            show a + h = a + χ.conductor + (h - χ.conductor) by omega]
          exact (ih (h - χ.conductor) (by omega) (a + χ.conductor)).trans
            (by gcongr; exact_mod_cast Nat.sub_le h χ.conductor)
  have hmoeb (m : ℕ) : ∑ d ∈ m.divisors, (μ d : ℂ) = if m = 1 then 1 else 0 := by
    have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
    rw [show ∑ d ∈ m.divisors, (μ d : ℂ) = ((∑ d ∈ m.divisors, μ d : ℤ) : ℂ) by push_cast; rfl, h]
    split_ifs <;> simp
  have hsum_div : ∑ n ∈ Ioc N (N + H), χ n =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), ψ n := by
    have key (n : ℕ) : χ n = ∑ d ∈ q.divisors, if d ∣ n then (μ d : ℂ) * ψ n else 0 := by
      rw [← sum_filter, show q.divisors.filter (· ∣ n) = (Nat.gcd n q).divisors by
        ext d; simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hq0]; tauto, ← sum_mul, hmoeb]
      by_cases h : n.Coprime q
      · rw [ite_eq_left (Nat.coprime_iff_gcd_eq_one.mp h), one_mul]
        simpa using (χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr h)).symm
      · rw [ite_eq_right (mt Nat.coprime_iff_gcd_eq_one.mpr h), zero_mul]
        exact χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])
    rw [sum_congr rfl fun n _ => key n, sum_comm]
    exact sum_congr rfl fun d _ => by rw [sum_filter, mul_sum]; simp
  set B : ℝ := C₁' * (q : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) * (H : ℝ) ^ ((2 : ℝ) / 3) with hBdef
  have hinner (d : ℕ) (hd : d ∈ q.divisors) :
      ‖(μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), ψ n‖ ≤ B := by
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdiv : ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), ψ n =
        ψ d * ∑ m ∈ Ioc (N / d) ((N + H) / d), ψ m := by
      rw [sum_filter, sum_Ioc_ite_dvd (fun n => ψ n) hd0, mul_sum]
      exact sum_congr rfl fun m _ => by push_cast; exact map_mul ψ _ _
    have hH' : (N + H) / d - N / d ≤ H := by
      have h1 : (N + H) / d ≤ (N + H * d) / d := Nat.div_le_div_right (by nlinarith)
      rw [Nat.add_mul_div_right N H hd0] at h1; omega
    have hle : N / d ≤ (N + H) / d := Nat.div_le_div_right (by omega)
    rw [hdiv, show (N + H) / d = N / d + ((N + H) / d - N / d) by omega, norm_mul, norm_mul]
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hψd : ‖ψ d‖ ≤ 1 := ψ.norm_le_one _
    have hcond : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
    calc ‖(μ d : ℂ)‖ * (‖ψ d‖ * ‖∑ m ∈ Ioc (N / d) (N / d + ((N + H) / d - N / d)), ψ m‖)
        ≤ 1 * (1 * (C₁' * (χ.conductor : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) *
          (((N + H) / d - N / d : ℕ) : ℝ) ^ ((2 : ℝ) / 3))) := by
          gcongr; exact hprim_all _ _
      _ ≤ B := by rw [one_mul, one_mul, hBdef]; gcongr
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [hsum_div]
  refine (norm_sum_le _ _).trans ((sum_le_sum hinner).trans ?_)
  rw [sum_const, nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (hτ q hq0) (by positivity)).trans_eq ?_
  rw [hBdef, show (1 : ℝ) / 9 + ε = ε / 2 + ((1 : ℝ) / 9 + ε / 2) by ring,
    Real.rpow_add hqpos (ε / 2) ((1 : ℝ) / 9 + ε / 2)]
  ring

def mertensSum (y : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n / n

lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |mertensSum x - Real.log x| ≤ 7 := by
  set N := ⌊x⌋₊
  have hN : 1 ≤ N := Nat.le_floor (by simpa using hx)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsum : ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
    have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
    rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
    simpa [ArithmeticFunction.log_apply] using h
  have hlo : Real.log N - 1 ≤ mertensSum x := by
    have h1 := Real.le_sum_log_nat N
    have h2 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) ≤ N * mertensSum x := by
      rw [mertensSum, Finset.mul_sum]
      refine Finset.sum_le_sum fun n _ => ?_
      rw [mul_div_left_comm]
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
    exact le_of_mul_le_mul_left (by linarith) hNR
  have hup : mertensSum x ≤ Real.log N + (Real.log 4 + 4) := by
    have h1 := Real.sum_log_le' (x := (N : ℝ)) hNR1
    rw [Nat.floor_natCast, hsum] at h1
    have h2 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n - 1) ≤
        ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) :=
      Finset.sum_le_sum fun n hn => by
        have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
        refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
        rw [div_sub_one hnR.ne', div_le_iff₀ hnR]
        have : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast Nat.lt_div_mul_add hn0
        linarith
    have h3 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n - 1) =
        N * mertensSum x - Chebyshev.psi N := by
      rw [mertensSum, Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    have h4 := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hNR.le
    exact le_of_mul_le_mul_left (by nlinarith) hNR
  have hfl : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfl2 : x < N + 1 := Nat.lt_floor_add_one x
  have hlog1 : Real.log N ≤ Real.log x := Real.log_le_log hNR hfl
  have hlog2 : Real.log x ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hNR.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  rw [abs_le]
  constructor <;> linarith [Real.log_le_sub_one_of_pos (x := 2) (by norm_num),
    Real.log_le_sub_one_of_pos (x := 4) (by norm_num)]

def cell (φ : ℝ → ℝ) (h : ℝ) (i : ℕ) : ℝ := sSup (φ '' Set.Icc (i * h) ((i + 1) * h))

def stepFn (φ : ℝ → ℝ) (h : ℝ) (t : ℝ) : ℝ := cell φ h (⌈t / h⌉₊ - 1)

lemma stepFn_eq (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ) {t : ℝ} (ht1 : (i : ℝ) * h < t)
    (ht2 : t ≤ (i + 1) * h) : stepFn φ h t = cell φ h i := by
  have hc : ⌈t / h⌉₊ = i + 1 :=
    (Nat.ceil_eq_iff i.succ_ne_zero).2 ⟨by rw [Nat.succ_sub_one, lt_div_iff₀ hh]; exact ht1,
      by rw [div_le_iff₀ hh]; push_cast; exact ht2⟩
  unfold stepFn; rw [hc, Nat.add_sub_cancel]

lemma integral_stepFn (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    IntervalIntegrable (stepFn φ h) volume 0 (j * h) ∧
      ∫ t in (0 : ℝ)..(j * h), stepFn φ h t = ∑ i ∈ Finset.range j, cell φ h i * h := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hEq (t : ℝ) (ht : t ∈ Set.Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h)) :
        stepFn φ h t = cell φ h j :=
      stepFn_eq φ hh j ht.1 (by push_cast at ht; exact ht.2)
    have hle : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hII : IntervalIntegrable (stepFn φ h) volume ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
      exact (integrableOn_const (C := cell φ h j) (hs := by rw [Real.volume_Ioc]; exact
        ENNReal.ofReal_ne_top)).congr_fun (fun t ht => (hEq t ht).symm) measurableSet_Ioc
    have hI : ∫ t in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), stepFn φ h t = cell φ h j * h := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => cell φ h j)]
      · rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
      · exact Filter.Eventually.of_forall fun t ht => hEq t (Set.uIoc_of_le hle ▸ ht)
    refine ⟨ih.1.trans hII, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hII, ih.2, hI, Finset.sum_range_succ]

lemma laplace_re_conj (g : ℝ → ℝ) (z : ℂ) :
    (laplace g ((starRingEnd ℂ) z)).re = (laplace g z).re := by
  have : laplace g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (laplace g z) := by
    unfold laplace
    rw [← integral_conj]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]
  rw [this, Complex.conj_re]

def gramDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), D.g u * Real.exp ((D.s₁ - 2 * δ) * u)

theorem gram_form_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
        (∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re) /
            Real.log q ≤
          ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
            (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  classical
  set K : ℝ := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ
  obtain ⟨C, q₁, hC⟩ := hX31 D.g D.xg D.Bg hD.g_cond1
  obtain ⟨δ, hδ0, hδ1, q₂, hq₂⟩ := hX32 D.g D.xg D.Bg hD.g_cond1 (hD.g_cond2.nonneg 0 le_rfl) ε hε
  obtain ⟨q₃, hq₃⟩ := eventually_loglog_ge (max K (|C| / ε + 1))
  refine ⟨max (max q₁ q₂) q₃, fun q _ hq T hT hTq hsafe ι _ E hγ hΔ a ha => ?_⟩
  obtain ⟨hsq, hll, hq2⟩ := hq₃ q (by omega)
  have hℓ := log_q_pos hq2
  have hsre (j k : ι) : (sjk D E j k).re = 1 - (D.s₁ - E.δ j - E.δ k) / Real.log q := by simp [sjk, -natCast_log]
  have hsim (j k : ι) : (sjk D E j k).im = E.γ j - E.γ k := by simp [sjk, -natCast_log]
  have hre (j k : ι) : |(sjk D E j k).re - 1| ≤ K / Real.log q := by
    rw [hsre, show 1 - (D.s₁ - E.δ j - E.δ k) / Real.log q - 1 =
      -((D.s₁ - E.δ j - E.δ k) / Real.log q) by ring, abs_neg, abs_div, abs_of_pos hℓ]
    refine div_le_div_of_nonneg_right ?_ hℓ.le
    have h1 := single_le_sum hD.Δ_nonneg (hΔ j)
    have h2 := single_le_sum hD.Δ_nonneg (hΔ k)
    have h3 := hD.Δ_nonneg _ (hΔ j)
    have h4 := hD.Δ_nonneg _ (hΔ k)
    rw [abs_le]; constructor <;> linarith [le_abs_self D.s₁, neg_le_abs D.s₁]
  have him (j k : ι) : |(sjk D E j k).im| ≤ 2 * T := by
    rw [hsim]; linarith [abs_sub (E.γ j) (E.γ k), hγ j, hγ k]
  have hreg (j k : ι) : LemmaRegion q (sjk D E j k) :=
    ⟨(hre j k).trans (div_le_div_of_nonneg_right ((le_max_left _ _).trans hsq) hℓ.le), by linarith [him j k]⟩
  let M (j k : ι) : ℝ := (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re / Real.log q
  let R (j k : ι) : ℝ := (laplace D.g (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) +
    (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)).re
  have hsame (j k : ι) (hjk : E.χ j = E.χ k) : M j k ≤ R j k + ε := by
    dsimp [M, R]
    rw [show E.χ j * (E.χ k)⁻¹ = 1 by rw [hjk, mul_inv_cancel]]
    have h2 : |C| / ε + 1 ≤ Real.log (Real.log q) := (le_max_right _ _).trans hll
    have hll_pos : 0 < Real.log (Real.log q) := lt_of_lt_of_le (by positivity) h2
    have h1 := (Complex.re_le_norm _).trans (hC q (by omega) (sjk D E j k) (hreg j k))
    rw [Complex.sub_re, Complex.re_ofReal_mul, mul_div_right_comm] at h1
    have hsmall : C / Real.log (Real.log q) ≤ ε := by
      rw [div_le_iff₀ hll_pos]
      rw [div_add_one hε.ne', div_le_iff₀ hε] at h2
      nlinarith [le_abs_self C, abs_nonneg C]
    have harg : (sjk D E j k - 1) * (Real.log q : ℂ) =
        (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) : ℂ) + (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I := by
      have := hℓ.ne'
      unfold sjk
      apply Complex.ext <;> simp [-natCast_log]; field_simp; ring
    rw [harg] at h1
    rw [div_le_iff₀ hℓ]
    nlinarith [mul_le_mul_of_nonneg_right hsmall hℓ.le]
  have hdiff (j k : ι) (hjk : E.χ j ≠ E.χ k) : M j k ≤ D.d₁ + ε := by
    dsimp [M]
    have h1 : E.χ j * (E.χ k)⁻¹ ≠ 1 := fun h => hjk (mul_inv_eq_one.1 h)
    have hb := hq₂ q (by omega) _ h1 (sjk D E j k) (hreg j k)
    have hzs : 0 ≤ zeroSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k) δ :=
      finsum_nonneg fun ρ => finsum_nonneg fun hρ =>
        mul_nonneg (Nat.cast_nonneg _) <| hD.g_cond2.re_nonneg _ <| by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.sub_re, hsre]
          have h2 : |ρ.im - (sjk D E j k).im| ≤ δ := by
            have := Complex.abs_im_le_norm ((1 + ((sjk D E j k).im : ℂ) * I) - ρ)
            simp at this; rw [abs_sub_comm]; linarith [hρ.1]
          have hsafe' := hsafe _ h1 ρ hρ.2 (by linarith [abs_sub_abs_le_abs_sub ρ.im (sjk D E j k).im, him j k])
          have hδs : D.s₁ - E.δ j - E.δ k ≤ D.s₁ := by
            linarith [hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k)]
          exact mul_nonneg (by linarith [div_le_div_of_nonneg_right hδs hℓ.le]) hℓ.le
    rw [div_le_iff₀ hℓ]; unfold NearData.d₁
    nlinarith
  set P : ι → ι → ℝ := fun j k => if k ≠ j ∧ E.χ k = E.χ j then max 0 (R j k - D.d₁) else 0 with hP
  have hPsymm (j k : ι) : P j k = P k j := by
    have hR : R j k = R k j := by
      dsimp [R]; rw [← laplace_re_conj]; congr 2; simp [-natCast_log]; ring
    simp only [hP, hR, ne_comm (a := k), eq_comm (a := E.χ k)]
  have hterm (j k : ι) : a j * a k * M j k ≤
      a j * a k * (D.d₁ + ε) + (if k = j then a j * a k * (R j k - D.d₁) else 0) +
        a j * a k * P j k := by
    have hajk := mul_nonneg (ha j) (ha k)
    by_cases hkj : k = j
    · subst hkj; simp [hP]; nlinarith [mul_le_mul_of_nonneg_left (hsame k k rfl) hajk]
    · rw [ite_eq_right hkj]
      by_cases hs : E.χ k = E.χ j
      · simp only [hP, hkj, hs, and_self, ↓reduceIte, ne_eq, not_false_eq_true]
        nlinarith [mul_le_mul_of_nonneg_left (hsame j k hs.symm) hajk,
          mul_le_mul_of_nonneg_left (le_max_right 0 (R j k - D.d₁)) hajk]
      · simp only [hP, hs, and_false, ↓reduceIte, mul_zero, add_zero]
        nlinarith [mul_le_mul_of_nonneg_left (hdiff j k (Ne.symm hs)) hajk]
  have hpair : ∑ j, ∑ k, a j * a k * P j k ≤ ∑ j, pairExcess D E j * a j ^ 2 := by
    have h1 (j k : ι) : a j * a k * P j k ≤ a j ^ 2 * P j k / 2 + a k ^ 2 * P k j / 2 := by
      have hPnn : 0 ≤ P j k := by simp only [hP]; split_ifs <;> simp
      rw [hPsymm k j]; nlinarith [mul_le_mul_of_nonneg_right (two_mul_le_add_sq (a j) (a k)) hPnn]
    refine (sum_le_sum fun j _ => sum_le_sum fun k _ => h1 j k).trans_eq ?_
    simp_rw [sum_add_distrib, ← sum_div]
    rw [sum_comm (f := fun j k => a k ^ 2 * P k j), add_halves]
    refine sum_congr rfl fun j _ => ?_
    rw [pairExcess, sameCharOthers, sum_filter, sum_mul]
    exact sum_congr rfl fun k _ => by simp [P, R]; ring_nf
  have hdiag : ∑ j, ∑ k, (if k = j then a j * a k * (R j k - D.d₁) else 0) =
      ∑ j, (gramDiag D (E.δ j) - D.d₁) * a j ^ 2 :=
    sum_congr rfl fun j _ => by
      rw [sum_ite_eq' univ j (fun k => a j * a k * (R j k - D.d₁)), ite_eq_left (mem_univ j)]
      have hself : R j j = gramDiag D (E.δ j) := by
        dsimp [R]; unfold gramDiag laplace
        have (u : ℝ) : (D.g u : ℂ) * cexp (-((((-(D.s₁ - E.δ j - E.δ j)) : ℝ) +
            (((E.γ j - E.γ j) * Real.log q : ℝ) : ℂ) * I) * u)) =
            ((D.g u * Real.exp ((D.s₁ - 2 * E.δ j) * u) : ℝ) : ℂ) := by
          push_cast; congr 2; ring
        simp_rw [this, integral_complex_ofReal, ofReal_re]
      rw [hself]; ring
  have hconst : ∑ j, ∑ k, a j * a k * (D.d₁ + ε) = (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
    rw [sq, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun j _ => by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  rw [Finset.sum_div]
  simp_rw [Finset.sum_div, mul_div_assoc]
  refine (sum_le_sum fun j _ => sum_le_sum fun k _ => hterm j k).trans ?_
  simp_rw [sum_add_distrib, hconst, hdiag, add_mul, sum_add_distrib]
  linarith

theorem first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n *
          (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))) /
        Real.log q ≤ D.IB + ε := by
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  set X := D.xf
  have hX : 0 < X := hD.f_cond.pos
  let φ (u : ℝ) : ℝ := Real.exp (2 * D.s * u) * D.f u ^ 2 / D.omega u
  have habs_phi {v : ℝ} (hv : 0 ≤ v) : |φ v| ≤ Real.exp (2 * D.s * v) * D.f v ^ 2 / c := by
    dsimp [φ]
    by_cases hf : D.f v = 0
    · simp [hf]
    · have hω := hcω v hv hf
      have hnum : 0 ≤ Real.exp (2 * D.s * v) * D.f v ^ 2 := by positivity
      rw [abs_of_nonneg (div_nonneg hnum (hc.trans_le hω).le)]
      exact div_le_div_of_nonneg_left hnum hc hω
  have hcont_ub : ContinuousOn (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / c) (Set.Icc 0 X) :=
    ((by fun_prop : Continuous fun v => Real.exp (2 * D.s * v)).continuousOn.mul
      ((hD.f_cond.cont.mono Set.Icc_subset_Ici_self).pow 2)).div_const c
  obtain ⟨M, hM_ub⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_ub
  have hbd (u : ℝ) (hu : u ∈ Set.Icc 0 X) : |φ u| ≤ M :=
    (habs_phi hu.1).trans ((le_abs_self _).trans (Real.norm_eq_abs _ ▸ hM_ub u hu))
  have hM : 0 ≤ M := (abs_nonneg _).trans (hbd 0 ⟨le_rfl, hX.le⟩)
  set P : Finset ℝ := insert D.xg ((Finset.range (D.m + 1)).image D.t)
  have hcont (u : ℝ) (hu : u ∈ Set.Ioo 0 X) (huP : u ∉ P) : ContinuousAt φ u := by
    have hu' (k : ℕ) (hk : k ≤ D.m) : u ≠ D.t k := fun hEq => huP <|
      Finset.mem_insert.2 <| Or.inr <| Finset.mem_image.2 ⟨k, Finset.mem_range.2 (by omega), hEq.symm⟩
    have hf : ContinuousAt D.f u := hD.f_cond.cont.continuousAt (Ici_mem_nhds hu.1)
    have hg : ContinuousAt D.g u := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu.1)
    have hH : ContinuousAt D.sieveH u :=
      tendsto_finsetSum _ fun k hk => by
        refine (continuousAt_const : ContinuousAt (fun _ => if D.t k ≤ u ∧ u < D.t (k + 1) then D.h k else 0) u).congr ?_
        rcases lt_or_gt_of_ne (hu' k (by simp at hk; omega)) with h1 | h1
        · filter_upwards [Iio_mem_nhds h1] with v hv; simp [hv.not_ge, h1.not_ge]
        · rcases lt_or_gt_of_ne (hu' (k + 1) (by simp at hk; omega)) with h2 | h2
          · filter_upwards [Ioo_mem_nhds h1 h2] with v hv; simp [hv.1.le, hv.2, h1.le, h2]
          · filter_upwards [Ioi_mem_nhds h2] with v hv; simp [hv.not_gt, h2.not_gt]
    have hexp (a : ℝ) : ContinuousAt (fun v : ℝ => Real.exp (a * v)) u := by fun_prop
    have hω : ContinuousAt D.omega u := (hg.mul (hexp D.s₁)).add hH
    have hnum : ContinuousAt (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2) u :=
      (hexp (2 * D.s)).mul (hf.pow 2)
    by_cases hωu : D.omega u = 0
    · have hfu : D.f u = 0 := by by_contra hne; linarith [hcω u hu.1.le hne]
      show Tendsto φ (𝓝 u) (𝓝 (φ u))
      rw [show φ u = 0 by simp [φ, hfu]]
      refine squeeze_zero_norm' ?_ (by simpa [hfu] using (hnum.div_const c).tendsto)
      filter_upwards [Ioi_mem_nhds hu.1] with v hv
      rw [Real.norm_eq_abs]; exact habs_phi hv.le
    · exact hnum.div hω hωu
  have hceil_idx {K : ℕ} (hK : 0 < K) {t : ℝ} (ht0 : 0 < t) (htX : t ≤ X) :
      ⌈t / (X / K)⌉₊ - 1 < K ∧ ((⌈t / (X / K)⌉₊ - 1 : ℕ) : ℝ) * (X / K) < t ∧
        t ≤ (((⌈t / (X / K)⌉₊ - 1 : ℕ) : ℝ) + 1) * (X / K) := by
    have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
    have hh : 0 < X / K := div_pos hX hKR
    have hpos : 0 < t / (X / K) := div_pos ht0 hh
    have hKh : (K : ℝ) * (X / K) = X := by field_simp
    set m := ⌈t / (X / K)⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
    have hmK : m ≤ K := Nat.ceil_le.2 (by rw [div_le_iff₀ hh, hKh]; exact htX)
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
    refine ⟨by omega, ?_, ?_⟩
    · rw [hcast, ← lt_div_iff₀ hh]
      have h1 := Nat.ceil_lt_add_one hpos.le
      rw [← hm] at h1; linarith
    · rw [hcast, sub_add_cancel, ← div_le_iff₀ hh]; exact Nat.le_ceil _
  have hcell_bd {K i : ℕ} (hi : i < K) {v : ℝ}
      (hv : v ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K))) : |φ v| ≤ M := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast Nat.zero_lt_of_lt hi
    have hh : 0 < X / K := div_pos hX hKR
    have hiK : (i : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt hi
    have hKh : (K : ℝ) * (X / K) = X := by field_simp
    exact hbd v ⟨by linarith [hv.1, show 0 ≤ (i : ℝ) * (X / K) by positivity],
      by linarith [hv.2, mul_le_mul_of_nonneg_right hiK hh.le]⟩
  have hle_cell {K i : ℕ} (hi : i < K) {t : ℝ}
      (ht : t ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K))) : φ t ≤ cell φ (X / K) i :=
    le_csSup ⟨M, by rintro _ ⟨v, hv, rfl⟩; exact (abs_le.1 (hcell_bd hi hv)).2⟩ ⟨t, ht, rfl⟩
  have habs_cell {K i : ℕ} (hi : i < K) : |cell φ (X / K) i| ≤ M := by
    have hh : 0 < X / K := div_pos hX (by exact_mod_cast Nat.zero_lt_of_lt hi)
    have hmem : (i : ℝ) * (X / K) ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K)) := ⟨le_rfl, by nlinarith⟩
    exact abs_le.2 ⟨by linarith [hle_cell hi hmem, (abs_le.1 (hcell_bd hi hmem)).1],
      csSup_le ⟨_, _, hmem, rfl⟩ (by rintro _ ⟨v, hv, rfl⟩; exact (abs_le.1 (hcell_bd hi hv)).2)⟩
  have htend : Tendsto (fun K : ℕ => ∫ t in (0 : ℝ)..X, stepFn φ (X / K) t) atTop
      (𝓝 (∫ u in (0 : ℝ)..X, φ u)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
    · exact Filter.Eventually.of_forall fun K => by
        change AEStronglyMeasurable ((fun k : ℕ => cell φ (X / K) (k - 1)) ∘ fun t : ℝ => ⌈t / (X / K)⌉₊) _
        exact (measurable_from_nat.comp (measurable_id.div_const _).nat_ceil).aestronglyMeasurable
    · refine eventually_atTop.2 ⟨1, fun K hK => Filter.Eventually.of_forall fun t ht => ?_⟩
      have hK0 : 0 < K := by omega
      rw [Set.uIoc_of_le hX.le] at ht
      obtain ⟨hiK, hi1, hi2⟩ := hceil_idx hK0 ht.1 ht.2
      rw [Real.norm_eq_abs, stepFn_eq φ (div_pos hX (Nat.cast_pos.2 hK0)) _ hi1 hi2]
      exact habs_cell hiK
    · exact intervalIntegrable_const
    · have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ((P : Set ℝ) ∪ {X}) :=
        measure_eq_zero_iff_ae_notMem.1 ((P.finite_toSet.union (Set.finite_singleton X)).measure_zero _)
      filter_upwards [hnull] with t ht htI
      rw [Set.uIoc_of_le hX.le] at htI
      simp only [Set.mem_union, Set.mem_singleton_iff, not_or, Finset.mem_coe] at ht
      have htIoo : t ∈ Set.Ioo 0 X := ⟨htI.1, lt_of_le_of_ne htI.2 ht.2⟩
      rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 (hcont t htIoo ht.1) (η / 2) (by linarith)
      refine ⟨⌈X / δ⌉₊ + 1, fun K hK => ?_⟩
      have hK0 : 0 < K := by omega
      have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK0
      have hh : 0 < X / K := div_pos hX hKR
      have hhδ : X / K < δ := by
        rw [div_lt_iff₀ hKR]
        have h2 : ((⌈X / δ⌉₊ : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast hK
        have h3 : X / δ < K := by linarith [Nat.le_ceil (X / δ)]
        rw [div_lt_iff₀ hδ] at h3; linarith
      obtain ⟨hiK, hi1, hi2⟩ := hceil_idx hK0 htIoo.1 htIoo.2.le
      set i := ⌈t / (X / K)⌉₊ - 1
      rw [stepFn_eq φ hh i hi1 hi2, Real.dist_eq, abs_lt]
      have hlow := hle_cell hiK ⟨hi1.le, hi2⟩
      have hup : cell φ (X / K) i ≤ φ t + η / 2 :=
        csSup_le ⟨φ t, t, ⟨hi1.le, hi2⟩, rfl⟩ (by
          rintro _ ⟨v, hv, rfl⟩
          have hd : dist v t < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hv.1, hv.2]
          linarith [(abs_lt.1 (Real.dist_eq (φ v) (φ t) ▸ hδφ hd)).2])
      constructor <;> linarith
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 htend).2 _ (lt_add_of_pos_right _ (half_pos hε)))
  set K : ℕ := K₁ + 1
  have hK : 0 < K := Nat.succ_pos _
  have hKint := hK₁ K (Nat.le_succ _)
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set h : ℝ := X / K with hhdef
  have hh : 0 < h := div_pos hX hKR
  have hKh : (K : ℝ) * h = X := by rw [hhdef]; field_simp
  have hint_IB : ∫ u in (0 : ℝ)..X, φ u = D.IB := by
    rw [intervalIntegral.integral_of_le hX.le]
    exact (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      Set.Ioc_subset_Ioi_self fun v ⟨hv1, hv2⟩ => by
        simp [φ, hD.f_cond.vanish v (not_lt.1 fun h => hv2 ⟨hv1, h.le⟩)]).symm
  rw [hint_IB] at hKint
  refine ⟨⌈Real.exp (28 * K * M / ε)⌉₊ + 2, fun q hq => ?_⟩
  have hq1 : 1 < q := by omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
  have hqpos : (0 : ℝ) < q := by linarith
  have hℓ : 0 < Real.log q := Real.log_pos hqR
  have hℓbig : 28 * K * M < ε * Real.log q := by
    rw [← div_lt_iff₀' hε, Real.lt_log_iff_exp_lt (by linarith)]
    have : (⌈Real.exp (28 * K * M / ε)⌉₊ : ℝ) + 2 ≤ q := by exact_mod_cast hq
    linarith [Nat.le_ceil (Real.exp (28 * K * M / ε))]
  have hpart : ∀ j ≤ K, ∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ ((j : ℝ) * h)⌋₊, Λ n / n * φ (Real.log n / Real.log q) ≤
      ∑ i ∈ Finset.range j, cell φ h i * (mertensSum ((q : ℝ) ^ (((i + 1 : ℕ) : ℝ) * h)) - mertensSum ((q : ℝ) ^ ((i : ℝ) * h))) := by
    intro j hj
    induction j with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, Real.rpow_zero, Nat.floor_one, Finset.range_zero, Finset.sum_empty]
      rw [show Finset.Ioc 0 1 = {1} from rfl, Finset.sum_singleton]; simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have hmonoF : ⌊(q : ℝ) ^ ((j : ℝ) * h)⌋₊ ≤ ⌊(q : ℝ) ^ (((j + 1 : ℕ) : ℝ) * h)⌋₊ :=
        Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hqR.le (by push_cast; nlinarith))
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF,
        show mertensSum ((q : ℝ) ^ (((j + 1 : ℕ) : ℝ) * h)) - mertensSum ((q : ℝ) ^ ((j : ℝ) * h)) =
          ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ ((j : ℝ) * h)⌋₊ ⌊(q : ℝ) ^ (((j + 1 : ℕ) : ℝ) * h)⌋₊, Λ n / n by
          unfold mertensSum; rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF]; ring,
        Finset.mul_sum]
      refine add_le_add (ih (by omega)) (Finset.sum_le_sum fun n hn => ?_)
      rw [Finset.mem_Ioc] at hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le _).trans_lt hn.1
      have h1 : (j : ℝ) * h * Real.log q < Real.log n := by
        rw [← Real.log_rpow hqpos]
        exact Real.log_lt_log (Real.rpow_pos_of_pos hqpos _)
          ((Nat.floor_lt (Real.rpow_pos_of_pos hqpos _).le).1 hn.1)
      have h2 : Real.log n ≤ ((j + 1 : ℕ) : ℝ) * h * Real.log q := by
        rw [← Real.log_rpow hqpos]
        exact Real.log_le_log hnR ((Nat.le_floor_iff (Real.rpow_pos_of_pos hqpos _).le).1 hn.2)
      rw [mul_comm (cell φ h j)]
      exact mul_le_mul_of_nonneg_left
        (hle_cell (by omega) ⟨((lt_div_iff₀ hℓ).2 h1).le, by push_cast at h2; exact (div_le_iff₀ hℓ).2 h2⟩)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg hnR.le)
  have hpartK := hpart K le_rfl
  simp only [hKh, ← Finset.Icc_add_one_left_eq_Ioc, zero_add] at hpartK
  change (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊, Λ n / n * φ (Real.log n / Real.log q)) / Real.log q ≤ _
  have hterm (i : ℕ) (hi : i ∈ Finset.range K) :
      cell φ h i * (mertensSum ((q : ℝ) ^ (((i + 1 : ℕ) : ℝ) * h)) -
        mertensSum ((q : ℝ) ^ ((i : ℝ) * h))) ≤ cell φ h i * h * Real.log q + 14 * M := by
    have h1 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR.le (by positivity : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) * h))
    have h2 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR.le (by positivity : (0 : ℝ) ≤ (i : ℝ) * h))
    rw [Real.log_rpow hqpos] at h1 h2
    rw [abs_le] at h1 h2
    set D := mertensSum ((q : ℝ) ^ (((i + 1 : ℕ) : ℝ) * h)) - mertensSum ((q : ℝ) ^ ((i : ℝ) * h))
    have hs : |D - h * Real.log q| ≤ 14 := by
      dsimp only [D]; push_cast at h1 ⊢
      rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hc := habs_cell (Finset.mem_range.1 hi)
    rw [← hhdef] at hc
    have := (le_abs_self (cell φ h i * (D - h * Real.log q))).trans
      (abs_mul (cell φ h i) (D - h * Real.log q) ▸ mul_le_mul hc hs (abs_nonneg _) hM)
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_mul] at hsum
  have hint := (integral_stepFn φ hh K).2
  rw [hKh] at hint
  rw [← hint] at hsum
  rw [div_le_iff₀ hℓ]
  nlinarith [mul_lt_mul_of_pos_right hKint hℓ]

def sieveNu (V : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamWeight V d) ^ 2

lemma sieveNu_nonneg (V : ℝ) (n : ℕ) : 0 ≤ sieveNu V n := sq_nonneg _

lemma abs_grahamWeight_le_one (V : ℝ) (d : ℕ) : |grahamWeight V d| ≤ 1 := by
  unfold grahamWeight
  split_ifs with h
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      have hVpos : 0 < V := by linarith
      have hdpos : (0 : ℝ) < d := by linarith
      have hlogV : 0 ≤ Real.log V := Real.log_nonneg (hd1.trans h)
      have h1 : 0 ≤ Real.log (V / d) := Real.log_nonneg (by rw [le_div_iff₀ hdpos]; linarith)
      have h2 : Real.log (V / d) ≤ Real.log V := Real.log_le_log (by positivity) (div_le_self hVpos.le hd1)
      have hmu : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      rw [abs_div, abs_mul, abs_of_nonneg h1, abs_of_nonneg hlogV]
      exact div_le_one_of_le₀ (by nlinarith) hlogV
  · simp

lemma sum_Ioc_by_parts (f W : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, f n * W n =
      (∑ k ∈ Finset.Ioc a b, f k) * W (b + 1) +
        ∑ n ∈ Finset.Ioc a b, (∑ k ∈ Finset.Ioc a n, f k) * (W n - W (n + 1)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : a ≤ b
    · simp only [Finset.sum_Ioc_succ_top hab, ih]; ring
    · simp [Finset.Ioc_eq_empty (by omega : ¬ a < b + 1)]

lemma sum_Ioc_inv_le (a b : ℕ) : ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n ≤ 1 + Real.log b :=
  (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc (Nat.zero_le a) le_rfl)
    fun _ _ _ => by positivity).trans
    (by simpa [← Finset.Icc_add_one_left_eq_Ioc, harmonic_eq_sum_Icc, one_div] using harmonic_le_one_add_log b)

def wt (s : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) * (n : ℂ) ^ (-s)

lemma norm_wt_sub_le (s : ℂ) (hs : 1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖wt s n - wt s (n + 1)‖ ≤ (1 + ‖s‖ * Real.log (n + 1)) / (n : ℝ) ^ 2 := by
  set G : ℝ → ℂ := fun u => (u : ℂ) * cexp ((u : ℂ) * (-s))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hwt (m : ℕ) (hm : 0 < m) : wt s m = G (Real.log m) := by
    unfold wt G
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm.ne'), ← Complex.ofReal_natCast,
      ← Complex.ofReal_log (Nat.cast_nonneg m)]
  set u₀ := Real.log n
  set u₁ := Real.log ((n : ℝ) + 1)
  have hu : u₀ ≤ u₁ := Real.log_le_log hn0 (by linarith)
  have hu0 : 0 ≤ u₀ := Real.log_nonneg (by exact_mod_cast hn)
  have hu₁0 : 0 ≤ u₁ := hu0.trans hu
  have hderiv (u : ℝ) : HasDerivAt G (cexp ((u : ℂ) * (-s)) * (1 - u * s)) u := by
    have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := by simpa using (hasDerivAt_id u).ofReal_comp
    convert h1.mul (h1.mul_const (-s)).cexp using 1; ring
  have hbound (u : ℝ) (hu' : u ∈ Set.Icc u₀ u₁) :
      ‖cexp ((u : ℂ) * (-s)) * (1 - u * s)‖ ≤ (1 + ‖s‖ * u₁) / n := by
    have hu'nn : 0 ≤ u := hu0.trans hu'.1
    rw [norm_mul, Complex.norm_exp, div_eq_mul_inv, mul_comm, Complex.re_ofReal_mul, Complex.neg_re]
    have e2 : Real.exp (u * -s.re) ≤ (n : ℝ)⁻¹ := by
      rw [← Real.exp_log hn0, ← Real.exp_neg]
      exact Real.exp_le_exp.2 (by nlinarith [hu'.1])
    have e3 : ‖1 - (u : ℂ) * s‖ ≤ 1 + ‖s‖ * u₁ :=
      (norm_sub_le _ _).trans (by
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu'nn]
        nlinarith [hu'.2, norm_nonneg s])
    exact mul_le_mul e3 e2 (by positivity) (by positivity)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ => (hderiv u).hasDerivWithinAt) hbound (convex_Icc u₀ u₁)
    (Set.left_mem_Icc.2 hu) (Set.right_mem_Icc.2 hu)
  have hdiff' : ‖u₁ - u₀‖ ≤ 1 / n := by
    rw [Real.norm_of_nonneg (sub_nonneg.2 hu), ← Real.log_div (by positivity) hn0.ne']
    exact (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by field_simp; ring)
  rw [hwt n hn, hwt (n + 1) n.succ_pos, Nat.cast_add, Nat.cast_one, norm_sub_rev]
  exact key.trans ((mul_le_mul_of_nonneg_left hdiff' (by positivity)).trans_eq (by ring))

lemma lcm_sum_le (K : ℕ) :
    ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤
      9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log K) := by
  have hrpow_sum (Y : ℕ) : ∑ j ∈ Finset.Ioc 0 Y, (j : ℝ) ^ (-((2 : ℝ) / 3)) ≤ 3 * (Y : ℝ) ^ ((1 : ℝ) / 3) := by
    induction Y with
    | zero => simp
    | succ Y ih =>
      rw [Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
      have hY0 : (0 : ℝ) ≤ Y := Y.cast_nonneg
      have hY1 : (0 : ℝ) < (Y : ℝ) + 1 := by linarith
      set a := ((Y : ℝ) + 1) ^ ((1 : ℝ) / 3)
      set b := (Y : ℝ) ^ ((1 : ℝ) / 3)
      have ha3 : a ^ 3 = (Y : ℝ) + 1 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hY1.le]; norm_num
      have hb3 : b ^ 3 = (Y : ℝ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
      have hlhs : ((Y : ℝ) + 1) ^ (-((2 : ℝ) / 3)) = 1 / a ^ 2 := by
        rw [Real.rpow_neg hY1.le, ← Real.rpow_natCast, ← Real.rpow_mul hY1.le, one_div]; norm_num
      have ha0 : 0 < a := Real.rpow_pos_of_pos hY1 _
      have hb0 : 0 ≤ b := Real.rpow_nonneg hY0 _
      have key : ((Y : ℝ) + 1) ^ (-((2 : ℝ) / 3)) ≤ 3 * (a - b) := by
        rw [hlhs, div_le_iff₀ (by positivity)]
        nlinarith [mul_nonneg (sq_nonneg (a - b)) (by positivity : (0 : ℝ) ≤ 2 * a + b)]
      push_cast; dsimp [a, b] at key; linarith
  let F : ℕ → ℕ → ℝ := fun g d => if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0
  have hF0 (g d : ℕ) : 0 ≤ F g d := by simp only [F]; split_ifs <;> positivity
  let X : ℕ → ℕ → ℕ → ℝ := fun g d e => (g : ℝ) ^ ((2 : ℝ) / 3) * (F g d * F g e)
  have hX0 (g d e : ℕ) : 0 ≤ X g d e := mul_nonneg (by positivity) (mul_nonneg (hF0 g d) (hF0 g e))
  have h1 (d : ℕ) (hd : d ∈ Finset.Ioc 0 K) (e : ℕ) (he : e ∈ Finset.Ioc 0 K) :
      ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤ ∑ g ∈ Finset.Ioc 0 K, X g d e := by
    rw [Finset.mem_Ioc] at hd he
    have hg : (0 : ℝ) < (Nat.gcd d e : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left e hd.1
    have hl : (0 : ℝ) < (Nat.lcm d e : ℕ) := by exact_mod_cast Nat.lcm_pos hd.1 he.1
    have hprod : ((Nat.gcd d e : ℕ) : ℝ) * (Nat.lcm d e : ℕ) = (d : ℝ) * e := by
      exact_mod_cast Nat.gcd_mul_lcm d e
    have hval : ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) = X (Nat.gcd d e) d e := by
      simp only [X, F, Nat.gcd_dvd_left d e, Nat.gcd_dvd_right d e, ite_true]
      rw [← Real.mul_rpow d.cast_nonneg e.cast_nonneg, ← hprod, Real.mul_rpow hg.le hl.le,
        ← mul_assoc, ← Real.rpow_add hg]
      norm_num
    rw [hval]
    exact Finset.single_le_sum (fun g _ => hX0 g d e)
      (Finset.mem_Ioc.2 ⟨Nat.gcd_pos_of_pos_left e hd.1, (Nat.gcd_le_left e hd.1).trans hd.2⟩)
  have hK13 : ((K : ℝ) ^ ((1 : ℝ) / 3)) * ((K : ℝ) ^ ((1 : ℝ) / 3)) = (K : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add' K.cast_nonneg (by norm_num)]; norm_num
  refine (Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => h1 d hd e he).trans ?_
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm), Finset.sum_comm]
  have hstep : ∑ g ∈ Finset.Ioc 0 K, ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e ≤
      ∑ g ∈ Finset.Ioc 0 K, 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 / (g : ℝ)) := by
    refine Finset.sum_le_sum fun g hg => ?_
    have hfactor : ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e =
        (g : ℝ) ^ ((2 : ℝ) / 3) * ((∑ d ∈ Finset.Ioc 0 K, F g d) * (∑ e ∈ Finset.Ioc 0 K, F g e)) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
    rw [hfactor]
    have hg1' : 0 < g := (Finset.mem_Ioc.1 hg).1
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg1'
    have hg0 : (0 : ℝ) < g := by linarith
    have hU : ∑ d ∈ Finset.Ioc 0 K, F g d ≤ 3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ := by
      dsimp [F]
      rw [sum_Ioc_ite_dvd (f := fun d => (d : ℝ) ^ (-((2 : ℝ) / 3))) hg1', Nat.zero_div]
      simp only [Nat.cast_mul]
      rw [Finset.sum_congr rfl fun m _ => Real.mul_rpow hg0.le (Nat.cast_nonneg m), ← Finset.mul_sum]
      refine (mul_le_mul_of_nonneg_left ((hrpow_sum _).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) Nat.cast_div_le (by norm_num)) (by norm_num)))
        (by positivity)).trans_eq ?_
      rw [Real.div_rpow K.cast_nonneg hg0.le,
        ← show (g : ℝ) ^ (-((2 : ℝ) / 3)) / (g : ℝ) ^ ((1 : ℝ) / 3) = (g : ℝ)⁻¹ by
          rw [← Real.rpow_sub hg0, show (-((2 : ℝ) / 3) - 1 / 3) = -1 by norm_num, Real.rpow_neg_one]]
      ring
    have hU0 : 0 ≤ ∑ d ∈ Finset.Ioc 0 K, F g d := Finset.sum_nonneg fun d _ => hF0 g d
    have hgg : (g : ℝ) ^ ((2 : ℝ) / 3) * (g : ℝ)⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ hg0, one_mul]
      exact (Real.rpow_le_rpow_of_exponent_le hg1 (by norm_num)).trans_eq (Real.rpow_one _)
    refine (mul_le_mul_of_nonneg_left (mul_self_le_mul_self hU0 hU) (by positivity)).trans ?_
    rw [show (g : ℝ) ^ ((2 : ℝ) / 3) * ((3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹) * (3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹)) =
      9 * (K : ℝ) ^ ((2 : ℝ) / 3) * ((g : ℝ) ^ ((2 : ℝ) / 3) * (g : ℝ)⁻¹) * (g : ℝ)⁻¹ by rw [← hK13]; ring,
      one_div]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) hgg) (by positivity)
  refine hstep.trans ?_
  rw [← Finset.mul_sum]; gcongr; exact sum_Ioc_inv_le 0 K

private lemma Lambda_bound {L σ c P : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ c * P) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ 2 * P) (hc : 1 ≤ c) (hP : 1 ≤ P) :
    L + (1 + σ * L) * (1 + L) ≤ 7 * c ^ 2 * P ^ 3 := by
  have hcP : 1 ≤ c * P := by nlinarith
  have h0 : 1 ≤ c * P * P := by nlinarith
  have h1 := mul_le_mul hσ hL hL0 (by linarith)
  have h4 : (1 + σ * L) * (1 + L) ≤ (3 * (c * P) * P) * (2 * (c * P)) :=
    mul_le_mul (by nlinarith) (by linarith) (by linarith) (by positivity)
  nlinarith [show L ≤ (c * P) * (c * P) * P by nlinarith]

theorem sieve_offdiag (hBur : BurgessBound) {ε' tmax : ℝ} (hε' : 0 < ε') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {q : ℕ}, 2 ≤ q →
      ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, 1 / 3 + 2 * ε' < t → t ≤ t' → t' ≤ tmax → 0 ≤ β → β ≤ 1 →
        |τ| ≤ Real.log q →
        ‖∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu ((q : ℝ) ^ ((t - 1 / 3) / 2 - ε')) n : ℂ) * ψ n * (Real.log n : ℂ) *
              (n : ℂ) ^ (-((1 + β : ℝ) + (τ : ℂ) * I))‖ ≤ C * (q : ℝ) ^ (-(ε' / 6)) := by
  obtain ⟨CB, hCB⟩ := hBur (ε' / 3) (by positivity)
  set C₀ := max CB 0
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set c₁ := max 1 tmax
  have hc₁1 : 1 ≤ c₁ := le_max_left _ _
  have hc₁t : tmax ≤ c₁ := le_max_right _ _
  set M : ℝ := 1 + 24 / ε' with hM
  refine ⟨C₀ * (63 * c₁ ^ 3 * M ^ 4), by positivity, ?_⟩
  intro q hq ψ hψ t t' β τ ht htt' ht'max hβ0 hβ1 hτ
  have hqpos : 0 < q := by omega
  have : NeZero q := ⟨hqpos.ne'⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hqpos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hℓ0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht0 : 0 < t := by linarith
  set Kq := C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) with hKq
  have hKq0 : 0 ≤ Kq := by positivity
  have hBurq (N H : ℕ) : ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤ Kq * (H : ℝ) ^ ((2 : ℝ) / 3) := by
    induction H using Nat.strong_induction_on generalizing N with
    | _ H ih =>
      rcases Nat.eq_zero_or_pos H with rfl | hH
      · simp
      by_cases hHq : H ≤ q
      · exact (hCB q ψ hψ N H hH hHq).trans (by dsimp [Kq]; gcongr; exact le_max_left _ _)
      · rw [← Finset.sum_Ioc_consecutive _ (Nat.le_add_right N q) (by omega),
          sum_Ioc_period_eq_zero ψ hψ, zero_add, show N + H = N + q + (H - q) by omega]
        exact (ih (H - q) (by omega) (N + q)).trans (by gcongr; exact_mod_cast Nat.sub_le H q)
  set P := 1 + Real.log q with hPdef
  have hP1 : 1 ≤ P := by linarith
  set s : ℂ := ((1 + β : ℝ) : ℂ) + (τ : ℂ) * I
  have hs : 1 ≤ s.re := by simp [s]; linarith
  have hsn : ‖s‖ ≤ 2 * P := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith [hPdef]
  set δ := (t - 1 / 3) / 2 - ε' with hδ
  have hδ0 : 0 < δ := by linarith
  set V := (q : ℝ) ^ δ
  set A := (q : ℝ) ^ t
  set B := (q : ℝ) ^ t'
  have hV1 : 1 ≤ V := Real.one_le_rpow hq1 hδ0.le
  have hlogV : Real.log V = δ * Real.log q := Real.log_rpow hq0 δ
  have hexp : (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * A ^ (-((1 : ℝ) / 3)) *
      V ^ ((2 : ℝ) / 3) = (q : ℝ) ^ (-(ε' / 3)) := by
    dsimp [A, V]
    rw [← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
    congr 1; rw [hδ]; ring
  have hA1 : 1 ≤ A := Real.one_le_rpow hq1 ht0.le
  have hB1 : 1 ≤ B := Real.one_le_rpow hq1 (by linarith)
  have hlogB : Real.log B = t' * Real.log q := Real.log_rpow hq0 t'
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  set a := ⌈A⌉₊ - 1
  set b := ⌈B⌉₊ - 1
  have ha1 : (a : ℝ) + 1 = (⌈A⌉₊ : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hA0).ne'), Nat.cast_one]; ring
  have hb1 : (b : ℝ) + 1 = (⌈B⌉₊ : ℝ) := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hB0).ne'), Nat.cast_one]; ring
  set L := Real.log ((b : ℝ) + 1) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [b.cast_nonneg (α := ℝ)])
  set Λs := L + (1 + ‖s‖ * L) * (1 + L)
  have hΛ0 : 0 ≤ Λs := add_nonneg hL0 (mul_nonneg (by nlinarith [norm_nonneg s]) (by linarith))
  have hIco : Finset.Ico ⌈A⌉₊ ⌈B⌉₊ = Finset.Ioc a b := by
    ext n; simp only [Finset.mem_Ico, Finset.mem_Ioc, a, b]
    have := Nat.ceil_pos.2 hA0; have := Nat.ceil_pos.2 hB0; omega
  simp_rw [show ∀ n : ℕ, (sieveNu V n : ℂ) * ψ n * (Real.log n : ℂ) * (n : ℂ) ^ (-s) =
    (sieveNu V n : ℂ) * (ψ n * wt s n) from fun n => by unfold wt; ring]
  have hexpand : ∑ n ∈ Finset.Ioc a b, (sieveNu V n : ℂ) * (ψ n * wt s n) =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0) := by
    have hpt (n : ℕ) (hn : n ∈ Finset.Ioc a b) : (sieveNu V n : ℂ) * (ψ n * wt s n) =
        ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
          ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
            (if Nat.lcm d e ∣ n then ψ n * wt s n else 0) := by
      have hn0 : n ≠ 0 := by simp only [Finset.mem_Ioc] at hn; omega
      have hdiv : ∑ d ∈ n.divisors, grahamWeight V d =
          ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, (if d ∣ n then grahamWeight V d else 0) := by
        rw [← Finset.sum_filter]
        exact (Finset.sum_subset (fun d hd => by
            simp only [Finset.mem_filter, Finset.mem_Ioc] at hd
            exact Nat.mem_divisors.2 ⟨hd.2, hn0⟩)
          fun d hd hnot => by
            unfold grahamWeight
            refine ite_eq_right (not_le.2 (Nat.lt_of_floor_lt ?_))
            simp only [Finset.mem_filter, Finset.mem_Ioc, not_and] at hnot
            by_contra hle
            exact hnot ⟨Nat.pos_of_mem_divisors hd, not_lt.1 hle⟩ (Nat.dvd_of_mem_divisors hd)).symm
      have hnu : sieveNu V n = ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
          (if Nat.lcm d e ∣ n then grahamWeight V d * grahamWeight V e else 0) := by
        unfold sieveNu; rw [hdiv, sq, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => by
          by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff]
      rw [hnu, Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Complex.ofReal_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by split_ifs <;> simp
    rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => (Finset.mul_sum _ _ _).symm
  rw [hIco, hexpand]
  have hnorm_T {l : ℕ} (hl : 0 < l) :
      ‖∑ n ∈ Finset.Ioc a b, (if l ∣ n then ψ n * wt s n else 0)‖ ≤
        Kq * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * Λs := by
    have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
    have ha1pos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    set E := Kq * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3))
    have hE0 : 0 ≤ E := by positivity
    have hsum : ∑ n ∈ Finset.Ioc a b, (if l ∣ n then ψ n * wt s n else 0) =
        ∑ n ∈ Finset.Ioc a b, (fun n => if l ∣ n then ψ n else 0) n * wt s n :=
      Finset.sum_congr rfl fun n _ => by by_cases hd : l ∣ n <;> simp [hd]
    rw [hsum, sum_Ioc_by_parts]
    have hkey (x : ℕ) (hx : a < x) :
        ‖∑ k ∈ Finset.Ioc a x, (fun n => if l ∣ n then ψ n else 0) k‖ ≤ E * x := by
      have hcx : (a : ℝ) + 1 ≤ x := by exact_mod_cast hx
      have hdvd : ‖∑ k ∈ Finset.Ioc a x, (if l ∣ k then ψ k else 0)‖ ≤ Kq * ((x : ℝ) / l) ^ ((2 : ℝ) / 3) := by
        rw [sum_Ioc_ite_dvd (f := fun k => ψ k) hl]
        simp only [Nat.cast_mul, map_mul, ← Finset.mul_sum, norm_mul]
        by_cases hax : a / l ≤ x / l
        · rw [show x / l = a / l + (x / l - a / l) by omega]
          refine (mul_le_mul (DirichletCharacter.norm_le_one ψ _) (hBurq _ _) (norm_nonneg _) zero_le_one).trans ?_
          rw [one_mul]; gcongr; exact (Nat.cast_le.2 (Nat.sub_le _ _)).trans Nat.cast_div_le
        · rw [Finset.Ioc_eq_empty (by omega)]; simp; positivity
      have hdiv : ((x : ℝ) / l) ^ ((2 : ℝ) / 3) ≤
          (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * x := by
        have hx0 : (0 : ℝ) < x := ha1pos.trans_le hcx
        rw [Real.div_rpow hx0.le hlpos.le, div_eq_mul_inv, ← Real.rpow_neg hlpos.le,
          show (x : ℝ) ^ ((2 : ℝ) / 3) = x * (x : ℝ) ^ (-((1 : ℝ) / 3)) by
            rw [show (2 : ℝ) / 3 = 1 + (-((1 : ℝ) / 3)) by norm_num, Real.rpow_add hx0, Real.rpow_one]]
        have h2 : (x : ℝ) ^ (-((1 : ℝ) / 3)) ≤ ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) :=
          Real.rpow_le_rpow_of_nonpos ha1pos hcx (by norm_num)
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hx0.le) (by positivity)).trans_eq (by ring)
      exact hdvd.trans ((mul_le_mul_of_nonneg_left hdiv hKq0).trans_eq (by dsimp [E]; ring))
    rcases le_or_gt b a with hab | hab
    · rw [Finset.Ioc_eq_empty (by omega)]; simp; exact mul_nonneg hE0 hΛ0
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
    have hT1 : ‖(∑ k ∈ Finset.Ioc a b, (fun n => if l ∣ n then ψ n else 0) k) * wt s (b + 1)‖ ≤ E * L := by
      rw [norm_mul]
      have hw : ‖wt s (b + 1)‖ ≤ L / ((b : ℝ) + 1) := by
        unfold wt
        rw [norm_mul, Complex.norm_natCast_cpow_of_pos b.succ_pos, Nat.cast_add, Nat.cast_one,
          ← hL, Complex.norm_real, Real.norm_of_nonneg hL0, div_eq_mul_inv, Complex.neg_re]
        gcongr
        exact (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans_eq (Real.rpow_neg_one _)
      refine (mul_le_mul (hkey b hab) hw (norm_nonneg _) (mul_nonneg hE0 hb0.le)).trans ?_
      rw [show E * b * (L / ((b : ℝ) + 1)) = E * L * (b / ((b : ℝ) + 1)) by ring]
      exact mul_le_of_le_one_right (mul_nonneg hE0 hL0) ((div_le_one (by positivity)).2 (by linarith))
    have hT2 (n : ℕ) (hn : n ∈ Finset.Ioc a b) :
        ‖(∑ k ∈ Finset.Ioc a n, (fun n => if l ∣ n then ψ n else 0) k) *
          (wt s n - wt s (n + 1))‖ ≤ E * (1 + ‖s‖ * L) * (1 / (n : ℝ)) := by
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := by omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hlog : Real.log ((n : ℝ) + 1) ≤ L :=
        Real.log_le_log (by positivity) (by linarith [show (n : ℝ) ≤ b by exact_mod_cast hn.2])
      have hw : ‖wt s n - wt s (n + 1)‖ ≤ (1 + ‖s‖ * L) / (n : ℝ) ^ 2 :=
        (norm_wt_sub_le s hs hn1).trans (by gcongr)
      rw [norm_mul]
      exact (mul_le_mul (hkey n hn.1) hw (norm_nonneg _) (mul_nonneg hE0 hn0.le)).trans_eq (by field_simp)
    have hharm : ∑ n ∈ Finset.Ioc a b, (1 / (n : ℝ)) ≤ 1 + L :=
      (sum_Ioc_inv_le a b).trans (by dsimp [L]; gcongr; linarith)
    refine ((norm_add_le _ _).trans (add_le_add hT1 ((norm_sum_le _ _).trans (Finset.sum_le_sum hT2)))).trans ?_
    rw [← Finset.mul_sum]; dsimp [Λs]; rw [mul_add]
    linarith [mul_le_mul_of_nonneg_left hharm (show 0 ≤ E * (1 + ‖s‖ * L) by positivity)]
  have hT (d : ℕ) (hd : d ∈ Finset.Ioc 0 ⌊V⌋₊) (e : ℕ) (he : e ∈ Finset.Ioc 0 ⌊V⌋₊) :
      ‖((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0)‖ ≤
        Kq * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * Λs * ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) := by
    rw [Finset.mem_Ioc] at hd he
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (mul_le_mul (abs_grahamWeight_le_one V d) (abs_grahamWeight_le_one V e)
      (abs_nonneg _) zero_le_one) (hnorm_T (Nat.lcm_pos hd.1 he.1))
      (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hLle : L ≤ c₁ * P := by
    dsimp [L]; rw [hb1]
    have h2 : Real.log (⌈B⌉₊ : ℝ) ≤ Real.log (2 * B) :=
      Real.log_le_log (by exact_mod_cast Nat.ceil_pos.2 hB0) (by linarith [Nat.ceil_lt_add_one hB0.le])
    rw [Real.log_mul (by norm_num) hB0.ne', hlogB] at h2
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (x := 2) (by norm_num)]
    linarith [mul_le_mul_of_nonneg_right (ht'max.trans hc₁t) hℓ0, hPdef]
  have hK1 : 1 ≤ ⌊V⌋₊ := Nat.floor_pos.2 hV1
  have h1logK : 0 ≤ 1 + Real.log (⌊V⌋₊ : ℝ) := by
    linarith [Real.log_nonneg (by exact_mod_cast hK1 : (1 : ℝ) ≤ ⌊V⌋₊)]
  have hlogK : 1 + Real.log (⌊V⌋₊ : ℝ) ≤ c₁ * P := by
    have h1 : Real.log (⌊V⌋₊ : ℝ) ≤ Real.log V :=
      Real.log_le_log (by exact_mod_cast hK1) (Nat.floor_le (by linarith))
    rw [hlogV] at h1
    have hδt : δ ≤ c₁ := by rw [hδ]; linarith
    linarith [mul_le_mul_of_nonneg_right hδt hℓ0, hPdef]
  have hK23 : (⌊V⌋₊ : ℝ) ^ ((2 : ℝ) / 3) ≤ V ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num)
  have hA13 : ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) ≤ A ^ (-((1 : ℝ) / 3)) := by
    rw [ha1]; exact Real.rpow_le_rpow_of_nonpos hA0 (Nat.le_ceil A) (by norm_num)
  have hPq : P ^ 4 ≤ M ^ 4 * (q : ℝ) ^ (ε' / 6) := by
    have hlog := Real.log_le_rpow_div hq0.le (show 0 < ε' / 24 by positivity)
    have hq24 : 1 ≤ (q : ℝ) ^ (ε' / 24) := Real.one_le_rpow hq1 (by positivity)
    have hP : P ≤ M * (q : ℝ) ^ (ε' / 24) := by
      rw [hM, hPdef]; have : (q : ℝ) ^ (ε' / 24) / (ε' / 24) = 24 / ε' * (q : ℝ) ^ (ε' / 24) := by field_simp
      linarith
    have hpow : ((q : ℝ) ^ (ε' / 24)) ^ 4 = (q : ℝ) ^ (ε' / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; congr 1; push_cast; ring
    exact (pow_le_pow_left₀ (by positivity) hP 4).trans_eq (by rw [mul_pow, hpow])
  have hΛ : Λs ≤ 7 * c₁ ^ 2 * P ^ 3 :=
    Lambda_bound hL0 hLle (norm_nonneg s) hsn hc₁1 hP1
  have hAr0 : 0 ≤ A ^ (-((1 : ℝ) / 3)) := Real.rpow_nonneg hA0.le _
  have hVr0 : 0 ≤ V ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have hc0 : 0 ≤ c₁ := by linarith
  have hP0 : 0 ≤ P := by linarith
  refine ((norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)).trans ?_
  refine (Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hT d hd e he).trans ?_
  simp_rw [← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left (lcm_sum_le _)
    (mul_nonneg (mul_nonneg hKq0 (Real.rpow_nonneg (by positivity) _)) hΛ0)).trans ?_
  refine (mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hA13 hKq0) hΛ hΛ0 (mul_nonneg hKq0 hAr0))
    (mul_le_mul (mul_le_mul_of_nonneg_left hK23 (by norm_num)) hlogK h1logK (by positivity))
    (mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _)) h1logK)
    (mul_nonneg (mul_nonneg hKq0 hAr0) (by positivity))).trans ?_
  rw [show Kq * A ^ (-((1 : ℝ) / 3)) * (7 * c₁ ^ 2 * P ^ 3) * (9 * V ^ ((2 : ℝ) / 3) * (c₁ * P)) =
      63 * c₁ ^ 3 * P ^ 4 * (C₀ * ((q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) *
        A ^ (-((1 : ℝ) / 3)) * V ^ ((2 : ℝ) / 3))) by rw [hKq]; ring, hexp]
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPq (by positivity))
    (mul_nonneg hC₀0 (Real.rpow_nonneg hq0.le _))).trans_eq ?_
  rw [show 63 * c₁ ^ 3 * (M ^ 4 * (q : ℝ) ^ (ε' / 6)) * (C₀ * (q : ℝ) ^ (-(ε' / 3))) =
    C₀ * (63 * c₁ ^ 3 * M ^ 4) * ((q : ℝ) ^ (-(ε' / 3)) * (q : ℝ) ^ (ε' / 6)) by ring,
    ← Real.rpow_add hq0]
  congr 2; ring

def sieveDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D.m,
    D.h k * Real.exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

private lemma hasDerivAt_log_div_self {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log t / t) ((1 - Real.log t) / t ^ 2) t := by
  convert (Real.hasDerivAt_log ht).div (hasDerivAt_id' (x := t)) ht using 1
  field_simp

private lemma continuousOn_log_div_self {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc A B) :=
  (Real.continuousOn_log.mono fun _ ht => (hA.trans_le ht.1).ne').div continuousOn_id
    fun _ ht => (hA.trans_le ht.1).ne'

private lemma sum_Icc_zero_sieveNu (V : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, sieveNu V k = ∑ k ∈ Finset.Icc 1 n, sieveNu V k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons,
    show sieveNu V 0 = 0 by simp [sieveNu], zero_add, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

private lemma sieve_diagonal (hGr : GrahamEstimate) :
    ∃ C V₀ : ℝ, 0 ≤ C ∧ ∀ V A B : ℝ, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
        (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
          C * (Real.log B ^ 2 + 1) / Real.log V ^ 2 := by
  obtain ⟨C₀, V₁, hC₀⟩ := hGr
  set C₁ := max C₀ 0
  have hC₁ : 0 ≤ C₁ := le_max_right C₀ 0
  refine ⟨3 + 3 * C₁, max V₁ (Real.exp 1), by positivity, fun V A B hV hVA hAB => ?_⟩
  have hV1 : V₁ ≤ V := (le_max_left _ _).trans hV
  have hVe : Real.exp 1 ≤ V := (le_max_right _ _).trans hV
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hA2 : 2 ≤ A := (h2e.trans hVe).trans hVA
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hL1 : 1 ≤ Real.log V := by simpa using Real.log_le_log (Real.exp_pos 1) hVe
  have hL0 : 0 < Real.log V := by linarith
  have hLA : Real.log V ≤ Real.log A := Real.log_le_log (by linarith) hVA
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log hA0 hAB
  set K := 1 / Real.log V + C₁ / Real.log V ^ 2
  have hK0 : 0 ≤ K := by positivity
  have hS (N : ℝ) (hVN : V ≤ N) :
      N / Real.log V - C₁ * N / Real.log V ^ 2 ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ∧
        ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ≤ N * K := by
    have hN : 0 ≤ N := (Real.exp_pos 1).le.trans (hVe.trans hVN)
    have h2 := abs_le.mp ((hC₀ V N hV1 hVN).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C₀ 0) hN) (sq_nonneg _)))
    simp only [sieveNu, K]
    exact ⟨by linarith [h2.1], by linarith [h2.2, show N / Real.log V + C₁ * N / Real.log V ^ 2 =
      N * (1 / Real.log V + C₁ / Real.log V ^ 2) by ring]⟩
  have step1 : ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
      Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * sieveNu V ⌊A⌋₊ +
        ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, Real.log n / n * sieveNu V n := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (Nat.floor_le_ceil A) le_rfl)
      fun n _ _ => mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) n.cast_nonneg)
        (sieveNu_nonneg V n)).trans_eq ?_
    rw [Finset.Icc_eq_cons_Ioc (Nat.floor_le_floor hAB), Finset.sum_cons]
  have hint : IntegrableOn (deriv (fun t : ℝ => Real.log t / t)) (Set.Icc A B) := by
    have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Icc A B) :=
      (continuousOn_const.sub (Real.continuousOn_log.mono fun _ ht => (hA0.trans_le ht.1).ne')).div
        (continuousOn_id.pow 2) fun _ ht => pow_ne_zero 2 (hA0.trans_le ht.1).ne'
    exact hcont.integrableOn_Icc.congr_fun
      (fun t ht => (hasDerivAt_log_div_self (hA0.trans_le ht.1).ne').deriv.symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul (sieveNu V) hA0.le hAB
    (fun t ht => (hasDerivAt_log_div_self (hA0.trans_le ht.1).ne').differentiableAt) hint
  have hBt : Real.log B / B * ∑ k ∈ Finset.Icc 0 ⌊B⌋₊, sieveNu V k ≤
      Real.log B / Real.log V + C₁ * Real.log B / Real.log V ^ 2 := by
    rw [sum_Icc_zero_sieveNu]
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    refine (mul_le_mul_of_nonneg_left (hS B (hVA.trans hAB)).2 (div_nonneg hlogB0 hB0.le)).trans_eq ?_
    dsimp [K]; field_simp
  have hAt : Real.log A / Real.log V - C₁ * Real.log A / Real.log V ^ 2 ≤
      Real.log A / A * ∑ k ∈ Finset.Icc 0 ⌊A⌋₊, sieveNu V k := by
    rw [sum_Icc_zero_sieveNu]
    have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
    refine (le_of_eq (by field_simp)).trans
      (mul_le_mul_of_nonneg_left (hS A hVA).1 (div_nonneg hlogA0 hA0.le))
  have hIlog : ∫ t in Set.Ioc A B, Real.log t / t = (Real.log B ^ 2 - Real.log A ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t : ℝ => Real.log t ^ 2 / 2)
        (fun x hx => by
          rw [Set.uIcc_of_le hAB] at hx
          have hx0 : x ≠ 0 := (hA0.trans_le hx.1).ne'
          convert ((Real.hasDerivAt_log hx0).pow 2).div_const 2 using 1
          field_simp; ring)
        (by rw [intervalIntegrable_iff, Set.uIoc_of_le hAB]
            exact (continuousOn_log_div_self hA0).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)]
    ring
  have hI : -(∫ t in Set.Ioc A B, deriv (fun t : ℝ => Real.log t / t) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, sieveNu V k) ≤
      K * ((Real.log B ^ 2 - Real.log A ^ 2) / 2) := by
    rw [← integral_neg, ← hIlog, ← integral_const_mul]
    refine setIntegral_mono_on
      (((integrableOn_mul_sum_Icc (m := 0) (sieveNu V) hA0.le hint).mono_set Set.Ioc_subset_Icc_self).neg)
      (((continuousOn_log_div_self hA0).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _)
      measurableSet_Ioc fun t ht => ?_
    have ht0 : 0 < t := hA0.trans ht.1
    have hVt : V ≤ t := hVA.trans ht.1.le
    have hlogt : 1 ≤ Real.log t := by simpa using Real.log_le_log (Real.exp_pos 1) (hVe.trans hVt)
    rw [(hasDerivAt_log_div_self ht0.ne').deriv, sum_Icc_zero_sieveNu,
      show -((1 - Real.log t) / t ^ 2 * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, sieveNu V k) =
        (Real.log t - 1) * (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, sieveNu V k) / t ^ 2 by ring,
      show K * (Real.log t / t) = Real.log t * (t * K) / t ^ 2 by field_simp]
    exact div_le_div_of_nonneg_right
      (mul_le_mul (by linarith) (hS t hVt).2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (by linarith))
      (sq_nonneg t)
  have hE : Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * sieveNu V ⌊A⌋₊ ≤ 2 * Real.log A * K := by
    have hm1 : 1 ≤ ⌊A⌋₊ := (Nat.one_le_floor_iff A).mpr (by linarith)
    have hm_pos : (0 : ℝ) < ⌊A⌋₊ := by exact_mod_cast hm1
    have hlogm : Real.log ⌊A⌋₊ ≤ Real.log A := Real.log_le_log hm_pos (Nat.floor_le hA0.le)
    have hA2m : A ≤ 2 * ⌊A⌋₊ := by linarith [Nat.lt_floor_add_one A]
    have hnu : sieveNu V ⌊A⌋₊ ≤ A * K :=
      (Finset.single_le_sum (f := sieveNu V) (fun i _ => sq_nonneg _)
        (Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩)).trans (hS A hVA).2
    refine (mul_le_mul_of_nonneg_left hnu (div_nonneg (Real.log_natCast_nonneg _) hm_pos.le)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hm_pos]
    have h1 := mul_le_mul hlogm hA2m hA0.le (Real.log_nonneg (by linarith))
    nlinarith [mul_le_mul_of_nonneg_right h1 hK0]
  set a := Real.log A
  set b := Real.log B
  set L := Real.log V
  have hfin : 2 * a * K + (b / L + C₁ * b / L ^ 2) - (a / L - C₁ * a / L ^ 2) +
      K * ((b ^ 2 - a ^ 2) / 2) ≤ (b ^ 2 - a ^ 2) / (2 * L) + (3 + 3 * C₁) * (b ^ 2 + 1) / L ^ 2 := by
    rw [← sub_nonneg, show (b ^ 2 - a ^ 2) / (2 * L) + (3 + 3 * C₁) * (b ^ 2 + 1) / L ^ 2 -
        (2 * a * K + (b / L + C₁ * b / L ^ 2) - (a / L - C₁ * a / L ^ 2) +
          K * ((b ^ 2 - a ^ 2) / 2)) =
        ((3 + 3 * C₁) * (b ^ 2 + 1) - (a + b) * L - C₁ * (3 * a + b) -
          C₁ * (b ^ 2 - a ^ 2) / 2) / L ^ 2 by dsimp [K, L]; field_simp; ring]
    refine div_nonneg ?_ (by positivity)
    nlinarith [mul_nonneg hC₁ (sq_nonneg (b - 1)), mul_nonneg hC₁ (sub_nonneg.2 hlogAB),
      mul_nonneg hC₁ (sq_nonneg a), mul_nonneg (sub_nonneg.2 hLA) (sub_nonneg.2 hlogAB),
      mul_nonneg (sub_nonneg.2 (hLA.trans hlogAB)) (sub_nonneg.2 hlogAB),
      mul_nonneg hC₁ (sub_nonneg.2 hL1), mul_nonneg hC₁ (sub_nonneg.2 hLA)]
  linarith

private lemma small_primepow_sum {V A B : ℝ} (hV : 1 ≤ V) (hA : 1 ≤ A) :
    ∑ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V),
      Λ n / n ≤ 2 * V * Real.log V / A := by
  have hA0 : 0 < A := by linarith
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  set S := (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V)
  have hmaps (n : ℕ) (hn : n ∈ S) : Nat.minFac n ∈ Finset.Icc 1 ⌊V⌋₊ :=
    Finset.mem_Icc.mpr ⟨Nat.minFac_pos n, Nat.le_floor (Finset.mem_filter.1 hn).2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib (p : ℕ) (hpI : p ∈ Finset.Icc 1 ⌊V⌋₊) :
      ∑ n ∈ S.filter (fun n => Nat.minFac n = p), Λ n / n ≤ 2 * Real.log V / A := by
    set T := S.filter (fun n => Nat.minFac n = p)
    have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hpV : (p : ℝ) ≤ V := (Nat.cast_le.mpr (Finset.mem_Icc.1 hpI).2).trans (Nat.floor_le (by linarith))
    have hlogpV : Real.log p ≤ Real.log V :=
      Real.log_le_log (by exact_mod_cast (Finset.mem_Icc.1 hpI).1) hpV
    rcases T.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
    · rw [h, Finset.sum_empty]; positivity
    have hT (n : ℕ) (hn : n ∈ T) : IsPrimePow n ∧ Nat.minFac n = p ∧ A ≤ n := by
      simp only [T, S, Finset.mem_filter, Finset.mem_Ico] at hn
      exact ⟨hn.1.2.1, hn.2, Nat.ceil_le.mp hn.1.1.1⟩
    have hp : p.Prime := (hT n₀ hn₀).2.1 ▸ Nat.minFac_prime (hT n₀ hn₀).1.ne_one
    have hpow (n : ℕ) (hn : n ∈ T) : p ^ (n.factorization p) = n :=
      (hT n hn).2.1 ▸ (hT n hn).1.minFac_pow_factorization_eq
    have hcast (n : ℕ) (hn : n ∈ T) : (n : ℝ) = (p : ℝ) ^ (n.factorization p) := by
      exact_mod_cast (hpow n hn).symm
    have hinj : Set.InjOn (fun n : ℕ => n.factorization p) T := fun n hn m hm h => by
      dsimp only at h; rw [← hpow n hn, ← hpow m hm, h]
    have hterm : ∑ n ∈ T, Λ n / n = Real.log p * ∑ k ∈ T.image (·.factorization p), (1 / (p : ℝ)) ^ k := by
      rw [Finset.sum_image hinj, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hpp, hmin, _⟩ := hT n hn
      rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hpp, hmin, hcast n hn, one_div_pow]
      ring
    set F := T.image (·.factorization p)
    have hne : F.Nonempty := ⟨n₀.factorization p, Finset.mem_image_of_mem _ hn₀⟩
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
    have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    obtain ⟨n₁, hn₁, hminF⟩ := Finset.mem_image.mp (F.min'_mem hne)
    have hAk : A ≤ (p : ℝ) ^ (F.min' hne) := hminF ▸ hcast n₁ hn₁ ▸ (hT n₁ hn₁).2.2
    have hgeom : ∑ k ∈ F, (1 / (p : ℝ)) ^ k ≤ 2 / A := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg
        (t := Finset.Ico (F.min' hne) (F.max' hne + 1))
        (fun k hk => Finset.mem_Ico.mpr ⟨F.min'_le k hk, Nat.lt_succ_of_le (F.le_max' k hk)⟩)
        (fun k _ _ => pow_nonneg hx0 k)).trans ?_
      refine (geom_sum_Ico_le_of_lt_one hx0 (by linarith)).trans ?_
      refine (show (1 / (p : ℝ)) ^ (F.min' hne) / (1 - 1 / (p : ℝ)) ≤ 2 / (p : ℝ) ^ (F.min' hne) by
        rw [div_le_iff₀ (by linarith), show 2 / (p : ℝ) ^ (F.min' hne) = 2 * (1 / (p : ℝ)) ^ (F.min' hne) by
          rw [one_div_pow]; ring]
        nlinarith [pow_nonneg hx0 (F.min' hne)]).trans
        (div_le_div_of_nonneg_left (by norm_num) hA0 hAk)
    rw [hterm]
    refine (mul_le_mul_of_nonneg_left hgeom hlogp).trans ?_
    rw [← mul_div_assoc, mul_comm]
    exact div_le_div_of_nonneg_right (by linarith) hA0.le
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp only [add_tsub_cancel_right]
  exact (mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (by positivity)).trans_eq (by ring)

private lemma rpow_le_natCast_iff_tn {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) (t : ℝ) :
    (q : ℝ) ^ t ≤ n ↔ t ≤ tn q n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hq0 t) (by exact_mod_cast hn), Real.log_rpow hq0,
    tn, le_div_iff₀ (log_q_pos hq)]

private lemma t_mono_le (D : NearData) (hD : D.Valid) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ D.m) :
    D.t k ≤ D.t l := by
  induction l with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact le_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · linarith [ih (by omega) (by omega), hD.t_lt l (by omega)]
    · obtain rfl : k = l + 1 := by omega
      exact le_rfl

theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  obtain ⟨CB, V₀, hCB0, hdiagG⟩ := sieve_diagonal hGr
  obtain ⟨CC, hCC0, hoffC⟩ := sieve_offdiag hBur (tmax := D.t D.m) hD.ε'_pos
  have ht0k (k : ℕ) (hk : k < D.m) : 1 / 3 + 2 * D.ε' < D.t k :=
    hD.t_zero.trans_le (t_mono_le D hD (Nat.zero_le k) hk.le)
  have hlev_pos (k : ℕ) (hk : k < D.m) : 0 < D.level k := by
    unfold NearData.level; linarith [ht0k k hk]
  have hlev_lt (k : ℕ) (hk : k < D.m) : D.level k < D.t k := by
    unfold NearData.level; linarith [ht0k k hk, hD.ε'_pos]
  have hlog_top : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv_log : Tendsto (fun q : ℕ => (Real.log q)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog_top
  have hrpow_neg {α : ℝ} (hα : 0 < α) : Tendsto (fun q : ℕ => (q : ℝ) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop
  have hTerr : Tendsto (fun q : ℕ => ∑ k ∈ Finset.range D.m, D.h k *
      (CB * D.t (k + 1) ^ 2 / D.level k ^ 2 * (Real.log q)⁻¹ +
        CB / D.level k ^ 2 * ((Real.log q)⁻¹) ^ 3 +
        CC * ((q : ℝ) ^ (-(D.ε' / 6)) * (Real.log q)⁻¹) +
        2 * D.level k * (q : ℝ) ^ (-(D.t k - D.level k)))) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ k ∈ Finset.range D.m, D.h k * (0 + 0 + 0 + 0) by simp]
    refine tendsto_finsetSum _ fun k hk => Tendsto.const_mul _
      (Tendsto.add (Tendsto.add (Tendsto.add ?_ ?_) ?_) ?_)
    · simpa only [mul_zero] using hinv_log.const_mul _
    · simpa only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using (hinv_log.pow 3).const_mul _
    · simpa only [mul_zero] using ((hrpow_neg (by linarith [hD.ε'_pos])).mul hinv_log).const_mul CC
    · simpa only [mul_zero] using (hrpow_neg (by linarith [hlev_lt k (Finset.mem_range.1 hk)])).const_mul _
  obtain ⟨qE, hqE⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 hTerr).2 ε hε)
  obtain ⟨qV, hqV⟩ := Filter.eventually_atTop.1 ((Finset.eventually_all _).2 fun k hk =>
    ((tendsto_rpow_atTop (hlev_pos k (Finset.mem_range.1 hk))).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop V₀)
  obtain ⟨qβ, hqβ⟩ := Filter.eventually_atTop.1 (hlog_top.eventually_ge_atTop (2 * ∑ δ ∈ D.Δ, δ))
  refine ⟨max (max qE qV) (max qβ 2), fun q hq T hT hTq ι _ E hγ hΔ hinj a ha N => ?_⟩
  classical
  have hq2 : 2 ≤ q := by omega
  have hℓ := log_q_pos hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hδ (j : ι) : 0 ≤ E.δ j := hD.Δ_nonneg _ (hΔ j)
  by_cases hH : ∃ k < D.m, D.h k ≠ 0
  swap
  · have hH' (k : ℕ) (hk : k < D.m) : D.h k = 0 := by by_contra h; exact hH ⟨k, hk, h⟩
    have hS0 (u : ℝ) : D.sieveH u = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hH' k (Finset.mem_range.1 hk)]; simp
    have hD0 (δ : ℝ) : sieveDiag D δ = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hH' k (Finset.mem_range.1 hk)]; simp
    simp only [hS0, hD0, mul_zero, zero_mul, Finset.sum_const_zero, zero_div, zero_add]
    positivity
  have hinj' := hinj hH
  have hβ (j j' : ι) : (E.δ j + E.δ j') / Real.log q ≤ 1 := by
    rw [div_le_one hℓ]
    linarith [Finset.single_le_sum hD.Δ_nonneg (hΔ j),
      Finset.single_le_sum hD.Δ_nonneg (hΔ j'), hqβ q (by omega)]
  have hτ (j j' : ι) : |E.γ j - E.γ j'| ≤ Real.log q := by
    linarith [abs_sub (E.γ j) (E.γ j'), hγ j, hγ j']
  have hsieve_cells : ∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 =
      ∑ k ∈ Finset.range D.m, D.h k * ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)), Λ n / n * ‖Yn E a n‖ ^ 2 := by
    unfold NearData.sieveH
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => by
      rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun n _ => by split_ifs <;> ring
  rw [hsieve_cells]
  have hyc (j : ι) (n : ℕ) : ‖ycomp E a j n‖ ≤ a j * Real.exp (-(E.δ j) * tn q n) := by
    unfold ycomp
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j),
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_right (Real.exp_pos _).le (DirichletCharacter.norm_le_one _ _)) (ha j)
  have hY (n : ℕ) : ‖Yn E a n‖ ^ 2 ≤ (∑ j, a j) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)) 2
    exact (hyc j n).trans (mul_le_of_le_one_right (ha j)
      (Real.exp_le_one_iff.2 (by nlinarith [hδ j, tn_nonneg q n hq2])))
  set main : ℕ → ℝ := fun k => (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)
  set err1 : ℕ → ℝ := fun k => CB * D.t (k + 1) ^ 2 / (D.level k ^ 2 * Real.log q) +
    CB / (D.level k ^ 2 * Real.log q ^ 3)
  set Dk : ℕ → ℝ := fun k => Real.log q * main k +
    CB * (D.t (k + 1) ^ 2 * Real.log q ^ 2 + 1) / (D.level k ^ 2 * Real.log q ^ 2) with hDk
  set Pk : ℕ → ℝ := fun k => 2 * (q : ℝ) ^ D.level k * (D.level k * Real.log q) /
    (q : ℝ) ^ D.t k with hPk
  set O : ℝ := CC * (q : ℝ) ^ (-(D.ε' / 6))
  have hcell (k : ℕ) (hk : k ∈ Finset.range D.m) :
      D.h k * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)),
        Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      D.h k * (∑ j, Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 +
        (O + Pk k) * (∑ j, a j) ^ 2) := by
    have hk' := Finset.mem_range.1 hk
    refine mul_le_mul_of_nonneg_left ?_ (hD.h_nonneg k hk')
    set A : ℝ := (q : ℝ) ^ D.t k
    set B : ℝ := (q : ℝ) ^ D.t (k + 1)
    set C := Finset.Ico ⌈A⌉₊ ⌈B⌉₊
    have hsub : (Finset.Icc 1 N).filter (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)) ⊆ C := fun n hn => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn
      obtain ⟨⟨hn1, -⟩, ht, ht'⟩ := hn
      exact Finset.mem_Ico.2 ⟨Nat.ceil_le.2 ((rpow_le_natCast_iff_tn hq2 hn1 _).2 ht),
        Nat.lt_ceil.2 (not_le.1 fun h => not_le.2 ht' ((rpow_le_natCast_iff_tn hq2 hn1 _).1 h))⟩
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg n.cast_nonneg) (sq_nonneg _)).trans ?_
    have htk_lt := hD.t_lt k hk'
    have hlev := hlev_pos k hk'
    set V : ℝ := (q : ℝ) ^ D.level k
    have hVpos : 1 < V := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by omega)) hlev
    have hVA : V ≤ A := Real.rpow_le_rpow_of_exponent_le hq1 (hlev_lt k hk').le
    have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le hq1 htk_lt.le
    have hA1 : 1 ≤ A := Real.one_le_rpow hq1 (by linarith [hlev_lt k hk'])
    have hlogV : Real.log V = D.level k * Real.log q := Real.log_rpow hq0 _
    have hlogA : Real.log A = D.t k * Real.log q := Real.log_rpow hq0 _
    have hlogB : Real.log B = D.t (k + 1) * Real.log q := Real.log_rpow hq0 _
    have hmem (n : ℕ) (hn : n ∈ C) : 1 ≤ n ∧ D.t k ≤ tn q n := by
      have h1 : 1 ≤ n := by
        have : 0 < ⌈A⌉₊ := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hq0 _)
        have := (Finset.mem_Ico.1 hn).1; omega
      exact ⟨h1, (rpow_le_natCast_iff_tn hq2 h1 _).1 (Nat.ceil_le.1 (Finset.mem_Ico.1 hn).1)⟩
    let pp (n : ℕ) : ℝ := if IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V then Λ n / n else 0
    have step1 : ∑ n ∈ C, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
        ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 +
          ∑ n ∈ C, pp n * ‖Yn E a n‖ ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun n hn => ?_
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (hmem n hn).1
      rw [← add_mul]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      dsimp [pp]
      have hprod : 0 ≤ Real.log n / n * sieveNu V n :=
        mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) hnpos.le) (sq_nonneg _)
      by_cases hpp : IsPrimePow n
      · by_cases hmin : ((Nat.minFac n : ℕ) : ℝ) ≤ V
        · rw [ite_eq_left ⟨hpp, hmin⟩]; linarith
        · rw [ite_eq_right fun h => hmin h.2, add_zero]
          have hsum : ∑ d ∈ n.divisors, grahamWeight V d = 1 := by
            rw [Finset.sum_eq_single 1]
            · simp [grahamWeight, hVpos.le, (Real.log_pos hVpos).ne']
            · intro d hd hd1
              have hdpos := Nat.pos_of_mem_divisors hd
              have hle : ((Nat.minFac n : ℕ) : ℝ) ≤ d := by
                exact_mod_cast Nat.minFac_le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)
              simp [grahamWeight, show ¬ (d : ℝ) ≤ V by linarith]
            · exact fun h => absurd (Nat.one_mem_divisors.mpr hpp.ne_zero) h
          simp only [sieveNu, hsum, one_pow, mul_one]
          exact div_le_div_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log hnpos.le
      · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, zero_div, ite_eq_right fun h => hpp h.1, add_zero]
        exact hprod
    have step2 : ∑ n ∈ C, pp n * ‖Yn E a n‖ ^ 2 ≤ Pk k * (∑ j, a j) ^ 2 := by
      refine (Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_left (hY n)
        (by dsimp [pp]; split_ifs <;> positivity)).trans ?_
      rw [← Finset.sum_mul, ← Finset.sum_filter]
      exact mul_le_mul_of_nonneg_right (by dsimp [Pk, V, A]; rw [← hlogV]; exact small_primepow_sum hVpos.le hA1) (sq_nonneg _)
    have hdiag : ∑ n ∈ C, Real.log n / n * sieveNu V n ≤ Dk k := by
      refine (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.Icc ⌈A⌉₊ ⌊B⌋₊)
        (fun n hn => Finset.mem_Icc.2 ⟨(Finset.mem_Ico.1 hn).1, Nat.le_floor (Nat.lt_ceil.1 (Finset.mem_Ico.1 hn).2).le⟩)
        (fun n _ _ => mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) n.cast_nonneg) (sieveNu_nonneg V n))).trans
        ((hdiagG V A B (hqV q (by omega) k hk) hVA hAB).trans_eq ?_)
      rw [hlogV, hlogA, hlogB]
      have := (mul_pos hlev hℓ).ne'
      dsimp [Dk, main]; field_simp
    have hdiagj (j : ι) : ∑ n ∈ C, sieveNu V n *
        (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j n)).re) ≤
        Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 := by
      refine (Finset.sum_le_sum fun n hn => ?_).trans
        ((Finset.sum_mul _ _ (a j ^ 2 * Real.exp (-2 * E.δ j * D.t k))).symm.le.trans
          ((mul_le_mul_of_nonneg_right hdiag (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)).trans_eq (by ring)))
      have hself : (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j n)).re ≤
          a j ^ 2 * Real.exp (-2 * E.δ j * D.t k) := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
        have h4 : ‖ycomp E a j n‖ ≤ a j * Real.exp (-(E.δ j) * D.t k) :=
          (hyc j n).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hδ j, (hmem n hn).2])) (ha j))
        refine (pow_le_pow_left₀ (norm_nonneg _) h4 2).trans_eq ?_
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
      have hlog : 0 ≤ Real.log n / n := div_nonneg (Real.log_natCast_nonneg n) n.cast_nonneg
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hself hlog) (sieveNu_nonneg V n)).trans_eq (by ring)
    have hoffj (j j' : ι) (hjj' : j ≠ j') : ∑ n ∈ C, sieveNu V n *
        (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) ≤
        a j * a j' * O := by
      have hrw (n : ℕ) (hn : n ∈ C) : sieveNu V n *
          (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) =
          a j * a j' * ((sieveNu V n : ℂ) * (E.χ j * (E.χ j')⁻¹) n * (Real.log n : ℂ) *
            (n : ℂ) ^ (-(((1 + (E.δ j + E.δ j') / Real.log q : ℝ) : ℂ) +
              ((E.γ j - E.γ j' : ℝ) : ℂ) * I))).re := by
        have hn1 := (hmem n hn).1
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
        have := hℓ.ne'
        rw [ycomp_mul_conj, natCast_cpow_neg (by omega),
          show Real.exp (-(1 + (E.δ j + E.δ j') / Real.log q) * Real.log n) =
            (1 / n) * Real.exp (-(E.δ j + E.δ j') * tn q n) by
            rw [one_div, ← Real.exp_log hnpos, ← Real.exp_neg, Real.exp_log hnpos, ← Real.exp_add]
            congr 1; unfold tn; field_simp; ring,
          Complex.re_ofReal_mul,
          show (sieveNu V n : ℂ) * (E.χ j * (E.χ j')⁻¹) n * (Real.log n : ℂ) *
            (((1 / n * Real.exp (-(E.δ j + E.δ j') * tn q n) : ℝ) : ℂ) *
              cexp (-(((E.γ j - E.γ j') * Real.log n : ℝ) : ℂ) * I)) =
            ((sieveNu V n * (Real.log n * (1 / n * Real.exp (-(E.δ j + E.δ j') * tn q n))) : ℝ) : ℂ) *
              ((E.χ j * (E.χ j')⁻¹) n * cexp (-(((E.γ j - E.γ j') * Real.log n : ℝ) : ℂ) * I)) by
            push_cast; ring,
          Complex.re_ofReal_mul]
        ring
      rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, ← Complex.re_sum]
      have hψ : E.χ j * (E.χ j')⁻¹ ≠ 1 := fun h => hjj' (hinj' (mul_inv_eq_one.1 h))
      have hb := hoffC hq2 _ hψ (D.t k) (D.t (k + 1)) ((E.δ j + E.δ j') / Real.log q)
        (E.γ j - E.γ j') (ht0k k hk') htk_lt.le (t_mono_le D hD (by omega) le_rfl)
        (div_nonneg (add_nonneg (hδ j) (hδ j')) hℓ.le) (hβ j j') (hτ j j')
      have hV' : (q : ℝ) ^ ((D.t k - 1 / 3) / 2 - D.ε') = V := rfl
      rw [hV'] at hb
      exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans hb) (mul_nonneg (ha j) (ha j'))
    have hexpand : ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 =
        ∑ j, ∑ j', ∑ n ∈ C, sieveNu V n *
          (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) := by
      simp_rw [norm_Yn_sq, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun n _ => by ring
    have step3 : ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 ≤
        ∑ j, Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 + O * (∑ j, a j) ^ 2 := by
      rw [hexpand]
      refine (Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ =>
        show _ ≤ (if j' = j then Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 else 0) + a j * a j' * O by
          by_cases h : j' = j
          · subst h; rw [ite_eq_left rfl]; nlinarith [hdiagj j', mul_nonneg (ha j') (ha j'), show 0 ≤ O by positivity]
          · rw [ite_eq_right h, zero_add]; exact hoffj j j' (Ne.symm h)).trans (le_of_eq ?_)
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_ite_eq' Finset.univ j]; simp
      · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j' _ => by ring
    linarith [step1, step2, step3]
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum hcell) hℓ.le).trans ?_
  have hA2 : ∑ j, a j ^ 2 ≤ (∑ j, a j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_le_sum fun j _ => by
      simpa [sq] using Finset.single_le_sum (f := fun j' => a j * a j')
        (fun j' _ => mul_nonneg (ha j) (ha j')) (Finset.mem_univ j)
  set e : ι → ℕ → ℝ := fun j k => Real.exp (-2 * E.δ j * D.t k)
  have hk_eq (k : ℕ) (hk : k ∈ Finset.range D.m) :
      D.h k * (∑ j, e j k * Dk k * a j ^ 2 + (O + Pk k) * (∑ j, a j) ^ 2) / Real.log q =
        (∑ j, D.h k * e j k * main k * a j ^ 2) + (∑ j, D.h k * e j k * err1 k * a j ^ 2) +
          D.h k * ((O + Pk k) / Real.log q) * (∑ j, a j) ^ 2 := by
    have hl := (hlev_pos k (Finset.mem_range.1 hk)).ne'
    have hDk' : Dk k = Real.log q * (main k + err1 k) := by
      dsimp [Dk, main, err1]; field_simp
    have e1 : D.h k * (∑ j, e j k * Dk k * a j ^ 2) / Real.log q =
        ∑ j, D.h k * e j k * main k * a j ^ 2 + ∑ j, D.h k * e j k * err1 k * a j ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [hDk']; field_simp
    rw [mul_add, add_div, e1]; ring
  rw [Finset.sum_div, Finset.sum_congr rfl hk_eq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hmain : ∑ k ∈ Finset.range D.m, ∑ j, D.h k * e j k * main k * a j ^ 2 =
      ∑ j, sieveDiag D (E.δ j) * a j ^ 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold sieveDiag
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by dsimp [e, main]; ring
  have herr_le : ∑ k ∈ Finset.range D.m, ∑ j, D.h k * e j k * err1 k * a j ^ 2 ≤
      (∑ k ∈ Finset.range D.m, D.h k * err1 k) * (∑ j, a j) ^ 2 := by
    rw [Finset.sum_comm]
    have h1 (j : ι) : ∑ k ∈ Finset.range D.m, D.h k * e j k * err1 k * a j ^ 2 ≤
        (∑ k ∈ Finset.range D.m, D.h k * err1 k) * a j ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hk' := Finset.mem_range.1 hk
      have he1 : e j k ≤ 1 := Real.exp_le_one_iff.2 (by
        have : 0 < D.t k := by linarith [ht0k k hk', hD.ε'_pos]
        nlinarith [hδ j])
      have herr0 : 0 ≤ err1 k := by have := hlev_pos k hk'; dsimp [err1]; positivity
      nlinarith [mul_le_mul_of_nonneg_left he1 (mul_nonneg (hD.h_nonneg k hk') herr0)]
    refine (Finset.sum_le_sum fun j _ => h1 j).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hA2 (Finset.sum_nonneg fun k hk => by
      have hk' := Finset.mem_range.1 hk; have := hlev_pos k hk'; dsimp [err1]
      exact mul_nonneg (hD.h_nonneg k hk') (by positivity))
  have herr : (∑ k ∈ Finset.range D.m, D.h k * err1 k) +
      ∑ k ∈ Finset.range D.m, D.h k * ((O + Pk k) / Real.log q) ≤ ε := by
    rw [← Finset.sum_add_distrib]
    refine (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)).trans (hqE q (by omega)).le
    dsimp [err1, O, Pk]
    rw [add_div, show 2 * (q : ℝ) ^ D.level k * (D.level k * Real.log q) / (q : ℝ) ^ D.t k / Real.log q =
      2 * D.level k * (q : ℝ) ^ (-(D.t k - D.level k)) by
        rw [show -(D.t k - D.level k) = D.level k - D.t k by ring, Real.rpow_sub hq0]; field_simp]
    ring
  rw [hmain, ← Finset.sum_mul]
  nlinarith [mul_le_mul_of_nonneg_right herr (sq_nonneg (∑ j, a j))]

end
open Complex Filter Topology NearData

theorem graded_near_lemma
    (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
    (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid) {η : ℝ} (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
          (max 0 (∑ j, a j * response D E j)) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2) := by
  have hIB := hD.IB_pos
  obtain ⟨qF, hqF⟩ := first_factor_bound D hD (ε := η * D.IB) (mul_pos hη hIB)
  obtain ⟨qG, hqG⟩ := gram_form_bound hX31 hX32 D hD (ε := η / 2) (half_pos hη)
  obtain ⟨qS, hqS⟩ := sieve_part_bound hGr (burgessBound_of_primitive hBur) D hD (ε := η / 2) (half_pos hη)
  obtain ⟨c, hc, hωc⟩ := hD.omega_lb
  refine ⟨max (max qF qG) (max qS 2), fun q _ hq T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha => ?_⟩
  have hq2 : 2 ≤ q := by omega
  have hℓ := log_q_pos hq2
  set Sf := Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊
  set N := max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊
  set w : ℕ → ℝ := fun n => Λ n / n * D.omega (tn q n) with hw
  let cW (n : ℕ) : ℝ := Λ n / n * Real.exp (D.s * tn q n) * D.f (tn q n)
  have hw0 (n : ℕ) : 0 ≤ w n :=
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg n.cast_nonneg) <|
      add_nonneg (mul_nonneg (hD.g_cond2.nonneg _ (tn_nonneg q n hq2)) (Real.exp_pos _).le) <|
        Finset.sum_nonneg fun k hk => by
          split_ifs
          · exact hD.h_nonneg k (Finset.mem_range.1 hk)
          · exact le_rfl
  have hresp : ∑ j, a j * response D E j =
      -(∑ n ∈ Sf, (cW n : ℂ) * Yn E a n).re / Real.log q := by
    unfold response
    have hrepr (j : ι) : a j * -(primeSum (E.χ j) D.f
        (((1 - (D.s - E.δ j) / Real.log q : ℝ) : ℂ) + (E.γ j : ℂ) * I)).re / Real.log q =
        -((∑ n ∈ Sf, (cW n : ℂ) * ycomp E a j n).re) / Real.log q := by
      rw [primeSum_eq_sum hq2 _ _ hD.f_cond.vanish, mul_neg, ← Complex.re_ofReal_mul, Finset.mul_sum]
      congr 3
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [prime_term D.f (Finset.mem_Icc.1 hn).1, show Real.exp ((D.s - E.δ j) * tn q n) =
        Real.exp (D.s * tn q n) * Real.exp (-(E.δ j) * tn q n) by rw [← Real.exp_add]; ring_nf]
      dsimp [cW, ycomp]; push_cast; ring
    simp_rw [mul_div_assoc', hrepr, ← Finset.sum_div, Finset.sum_neg_distrib, ← Complex.re_sum]
    congr 3; rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun n _ => (Finset.mul_sum _ _ _).symm
  have hcs : (∑ n ∈ Sf, |cW n| * ‖Yn E a n‖) ^ 2 ≤
      (∑ n ∈ Sf, cW n ^ 2 / w n) * (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) := by
    have key (n : ℕ) (hn : n ∈ Sf) :
        |cW n| * ‖Yn E a n‖ = (|cW n| / Real.sqrt (w n)) * (Real.sqrt (w n) * ‖Yn E a n‖) := by
      by_cases hc0 : cW n = 0
      · simp [hc0]
      · have hΛ : Λ n ≠ 0 := fun h => hc0 (by simp [cW, h])
        have hf : D.f (tn q n) ≠ 0 := fun h => hc0 (by simp [cW, h])
        have hwn : 0 < w n := mul_pos (div_pos (lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm hΛ))
          (by exact_mod_cast (Finset.mem_Icc.1 hn).1))
          (lt_of_lt_of_le hc (hωc _ (tn_nonneg q n hq2) hf))
        have hs : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 hwn).ne'
        field_simp
    rw [Finset.sum_congr rfl key]
    refine (Finset.sum_mul_sq_le_sq_mul_sq Sf _ _).trans (le_of_eq ?_)
    congr 1 <;> refine Finset.sum_congr rfl fun n _ => ?_
    · rw [div_pow, sq_abs, Real.sq_sqrt (hw0 n)]
    · rw [mul_pow, Real.sq_sqrt (hw0 n)]
  have hfirst_eq : ∑ n ∈ Sf, cW n ^ 2 / w n = ∑ n ∈ Sf, Λ n / n *
      (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp [cW, w]
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
      by_cases hω : D.omega (tn q n) = 0
      · simp [hω]
      · rw [show Real.exp (2 * D.s * tn q n) = Real.exp (D.s * tn q n) ^ 2 by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring]
        field_simp
  have hfirst : (∑ n ∈ Sf, cW n ^ 2 / w n) / Real.log q ≤ (1 + η) * D.IB := by
    rw [hfirst_eq]; linarith [hqF q (by omega)]
  have hsecond_mono : ∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, w n * ‖Yn E a n‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (le_max_left _ _))
      (fun n _ _ => mul_nonneg (hw0 n) (sq_nonneg _))
  have hsplit : ∑ n ∈ Finset.Icc 1 N, w n * ‖Yn E a n‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
          ‖Yn E a n‖ ^ 2 +
        ∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by simp only [hw, NearData.omega]; ring
  have hgram : ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re := by
    set Sg := Finset.Icc 1 ⌊(q : ℝ) ^ D.xg⌋₊
    have hLHS : ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
          ‖Yn E a n‖ ^ 2 =
        ∑ n ∈ Sg, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 :=
      (Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (le_max_right _ _)) fun n hn hn' => by
        rw [hD.g_cond1.vanish _ (tn_ge_of_gt hq2 (not_le.1 fun h => hn' (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hn).1, h⟩)))]
        simp).symm
    rw [hLHS]
    have hR (j k : ι) : a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re =
        ∑ n ∈ Sg, a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk D E j k) *
          (D.g (tn q n) : ℂ)).re := by
      rw [primeSum_eq_sum hq2 _ _ hD.g_cond1.vanish, Complex.re_sum, Finset.mul_sum]
    simp_rw [hR]
    have hL (n : ℕ) (hn : n ∈ Sg) : Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 =
        ∑ j, ∑ k, a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk D E j k) *
          (D.g (tn q n) : ℂ)).re := by
      rw [norm_Yn_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ycomp_mul_conj, sjk, prime_term D.g (Finset.mem_Icc.1 hn).1,
        Complex.re_ofReal_mul, Complex.re_ofReal_mul,
        show Real.exp ((D.s₁ - E.δ j - E.δ k) * tn q n) =
          Real.exp (D.s₁ * tn q n) * Real.exp (-(E.δ j + E.δ k) * tn q n) by
          rw [← Real.exp_add]; congr 1; ring]
      ring
    rw [Finset.sum_congr rfl hL, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
  have hG := hqG q (by omega) T hT hTq hsafe ι E hγ hΔ a ha
  have hS := hqS q (by omega) T hT hTq ι E hγ hΔ hinj a ha N
  have hsecond : (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q ≤
      ∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
        (D.d₁ + η) * (∑ j, a j) ^ 2 := by
    refine (div_le_div_of_nonneg_right hsecond_mono hℓ.le).trans ?_
    rw [hsplit, add_div, hgram]
    have : ∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 =
        ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by
        change (gramDiag D (E.δ j) + sieveDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 = _; ring
    linarith
  have hsecond0 : 0 ≤ (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q :=
    div_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le
  have hsq : (∑ j, a j * response D E j) ^ 2 ≤
      ((∑ n ∈ Sf, cW n ^ 2 / w n) / Real.log q) *
        ((∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q) := by
    rw [hresp, neg_div, neg_sq, div_pow, div_mul_div_comm, ← sq]
    refine div_le_div_of_nonneg_right ((sq_abs _).symm.le.trans
      ((pow_le_pow_left₀ (abs_nonneg _) ?_ 2).trans hcs)) (sq_nonneg _)
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq
      (Finset.sum_congr rfl fun n _ => ?_)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc (max 0 (∑ j, a j * response D E j)) ^ 2 ≤ (∑ j, a j * response D E j) ^ 2 := by
        rcases le_total 0 (∑ j, a j * response D E j) with h | h <;> simp [h, sq_nonneg]
    _ ≤ _ := hsq
    _ ≤ _ := mul_le_mul hfirst hsecond hsecond0 (by nlinarith)

theorem response_lemma (hX32 : XylourisLemma32) {f : ℝ → ℝ} {x₀ B : ℝ}
    (hf1 : Condition1 f x₀ B) (hf2 : Condition2 f) (σmax : ℝ) (K₀ : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ : ℝ, |σ| ≤ σmax → |γ| ≤ Real.log q →
      ∀ Sz : Finset ℂ,
        (∀ ρ ∈ Sz, DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ) →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ →
          ρ ∉ Sz → (1 - ρ.re) * Real.log q < σ → M ≤ |γ - ρ.im| * Real.log q) →
        (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
            ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ},
          zmult χ ρ) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  have hK1 : (0 : ℝ) < (K₀ : ℝ) + 1 := by positivity
  set ε' : ℝ := η / 2 / ((K₀ : ℝ) + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax hε'pos
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge σmax
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩
  obtain ⟨hsq, -, hq2⟩ := hq₂ q (by omega)
  have hℓ := log_q_pos hq2
  set s : ℂ := (((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I with hs
  have hsre : s.re = 1 - σ / Real.log q := by simp [hs, -natCast_log]
  have hsim : s.im = γ := by simp [hs, -natCast_log]
  have hreg : LemmaRegion q s := by
    refine ⟨?_, by rw [hsim]; exact hγ⟩
    rw [hsre, show 1 - σ / Real.log q - 1 = -(σ / Real.log q) by ring, abs_neg, abs_div,
      abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right (hσ.trans hsq) hℓ.le
  have hX := hq₁ q (by omega) χ hχ s hreg
  set Z : Set ℂ := {ρ : ℂ | ‖(1 + (s.im : ℂ) * I) - ρ‖ ≤ δ ∧
    DirichletCharacter.LFunction χ ρ = 0} with hZ
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ =>
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hZfin : Z.Finite := by
    rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
    · exact absurd (h (Set.mem_univ 2))
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num))
    · refine ((isCompact_closedBall (1 + (s.im : ℂ) * I) δ).finite_sdiff_of_mem_codiscreteWithin
        (Filter.codiscreteWithin_mono (Set.subset_univ _) h)).subset fun ρ ⟨hρ, hL⟩ =>
        ⟨by rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm], by simp [hL]⟩
  have hzs : zeroSum χ f s δ = ∑ ρ ∈ hZfin.toFinset, zmult χ ρ * zeroTerm f q σ γ ρ := by
    unfold zeroSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold zeroTerm; congr 3
    have := hℓ.ne'
    apply Complex.ext <;> simp [hs, -natCast_log]; field_simp; ring
  have hmem (ρ : ℂ) : ρ ∈ hZfin.toFinset ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ := by
    rw [Set.Finite.mem_toFinset, hZ, Set.mem_ofPred_eq, hsim]; exact And.comm
  have hSsub : Sz ⊆ hZfin.toFinset := fun ρ hρ => (hmem ρ).2 (hSz ρ hρ)
  set g : ℂ → ℝ := fun ρ => zmult χ ρ * zeroTerm f q σ γ ρ
  set T := hZfin.toFinset \ Sz with hT
  have hsplit : ∑ ρ ∈ hZfin.toFinset, g ρ = ∑ ρ ∈ Sz, g ρ +
      (∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ +
        ∑ ρ ∈ T.filter (fun ρ => ¬ (1 - ρ.re) * Real.log q < σ), g ρ) := by
    rw [Finset.sum_filter_add_sum_filter_not, hT, add_comm, Finset.sum_sdiff hSsub]
  have hre1 (ρ : ℂ) (hρ : DirichletCharacter.LFunction χ ρ = 0) : ρ.re < 1 := by
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (not_lt.1 h) hρ
  have hgood : 0 ≤ ∑ ρ ∈ T.filter (fun ρ => ¬ (1 - ρ.re) * Real.log q < σ), g ρ :=
    Finset.sum_nonneg fun ρ hρ => mul_nonneg (Nat.cast_nonneg _) <| hf2.re_nonneg _ <| by
      simp [-natCast_log]; linarith [not_lt.1 (Finset.mem_filter.1 hρ).2]
  have hadv_term : ∀ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ),
      -ε' ≤ zeroTerm f q σ γ ρ := by
    intro ρ hρ
    rw [Finset.mem_filter, hT, Finset.mem_sdiff] at hρ
    obtain ⟨⟨hρZ, hρS⟩, hρadv⟩ := hρ
    obtain ⟨hL, hd⟩ := (hmem ρ).1 hρZ
    have hsepρ := hsep ρ hL hd hρS hρadv
    have hr1 := hre1 ρ hL
    have hx : (1 - ρ.re) * Real.log q - σ ∈ Set.Icc (-σmax) σmax := by
      have : 0 ≤ (1 - ρ.re) * Real.log q := mul_nonneg (by linarith) hℓ.le
      exact ⟨by linarith [le_abs_self σ], by linarith [abs_nonneg σ]⟩
    have hY : M ≤ |(γ - ρ.im) * Real.log q| := by rwa [abs_mul, abs_of_pos hℓ]
    have := hdecay _ hx _ hY
    unfold zeroTerm
    linarith [Complex.abs_re_le_norm (laplace f ((((1 - ρ.re) * Real.log q - σ : ℝ)) +
      (((γ - ρ.im) * Real.log q : ℝ) : ℂ) * I)),
      neg_abs_le ((laplace f ((((1 - ρ.re) * Real.log q - σ : ℝ)) +
        (((γ - ρ.im) * Real.log q : ℝ) : ℂ) * I)).re)]
  have hadv_mult : ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), zmult χ ρ ≤ K₀ := by
    have hset : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ} =
        ↑(T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ)) := by
      ext ρ; simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT, Finset.mem_sdiff, hmem]; tauto
    rwa [hset, finsum_mem_coe_finset] at hK
  have hadv : -(η / 2) ≤ ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ := by
    have h1 : (∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), zmult χ ρ) * (-ε') ≤
        ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun ρ hρ => mul_le_mul_of_nonneg_left (hadv_term ρ hρ) (Nat.cast_nonneg _)
    have h2 : (K₀ : ℝ) * ε' ≤ η / 2 := by rw [hε', mul_div_assoc', div_le_iff₀ hK1]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hadv_mult hε'pos.le]
  have hzs' : ∑ ρ ∈ Sz, g ρ - η / 2 ≤ zeroSum χ f s δ := by rw [hzs, hsplit]; linarith
  unfold responseAt
  rw [← hs, le_div_iff₀ hℓ]
  change (∑ ρ ∈ Sz, g ρ - f 0 / 6 - η) * Real.log q ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hzs' hℓ.le]

theorem graded_near_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((D.d₁ + η) / Dn) ∧
              ∑ j, (max 0 (keptBound D E Sz η j / Real.sqrt ((1 + η) * D.IB * Dn) - τ)) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨q₁, hq₁⟩ := graded_near_lemma hX31 hX32 hBur hGr D hD hη
  obtain ⟨M, hM, δ, hδ0, hδ1, q₂, hq₂⟩ :=
    response_lemma hX32 hD.f_cond hf2 (|D.s| + ∑ δ ∈ D.Δ, |δ|) K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK Dn hDn hDj
  have hresp (j : ι) : keptBound D E Sz η j ≤ response D E j := by
    have hσ : |D.s - E.δ j| ≤ |D.s| + ∑ δ ∈ D.Δ, |δ| :=
      (abs_sub _ _).trans (by gcongr; exact Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ j))
    exact hq₂ q (by omega) (E.χ j) (hχ j) (D.s - E.δ j) (E.γ j) hσ (by linarith [hγ j])
      (Sz j) (hSz j) (hsep j) (hK j)
  have hIB := hD.IB_pos
  set N := Real.sqrt ((1 + η) * D.IB * Dn)
  have hNpos : 0 < N := Real.sqrt_pos.2 (by positivity)
  have hN2 : N ^ 2 = (1 + η) * D.IB * Dn := Real.sq_sqrt (by positivity)
  have hd₁ : 0 ≤ D.d₁ := by unfold NearData.d₁; linarith [hD.g_cond2.nonneg 0 le_rfl]
  set v := fun j => keptBound D E Sz η j / N
  set Dg := fun j => (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn
  set d := (D.d₁ + η) / Dn
  have hDg (j : ι) : 0 < Dg j := div_pos (hDj j) hDn
  have hd : 0 < d := div_pos (by linarith) hDn
  let b := d * ∑ i, max 0 (v i) / Dg i
  let f := fun t => d * (∑ i, max 0 (v i - t) / Dg i) - t
  have hb : 0 ≤ b := mul_nonneg hd.le (Finset.sum_nonneg fun i _ => div_nonneg (le_max_left _ _) (hDg i).le)
  have hfb : f b ≤ 0 := by
    have hp : (∑ i, max 0 (v i - b) / Dg i) ≤ ∑ i, max 0 (v i) / Dg i :=
      Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (max_le_max le_rfl (by linarith)) (hDg i).le
    dsimp [f, b]; nlinarith [mul_le_mul_of_nonneg_left hp hd.le]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hb (by dsimp [f]; fun_prop) ⟨hfb, by simpa [f, b] using hb⟩
  let a := fun i => max 0 (v i - t) / Dg i
  have ha (i : ι) : 0 ≤ a i := div_nonneg (le_max_left _ _) (hDg i).le
  have htfix : t = d * ∑ i, a i := by dsimp [f, a] at hft ⊢; linarith
  have hcoord (i : ι) : a i * v i = Dg i * a i ^ 2 + t * a i := by
    have hp : max 0 (v i - t) * (v i - t) = max 0 (v i - t) ^ 2 := by
      rcases le_total 0 (v i - t) with h | h <;> simp [h, sq]
    have := (hDg i).ne'
    dsimp [a]; field_simp; nlinarith
  have hdot : ∑ i, a i * v i = ∑ i, Dg i * a i ^ 2 + d * (∑ i, a i) ^ 2 := by
    simp_rw [hcoord, Finset.sum_add_distrib, ← Finset.mul_sum, htfix]; ring
  have hres : 0 ≤ ∑ i, a i * v i := hdot ▸ add_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (hDg i).le (sq_nonneg _)) (mul_nonneg hd.le (sq_nonneg _))
  have hq' : (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, Dg j * a j ^ 2 + d * (∑ j, a j) ^ 2 := by
    have hmain := hq₁ q (by omega) T hT0 hTl hsafe ι E hχ hγ hΔ hinj a ha
    have h1 : max 0 (∑ j, a j * v j) = max 0 (∑ j, a j * keptBound D E Sz η j) / N := by
      rw [← max_div_div_right hNpos.le, zero_div, Finset.sum_div]
      simp_rw [v, mul_div_assoc]
    have h4 : (max 0 (∑ j, a j * keptBound D E Sz η j)) ^ 2 ≤
        (max 0 (∑ j, a j * response D E j)) ^ 2 :=
      pow_le_pow_left₀ (le_max_left _ _) (max_le_max le_rfl
        (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hresp j) (ha j))) 2
    have h5 : ∑ j, Dg j * a j ^ 2 + d * (∑ j, a j) ^ 2 =
        (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
          (D.d₁ + η) * (∑ j, a j) ^ 2) / Dn := by
      dsimp [Dg, d]
      rw [eq_div_iff hDn.ne', add_mul, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun j _ => by field_simp
      · field_simp
    rw [h1, div_pow, hN2, h5, div_le_div_iff₀ (by positivity) hDn]
    nlinarith [mul_le_mul_of_nonneg_right (h4.trans hmain) hDn.le]
  rw [max_eq_right hres, ← hdot] at hq'
  have hcost : t ^ 2 / d + ∑ i, max 0 (v i - t) ^ 2 / Dg i = ∑ i, a i * v i := by
    have he (i : ι) : max 0 (v i - t) ^ 2 / Dg i = Dg i * a i ^ 2 := by
      have := (hDg i).ne'; dsimp [a]; field_simp
    have := hd.ne'
    simp_rw [he]; rw [hdot, htfix]; field_simp; ring
  have hsum : 0 ≤ ∑ i, max 0 (v i - t) ^ 2 / Dg i :=
    Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hDg i).le
  refine ⟨t, ht.1, Real.le_sqrt_of_sq_le ((div_le_one hd).1 (by nlinarith)), ?_⟩
  change ∑ i, max 0 (v i - t) ^ 2 / Dg i ≤ 1 - t ^ 2 / d
  nlinarith

private lemma LFunction_analyticOrderAt_ne_top {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) (ρ : ℂ) : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
  AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z _ ↦ (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)
    isPreconnected_univ (Set.mem_univ 2) (Set.mem_univ ρ) <| by
    rw [analyticOrderAt_eq_zero.2 (Or.inr
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num)))]
    exact ENat.zero_ne_top

private lemma one_le_zmult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have hne : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨(DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ, hρ⟩
  unfold zmult
  exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h =>
    hne (by rw [← Nat.cast_analyticOrderNatAt (LFunction_analyticOrderAt_ne_top hχ ρ), h]; rfl)

private lemma zeroTerm_at_height_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) {q : ℕ} {σ γ hi : ℝ} {ρ : ℂ} (hγ : ρ.im = γ)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  have hreal (x : ℝ) : (laplace f (x : ℂ)).re = ∫ t in (0 : ℝ)..x₀, f t * Real.exp (-(x * t)) := by
    rw [laplace_eq_intervalIntegral hf]
    have (t : ℝ) : (f t : ℂ) * Complex.exp (-((x : ℂ) * t)) =
        ((f t * Real.exp (-(x * t)) : ℝ) : ℂ) := by push_cast; ring_nf
    simp_rw [this, intervalIntegral.integral_ofReal, Complex.ofReal_re]
  have hc (z : ℝ) : IntervalIntegrable (fun t => f t * Real.exp (-(z * t))) MeasureTheory.volume 0 x₀ := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hf.pos.le]
    exact (hf.cont.mono Set.Icc_subset_Ici_self).mul (by fun_prop)
  have hterm : zeroTerm f q σ γ ρ = (laplace f (((1 - ρ.re) * Real.log q - σ : ℝ) : ℂ)).re := by
    unfold zeroTerm; rw [hγ, sub_self, zero_mul, ofReal_zero, zero_mul, add_zero]
  rw [hterm, hreal, hreal]
  exact ⟨intervalIntegral.integral_mono_on hf.pos.le (hc _) (hc _) fun t ht =>
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [ht.1])) (hf2.nonneg t ht.1),
    intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
      mul_nonneg (hf2.nonneg t ht.1) (Real.exp_pos _).le⟩

section
variable {q : ℕ} {ι : Type*}

theorem keptBound_single [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith [one_le_zmult hχ hρ]

theorem keptBound_pair [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : D.s - E.δ j ≤ (1 - ρ'.re) * Real.log q) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have h2 : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' :=
    hf2.re_nonneg _ (by simp [-natCast_log]; linarith)
  nlinarith [one_le_zmult hχ hρ, one_le_zmult hχ hρ']

theorem single_zero_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ j‖ ≤ δ ∧ (1 - (ρ j).re) * Real.log q ≤ hi j) →
          (∀ j, ∀ ρ' : ℂ, DirichletCharacter.LFunction (E.χ j) ρ' = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ → ρ' ≠ ρ j →
            (1 - ρ'.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ'.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ' ∈ {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ ∧ ρ' ≠ ρ j ∧
              (1 - ρ'.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ') ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((D.d₁ + η) / Dn) ∧
              ∑ j, (max 0 (((laplace D.f ((hi j - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η) /
                  Real.sqrt ((1 + η) * D.IB * Dn) - τ)) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj ρ hi hρ hsep hK Dn hDn hDj
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj (fun j => {ρ j})
    (fun j ρ' hρ' => by rw [Finset.mem_singleton] at hρ'; subst hρ'; exact ⟨(hρ j).1, (hρ j).2.2.1⟩)
    (fun j ρ' h1 h2 h3 h4 => hsep j ρ' h1 h2 (by simpa using h3) h4)
    (fun j => by simpa only [Finset.mem_singleton] using hK j) Dn hDn hDj
  refine ⟨τ, hτ0, hτd, (Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (le_max_left _ _) (max_le_max le_rfl ?_) 2) (div_pos (hDj j) hDn).le).trans hT⟩
  exact sub_le_sub_right (div_le_div_of_nonneg_right
    (keptBound_single D hD hf2 E (fun j => {ρ j}) η j (hχ j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2)
    (Real.sqrt_nonneg _)) _

lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  unfold zeroTerm
  rw [← laplace_re_conj f]
  congr 2; simp [-natCast_log]; ring

theorem keptBound_double [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith

theorem keptBound_pair_neg [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ') :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ 0 := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have hm2 := one_le_zmult hχ hρ'
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ +
      zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ'
  · left; nlinarith [mul_le_mul_of_nonneg_right hm hA0, mul_le_mul_of_nonneg_left hm2 hAB]
  · right; linarith

end

section
variable {q : ℕ} [NeZero q]

theorem zmult_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    zmult χ (conj ρ) = zmult χ ρ := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have heq : (fun z => conj (DirichletCharacter.LFunction χ (conj z))) =
      DirichletCharacter.LFunction χ :=
    (analyticOnNhd_univ_iff_differentiable.2 fun z => differentiableAt_conj_conj_iff.2 (hL _)).eq_of_eventuallyEq
      (analyticOnNhd_univ_iff_differentiable.2 hL) (z₀ := 2) <|
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num)) fun s (hs : 1 < s.re) => by
        change conj (DirichletCharacter.LFunction χ (conj s)) = _
        rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [conj_re]),
          DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries, LSeries, conj_tsum]
        refine tsum_congr fun n => ?_
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
            ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
  have hT : Tendsto (starRingEnd ℂ) (𝓝 (conj ρ)) (𝓝 ρ) := by
    simpa using continuous_conj.tendsto (conj ρ)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (LFunction_analyticOrderAt_ne_top hχ ρ)
  obtain ⟨g, hg, hg0, hfg⟩ := (hL.analyticAt ρ).analyticOrderAt_eq_natCast.mp hn.symm
  have hord : analyticOrderAt (DirichletCharacter.LFunction χ) (conj ρ) = n := by
    rw [(hL.analyticAt _).analyticOrderAt_eq_natCast]
    refine ⟨fun z => conj (g (conj z)), ?_, by simpa using hg0, ?_⟩
    · rw [analyticAt_iff_eventually_differentiableAt] at hg ⊢
      filter_upwards [hT.eventually hg] with z using differentiableAt_conj_conj_iff.mpr
    · filter_upwards [hT.eventually hfg] with z hz
      simpa [← congrFun heq z, smul_eq_mul] using congrArg conj hz
  simp only [zmult, analyticOrderNatAt, hord, ← hn]

variable {ι : Type*}

theorem keptBound_pair_neg_real (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1)
    (hreal : ∀ a : ZMod q, starRingEnd ℂ (E.χ j a) = E.χ j a) {ρ : ℂ} {hi C : ℝ}
    (hne : ρ ≠ starRingEnd ℂ ρ) (hS : Sz j = {ρ, starRingEnd ℂ ρ}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) (starRingEnd ℂ ρ) = 0)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) (starRingEnd ℂ ρ)) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC

end

namespace Cert

open Finset

lemma term_le {v v' D D' τ : ℝ} (hv : v ≤ v' ∨ v ≤ 0) (hτ : 0 ≤ τ) (hD' : 0 < D')
    (hDD : D' ≤ D) : (max 0 (v - τ)) ^ 2 / D ≤ (max 0 (v' - τ)) ^ 2 / D' := by
  rcases hv with hv | hv
  · exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (le_max_left _ _)
      (max_le_max le_rfl (by linarith)) 2) (hD'.le.trans hDD)).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) hD' hDD)
  · rw [max_eq_left (by linarith), sq, zero_mul, zero_div]
    exact div_nonneg (sq_nonneg _) hD'.le

theorem near_row_of_bins (L : Leaf) (k : ℕ) {ι : Type*} [Fintype ι] (v Dg : ι → ℝ) (d τ : ℝ)
    (hDg : ∀ j, 0 < Dg j) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (L.rows.getD k ⟨1, []⟩).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (((L.cols.get c).v.getD k 0 : ℝ) / S ≤ v j ∨ (L.cols.get c).v.getD k 0 ≤ 0) ∧
        Dg j ≤ ((L.cols.get c).D.getD k 1 : ℝ) / S)
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℤ) : ℝ) / S ≤ v j ∨
          ((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 ≤ 0) ∧
        Dg j ≤ ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℤ) : ℝ) / S)
    (hfamD : ∀ i, 0 < ((L.rows.getD k ⟨1, []⟩).fam.get i).2.2)
    (hn : ∀ i, ((((L.rows.getD k ⟨1, []⟩).fam.get i).1 : ℤ) : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < (L.cols.get c).v.getD k 0 →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  have hS : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  refine ⟨hτ0, (Real.sq_sqrt hd.le ▸ pow_le_pow_left₀ hτ0 hτd 2).trans hdrow, ?_⟩
  set t : ι → ℝ := fun j => (max 0 (v j - τ)) ^ 2 / Dg j
  have ht0 (j : ι) : 0 ≤ t j := div_nonneg (sq_nonneg _) (hDg j).le
  have hsplit : ∑ j, t j =
      ∑ j ∈ univ.filter (fun j => bin j = none), t j +
        (∑ c, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j +
          ∑ i, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inr i)), t j) := by
    rw [← Finset.sum_fiberwise univ bin t, Fintype.sum_option, Fintype.sum_sum_type]
  have hcols : ∑ c, x c * (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
          (((L.cols.get c).D.getD k 1 : ℝ) / S) ≤
      ∑ c, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j := by
    refine Finset.sum_le_sum fun c _ => ?_
    set Fc := univ.filter fun j => bin j = some (Sum.inl c)
    have hsum0 : 0 ≤ ∑ j ∈ Fc, t j := Finset.sum_nonneg fun j _ => ht0 j
    by_cases hv : (L.cols.get c).v.getD k 0 ≤ 0
    · rw [max_eq_left (sub_nonpos.2 ((div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hv) hS.le).trans hτ0)),
        sq, zero_mul, mul_zero, zero_div]
      exact hsum0
    · have hxc := hx c (lt_of_not_ge hv)
      rcases Fc.eq_empty_or_nonempty with he | ⟨j₀, hj₀⟩
      · rw [le_antisymm (by simpa [Fc, he] using hxc) (hx0 c), zero_mul, zero_div]
        exact hsum0
      · have htc : 0 ≤ (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
            (((L.cols.get c).D.getD k 1 : ℝ) / S) :=
          div_nonneg (sq_nonneg _) ((hDg j₀).le.trans (hcol j₀ c (Finset.mem_filter.1 hj₀).2).2)
        rw [mul_div_assoc]
        refine (mul_le_mul_of_nonneg_right hxc htc).trans ?_
        rw [← nsmul_eq_mul, ← Finset.sum_const]
        exact Finset.sum_le_sum fun j hj =>
          let ⟨hv, hD⟩ := hcol j c (Finset.mem_filter.1 hj).2
          term_le (hv.imp_right fun h => div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hS.le)
            hτ0 (hDg j) hD
  have hfams : (((L.rows.getD k ⟨1, []⟩).fam).map fun u =>
        (u.1 : ℝ) * (max 0 ((u.2.1 : ℝ) / S - τ)) ^ 2 / ((u.2.2 : ℝ) / S)).sum ≤
      ∑ i, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inr i)), t j := by
    rw [← Fin.sum_univ_fun_getElem]
    refine Finset.sum_le_sum fun i _ => ?_
    have hget : (L.rows.getD k ⟨1, []⟩).fam[i.1] = (L.rows.getD k ⟨1, []⟩).fam.get i := rfl
    rw [hget, mul_div_assoc]
    refine (mul_le_mul_of_nonneg_right (hn i)
      (div_nonneg (sq_nonneg _) (div_pos (by exact_mod_cast hfamD i) hS).le)).trans ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun j hj =>
      let ⟨hv, hD⟩ := hfam j i (Finset.mem_filter.1 hj).2
      term_le (hv.imp_right fun h => div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h) hS.le)
        hτ0 (hDg j) hD
  unfold rowLHS
  linarith [div_le_div_of_nonneg_left (sq_nonneg τ) hd hdrow,
    Finset.sum_nonneg (s := univ.filter fun j => bin j = none) fun j _ => ht0 j]

def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) *
      x j ≤ ((rowBudget (L.rows.getD k ⟨1, []⟩) a b c : ℤ) : ℝ)

lemma cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a hb.ne'

lemma wf_col {L : Leaf} (hwf : wellFormed L = true) (j : Fin L.cols.length) :
    ((L.cols.get j).v.length = L.rows.length ∧ (L.cols.get j).D.length = L.rows.length) ∧
      ∀ k, 0 < (L.cols.get j).D.getD k 1 := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have h := hwf.1 _ (List.get_mem L.cols j)
  refine ⟨h.1, fun k => ?_⟩
  rw [List.getD_eq_getElem?_getD]
  cases hk : (L.cols.get j).D[k]? <;> [simp; exact h.2 _ (List.mem_of_getElem? hk)]

lemma wf_row {L : Leaf} (hwf : wellFormed L = true) (k : ℕ) :
    0 < (L.rows.getD k ⟨1, []⟩).d ∧ ∀ t ∈ (L.rows.getD k ⟨1, []⟩).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  rw [List.getD_eq_getElem?_getD]
  cases h : L.rows[k]? with
  | none => simp
  | some r => simpa using hwf.2 r (List.mem_of_getElem? h)

lemma list_sum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => exact add_le_add (h a (by simp)) (ih fun t ht => h t (by simp [ht]))

lemma list_affine {α : Type*} (l : List α) (g : α → ℝ → ℝ)
    (hg : ∀ i s, g i s = g i 0 + s * (g i 1 - g i 0)) (s : ℝ) :
    (l.map (g · s)).sum = (l.map (g · 0)).sum + s * ((l.map (g · 1)).sum - (l.map (g · 0)).sum) := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, hg a s]; ring

lemma first_le (n v D sh : ℤ) (hn : 0 ≤ n) (hD : 0 < D) {τ : ℝ} (hsh : (S : ℝ) * τ ≤ sh) :
    (((n * (max (v - sh) 0) ^ 2) / D : ℤ) : ℝ) ≤
      S * ((n : ℝ) * (max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hnr : (0 : ℝ) ≤ n := by exact_mod_cast hn
  refine (cast_ediv_le _ _ hD).trans ?_
  push_cast
  have hM : max ((v : ℝ) - sh) 0 ≤ S * max 0 ((v : ℝ) / S - τ) := by
    refine max_le ?_ (mul_nonneg hS.le (le_max_left _ _))
    have e : (S : ℝ) * ((v : ℝ) / S - τ) = v - S * τ := by field_simp
    linarith [mul_le_mul_of_nonneg_left (le_max_right 0 ((v : ℝ) / S - τ)) hS.le]
  calc (n : ℝ) * (max ((v : ℝ) - sh) 0) ^ 2 / D
      ≤ n * (S * max 0 ((v : ℝ) / S - τ)) ^ 2 / D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) hM 2) hnr) hDr.le
    _ = S * ((n : ℝ) * (max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
        rw [div_div_eq_mul_div]; ring

def tgt (w m s : ℝ) : ℝ := (max 0 (w - m)) ^ 2 - 2 * max 0 (w - m) * s

lemma tangent_ineq (w m t : ℝ) : tgt w m (t - m) ≤ (max 0 (w - t)) ^ 2 := by
  unfold tgt
  rcases le_total (w - m) 0 with h1 | h1
  · rw [max_eq_left h1]; nlinarith [sq_nonneg (max 0 (w - t))]
  · rw [max_eq_right h1]
    nlinarith [sq_nonneg (max 0 (w - t) - (w - m)), mul_nonneg h1 (sub_nonneg.2 (le_max_right 0 (w - t)))]

theorem relax_first {L : Leaf} (hwf : wellFormed L = true) {x : Fin L.cols.length → ℝ}
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} {a b : ℤ} (ha : 0 ≤ a) {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 2 := by
  set r := L.rows.getD k ⟨1, []⟩
  obtain ⟨hd, hfam⟩ := wf_row hwf k
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hT : (0 : ℝ) < TS := by norm_num [TS]
  have hsh : (S : ℝ) * τ ≤ ((b * (S / TS) : ℤ) : ℝ) := by
    calc (S : ℝ) * τ = ((S / TS : ℤ) : ℝ) * (τ * TS) := by norm_num [S, TS]; ring
      _ ≤ ((S / TS : ℤ) : ℝ) * b := mul_le_mul_of_nonneg_left hτb (by norm_num [S, TS])
      _ = ((b * (S / TS) : ℤ) : ℝ) := by push_cast; ring
  have hcols : ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b 2 :
      ℤ) : ℝ) * x j ≤ S * ∑ j, x j * (max 0 (((L.cols.get j).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
        (((L.cols.get j).D.getD k 1 : ℝ) / S) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := first_le 1 ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) _
      zero_le_one ((wf_col hwf j).2 k) hsh
    simp only [one_mul, Int.cast_one] at h
    rw [colCost, ite_eq_left rfl]
    exact (mul_le_mul_of_nonneg_right h (hx j)).trans_eq (by ring)
  have hfamb : (((r.fam.map fun t =>
      (t.1 * (max (t.2.1 - b * (S / TS)) 0) ^ 2) / t.2.2).sum : ℤ) : ℝ) ≤
      S * ((r.fam.map fun t =>
        (t.1 : ℝ) * (max 0 ((t.2.1 : ℝ) / S - τ)) ^ 2 / ((t.2.2 : ℝ) / S)).sum) := by
    rw [Int.cast_list_sum, List.map_map, ← List.sum_map_mul_left]
    refine list_sum_le _ _ _ fun t ht => ?_
    dsimp only [Function.comp_apply]
    exact first_le t.1 t.2.1 t.2.2 _ (hfam t ht).1 (hfam t ht).2 hsh
  have hquad : (((S * S * a * a) / (TS * TS * r.d) : ℤ) : ℝ) ≤ S * (τ ^ 2 / ((r.d : ℝ) / S)) := by
    have hdr : (0 : ℝ) < r.d := by exact_mod_cast hd
    have hTi : (0 : ℤ) < TS := by norm_num [TS]
    refine (cast_ediv_le _ _ (mul_pos (mul_pos hTi hTi) hd)).trans ?_
    have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have h1 : (a : ℝ) * a ≤ (τ * TS) * (τ * TS) := mul_self_le_mul_self har hτa
    push_cast
    rw [div_le_iff₀ (mul_pos (mul_pos hT hT) hdr)]
    have hS0 : (S : ℝ) ≠ 0 := hS.ne'
    have hd0 : (r.d : ℝ) ≠ 0 := hdr.ne'
    rw [show (S : ℝ) * (τ ^ 2 / ((r.d : ℝ) / S)) * (TS * TS * r.d) = S * S * ((τ * TS) * (τ * TS)) by field_simp]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hS.le hS.le)]
  have key := mul_le_mul_of_nonneg_left hrow hS.le
  unfold rowLHS at key
  unfold RelaxHolds
  rw [rowBudget, ite_eq_left rfl, Int.cast_sub, Int.cast_sub]
  linarith

theorem relax_tangent {L : Leaf} (hwf : wellFormed L = true) {x : Fin L.cols.length → ℝ}
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} {a b : ℤ} {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1 := by
  have hT : (0 : ℝ) < TS := by norm_num [TS]
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hSi : (0 : ℤ) < S := by norm_num [S]
  set r := L.rows.getD k ⟨1, []⟩
  obtain ⟨hd, hfam⟩ := wf_row hwf k
  set m : ℝ := ((a : ℝ) + b) / (2 * TS)
  set h : ℝ := ((b : ℝ) - a) / (2 * TS)
  let sgn (c : ℕ) : ℝ := (2 * (c : ℝ) - 1) * h
  let colT (s : ℝ) : ℝ :=
    ∑ j, x j * tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) m s / (((L.cols.get j).D.getD k 1 : ℝ) / S)
  let famT (s : ℝ) : ℝ :=
    (r.fam.map fun t => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m s / ((t.2.2 : ℝ) / S)).sum
  let quadT (s : ℝ) : ℝ := (m ^ 2 + 2 * m * s) / ((r.d : ℝ) / S)
  let tline (s : ℝ) : ℝ := colT s + famT s + quadT s
  have hB : tline (τ - m) ≤ rowLHS L x k τ + τ ^ 2 / ((r.d : ℝ) / S) := by
    have h1 : colT (τ - m) ≤ ∑ j, x j * (max 0 (((L.cols.get j).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
        (((L.cols.get j).D.getD k 1 : ℝ) / S) :=
      Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tangent_ineq _ _ _) (hx j))
        (div_pos (by exact_mod_cast (wf_col hwf j).2 k) hS).le
    have h2 : famT (τ - m) ≤ (r.fam.map fun t =>
        (t.1 : ℝ) * (max 0 ((t.2.1 : ℝ) / S - τ)) ^ 2 / ((t.2.2 : ℝ) / S)).sum :=
      list_sum_le _ _ _ fun t ht => div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tangent_ineq _ _ _) (by exact_mod_cast (hfam t ht).1))
        (div_pos (by exact_mod_cast (hfam t ht).2) hS).le
    have h3 : quadT (τ - m) ≤ τ ^ 2 / ((r.d : ℝ) / S) :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (τ - m)])
        (div_pos (by exact_mod_cast hd) hS).le
    dsimp [tline]; unfold rowLHS; linarith
  have haff (s : ℝ) : tline s = tline 0 + s * (tline 1 - tline 0) := by
    have h1 : colT s = colT 0 + s * (colT 1 - colT 0) := by
      dsimp [colT]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [tgt]; ring
    have h2 := list_affine r.fam
      (fun (t : ℤ × ℤ × ℤ) s => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m s / ((t.2.2 : ℝ) / S))
      (fun t s => by simp only [tgt]; ring) s
    have h3 : quadT s = quadT 0 + s * (quadT 1 - quadT 0) := by dsimp [quadT]; ring
    dsimp [tline, famT]; linear_combination h1 + h2 + h3
  have h1 : -h ≤ τ - m := by linarith [(div_le_iff₀ hT).2 hτa, show m - h = a / TS by dsimp [m, h]; ring]
  have h2 : τ - m ≤ h := by linarith [(le_div_iff₀ hT).2 hτb, show m + h = b / TS by dsimp [m, h]; ring]
  have hG0 : tline (τ - m) ≤ 1 := by linarith
  rw [haff (τ - m)] at hG0
  obtain ⟨c, hc, hG⟩ : ∃ c, (c = 0 ∨ c = 1) ∧ tline (sgn c) ≤ 1 := by
    rcases le_total 0 (tline 1 - tline 0) with hQ | hQ
    · refine ⟨0, .inl rfl, ?_⟩
      rw [show sgn 0 = -h by dsimp [sgn]; push_cast; ring, haff (-h)]; nlinarith
    · refine ⟨1, .inr rfl, ?_⟩
      rw [show sgn 1 = h by dsimp [sgn]; push_cast; ring, haff h]; nlinarith
  have hrel : RelaxHolds L x k a b c := by
    have hcols : ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c :
        ℤ) : ℝ) * x j ≤ S * colT (sgn c) := by
      dsimp only [colT]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      set v := (L.cols.get j).v.getD k 0
      have hD := (wf_col hwf j).2 k
      have hDr : (0 : ℝ) < (L.cols.get j).D.getD k 1 := by exact_mod_cast hD
      have htcost : ((tangentCost v (a + b) (b - a) c : ℤ) : ℝ) ≤ S * tgt ((v : ℝ) / S) m (sgn c) := by
        unfold tangentCost; dsimp only
        generalize hxi : v - (a + b) * HS = xi
        generalize hhs : (b - a) * HS = hS'
        have hxr : (xi : ℝ) = S * ((v : ℝ) / S - m) := by
          rw [← hxi]; dsimp [m]; simp only [S, TS, HS]; push_cast; ring
        have hhr : (hS' : ℝ) = S * h := by
          rw [← hhs]; dsimp [h]; simp only [S, TS, HS]; push_cast; ring
        by_cases hxi0 : xi ≤ 0
        · rw [ite_eq_left hxi0]
          have h0 : (xi : ℝ) ≤ 0 := by exact_mod_cast hxi0
          simp [tgt, max_eq_left (by nlinarith : (v : ℝ) / S - m ≤ 0)]
        · rw [ite_eq_right hxi0]
          have h0 : (0 : ℝ) < xi := by exact_mod_cast (not_le.mp hxi0)
          rw [tgt, max_eq_right (pos_of_mul_pos_right (hxr ▸ h0) hS.le).le]
          refine (cast_ediv_le _ _ hSi).trans (le_of_eq ?_)
          rcases hc with rfl | rfl <;> [rw [ite_eq_left rfl]; rw [ite_eq_right one_ne_zero]] <;>
            { push_cast; rw [hxr, hhr, div_eq_iff hS.ne']; dsimp [sgn]; push_cast; ring }
      have hcost : ((colCost v ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) ≤
          S * (tgt ((v : ℝ) / S) m (sgn c) / (((L.cols.get j).D.getD k 1 : ℝ) / S)) := by
        rw [colCost, ite_eq_right (by omega)]
        refine (cast_ediv_le _ _ hD).trans ?_
        rw [Int.cast_mul]
        refine (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right htcost hS.le) hDr.le).trans_eq ?_
        rw [div_div_eq_mul_div]; ring
      exact (mul_le_mul_of_nonneg_right hcost (hx j)).trans_eq (by dsimp only [v]; ring)
    have hbud : S * (1 - famT (sgn c) - quadT (sgn c)) ≤ ((rowBudget r a b c : ℤ) : ℝ) := by
      rw [rowBudget, ite_eq_right (by omega)]
      dsimp only
      refine (le_of_eq ?_).trans ((show ∀ q : ℚ, (q : ℝ) ≤ (⌈q⌉ : ℤ) from fun q => by exact_mod_cast Int.le_ceil q) _)
      rw [Rat.cast_mul, Rat.cast_sub, Rat.cast_list_sum, List.map_map,
        List.map_congr_left (g := fun t : ℤ × ℤ × ℤ => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m (sgn c) / ((t.2.2 : ℝ) / S))]
      · dsimp [famT, quadT, m, sgn, h]
        rcases hc with rfl | rfl <;> [rw [ite_eq_left rfl]; rw [ite_eq_right one_ne_zero]] <;>
          { push_cast; ring }
      · intro t _
        dsimp only [Function.comp_apply]
        rw [Rat.cast_div, Rat.cast_mul, Rat.cast_intCast, Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast]
        congr 2
        unfold tangentExact tgt
        dsimp only [m, sgn, h]
        rcases hc with rfl | rfl
        · rw [ite_eq_left rfl]; push_cast; rw [max_comm]; ring
        · rw [ite_eq_right one_ne_zero]
          split_ifs with hpos
          · push_cast; rw [max_comm]; ring
          · have hwm : (t.2.1 : ℚ) / S - (a + b : ℤ) / (2 * TS) ≤ 0 := by
              by_contra hcon; exact hpos (lt_max_of_lt_left (not_le.mp hcon))
            have hwm' : (t.2.1 : ℝ) / S - ((a : ℝ) + b) / (2 * TS) ≤ 0 := by exact_mod_cast hwm
            rw [max_eq_left hwm']; simp
    dsimp [tline] at hG
    unfold RelaxHolds
    exact hcols.trans ((mul_le_mul_of_nonneg_left (by linarith) hS.le).trans hbud)
  rcases hc with rfl | rfl <;> [exact .inl hrel; exact .inr hrel]

theorem getD_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (d : δ) (d1 : α) (d2 : β) (d3 : γ) :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ) (i : ℕ), i < l1.length → i < l2.length →
      i < l3.length →
      (List.zipWith3 f l1 l2 l3).getD i d = f (l1.getD i d1) (l2.getD i d2) (l3.getD i d3)
  | _ :: _, _ :: _, _ :: _, 0, _, _, _ => rfl
  | _ :: xs, _ :: ys, _ :: zs, i + 1, h1, h2, h3 =>
      getD_zipWith3 f d d1 d2 d3 xs ys zs i (by simpa using h1) (by simpa using h2) (by simpa using h3)
  | [], _, _, _, h, _, _ | _ :: _, [], _, _, _, h, _ | _ :: _, _ :: _, [], _, _, _, h =>
      absurd h (Nat.not_lt_zero _)

theorem getD_zip {α β : Type*} (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β) (i : ℕ), i < l1.length → i < l2.length →
      (l1.zip l2).getD i (d1, d2) = (l1.getD i d1, l2.getD i d2)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: xs, _ :: ys, i + 1, h1, h2 => getD_zip d1 d2 xs ys i (by simpa using h1) (by simpa using h2)
  | [], _, _, h, _ | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)

theorem sum_zipWith_zipWith3 {α β γ : Type*} (f : α → β → γ → ℤ) (d1 : α) (d2 : β) (d3 : γ) :
    ∀ (Z : List ℕ) (l1 : List α) (l2 : List β) (l3 : List γ),
      Z.length = l1.length → l2.length = l1.length → l3.length = l1.length →
      (List.zipWith (fun z c => z * c) (Z >>= fun a => pure (a : ℤ) : List ℤ)
        (List.zipWith3 f l1 l2 l3)).sum =
      ∑ k ∈ Finset.range l1.length, ((Z.getD k 0 : ℕ) : ℤ) * f (l1.getD k d1) (l2.getD k d2) (l3.getD k d3)
  | [], [], _, _, _, _, _ => by simp
  | z :: Z, x :: xs, y :: ys, w :: ws, hZ, h2, h3 => by
      change (z : ℤ) * f x y w + (List.zipWith _ (Z >>= _) (List.zipWith3 f xs ys ws)).sum = _
      simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ, List.getD_cons_zero,
        sum_zipWith_zipWith3 f d1 d2 d3 Z xs ys ws (by simpa using hZ) (by simpa using h2) (by simpa using h3)]
      ring
  | _ :: _, [], _, _, h, _, _ | [], _ :: _, _, _, h, _, _
  | _, _ :: _, [], _, _, h, _ | _, _ :: _, _ :: _, [], _, _, h => by simp at h

theorem le_mul_ceilDiv (a : ℤ) {b : ℤ} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv; linarith [Int.ediv_mul_le (-a) hb.ne']

theorem obj_le_of {L : Leaf} {x : Fin L.cols.length → ℝ} {T : ℤ}
    (h : ((DS : ℤ) : ℝ) * ∑ j, ((L.cols.get j).G : ℝ) * x j ≤ (T : ℝ)) :
    objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
  have h2 : (T : ℝ) ≤ (DS : ℝ) * (ceilDiv T DS : ℝ) := by
    exact_mod_cast le_mul_ceilDiv T (by norm_num [DS] : (0 : ℤ) < DS)
  have h3 := le_of_mul_le_mul_left (h.trans h2) (by norm_num [DS] : (0 : ℝ) < (DS : ℝ))
  unfold objective; push_cast; linarith

theorem exists_caseVector (P : ℕ → ℕ → Prop) (os : List ℕ)
    (h : ∀ k < os.length, (os.getD k 0 = 1 → P k 0 ∨ P k 1) ∧ (os.getD k 0 ≠ 1 → P k 2)) :
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0) := by
  induction os generalizing P with
  | nil => exact ⟨[], by simp [caseVectors], rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | cons o os ih =>
    obtain ⟨cs, hcs, hlen, hP⟩ := ih (fun k c => P (k + 1) c)
      (fun k hk => by simpa using h (k + 1) (by simpa using hk))
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hext (c : ℕ) (hc : P 0 c) (k : ℕ) (hk : k < (o :: os).length) : P k ((c :: cs).getD k 0) := by
      cases k <;> [simpa using hc; exact hP _ (by simpa using hk)]
    by_cases ho : o = 1
    · rcases h0.1 ho with hp | hp <;>
        [exact ⟨0 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 0 hp⟩;
         exact ⟨1 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 1 hp⟩]
    · exact ⟨2 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 2 (h0.2 ho)⟩

theorem foldl_some {α : Type*} (f : Option ℤ → α → Option ℤ) (Q : α → ℤ → Prop)
    (hf : ∀ acc a m, f acc a = some m → ∃ m0, acc = some m0 ∧ m0 ≤ m ∧ Q a m)
    (hQ : ∀ a m1 m2, Q a m1 → m1 ≤ m2 → Q a m2) (l : List α) :
    ∀ (init : Option ℤ) (m : ℤ), l.foldl f init = some m →
      (∃ m0, init = some m0 ∧ m0 ≤ m) ∧ ∀ a ∈ l, Q a m := by
  induction l with
  | nil => intro init m h; exact ⟨⟨m, h, le_rfl⟩, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    intro init m h
    obtain ⟨⟨m1, hm1, hm1le⟩, hl⟩ := ih _ _ h
    obtain ⟨m0, hinit, hm0, hQa⟩ := hf _ _ _ hm1
    refine ⟨⟨m0, hinit, hm0.trans hm1le⟩, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hQ _ _ _ hQa hm1le
    · exact hl b hb

theorem getD_set_of_lt {box : List (ℤ × ℤ)} {k : ℕ} (hk : k < box.length) (p : ℤ × ℤ) (i : ℕ) :
    (box.set k p).getD i (0, 0) = if i = k then p else box.getD i (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases hi : i = k <;> [ (subst hi; simp [hk]); simp [Ne.symm hi, hi] ]

theorem checkLeaf_sound {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  have hbox : (rootBox L).length = L.rows.length := by simp [rootBox]
  have hτ : ∀ k < L.rows.length, 0 ≤ ((rootBox L).getD k (0, 0)).1 ∧
      (((rootBox L).getD k (0, 0)).1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ ((rootBox L).getD k (0, 0)).2 := by
    intro k hk
    unfold rootBox
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
    obtain ⟨h0, htd, -⟩ := hfeas.2.2.2.2.2 k hk
    rw [List.getD_eq_getElem _ _ hk] at htd
    refine ⟨le_rfl, by push_cast; exact mul_nonneg h0 (by norm_num [TS]), ?_⟩
    unfold rootEnd
    set d := L.rows[k].d
    set q := d * TS * TS / S
    set r := isqrtUp (q.toNat + 1)
    have hS : (0 : ℤ) < S := by norm_num [S]
    have hSr : (0 : ℝ) < S := by exact_mod_cast hS
    have h1r : (d : ℝ) * TS * TS < ((q : ℝ) + 1) * S := by
      exact_mod_cast Int.lt_ediv_add_one_mul_self (d * TS * TS) hS
    have h2r : (q : ℝ) ≤ (q.toNat : ℝ) := by exact_mod_cast Int.self_le_toNat q
    have h3r : ((q.toNat : ℝ) + 1) ≤ (r : ℝ) * r := by
      exact_mod_cast (by unfold r isqrtUp; split_ifs with hsq <;> [exact hsq.ge; exact (Nat.lt_succ_sqrt _).le] : q.toNat + 1 ≤ r * r)
    have h4 : (τ k) ^ 2 * S ≤ d := (le_div_iff₀ hSr).mp htd
    have h6 : (τ k * TS) ^ 2 < (q : ℝ) + 1 :=
      lt_of_mul_lt_mul_right (by nlinarith [mul_le_mul_of_nonneg_right h4 (sq_nonneg (TS : ℝ))]) hSr.le
    have hr0 : (0 : ℝ) ≤ r := r.cast_nonneg
    have htT : 0 ≤ τ k * TS := mul_nonneg h0 (by norm_num [TS])
    push_cast; nlinarith
  revert val hbox hτ
  generalize rootBox L = box
  induction T generalizing box with
  | split k mid l r ihl ihr =>
    intro m h hlen hτ
    simp only [verifyTree] at h
    split at h
    · rename_i a b hk
      split_ifs at h with hab
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
      have hgk : box.getD k (0, 0) = (a, b) := by rw [List.getD_eq_getElem _ _ hkl, hkv]
      obtain ⟨ha0, hτa, hτb⟩ := hgk ▸ hτ k (hlen ▸ hkl)
      by_cases hmid : τ k * TS ≤ (mid : ℝ)
      · refine (ihl _ h1 (by rw [List.length_set, hlen]) fun i hi => ?_).trans
          (by exact_mod_cast le_max_left _ _)
        rw [getD_set_of_lt hkl]
        split_ifs with hik
        · subst hik; exact ⟨ha0, hτa, hmid⟩
        · exact hτ i hi
      · refine (ihr _ h3 (by rw [List.length_set, hlen]) fun i hi => ?_).trans
          (by exact_mod_cast le_max_right _ _)
        rw [getD_set_of_lt hkl]
        split_ifs with hik
        · subst hik; exact ⟨ha0.trans hab.1.le, (not_le.mp hmid).le, hτb⟩
        · exact hτ i hi
    · simp at h
  | node orders certs =>
    intro m h hbox hτ
    simp only [verifyTree] at h
    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h' with hvS
    cases h'
    unfold checkBox at hv
    dsimp only at hv
    split_ifs at hv with hc
    obtain ⟨hord, hlen, -⟩ := hc
    have key := foldl_some _ (fun (cc : List ℕ × CaseCert) m =>
        excludable L box cc.1 = true ∨ ∃ du v, caseValue L box cc.1 du = some v ∧ v ≤ m)
      (fun acc ⟨cv, cert⟩ m' hf => by
        cases acc with
        | none => simp at hf
        | some m0 =>
          refine ⟨m0, rfl, ?_⟩
          cases cert with
          | excluded =>
            simp only [Option.bind_some] at hf
            split_ifs at hf with hex
            cases hf
            exact ⟨le_rfl, Or.inl hex⟩
          | duals du =>
            simp only [Option.bind_some] at hf
            obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hf
            exact ⟨le_max_left _ _, Or.inr ⟨du, v, hv, le_max_right _ _⟩⟩)
      (fun cc m1 m2 hQ hle => hQ.imp_right fun ⟨du, v, hv, hvle⟩ => ⟨du, v, hv, hvle.trans hle⟩)
      _ _ _ hv
    obtain ⟨hx, hW, hC, hNH, hE, hrows⟩ := hfeas
    obtain ⟨cs, hcs, hcslen, hrel⟩ := exists_caseVector
      (fun k c => RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 c) orders fun k hk => by
        rw [hord] at hk
        obtain ⟨-, -, hr⟩ := hrows k hk
        obtain ⟨hlo, ha, hb⟩ := hτ k hk
        exact ⟨fun _ => relax_tangent hwf hx ha hb hr,
          fun _ => relax_first hwf hx hlo ha hb hr⟩
    rw [hord] at hcslen hrel
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcs
    have hcv := key.2 _ (List.getElem_mem (by simp [hlen, hi] : i < ((caseVectors orders).zip certs).length))
    rw [List.getElem_zip] at hcv
    dsimp only at hcv
    set cs := (caseVectors orders)[i]
    rcases hcv with hex | ⟨du, v, hv', hvm⟩
    · exfalso
      unfold excludable at hex
      obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hex
      rw [List.mem_range] at hk
      rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk'
      obtain ⟨hneg, hcost⟩ := hk'
      unfold budgets at hneg
      rw [getD_zipWith3 _ _ ⟨1, []⟩ (0, 0) 0 _ _ _ k hk (by omega) (by omega)] at hneg
      have hr := hrel k hk
      unfold RelaxHolds at hr
      have hnn : (0 : ℝ) ≤ ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
          (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ) * x j :=
        Finset.sum_nonneg fun j _ => by
          obtain ⟨hvlen, hDlen⟩ := (wf_col hwf j).1
          have h1 := hcost _ (List.get_mem L.cols j)
          rw [decide_eq_true_eq, colCosts,
            getD_zipWith3 _ _ (0, 0) (0, 1) 0 _ _ _ k (by omega)
              (by rw [List.length_zip, hvlen, hDlen, min_self]; omega) (by omega),
            getD_zip 0 1 _ _ k (by omega) (by omega)] at h1
          exact mul_nonneg (by exact_mod_cast h1) (hx j)
      have hneg' : ((rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1 (box.getD k (0, 0)).2
          (cs.getD k 0) : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      linarith
    · refine (?_ : objective L x ≤ v).trans (by exact_mod_cast hvm)
      unfold caseValue at hv'
      split_ifs at hv' with hcond
      obtain ⟨hZ, hcols⟩ := hcond
      obtain rfl := Option.some.inj hv'
      apply obj_le_of
      unfold budgets
      rw [sum_zipWith_zipWith3 _ ⟨1, []⟩ (0, 0) 0 du.Z L.rows box cs hZ hbox hcslen]
      set c := fun (j : Fin L.cols.length) k =>
        ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
          (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ)
      set bud := fun k => ((rowBudget (L.rows.getD k ⟨1, []⟩)
        (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ)
      set z := fun k => ((du.Z.getD k 0 : ℕ) : ℝ)
      have hcol (j : Fin L.cols.length) : ((DS : ℤ) : ℝ) * (L.cols.get j).G ≤
          du.Y * (L.cols.get j).W + du.V * (L.cols.get j).C + du.U * (L.cols.get j).NH +
            ((du.P : ℝ) - du.M) * (L.cols.get j).E + ∑ k ∈ Finset.range L.rows.length, z k * c j k := by
        obtain ⟨hvlen, hDlen⟩ := (wf_col hwf j).1
        have h1 := List.all_eq_true.mp hcols _ (List.get_mem L.cols j)
        rw [decide_eq_true_eq, colCosts, sum_zipWith_zipWith3 _ (0, 0) (0, 1) 0 du.Z box _ cs
          (hZ.trans hbox.symm) (by rw [List.length_zip, hvlen, hDlen, hbox, min_self])
          (hcslen.trans hbox.symm), hbox] at h1
        have h2 : ∑ k ∈ Finset.range L.rows.length,
            ((du.Z.getD k 0 : ℕ) : ℤ) * colCost (((L.cols.get j).v.zip (L.cols.get j).D).getD k (0, 1)).1
              (((L.cols.get j).v.zip (L.cols.get j).D).getD k (0, 1)).2
              (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) =
            ∑ k ∈ Finset.range L.rows.length, ((du.Z.getD k 0 : ℕ) : ℤ) *
              colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
                (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) :=
          Finset.sum_congr rfl fun k hk => by
            have hk' := Finset.mem_range.mp hk
            rw [getD_zip 0 1 _ _ k (by omega) (by omega)]
        rw [h2] at h1
        dsimp only [z, c]
        exact_mod_cast h1
      push_cast
      change ((DS : ℤ) : ℝ) * ∑ j, (L.cols.get j).G * x j ≤
        du.Y * L.F + du.V * (2 * S) + du.U * (L.ng * S) + ((du.P : ℝ) - du.M) * (L.n2 * S) +
          ∑ k ∈ Finset.range L.rows.length, z k * bud k
      generalize ((DS : ℤ) : ℝ) = DSr at hcol ⊢
      generalize (S : ℝ) = Sr at hC hNH hE ⊢
      have h1 : DSr * ∑ j, (L.cols.get j).G * x j ≤
          ∑ j, (du.Y * (L.cols.get j).W + du.V * (L.cols.get j).C + du.U * (L.cols.get j).NH +
            ((du.P : ℝ) - du.M) * (L.cols.get j).E + ∑ k ∈ Finset.range L.rows.length, z k * c j k) * x j := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ => by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hcol j) (hx j)
      have hsplit : ∑ j, (du.Y * (L.cols.get j).W + du.V * (L.cols.get j).C + du.U * (L.cols.get j).NH +
          ((du.P : ℝ) - du.M) * (L.cols.get j).E + ∑ k ∈ Finset.range L.rows.length, z k * c j k) * x j =
          du.Y * ∑ j, (L.cols.get j).W * x j + du.V * ∑ j, (L.cols.get j).C * x j +
            du.U * ∑ j, (L.cols.get j).NH * x j + ((du.P : ℝ) - du.M) * ∑ j, (L.cols.get j).E * x j +
            ∑ k ∈ Finset.range L.rows.length, z k * ∑ j, c j k * x j := by
        simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
      have h2 : ∑ k ∈ Finset.range L.rows.length, z k * ∑ j, c j k * x j ≤
          ∑ k ∈ Finset.range L.rows.length, z k * bud k :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hrel k (Finset.mem_range.mp hk)) (Nat.cast_nonneg _)
      have h3 := mul_le_mul_of_nonneg_left hW (Nat.cast_nonneg du.Y)
      have h4 := mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg du.V)
      have h5 := mul_le_mul_of_nonneg_left hNH (Nat.cast_nonneg du.U)
      rw [hsplit, hE] at h1
      linarith

theorem checkLeaf_lt {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val) :
    val < S := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  revert val
  generalize rootBox L = box
  induction T generalizing box with
  | split k mid l r ihl ihr =>
    intro m h
    simp only [verifyTree] at h
    split at h
    · split_ifs at h
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      exact max_lt (ihl _ h1) (ihr _ h3)
    · simp at h
  | node orders certs =>
    intro m h
    simp only [verifyTree] at h
    obtain ⟨v, _, h'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h' with hvS
    cases h'
    exact hvS

theorem certified {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (by exact_mod_cast checkLeaf_lt h)

end Cert

theorem pairExcess_eq_zero (D : NearData) (hD : D.Valid) (hg0 : 0 < D.g 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {q : ℕ} {ι : Type} [Fintype ι] (E : Entries q ι), (∀ j, E.δ j ∈ D.Δ) →
      ∀ j, (∀ k, k ≠ j → E.χ k = E.χ j → M ≤ |E.γ j - E.γ k| * Real.log q) →
        pairExcess D E j = 0 := by
  classical
  have hd₁ : 0 < D.d₁ := by unfold NearData.d₁; linarith
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 (|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|) hd₁
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => Finset.sum_eq_zero fun k hk => ?_⟩
  obtain ⟨hk1, hk2⟩ := (Finset.mem_filter.1 hk).2
  have hY : M ≤ |(E.γ j - E.γ k) * Real.log q| := by
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)]
    exact hsep k hk1 hk2
  have hx : -(D.s₁ - E.δ j - E.δ k) ∈
      Set.Icc (-(|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|)) (|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|) := by
    have hj := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ j)
    have hk3 := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ k)
    rw [Set.mem_Icc, ← abs_le, abs_neg]
    linarith [abs_sub (D.s₁ - E.δ j) (E.δ k), abs_sub D.s₁ (E.δ j)]
  have h := hdec _ hx _ hY
  apply max_eq_left
  linarith [(abs_le.1 (Complex.abs_re_le_norm (laplace D.g (((-(D.s₁ - E.δ j - E.δ k) : ℝ) : ℂ) +
    (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)))).2]

theorem builder_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) {Iu Du : ℝ} (hIu : D.IB ≤ Iu)
    (hDu : 0 < Du) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            (∀ j, D.Dδ (E.δ j) - D.d₁ + pairExcess D E j ≤ De j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((1 + η) * (D.d₁ / Du + η)) ∧
              ∑ j, (max 0 (r j / Real.sqrt (Iu * Du) - η - τ)) ^ 2 / ((1 + η) * De j / Du) ≤
                1 - τ ^ 2 / ((1 + η) * (D.d₁ / Du + η)) := by
  have hIB := hD.IB_pos
  have hNpos : 0 < Real.sqrt (D.IB * Du) := Real.sqrt_pos.2 (by positivity)
  set m := min 1 (min (Real.sqrt (D.IB * Du)) Du)
  have hη'pos : 0 < η * m := mul_pos hη (lt_min one_pos (lt_min hNpos hDu))
  have hη'η : η * m ≤ η := by nlinarith [min_le_left 1 (min (Real.sqrt (D.IB * Du)) Du)]
  have hη'N : η * m ≤ η * Real.sqrt (D.IB * Du) :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hη.le
  have hη'D : η * m ≤ η * Du :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hη.le
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ :=
    graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη'pos
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK r De hr hDj hDe
  set η' := η * m
  set N := Real.sqrt (D.IB * Du)
  have hDnpos : 0 < Du / (1 + η') := div_pos hDu (by linarith)
  obtain ⟨τ, hτ0, hτd, hT⟩ :=
    h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj Sz hSz hsep hK (Du / (1 + η')) hDnpos hDj
  have hd₁ : 0 ≤ D.d₁ := by unfold NearData.d₁; linarith [hD.g_cond2.nonneg 0 le_rfl]
  have hNn : Real.sqrt ((1 + η') * D.IB * (Du / (1 + η'))) = N := by
    congr 1; field_simp
  rw [hNn] at hT
  have hsq : N ≤ Real.sqrt (Iu * Du) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hIu hDu.le)
  have hdd : (D.d₁ + η') / (Du / (1 + η')) ≤ (1 + η) * (D.d₁ / Du + η) := by
    rw [show (D.d₁ + η') / (Du / (1 + η')) = (1 + η') * (D.d₁ + η') / Du by field_simp,
      show (1 + η) * (D.d₁ / Du + η) = (1 + η) * (D.d₁ + η * Du) / Du by field_simp]
    exact div_le_div_of_nonneg_right (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)) hDu.le
  refine ⟨τ, hτ0, hτd.trans (Real.sqrt_le_sqrt hdd), ?_⟩
  have h1 : ∑ j, (max 0 (r j / Real.sqrt (Iu * Du) - η - τ)) ^ 2 / ((1 + η) * De j / Du) ≤
      ∑ j, (max 0 (keptBound D E Sz η' j / N - τ)) ^ 2 /
        ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / (Du / (1 + η'))) := by
    refine Finset.sum_le_sum fun j _ => Cert.term_le ?_ hτ0 (div_pos (hDj j) hDnpos) ?_
    · by_cases hr0 : r j ≤ 0
      · right; linarith [div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg (Iu * Du))]
      · left
        have hrk := (hr j).resolve_right hr0
        have hk : keptBound D E Sz η' j = keptBound D E Sz 0 j - η' := by unfold keptBound; ring
        rw [hk, sub_div]
        linarith [div_le_div_of_nonneg_left (lt_of_not_ge hr0).le hNpos hsq,
          (div_le_iff₀ hNpos).2 hη'N, div_le_div_of_nonneg_right hrk hNpos.le]
    · rw [show (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / (Du / (1 + η')) =
        (1 + η') * (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Du by field_simp]
      exact div_le_div_of_nonneg_right (mul_le_mul (by linarith) (hDe j) (hDj j).le (by linarith)) hDu.le
  have h2 := div_le_div_of_nonneg_left (sq_nonneg τ) (div_pos (by linarith) hDnpos) hdd
  linarith

end GradedNear
