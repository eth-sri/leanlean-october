module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FiniteExponentialSums

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual convergent oscillatory tails of Lemma 3 -/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology

/-- Absolute convergence of summable nonnegative weights times the actual modes. -/
theorem summable_weighted_modes {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (x : ℝ) (N : ℕ) :
    Summable (fun n : ℕ => w n • expMode x (n + N + 1)) := by
  apply hs.of_norm_bounded
  intro n
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw n), norm_expMode, mul_one,
    le_refl]

/-- Reindex a complex natural-number tail, retaining its precise source inequality. -/
theorem tsum_complex_nat_tail_eq {F : ℕ → ℂ} (N : ℕ)
    (hF : Summable (fun n : ℕ => F (n + N + 1))) :
    (∑' ν : ℕ, if N < ν then F ν else 0) = ∑' n : ℕ, F (n + N + 1) := by
  let f : ℕ → ℂ := fun ν => if N < ν then F ν else 0
  have htail : (fun n => f (n + (N + 1))) = (fun n => F (n + N + 1)) := by
    funext n
    simp only [f, show N < n + (N + 1) by omega, ite_true, Nat.add_assoc]
  have hs : Summable f := (summable_nat_add_iff (N + 1)).mp (htail.symm ▸ hF)
  have hhead : ∑ ν ∈ Finset.range (N + 1), f ν = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    simp only [Finset.mem_range] at hν
    simp only [f, show ¬ N < ν by omega, ite_false]
  have he := hs.sum_add_tsum_nat_add (N + 1)
  rw [hhead, zero_add, htail] at he
  exact he.symm

/-- The source's actual negative-shift oscillatory tail. -/
noncomputable def negativeTail (N : ℕ) (x y : ℝ) : ℂ :=
  ∑' ν : ℕ, if N < ν then expMode x ν / (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0

/-- The source's actual positive-shift oscillatory tail. -/
noncomputable def positiveTail (x y : ℝ) : ℂ :=
  ∑' ν : ℕ, if 0 < ν then expMode x ν / (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0

/-- The mixed negative-shift denominator makes the actual series absolutely convergent. -/
theorem summable_negative_tail_shift {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    Summable (fun n : ℕ => expMode x (n + N + 1) /
      (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) : ℝ)) := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply one_div_nonneg.mpr
    exact mul_nonneg (by positivity) (by linarith)
  have h := summable_weighted_modes hw (hasSum_harmonic_tail hy hNy).summable x N
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using h

/-- Reindexing the actual negative tail preserves its first included frequency. -/
theorem negativeTail_eq_shift {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    negativeTail N x y = ∑' n : ℕ,
      (1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) • expMode x (n + N + 1) := by
  unfold negativeTail
  rw [tsum_complex_nat_tail_eq (F := fun ν : ℕ =>
    expMode x ν / (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ)) N
    (by simpa only [Nat.cast_add, Nat.cast_one] using summable_negative_tail_shift hy hNy x)]
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Absolute convergence of the actual positive-shift series. -/
theorem summable_positive_tail_shift {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => expMode x (n + 1) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) : ℝ)) := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y)) := by positivity
  have h := summable_weighted_modes hw (hasSum_harmonic_plus hy).summable x 0
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using h

/-- Reindexing the positive tail starts at one, not zero or two. -/
theorem positiveTail_eq_shift {y : ℝ} (hy : 0 < y) (x : ℝ) :
    positiveTail x y = ∑' n : ℕ,
      (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1) := by
  unfold positiveTail
  rw [tsum_complex_nat_tail_eq (F := fun ν : ℕ =>
    expMode x ν / (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ)) 0
    (by simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
      summable_positive_tail_shift hy x)]
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Differentiating the actual Gamma reflection identity gives the real digamma reflection. -/
theorem real_digamma_one_sub {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Complex.digamma (1 - x : ℝ)).re - (Complex.digamma (x : ℂ)).re =
      Real.pi * Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
  have hx' : 0 < 1 - x := by linarith
  have hd : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hd' : DifferentiableAt ℝ Real.Gamma (1 - x) :=
    Real.differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hsin : Real.sin (Real.pi * x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx)
      (by nlinarith [Real.pi_pos])).ne'
  have he : (fun u : ℝ => Real.Gamma u * Real.Gamma (1 - u)) =
      (fun u => Real.pi / Real.sin (Real.pi * u)) := funext Real.Gamma_mul_Gamma_one_sub
  have h := congrArg (fun f : ℝ → ℝ => logDeriv f x) he
  rw [logDeriv_fun_mul (f := Real.Gamma) (g := fun u : ℝ => Real.Gamma (1 - u)) x (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hx').ne'
      hd (hd'.comp x ((differentiableAt_const (1 : ℝ)).sub differentiableAt_id)),
    logDeriv_fun_div (f := fun _ : ℝ => Real.pi) (g := fun u => Real.sin (Real.pi * u)) x Real.pi_ne_zero hsin (differentiableAt_const _) (by fun_prop),
    logDeriv_const, Pi.zero_apply, zero_sub] at h
  have hcomp : logDeriv (fun u : ℝ => Real.Gamma (1 - u)) x = -logDeriv Real.Gamma (1 - x) := by
    change logDeriv (Real.Gamma ∘ (fun u : ℝ => 1 - u)) x = _
    rw [logDeriv_comp hd' ((differentiableAt_const (1 : ℝ)).sub differentiableAt_id)]
    simp
  have htrig : logDeriv (fun u : ℝ => Real.sin (Real.pi * u)) x =
      Real.pi * Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
    change logDeriv (Real.sin ∘ (fun u : ℝ => Real.pi * u)) x = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Real.logDeriv_sin]
    simp [Real.cot_eq_cos_div_sin]
    ring
  rw [hcomp, htrig, logDeriv_apply, logDeriv_apply,
    ← real_digamma_eq_deriv_Gamma_div hx, ← real_digamma_eq_deriv_Gamma_div hx'] at h
  linarith

/-- The paired reciprocal sum at one half has the exact value pi/2. -/
theorem paired_reciprocal_half :
    ((Complex.digamma (3 / 4 : ℝ)).re - (Complex.digamma (1 / 4 : ℝ)).re) / 2 =
      Real.pi / 2 := by
  have h := real_digamma_one_sub (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  norm_num at h
  rw [show Real.pi * (1 / 4) = Real.pi / 4 by ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have he : Real.pi * (Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) = Real.pi := by
    field_simp
  rw [he] at h
  norm_num
  linarith

/-- The paired reciprocal value decreases on its positive domain. -/
theorem paired_reciprocal_antitone {x z : ℝ} (hx : 0 < x) (hxz : x ≤ z) :
    ((Complex.digamma ((z + 1) / 2 : ℝ)).re - (Complex.digamma (z / 2 : ℝ)).re) / 2 ≤
      ((Complex.digamma ((x + 1) / 2 : ℝ)).re - (Complex.digamma (x / 2 : ℝ)).re) / 2 := by
  have hz : 0 < z := hx.trans_le hxz
  rw [← (hasSum_paired_reciprocal hz).tsum_eq, ← (hasSum_paired_reciprocal hx).tsum_eq]
  apply (hasSum_paired_reciprocal hz).summable.tsum_le_tsum _ (hasSum_paired_reciprocal hx).summable
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he (u : ℝ) (hu : 0 < u) : 1 / u - 1 / (u + 1) = 1 / (u * (u + 1)) := by
    have hu' : 0 < u + 1 := by positivity
    field_simp
    ring
  rw [show 2 * (n : ℝ) + 1 + z = (2 * (n : ℝ) + z) + 1 by ring,
    show 2 * (n : ℝ) + 1 + x = (2 * (n : ℝ) + x) + 1 by ring,
    he _ (by positivity), he _ (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-- The actual half-integer negative tail is the real alternating source series. -/
theorem negativeTail_half_integer (N : ℕ) (k : ℤ) (y : ℝ) :
    negativeTail N ((k : ℝ) + 1 / 2) y =
      ((∑' ν : ℕ, if N < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) - y)) else 0 : ℝ) : ℂ) := by
  unfold negativeTail
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ν
  split_ifs
  · rw [expMode_half_integer]
    simp
  · simp

/-- The actual half-integer positive tail is the real alternating source series. -/
theorem positiveTail_half_integer (k : ℤ) (y : ℝ) :
    positiveTail ((k : ℝ) + 1 / 2) y =
      ((∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0 : ℝ) : ℂ) := by
  unfold positiveTail
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ν
  split_ifs
  · rw [expMode_half_integer]
    simp
  · simp

