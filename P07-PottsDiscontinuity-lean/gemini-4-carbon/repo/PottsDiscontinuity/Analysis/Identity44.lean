module

public import Mathlib

/-! # Identity (4.4): partial-fraction expansion and positivity of the alternating `tanh` series -/

@[expose] public section

open Filter Topology Real

namespace PottsDiscontinuity

theorem sum_Icc_one_eq_sum_range (g : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, g k = ∑ n ∈ Finset.range N, g (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

private noncomputable def invSqSumValue (a : ℝ) : ℝ :=
  π * (Real.cosh (π * a) / Real.sinh (π * a)) / (2 * a) + 1 / (2 * a ^ 2)

private theorem hasSum_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) (invSqSumValue a) := by
  have hx : ((a : ℂ) * Complex.I) ∈ Complex.integerComplement := fun ⟨n, hn⟩ => by
    have := congrArg Complex.im hn; simp at this; exact ha.ne' this.symm
  have h := cot_series_rep' hx
  have hsinh : Real.sinh (π * a) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hs : Complex.sinh ((π : ℂ) * a) ≠ 0 := by
    have : (Real.sinh (π * a) : ℂ) ≠ 0 := by exact_mod_cast hsinh
    rw [Complex.ofReal_sinh] at this; push_cast at this; exact this
  have hcot : Complex.cot (π * ((a : ℂ) * Complex.I)) =
      -(Complex.I * ((Real.cosh (π * a) / Real.sinh (π * a) : ℝ) : ℂ)) := by
    rw [Complex.cot_eq_cos_div_sin, show (π : ℂ) * ((a : ℂ) * Complex.I) = ((π * a : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.cos_mul_I, Complex.sin_mul_I]
    push_cast; field_simp; simp [Complex.I_sq]
  have hterm (n : ℕ) : (1 / ((a : ℂ) * Complex.I - ((n : ℂ) + 1)) + 1 / ((a : ℂ) * Complex.I + ((n : ℂ) + 1))) =
      -(Complex.I * ((2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) := by
    have h1 : (a : ℂ) ^ 2 + ((n : ℂ) + 1) ^ 2 ≠ 0 := by exact_mod_cast (by positivity : a ^ 2 + ((n : ℝ) + 1) ^ 2 ≠ 0)
    have h2 : (a : ℂ) * Complex.I - ((n : ℂ) + 1) ≠ 0 := fun h0 => ha.ne' (by have := congrArg Complex.im h0; simp at this; exact this)
    have h3 : (a : ℂ) * Complex.I + ((n : ℂ) + 1) ≠ 0 := fun h0 => ha.ne' (by have := congrArg Complex.im h0; simp at this; exact this)
    push_cast; field_simp; ring_nf; simp
  simp_rw [hterm] at h
  rw [hcot, show ∑' n : ℕ, -(Complex.I * ((2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) =
      -(Complex.I * ((∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ)) by
        rw [Complex.ofReal_tsum, tsum_neg, tsum_mul_left],
    show (1 : ℂ) / ((a : ℂ) * Complex.I) = -(Complex.I * ((1 / a : ℝ) : ℂ)) by push_cast; field_simp; simp [Complex.I_sq]] at h
  have hcoth : π * (Real.cosh (π * a) / Real.sinh (π * a)) = 1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) := by
    have h7 : ((π * (Real.cosh (π * a) / Real.sinh (π * a)) : ℝ) : ℂ) =
        ((1 / a + ∑' n : ℕ, 2 * a / (a ^ 2 + ((n : ℝ) + 1) ^ 2) : ℝ) : ℂ) := by
      apply mul_left_cancel₀ Complex.I_ne_zero
      rw [Complex.ofReal_mul, Complex.ofReal_add]
      linear_combination (-1 : ℂ) * h
    exact_mod_cast h7
  have hsum1 : Summable (fun n : ℕ => 1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)) :=
    Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => by
        have hp : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
        exact one_div_le_one_div_of_le hp (by nlinarith [sq_nonneg a]))
      (by simpa using (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two))
  have hsum2 := (hsum1.mul_left (2 * a)).hasSum
  rw [show ∑' n : ℕ, 2 * a * (1 / (a ^ 2 + ((n : ℝ) + 1) ^ 2)) = π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a by
    rw [hcoth]; simp_rw [mul_one_div]; ring] at hsum2
  have hsum3 : HasSum (fun n : ℕ => 1 / (a ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2))
      ((π * (Real.cosh (π * a) / Real.sinh (π * a)) - 1 / a) / (2 * a)) := by
    convert hsum2.div_const (2 * a) using 1; funext n; push_cast; have := ha.ne'; field_simp
  refine (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) 1).1 ?_
  convert hsum3 using 1
  simp only [invSqSumValue, Finset.sum_range_one, Nat.cast_zero]
  have := ha.ne'; field_simp; ring

private theorem hasSum_inv_sq_even_odd {a : ℝ} (ha : 0 < a) :
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k : ℕ) : ℝ) ^ 2)) (invSqSumValue (a / 2) / 4) ∧
    HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2)) (invSqSumValue a - invSqSumValue (a / 2) / 4) := by
  have he : HasSum (fun k : ℕ => 1 / (a ^ 2 + ((2 * k : ℕ) : ℝ) ^ 2)) (invSqSumValue (a / 2) / 4) := by
    convert (hasSum_inv_sq_add_sq (half_pos ha)).div_const 4 using 1
    funext k; push_cast; field_simp; norm_num
  refine ⟨he, ?_⟩
  have hf := hasSum_inv_sq_add_sq ha
  have hodd : Summable (fun k : ℕ => 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
    hf.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun _ _ h => by simp only at h; omega
  have hu := hf.unique (HasSum.even_add_odd (f := fun n : ℕ => 1 / (a ^ 2 + (n : ℝ) ^ 2)) he hodd.hasSum)
  rw [show invSqSumValue a - invSqSumValue (a / 2) / 4 = ∑' k : ℕ, 1 / (a ^ 2 + ((2 * k + 1 : ℕ) : ℝ) ^ 2) by linarith]
  exact hodd.hasSum

private noncomputable def cTerm (lam : ℝ) (j : ℕ) (m : ℝ) : ℝ :=
  8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2 + 4 * m ^ 2 * lam ^ 2)

private noncomputable def dTerm (lam : ℝ) (j : ℕ) : ℝ :=
  2 / ((2 * (j : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam))) -
    4 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)

private theorem alt_partial_sum_bounds : ∀ (N : ℕ) (u : ℕ → ℝ), Antitone u → (∀ i, 0 ≤ u i) →
    0 ≤ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ∧ ∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u i ≤ u 0
  | 0, u, _, h0 => by simp [h0 0]
  | N + 1, u, hu, h0 => by
    have ih := alt_partial_sum_bounds N (fun i => u (i + 1)) (fun _ _ hab => hu (by omega)) fun _ => h0 _
    have h01 : u 1 ≤ u 0 := hu (by omega)
    rw [Finset.sum_range_succ', show ∑ i ∈ Finset.range N, (-1 : ℝ) ^ (i + 1) * u (i + 1) =
        -∑ i ∈ Finset.range N, (-1 : ℝ) ^ i * u (i + 1) by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring]
    simp only [pow_zero, one_mul]; exact ⟨by linarith [ih.2], by linarith [ih.1]⟩

/-- **Identity (4.4)** together with the convergence and positivity statements. -/
theorem identity44 (lam : ℝ) (hlam : 0 < lam) :
    ∃ S T : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
          (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
      0 < lam + 2 * S ∧ lam + 2 * S = T := by
  have hpi := Real.pi_ne_zero; have hl0 := hlam.ne'
  have hodd_sq : HasSum (fun j : ℕ => 1 / (2 * (j : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
    have hz := hasSum_zeta_two
    have hev : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ 2) (π ^ 2 / 6 / 4) := by
      convert hz.div_const 4 using 1; funext k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · push_cast; have : (k : ℝ) ≠ 0 := by positivity
        field_simp; norm_num
    have hodd : Summable (fun j : ℕ => 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
      hz.summable.comp_injective (i := fun k : ℕ => 2 * k + 1) fun _ _ h => by simp only at h; omega
    have hu := hz.unique (HasSum.even_add_odd (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) hev hodd.hasSum)
    rw [show π ^ 2 / 8 = ∑' j : ℕ, 1 / ((2 * j + 1 : ℕ) : ℝ) ^ 2 by linarith]
    convert hodd.hasSum using 1; funext j; push_cast; rfl
  have hbound : HasSum (fun j : ℕ => 8 * lam / ((2 * (j : ℝ) + 1) ^ 2 * π ^ 2)) lam := by
    convert hodd_sq.mul_left (8 * lam / π ^ 2) using 1
    · funext j; have : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
      field_simp
    · field_simp
  have htpos (k : ℕ) : 0 < 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) := by
    have : 0 < Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)) := Real.sinh_pos_iff.2 (by positivity)
    positivity
  have hsum_t : Summable (fun k : ℕ => 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))) :=
    Summable.of_nonneg_of_le (fun k => (htpos k).le) (fun k => by
      have hy : 0 < π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam) := by positivity
      have hs := Real.self_le_sinh_iff.2 hy.le
      calc 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam)))
          ≤ 4 / ((2 * (k : ℝ) + 1) * (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) :=
            div_le_div_of_nonneg_left (by norm_num) (by positivity) (mul_le_mul_of_nonneg_left hs (by positivity))
        _ = 8 * lam / ((2 * (k : ℝ) + 1) ^ 2 * π ^ 2) := by field_simp; norm_num)
      hbound.summable
  have hT := hsum_t.hasSum
  set T := ∑' k : ℕ, 4 / ((2 * (k : ℝ) + 1) * Real.sinh (π ^ 2 * (2 * (k : ℝ) + 1) / (2 * lam))) with hTdef
  have hTpos : 0 < T := hsum_t.tsum_pos (fun k => (htpos k).le) 0 (htpos 0)
  have hd : HasSum (fun j : ℕ => dTerm lam j) (T / 2 - lam / 2) := by
    convert (hT.div_const 2).sub (hodd_sq.mul_left (4 * lam / π ^ 2)) using 1
    · funext j; unfold dTerm
      have hs : Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
      have : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
      generalize Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) = s at hs ⊢
      field_simp; ring
    · field_simp; ring
  let S := ∑' j : ℕ, dTerm lam j
  have hS : S = T / 2 - lam / 2 := hd.tsum_eq
  refine ⟨S, T, ?_, hT, by rw [hS]; linarith, by rw [hS]; ring⟩
  have hc_tanh {m : ℝ} (hm : 0 < m) : HasSum (fun j : ℕ => cTerm lam j m) (Real.tanh (m * lam) / m) := by
    let a := 2 * m * lam / π
    have ha : 0 < a := by dsimp [a]; positivity
    have ho := (hasSum_inv_sq_even_odd ha).2
    have hx : 0 < π * a / 2 := by positivity
    have hsx : Real.sinh (π * a / 2) ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
    have hcx : Real.cosh (π * a / 2) ≠ 0 := (Real.cosh_pos _).ne'
    have htanh_id : 2 * (Real.cosh (π * a) / Real.sinh (π * a)) - Real.cosh (π * a / 2) / Real.sinh (π * a / 2) =
        Real.tanh (π * a / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh, show π * a = 2 * (π * a / 2) by ring, Real.sinh_two_mul, Real.cosh_two_mul]
      field_simp; nlinarith [Real.cosh_sq (π * a / 2)]
    have hodd_val : HasSum (fun k : ℕ => 1 / (a ^ 2 + (2 * (k : ℝ) + 1) ^ 2)) (π / (4 * a) * Real.tanh (π * a / 2)) := by
      rw [← htanh_id]; convert ho using 1
      · funext k; push_cast; rfl
      · simp only [invSqSumValue]; rw [show π * (a / 2) = π * a / 2 by ring]
        have := ha.ne'; field_simp; ring
    have hm0 := hm.ne'
    convert hodd_val.mul_left (8 * lam / π ^ 2) using 1
    · funext j; unfold cTerm; dsimp [a]; field_simp; ring
    · dsimp [a]; rw [show π * (2 * m * lam / π) / 2 = m * lam by field_simp]; field_simp; ring
  have halt_c (j : ℕ) : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1)) (dTerm lam j) := by
    let b : ℝ := (2 * (j : ℝ) + 1) * π / (2 * lam)
    have hbpos : 0 < b := by dsimp [b]; positivity
    obtain ⟨he, ho⟩ := hasSum_inv_sq_even_odd hbpos
    have halt : HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (b ^ 2 + (n : ℝ) ^ 2)) (π / (2 * b * Real.sinh (π * b)) + 1 / (2 * b ^ 2)) := by
      have h := HasSum.even_add_odd (f := fun n : ℕ => (-1 : ℝ) ^ n / (b ^ 2 + (n : ℝ) ^ 2))
        (by convert he using 1; funext k; simp [pow_mul])
        (by convert ho.neg using 1; funext k; simp [pow_succ, pow_mul]; ring)
      convert h using 1
      have hx : 0 < π * b / 2 := by positivity
      have hsx : Real.sinh (π * b / 2) ≠ 0 := (Real.sinh_pos_iff.2 hx).ne'
      have hcx : Real.cosh (π * b / 2) ≠ 0 := (Real.cosh_pos _).ne'
      have hcoth_id : Real.cosh (π * b / 2) / Real.sinh (π * b / 2) =
          Real.cosh (π * b) / Real.sinh (π * b) + 1 / Real.sinh (π * b) := by
        rw [show π * b = 2 * (π * b / 2) by ring, Real.sinh_two_mul, Real.cosh_two_mul]
        field_simp; nlinarith [Real.cosh_sq (π * b / 2)]
      simp only [invSqSumValue]
      rw [show π * (b / 2) = π * b / 2 by ring, hcoth_id]
      have := hbpos.ne'; have : Real.sinh (π * b) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
      field_simp; ring
    have hsh := ((hasSum_nat_add_iff' (f := fun n : ℕ => (-1 : ℝ) ^ n / (b ^ 2 + (n : ℝ) ^ 2)) 1).2 halt).mul_left (2 / lam)
    have hb0 := hbpos.ne'; have hj : 2 * (j : ℝ) + 1 ≠ 0 := by positivity
    convert hsh using 1
    · funext n; unfold cTerm; dsimp [b]; push_cast
      have : ((n : ℝ) + 1) ^ 2 * (4 * lam ^ 2) + (2 * (j : ℝ) + 1) ^ 2 * π ^ 2 ≠ 0 := by positivity
      field_simp; ring
    · unfold dTerm
      simp only [Finset.sum_range_one, Nat.cast_zero, pow_zero, zero_pow two_ne_zero, add_zero, one_div]
      rw [show π * b = π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam) by dsimp [b]; field_simp]
      dsimp [b]
      have : Real.sinh (π ^ 2 * (2 * (j : ℝ) + 1) / (2 * lam)) ≠ 0 := (Real.sinh_pos_iff.2 (by positivity)).ne'
      field_simp; ring
  have hf (N : ℕ) : ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / k * Real.tanh (k * lam) =
      ∑' j : ℕ, ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) := by
    rw [Summable.tsum_finsetSum, sum_Icc_one_eq_sum_range]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [((hc_tanh (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mul_left ((-1 : ℝ) ^ (n + 1))).tsum_eq]
      push_cast; ring
    · exact fun n _ => ((hc_tanh (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mul_left ((-1 : ℝ) ^ (n + 1))).summable
  simp_rw [hf]
  refine tendsto_tsum_of_dominated_convergence hbound.summable
    (fun j => (halt_c j).tendsto_sum_nat) (Eventually.of_forall fun N j => ?_)
  have hanti : Antitone (fun n : ℕ => cTerm lam j ((n : ℝ) + 1)) := fun a b hab => by
    unfold cTerm
    have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hab
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (by nlinarith [sq_nonneg lam, mul_le_mul hab' hab' (by positivity : (0 : ℝ) ≤ (a : ℝ) + 1) (by positivity)])
  have hb := alt_partial_sum_bounds N (fun n : ℕ => cTerm lam j ((n : ℝ) + 1)) hanti fun _ => by unfold cTerm; positivity
  rw [show ∑ n ∈ Finset.range N, (-1 : ℝ) ^ (n + 1) * cTerm lam j ((n : ℝ) + 1) =
      -∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * cTerm lam j ((n : ℝ) + 1) by
    rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by rw [pow_succ]; ring,
    norm_neg, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.trans (by unfold cTerm; exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg lam]))

end PottsDiscontinuity
