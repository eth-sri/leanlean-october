module

public import PottsDiscontinuity.Bethe.CountingDifference
public import PottsDiscontinuity.Bethe.AsymptoticOffset

/-! Centered counting levels align exactly in the even case and to second order
    in the odd case. Inverting the counting function is then uniformly stable. -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

local notation "J" => Icc (-Real.pi) Real.pi

theorem exists_mean_deriv {F D : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (D x) x) (a b : ℝ) :
    ∃ t ∈ uIcc a b, F b - F a = D t * (b - a) := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hF x).continuousAt
  have hlt (u v : ℝ) (huv : u < v) : ∃ t ∈ Icc u v, F v - F u = D t * (v - u) := by
    obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope F D huv hc.continuousOn (fun x _ => hF x)
    exact ⟨t, Ioo_subset_Icc_self ht, ((eq_div_iff (sub_ne_zero.mpr huv.ne')).mp he).symm⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · simpa [uIcc_of_le hab.le] using hlt a b hab
  · simp
  · obtain ⟨t, ht, he⟩ := hlt b a hba
    exact ⟨t, uIcc_of_ge hba.le ▸ ht, by linarith⟩

private theorem mean_midpoint_error {F D : ℝ → ℝ} {M u v : ℝ} (hM : 0 ≤ M)
    (hu : u ∈ J) (hv : v ∈ J) (huv : u ≤ v)
    (hF : ∀ x, HasDerivAt F (D x) x)
    (hLip : ∀ x ∈ J, ∀ y ∈ J, |D x - D y| ≤ M * |x - y|) :
    |F ((u + v) / 2) - (F u + F v) / 2| ≤ M * (v - u) ^ 2 := by
  let a := (u + v) / 2
  have h1 : u ≤ a := by dsimp [a]; linarith
  have h2 : a ≤ v := by dsimp [a]; linarith
  obtain ⟨t, ht, het⟩ := exists_mean_deriv hF u a
  obtain ⟨s, hs, hes⟩ := exists_mean_deriv hF a v
  rw [uIcc_of_le h1] at ht
  rw [uIcc_of_le h2] at hs
  have hts : |t - s| ≤ v - u := abs_le.mpr (by constructor <;> linarith [ht.1, ht.2, hs.1, hs.2])
  have heq : F a - (F u + F v) / 2 = (D t - D s) * ((v - u) / 4) := by
    linear_combination (het - hes) / 2
  change |F a - (F u + F v) / 2| ≤ _
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (v - u) / 4)]
  have h := (hLip t ⟨hu.1.trans ht.1, ht.2.trans (h2.trans hv.2)⟩ s
    ⟨hu.1.trans (h1.trans hs.1), hs.2.trans hv.2⟩).trans (mul_le_mul_of_nonneg_left hts hM)
  exact (mul_le_mul_of_nonneg_right h (by positivity)).trans (by nlinarith [mul_nonneg hM (sq_nonneg (v - u))])

section

variable {Δ : ℝ} (hΔ : Δ < -1) {N r : ℕ} (hN : 0 < N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ} (hp : p ∈ S_n (N / 2))
    (hpBE : DiscreteBetheEquation Δ N (N / 2) p) (hqBE : DiscreteBetheEquation Δ N (N / 2 - r) q)
    {m M : ℝ} (hm : 0 < m) (hM : 0 ≤ M)
    (hpos : ∀ x ∈ J, m ≤ betheCountingDerivative Δ N (N / 2) p x)
    (hLip : ∀ x ∈ J, ∀ y ∈ J, |betheCountingDerivative Δ N (N / 2) p x -
      betheCountingDerivative Δ N (N / 2) p y| ≤ M * |x - y|)

include hΔ hN hp hpBE hqBE hm hM hpos hLip in
private theorem aligned_counting_error (j : Fin (N / 2 - r)) :
    |(N : ℝ) * (betheCountingFunction Δ N (N / 2 - r) q (q j) -
      betheCountingFunction Δ N (N / 2) p (alignedRoot N r hr p j))| ≤ (M / m ^ 2) / N := by
  let F := betheCountingFunction Δ N (N / 2) p
  let D := betheCountingDerivative Δ N (N / 2) p
  let d := discreteBetheIndex (N / 2 - r) j
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((N / 2 : ℕ) : ℝ) = ((N / 2 - r : ℕ) : ℝ) + r := by
    exact_mod_cast (show N / 2 = (N / 2 - r) + r by omega)
  rw [betheCountingFunction_root_value hN q hqBE]
  change |(N : ℝ) * (d / N - F (alignedRoot N r hr p j))| ≤ _
  unfold alignedRoot
  split
  next he =>
    let i : Fin (N / 2) := ⟨j.val + r / 2, by omega⟩
    have hd : discreteBetheIndex (N / 2) i = d := by
      have hcast : 2 * ((r / 2 : ℕ) : ℝ) = (r : ℝ) := by
        exact_mod_cast (show 2 * (r / 2) = r by omega)
      dsimp [d, discreteBetheIndex, i]
      push_cast
      linarith
    change |(N : ℝ) * (d / N - F (p i))| ≤ _
    dsimp [F]
    rw [betheCountingFunction_root_value hN p hpBE, hd, sub_self, mul_zero, abs_zero]
    positivity
  next ho =>
    let l : Fin (N / 2) := ⟨j.val + (r - 1) / 2, by omega⟩
    let k : Fin (N / 2) := ⟨j.val + (r + 1) / 2, by omega⟩
    have hi : (l.val : ℝ) + 1 = k.val := by exact_mod_cast (show l.val + 1 = k.val by dsimp [l, k]; omega)
    have hi' : (l.val : ℝ) + k.val = 2 * (j.val : ℝ) + r := by
      exact_mod_cast (show l.val + k.val = 2 * j.val + r by dsimp [l, k]; omega)
    have huv : p l ≤ p k := hp.2.1.monotone (by change l.val ≤ k.val; dsimp [l, k]; omega)
    have hav : (F (p l) + F (p k)) / 2 = d / N := by
      dsimp [F, d]
      rw [betheCountingFunction_root_value hN p hpBE, betheCountingFunction_root_value hN p hpBE]
      unfold discreteBetheIndex
      linear_combination (hi' - hc) / (2 * (N : ℝ))
    have hd : F (p k) - F (p l) = 1 / (N : ℝ) := by
      dsimp [F]
      rw [betheCountingFunction_root_value hN p hpBE, betheCountingFunction_root_value hN p hpBE]
      unfold discreteBetheIndex
      linear_combination -hi / (N : ℝ)
    have hF (x : ℝ) : HasDerivAt F (D x) x := hasDerivAt_betheCountingFunction hΔ N _ p x
    have hgap := counting_length_le hm hF hpos (Ioo_subset_Icc_self (hp.1 l)) (Ioo_subset_Icc_self (hp.1 k)) huv
    rw [hd, div_div, mul_comm (N : ℝ)] at hgap
    change |(N : ℝ) * (d / N - F ((p l + p k) / 2))| ≤ _
    rw [← hav, abs_mul, abs_of_pos hN', abs_sub_comm]
    have herr := mean_midpoint_error hM (Ioo_subset_Icc_self (hp.1 l)) (Ioo_subset_Icc_self (hp.1 k)) huv hF hLip
    have hb := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr huv) hgap 2) hM
    exact (mul_le_mul_of_nonneg_left (herr.trans hb) hN'.le).trans_eq (by field_simp [hm.ne', hN'.ne'])

end

/-- A nonzero root is at least half a counting spacing from zero. -/
private theorem bethe_root_abs_lower {Δ : ℝ} (hΔ : Δ < -1) {N n : ℕ} (hN : 0 < N)
    {q : Fin n → ℝ} (hq : q ∈ S_n n) (hBE : DiscreteBetheEquation Δ N n q) {m U : ℝ} (hm : 0 < m)
    (hlow : ∀ x ∈ J, m ≤ betheCountingDerivative Δ N n q x)
    (hup : ∀ x ∈ J, betheCountingDerivative Δ N n q x ≤ U) (j : Fin n) (hj : q j ≠ 0) :
    1 / 2 ≤ U * ((N : ℝ) * |q j|) := by
  obtain ⟨t, ht, ht'⟩ := exists_mean_deriv (hasDerivAt_betheCountingFunction hΔ N n q) 0 (q j)
  have h0 : (0 : ℝ) ∈ J := ⟨neg_nonpos.mpr Real.pi_pos.le, Real.pi_pos.le⟩
  have htJ := (ordConnected_Icc.uIcc_subset h0 (Ioo_subset_Icc_self (hq.1 j))) ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [betheCountingFunction_zero hq, sub_zero, sub_zero, betheCountingFunction_root_value hN q hBE] at ht'
  have hi := (div_eq_iff hN'.ne').mp ht'
  let z : ℤ := 2 * (j.val : ℤ) + 1 - n
  have hcast : (z : ℝ) = 2 * discreteBetheIndex n j := by dsimp [z, discreteBetheIndex]; push_cast; ring
  have hD : 0 < betheCountingDerivative Δ N n q t := hm.trans_le (hlow t htJ)
  have hne : z ≠ 0 := by
    intro h
    rw [h, Int.cast_zero] at hcast
    exact (mul_ne_zero (mul_ne_zero hD.ne' hj) hN'.ne') (by linarith)
  have h1 : (1 : ℤ) ≤ |z| := by
    have hp := abs_pos.mpr hne
    omega
  have h1' : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast h1
  rw [hcast, hi, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2), abs_mul, abs_of_pos hN',
    abs_mul, abs_of_pos hD] at h1'
  have hb := mul_le_mul_of_nonneg_right (hup t htJ) (show 0 ≤ (N : ℝ) * |q j| by positivity)
  linarith

/-- The scaled root shift is controlled near zero as well as away from it. -/
theorem bethe_alignedShift_control {Δ : ℝ} (hΔ : Δ < -1) {N r : ℕ} (hN : 0 < N) (hr : r ≤ N / 2)
    {p : Fin (N / 2) → ℝ} {q : Fin (N / 2 - r) → ℝ} (hp : p ∈ S_n (N / 2)) (hq : q ∈ S_n (N / 2 - r))
    (hpBE : DiscreteBetheEquation Δ N (N / 2) p) (hqBE : DiscreteBetheEquation Δ N (N / 2 - r) q)
    {m M U C T : ℝ} (hm : 0 < m) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hpos : ∀ x ∈ J, m ≤ betheCountingDerivative Δ N (N / 2) p x ∧
      m ≤ betheCountingDerivative Δ N (N / 2 - r) q x)
    (hup : ∀ x ∈ J, betheCountingDerivative Δ N (N / 2 - r) q x ≤ U)
    (hLip : ∀ x ∈ J, ∀ y ∈ J, |betheCountingDerivative Δ N (N / 2) p x -
      betheCountingDerivative Δ N (N / 2) p y| ≤ M * |x - y|)
    (hH : ∀ x ∈ J, |countingShift Δ N p q x + (r : ℝ) * tauCont Δ x| ≤ C / N)
    (hτ : ∀ x ∈ J, |tauCont Δ x| ≤ T * |x|) (j : Fin (N / 2 - r)) :
    let a := alignedRoot N r hr p j
    let S := (N : ℝ) * (q j - a)
    |S| ≤ (((r : ℝ) * T + 2 * (C + M / m ^ 2) * U) / m) * |q j| ∧
      ∃ t ∈ uIcc (q j) a, |betheCountingDerivative Δ N (N / 2) p t * S + countingShift Δ N p q (q j)| ≤
        (M / m ^ 2) / N := by
  dsimp only
  let a := alignedRoot N r hr p j
  let S := (N : ℝ) * (q j - a)
  let F := betheCountingFunction Δ N (N / 2) p
  let D := betheCountingDerivative Δ N (N / 2) p
  let H := countingShift Δ N p q
  obtain ⟨t, ht, he⟩ := exists_mean_deriv (hasDerivAt_betheCountingFunction hΔ N (N / 2) p) a (q j)
  change F (q j) - F a = D t * (q j - a) at he
  rw [uIcc_comm] at ht
  have hqJ := Ioo_subset_Icc_self (hq.1 j)
  have htJ := (ordConnected_Icc.uIcc_subset hqJ (alignedRoot_mem_Icc hr hp j)) ht
  have herr := aligned_counting_error hΔ hN hr hp hpBE hqBE hm hM (fun x hx => (hpos x hx).1) hLip j
  have hS : |D t * S + H (q j)| ≤ (M / m ^ 2) / N := by
    convert herr using 2
    dsimp only [S, H, countingShift]
    linear_combination -(N : ℝ) * he
  refine ⟨?_, t, ht, hS⟩
  change |S| ≤ _
  by_cases hz : q j = 0
  · have hj : Fin.rev j = j := hq.2.1.injective (by simp [show q (Fin.rev j) = -q j from hq.2.2 j, hz])
    have ha := alignedRoot_rev hr hp j
    rw [hj] at ha
    simp [S, hz, show a = 0 by linarith]
  · have hl := bethe_root_abs_lower hΔ hN hq hqBE hm (fun x hx => (hpos x hx).2) hup j hz
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hd : (C + M / m ^ 2) / N ≤ (2 * (C + M / m ^ 2) * U) * |q j| := by
      apply (div_le_iff₀ hN').mpr
      nlinarith only [mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * (C + M / m ^ 2) by positivity)]
    have hτ' := mul_le_mul_of_nonneg_left (hτ _ hqJ) (Nat.cast_nonneg r : 0 ≤ (r : ℝ))
    have h := (abs_sub (D t * S + H (q j)) (H (q j) + (r : ℝ) * tauCont Δ (q j))).trans
      (add_le_add hS (hH _ hqJ))
    rw [show D t * S + H (q j) - (H (q j) + (r : ℝ) * tauCont Δ (q j)) =
      D t * S - (r : ℝ) * tauCont Δ (q j) by ring] at h
    have h' := abs_add_le (D t * S - (r : ℝ) * tauCont Δ (q j)) ((r : ℝ) * tauCont Δ (q j))
    have hp' : m ≤ D t := (hpos t htJ).1
    rw [sub_add_cancel, abs_mul (D t), abs_of_pos (hm.trans_le hp'), abs_mul (r : ℝ),
      abs_of_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ (r : ℝ))] at h'
    rw [div_mul_eq_mul_div, le_div_iff₀ hm]
    linarith only [h, h', hτ', hd, mul_le_mul_of_nonneg_right hp' (abs_nonneg S),
      add_div C (M / m ^ 2) (N : ℝ)]

end PottsDiscontinuity.Bethe
