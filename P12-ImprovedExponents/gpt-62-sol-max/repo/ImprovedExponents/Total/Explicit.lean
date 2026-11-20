module

public import ImprovedExponents.Total.Params

@[expose] public section

/-! The time exponents of the six costs follow from the asymptotic growth of their factors. -/

namespace ImprovedExponents

open ThreeSumApsp ThreeSumApsp.Spec Light.Sec4 Filter

/-- `log₂ 7 ≤ 250/89 ≤ 2.81`, because `7^89 ≤ 2^250`. -/
private theorem logb_two_seven_lt : Real.logb 2 7 < 2.81 := by
  have h7 : Real.logb 2 7 ≤ 250 / 89 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    refine le_of_pow_le_pow_left₀ (n := 89) (by norm_num) (by positivity) ?_
    have h : (250 / 89 : ℝ) * ((89 : ℕ) : ℝ) = ((250 : ℕ) : ℝ) := by norm_num
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (250 / 89 : ℝ)) 89, ← Real.rpow_mul (by norm_num), h,
      Real.rpow_natCast]
    norm_num
  linarith

/-- **The reduction with the calls at the dimension of the middle part**,
`⌈⌊√D⌋/g⌉ ⌊√D⌋ = Θ(D^{1-η})`. -/
theorem explicitFrom_mid (M : DetTimeModel) {d η ε γ q δ : ℝ} {D g : ℕ → ℕ}
    (hd0 : 0 < d) (hη0 : 0 < η) (hη1 : η < 1 / 2) (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hδ0 : 0 ≤ δ)
    (hsmall : 3 / 2 * d + δ ≤ 19 / 100)
    (hD : ∀ n, D n = ⌊(n : ℝ) ^ d⌋₊) (hg : ∀ n, g n = ⌈(D n : ℝ) ^ η⌉₊)
    (hhost : HostBound M strassen D g (fun n => pieceSizeNat (D n) (g n) * Nat.sqrt (D n)))
    (hlop : LopClaim M ε γ q) (hthin : d * (1 - η) < ε)
    (hδ : δ < d * min η (min (γ * (1 - η)) (1 / 2 - q * (1 - η)) - η)) : ExplicitFrom M δ 1 := by
  simp only [sub_eq_add_neg, ← min_add_add_right, mul_min_of_nonneg _ _ hd0.le,
    lt_min_iff] at hδ
  obtain ⟨hs1, hs2, hs3⟩ := hδ
  obtain ⟨C, hC, hhost⟩ := hhost
  obtain ⟨CL, Td, hTd, hlop⟩ := hlop
  obtain ⟨T, hT, hhost⟩ := hhost Td hTd
  have hP := eventually_hostParams hd0 (by linarith) hη0 hη1 hD hg
  let Dc n := pieceSizeNat (D n) (g n) * Nat.sqrt (D n)
  have θD := hostThetaD hP
  have θG := (hostThetaG hP).trans (theta_rpow (by intro; positivity) θD η)
  have θDc := (theta_of_bounds (by norm_num : (0 : ℝ) < 1 / 8)
    (f := fun n => (Dc n : ℝ)) (by intro; positivity) (by intro; positivity)
    (hP.mono fun _ p => p.pieceSize_bounds)).trans (theta_rpow (by intro; positivity) θD (1 - η))
  have hQ := callSizes θDc hthin (by nlinarith [mul_pos hd0 hη0])
  have pD : IsBigOPow (fun n => (D n : ℝ)) d := θD.1
  have pG : IsBigOPow (fun n => (g n : ℝ)) (d * η) := θG.1
  have pGi : IsBigOPow (fun n => (g n : ℝ)⁻¹) (-(d * η)) := by
    simpa only [IsBigOPow, Real.rpow_neg (Nat.cast_nonneg _)]
      using θG.inv.1
  have pDi : IsBigOPow (fun n => (Real.sqrt (D n))⁻¹) (-(d / 2)) := by
    simpa only [IsBigOPow, Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg _), mul_neg, mul_one_div]
      using (theta_rpow (by intro; positivity) θD (-(1 / 2))).1
  have pY (r : ℝ) : IsBigOPow (fun n => (Dc n : ℝ) ^ r) (d * (1 - η) * r) :=
    (theta_rpow (by intro; positivity) θDc r).1
  have pLog : IsPowPolylog (fun n => Real.log (Dc n) + 1) 0 :=
    (isPowPolylog_log.add (isPowPolylog_const 1)).mono_left_of_nonneg
      (.of_forall fun n => by linarith [Real.log_natCast_nonneg (Dc n)])
      (hQ.mono fun n Q => add_le_add_left (Real.log_le_log
        (Nat.cast_pos.2 Q.1) Q.2.2) 1)
  have pn : IsBigOPow (fun n : ℕ => (n : ℝ)) 1 := by simpa using isBigOPow_rpow 1
  have pn₂ := isBigOPow_natCast_pow 2
  have pRead : IsBigOPow (fun n => (n : ℝ) ^ 2 / Real.sqrt (D n)) (2 - d / 2) := by
    simpa only [div_eq_mul_inv, sub_eq_add_neg, Nat.cast_ofNat] using pn₂.mul pDi
  have pCap : IsBigOPow (fun n => (queryCap n (D n) : ℝ)) (2 - d / 2) :=
    pRead.mono_left (.of_forall fun _ =>
      abs_le_abs_of_nonneg (Nat.cast_nonneg _) (Nat.floor_le (by positivity)))
  let B (n m w : ℕ) := |CL| * (preBound31 γ n m + (w : ℝ) * queryBound31 q m)
  let F (n : ℕ) := hostCharge strassen n (D n) (g n) (Dc n) C 1 B
  have pF : IsBigOPow F (3 - δ) := by
    apply IsPowPolylog.isBigOPow
    · simp only [F, hostCharge, B, preBound31, queryBound31, termPrime, strassen, termScans, termBuild,
        div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg _), one_mul]
      power_exponents [pD, pG, pGi, pDi, pY (-γ), pY q, pLog, pCap, pn]
    · simp only [add_max, max_lt_iff]
      repeat' apply And.intro
      all_goals norm_num <;> nlinarith [logb_two_seven_lt, mul_nonneg hd0.le (mul_nonneg hq (show 0 ≤ 1 - η by linarith)),
        mul_nonneg hd0.le (show 0 ≤ 1 / 2 - η by linarith)]
  obtain ⟨K, hK⟩ := pF.upperBigOPow
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (hP.and (hQ.and (hK.and (eventually_ge_atTop 3))))
  refine ⟨n₀, max K 0, T, hT, fun n κ u hn hκ hu => ?_⟩
  obtain ⟨P, Q, hF, hn3⟩ := hn₀ n hn
  have hTκ : T n u ≤ κ * F n := calc
    T n u ≤ hostCharge strassen n (D n) (g n) (Dc n) C κ Td :=
      hhost n κ u P.sixteen_le P.le_n P.one_le_g P.g_le_sqrt hκ hu
    _ ≤ hostCharge strassen n (D n) (g n) (Dc n) C κ B := by
      unfold hostCharge
      gcongr
      refine (hlop n (Dc n) _ P.one_le_n Q.1 Q.2.1).trans ?_
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by
        unfold preBound31 queryBound31
        positivity)
    _ ≤ κ * F n := by
      have he : κ * F n - hostCharge strassen n (D n) (g n) (Dc n) C κ B =
          (κ - 1) * hostCharge strassen n (D n) (g n) (Dc n) C 0 B := by
        unfold F hostCharge termScans
        ring
      apply sub_nonneg.mp
      rw [he]
      unfold hostCharge B preBound31 queryBound31 termScans termPrime termBuild strassen
      positivity
  rw [pow_one, ← mul_assoc, mul_comm (max K 0) κ, mul_assoc]
  refine hTκ.trans (mul_le_mul_of_nonneg_left (hF.trans ?_) (by positivity))
  calc
    K * (n : ℝ) ^ (3 - δ) ≤ max K 0 * (n : ℝ) ^ (3 - δ) := by gcongr; exact le_max_left ..
    _ ≤ _ := by
      rw [← mul_assoc]
      exact le_mul_of_one_le_right (by positivity) (Real.one_le_log_natCast_of_three_le hn3)

end ImprovedExponents
