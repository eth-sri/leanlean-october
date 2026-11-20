module

public import DedekindZetaZeroFree.Moments.Principal.EulerProducts.Poisson.ShellMajorants

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.BadPrimeShellSeries

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.EulerDomain
open DedekindZetaZeroFree.LocalFiniteSums
open DedekindZetaZeroFree.CorrectionFactors (V)
open DedekindZetaZeroFree.Quantitative.EulerShellMargin (shellExponent)
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
    {A : SArithmeticData F} {σ : F →+* ℂ}
    {η : RayClassCharacter F A.modulus} {hS : A.ContainsTraceBadPlaces}

private alias Q_pos := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.Q_pos

private alias two_le_Q := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.two_le_Q

private alias norm_qPower := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.norm_qPower

private alias norm_vartheta := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.norm_vartheta

private alias norm_gammaTwo := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.norm_gammaTwo

section

variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (j : Fin 6)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (e : Fin 2) (l k m : ℕ)

theorem seriesTerm_eq_zero_of_two_le (ht : 0 < e.val + 3 * l) (hk : 2 ≤ k) (ξ w z : ℂ) :
    seriesTerm C p j θ e l k m ξ w z = 0 := by
  simp only [seriesTerm, Ctk_eq_zero_of_two_le C p _ _ _ ht hk, mul_zero, zero_mul]

theorem norm_seriesTerm_le_Ctk (x : Coordinates) :
    ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
      ‖Ctk C p (e.val + 3 * l) k (j.val + 6 * m)‖ *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) := by apply @DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.norm_series_le <;> assumption

end

alias norm_Ctk_le_shell := DedekindZetaZeroFree.CorrectionFactors.BadPrimeEstimates.shell_bound

section

variable (C : A.GeneralArithmeticContext σ η hS) (p : ExteriorPrime A) (j : Fin 6)

theorem norm_seriesTerm_le_rpow_shellExponent (θ : {θ : ℂ // ‖θ‖ = 1})
    (e : Fin 2) (l k m : ℕ) (ht : 0 < e.val + 3 * l) (hk : k ≤ 1) (x : Coordinates) :
    ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
      (Q p) ^ shellExponent x.1.re x.2.1.re x.2.2.re e.val k l m := by
  calc _
      ≤ ‖Ctk C p (e.val + 3 * l) k (j.val + 6 * m)‖ *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) := norm_seriesTerm_le_Ctk C p j θ e l k m x
    _ ≤ (Q p) ^ (((e.val + 3 * l : ℕ) : ℝ) + (k : ℝ) / 2) *
        (Q p) ^ (-(e.val : ℝ) * (1 / 2 + x.1.re) -
          (l : ℝ) * (1 + 3 * x.1.re) - (k : ℝ) * x.2.1.re -
          6 * (m : ℝ) * x.2.2.re) :=
      mul_le_mul_of_nonneg_right (norm_Ctk_le_shell C p _ _ _ ht hk)
        (Real.rpow_nonneg (Q_pos p).le _)
    _ = (Q p) ^ shellExponent x.1.re x.2.1.re x.2.2.re e.val k l m := by
      rw [← Real.rpow_add (Q_pos p)]
      congr 1
      unfold shellExponent
      push_cast
      ring

theorem seriesTerm_leading (hj : j.val ≠ 0)
    (θ : {θ : ℂ // ‖θ‖ = 1}) (k m : ℕ) (ξ w z : ℂ) :
    seriesTerm C p j θ 0 0 k m ξ w z = if k = 0 then V p z ^ m else 0 := by
  by_cases hk : k = 0
  · subst k
    simp only [seriesTerm, Fin.val_zero, pow_zero, Nat.mul_zero, Nat.add_zero,
      Int.ofNat_zero, sub_zero, zero_sub, zpow_zero, one_mul, Ctk_zero_zero, zero_mul,
      sub_self, sub_zero, if_true]
    rw [CorrectionFactors.V, qPower, qPower, ← Complex.exp_nat_mul]
    norm_num only [mul_zero, neg_zero, zpow_zero, one_mul, mul_one, Nat.cast_zero,
      zero_mul, sub_zero, zero_sub]
    congr 1
    push_cast
    ring
  · have hJ : j.val + 6 * m ≠ 0 := by omega
    unfold seriesTerm
    rw [show (0 : Fin 2).val + 3 * 0 = 0 by rfl,
      Ctk_zero_pos C p k _ (Nat.pos_of_ne_zero hk), if_neg hJ]
    simp only [mul_zero, zero_mul, if_neg hk]

end

def weight (ρ : ℝ) (i : Fin 2 × ℕ × ℕ × ℕ) : ℝ :=
  2 * ρ ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ρ ^ i.2.2.2

theorem weight_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (i : Fin 2 × ℕ × ℕ × ℕ) : 0 ≤ weight ρ i := by
  unfold weight
  positivity

theorem weight_summable {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) : Summable (weight ρ) := by
  have hr : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one hρ0 hρ1
  have hh : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hkm := hh.mul_of_nonneg hr (fun n => by positivity) (fun n => by positivity)
  have hlkm := hr.mul_of_nonneg hkm (fun n => by positivity) (fun n => by dsimp; positivity)
  have h := (Summable.of_finite : Summable (fun _ : Fin 2 => (2 : ℝ))).mul_of_nonneg hlkm
    (fun _ => by norm_num) (fun n => by dsimp; positivity)
  change Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
    2 * ρ ^ i.2.1 * (1 / 2 : ℝ) ^ i.2.2.1 * ρ ^ i.2.2.2)
  simpa only [mul_assoc] using h

section

variable (p : ExteriorPrime A)

private lemma rpow_le_rho (b : ℝ) (hb : 0 ≤ b) (n : ℕ) :
    (Q p) ^ (-(b * n)) ≤ ((2 : ℝ) ^ (-b)) ^ n := by
  calc _ ≤ (2 : ℝ) ^ (-(b * n)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p)
          (by nlinarith [mul_nonneg hb (Nat.cast_nonneg n)])
    _ = ((2 : ℝ) ^ (-b)) ^ n := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        congr 1
        ring

private lemma decay_split (a b : ℝ) (hb : 0 ≤ b) (l m : ℕ) :
    (Q p) ^ (-a - b * (l : ℝ) - b * (m : ℝ)) ≤
      (Q p) ^ (-a) * ((2 : ℝ) ^ (-b)) ^ l * ((2 : ℝ) ^ (-b)) ^ m := by
  have hq := Q_pos p
  have h2 : -a - b * (l : ℝ) - b * (m : ℝ) = -a + -(b * l) + -(b * m) := by ring
  rw [h2, Real.rpow_add hq, Real.rpow_add hq]
  exact mul_le_mul (mul_le_mul_of_nonneg_left (rpow_le_rho p b hb l)
    (Real.rpow_nonneg hq.le _)) (rpow_le_rho p b hb m) (Real.rpow_nonneg hq.le _)
    (by positivity)

theorem norm_V_le (b : ℝ) (hb : 0 ≤ b) (z : ℂ) (hz : b ≤ 6 * z.re) :
    ‖V p z‖ ≤ (2 : ℝ) ^ (-b) := by
  rw [CorrectionFactors.V, norm_qPower]
  have he : (-6 * z).re = -(6 * z.re) := by simp
  rw [he]
  calc _ ≤ (2 : ℝ) ^ (-(6 * z.re)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (two_le_Q p) (by linarith)
    _ ≤ (2 : ℝ) ^ (-b) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

end

private lemma rho_pos (b : ℝ) : 0 < (2 : ℝ) ^ (-b) := Real.rpow_pos_of_pos (by norm_num) _

private lemma rho_lt_one (b : ℝ) (hb : 0 < b) : (2 : ℝ) ^ (-b) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem norm_seriesTerm_le_weight (C : A.GeneralArithmeticContext σ η hS)
    (p : ExteriorPrime A) (j : Fin 6) (hj : j.val ≠ 0) (θ : {θ : ℂ // ‖θ‖ = 1})
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (x : Coordinates) (hv : b ≤ 6 * x.2.2.re)
    (hshell : ∀ e k l m : ℕ, e ≤ 1 → k ≤ 1 → 0 < e + 3 * l →
      shellExponent x.1.re x.2.1.re x.2.2.re e k l m ≤ -a - b * (l : ℝ) - b * (m : ℝ))
    (i : Fin 2 × ℕ × ℕ × ℕ) :
    ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
        weight ((2 : ℝ) ^ (-b)) i ∧
      (0 < i.1.val + 3 * i.2.1 →
        ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
          (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) i) := by
  obtain ⟨e, l, k, m⟩ := i
  have hρ := rho_pos b
  have hw := weight_nonneg hρ.le (e, l, k, m)
  have hpos : 0 < e.val + 3 * l →
      ‖seriesTerm C p j θ e l k m x.1 x.2.1 x.2.2‖ ≤
        (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) (e, l, k, m) := by
    intro ht
    by_cases hk : k ≤ 1
    · have hQ0 : 0 ≤ (Q p) ^ (-a) := Real.rpow_nonneg (Q_pos p).le _
      refine ((norm_seriesTerm_le_rpow_shellExponent C p j θ e l k m ht hk x).trans ((Real.rpow_le_rpow_of_exponent_le (by linarith [two_le_Q p])
        (hshell e.val k l m (Nat.lt_succ_iff.mp e.isLt) hk ht)).trans (decay_split p a b hb.le l m))).trans ?_
      have : ((Q p) ^ (-a) * ((2 : ℝ) ^ (-b)) ^ l * ((2 : ℝ) ^ (-b)) ^ m) ≤
          (Q p) ^ (-a) * weight ((2 : ℝ) ^ (-b)) (e, l, k, m) := by
        unfold weight
        simp only
        interval_cases k <;> simp only [pow_zero, pow_one] <;>
          nlinarith [mul_nonneg (mul_nonneg hQ0 (pow_nonneg hρ.le l)) (pow_nonneg hρ.le m)]
      exact this
    · have hk2 : 2 ≤ k := by omega
      rw [seriesTerm_eq_zero_of_two_le C p j θ e l k m ht hk2, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (Q_pos p).le _) hw
  refine ⟨?_, hpos⟩
  by_cases ht : 0 < e.val + 3 * l
  · exact (hpos ht).trans (mul_le_of_le_one_left hw (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [two_le_Q p]) (by linarith)))
  · have he : e = 0 := Fin.ext (by simp; omega)
    have hl : l = 0 := by omega
    subst he hl
    rw [seriesTerm_leading C p j hj θ]
    split_ifs with hk
    · subst hk
      rw [norm_pow]
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_V_le p b hb.le _ hv) m
      simp only [weight, pow_zero, mul_one]
      nlinarith [pow_nonneg hρ.le m]
    · simpa using hw

section

variable (p : ExteriorPrime A) (z : ℂ)

def baseline (i : Fin 2 × ℕ × ℕ × ℕ) : ℂ :=
  if i.1 = 0 ∧ i.2.1 = 0 ∧ i.2.2.1 = 0 then V p z ^ i.2.2.2 else 0

theorem baseline_norm_le (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hV : ‖V p z‖ ≤ ρ) (i : Fin 2 × ℕ × ℕ × ℕ) : ‖baseline p z i‖ ≤ weight ρ i := by
  unfold baseline
  split_ifs with h
  · rcases h with ⟨he, hl, hk⟩
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) hV i.2.2.2
    simp only [weight, he, hl, hk, pow_zero, mul_one]
    nlinarith [pow_nonneg hρ i.2.2.2]
  · simp only [norm_zero]
    exact weight_nonneg hρ i

theorem one_sub_V_mul_tsum_baseline (hV : ‖V p z‖ < 1) :
    (1 - V p z) * (∑' i, baseline p z i) = 1 := by
  have hs : Summable (baseline p z) := by
    refine Summable.of_norm_bounded (weight_summable (norm_nonneg _) hV) ?_
    exact baseline_norm_le p z _ (norm_nonneg _) le_rfl
  rw [hs.tsum_prod]
  have hs0 := hs.prod_factor (0 : Fin 2)
  simp only [baseline]
  rw [tsum_eq_single (0 : Fin 2)]
  · simp only [ite_true]
    rw [show (∑' c : ℕ × ℕ × ℕ, if True ∧ c.1 = 0 ∧ c.2.1 = 0 then V p z ^ c.2.2 else 0) =
      ∑' l : ℕ, ∑' c : ℕ × ℕ, baseline p z (0, l, c) by
        simpa only [baseline, Fin.val_zero] using hs0.tsum_prod]
    simp only [baseline, true_and]
    rw [tsum_eq_single (0 : ℕ)]
    · simp only [ite_true]
      rw [show (∑' c : ℕ × ℕ, if True ∧ c.1 = 0 then V p z ^ c.2 else 0) =
        ∑' k : ℕ, ∑' m : ℕ, baseline p z (0, 0, k, m) by
          simpa only [baseline, true_and] using (hs0.prod_factor (0 : ℕ)).tsum_prod]
      simp only [baseline, true_and]
      rw [tsum_eq_single (0 : ℕ)]
      · simp only [ite_true]
        exact (summable_geometric_of_norm_lt_one hV).one_sub_mul_tsum_pow
      · intro k hk
        simp [hk]
    · intro l hl
      simp [hl]
  · intro e he
    simp [he]

end

theorem seriesTerm_majorant_margin (δ : ℝ) (hδ : 0 < δ) :
    ∃ (ρ δ₀ : ℝ), 0 < ρ ∧ ρ < 1 ∧ 0 < δ₀ ∧ Summable (weight ρ) ∧
      ∀ (C : A.GeneralArithmeticContext σ η hS)
        (p : ExteriorPrime A) (j : Fin 6), j.val ≠ 0 → ∀ (θ : {θ : ℂ // ‖θ‖ = 1}),
        ∀ x ∈ OmegaStarMargin δ, ∀ i : Fin 2 × ℕ × ℕ × ℕ,
          ‖V p x.2.2‖ ≤ ρ ∧
          ‖(1 - V p x.2.2) *
            seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤ 2 * weight ρ i ∧
          (0 < i.1.val + 3 * i.2.1 →
            ‖seriesTerm C p j θ i.1 i.2.1 i.2.2.1 i.2.2.2 x.1 x.2.1 x.2.2‖ ≤
              (Q p) ^ (-δ₀) * weight ρ i) := by
  obtain ⟨δ₀, δ', hδ₀, hδ', hsh⟩ := EulerShellMargin.shellExponent_le_margin δ hδ
  set b : ℝ := min δ' δ with hbdef
  have hb : 0 < b := lt_min hδ' hδ
  have hbδ' : b ≤ δ' := min_le_left _ _
  have hbδ : b ≤ δ := min_le_right _ _
  refine ⟨(2 : ℝ) ^ (-b), δ₀, rho_pos b, rho_lt_one b hb, hδ₀,
    weight_summable (rho_pos b).le (rho_lt_one b hb), ?_⟩
  intro C p j hj θ x hx i
  have hv : b ≤ 6 * x.2.2.re := by
    obtain ⟨_, _, h3, _⟩ := hx
    linarith
  have hshell : ∀ e k l m : ℕ, e ≤ 1 → k ≤ 1 → 0 < e + 3 * l →
      shellExponent x.1.re x.2.1.re x.2.2.re e k l m ≤ -δ₀ - b * (l : ℝ) - b * (m : ℝ) := by
    intro e k l m he hk ht
    have h := hsh x hx e k l m he hk ht
    have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg l
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (sub_nonneg.mpr hbδ') hl, mul_nonneg (sub_nonneg.mpr hbδ') hm]
  obtain ⟨h1, h2⟩ := norm_seriesTerm_le_weight C p j hj θ δ₀ b hδ₀.le hb x hv hshell i
  have hVn := norm_V_le p b hb.le _ hv
  refine ⟨hVn, ?_, h2⟩
  have hV2 : ‖1 - V p x.2.2‖ ≤ 2 := by
    calc ‖1 - V p x.2.2‖ ≤ ‖(1 : ℂ)‖ + ‖V p x.2.2‖ := norm_sub_le _ _
      _ ≤ 2 := by
        have := rho_lt_one b hb
        simp only [norm_one]; linarith
  rw [norm_mul]
  exact mul_le_mul hV2 h1 (norm_nonneg _) (by norm_num)

end

end DedekindZetaZeroFree.Quantitative.BadPrimeShellSeries
