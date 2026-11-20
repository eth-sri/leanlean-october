module

public import NormalizerDelta.Basic

@[expose] public section

/-! The exceptions to h_Δ = h(N), prime by prime. -/

namespace NormalizerLean

variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ}

private theorem dvd_eps_iff_sq {m : ℕ} (hm : 2 ≤ m) (hmN : m ∣ N) :
    m ∣ epsDelta N Δ ↔ ∀ u ∈ Δ, (ZMod.cast (u : ZMod N) : ZMod m)^2 = 1 := by
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 (by have := Nat.le_of_dvd (NeZero.pos N) hmN; omega)
  simp only [dvd_epsDelta_iff, hmN, true_and, ZMod.cast_eq_val]
  refine forall_congr' fun u => imp_congr_right fun _ => ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (ZMod.val_pos.2 u.ne_zero))]
  simp [sub_eq_zero]

private theorem units_sq {m : ℕ} (hm : m ∣ 24) (u : (ZMod m)ˣ) : (u : ZMod m)^2 = 1 := by
  have := Nat.le_of_dvd (by decide : 0 < 24) hm
  revert u
  interval_cases m <;> norm_num at hm <;> decide

private theorem gcd24_eps (Δ : Subgroup (ZMod N)ˣ) : N.gcd 24 ∣ epsDelta N Δ := by
  have hm : 0 < N.gcd 24 := Nat.gcd_pos_of_pos_right _ (by decide)
  by_cases h : N.gcd 24 = 1
  · simp [h]
  rw [dvd_eps_iff_sq (by omega) (Nat.gcd_dvd_left N 24)]
  intro u _
  exact units_sq (Nat.gcd_dvd_right N 24)
    (Units.map (ZMod.castHom (Nat.gcd_dvd_left N 24) _).toMonoidHom u)

private theorem factorization_two_three (i j p : ℕ) :
    (2 ^ i * 3 ^ j).factorization p = if p = 2 then i else if p = 3 then j else 0 := by
  rw [Nat.factorization_mul (by positivity) (by positivity), Nat.prime_two.factorization_pow,
    Nat.prime_three.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> omega

private theorem factorization_24 (p : ℕ) :
    (24 : ℕ).factorization p = if p = 2 then 3 else if p = 3 then 1 else 0 :=
  factorization_two_three 3 1 p

private theorem hPart_fact (N p : ℕ) :
    (hPart N).factorization p = min ((24 : ℕ).factorization p) (N.factorization p / 2) := by
  rw [hPart, factorization_two_three, factorization_24]
  split_ifs <;> simp_all

private theorem factorization_diff {p : ℕ} (hp : p.Prime) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      p ^ (2 * ((24 : ℕ).factorization p + 1)) ∣ N ∧
        p ^ ((24 : ℕ).factorization p + 1) ∣ epsDelta N Δ := by
  have hN := NeZero.ne N
  have hε := (epsDelta_pos (N := N) (Δ := Δ)).ne'
  have hle := (Nat.factorization_le_iff_dvd (Nat.gcd_pos_of_pos_left 24 (NeZero.pos N)).ne' hε).2
    (gcd24_eps Δ) p
  rw [Nat.factorization_gcd hN (by decide)] at hle
  change min (N.factorization p) ((24 : ℕ).factorization p) ≤ _ at hle
  rw [factorization_hDelta, hPart_fact, hp.pow_dvd_iff_le_factorization hN,
    hp.pow_dvd_iff_le_factorization hε]
  omega

private theorem sq9 : ∀ x : ZMod 9, x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by decide

private theorem sq16 : ∀ x : ZMod 16, x ^ 2 = 1 ↔
    (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) x = 1 ∨
    (ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8)) x = -1 := by decide

private theorem failure_at {p : ℕ} (hp : p.Prime) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
      (5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod p u) ∨
      (p = 3 ∧ 3 ^ 4 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 9 u) ∨
      (p = 2 ∧ 2 ^ 8 ∣ N ∧ ∀ u ∈ Δ, IsPmOneMod 8 u) := by
  rw [factorization_diff hp]
  by_cases h5 : 5 ≤ p
  · simp [factorization_24, h5, show p ≠ 2 by omega, show p ≠ 3 by omega]
    intro h
    rw [dvd_eps_iff_sq hp.two_le ((dvd_pow_self p two_ne_zero).trans h)]
    have : Fact p.Prime := ⟨hp⟩
    simp [IsPmOneMod, sq, mul_self_eq_one_iff]
  · have := hp.two_le
    interval_cases p <;> norm_num at hp
    all_goals (rw [factorization_24]; norm_num)
    · intro h
      rw [dvd_eps_iff_sq (by decide) (dvd_trans (by decide : 16 ∣ 256) h)]
      simp only [IsPmOneMod, ZMod.cast_eq_val, sq16, map_natCast]
    · intro h
      rw [dvd_eps_iff_sq (by decide) (dvd_trans (by decide : 9 ∣ 81) h)]
      simp [IsPmOneMod, sq9]

/-- The exceptional moduli are p, 9 and 8. -/
theorem hDelta_eq_hPart_iff (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ) :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  rw [← not_iff_not, not_not, Nat.eq_iff_prime_padicValNat_eq _ _ (hDelta_pos N Δ).ne'
    (by unfold hPart; positivity)]
  push Not
  rw [exists_congr fun p => and_congr_right fun hp => by
    rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp, failure_at hp]]
  simp [and_or_left, exists_or, @and_left_comm (Nat.Prime _) (_ = _) _, Nat.prime_three, Nat.prime_two]

end NormalizerLean
