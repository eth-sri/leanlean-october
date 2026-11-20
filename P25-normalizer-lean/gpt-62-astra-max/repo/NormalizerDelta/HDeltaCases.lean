module

public import NormalizerLean.Basic

@[expose] public section

/-! Compare the defining exponents of `hDelta` with the bound coming from 24. For each
prime p it suffices to test the least power of p that does not divide 24. -/

namespace NormalizerLean

variable {N : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ}

private lemma dvd_eps_mod {m : ℕ} (hm : m ∣ N) : m ∣ epsDelta N Δ ↔
    ∀ u ∈ Δ, ((u : ZMod N).val : ZMod m) ^ 2 = 1 := by
  rcases eq_or_ne N 1 with rfl | h
  · obtain rfl := Nat.eq_one_of_dvd_one hm; simp; exact fun _ _ => Subsingleton.elim ..
  have := ZMod.nontrivial_iff.mpr h
  simp only [dvd_epsDelta_iff, hm, true_and]
  refine forall₂_congr fun u _ => ?_
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (Nat.one_le_pow _ _ (ZMod.val_pos.mpr u.ne_zero)), sub_eq_zero]
  push_cast; rfl

/-- Every unit modulo a divisor of 24 squares to one. -/
private lemma gcd24_dvd : N.gcd 24 ∣ epsDelta N Δ := by
  apply (dvd_eps_mod (Nat.gcd_dvd_left ..)).mpr
  intro u _
  rw [← ZMod.cast_eq_val, ← ZMod.unitsMap_val (Nat.gcd_dvd_left N 24)]
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective (Nat.gcd_dvd_right N 24) (ZMod.unitsMap (Nat.gcd_dvd_left N 24) u)
  have small : ∀ v : (ZMod 24)ˣ, v ^ 2 = 1 := by decide
  rw [← hv, ← Units.val_pow_eq_pow_val, ← map_pow, small, map_one, Units.val_one]

private def at23 (i j p : ℕ) := if p = 2 then i else if p = 3 then j else 0

private lemma factor23 (i j p : ℕ) : (2 ^ i * 3 ^ j).factorization p =
    at23 i j p := by
  simp [at23, Nat.prime_two.factorization, Nat.prime_three.factorization, Finsupp.single_apply]
  split_ifs <;> omega

/-- A discrepancy at p is detected modulo the first power of p beyond the 24-bound. -/
private lemma bad_prime {p q : ℕ} (hp : p.Prime) (hq : q = p ^ (at23 3 1 p + 1)) :
    (hDelta N Δ).factorization p ≠ (hPart N).factorization p ↔
    q ^ 2 ∣ N ∧ ∀ u ∈ Δ, ((u : ZMod N).val : ZMod q) ^ 2 = 1 := by
  have hN := NeZero.ne N
  have ge := (Nat.factorization_le_iff_dvd (by positivity) (NeZero.ne _)).mpr (gcd24_dvd (Δ := Δ)) p
  rw [Nat.factorization_gcd hN (by decide), Finsupp.inf_apply, show (24 : ℕ) = 2 ^ 3 * 3 ^ 1 by decide, factor23] at ge
  trans q ^ 2 ∣ N ∧ q ∣ epsDelta N Δ
  · rw [hq, ← pow_mul, hPart, factor23, factorization_hDelta, hp.pow_dvd_iff_le_factorization hN, hp.pow_dvd_iff_le_factorization (NeZero.ne _)]
    unfold at23 at *; split_ifs at * <;> subst_vars <;> omega
  · exact and_congr_right fun h => dvd_eps_mod ((dvd_pow_self q two_ne_zero).trans h)

private lemma at16 : ∀ y : ZMod 16, y ^ 2 = 1 ↔
    let z := ZMod.castHom (by decide : 8 ∣ 16) (ZMod 8) y; z = 1 ∨ z = -1 := by decide

variable (N Δ) in
theorem hDelta_eq_hPart_iff :
    hDelta N Δ = hPart N ↔
      ¬ ((∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ^ 2 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod p d) ∨
        (3 ^ 4 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 9 d) ∨
        (2 ^ 8 ∣ N ∧ ∀ d ∈ Δ, IsPmOneMod 8 d)) := by
  have two := bad_prime (q := 16) (Δ := Δ) Nat.prime_two rfl
  have three := bad_prime (q := 9) (Δ := Δ) Nat.prime_three rfl
  have nine : ∀ y : ZMod 9, y ^ 2 = 1 ↔ y = 1 ∨ y = -1 := by decide
  simp only [at16, map_natCast] at two
  simp only [nine] at three
  have other (p : ℕ) (hp : p.Prime) (h : 5 ≤ p) :=
    letI := Fact.mk hp
    (bad_prime (q := p) (Δ := Δ) hp (by unfold at23; split_ifs <;> first | omega | simp)).trans
      (and_congr_right' (forall₂_congr fun _ _ => sq_eq_one_iff))
  simp only [IsPmOneMod, ZMod.cast_eq_val] at *
  rw [Nat.eq_iff_prime_padicValNat_eq _ _ (NeZero.ne _) (by unfold hPart; positivity)]
  grind [Nat.factorization_def, Nat.prime_two, Nat.prime_three, Nat.Prime.five_le_of_ne_two_of_ne_three]

end NormalizerLean
