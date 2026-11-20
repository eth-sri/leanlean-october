module

public import NormalizerLean.Basic

@[expose] public section

/-! The prime-by-prime part of the generalized Newman bound. -/

namespace NormalizerLean

private lemma local_dvd {m : ℕ} [NeZero m] (x : ℤ) : (m : ℤ) ∣ x ↔
    ∀ p : ℕ, p.Prime → emultiplicity (p : ℤ) (m : ℤ) ≤ emultiplicity (p : ℤ) x := by
  rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le (NeZero.ne m)]
  simp only [Nat.prime_iff, Int.natCast_emultiplicity, Int.emultiplicity_natAbs]

/-- Integral content one. -/
def Primitive (a b c d : ℤ) := ∀ k : ℤ, k ∣ a ∧ k ∣ b ∧ k ∣ c ∧ k ∣ d → k ∣ 1

/-- Recover global divisibility of the primitive entries and of their determinant. -/
lemma newman_divisors {N e : ℕ} [NeZero N] {Δ : Subgroup (ZMod N)ˣ} {a b c d : ℤ}
    (he : 0 < e) (det : a * d - b * c = e)
    (prim : Primitive a b c d) :
    let n := nDelta N Δ; let h := hDelta N Δ; let s := epsDelta N Δ
    (e : ℤ) ∣ a * a → (e : ℤ) ∣ (n : ℤ) * (b * b) → (e : ℤ) * n ∣ c * c → (e : ℤ) ∣ d * d →
    (e : ℤ) * h ∣ (s : ℤ) * (a * b) →
    (e : ℤ) * n * h ∣ (s : ℤ) * (c * d) →
    e ∣ n ∧ (n : ℤ) ∣ c ∧ (e : ℤ) ∣ a ∧ (e : ℤ) ∣ d := by
  intro n h s A B C D X Z
  have := NeZero.mk he.ne'
  rw [← Int.natCast_dvd_natCast]
  simp only [local_dvd, ← forall_and]
  intro p hp
  have v {x y : ℤ} (z : x ∣ y) := emultiplicity_le_emultiplicity_of_dvd_right (a := (p : ℤ)) z
  have f (m : ℕ) [NeZero m] : emultiplicity (p : ℤ) (m : ℤ) = m.factorization p := by
    rw [Int.natCast_emultiplicity, Nat.factorization_def _ hp, padicValNat_eq_emultiplicity_of_ne_one hp.ne_one (NeZero.ne _)]
  have hn := DFunLike.congr_fun (Nat.factorization_mul (NeZero.ne n) (pow_ne_zero 2 (NeZero.ne h))) p
  rw [nDelta_mul] at hn
  simp [Nat.factorization_pow] at hn
  have hp' := Nat.prime_iff_prime_int.mp hp
  have P := mt (prim p) hp'.not_dvd_one
  simp only [not_and_or, ← emultiplicity_eq_zero] at P
  have E := min_le_emultiplicity_add (p := (p : ℤ)) (a := a * d) (b := -(b * c))
  rw [← sub_eq_add_neg, det, emultiplicity_neg, min_le_iff] at E
  -- If the minimum defining h is not attained at s, the reduced level
  -- has at most one remaining factor of p.
  have hs : h.factorization p = s.factorization p ∨ n.factorization p ≤ 1 := by
    have : h.factorization p = min (s.factorization p) _ := factorization_hDelta (Δ := Δ) p
    omega
  -- Finite valuations are natural numbers. Allowing infinity on the four entries
  -- treats zero coefficients without separate divisibility lemmas.
  replace A := v A; replace B := v B; replace C := v C; replace D := v D
  replace X := v X; replace Z := v Z
  simp only [emultiplicity_mul hp', f] at A B C D X Z E ⊢
  set ν := emultiplicity (p : ℤ)
  generalize ν a = va, ν b = vb, ν c = vc, ν d = vd at *
  clear * - A B C D X Z E P hs
  enat_to_nat <;> try simp_all
  all_goals omega

end NormalizerLean
