module

public import NormalizerLean.Defs

@[expose] public section

/-! Basic arithmetic and matrix identities. In particular, the defining minimum of valuations
gives `nDelta N Δ * hDelta N Δ ^ 2 = N`. -/

open Matrix CongruenceSubgroup

namespace NormalizerLean

/-- Integral special linear matrix with specified entries. -/
def mkSL (a b c d : ℤ) (h : a * d - b * c = 1) : SL₂ℤ := ⟨!![a, b; c, d], by simpa [det_fin_two_of]⟩

macro "entries" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j))

@[simp] lemma ofZ_mkSL (a b c d) (det) : (ofZ (mkSL a b c d det) : Mat₂ ℝ) = !![(a : ℝ), b; c, d] := by entries <;> rfl

theorem coe_projSL {A : Mat₂ ℝ} (h : 0 < A.det) : (projSL A : Mat₂ ℝ) = (Real.sqrt A.det)⁻¹ • A := by simp [projSL, h]

variable {N : ℕ} {Δ : Subgroup (ZMod N)ˣ}

lemma gamma0_dvd {g : SL₂ℤ} : g ∈ Gamma0 N ↔ (N : ℤ) ∣ g 1 0 := ZMod.intCast_zmod_eq_zero_iff_dvd ..

lemma lift_unit (u : (ZMod N)ˣ) : ∃ x y : ℤ, x * (u : ZMod N).val - y * N = 1 := by
  obtain ⟨x, y, h⟩ : IsCoprime ((u : ZMod N).val : ℤ) N := by
    simpa [Int.isCoprime_iff_gcd_eq_one] using ZMod.val_coe_unit_coprime u
  exact ⟨x, -y, by linear_combination h⟩

variable [NeZero N]

lemma dvd_epsDelta_iff {m : ℕ} : m ∣ epsDelta N Δ ↔ m ∣ N ∧ ∀ u ∈ Δ, m ∣ (u : ZMod N).val ^ 2 - 1 := by
  classical simp [epsDelta, Nat.dvd_gcd_iff, Finset.dvd_gcd_iff]

instance : NeZero (epsDelta N Δ) := ⟨(Nat.gcd_pos_of_pos_left _ (NeZero.pos N)).ne'⟩

lemma factorization_hDelta (p : ℕ) : (hDelta N Δ).factorization p = min ((epsDelta N Δ).factorization p) (N.factorization p / 2) := by
  simp only [hDelta, Nat.factorization_prod_apply (fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primeFactors hq).ne_zero)]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(Nat.prime_of_mem_primeFactors hq).factorization_pow, Finsupp.single_apply]), Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp [N.factorization.notMem_support_iff.mp h]

variable (N Δ)

instance : NeZero (hDelta N Δ) :=
  ⟨(Finset.prod_pos fun _ h => pow_pos (Nat.pos_of_mem_primeFactors h) _).ne'⟩

/-- The square divisor used to define the reduced level is exact. -/
lemma nDelta_mul : nDelta N Δ * hDelta N Δ ^ 2 = N := by
  apply Nat.div_mul_cancel
  apply (Nat.factorization_le_iff_dvd (pow_ne_zero _ (NeZero.ne _)) (NeZero.ne N)).mp
  intro p
  simp [Nat.factorization_pow, factorization_hDelta]
  omega

instance : NeZero (nDelta N Δ) :=
  ⟨left_ne_zero_of_mul ((nDelta_mul N Δ).trans_ne (NeZero.ne N))⟩

variable {N} in
lemma cast_level {R : Type*} [Semiring R] : (N : R) = (nDelta N Δ : R) * (hDelta N Δ : R) ^ 2 := by
  rw [← Nat.cast_pow, ← Nat.cast_mul, nDelta_mul]

end NormalizerLean
