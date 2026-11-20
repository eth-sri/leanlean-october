module

public import NormalizerDelta.NewmanDelta
public import NormalizerDelta.IndexDelta

@[expose] public section

/-! Atkin–Lehner products at reduced level, their diagonal conjugates, and the normalizer bound. -/

open Matrix

namespace NormalizerLean

/-- In SL₂ the shape of the matrix already forces the Atkin–Lehner determinant equation. -/
private lemma al_of_matrix {n q : ℕ} {g : SL₂ℝ} (a b c d : ℤ)
    (m : (g : Mat₂ ℝ) = (Real.sqrt q)⁻¹ • !![(q : ℝ) * a, b; n * c, q * d]) : IsAtkinLehner n q g := by
  refine ⟨a, b, c, d, ?_, m⟩
  have H := g.2
  rw [m, det_smul, det_fin_two_of, Fintype.card_fin, inv_pow, Real.sq_sqrt (by positivity)] at H
  rify; linear_combination inv_injective (inv_eq_of_mul_eq_one_left H)

abbrev AL (n : ℕ) (g : SL₂ℝ) := ∃ q : ℕ, q ∣ n ∧ IsAtkinLehner n q g

/-- Write the two parameters as `u*G`, `v*G` with coprime `u`, `v`. Their product
has parameter `u*v`; its coefficients use the complementary factor of their lcm. -/
private lemma al_mul {n : ℕ} [NeZero n] {g g' : SL₂ℝ} : AL n g → AL n g' → AL n (g * g') := by
  rintro ⟨q, hq, a, b, c, d, -, M⟩ ⟨q', hq', x, y, z, w, -, M'⟩
  obtain ⟨G, u, v, hG, co, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_left q' (Nat.pos_of_dvd_of_pos hq (NeZero.pos n)))
  obtain ⟨L, rfl⟩ : u * v * G ∣ n := by simpa only [Nat.lcm_mul_right, co.lcm_eq_mul] using Nat.lcm_dvd hq hq'
  refine ⟨u * v, ⟨_, mul_assoc ..⟩, al_of_matrix
    (G * a * x + L * b * z) (u * a * y + v * b * w) (v * c * x + u * d * z) (L * c * y + G * d * w) ?_⟩
  change (g : Mat₂ ℝ) * (g' : Mat₂ ℝ) = _
  rw [M, M', Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  entries <;> simp [Real.sqrt_mul (Nat.cast_nonneg _)] <;>
    field_simp <;> simp [Real.sq_sqrt, mul_assoc, mul_left_comm, mul_comm]

private lemma mem_plus {n : ℕ} [NeZero n] {g : SL₂ℝ} : g ∈ Gamma0Plus n ↔ AL n g := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, one_dvd _, 1, 0, 0, 1, by simp, by entries <;> simp⟩
  | mul _ _ _ _ h k => exact al_mul h k
  | inv g _ ih =>
    obtain ⟨q, hq, a, b, c, d, H, M⟩ := ih
    exact ⟨q, hq, d, -b, -c, a, by linear_combination H, by rw [coe_inv_scaled M]; entries <;> simp⟩

variable (N : ℕ) [NeZero N] (Δ : Subgroup (ZMod N)ˣ)

local notation "h" => hDelta N Δ
local notation "n" => nDelta N Δ

/-- Undo the diagonal conjugation, cancelling the scalar factors from `projSL`. -/
lemma diagonal_conj (g : SL₂ℝ) (s q a b c d : ℝ) :
    ((MulAut.conj (projSL !![(h : ℝ), 0; 0, 1]) g : SL₂ℝ) : Mat₂ ℝ) = s • !![q * a, b; n * c, q * d] ↔
    (g : Mat₂ ℝ) = s • !![a * q, b / h; N * c / h, d * q] := by
  have S := coe_projSL (show 0 < (!![(h : ℝ), 0; 0, 1] : Mat₂ ℝ).det by simpa [det_fin_two_of] using NeZero.pos h)
  simp only [MulAut.conj_apply, ← Matrix.ext_iff, Fin.forall_fin_two]
  simp [S, coe_inv_scaled S, det_fin_two_of, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, cast_level Δ]
  have := NeZero.ne (h : ℝ)
  field_simp; simp [sq]; grind

lemma mem_MDelta {g : SL₂ℝ} : g ∈ MDelta N Δ ↔ AL n (MulAut.conj (projSL !![(h : ℝ), 0; 0, 1]) g) := by
  rw [MDelta, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]; exact mem_plus

theorem coe_MDelta : (MDelta N Δ : Set SL₂ℝ) = {g | IsNewmanFormH N h g} := by
  ext g; change g ∈ MDelta N Δ ↔ _; rw [mem_MDelta]
  constructor
  · rintro ⟨q, hq, a, b, c, d, H, M⟩
    refine ⟨a, b, c, d, q, Nat.pos_of_dvd_of_pos hq (NeZero.pos _), hq, by simpa [nDelta, mul_assoc, mul_left_comm, mul_comm] using H, 1, Or.inl rfl, ?_⟩
    simpa only [one_div] using (diagonal_conj N Δ ..).mp M
  · rintro ⟨a, b, c, d, q, _, hd, _, s, hs, M⟩
    refine ⟨q, hd, ?_⟩
    rcases hs with rfl | rfl <;> [apply al_of_matrix a b c d; apply al_of_matrix (-a) (-b) (-c) (-d)] <;>
      rw [diagonal_conj N Δ, M] <;> entries <;> simp <;> ring

theorem normG_GammaDeltaR_le_MDelta : NormG (GammaDeltaR N Δ) ≤ MDelta N Δ :=
  fun _ hg => (Set.ext_iff.mp (coe_MDelta N Δ) _).mpr (newman_delta hg)

theorem Gamma0R_le_MDelta : Gamma0R N ≤ MDelta N Δ := gamma0_normalizes.trans (normG_GammaDeltaR_le_MDelta N Δ)

end NormalizerLean
