module

public import NormalizerDelta.MDelta
public import NormalizerDelta.Hermite

@[expose] public section

/-! Projective Hermite representatives for the right cosets, and uniqueness. -/

open Matrix CongruenceSubgroup

namespace NormalizerLean

/-- The product of an integral determinant-one matrix and a Hermite matrix. -/
scoped notation "σH " r:arg a:arg b:arg d:arg => (ofZ r : Mat₂ ℝ) * hermMat a b d

private lemma left_sigma (q r : SL₂ℤ) (a b d : ℕ) :
    (ofZ q : Mat₂ ℝ) * σH r a b d = σH (q * r) a b d := by
  simp [ofZ, Matrix.mul_assoc]

variable {N : ℕ}

private lemma eq_proj {g : SL₂ℝ} {s : ℝ} {A : Mat₂ ℝ} (hs : 0 < s) (M : (g : Mat₂ ℝ) = s • A) : g = projSL A := by
  have E := g.2
  rw [M, det_smul, Fintype.card_fin] at E
  have hd := pos_of_mul_pos_right (E.symm ▸ zero_lt_one) (sq_nonneg s)
  have eq : s * Real.sqrt A.det = 1 := by simpa [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le] using congrArg Real.sqrt E
  apply Subtype.ext; rw [coe_projSL hd, M, inv_eq_of_mul_eq_one_left eq]

lemma pos_det (r : SL₂ℤ) {a b d : ℕ} (H : IsHermiteN N a b d) : 0 < (σH r a b d).det := by
  rw [det_mul, (ofZ r).2]; simp [hermMat, det_fin_two_of, H.1, H.2.1, mul_pos_iff_of_pos_left]

section
variable [NeZero N] (Δ : Subgroup (ZMod N)ˣ) {R : Set SL₂ℤ} (hR : IsGamma0Reps N R) {g : SL₂ℝ}
include hR

local notation "n" => nDelta N Δ
local notation "h" => hDelta N Δ

/-- Use the positive Atkin–Lehner scaling so that projection of σH chooses
the actual coset representative, not just a representative up to sign. -/
lemma representative (hg : g ∈ MDelta N Δ) : ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧
    projSL (σH r a b d) * g⁻¹ ∈ Gamma0R N := by
  obtain ⟨e, hen, a, b, c, d, det, M⟩ := (mem_MDelta N Δ).mp hg
  have hh := NeZero.pos h
  rw [diagonal_conj N Δ] at M
  have he := Nat.pos_of_dvd_of_pos hen (NeZero.pos n)
  have detW : (a * e * h) * (d * e * h) - b * (N * c) = ((h ^ 2 * e : ℕ) : ℤ) := by
    rw [cast_level Δ]; push_cast; linear_combination (h : ℤ) ^ 2 * det
  obtain ⟨σ, t, A, B, D, ht, H, F⟩ := hermite_factor (N := N) detW (by positivity)
    ((mul_dvd_mul_left (h ^ 2) hen).trans (by rw [mul_comm, nDelta_mul N Δ]))
  obtain ⟨r, ⟨hr, hq⟩, _⟩ := hR σ
  let k := (Real.sqrt e * h)⁻¹
  have scaledW : (g : Mat₂ ℝ) = (k * t) • σH σ A B D := by
    rw [mul_smul, ← F, M]; entries <;> simp [k] <;> field_simp
  have eq : ofZ (σ * r⁻¹)⁻¹ * g = projSL (σH r A B D) := by
    apply eq_proj (s := k * t) (by dsimp [k]; positivity)
    change (ofZ _ : Mat₂ ℝ) * (g : Mat₂ ℝ) = _
    rw [scaledW, Matrix.mul_smul, left_sigma, _root_.mul_inv_rev, inv_inv, inv_mul_cancel_right]
  exact ⟨r, hr, A, B, D, H, by rw [← eq, mul_inv_cancel_right]; exact Subgroup.mem_map_of_mem _ (inv_mem hq)⟩

theorem exists_sigmaH (hg : g ∈ MDelta N Δ) :
    ∃ γ ∈ Gamma0R N, ∃ r ∈ R, ∃ a b d : ℕ, IsHermiteN N a b d ∧ ∃ c : ℝ, c ≠ 0 ∧
      ((γ * g : SL₂ℝ) : Mat₂ ℝ) = c • (σH r a b d) := by
  obtain ⟨r, hr, a, b, d, H, hm⟩ := representative Δ hR hg
  have hd := pos_det r H
  exact ⟨_, hm, r, hr, a, b, d, H, _, inv_ne_zero (Real.sqrt_pos.mpr hd).ne', by rw [inv_mul_cancel_right]; exact coe_projSL hd⟩

end

theorem sigmaH_unique [NeZero N] {R : Set SL₂ℤ} (hR : IsGamma0Reps N R) {r r' : SL₂ℤ} (hr : r ∈ R) (hr' : r' ∈ R)
    {a b d a' b' d' : ℕ} (H : IsHermiteN N a b d) (H' : IsHermiteN N a' b' d') {c c' : ℝ}
    (hc : c ≠ 0) (_hc' : c' ≠ 0) {γ : SL₂ℝ} (hγ : γ ∈ Gamma0R N)
    (h : c • (σH r a b d) = (γ : Mat₂ ℝ) * (c' • (σH r' a' b' d'))) :
    r = r' ∧ a = a' ∧ b = b' ∧ d = d' := by
  obtain ⟨q, hq, rfl⟩ := hγ
  rw [Matrix.mul_smul, left_sigma] at h
  have F := congrArg ((ofZ (q * r')⁻¹ : Mat₂ ℝ) * ·) h
  simp only [Matrix.mul_smul, left_sigma, inv_mul_cancel] at F
  conv_rhs at F => simp [ofZ]
  obtain ⟨ha, hb, hd, sign⟩ := hermite_rigid H H' hc F
  refine ⟨(hR r).unique ⟨hr, by simp⟩ ⟨hr', ?_⟩, ha, hb, hd⟩
  have mov : r = q * r' * ((q * r')⁻¹ * r) := by group
  rw [mov]; rcases sign with s | s <;> rw [s] <;> simp [neg_mul, Gamma0_mem.mp hq]

end NormalizerLean
