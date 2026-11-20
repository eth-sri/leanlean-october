module

public import NormalizerLean.Basic

@[expose] public section

/-! Existence and projective rigidity of primitive two-by-two Hermite forms. -/

open Matrix

namespace NormalizerLean

/-- Remove the common content of the three entries of an upper triangular form. -/
private lemma primitive_hnf {A B D N : ℕ} (hA : 0 < A) (hB : B < D) (hAD : A * D ∣ N) :
    ∃ t a b d : ℕ, 0 < t ∧ IsHermiteN N a b d ∧ A = t * a ∧ B = t * b ∧ D = t * d := by
  obtain ⟨f, eq, prim⟩ := Finset.extract_gcd ![A, B, D] Finset.univ_nonempty
  generalize Finset.univ.gcd ![A, B, D] = t at eq
  simp [Fin.forall_fin_succ] at eq
  obtain ⟨rfl, rfl, rfl⟩ := eq
  have ht := Nat.pos_of_mul_pos_right hA
  rw [Nat.mul_lt_mul_left ht] at hB
  refine ⟨t, _, _, _, ht, ⟨Nat.pos_of_mul_pos_left hA, by omega, ?_, hB, ?_⟩, rfl, rfl, rfl⟩
  · exact dvd_trans ⟨t * t, by ring⟩ hAD
  · simpa [Fin.univ_succ, Finset.gcd_image, gcd_eq_nat_gcd, Nat.gcd_assoc, Function.comp_def] using prim

/-- A real, primitive Hermite factorization of the given integer matrix. -/
lemma hermite_factor {x y z w : ℤ} {N E : ℕ} (det : x * w - y * z = E) (hE : 0 < E) (hN : E ∣ N) :
    ∃ σ : SL₂ℤ, ∃ t a b d : ℕ, 0 < t ∧ IsHermiteN N a b d ∧
      !![(x : ℝ), y; z, w] = (t : ℝ) • ((ofZ σ : Mat₂ ℝ) * hermMat a b d) := by
  have hW : 0 < x * w - y * z := by rw [det]; positivity
  have hg0 : 0 < x.gcd z := by rw [Int.gcd_pos_iff]; contrapose! hW; simp [hW.1, hW.2]
  obtain ⟨g, p, q, hg, hpq, rfl, rfl⟩ := Int.exists_gcd_one' hg0
  -- Bézout clears the first column; reduction modulo the new diagonal entry
  -- puts the upper right entry into its fundamental interval.
  obtain ⟨A, B, H⟩ := Int.isCoprime_iff_gcd_eq_one.mpr hpq
  let b := A * y + B * w
  have hD : 0 < p * w - q * y := by nlinarith
  lift p * w - q * y to ℕ using hD.le with D hd
  have hlt := Int.emod_lt_of_pos b hD
  have mod := Int.emod_add_mul_ediv b D
  lift b % (D : ℤ) to ℕ using Int.emod_nonneg _ hD.ne' with C hc
  obtain rfl : E = g * D := by exact_mod_cast (show (E : ℤ) = (g : ℤ) * D by grobner)
  obtain ⟨t, a, b', d, ht, H', rfl, rfl, rfl⟩ := primitive_hnf hg (B := C) (by omega) hN
  refine ⟨mkSL p (p * (b / (t * d)) - B) q (q * (b / (t * d)) + A) (by linear_combination H), t, a, b', d, ht, H', ?_⟩
  dsimp only [b] at mod ⊢
  rify at H hd mod
  rw [ofZ_mkSL]
  entries <;> simp [hermMat] <;> grobner

/-- Upper triangularity forces the change of basis to be a shear up to sign.
Primitivity fixes the scale and reduction modulo `d` fixes the shear. -/
lemma hermite_rigid {N a b d A B D : ℕ} (H : IsHermiteN N a b d) (H' : IsHermiteN N A B D)
    {u v : ℝ} (hu : u ≠ 0) {M : SL₂ℤ}
    (eq : u • ((ofZ M : Mat₂ ℝ) * hermMat a b d) = v • hermMat A B D) :
    a = A ∧ b = B ∧ d = D ∧ (M = 1 ∨ M = -1) := by
  obtain ⟨ha, hd, _, hbd, prim⟩ := H
  obtain ⟨hA, hD, _, hBD, prim'⟩ := H'
  induction M using SpecialLinearGroup.fin_two_induction with
  | h x y z w det =>
    erw [ofZ_mkSL x y z w det, ← Matrix.ext_iff] at eq
    simp [Fin.forall_fin_two, hermMat, hu, ha.ne'] at eq
    obtain ⟨⟨e00, e01⟩, rfl, e11⟩ := eq
    simp at det
    have signs := Int.eq_one_or_neg_one_of_mul_eq_one' det
    obtain ⟨X, Y⟩ : (a : ℤ) * B = (b + x * y * d) * A ∧ (a : ℤ) * D = d * A := by
      rcases signs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp at e00 e01 e11 ⊢ <;> constructor <;> rify <;> grobner
    -- Compare contents after clearing denominators: the upper triangular shear
    -- leaves gcd(b,d) unchanged.
    have G := congrArg₂ (fun x y : ℤ => Nat.gcd (a * A) (x.gcd y)) X Y
    obtain rfl : a = A := by
      simpa [Int.gcd_mul_left, Int.gcd_mul_right, Nat.gcd_mul_left, Nat.gcd_mul_right, ← Nat.gcd_assoc, prim, prim'] using G
    rw [mul_comm _ (a : ℤ), mul_right_inj' (by positivity : (a : ℤ) ≠ 0)] at X Y
    obtain rfl : D = d := by exact_mod_cast Y
    obtain rfl : B = b := by simpa [← Int.natCast_mod, Nat.mod_eq_of_lt hbd, Nat.mod_eq_of_lt hBD] using congrArg (· % (D : ℤ)) X
    obtain rfl : y = 0 := by simpa [hd.ne', left_ne_zero_of_mul (det.trans_ne one_ne_zero)] using X.symm
    refine ⟨rfl, rfl, rfl, ?_⟩
    rcases signs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [left; right] <;> entries <;> rfl

end NormalizerLean
