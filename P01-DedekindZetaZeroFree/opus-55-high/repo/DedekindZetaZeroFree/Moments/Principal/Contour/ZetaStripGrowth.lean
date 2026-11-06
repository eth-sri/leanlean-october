module

public import DedekindZetaZeroFree.LFunctions.Hecke.PoissonRows.RightBounds

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PrincipalZetaStripGrowth

open DedekindZetaZeroFree Filter Topology

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem strip_le_four (D : FixedData S η) (a ρ : ℝ) (ha : 0 < a) (ha4 : a ≤ 4)
    (hρ : 0 < ρ) :
    ∃ B d : ℝ, 0 < B ∧ 0 ≤ d ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ 4 → ρ ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ B * (2 + |s.im|) ^ d :=
  PrincipalNumerator.stripNumerator_bound_away_pole D.recipe a 4 ρ ha ha4 le_rfl hρ

theorem strip_poly (D : FixedData S η) (a b ρ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hρ : 0 < ρ) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ρ ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := by
  obtain ⟨K, hK, hKb⟩ := RightHeckeBounds.zetaSCont_norm_le_right D 4 (by norm_num)
  by_cases ha4 : a ≤ 4
  · obtain ⟨B, d, hB, hd, hbd⟩ := strip_le_four D a ρ ha ha4 hρ
    refine ⟨B * 2 ^ d + K, d, by positivity, hd, ?_⟩
    intro s h1 h2 hsep
    have hp : 0 ≤ (1 + |s.im|) ^ d := Real.rpow_nonneg (by positivity) d
    have hone : (1 : ℝ) ≤ (1 + |s.im|) ^ d :=
      Real.one_le_rpow (by linarith [abs_nonneg s.im]) hd
    by_cases h4 : s.re ≤ 4
    · have h := hbd s h1 h4 hsep
      have hrp : (2 + |s.im|) ^ d ≤ 2 ^ d * (1 + |s.im|) ^ d := by
        rw [← Real.mul_rpow (by norm_num) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg s.im]) hd
      have h3 : B * (2 + |s.im|) ^ d ≤ B * (2 ^ d * (1 + |s.im|) ^ d) :=
        mul_le_mul_of_nonneg_left hrp hB.le
      have h5 : (B * 2 ^ d + K) * (1 + |s.im|) ^ d
          = B * (2 ^ d * (1 + |s.im|) ^ d) + K * (1 + |s.im|) ^ d := by ring
      have h6 : 0 ≤ K * (1 + |s.im|) ^ d := mul_nonneg hK.le hp
      linarith
    · have h := hKb s (by linarith)
      have h7 : K ≤ K * (1 + |s.im|) ^ d := le_mul_of_one_le_right hK.le hone
      have h8 : 0 ≤ B * 2 ^ d * (1 + |s.im|) ^ d := by positivity
      nlinarith
  · refine ⟨K, 0, hK, le_rfl, ?_⟩
    intro s h1 _ _
    have h := hKb s (by linarith [not_le.mp ha4])
    simpa using h

theorem zetaSCont_strip_polynomial_bound (D : FixedData S η) (a b r : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → r ≤ ‖s - 1‖ →
      ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k :=
  strip_poly D a b r ha hab hr

theorem zetaSCont_high_height_bound (D : FixedData S η) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖D.zetaSCont s‖ ≤ C * |s.im| ^ k := by
  obtain ⟨C, k, hC, hk, h⟩ := strip_poly D a b 1 ha hab one_pos
  refine ⟨C * 2 ^ k, k, by positivity, hk, ?_⟩
  intro s h1 h2 him
  have hsep : 1 ≤ ‖s - 1‖ := by
    have : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
    linarith
  have hx : 0 ≤ |s.im| := abs_nonneg _
  have hle : (1 + |s.im|) ^ k ≤ (2 * |s.im|) ^ k :=
    Real.rpow_le_rpow (by linarith) (by linarith) hk
  rw [Real.mul_rpow (by norm_num) hx] at hle
  have hC' := h s h1 h2 hsep
  calc ‖D.zetaSCont s‖ ≤ C * (1 + |s.im|) ^ k := hC'
    _ ≤ C * (2 ^ k * |s.im| ^ k) := mul_le_mul_of_nonneg_left hle hC.le
    _ = C * 2 ^ k * |s.im| ^ k := by ring

end DedekindZetaZeroFree.Quantitative.PrincipalZetaStripGrowth
