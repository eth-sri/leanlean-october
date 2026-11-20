module
public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds

public import DedekindZetaZeroFree.Analysis.Gamma.ElementaryNormBounds

@[expose] public section

namespace DedekindZetaZeroFree

alias detector_sz_gamma_norm_le_real := GammaBounds.norm_Gamma_le_real

theorem detector_sz_gamma_decay (a b : ℝ) (hab : a ≤ b) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ σ ∈ Set.Icc a b, ∀ t : ℝ, 1 ≤ |t| →
        ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
          C * Real.rpow |t| (-(m : ℝ)) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-(a + m))
  have hpos : 0 < a + (m + n : ℕ) := by
    push_cast
    linarith
  obtain ⟨M, hM, hbound⟩ := gamma_real_interval_bound (b := b + (m + n : ℕ)) hpos
  refine ⟨M, hM, ?_⟩
  intro σ hσ t ht
  let z := (σ : ℂ) + (t : ℂ) * Complex.I
  have him : z.im = t := by simp [z]
  have hshift : ∀ j : ℕ, |t| ^ j * ‖Complex.Gamma z‖ ≤ ‖Complex.Gamma (z + (j : ℂ))‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hne : z + (j : ℂ) ≠ 0 := by
        intro h
        have : t = 0 := by
          simpa [him] using (congrArg Complex.im h)
        grind
      calc
        _ = |t| * (|t| ^ j * ‖Complex.Gamma z‖) := by ring
        _ ≤ |t| * ‖Complex.Gamma (z + (j : ℂ))‖ := mul_le_mul_of_nonneg_left ih (abs_nonneg _)
        _ ≤ ‖z + (j : ℂ)‖ * ‖Complex.Gamma (z + (j : ℂ))‖ :=
          mul_le_mul_of_nonneg_right (by
            simpa [him] using Complex.abs_im_le_norm (z + (j : ℂ))) (norm_nonneg _)
        _ = ‖Complex.Gamma (z + ((j + 1 : ℕ) : ℂ))‖ := by
          simp [← add_assoc, Complex.Gamma_add_one _ hne, norm_mul]
  have hre : (z + ((m + n : ℕ) : ℂ)).re = σ + (m + n : ℕ) := by simp [z]
  have hreal : 0 < (z + ((m + n : ℕ) : ℂ)).re := by
    rw [hre]
    linarith [hσ.1]
  have hb : Real.Gamma (z + ((m + n : ℕ) : ℂ)).re ≤ M := by
    apply hbound
    rw [hre]
    constructor <;> linarith [hσ.1, hσ.2]
  have hfinal : |t| ^ m * ‖Complex.Gamma z‖ ≤ M := by
    calc
      _ ≤ ‖Complex.Gamma (z + (m : ℂ))‖ := hshift m
      _ ≤ ‖Complex.Gamma ((z + (m : ℂ)) + (n : ℂ))‖ := (gamma_norm_le_add_nat (by simpa [him] using ht) n)
      _ = ‖Complex.Gamma (z + ((m + n : ℕ) : ℂ))‖ := by simp [Nat.cast_add, add_assoc]
      _ ≤ Real.Gamma (z + ((m + n : ℕ) : ℂ)).re := detector_sz_gamma_norm_le_real _ hreal
      _ ≤ M := hb
  change ‖Complex.Gamma z‖ ≤ M * |t| ^ (-(m : ℝ))
  simp [Real.rpow_neg (abs_nonneg t)]
  simpa [div_eq_mul_inv] using ((le_div_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one ht) _)).2 (by linarith))

end DedekindZetaZeroFree
