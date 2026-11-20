module

public import NearlyMinimax.FiniteBounds

public import NearlyMinimax.HighLocalFrame


@[expose] public section

/-! Actual coordinatewise chart bounds for the finite polynomial frame. -/
noncomputable section
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section
variable {d F : ℕ}

section
variable (x : Covariate d)
    (hx : ∀ i, |x i| ≤ 2)
include hx

theorem highFrameFeature_abs_le_one (γ : HighFrameIndex d F) :
    |highFrameFeature x γ| ≤ 1 := by
  unfold highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · solve_by_elim [abs_nonneg]
  · intro i _
    rw [abs_pow]
    have hb : |x i / 8| ≤ 1 := by
      grind
    exact pow_le_one₀ (abs_nonneg _) hb

theorem highFrameProfile_abs_le_coefficients (v : HighFrameIndex d F → ℝ) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ ∑ γ, |v γ| := by
  simpa only [mul_comm, mul_one, one_mul] using abs_weighted_sum_le (s := Finset.univ) (w := v)
    (f := highFrameFeature x) (B := 1) (fun i _ => highFrameFeature_abs_le_one x hx i)

end

theorem highFrameProfile_abs_le_one (C : ℝ) (hC : 1 ≤ C)
    (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ)
    (hv : ∑ γ, |v γ| ≤ C⁻¹) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ 1 :=
  (highFrameProfile_abs_le_coefficients x hx v).trans (hv.trans (inv_le_one_of_one_le₀ hC))

end

theorem highFrameResponseGuards {d n F : ℕ} (C a V η ρ : ℝ) (hC : 1 ≤ C)
    (ha : 0 < a) (hη : 0 ≤ η) (hηρ : η ≤ ρ / 2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) :
    ResponseGuards C a V η ρ g w (fun i => highFrameFeature (D := F) (U i)) :=
  ⟨zero_lt_one.trans_le hC, ha, hη, hηρ, hg, hw,
    fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv, hp⟩

end NearlyMinimax
