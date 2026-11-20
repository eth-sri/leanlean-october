module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.ToIntervalMod
public import Mathlib.Tactic

/-! Gluing Lipschitz functions on adjacent intervals and extending a closed arc periodically. -/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Real Set

/-! ### Gluing Lipschitz pieces -/

/-- A function which is `K`-Lipschitz on every interval `[n p, (n + 1) p]` (`n ∈ ℤ`) is
`K`-Lipschitz. -/
lemma lipschitzWith_of_pieces {H : Type*} [PseudoMetricSpace H] {f : ℝ → H} {K : NNReal} {p : ℝ} (hp : 0 < p)
    (h : ∀ n : ℤ, LipschitzOnWith K f (Icc (n * p) ((n + 1) * p))) : LipschitzWith K f := by
  have key : ∀ k : ℕ, ∀ x y : ℝ, x ≤ y → ⌊y / p⌋ = ⌊x / p⌋ + k →
      dist (f x) (f y) ≤ K * dist x y := by
    intro k
    induction k with
    | zero =>
      intro x y hxy hfl
      have hx := Int.floor_le (x / p)
      have hx' := Int.lt_floor_add_one (x / p)
      have hy := Int.floor_le (y / p)
      have hy' := Int.lt_floor_add_one (y / p)
      simp   at hfl
      rw [hfl] at hy hy'
      set n := ⌊x / p⌋
      have hmem : ∀ z, (n : ℝ) ≤ z / p → z / p < n + 1 → z ∈ Icc (n * p) ((n + 1) * p) :=
        fun z h1 h2 => ⟨by rwa [le_div_iff₀ hp] at h1, by rw [div_lt_iff₀ hp] at h2; linarith⟩
      exact (h n).dist_le_mul x (hmem x hx hx') y (hmem y hy hy')
    | succ k ih =>
      intro x y hxy hfl
      set n := ⌊x / p⌋
      set b : ℝ := (n + 1) * p
      have hx := Int.floor_le (x / p)
      have hx' := Int.lt_floor_add_one (x / p)
      have hxb : x ≤ b := by
        have := hx'
        rw [div_lt_iff₀ hp] at this; gcongr
      have hbfl : ⌊b / p⌋ = n + 1 := by
        simp  [b]; rw [mul_div_cancel_right₀ _ hp.ne']; simp
      have hby : b ≤ y := by
        have h1 : ((n + 1 : ℤ) : ℝ) ≤ ⌊y / p⌋ := by
          simp_all
        have h2 := Int.floor_le (y / p)
        have : (n + 1 : ℝ) ≤ y / p := by grind
        rw [le_div_iff₀ hp] at this; assumption
      have h1 : dist (f x) (f b) ≤ K * dist x b := by
        refine (h n).dist_le_mul x ⟨?_, hxb⟩ b ⟨?_, le_rfl⟩
        · have := hx
          rwa [le_div_iff₀ hp] at this
        linarith
      have h2 :=
        ih b y hby (by omega)
      calc dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) := dist_triangle _ _ _
        _ ≤ K * dist x b + K * dist b y := add_le_add h1 h2
        _ = K * dist x y := by
          rw [Real.dist_eq, Real.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith),
            abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; ring
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rcases le_total x y with hxy | hxy
  · have hfl := Int.floor_mono (div_le_div_of_nonneg_right hxy hp.le)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hfl)
    grind
  · have hfl := Int.floor_mono (div_le_div_of_nonneg_right hxy hp.le)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr hfl)
    rw [dist_comm, dist_comm x]
    grind

/-! ### Periodic extension -/

section

variable {H : Type*}

/-- The `2π`-periodic extension of the restriction of `f` to `[0, 2π)`. -/
def periodize (f : ℝ → H) : ℝ → H := fun θ => f (toIcoMod two_pi_pos 0 θ)

lemma periodize_apply_of_mem {f : ℝ → H} {θ : ℝ} (hθ : θ ∈ Set.Ico 0 (2 * π)) :
    periodize f θ = f θ := by
  unfold periodize
  rw [(toIcoMod_eq_self two_pi_pos).mpr (by simp_all)]

lemma periodic_periodize (f : ℝ → H) : Function.Periodic (periodize f) (2 * π) := by simp_all [periodize]

lemma periodize_apply_two_pi {f : ℝ → H} (hend : f (2 * π) = f 0) :
    periodize f (2 * π) = f (2 * π) := by
  have := periodic_periodize f 0
  rw [zero_add] at this
  rw [this, periodize_apply_of_mem ⟨le_rfl, two_pi_pos⟩, hend]

lemma periodize_eqOn_Icc {f : ℝ → H} (hend : f (2 * π) = f 0) :
    Set.EqOn (periodize f) f (Set.Icc 0 (2 * π)) := by
  intro θ hθ
  rcases eq_or_lt_of_le hθ.2 with h | h
  simpa [h] using periodize_apply_two_pi hend
  exact periodize_apply_of_mem ⟨hθ.left, h⟩
/-- Periodic extension preserves the Lipschitz bound on the closed period. -/
theorem lipschitzWith_periodizeOn [PseudoMetricSpace H] {f : ℝ → H} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc 0 (2 * π))) (hend : f (2 * π) = f 0) :
    LipschitzWith K (periodize f) := by
  apply lipschitzWith_of_pieces two_pi_pos
  intro n
  have he (x : ℝ) (hx : x ∈ Icc (n * (2 * π)) ((n + 1) * (2 * π))) :
      periodize f x = f (x - n * (2 * π)) := by
    have h := (periodic_periodize f).zsmul n (x - n * (2 * π))
    rw [zsmul_eq_mul, sub_add_cancel] at h
    exact h.trans (periodize_eqOn_Icc hend (by constructor <;> linarith [hx.1, hx.2]))
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [he x hx, he y hy, ← dist_sub_right x y (n * (2 * π))]
  exact hf.dist_le_mul _ (by constructor <;> linarith [hx.1, hx.2]) _
    (by constructor <;> linarith [hy.1, hy.2])

theorem lipschitzWith_periodize [NormedAddCommGroup H] {f : ℝ → H} {K : NNReal}
    (hf : ∀ x ∈ Icc 0 (2 * π), ∀ y ∈ Icc 0 (2 * π), ‖f x - f y‖ ≤ K * |x - y|)
    (hend : f (2 * π) = f 0) : LipschitzWith K (periodize f) :=
  lipschitzWith_periodizeOn (LipschitzOnWith.of_dist_le_mul fun x hx y hy => by
    simpa [dist_eq_norm, Real.norm_eq_abs] using hf x hx y hy) hend

end

end PolyaNeumann
