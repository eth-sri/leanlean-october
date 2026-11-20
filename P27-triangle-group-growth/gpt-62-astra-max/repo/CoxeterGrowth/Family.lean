module
public import CoxeterGrowth.Rates

/-!
# Sphere counts in the combinatorial model

The admissible forms of a fixed length grow by inclusion as the labels increase,
and reindexing the two sides preserves cardinality. For the asymptotics we compare
two solutions of the same recurrence: the cardinalities and the powers of a root
of the rate equation. For the smallest hyperbolic label pair we also calculate
the base cases and give an induction principle with the Padovan step.
-/

@[expose] public section

namespace TriangleGrowth

open Finset Filter

variable {p q p' q' : ℕ}

theorem validTail_mono (hp : p ≤ p') (hq : q ≤ q') {r : List ℕ}
    (h : ValidTail p q r) : ValidTail p' q' r := by
  induction r generalizing p q p' q' <;> grind [ValidTail]

theorem count_mono (hp : p ≤ p') (hq : q ≤ q') (n : ℕ) : count p q n ≤ count p' q' n := by
  apply card_le_card
  intro v hv
  grind [mem_forms, validTail_mono]

theorem count_symm (p q n : ℕ) : count p q n = count q p n :=
  card_equiv swap (by simp)

/-- The homogeneous recursion, with one summand for each pair of positive block lengths. -/
abbrev Rec (p q : ℕ) (f : ℕ → ℝ) :=
  ∀ n, p + q ≤ n → f n = ∑ u ∈ pairs p q, f (n - degree u)

/-- Any solution is bounded above by a constant times a positive solution.
Bound the ratios on the finite initial segment, then add the inequalities. -/
theorem dominates {f g} (hf : Rec p q f) (hg : Rec p q g) (pos : ∀ i, 0 < g i) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, f n ≤ C * g n := by
  obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun i : Fin (p + q) => f i / g i)
  refine ⟨max 1 C, by positivity, fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n (p + q) with hn | hn
    · exact (div_le_iff₀ (pos _)).mp ((hC ⟨⟨n, hn⟩, rfl⟩).trans (le_max_right _ _))
    · rw [hf n hn, hg n hn, mul_sum]
      gcongr
      exact ih _ (by grind)

scoped macro "RootLimit " "(" n:ident " ↦ " f:term ")" τ:term:arg : term =>
  `(Tendsto (fun $n : ℕ => ($f : ℝ) ^ ($n : ℝ)⁻¹) atTop (nhds $τ))

theorem count_limit (hp : 2 ≤ p) (hq : 2 ≤ q) {τ : ℝ} (ht : 0 < τ)
    (heq : G p q τ = 1) : RootLimit (n ↦ count p q n) τ := by
  have hf : Rec p q (fun n => (count p q n : ℝ)) := by
    intro n hn
    dsimp only
    exact_mod_cast count_rec hn
  have hpos (n) : (0 : ℝ) < count p q n := by
    -- Alternating singleton blocks realize every length, even at labels (2,2).
    norm_cast
    apply card_pos.2
    have ones (k : ℕ) : ValidTail 2 2 (List.replicate k 1) := by
      induction k <;> simp_all [ValidTail, List.replicate_succ]
    exact ⟨(false, 0, List.replicate n 1), by
      simp [Valid, len, validTail_mono hq hp (ones n)]
      omega⟩
  -- Multiply the defining equation by τⁿ: the exponential is an exact solution.
  have powRec : Rec p q (τ ^ ·) := by
    intro n hn
    rw [geom_mul] at heq
    simpa (disch := grind) [pairs, mul_sum, pow_sub₀ _ ht.ne', inv_pow] using
      congrArg (τ ^ n * ·) heq.symm
  obtain ⟨c, hc, lo⟩ := dominates powRec hf hpos
  obtain ⟨C, hC, hi⟩ := dominates hf powRec (pow_pos ht)
  have lim {k : ℝ} (hk : 0 < k) : RootLimit (n ↦ k * τ ^ n) τ := by
    -- Away from n = 0, the nth root is k^(1/n) * τ.
    have H := (tendsto_const_nhds.rpow tendsto_inv_atTop_nhds_zero_nat (Or.inl hk.ne')).mul_const τ
    simp at H
    apply H.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [Real.mul_rpow hk.le (pow_nonneg ht.le _), Real.pow_rpow_inv_natCast ht.le hn]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (lim (inv_pos.2 hc)) (lim hC) <;>
    intro n <;> dsimp only <;> gcongr <;> grind [inv_mul_le_iff₀]

/-! ### The `(2,3)` recurrence -/

theorem count23_rec (n : ℕ) :
    count 2 3 (n + 5) = count 2 3 (n + 3) + count 2 3 (n + 2) := by
  simpa +arith [show pairs 2 3 = {(1, 1), (1, 2)} by decide, degree] using
    count_rec (by omega : 2 + 3 ≤ n + 5)

/-- Induction on the homogeneous part of the sequence, indexed from length two.
The three base counts, `5, 7, 9`, are kernel computations on `forms`. -/
theorem count23_ind {P : ℕ → ℕ → Prop} (base : ∀ k < 3, P k (2 * k + 5))
    (step : ∀ n x y, P n x → P (n + 1) y → P (n + 3) (y + x)) (n) : P n (count 2 3 (n + 2)) := by
  induction n using Nat.stepInduction 3 with
  | base n hn =>
    convert! base n hn using 1
    interval_cases n <;> decide +kernel
  | step n ih => exact count23_rec n ▸ step n _ _ (ih 0 (by decide)) (ih 1 (by decide))

scoped notation "Bounds " ρ:arg k:arg v:arg =>
  2 * ρ ^ (k + 2) ≤ (v : ℝ) ∧ (v : ℝ) ≤ 4 * ρ ^ (k + 2)

theorem bounds23 (ρ : ℝ) (hρ : 1 < ρ) (hc : ρ ^ 3 = ρ + 1) (n : ℕ) :
    Bounds ρ n (count 2 3 (n + 2)) := by
  apply count23_ind (P := fun k v => Bounds ρ k v)
  · have := congrArg (ρ * ·) hc
    intro k hk
    interval_cases k <;> norm_num <;> constructor <;> nlinarith [sq_nonneg (ρ ^ 2 - 2)]
  · intro k x y hx hy
    have H : ρ ^ (k + 5) = ρ ^ (k + 3) + ρ ^ (k + 2) := by
      linear_combination ρ ^ (k + 2) * hc
    push_cast
    rw [H]
    grind

end TriangleGrowth
