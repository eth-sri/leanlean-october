module

public import PottsDiscontinuity.BetheAnsatz.Scattering

/-!
# Adjacent transpositions in the coordinate Bethe amplitudes

Companion paper, Lemma `lem:ratios`, equation (8). Products are over ordered index pairs.
The finite product argument explicitly isolates the single pair whose order is reversed
by an adjacent transposition.
-/

public section

open Finset Complex

namespace PottsDiscontinuity.BetheAnsatz

section
variable {n : ℕ}

/-- An adjacent transposition changes exactly one factor in a product over `i < j`.
The multiplication form avoids dividing by factors that might vanish. -/
theorem pair_product_adjacent_swap (f : Fin n → Fin n → ℂ)
    {a b : Fin n} (hab : a.val + 1 = b.val) :
    (∏ i, ∏ j ∈ Ioi i, f (Equiv.swap a b i) (Equiv.swap a b j)) * f a b =
      (∏ i, ∏ j ∈ Ioi i, f i j) * f b a := by
  let D : Finset (Fin n × Fin n) := (univ ×ˢ univ).filter (fun q => q.1 < q.2)
  let s := Equiv.swap a b
  have hmem : (a, b) ∈ D := by grind
  have hstable : ∀ q ∈ D.erase (a, b), (s q.1, s q.2) ∈ D.erase (a, b) := by
    grind
  have hr : (∏ q ∈ D.erase (a, b), f (s q.1) (s q.2)) =
      ∏ q ∈ D.erase (a, b), f q.1 q.2 := by
    apply Finset.prod_bij (fun q _ => (s q.1, s q.2))
    · omega
    · intro q _ r _ he
      exact Prod.ext (s.injective (congrArg Prod.fst he)) (s.injective (congrArg Prod.snd he))
    · intro q hq
      refine ⟨(s q.1, s q.2), hstable q hq, ?_⟩
      simp [s]
    simp
  have hpair : ∀ g : Fin n → Fin n → ℂ,
      (∏ i, ∏ j ∈ Ioi i, g i j) = ∏ q ∈ D, g q.1 q.2 := by
    intro g
    simp only [D, Finset.prod_filter, Finset.prod_product]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_filter, Finset.filter_lt_eq_Ioi]
  rw [hpair, hpair]
  rw [← Finset.mul_prod_erase D (fun q => f (s q.1) (s q.2)) hmem,
    ← Finset.mul_prod_erase D (fun q => f q.1 q.2) hmem]
  simp only [s, Equiv.swap_apply_left, Equiv.swap_apply_right] at hr ⊢
  rw [hr]
  ring

/-- The adjacent amplitude relation, in multiplication form. Bethe equations are not needed.
Permutation multiplication is composition: `(σ * swap a b) i = σ (swap a b i)`. -/
theorem amplitude_adjacent_swap {Δ : ℝ} (hΔ : Δ < -1)
    (p : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a.val + 1 = b.val) :
    amplitude Δ p (σ * Equiv.swap a b) =
      -Complex.exp (I * (Bethe.theta Δ (p (σ a)) (p (σ b)) : ℂ)) * amplitude Δ p σ := by
  let f := fun i j =>
    z (p (σ i)) * scattering Δ (p (σ i)) (p (σ j))
  have hf : f a b ≠ 0 := mul_ne_zero (z_ne_zero _) (scattering_ne_zero hΔ _ _)
  have hp := pair_product_adjacent_swap f hab
  have habne : a ≠ b := by omega
  have hsign : (((Equiv.Perm.sign (σ * Equiv.swap a b) : ℤ) : ℂ)) =
      -(((Equiv.Perm.sign σ : ℤ) : ℂ)) := by
    simp_all
  have he : Complex.exp (I * (Bethe.theta Δ (p (σ a)) (p (σ b)) : ℂ)) =
      f b a / f a b := exp_I_theta_eq_scattering hΔ _ _
  have hm : amplitude Δ p (σ * Equiv.swap a b) * f a b =
      -(amplitude Δ p σ * f b a) := by
    unfold amplitude
    rw [hsign]
    change (-(((Equiv.Perm.sign σ : ℤ) : ℂ)) *
      (∏ i, ∏ j ∈ Ioi i, f (Equiv.swap a b i) (Equiv.swap a b j))) * f a b =
      -((((Equiv.Perm.sign σ : ℤ) : ℂ)) * (∏ i, ∏ j ∈ Ioi i, f i j) * f b a)
    grind
  grind
end

end PottsDiscontinuity.BetheAnsatz
