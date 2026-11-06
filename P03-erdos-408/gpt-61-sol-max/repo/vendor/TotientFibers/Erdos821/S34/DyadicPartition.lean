module
public import Mathlib.Tactic

public import Erdos821.S34.MajorDyadic
public import Erdos821.S34.ProductDyads

@[expose] public section

set_option autoImplicit false
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace Erdos821.S34Core
noncomputable section
open Blueprint.Analytic

def occupiedDyads (G : PrimeGroups) (k : Fin G.size → ℕ)  :=
  Finset.univ.image (fun z : Tuple G k => dyadIndex (product G k z))

def dyadRestriction (G ) (k ) (j : ℤ)
    (f : Tuple G k → ℂ) (z : Tuple G k)  :=
  if dyadIndex (product G k z) = j then f z else 0

theorem dyadRestriction_norm_le  G   k 
     j   f  :
    tupleNorm G k (dyadRestriction G k j f) ≤ tupleNorm G k f := by
  unfold tupleNorm
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro z _
  unfold dyadRestriction
  split_ifs
  · exact le_rfl
  · simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact mul_nonneg (Erdos821.S34.Proofs.tupleWeight_nonneg (coreGroups G) k z) (sq_nonneg _)

theorem dyadRestriction_support  G   k 
     j  (f : Tuple G k → ℂ)  z  (hne : dyadRestriction G k j f z ≠ 0) :
    dyadScale j ≤ (product G k z : ℝ) ∧ (product G k z : ℝ) ≤ 2 * dyadScale j := by
  have heq : dyadIndex (product G k z) = j := by
    by_contra hn
    simp [dyadRestriction, hn] at hne
  have hs := product_in_dyad _ (tuple_product_pos G k z)
  rw [heq] at hs
  exact ⟨hs.1, hs.2.le⟩

theorem sum_quad_finset_reorder {α β γ δ M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (u : Finset γ) (v : Finset δ) (F : α → β → γ → δ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, F a b c d) =
      ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b c d := by
  calc
    _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, F a b c d :=
      Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, F a b c d := Finset.sum_comm
    _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, F a b c d :=
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem scalar_pairing_partition {α β κ η : Type} [Fintype α] [Fintype β]
    [DecidableEq κ] [DecidableEq η] (w : α → ℝ) (v : β → ℝ)
    (c : α → κ) (d : β → η) (f : β → ℂ) (g : α → ℂ) (R : α → β → ℂ) :
    (∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y) =
      ∑ j ∈ Finset.univ.image c, ∑ k ∈ Finset.univ.image d,
        ∑ x, ∑ y, (w x : ℂ) * (v y : ℂ) * star (if d y = k then f y else 0) *
          (if c x = j then g x else 0) * R x y := by
  symm
  calc
    _ = ∑ j ∈ Finset.univ.image c, ∑ k ∈ Finset.univ.image d, ∑ x, ∑ y,
        if c x = j ∧ d y = k then (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y else 0 := by
      apply Finset.sum_congr rfl
      grind
    _ = ∑ x, ∑ y, ∑ j ∈ Finset.univ.image c, ∑ k ∈ Finset.univ.image d,
        if c x = j ∧ d y = k then (w x : ℂ) * (v y : ℂ) * star (f y) * g x * R x y else 0 :=
      sum_quad_finset_reorder _ _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have hc := Finset.mem_image_of_mem c (Finset.mem_univ x)
      have hd := Finset.mem_image_of_mem d (Finset.mem_univ y)
      simp [ite_and, hc, hd]

theorem comparison_dyadic_partition  G   a b 
     Q   h ξ θ ζ   f   g  :
    comparisonError G a b Q h ξ θ ζ f g =
      ∑ j ∈ occupiedDyads G a, ∑ k ∈ occupiedDyads G b,
        comparisonError G a b Q h ξ θ ζ (dyadRestriction G b k f) (dyadRestriction G a j g) := by
  simp only [comparison_error_scalar_pairing, occupiedDyads, dyadRestriction]
  solve_by_elim [scalar_pairing_partition, tupleWeight, dyadIndex, product, tuplePhase, comparisonScalar]

theorem comparison_bound_from_dyads  G   a b 
     Q   h ξ θ ζ E   f   g 
    (hE : 0 ≤ E)
    (hdyad : ∀ j ∈ occupiedDyads G a, ∀ k ∈ occupiedDyads G b,
      ‖comparisonError G a b Q h ξ θ ζ (dyadRestriction G b k f) (dyadRestriction G a j g)‖ ≤
        E * tupleNorm G b (dyadRestriction G b k f) * tupleNorm G a (dyadRestriction G a j g)) :
    ‖comparisonError G a b Q h ξ θ ζ f g‖ ≤
      ((occupiedDyads G a).card : ℝ) * (occupiedDyads G b).card * E * tupleNorm G b f * tupleNorm G a g := by
  rw [comparison_dyadic_partition]
  calc
    _ ≤ ∑ j ∈ occupiedDyads G a, ∑ k ∈ occupiedDyads G b,
        ‖comparisonError G a b Q h ξ θ ζ (dyadRestriction G b k f) (dyadRestriction G a j g)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ _j ∈ occupiedDyads G a, ∑ _k ∈ occupiedDyads G b, E * tupleNorm G b f * tupleNorm G a g := by
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      apply (hdyad j hj k hk).trans
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (dyadRestriction_norm_le G b k f) hE)
        (dyadRestriction_norm_le G a j g) (tuple_norm_nonneg G a (dyadRestriction G a j g))
        (mul_nonneg hE (tuple_norm_nonneg G b f))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end
end Erdos821.S34Core
