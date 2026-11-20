module

public import PottsDiscontinuity.Potts.CylinderColoring
public import PottsDiscontinuity.Potts.GraphCoupling

/-! One-point pinned and two-point free colouring kernels, with the corrected factors. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open Classical
noncomputable section

private theorem setoid_top_of_two_classes {A : Type*} (R : Setoid A) (x y : A)
    (hcover : ∀ a, a = x ∨ a = y) (hxy : R x y) : R = ⊤ := by
  apply top_unique
  intro a b _
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl
  · exact R.refl _
  · exact hxy
  · exact R.symm hxy
  rfl

private theorem setoid_bot_of_two_classes {A : Type*} (R : Setoid A) (x y : A)
    (hcover : ∀ a, a = x ∨ a = y) (hxy : ¬ R x y) : R = ⊥ := by
  apply bot_unique
  intro a b hab
  rcases hcover a with rfl | rfl <;> rcases hcover b with rfl | rfl
  · rfl
  · trivial
  · exact (hxy (R.symm hab)).elim
  · rfl

private theorem card_quotient_top {A : Type*} [Nonempty A] : Nat.card (Quotient (⊤ : Setoid A)) = 1 := by
  let : Subsingleton (Quotient (⊤ : Setoid A)) := Quotient.subsingleton_iff.mpr rfl
  let : Nonempty (Quotient (⊤ : Setoid A)) := ⟨Quotient.mk _ (Classical.choice (inferInstance : Nonempty A))⟩
  exact Nat.card_unique

/-- Two observed spins have one uniform colour if connected, and two independent
uniform colours otherwise. -/
theorem free_two_point_kernel (q : ℕ) (c : Set.Icc 1 q) (R : Setoid Bool) :
    clusterCylinderProbability R id (fun _ : Bool => c) =
      if R false true then (q : ℝ)⁻¹ else ((q : ℝ) ^ 2)⁻¹ := by
  have hcomp : R.comap id ≤ Setoid.ker (fun _ : Bool => c) := by intro _ _ _; rfl
  unfold clusterCylinderProbability
  rw [ite_eq_left hcomp, card_pottsColors]
  have hcount : observedClassCount R id = Nat.card (Quotient R) := rfl
  rw [hcount]
  have hcover : ∀ b : Bool, b = false ∨ b = true := by trivial
  by_cases h : R false true
  · rw [ite_eq_left h, setoid_top_of_two_classes R false true hcover h, card_quotient_top, pow_one]
  · rw [ite_eq_right h, setoid_bot_of_two_classes R false true hcover h,
      Nat.card_congr (Setoid.quotientBotEquiv : Quotient (⊥ : Setoid Bool) ≃ Bool)]
    simp

end
end PottsDiscontinuity.Potts
