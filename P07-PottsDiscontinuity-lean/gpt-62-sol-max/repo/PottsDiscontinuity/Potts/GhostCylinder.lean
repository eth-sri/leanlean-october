module

public import PottsDiscontinuity.Potts.GhostBoundary
public import PottsDiscontinuity.Potts.CylinderColoring

/-!
# Exact ghost cylinder formula for the frozen Potts law

The spin carrier remains the original finite vertex set. Extending by the
fixed ghost colour identifies its compatible cylinder patterns with the
marked component-colouring patterns. Consequently the finite Potts cylinder
formula uses only the connection partition of the observed vertices and ghost.
-/

@[expose] public section

namespace PottsDiscontinuity.Potts

noncomputable section

open Classical

local instance ghostCylinderLiteralBondDecidableEq (V : Finset (ℤ × ℤ)) :
    DecidableEq (LiteralBond V) := fun _ _ => Classical.propDecidable _

local instance ghostCylinderBoundaryVertexFintype (V : Finset (ℤ × ℤ)) :
    Fintype (BoundaryVertex V) := Fintype.ofFinite _

/-- Every colouring with a prescribed ghost spin is the extension of a unique literal colouring. -/
private def ghostExtensionEquiv {q : ℕ} {V : Finset (ℤ × ℤ)} (c : Set.Icc 1 q) :
    SpinConfiguration q V ≃ {τ : Option ↥(V : Set (ℤ × ℤ)) → Set.Icc 1 q // τ none = c} where
  toFun σ := ⟨ghostExtension c σ, rfl⟩
  invFun τ v := τ.val (some v)
  left_inv _ := rfl
  right_inv τ := by
    apply Subtype.ext
    funext a
    cases a with
    | none => exact τ.property.symm
    | some a => rfl

/-- The original-spin cylinder mass under uniform ghost-pinned component
colours depends only on the marked connection partition. -/
theorem ghostColoringProbability_cylinder (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ))
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ)) (ω : LiteralBond V → Bool)
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q V,
      if ∀ a, σ (v a) = ξ a then ghostColoringProbability q V i hi ω σ else 0) =
      pinnedClusterCylinderProbability (ghostOpenGraph V ω).reachableSetoid
        (some ∘ v) ξ none (boundaryColor q i hi) := by
  let R := (ghostOpenGraph V ω).reachableSetoid
  let c := boundaryColor q i hi
  let : Nonempty (Set.Icc 1 q) := ⟨c⟩
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have scale (k : ℕ) (hk : 0 < k) : (q : ℝ) * ((q : ℝ)^k)⁻¹ = ((q : ℝ)^(k-1))⁻¹ := by
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ k), pow_succ]
    simp_all
  have hmul (σ : SpinConfiguration q V) : (q : ℝ) * clusterColoringProbability R (ghostExtension c σ) =
      ghostColoringProbability q V i hi ω σ := by
    simp only [clusterColoringProbability, ghostColoringProbability, card_pottsColors, mul_ite_zero]
    change (if _ then _ else _) = (if _ then _ else _)
    split_ifs
    · exact scale _ (ghostComponentCount_pos V ω)
    rfl
  have hp : pinnedClusterCylinderProbability R (some ∘ v) ξ none c =
      (q : ℝ) * clusterCylinderProbability R (markedMap (some ∘ v) none) (markedMap ξ c) := by
    simp only [pinnedClusterCylinderProbability, clusterCylinderProbability, card_pottsColors, mul_ite_zero]
    split_ifs
    · exact (scale _ (observedClassCount_marked_pos R (some ∘ v) none)).symm
    · rfl
  rw [hp, ← clusterColoringProbability_cylinder, Finset.mul_sum]
  simp_rw [markedMap_agreement_iff, mul_ite_zero, ite_and]
  conv_rhs => rw [← Finset.sum_filter, Finset.sum_subtype (p := fun τ => τ none = c) _ (by simp), ← (ghostExtensionEquiv (V := V) c).sum_comp]
  apply Finset.sum_congr rfl
  intro σ _
  simp [ghostExtensionEquiv, ghostExtension, hmul]

/-- Exact cylinder formula for the frozen finite Potts law with its literal
one-field-term-per-boundary-vertex Hamiltonian and positive boundary colour. -/
theorem pottsProb_ghost_cylinder (q : ℕ) (hq : 2 ≤ q) (V : Finset (ℤ × ℤ)) (β : ℝ)
    (i : Fin (q + 1)) (hi : 1 ≤ (i : ℕ))
    {A : Type*} (v : A → ↥(V : Set (ℤ × ℤ))) (ξ : A → Set.Icc 1 q) :
    (∑ σ : SpinConfiguration q V,
      if ∀ a, σ (v a) = ξ a then pottsProb q V β i σ else 0) =
      ∑ ω : LiteralBond V → Bool, ghostRCProbability q V β ω *
        pinnedClusterCylinderProbability (ghostOpenGraph V ω).reachableSetoid
          (some ∘ v) ξ none (boundaryColor q i hi) := by
  have h := pottsProb_event_eq_ghostMixture q hq V β i hi {σ | ∀ a, σ (v a) = ξ a}
  simpa only [Set.mem_ofPred_eq, ghostColoringProbability_cylinder q hq V i hi] using h

end

end PottsDiscontinuity.Potts
