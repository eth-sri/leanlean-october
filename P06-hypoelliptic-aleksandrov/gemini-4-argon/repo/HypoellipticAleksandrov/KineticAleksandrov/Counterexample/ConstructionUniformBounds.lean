module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ConstructionSecondBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.BarrierPackedJets

/-! # Uniform bounds on raw selected jets over compact time intervals -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample
open Set

/- Continuous scalar functions are bounded on any compact carrier. -/
theorem construction_compact_scalar_bound {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C := by
  obtain ⟨C, hb⟩ := hK.bddAbove_image hf.abs.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hb ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩

/- Uniform scalar bounds are preserved by subtraction. -/
theorem construction_scalar_bound_sub {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x - g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  exact ⟨C + D, add_nonneg hC hD, fun x hx =>
    (abs_sub _ _).trans (add_le_add (hf x hx) (hg x hx))⟩

/- Uniform scalar bounds are preserved by multiplication. -/
theorem construction_scalar_bound_mul {X : Type*} (K : Set X) (f g : X → ℝ)
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x| ≤ C)
    (hg : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |g x| ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, |f x * g x| ≤ C := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C * D, mul_nonneg hC hD, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hf x hx) (hg x hx) (abs_nonneg _) hC

/- The packed barrier gradient depends continuously on time and space together. -/
theorem construction_barrier_gradient_joint_continuous (d : ℕ) (mu R : ℝ)
    (i : Fin (d + d)) : Continuous (fun z : ℝ × PDE.Vec (d + d) =>
      PDE.classicalGradient (spatialPackedBarrier d mu R z.1) z.2 i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [spatialPackedBarrier_positionGradient]
    exact continuous_const
  · simp only [spatialPackedBarrier_velocityGradient]
    exact (((continuous_const.mul (continuous_const.mul continuous_fst).rexp).div_const
      (R ^ 2)).neg).mul
      ((continuous_apply j).comp ((spatialCoordinateCLE d).continuous.comp
        continuous_snd).snd)

/- The packed barrier Hessian is jointly continuous. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
