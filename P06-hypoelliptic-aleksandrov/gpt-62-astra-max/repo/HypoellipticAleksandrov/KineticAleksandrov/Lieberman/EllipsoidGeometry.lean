module

public import HypoellipticAleksandrov.KineticAleksandrov.EllipsoidDirichlet
public import HypoellipticAleksandrov.Parabolic.ScalarClassical
import PDEFoundation.Geometry.EuclideanBall.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic

/-! # Geometry and compact-cylinder drift bounds for the literal ellipsoid -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Lieberman
open HypoellipticAleksandrov Parabolic Set
open scoped Matrix Topology BigOperators

section
variable {d : ℕ} (Q : PDE.Mat d)

private theorem quadratic_continuous :
    Continuous (fun x => PDE.vecDot x (Q *ᵥ x)) := by
  unfold PDE.vecDot Matrix.mulVec dotProduct
  fun_prop

private theorem quadratic_smul (c : ℝ) (x : PDE.Vec d) :
    PDE.vecDot (c • x) (Q *ᵥ (c • x)) = c ^ 2 * PDE.vecDot x (Q *ᵥ x) := by
  simp only [Matrix.mulVec_smul, PDE.vecDot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every literal open ellipsoid is open, without a definiteness assumption. -/
theorem isOpen_openEllipsoid : IsOpen (openEllipsoid Q) :=
  isOpen_lt (quadratic_continuous Q) continuous_const

end

variable {d : ℕ} {Q : PDE.Mat d} (hQ : Q.PosDef)

include hQ in
private theorem ellipsoid_bounded :
    Bornology.IsBounded (openEllipsoid Q) := by
  obtain ⟨m, hm, hmin⟩ := (isCompact_sphere 0 1).exists_forall_le'
    (quadratic_continuous Q).continuousOn (a := 0) (by
      intro x hx
      have hxne : x ≠ 0 := by
        aesop
      exact hQ.dotProduct_mulVec_pos hxne)
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1 + 1 / m, ?_⟩
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    simp only [norm_zero]
    positivity
  have hn := norm_pos_iff.mpr hx0
  have hs : ‖x‖⁻¹ • x ∈ Metric.sphere 0 1 := by
    simp [norm_smul, hn.ne']
  have hh := hmin _ hs
  rw [quadratic_smul] at hh
  have hmul : m * ‖x‖ ^ 2 ≤ PDE.vecDot x (Q *ᵥ x) := by
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖x‖)
    field_simp at hh'
    exact hh'
  have hq : PDE.vecDot x (Q *ᵥ x) < 1 := hx
  have hmdiv := mul_one_div_cancel hm.ne'
  have hdiv := one_div_pos.mpr hm
  nlinarith

private theorem ellipsoid_closure (_hQ : Q.PosDef) :
    closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} := by
  apply subset_antisymm
  · exact closure_lt_subset_le (quadratic_continuous Q) continuous_const
  · intro x hx
    have hc : Continuous (fun c : ℝ => c • x) := continuous_id.smul continuous_const
    have him : (fun c : ℝ => c • x) '' Ioo 0 1 ⊆ openEllipsoid Q := by
      rintro y ⟨c, hc', rfl⟩
      change PDE.vecDot (c • x) (Q *ᵥ (c • x)) < 1
      rw [quadratic_smul]
      have hc2 : c ^ 2 < 1 := by nlinarith only [hc'.1, hc'.2]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hx (sq_nonneg c)) (by simpa using hc2)
    have h1 : 1 ∈ closure (Ioo (0 : ℝ) 1) := by
      norm_num
    have ht := closure_mono him (image_closure_subset_closure_image hc (mem_image_of_mem _ h1))
    simpa using ht

include hQ in
/-- Positive-definite ellipsoids have bounded closure with the quadratic level set as frontier. -/
theorem openEllipsoid_geometry :
    Bornology.IsBounded (openEllipsoid Q) ∧
    closure (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) ≤ 1} ∧
    frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} := by
  have hcl := ellipsoid_closure hQ
  have hf : frontier (openEllipsoid Q) = {x | PDE.vecDot x (Q *ᵥ x) = 1} := by
    rw [(isOpen_openEllipsoid Q).frontier_eq, hcl]
    ext x
    change (_ ≤ 1 ∧ ¬ _ < 1) ↔ _ = 1
    grind
  exact ⟨ellipsoid_bounded hQ, hcl, hf⟩

/-- A continuous drift is Euclidean-bounded on every bounded closed spatial cylinder. -/
theorem exists_closedCylinder_drift_bound {Ω : Set (PDE.Vec d)}
    (hΩ : Bornology.IsBounded Ω) (a T : ℝ) (b : ℝ → PDE.Vec d → PDE.Vec d)
    (hb : Continuous (fun z : TimeVelocity d => b z.1 z.2)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z ∈ scalarParabolicClosedCylinder a T Ω,
      PDE.vecEuclideanNorm (b z.1 z.2) ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hΩ.isCompact_closure).exists_bound_of_continuousOn
    (PDE.continuous_vecEuclideanNorm.comp hb).continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro z hz
  exact (le_abs_self _).trans ((hB z hz).trans (le_max_left _ _))

end HypoellipticAleksandrov.KineticAleksandrov.Lieberman
