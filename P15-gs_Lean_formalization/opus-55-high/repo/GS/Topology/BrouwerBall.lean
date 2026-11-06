module

public import GS.Topology.Brouwer.Brouwer
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Transfer from the standard simplex to a closed ball. The construction embeds
finite-dimensional coordinates in a sufficiently large affine simplex and retracts
that simplex to the closed unit ball by radial clamping. -/
noncomputable section
namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous radial retraction onto the closed unit ball. -/
def unitBallClamp (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg (by positivity)]
    exact inv_mul_le_of_le_mul₀ (by positivity) (by positivity) (by simp)⟩

@[fun_prop] theorem continuous_unitBallClamp : Continuous (unitBallClamp (E := E)) :=
  .subtype_mk (((continuous_const.max continuous_norm).inv₀ (by grind)).smul continuous_id) _

variable [FiniteDimensional ℝ E]

theorem closedBall_fixedPoint (f : Metric.closedBall (0 : E) 1 → Metric.closedBall (0 : E) 1)
    (hf : Continuous f) : ∃ x, f x = x := by
  let n := Module.finrank ℝ E
  obtain ⟨e⟩ : Nonempty (E ≃L[ℝ] (Fin n → ℝ)) := ⟨(Module.finBasis ℝ E).equivFunL⟩
  let R := ‖(e : E →L[ℝ] (Fin n → ℝ))‖ + 1
  have hcoord (x : Metric.closedBall (0 : E) 1) (i : Fin n) : |e x i| ≤ R := by
    have := (norm_le_pi_norm (e x) i).trans ((e : E →L[ℝ] (Fin n → ℝ)).le_opNorm x)
    have := mem_closedBall_zero_iff.mp x.2
    simp_all
    nlinarith [norm_nonneg (e : E →L[ℝ] (Fin n → ℝ))]
  let enc (x : Metric.closedBall (0 : E) 1) : stdSimplex ℝ (Fin (n + 1)) :=
    ⟨Fin.cons (1 - ∑ i, (e x i + R) / (2 * n * R + 1)) fun i => (e x i + R) / (2 * n * R + 1), by
      refine ⟨fun i => Fin.cases ?_ (fun j => div_nonneg (by grind) (by positivity)) i, by simp⟩
      rw [Fin.cons_zero, sub_nonneg, ← Finset.sum_div, div_le_one (by positivity)]
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => (abs_le.1 (hcoord x i)).2
      simp [Finset.sum_add_distrib] at this ⊢
      nlinarith⟩
  let ret (y : stdSimplex ℝ (Fin (n + 1))) := unitBallClamp (e.symm fun i => (2 * n * R + 1) * y.1 i.succ - R)
  obtain ⟨y, hy⟩ := Brouwer (n := ⟨n + 1, Nat.succ_pos _⟩) (enc ∘ f ∘ ret) ((by fun_prop : Continuous enc).comp (hf.comp (continuous_unitBallClamp.comp (e.symm.continuous.comp (continuous_pi fun i => (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)).sub continuous_const)))))
  have h x : ret (enc x) = x := by
    simp [ret, enc, mul_div_cancel₀ _ (by positivity : 2 * n * R + 1 ≠ 0), unitBallClamp,
      max_eq_left (mem_closedBall_zero_iff.mp x.2)]
  exact ⟨ret y, by simpa [h] using congrArg ret hy⟩

end GS.Topology
