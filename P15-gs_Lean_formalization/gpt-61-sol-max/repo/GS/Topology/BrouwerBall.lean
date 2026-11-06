import Mathlib.Tactic

import GS.Topology.BrouwerFixedPoint
import GS.Topology.Brouwer.Brouwer
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


set_option backward.isDefEq.respectTransparency false
/-! Transfer from the standard simplex to a closed ball. The construction embeds
finite-dimensional coordinates in a sufficiently large affine simplex and retracts
that simplex to the closed unit ball by radial clamping. -/
noncomputable section
namespace GS.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous radial retraction onto the closed unit ball. -/
def unitBallClamp (x : E) : Metric.closedBall (0 : E) 1 :=
  ⟨(max 1 ‖x‖)⁻¹ • x, by simp_all [abs_of_pos,inv_mul_le_iff₀,zero_lt_one,Real.norm_eq_abs,norm_smul,]⟩

theorem continuous_unitBallClamp : Continuous (unitBallClamp (E := E)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖x‖)))).smul
    continuous_id



variable [FiniteDimensional ℝ E]

/-- Brouwer on the ball follows by encoding it in a simplex and retracting. -/
instance instBrouwerFixedPoint : BrouwerFixedPoint E where
  brouwer_fixed_point f hf := by

    let n := Module.finrank ℝ E
    let e := (Module.finBasis ℝ E).equivFunL
    let R : ℝ := ‖(e : E →L[ℝ] (Fin n → ℝ))‖ + 1
    let D : ℝ := 2 * (n + 1) * R
    have hR : 0 < R := by positivity
    have hD : 0 < D := by positivity
    have hcoord (x : Metric.closedBall (0 : E) 1) (i : Fin n) : |e x i| ≤ R := by
      calc
        |e x i| = ‖e x i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖e x‖ := norm_le_pi_norm (e x) i
        _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * ‖(x : E)‖ := (e : E →L[ℝ] (Fin n → ℝ)).le_opNorm x
        _ ≤ ‖(e : E →L[ℝ] (Fin n → ℝ))‖ * 1 :=
          mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp x.property) (norm_nonneg _)
        _ ≤ R := by aesop
    let a : Metric.closedBall (0 : E) 1 → Fin n → ℝ := fun x i => (e x i + R) / D
    have ha0 (x : Metric.closedBall (0 : E) 1) (i : Fin n) : 0 ≤ a x i := by
      
      exact div_nonneg (by grind) hD.le
    have ha1 (x : Metric.closedBall (0 : E) 1) : ∑ i, a x i ≤ 1 := by
      have hi (i : Fin n) : a x i ≤ (2 * R) / D := by
        apply div_le_div_of_nonneg_right _ hD.le
        have := (abs_le.mp (hcoord x i)).2
        linarith
      calc
        ∑ i, a x i ≤ ∑ _i : Fin n, (2 * R) / D := Finset.sum_le_sum fun i _ => hi i
        _ = (n : ℝ) * (2 * R) / D := by simp [mul_div_assoc]
        _ ≤ 1 := (div_le_one hD).mpr (by grind)
    let enc : Metric.closedBall (0 : E) 1 → stdSimplex ℝ (Fin (n + 1)) := fun x =>
      ⟨Fin.cons (1 - ∑ i, a x i) (a x), by
        constructor
        · intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · aesop
          · exact ha0 x j
        · aesop⟩
    have henc : Continuous enc := by fun_prop
    let dec : stdSimplex ℝ (Fin (n + 1)) → E :=
      fun y => e.symm (fun i => D * y.val i.succ - R)
    have hdec : Continuous dec := e.symm.continuous.comp (continuous_pi fun i =>
        (continuous_const.mul ((continuous_apply i.succ).comp continuous_subtype_val)).sub
          continuous_const)
    have hdecenc (x : Metric.closedBall (0 : E) 1) : dec (enc x) = (x : E) := by
      apply e.injective
      simp only [dec, ContinuousLinearEquiv.apply_symm_apply]
      funext i
      change D * ((e (x : E) i + R) / D) - R = e (x : E) i
      field_simp
      ring
    let ret : stdSimplex ℝ (Fin (n + 1)) → Metric.closedBall (0 : E) 1 :=
      fun y => unitBallClamp (dec y)
    have hret := continuous_unitBallClamp.comp hdec
    have hretenc (x : Metric.closedBall (0 : E) 1) : ret (enc x) = x := by
      dsimp [ret]
      rw [hdecenc]
      aesop (add norm [unitBallClamp])
    obtain ⟨y, hy⟩ := Brouwer (n := ⟨n + 1, Nat.succ_pos _⟩) (enc ∘ f ∘ ret)
      (henc.comp (hf.comp hret))
    refine ⟨ret y, ?_⟩
    have hh := congrArg ret hy
    simpa only [Function.comp_apply, hretenc] using hh

end GS.Topology
