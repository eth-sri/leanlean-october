module

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierProfile
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Ring



/-!
# The collar supersolution `w(d)`

Proposition 2.1: with `d = r₀ - |y - m(σ)|`, `κ = (1 + L_γ)/λ` and
`w(t) = (1 - exp (-κ t))/κ`, the function `(σ, y, z) ↦ w(d)` satisfies, for every
`ε ≥ 0` and wherever `y ≠ m(σ)` and `m` is differentiable,
`L_ε w(d) = w'' e·Be - (w'/|y-m|)(tr B - e·Be) + w' m'·e ≤ w'(L_γ - λκ) = -w' ≤ 0`.
Here `e = (y - m)/|y - m|`, and `m = γ + c` is the centre of the moving ball.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov

open HypoellipticAleksandrov.Parabolic Matrix
open scoped MatrixOrder

variable {n : ℕ}

/-- The collar barrier `w(r₀ - |y - m(σ)|)`, independent of the transported coordinate. -/
def collarBarrier  (κ r₀ : ℝ) (m : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  collarProfile κ r₀ (PDE.vecNormSq (p.position - m p.time))

variable (c : ℝ) (x : PDE.Vec n)

/-- The gradient of a constant function vanishes. -/
theorem classicalGradient_const   :
    PDE.classicalGradient (fun _ : PDE.Vec n => c) x = 0 := by
  ext i
  simp [PDE.classicalGradient]

/-- The Hessian of a constant function vanishes. -/
theorem sliceHessian_const   :
    sliceHessian (fun _ : PDE.Vec n => c) x = 0 := by
  have hz : PDE.classicalGradient (fun _ : PDE.Vec n => c) = (0 : PDE.VectorField n) := by
    ext y i
    simp [PDE.classicalGradient]
  unfold sliceHessian
  rw [hz]
  ext <;> simp

variable {A : PDE.Mat n}

/-- `x ᵀ A x ≤ (tr A) |x|²` for positive semidefinite `A`. -/
theorem dotProduct_mulVec_le_trace_mul   (hA : A.PosSemidef)
    (x : PDE.Vec n) :
    dotProduct x (A.mulVec x) ≤ A.trace * PDE.vecNormSq x := by
  let P  := PDE.vecNormSq x • (1 : PDE.Mat n) - Matrix.vecMulVec x x

  have h1 := trace_mul_nonneg_of_posSemidef hA (show P.PosSemidef by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · apply Matrix.IsHermitian.ext
        intro i j
        simp only [P, star_trivial, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          Matrix.vecMulVec_apply]
        by_cases h : i = j
        · subst h; simp
        · grind
      · intro v
        have hcs := PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq x v
        have e : dotProduct (star v) (P.mulVec v) =
            PDE.vecNormSq x * PDE.vecNormSq v - PDE.vecDot x v ^ 2 := by
          simp only [P, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
            Matrix.vecMulVec_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
          simp [PDE.vecNormSq, PDE.vecDot, dotProduct, pow_two, mul_comm]
        rw [e]
        linarith)
  have h2 : (A * P).trace = A.trace * PDE.vecNormSq x - dotProduct x (A.mulVec x) := by
    simp only [P, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, smul_eq_mul]
    rw [mul_comm]
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
      Matrix.mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  linarith

/-- A lower Loewner bound gives `λ |x|² ≤ x ᵀ A x`. -/
theorem mul_vecNormSq_le_dotProduct_mulVec   {lam : ℝ}
    (h : lam • (1 : PDE.Mat n) ≤ A) (x : PDE.Vec n) :
    lam * PDE.vecNormSq x ≤ dotProduct x (A.mulVec x) := (vecDot_mulVec_lower_of_loewner h x)

/-- The collar barrier is slice regular where the centre is differentiable and `y ≠ m(σ)`. -/
theorem isSliceRegularAt_collarBarrier  (κ r₀ : ℝ) {m : ℝ → PDE.Vec n}
    {p : KineticPoint n} (hm : DifferentiableAt ℝ m p.time)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time)) :
    IsSliceRegularAt (collarBarrier κ r₀ m) p := by
  refine ⟨?_, ?_, ?_⟩
  ·
    exact ((contDiffAt_collarProfile κ r₀ hS).differentiableAt (by norm_num)).comp p.time (by
        have hfun : (fun t => PDE.vecNormSq (p.position - m t)) =
            fun t => ∑ i, (p.position i - m t i) ^ 2 := by
          funext t
          rw [PDE.vecNormSq_eq_sum_sq]
          rfl
        rw [hfun]
        refine DifferentiableAt.fun_sum (fun i _ => ?_)
        have : DifferentiableAt ℝ (fun t => m t i) p.time :=
          (differentiableAt_pi.mp hm) i
        exact (this.const_sub (p.position i)).pow 2)
  · exact (contDiffAt_collarProfile κ r₀ hS).comp p.position
      (contDiff_vecNormSq_sub (m p.time)).contDiffAt
  · exact (show ContDiffAt ℝ 2 (fun _ : PDE.Vec n => collarBarrier κ r₀ m p) p.velocity from
      contDiffAt_const)



variable {n : ℕ} {B : FullKineticCoefficient n} {b : PDE.VectorField n} (ε : ℝ)

/-- The exact collar identity `L_ε w(d) = w'' e·Be - (w'/|y-m|)(tr B - e·Be) + w' m'·e`
with `w' = exp (-κ d)` and `w'' = -κ exp (-κ d)`; here `S = |y - m|²`, `X = x·Bx`,
`x = y - m`. -/
theorem viscousTransportedOperator_collarBarrier  {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {m : ℝ → PDE.Vec n}
    {m' : PDE.Vec n} {p : KineticPoint n} (hm : HasDerivAt m m' p.time)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time)) :
    viscousTransportedOperator B b ε (collarBarrier κ r₀ m) p =
      Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - m p.time)))) *
        (-κ * (dotProduct (p.position - m p.time)
              ((B p.time p.position p.velocity).mulVec (p.position - m p.time)) /
            PDE.vecNormSq (p.position - m p.time)) -
          ((B p.time p.position p.velocity).trace -
              dotProduct (p.position - m p.time)
                ((B p.time p.position p.velocity).mulVec (p.position - m p.time)) /
                PDE.vecNormSq (p.position - m p.time)) /
            Real.sqrt (PDE.vecNormSq (p.position - m p.time)) +
          PDE.vecDot (p.position - m p.time) m' /
            Real.sqrt (PDE.vecNormSq (p.position - m p.time))) := by
  let sharedTerm_db27d4aac9 := ((PDE.vecNormSq (p.position - m p.time)))
  let sharedTerm_58ddffb18e := (∑ i, (p.position i - m p.time i) * m' i)


  have hdiff : matrixContraction (B p.time p.position p.velocity)
      (diffusedHessian (collarBarrier κ r₀ m) p) =
      4 * deriv (deriv (collarProfile κ r₀)) sharedTerm_db27d4aac9 *
        dotProduct (p.position - m p.time)
          ((B p.time p.position p.velocity).mulVec (p.position - m p.time)) +
      2 * deriv (collarProfile κ r₀) sharedTerm_db27d4aac9 *
        (B p.time p.position p.velocity).trace := by
    rw [diffusedHessian_eq_sliceHessian]
    exact matrixContraction_sliceHessian_comp_vecNormSq_sub

      (contDiffAt_collarProfile κ r₀ hS) _
  have hgrad : kineticVelocityGradient (collarBarrier κ r₀ m) p = 0 :=
    classicalGradient_const (collarBarrier κ r₀ m p) p.velocity
  have hlap : ∑ i, kineticVelocityHessian (collarBarrier κ r₀ m) p i i = 0 := by
    have : kineticVelocityHessian (collarBarrier κ r₀ m) p = 0 :=
      sliceHessian_const (collarBarrier κ r₀ m p) p.velocity
    simp [this]
  rw [viscousTransportedOperator_apply, transportedForwardOperator_apply]
  simp only [fullKineticCoefficientAt_apply]
  rw [(show kineticTimeDerivative (collarBarrier κ r₀ m) p =
      deriv (collarProfile κ r₀) sharedTerm_db27d4aac9 *
        (-2 * sharedTerm_58ddffb18e) from (hasDerivAt_comp_vecNormSq_sub_moving  p.position hm ((contDiffAt_collarProfile κ r₀ hS).differentiableAt (by norm_num))).deriv), hdiff, hgrad, hlap, deriv_collarProfile hκ r₀ hS,
    deriv_deriv_collarProfile hκ r₀ hS]

  have hsum : sharedTerm_58ddffb18e = PDE.vecDot (p.position - m p.time) m' :=
    rfl
  have h0 : PDE.vecDot (b p.position) (0 ) = 0 := by simp [PDE.vecDot]
  rw [h0, hsum]
  ring

variable {κ lam Lγ : ℝ} (hκ : 0 < κ) (hlam : 0 ≤ lam)

include hκ hlam
/-- The collar inequality `L_ε w(d) ≤ w'(d) (L_γ - λ κ)` with `w'(d) = exp (-κ d)`, where
`L_γ` bounds the speed `|m'|` of the centre and `λ I ≤ B`. -/
theorem viscousTransportedOperator_collarBarrier_le
    (r₀ : ℝ) {m : ℝ → PDE.Vec n} {m' : PDE.Vec n} {p : KineticPoint n}
    (hm : HasDerivAt m m' p.time) (hm' : PDE.vecEuclideanNorm m' ≤ Lγ)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time))
    (hB : lam • (1 : PDE.Mat n) ≤ B p.time p.position p.velocity) :
    viscousTransportedOperator B b ε (collarBarrier κ r₀ m) p ≤
      Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - m p.time)))) *
        (Lγ - lam * κ) := by
  rw [viscousTransportedOperator_collarBarrier ε hκ.ne' r₀ hm hS]
  set x := p.position - m p.time with hx
  set S := PDE.vecNormSq x with hSdef
  set A := B p.time p.position p.velocity with hA
  set X := dotProduct x (A.mulVec x) with hX
  have hρ  := Real.sqrt_pos.mpr hS

  have hX1 : lam * S ≤ X := mul_vecNormSq_le_dotProduct_mulVec hB x
  have hX2 : X ≤ A.trace * S := dotProduct_mulVec_le_trace_mul (by

      exact Matrix.nonneg_iff_posSemidef.mp ((show (0 : PDE.Mat n) ≤ lam • (1 : PDE.Mat n) by
          rw [Matrix.nonneg_iff_posSemidef]
          exact Matrix.PosSemidef.one.smul hlam).trans hB)) x
  have hXS : lam ≤ X / S := by rw [le_div_iff₀ hS]; exact hX1
  have hXt : X / S ≤ A.trace := by rw [div_le_iff₀ hS]; exact hX2
  have hg : PDE.vecDot x m' ≤ Real.sqrt S * Lγ := by
    calc PDE.vecDot x m' ≤ |PDE.vecDot x m'| := le_abs_self _
      _ ≤ PDE.vecEuclideanNorm x * PDE.vecEuclideanNorm m' :=
          PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
      _ ≤ Real.sqrt S * Lγ :=
          mul_le_mul_of_nonneg_left hm' (Real.sqrt_nonneg _)
  have hgρ : PDE.vecDot x m' / Real.sqrt S ≤ Lγ := by
    rw [div_le_iff₀ hρ]
    linarith
  have hEpos : 0 < Real.exp (-κ * (r₀ - Real.sqrt S)) := Real.exp_pos _
  have hb1 : -κ * (X / S) ≤ -κ * lam := by nlinarith
  have hb2 : -((A.trace - X / S) / Real.sqrt S) ≤ 0 := by
    have : 0 ≤ (A.trace - X / S) / Real.sqrt S := div_nonneg (by linarith) hρ.le
    linarith

  exact mul_le_mul_of_nonneg_left (show _ by
      linarith) hEpos.le

/-- The collar barrier is a supersolution: with `κ λ = 1 + L_γ` one has `L_ε w(d) ≤ 0`. -/
theorem viscousTransportedOperator_collarBarrier_nonpos
    (hκlam : κ * lam = 1 + Lγ) (r₀ : ℝ) {m : ℝ → PDE.Vec n} {m' : PDE.Vec n}
    {p : KineticPoint n} (hm : HasDerivAt m m' p.time) (hm' : PDE.vecEuclideanNorm m' ≤ Lγ)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time))
    (hB : lam • (1 : PDE.Mat n) ≤ B p.time p.position p.velocity) :
    viscousTransportedOperator B b ε (collarBarrier κ r₀ m) p ≤ 0 := by
  have h := viscousTransportedOperator_collarBarrier_le (b := b) ε hκ hlam r₀ hm hm' hS hB
  have hE := Real.exp_pos (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - m p.time))))
  have : Lγ - lam * κ = -1 := by linarith
  rw [this] at h
  linarith

end HypoellipticAleksandrov.KineticAleksandrov
