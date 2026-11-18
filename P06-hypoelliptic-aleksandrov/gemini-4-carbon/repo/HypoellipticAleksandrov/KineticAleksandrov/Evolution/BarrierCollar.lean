module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Positivity
import HypoellipticAleksandrov.Parabolic.MinimumPrinciple
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonGrowth

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Filter Set HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic Matrix
open scoped Topology MatrixOrder


/-- The collar profile `w(r₀ - √s)` with `w(t) = (1 - exp (-κ t)) / κ`. -/
def collarProfile (κ r₀ s : ℝ) : ℝ :=
  (1 - Real.exp (-κ * (r₀ - Real.sqrt s))) / κ

/-- First derivative of the collar profile in the squared distance. -/
theorem hasDerivAt_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (collarProfile κ r₀) (-(Real.exp (-κ * (r₀ - Real.sqrt s)) /
      (2 * Real.sqrt s))) s := by
  have h2 := ((Real.hasDerivAt_sqrt hs.ne').const_sub r₀).const_mul (-κ)
  have h4 := ((hasDerivAt_const s 1).sub h2.exp).div_const κ
  refine h4.congr_deriv ?_
  field_simp
  ring

/-- The first derivative of the collar profile. -/
theorem deriv_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (collarProfile κ r₀) s =
      -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (2 * Real.sqrt s)) :=
  (hasDerivAt_collarProfile hκ r₀ hs).deriv

/-- Second derivative of the collar profile in the squared distance. -/
theorem hasDerivAt_collarProfile_deriv {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (deriv (collarProfile κ r₀))
      (-(Real.exp (-κ * (r₀ - Real.sqrt s)) / (4 * s)) * (κ - 1 / Real.sqrt s)) s := by
  have hsq := (Real.sqrt_pos.mpr hs).ne'
  have h1 := Real.hasDerivAt_sqrt hs.ne'
  have h2 := (h1.const_sub r₀).const_mul (-κ)
  have h3 := h2.exp
  have h5 := (h3.div (h1.const_mul 2) (by positivity)).neg
  have heq : deriv (collarProfile κ r₀) =ᶠ[𝓝 s]
      fun s => -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (2 * Real.sqrt s)) := by
    filter_upwards [lt_mem_nhds hs] with t ht
    exact deriv_collarProfile hκ r₀ ht
  refine (h5.congr_of_eventuallyEq heq).congr_deriv ?_
  have hs2 := Real.sq_sqrt hs.le
  generalize Real.sqrt s = ρ at *
  subst hs2
  field_simp
  ring

/-- The collar profile is `C²` away from the centre. -/
theorem contDiffAt_collarProfile (κ r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    ContDiffAt ℝ 2 (collarProfile κ r₀) s := by
  have h1 : ContDiffAt ℝ 2 Real.sqrt s := contDiffAt_id.sqrt hs.ne'
  unfold collarProfile
  have h2 : ContDiffAt ℝ 2 (fun s => -κ * (r₀ - Real.sqrt s)) s :=
    contDiffAt_const.mul (contDiffAt_const.sub h1)
  exact (contDiffAt_const.sub h2.exp).div_const κ

/-- The second derivative of the collar profile. -/
theorem deriv_deriv_collarProfile {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {s : ℝ} (hs : 0 < s) :
    deriv (deriv (collarProfile κ r₀)) s =
      -(Real.exp (-κ * (r₀ - Real.sqrt s)) / (4 * s)) * (κ - 1 / Real.sqrt s) :=
  (hasDerivAt_collarProfile_deriv hκ r₀ hs).deriv



/-- The collar barrier `w(r₀ - |y - m(σ)|)`, independent of the transported coordinate. -/
def collarBarrier {n : ℕ} (κ r₀ : ℝ) (m : ℝ → PDE.Vec n) (p : KineticPoint n) : ℝ :=
  collarProfile κ r₀ (PDE.vecNormSq (p.position - m p.time))

/-- The gradient of a constant function vanishes. -/
theorem classicalGradient_const {n : ℕ} (c : ℝ) (x : PDE.Vec n) :
    PDE.classicalGradient (fun _ : PDE.Vec n => c) x = 0 := by
  ext i
  simp [PDE.classicalGradient]

/-- The Hessian of a constant function vanishes. -/
theorem sliceHessian_const {n : ℕ} (c : ℝ) (x : PDE.Vec n) :
    sliceHessian (fun _ : PDE.Vec n => c) x = 0 := by
  have hz : (fun y => PDE.classicalGradient (fun _ : PDE.Vec n => c) y) =
      fun _ => 0 := by
    funext y
    exact classicalGradient_const c y
  ext i j
  simp only [sliceHessian, hz]
  simp

/-- `x ᵀ A x ≤ (tr A) |x|²` for positive semidefinite `A`. -/
theorem dotProduct_mulVec_le_trace_mul {n : ℕ} {A : PDE.Mat n} (hA : A.PosSemidef)
    (x : PDE.Vec n) :
    dotProduct x (A.mulVec x) ≤ A.trace * PDE.vecNormSq x := by
  let P := PDE.vecNormSq x • 1 - Matrix.vecMulVec x x
  have hP : P.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.ext
      intro i j
      simp only [P, star_trivial, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.vecMulVec_apply]
      by_cases h : i = j
      · subst h; simp
      · have h' : j ≠ i := fun e => h e.symm
        simp [h, h', mul_comm]
    · intro v
      have hcs := PDE.sq_vecDot_le_vecNormSq_mul_vecNormSq x v
      have e : dotProduct (star v) (P.mulVec v) =
          PDE.vecNormSq x * PDE.vecNormSq v - PDE.vecDot x v ^ 2 := by
        simp [P, star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec, dotProduct_sub, dotProduct_smul]
        simp [PDE.vecNormSq, PDE.vecDot, dotProduct, pow_two, mul_comm]
      rw [e]
      linarith
  have h1 := trace_mul_nonneg_of_posSemidef hA hP
  have h2 : (A * P).trace = A.trace * PDE.vecNormSq x - dotProduct x (A.mulVec x) := by
    simp [P, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul]
    rw [mul_comm]
    congr 1
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
      Matrix.mulVec]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  linarith

/-- A lower Loewner bound gives `λ |x|² ≤ x ᵀ A x`. -/
theorem mul_vecNormSq_le_dotProduct_mulVec {n : ℕ} {A : PDE.Mat n} {lam : ℝ}
    (h : lam • (1 : PDE.Mat n) ≤ A) (x : PDE.Vec n) :
    lam * PDE.vecNormSq x ≤ dotProduct x (A.mulVec x) := by
  have h2 := (Matrix.le_iff.mp h).dotProduct_mulVec_nonneg x
  simp [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul] at h2
  have : dotProduct x x = PDE.vecNormSq x := rfl
  rw [this] at h2
  linarith

/-- The collar barrier is slice regular where the centre is differentiable and `y ≠ m(σ)`. -/
theorem isSliceRegularAt_collarBarrier {n : ℕ} (κ r₀ : ℝ) {m : ℝ → PDE.Vec n}
    {p : KineticPoint n} (hm : DifferentiableAt ℝ m p.time)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time)) :
    IsSliceRegularAt (collarBarrier κ r₀ m) p := by
  refine ⟨?_, ?_, ?_⟩
  · have hS' : DifferentiableAt ℝ (fun t => PDE.vecNormSq (p.position - m t)) p.time := by
      have hfun : (fun t => PDE.vecNormSq (p.position - m t)) =
          fun t => ∑ i, (p.position i - m t i) ^ 2 := by
        funext t
        rw [PDE.vecNormSq_eq_sum_sq]
        rfl
      rw [hfun]
      refine DifferentiableAt.fun_sum (fun i _ => ?_)
      have : DifferentiableAt ℝ (fun t => m t i) p.time :=
        (differentiableAt_pi.mp hm) i
      exact (this.const_sub (p.position i)).pow 2
    exact ((contDiffAt_collarProfile κ r₀ hS).differentiableAt (by norm_num)).comp p.time hS'
  · exact (contDiffAt_collarProfile κ r₀ hS).comp p.position
      (contDiff_vecNormSq_sub (m p.time)).contDiffAt
  · exact (show ContDiffAt ℝ 2 (fun _ => collarBarrier κ r₀ m p) p.velocity from
      contDiffAt_const)

/-- Pure algebra of the collar computation. -/
theorem collar_algebra {E κ ρ S X t g W' W'' : ℝ} (hρ : 0 < ρ) (hS : S = ρ ^ 2)
    (hW' : W' = -(E / (2 * ρ))) (hW'' : W'' = -(E / (4 * S)) * (κ - 1 / ρ)) :
    W' * (-2 * g) + (4 * W'' * X + 2 * W' * t) =
      E * (-κ * (X / S) - (t - X / S) / ρ + g / ρ) := by
  subst hW' hW'' hS
  field_simp
  ring


/-- The collar inequality `L_ε w(d) ≤ w'(d) (L_γ - λ κ)` with `w'(d) = exp (-κ d)`, where
`L_γ` bounds the speed `|m'|` of the centre and `λ I ≤ B`. -/
theorem viscousTransportedOperator_collarBarrier_le {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (ε : ℝ) {κ lam Lγ : ℝ} (hκ : 0 < κ) (hlam : 0 ≤ lam)
    (r₀ : ℝ) {m : ℝ → PDE.Vec n} {m' : PDE.Vec n} {p : KineticPoint n}
    (hm : HasDerivAt m m' p.time) (hm' : PDE.vecEuclideanNorm m' ≤ Lγ)
    (hS : 0 < PDE.vecNormSq (p.position - m p.time))
    (hB : lam • (1 : PDE.Mat n) ≤ B p.time p.position p.velocity) :
    viscousTransportedOperator B b ε (collarBarrier κ r₀ m) p ≤
      Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - m p.time)))) *
        (Lγ - lam * κ)  := by
  have viscousTransportedOperator_collarBarrier (ε : ℝ) {κ : ℝ} (hκ : κ ≠ 0) (r₀ : ℝ) {m : ℝ → PDE.Vec n} {m' : PDE.Vec n} {p : KineticPoint n} (hm : HasDerivAt m m' p.time) (hS : 0 < PDE.vecNormSq (p.position - m p.time)) :
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
    have hΨd := (contDiffAt_collarProfile κ r₀ hS).differentiableAt (by norm_num)
    have htime : kineticTimeDerivative (collarBarrier κ r₀ m) p =
        deriv (collarProfile κ r₀) (PDE.vecNormSq (p.position - m p.time)) *
          (-2 * ∑ i, (p.position i - m p.time i) * m' i) :=
      (hasDerivAt_comp_vecNormSq_sub_moving (Ψ := collarProfile κ r₀) p.position hm hΨd).deriv
    have hdiff : matrixContraction (B p.time p.position p.velocity)
        (diffusedHessian (collarBarrier κ r₀ m) p) =
        4 * deriv (deriv (collarProfile κ r₀)) (PDE.vecNormSq (p.position - m p.time)) *
          dotProduct (p.position - m p.time)
            ((B p.time p.position p.velocity).mulVec (p.position - m p.time)) +
        2 * deriv (collarProfile κ r₀) (PDE.vecNormSq (p.position - m p.time)) *
          (B p.time p.position p.velocity).trace := by
      rw [diffusedHessian_eq_sliceHessian]
      exact matrixContraction_sliceHessian_comp_vecNormSq_sub
        (Ψ := collarProfile κ r₀)
        (contDiffAt_collarProfile κ r₀ hS) _
    have hgrad : kineticVelocityGradient (collarBarrier κ r₀ m) p = 0 :=
      classicalGradient_const (collarBarrier κ r₀ m p) p.velocity
    have hlap : ∑ i, kineticVelocityHessian (collarBarrier κ r₀ m) p i i = 0 := by
      have : kineticVelocityHessian (collarBarrier κ r₀ m) p = 0 :=
        sliceHessian_const (collarBarrier κ r₀ m p) p.velocity
      simp [this]
    rw [viscousTransportedOperator_apply, transportedForwardOperator_apply]
    simp only [fullKineticCoefficientAt_apply]
    rw [htime, hdiff, hgrad, hlap, deriv_collarProfile hκ r₀ hS,
      deriv_deriv_collarProfile hκ r₀ hS]
    have hρ : 0 < Real.sqrt (PDE.vecNormSq (p.position - m p.time)) := Real.sqrt_pos.mpr hS
    have hsum : ∑ i, (p.position i - m p.time i) * m' i = PDE.vecDot (p.position - m p.time) m' :=
      rfl
    have h0 : PDE.vecDot (b p.position) 0 = 0 := by simp [PDE.vecDot]
    rw [h0, hsum]
    have := collar_algebra
      (E := Real.exp (-κ * (r₀ - Real.sqrt (PDE.vecNormSq (p.position - m p.time)))))
      (κ := κ) (X := dotProduct (p.position - m p.time)
        ((B p.time p.position p.velocity).mulVec (p.position - m p.time)))
      (t := (B p.time p.position p.velocity).trace)
      (g := PDE.vecDot (p.position - m p.time) m') hρ (Real.sq_sqrt hS.le).symm rfl rfl
    simp only [mul_zero, add_zero]
    linarith
  rw [viscousTransportedOperator_collarBarrier ε hκ.ne' r₀ hm hS]
  set x := p.position - m p.time with hx
  set S := PDE.vecNormSq x with hSdef
  set A := B p.time p.position p.velocity with hA
  set X := dotProduct x (A.mulVec x) with hX
  have hρ : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hApsd : A.PosSemidef := by
    have h0 : 0 ≤ lam • (1 : PDE.Mat n) := by
      rw [Matrix.nonneg_iff_posSemidef]
      exact Matrix.PosSemidef.one.smul hlam
    exact Matrix.nonneg_iff_posSemidef.mp (h0.trans hB)
  have hXS : lam ≤ X / S := by rw [le_div_iff₀ hS]; exact (mul_vecNormSq_le_dotProduct_mulVec hB x)
  have hXt : X / S ≤ A.trace := by rw [div_le_iff₀ hS]; exact (dotProduct_mulVec_le_trace_mul hApsd x)
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
  have hbracket : -κ * (X / S) - (A.trace - X / S) / Real.sqrt S +
      PDE.vecDot x m' / Real.sqrt S ≤ Lγ - lam * κ := by
    linarith
  exact mul_le_mul_of_nonneg_left hbracket hEpos.le

/-- The collar barrier is a supersolution: with `κ λ = 1 + L_γ` one has `L_ε w(d) ≤ 0`. -/
theorem viscousTransportedOperator_collarBarrier_nonpos {n : ℕ} {B : FullKineticCoefficient n}
    {b : PDE.Vec n → PDE.Vec n} (ε : ℝ) {κ lam Lγ : ℝ} (hκ : 0 < κ) (hlam : 0 ≤ lam)
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

