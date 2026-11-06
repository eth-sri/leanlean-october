module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceTraces
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonNodes
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonRadial
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Velocity-quadratic source barrier

The diffused position coordinate in Section Two is the physical velocity coordinate.
Lower ellipticity gives the required dimension-dependent quadratic supersolution.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov Parabolic Set Matrix Evolution
open scoped MatrixOrder

/- Quadratic source barrier in the diffused coordinate. -/
def boundedSourceQuadratic {d } (c : PDE.Vec d) (R lam : ℝ)
    (p : KineticPoint d) : ℝ :=
  (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)

/- The quadratic barrier is continuous without any sign assumptions on its parameters. -/
theorem continuous_boundedSourceQuadratic {d } (c : PDE.Vec d) (R lam : ℝ) :
    Continuous (boundedSourceQuadratic c R lam) :=
  (continuous_const.sub
    ((contDiff_vecNormSq_sub c).continuous.comp continuous_position)).div_const _

/- Every coordinate slice of the quadratic barrier has the required classical regularity. -/
theorem isSliceRegularAt_boundedSourceQuadratic {d } (c : PDE.Vec d)
    (R lam : ℝ) (p : KineticPoint d) :
    IsSliceRegularAt (boundedSourceQuadratic c R lam) p := by
  unfold boundedSourceQuadratic
  refine ⟨?_, ?_, ?_⟩
  · change DifferentiableAt ℝ (fun _ : ℝ =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.time
    exact differentiableAt_const _
  · change ContDiffAt ℝ 2 (fun y : PDE.Vec d =>
      (R ^ 2 - PDE.vecNormSq (y - c)) / (2 * (d : ℝ) * lam)) p.position
    exact ((contDiff_const.sub (contDiff_vecNormSq_sub c)).div_const _).contDiffAt
  · change ContDiffAt ℝ 2 (fun _ : PDE.Vec d =>
      (R ^ 2 - PDE.vecNormSq (p.position - c)) / (2 * (d : ℝ) * lam)) p.velocity
    exact contDiffAt_const

/- Lower Loewner ellipticity controls the trace in the exact dimension normalization. -/
theorem trace_ge_of_smul_one_le {d } {A : PDE.Mat d} {lam }
    (h : lam • (1 : PDE.Mat d) ≤ A) : (d : ℝ) * lam ≤ A.trace := by
  have htrace := (Matrix.le_iff.mp h).trace_nonneg
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one] at htrace
  simp only [Fintype.card_fin, smul_eq_mul] at htrace
  linarith

/- The unregularized kinetic operator of the quadratic barrier. -/
theorem boundedSource_sliceRegular_of_smooth {d } (u : KineticPoint d → ℝ)
    (p )
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) (u ∘ evolutionHomeomorph d)
      ((evolutionHomeomorph d).symm p)) : IsSliceRegularAt u p := by
  apply IsSliceRegularAt.of_contDiffAt
  have h := hu.comp (p.time, p.position, p.velocity)
    (evolutionProdCLE d).symm.contDiff.contDiffAt
  have hraw : rawLift u = (u ∘ evolutionHomeomorph d) ∘ (evolutionProdCLE d).symm := by
    funext q
    change u ⟨q.1, q.2.1, q.2.2⟩ = u (evolutionHomeomorph d (Occupation.packQ d q))
    rw [duhamel_homeomorph_packQ]
  rw [hraw]
  exact h.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

/- The quadratic barrier is nonnegative on the closed ball in the actual Euclidean geometry. -/
theorem boundedSourceQuadratic_nonneg {d lam}
    (hlam : 0 < lam) (c : PDE.Vec d) (R : ℝ) (p : KineticPoint d)
    (hp : p.position ∈ closure (PDE.euclideanBall c R)) :
    0 ≤ boundedSourceQuadratic c R lam p := by
  have hs : closure (PDE.euclideanBall c R) ⊆
      {y : PDE.Vec d | PDE.vecNormSq (y - c) ≤ R ^ 2} := by
    apply closure_minimal
    · intro y hy
      change PDE.vecNormSq (y - c) < R ^ 2 at hy
      exact le_of_lt hy
    · exact isClosed_le (contDiff_vecNormSq_sub c).continuous continuous_const
  exact div_nonneg (sub_nonneg.mpr (hs hp))
    (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hlam.le)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
