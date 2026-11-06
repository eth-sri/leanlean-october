module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FiniteUnionDomainsMixtures
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.BoundedSourceLimitsInfinite

/-! # Uniform finite mass of actual Green mixtures on finite interval unions -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov
open scoped ENNReal

variable (lam : ℝ) (H : FiniteIntervalUnion)

/-- A finite union's mass constant depends only on its interval lengths and ellipticity. -/
def finiteUnionGreenMassBound  : ℝ≥0∞ :=
  ∑ i : Fin H.count, ENNReal.ofReal (((H.component i).hi - (H.component i).lo) ^ 2 /
    (2 * lam))

/-- The geometric finite-union mass constant is finite. -/
theorem finiteUnionGreenMassBound_ne_top  :
    finiteUnionGreenMassBound lam H ≠ ⊤ := by
  simp_all [finiteUnionGreenMassBound]

variable (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (T : WithTop ℝ)

/-- Every actual union Green pole has the same uniform finite mass bound. -/
theorem finiteUnionGreen_mass_le

    (e : FiniteUnionPole H T) :
    finiteUnionGreen hH hLE hlam hLam A H T e univ ≤ finiteUnionGreenMassBound lam H := by
  let i := finiteUnionPoleIndex H T e
  let I := H.component i
  let ep := finiteUnionComponentPole H T e
  have hv := ep.2.2
  change I.lo < e.1.velocity 0 ∧ e.1.velocity 0 < I.hi at hv
  have hprod : (e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) ≤
      (I.hi - I.lo) ^ 2 := by
    have h1 : 0 ≤ e.1.velocity 0 - I.lo := by linarith
    have h2 : 0 ≤ I.hi - e.1.velocity 0 := by linarith
    nlinarith [sq_nonneg (e.1.velocity 0 - I.lo),
      sq_nonneg (I.hi - e.1.velocity 0), mul_nonneg h1 h2]
  have hb := stripGreen_quadratic_mass hH hLE hlam hLam A I T ep
  apply hb.trans
  apply (show ENNReal.ofReal ((e.1.velocity 0 - I.lo) * (I.hi - e.1.velocity 0) /
    (2 * lam)) ≤ ENNReal.ofReal ((I.hi - I.lo) ^ 2 / (2 * lam)) from
    ENNReal.ofReal_le_ofReal
      ((div_le_div_iff_of_pos_right (by positivity : 0 < 2 * lam)).mpr hprod)).trans
  unfold finiteUnionGreenMassBound
  exact Finset.single_le_sum
    (f := fun j : Fin H.count => ENNReal.ofReal
      (((H.component j).hi - (H.component j).lo) ^ 2 / (2 * lam)))
    (fun _ _ => zero_le) (Finset.mem_univ i)





end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
