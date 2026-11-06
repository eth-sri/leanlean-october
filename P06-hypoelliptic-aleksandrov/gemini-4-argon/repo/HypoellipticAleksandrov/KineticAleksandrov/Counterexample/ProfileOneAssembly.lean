module

public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.Profile
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileHomogeneousBounds
public import HypoellipticAleksandrov.KineticAleksandrov.Counterexample.ProfileWeakExtension
import Mathlib.Tactic.Linarith

/-! # Scalar branch assembly into the shared profile interface -/

@[expose] public section

namespace HypoellipticAleksandrov.KineticAleksandrov.Counterexample

open MeasureTheory Set
open scoped MatrixOrder

/- Scalar multiples of the identity preserve the scalar order. -/
theorem scalar_identity_le {d } (a b : ℝ) (hab : a ≤ b) :
    a • (1 : PDE.Mat d) ≤ b • (1 : PDE.Mat d) := by
  apply Matrix.le_iff.mpr
  simpa only [sub_smul] using
    (Matrix.PosSemidef.one (n := Fin d) (R := ℝ)).smul (sub_nonneg.mpr hab)

/- The literal scalar coefficient is entrywise measurable. -/
theorem measurable_scalarProfileCoefficient (Lam : ℝ) (i k : Fin 1) :
    Measurable (fun q => scalarProfileCoefficient Lam q i k) := by
  have hm : Measurable (fun q : XV 1 => q.1 0 * q.2 0) :=
    ((measurable_pi_apply 0).comp measurable_fst).mul
      ((measurable_pi_apply 0).comp measurable_snd)
  have hs : MeasurableSet {q : XV 1 | q.1 0 * q.2 0 < 0} :=
    measurableSet_lt hm measurable_const
  exact (measurable_const.ite hs measurable_const).mul measurable_const

/- The scalar coefficient has the source's uniform ellipticity bounds everywhere. -/
theorem scalarProfileCoefficient_order (Lam : ℝ) (hLam : 1 < Lam) (q : XV 1) :
    (1 : ℝ) • (1 : PDE.Mat 1) ≤ scalarProfileCoefficient Lam q ∧
      scalarProfileCoefficient Lam q ≤ Lam • (1 : PDE.Mat 1) := by
  unfold scalarProfileCoefficient
  split_ifs
  · exact ⟨scalar_identity_le 1 Lam hLam.le, le_refl _⟩
  · exact ⟨le_refl _, scalar_identity_le 1 Lam hLam.le⟩

/- The scalar branch yields the whole-carrier profile with no additional analytic premises. -/
end HypoellipticAleksandrov.KineticAleksandrov.Counterexample
