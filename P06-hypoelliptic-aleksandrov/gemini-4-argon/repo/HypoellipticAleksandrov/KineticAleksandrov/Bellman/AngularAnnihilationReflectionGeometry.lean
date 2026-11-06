module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

/-! # Reflection of the actual punctured position–velocity plane -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/- Simultaneous reflection of position and velocity on the punctured plane. -/
def bellmanReflection : BellmanPuncturedPlane ≃ₜ BellmanPuncturedPlane where
  toFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  invFun q := ⟨-q.val, by
    change -q.val ≠ (0 : ℝ × ℝ)
    exact neg_ne_zero.mpr q.property⟩
  left_inv q := by apply Subtype.ext; exact neg_neg _
  right_inv q := by apply Subtype.ext; exact neg_neg _
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/- Reflection commutes with every positive kinetic dilation. -/
theorem bellman_reflected_fderiv (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (q e : ℝ × ℝ) :
    fderiv ℝ (fun z => φ (-z)) q e = -fderiv ℝ φ (-q) e := by
  have hd := (hφ.differentiable (by simp) (-q)).hasFDerivAt.comp q
    ((hasFDerivAt_id q).neg)
  change fderiv ℝ (φ ∘ Neg.neg) q e = _
  rw [hd.fderiv]
  change fderiv ℝ φ (-q) (-e) = -fderiv ℝ φ (-q) e
  exact map_neg _ _

/- The second velocity jet of a reflected test retains its sign. -/
end HypoellipticAleksandrov.KineticAleksandrov
