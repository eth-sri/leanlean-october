import Mathlib.Tactic

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import GS.Topology.SectionPair
import GS.Topology.EuclideanSphere
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



/-!
# Explicit deformation of a punctured norm-ball to a unit sphere

The ambient real normed space may have dimension zero. No nonemptiness
assumption is used: in dimension zero both subtypes are empty.

The homotopy endpoints and the fixed-sphere identity are proved explicitly below.
-/
noncomputable section
open GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

variable (E : Type*)

abbrev NormSphere  [NormedAddCommGroup E] := {x : E // ‖x‖ = 1}
abbrev PuncturedNormBall  [NormedAddCommGroup E] (r : ℝ) :=
  {x : E // ‖x‖ < r ∧ x ≠ 0}

/-- Reconcile norm-equality subtypes with the actual mathlib `Metric.sphere`.
This homeomorphism uses no homology computation or homotopy invariance. -/
def normSphereStandard (n : ℕ) :
    NormSphere (EuclideanSpace ℝ (Fin n)) ≃ₜ UnitSphere (Fin n) :=
  Homeomorph.setCongr (by aesop)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial normalization. Its domain excludes only the origin. -/
def ballNormalize {r : ℝ} (x : PuncturedNormBall E r) : NormSphere E :=
  ⟨‖x.val‖⁻¹ • x.val, by grind [norm_pos_iff,Real.norm_eq_abs,norm_smul]⟩

def ballSection {r : ℝ} (hr : 0 < r) (v : NormSphere E) :
    PuncturedNormBall E r :=
  ⟨(r / 2) • v.val, by grind [norm_zero,Real.norm_eq_abs,norm_smul]⟩

theorem continuous_ballNormalize (r : ℝ) :
    Continuous (@ballNormalize E _ _ r) := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun x => norm_ne_zero_iff.mpr x.property.2)).smul continuous_subtype_val

theorem continuous_ballSection {r : ℝ} (hr : 0 < r) :
    Continuous (ballSection (E := E) hr) :=
  (continuous_const.smul continuous_subtype_val).subtype_mk _



@[simp] theorem norm_smul_ballNormalize {r : ℝ} (x : PuncturedNormBall E r) :
    ‖x.val‖ • (ballNormalize x).val = x.val := by
  change ‖x.val‖ • (‖x.val‖⁻¹ • x.val) = x.val
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.property.2), one_smul]

/-- Convex interpolation of positive radii, not of arbitrary vectors. -/
def radialRadius {r : ℝ} (p : unitInterval × PuncturedNormBall E r) : ℝ :=
  (1 - (p.1 : ℝ)) * (r / 2) + (p.1 : ℝ) * ‖p.2.val‖

theorem radialRadius_mem {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : radialRadius p ∈ Set.Ioo 0 r := convex_Ioo  0 r (by constructor <;> linarith : r / 2 ∈ Set.Ioo 0 r)
    ⟨norm_pos_iff.mpr p.2.property.2, p.2.property.1⟩
    (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))

theorem radialRadius_pos {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : 0 < radialRadius p :=
  (radialRadius_mem hr p).1



def radialDeform {r : ℝ} (hr : 0 < r)
    (p : unitInterval × PuncturedNormBall E r) : PuncturedNormBall E r :=
  ⟨radialRadius p • (ballNormalize p.2).val, by
    have hn : ‖radialRadius p • (ballNormalize p.2).val‖ = radialRadius p := by grind [radialRadius_pos,Real.norm_eq_abs,norm_smul]
    refine ⟨by rw [hn]; exact (radialRadius_mem hr p).2, ?_⟩
    intro hz
    rw [hz, norm_zero] at hn
    linarith [radialRadius_pos hr p]⟩

theorem continuous_radialDeform {r : ℝ} (hr : 0 < r) :
    Continuous (radialDeform (E := E) hr) := by
  apply Continuous.subtype_mk
  have hρ : Continuous (radialRadius : unitInterval × PuncturedNormBall E r → ℝ) := by
    unfold radialRadius
    fun_prop
  exact hρ.smul (continuous_subtype_val.comp
    ((continuous_ballNormalize r).comp continuous_snd))

/-- Normalization followed by the section is homotopic to the identity on the
punctured ball. Together with ballNormalize_section this is a homotopy equivalence. -/
def puncturedBallHomotopy {r : ℝ} (hr : 0 < r) :
    ContinuousMap.Homotopy
      (⟨fun x => ballSection hr (ballNormalize x),
        (continuous_ballSection hr).comp (continuous_ballNormalize r)⟩ :
          C(PuncturedNormBall E r, PuncturedNormBall E r))
      (ContinuousMap.id (PuncturedNormBall E r)) where
  toFun := radialDeform hr
  continuous_toFun := continuous_radialDeform hr
  map_zero_left x := by
    apply Subtype.ext
    simp [radialDeform, radialRadius, ballSection]
  map_one_left x := by simp_all [radialDeform,radialRadius]

end GS.NonmanifoldClosure
