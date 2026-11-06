module

public import GS.Topology.SectionPair
public import GS.Topology.EuclideanSphere
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homotopy.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section



/-!
# Explicit deformation of a punctured norm-ball to a unit sphere

The ambient real normed space may have dimension zero. No nonemptiness
assumption is used: in dimension zero both subtypes are empty.

The homotopy endpoints and the fixed-sphere identity are proved explicitly below.
-/
noncomputable section
open GS.NonmanifoldFinal
namespace GS.NonmanifoldClosure

section
variable (E : Type*) [NormedAddCommGroup E]
abbrev NormSphere := {x : E // ‖x‖ = 1}
abbrev PuncturedNormBall (r : ℝ) :=
  {x : E // ‖x‖ < r ∧ x ≠ 0}

end

/-- Reconcile norm-equality subtypes with the actual mathlib `Metric.sphere`.
This homeomorphism uses no homology computation or homotopy invariance. -/
def normSphereStandard (n : ℕ) :
    NormSphere (EuclideanSpace ℝ (Fin n)) ≃ₜ UnitSphere (Fin n) :=
  Homeomorph.setCongr (by aesop)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section
variable {r : ℝ}
/-- Radial normalization. Its domain excludes only the origin. -/
def ballNormalize (x : PuncturedNormBall E r) : NormSphere E :=
  ⟨‖x.val‖⁻¹ • x.val, by simp [norm_smul, x.property.2]⟩

def ballSection (hr : 0 < r) (v : NormSphere E) : PuncturedNormBall E r :=
  ⟨(r / 2) • v.val, by simp [norm_smul, v.property, abs_of_pos hr]; linarith,
    smul_ne_zero (by positivity) fun h => by simpa [h] using v.property⟩

theorem continuous_ballNormalize (r : ℝ) : Continuous (@ballNormalize E _ _ r) := by
  unfold ballNormalize; fun_prop (disch := exact fun x => by simp [x.2.2])

theorem continuous_ballSection (hr : 0 < r) : Continuous (ballSection (E := E) hr) := by
  unfold ballSection; fun_prop

/-- Convex interpolation of positive radii, not of arbitrary vectors. -/
def radialRadius (p : unitInterval × PuncturedNormBall E r) : ℝ :=
  (1 - (p.1 : ℝ)) * (r / 2) + (p.1 : ℝ) * ‖p.2.val‖

section
variable (hr : 0 < r) (p : unitInterval × PuncturedNormBall E r)
include hr in
theorem radialRadius_mem : 0 < radialRadius p ∧ radialRadius p < r := by
  have := norm_pos_iff.mpr p.2.property.2
  have := p.2.property.1
  rcases p.1.2.2.lt_or_eq with h | h <;> simp only [radialRadius, h] <;> constructor <;> nlinarith [p.1.2.1]

end

end

section
variable {r : ℝ} (hr : 0 < r)
/-- Normalization followed by the section is homotopic to the identity on the
punctured ball. Together with ballNormalize_section this is a homotopy equivalence. -/
def puncturedBallHomotopy :
    ContinuousMap.Homotopy
      (⟨fun x => ballSection hr (ballNormalize x),
        (continuous_ballSection hr).comp (continuous_ballNormalize r)⟩ :
          C(PuncturedNormBall E r, PuncturedNormBall E r))
      (ContinuousMap.id (PuncturedNormBall E r)) where
  toFun p := ⟨radialRadius p • (ballNormalize p.2).val, by
    simp [norm_smul, abs_of_pos (radialRadius_mem hr p).1, (ballNormalize p.2).property, (radialRadius_mem hr p).2],
    smul_ne_zero (radialRadius_mem hr p).1.ne' fun h => by simpa [h] using (ballNormalize p.2).property⟩
  continuous_toFun := by
    unfold radialRadius ballNormalize; fun_prop (disch := exact fun x => by simp [x.2.2.2])
  map_zero_left x := by simp [radialRadius, ballSection]
  map_one_left x := by simp [radialRadius, ballNormalize, smul_smul, x.property.2]

end

end GS.NonmanifoldClosure
