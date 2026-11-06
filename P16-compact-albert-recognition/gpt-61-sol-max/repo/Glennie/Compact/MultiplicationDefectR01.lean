/- Explicit generic norm hypotheses, with no assumed Phi-null field. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.MultiplicationDefectR01
noncomputable section
open Glennie.Compact.CyclicTraceNullR01
variable {A E : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Product (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] V →ₗ[ℝ] V

def Q (j : Product A) (a : A) : A →ₗ[ℝ] A :=
  (2 : ℝ) • (j a).comp (j a) - j (j a a)

def commutator (j : Product A) (x y z : A) : A :=
  Q j x (Q j y z) - Q j y (Q j x z)

def rightFactor (j : Product A) (x y z : A) : A := Q j z (j x y)

def response (j : Product A) (x y z : A) : ℝ :=
  phiWith (fun a b => j a b) (Inner.inner ℝ) x y z

theorem pairing_difference (a b a' b' : A) :
    |Inner.inner ℝ a b - Inner.inner ℝ a' b'| ≤
      ‖a-a'‖ * ‖b‖ + ‖a'‖ * ‖b-b'‖ := by
  rw [show Inner.inner ℝ a b - Inner.inner ℝ a' b' =
    Inner.inner ℝ (a-a') b + Inner.inner ℝ a' (b-b') by
      simp only [_root_.inner_sub_left, _root_.inner_sub_right]; ring]
  grw [abs_add_le, abs_real_inner_le_norm, abs_real_inner_le_norm]

variable (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
variable (hQ : ∀ a b, ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤
      6 * μ * ‖a‖ ^ 2 * ‖b‖)

include hA hE hμ hdef in
/-- Bilinear multiplication error propagates to U with coefficient six. -/
theorem quadratic_error
    (a b : A) :
    ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
  let D : A → A → E := fun u v => f (jA u v) - jE (f u) (f v)
  have hD (u v : A) : ‖D u v‖ ≤ μ * ‖u‖ * ‖v‖ := hdef u v
  have hexpand : f (Q jA a b) - Q jE (f a) (f b) =
      (2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b) -
        D (jA a a) b - jE (D a a) (f b) := by
    simp only [Q, D, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    module
  rw [hexpand]
  grw [norm_sub_le, norm_sub_le, norm_add_le]
  norm_num [norm_smul]
  grw [hE, hE, hD, hD, hD, hD, hA, hA]
  simp only [f.norm_map]
  ring_nf
  exact le_rfl

include hUE hQ in
theorem quadratic_perturbation (a b : A) (c : E) :
    ‖f (Q jA a b) - Q jE (f a) c‖ ≤
      6 * μ * ‖a‖^2 * ‖b‖ + ‖a‖^2 * ‖f b - c‖ := by
  rw [show f (Q jA a b) - Q jE (f a) c =
      (f (Q jA a b) - Q jE (f a) (f b)) + Q jE (f a) (f b - c) by
    rw [map_sub]; module]
  grw [norm_add_le, hQ, hUE]
  rw [f.norm_map]

include hUA hUE hμ hQ in
/-- One composed quadratic word has transport error twelve. -/
theorem nested_error
     (x y z : A) :
    ‖f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))‖ ≤
      12 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  grw [quadratic_perturbation jA jE f hUE μ hQ, hUA, hQ]
  ring_nf
  rfl

include hUA hUE hμ hQ in
/-- Difference of the two composed words has transport error twenty-four. -/
theorem commutator_error
     (x y z : A) :
    ‖f (commutator jA x y z) - commutator jE (f x) (f y) (f z)‖ ≤
      24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  simp only [commutator, map_sub, ← dist_eq_norm]
  grw [dist_sub_sub_le]
  simp only [dist_eq_norm]
  grw [nested_error jA jE f hUA hUE μ hμ hQ,
    nested_error jA jE f hUA hUE μ hμ hQ]
  ring_nf
  rfl

include hA hUE hμ hdef hQ in
/-- The final U/product factor has transport error seven. -/
theorem rightFactor_error
     (x y z : A) :
    ‖f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)‖ ≤
      7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
  change ‖f (Q jA z (jA x y)) - Q jE (f z) (jE (f x) (f y))‖ ≤ _
  grw [quadratic_perturbation jA jE f hUE μ hQ, hA, hdef]
  ring_nf
  rfl

/-- Coefficient-one U bounds give a coefficient-two commutator bound. -/
theorem norm_commutator_le (j : Product A)
    (hU : ∀ a b, ‖Q j a b‖ ≤ ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖commutator j x y z‖ ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
  change ‖Q j x (Q j y z) - Q j y (Q j x z)‖ ≤ _
  grw [norm_sub_le, hU, hU, hU, hU]
  ring_nf
  exact le_rfl

theorem norm_rightFactor_le (j : Product A)
    (hJ : ∀ a b, ‖j a b‖ ≤ ‖a‖ * ‖b‖)
    (hU : ∀ a b, ‖Q j a b‖ ≤ ‖a‖ ^ 2 * ‖b‖) (x y z : A) :
    ‖rightFactor j x y z‖ ≤ ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
  change ‖Q j z (j x y)‖ ≤ _
  grw [hU, hJ]
  ring_nf
  exact le_rfl



include jA jE f hA hE hUA hUE μ hμ hdef in
/-- Generic metric/product discrepancy; no target vanishing assumption.
The sharper anisotropic form also handles zero arguments without division. -/
theorem response_discrepancy

    (x y z : A) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤
      38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 := by
  have hQ := quadratic_error jA jE f hA hE μ hμ hdef
  change |Inner.inner ℝ (commutator jA x y z) (rightFactor jA x y z) -
    Inner.inner ℝ (commutator jE (f x) (f y) (f z)) (rightFactor jE (f x) (f y) (f z))| ≤ _
  rw [← f.inner_map_map]
  grw [pairing_difference, f.norm_map,
    commutator_error jA jE f hUA hUE μ hμ hQ,
    norm_rightFactor_le jA hA hUA, norm_commutator_le jE hUE,
    rightFactor_error jA jE f hA hUE μ hμ hdef hQ]
  simp only [f.norm_map]
  ring_nf
  rfl

include jA jE f hA hE hUA hUE μ hμ hdef in
/-- Radius-ball form, with radius power nine and no smallness restriction on μ. -/
theorem response_discrepancy_radius

    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤ 38 * μ * R ^ 9 := by
  grw [response_discrepancy jA jE f hA hE hUA hUE μ hμ hdef, hx, hy, hz]
  ring_nf
  rfl


end
end Glennie.Compact.MultiplicationDefectR01
