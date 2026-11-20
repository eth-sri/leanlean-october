/- Explicit generic norm hypotheses, with no assumed Phi-null field. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Glennie.Compact.InnerBounds
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.MultiplicationDefectR01
noncomputable section
open Glennie.Compact.CyclicTraceNullR01
set_option autoImplicit false

variable {A E : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Product (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] V →ₗ[ℝ] V

def Q (j : Product A) (a b : A) : A := quadraticWith (fun u v => j u v) a b

def commutator (j : Product A) (x y z : A) : A :=
  Q j x (Q j y z) - Q j y (Q j x z)

def rightFactor (j : Product A) (x y z : A) : A := Q j z (j x y)

def response (j : Product A) (x y z : A) : ℝ :=
  phiWith (fun a b => j a b) (Inner.inner ℝ) x y z

/-- Linearity of the quadratic representation in its final argument. -/
theorem Q_sub (j : Product A) (a b c : A) : Q j a (b - c) = Q j a b - Q j a c := by
  simp [Q, quadraticWith] <;> module

variable (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
  (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
  (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
  (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
  (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
  (μ : ℝ) (hμ : 0 ≤ μ)
  (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)

include hA hE hμ hdef in
theorem quadratic_error (a b : A) :
    ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
  let D u v := f (jA u v) - jE (f u) (f v)
  have hD (u v : A) : ‖D u v‖ ≤ μ * ‖u‖ * ‖v‖ := hdef u v
  have expand : f (Q jA a b) - Q jE (f a) (f b) =
      (2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b) -
        D (jA a a) b - jE (D a a) (f b) := by
    simp only [Q, quadraticWith, D, map_sub, map_smul, LinearMap.sub_apply]
    module
  rw [expand]
  grw [norm_sub_le, norm_sub_le, norm_add_le]
  simp only [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  grw [hD a (jA a b), hE, hD (jA a a) b, hE, hD a b, hD a a, hA a b, hA a a]
  simp only [f.norm_map]; exact le_of_eq (by ring)

/- Transport through a quadratic representation, allowing an approximate input. -/
include hA hE hμ hdef hUE in
theorem transport_Q (a b : A) (v : E) :
    ‖f (Q jA a b) - Q jE (f a) v‖ ≤
      6 * μ * ‖a‖ ^ 2 * ‖b‖ + ‖a‖ ^ 2 * ‖f b - v‖ := by
  grw [← sub_add_sub_cancel (f (Q jA a b)) (Q jE (f a) (f b)) (Q jE (f a) v),
    norm_add_le, ← Q_sub, quadratic_error jA jE f hA hE μ hμ hdef, hUE, f.norm_map]

include hA hE hUA hUE hμ hdef in
theorem response_discrepancy (x y z : A) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤
      38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 := by
  have trQ := transport_Q jA jE f hA hE hUE μ hμ hdef
  have nested (a b : A) : ‖f (Q jA a (Q jA b z)) - Q jE (f a) (Q jE (f b) (f z))‖ ≤
      12 * μ * ‖a‖^2 * ‖b‖^2 * ‖z‖ := by
    grw [trQ, hUA, quadratic_error jA jE f hA hE μ hμ hdef]; exact le_of_eq (by ring)
  have hF : ‖f (commutator jA x y z) - commutator jE (f x) (f y) (f z)‖ ≤
      24 * μ * ‖x‖^2 * ‖y‖^2 * ‖z‖ := by
    simp only [commutator, map_sub]
    rw [sub_sub_sub_comm]; grw [norm_sub_le, nested x y, nested y x]; exact le_of_eq (by ring)
  have hH : ‖f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)‖ ≤
      7 * μ * ‖z‖^2 * ‖x‖ * ‖y‖ := by
    unfold rightFactor; grw [trQ, hA, hdef]; exact le_of_eq (by ring)
  have nH : ‖f (rightFactor jA x y z)‖ ≤ ‖z‖^2 * (‖x‖ * ‖y‖) := by
    unfold rightFactor; grw [f.norm_map, hUA, hA]
  have nF : ‖commutator jE (f x) (f y) (f z)‖ ≤ 2 * ‖x‖^2 * ‖y‖^2 * ‖z‖ := by
    unfold commutator; grw [norm_sub_le, hUE, hUE, hUE, hUE]; simp only [f.norm_map]; exact le_of_eq (by ring)
  change |Inner.inner ℝ (commutator jA x y z) (rightFactor jA x y z) - Inner.inner ℝ (commutator jE (f x) (f y) (f z)) (rightFactor jE (f x) (f y) (f z))| ≤ _
  rw [← f.inner_map_map]
  grw [pair_difference, hF, nH, nF, hH]; exact le_of_eq (by ring)

include hA hE hUA hUE hμ hdef in
theorem response_discrepancy_radius
    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤ 38 * μ * R ^ 9 := by
  calc
    _ ≤ 38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 :=
      response_discrepancy jA jE f hA hE hUA hUE μ hμ hdef x y z
    _ ≤ 38 * μ * R ^ 3 * R ^ 3 * R ^ 3 := by gcongr
    _ = _ := by ring


end
end Glennie.Compact.MultiplicationDefectR01
