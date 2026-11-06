/- Explicit generic norm hypotheses, with no assumed Phi-null field. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module

@[expose] public section
namespace Glennie.Compact.MultiplicationDefectR01
open Glennie.Compact.CyclicTraceNullR01

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

theorem Q_sub (j : Product A) (a b c : A) : Q j a (b - c) = Q j a b - Q j a c := by
  simp [Q, quadraticWith, map_sub]
  module

/-- Radius-ball form, with radius power nine and no smallness restriction on μ. -/
theorem response_discrepancy_radius
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤ 38 * μ * R ^ 9 := by
  have hQ (a b : A) : ‖f (Q jA a b) - Q jE (f a) (f b)‖ ≤ 6 * μ * ‖a‖ ^ 2 * ‖b‖ := by
    let D : A → A → E := fun u v => f (jA u v) - jE (f u) (f v)
    have hD (u v : A) : ‖D u v‖ ≤ μ * ‖u‖ * ‖v‖ := hdef u v
    have h2 := hE (f a) (D a b)
    have h4 := hE (D a a) (f b)
    have n1 := norm_sub_le ((2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b) -
      D (jA a a) b) (jE (D a a) (f b))
    have n2 := norm_sub_le ((2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b)) (D (jA a a) b)
    have n3 := norm_add_le ((2 : ℝ) • D a (jA a b)) ((2 : ℝ) • jE (f a) (D a b))
    rw [f.norm_map] at h2 h4
    simp [norm_smul] at n2 n3
    rw [show f (Q jA a b) - Q jE (f a) (f b) =
        (2 : ℝ) • D a (jA a b) + (2 : ℝ) • jE (f a) (D a b) - D (jA a a) b - jE (D a a) (f b) by
      simp [Q, quadraticWith, D, map_sub, map_smul, LinearMap.sub_apply]; module]
    linarith [hD a (jA a b), hD (jA a a) b,
      mul_le_mul_of_nonneg_left (hA a b) (mul_nonneg hμ (norm_nonneg a)),
      mul_le_mul_of_nonneg_left (hD a b) (norm_nonneg a),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA a a) hμ) (norm_nonneg b),
      mul_le_mul_of_nonneg_right (hD a a) (norm_nonneg b)]
  have hN (x y z : A) : ‖f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))‖ ≤
      12 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    have h := hUE (f x) (f (Q jA y z) - Q jE (f y) (f z))
    rw [f.norm_map] at h
    rw [show f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z)) =
        (f (Q jA x (Q jA y z)) - Q jE (f x) (f (Q jA y z))) +
        Q jE (f x) (f (Q jA y z) - Q jE (f y) (f z)) by rw [Q_sub]; module]
    linarith [norm_add_le (f (Q jA x (Q jA y z)) - Q jE (f x) (f (Q jA y z)))
      (Q jE (f x) (f (Q jA y z) - Q jE (f y) (f z))), hQ x (Q jA y z),
      mul_le_mul_of_nonneg_left (hUA y z) (by positivity : 0 ≤ 6 * μ * ‖x‖ ^ 2),
      mul_le_mul_of_nonneg_left (hQ y z) (sq_nonneg ‖x‖)]
  have hF : ‖f (commutator jA x y z) - commutator jE (f x) (f y) (f z)‖ ≤
      24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    rw [show f (commutator jA x y z) - commutator jE (f x) (f y) (f z) =
      (f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z))) -
      (f (Q jA y (Q jA x z)) - Q jE (f y) (Q jE (f x) (f z))) by
        simp [commutator, map_sub]; module]
    linarith [norm_sub_le (f (Q jA x (Q jA y z)) - Q jE (f x) (Q jE (f y) (f z)))
      (f (Q jA y (Q jA x z)) - Q jE (f y) (Q jE (f x) (f z))),
      hN x y z, hN y x z]
  -- the right factor
  have hH : ‖f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)‖ ≤
      7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    have h := hUE (f z) (f (jA x y) - jE (f x) (f y))
    rw [f.norm_map] at h
    rw [show f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z) =
      (f (Q jA z (jA x y)) - Q jE (f z) (f (jA x y))) +
      Q jE (f z) (f (jA x y) - jE (f x) (f y)) by simp only [rightFactor, Q_sub]; module]
    linarith [norm_add_le (f (Q jA z (jA x y)) - Q jE (f z) (f (jA x y)))
      (Q jE (f z) (f (jA x y) - jE (f x) (f y))), hQ z (jA x y),
      mul_le_mul_of_nonneg_left (hA x y) (by positivity : 0 ≤ 6 * μ * ‖z‖ ^ 2),
      mul_le_mul_of_nonneg_left (hdef x y) (sq_nonneg ‖z‖)]
  have hnH : ‖f (rightFactor jA x y z)‖ ≤ ‖z‖ ^ 2 * ‖x‖ * ‖y‖ := by
    rw [f.norm_map, rightFactor]
    linarith [hUA z (jA x y), mul_le_mul_of_nonneg_left (hA x y) (sq_nonneg ‖z‖)]
  have hnF : ‖commutator jE (f x) (f y) (f z)‖ ≤ 2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖ := by
    have h1 := hUE (f x) (Q jE (f y) (f z))
    have h2 := hUE (f y) (Q jE (f x) (f z))
    have h3 := hUE (f y) (f z)
    have h4 := hUE (f x) (f z)
    simp [f.norm_map] at h1 h2 h3 h4
    rw [commutator]
    linarith [norm_sub_le (Q jE (f x) (Q jE (f y) (f z))) (Q jE (f y) (Q jE (f x) (f z))),
      mul_le_mul_of_nonneg_left h3 (sq_nonneg ‖x‖), mul_le_mul_of_nonneg_left h4 (sq_nonneg ‖y‖)]
  have heq : response jA x y z - response jE (f x) (f y) (f z) =
      Inner.inner ℝ (f (commutator jA x y z) - commutator jE (f x) (f y) (f z))
        (f (rightFactor jA x y z)) +
      Inner.inner ℝ (commutator jE (f x) (f y) (f z))
        (f (rightFactor jA x y z) - rightFactor jE (f x) (f y) (f z)) := by
    change Inner.inner ℝ (commutator jA x y z) (rightFactor jA x y z) -
      Inner.inner ℝ (commutator jE (f x) (f y) (f z)) (rightFactor jE (f x) (f y) (f z)) = _
    rw [← f.inner_map_map, _root_.inner_sub_left, _root_.inner_sub_right]
    ring
  rw [heq]
  refine (abs_add_le _ _).trans ((add_le_add (abs_real_inner_le_norm _ _)
    (abs_real_inner_le_norm _ _)).trans ?_)
  calc
    _ ≤ (24 * μ * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (‖z‖ ^ 2 * ‖x‖ * ‖y‖) +
        (2 * ‖x‖ ^ 2 * ‖y‖ ^ 2 * ‖z‖) * (7 * μ * ‖z‖ ^ 2 * ‖x‖ * ‖y‖) := by gcongr
    _ = 38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 := by ring
    _ ≤ 38 * μ * R ^ 3 * R ^ 3 * R ^ 3 := by gcongr
    _ = _ := by ring

/-- Compatible cyclic-trace specialization. Nullness is produced by the existing
explicit associative representation theorem, rather than assumed as a field.
Generic norm hypotheses remain visible until concrete native/target producers apply. -/
theorem response_bound_of_compatible_trace
    {M : Type*} [Ring M] [Algebra ℝ M]
    (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
    (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
    (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
    (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
    (ρ : E →ₗ[ℝ] M) (τ : M →ₗ[ℝ] ℝ)
    (hj : ∀ a b, ρ (jE a b) = symmProd (ρ a) (ρ b))
    (hB : ∀ a b, Inner.inner ℝ a b = τ (ρ a * ρ b))
    (hcyclic : ∀ a b : M, τ (a * b) = τ (b * a))
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)
    (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z| ≤ 38 * μ * R ^ 9 := by
  have hnull : response jE (f x) (f y) (f z) = 0 :=
    phiWith_eq_zero_of_compatible_trace (fun a b => jE a b) (Inner.inner ℝ) ρ τ hj hB hcyclic
      (f x) (f y) (f z)
  simpa [hnull, sub_zero] using
    response_discrepancy_radius jA jE f hA hE hUA hUE μ hμ hdef R hR x y z hx hy hz

end Glennie.Compact.MultiplicationDefectR01
