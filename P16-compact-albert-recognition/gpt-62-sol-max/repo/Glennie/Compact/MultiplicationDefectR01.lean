/- Explicit generic norm hypotheses, with no assumed Phi-null field. -/
module
public import Glennie.Compact.CyclicTraceNullR01
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.GRewrite
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

def Q (j : Product A) (a : A) : A →ₗ[ℝ] A :=
  (2 : ℝ) • (j a).comp (j a) - j (j a a)

@[simp] theorem Q_apply (j : Product A) (a b : A) :
    Q j a b = (2 : ℝ) • j a (j a b) - j (j a a) b := rfl

def commutator (j : Product A) (x y z : A) : A :=
  Q j x (Q j y z) - Q j y (Q j x z)

def rightFactor (j : Product A) (x y z : A) : A := Q j z (j x y)

def response (j : Product A) (x y z : A) : ℝ :=
  phiWith (fun a b => j a b) (Inner.inner ℝ) x y z

/-- Bilinearity and Cauchy–Schwarz bound the change in both pairing arguments. -/
theorem pairing_error (a b c d : E) :
    |Inner.inner ℝ a b - Inner.inner ℝ c d| ≤ ‖a - c‖ * ‖b‖ + ‖c‖ * ‖b - d‖ := by
  rw [show Inner.inner ℝ a b - Inner.inner ℝ c d =
    Inner.inner ℝ (a-c) b + Inner.inner ℝ c (b-d) by simp [_root_.inner_sub_left, _root_.inner_sub_right]]
  grw [abs_add_le, abs_real_inner_le_norm, abs_real_inner_le_norm]


variable (jA : Product A) (jE : Product E) (f : A →ₗᵢ[ℝ] E)
variable (hA : ∀ a b, ‖jA a b‖ ≤ ‖a‖ * ‖b‖)
  (hE : ∀ a b, ‖jE a b‖ ≤ ‖a‖ * ‖b‖)
  (hUA : ∀ a b, ‖Q jA a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
  (hUE : ∀ a b, ‖Q jE a b‖ ≤ ‖a‖ ^ 2 * ‖b‖)
  (μ : ℝ) (hμ : 0 ≤ μ)
  (hdef : ∀ a b, ‖f (jA a b) - jE (f a) (f b)‖ ≤ μ * ‖a‖ * ‖b‖)

/-- Norm and transport-error bounds for the same word in the two products. -/
private def Bound (x : A) (y : E) (r d : ℝ) : Prop :=
  ‖x‖ ≤ r ∧ ‖y‖ ≤ r ∧ ‖f x-y‖ ≤ d

private theorem exactBound (x : A) : Bound f x (f x) ‖x‖ 0 := by
  simp [Bound]

private theorem subBound {x y : A} {x' y' : E} {r s d e : ℝ}
    (hx : Bound f x x' r d) (hy : Bound f y y' s e) :
    Bound f (x-y) (x'-y') (r+s) (d+e) := by
  refine ⟨by grw [norm_sub_le, hx.1, hy.1], by grw [norm_sub_le, hx.2.1, hy.2.1], ?_⟩
  rw [map_sub, show f x-f y-(x'-y') = (f x-x')-(f y-y') by abel]
  grw [norm_sub_le, hx.2.2, hy.2.2]


include hA hE hμ hdef
private theorem productBound {x y : A} {x' y' : E} {r s d e : ℝ}
    (hx : Bound f x x' r d) (hy : Bound f y y' s e) :
    Bound f (jA x y) (jE x' y') (r*s) (μ*r*s+d*s+r*e) := by
  rcases hx with ⟨hx, hx', hd⟩
  rcases hy with ⟨hy, hy', he⟩
  have hr := (norm_nonneg _).trans hx
  have hs := (norm_nonneg _).trans hy
  refine ⟨by grw [hA, hx, hy], by grw [hE, hx', hy'], ?_⟩
  have h : f (jA x y)-jE x' y' = (f (jA x y)-jE (f x) (f y)) +
      jE (f x-x') (f y) + jE x' (f y-y') := by
    simp only [map_sub, LinearMap.sub_apply]; abel
  rw [h]
  grw [norm_add_le, norm_add_le, hdef, hE, hE, f.norm_map, hx, hy, hx', hd, he]


private theorem quadratic_error (x y : A) :
    ‖f (Q jA x y)-Q jE (f x) (f y)‖ ≤ 6*μ*‖x‖^2*‖y‖ := by
  let p := @productBound _ _ _ _ _ _ jA jE f hA hE μ hμ hdef
  have ⟨_,_,h₁⟩ := p (exactBound f x) (p (exactBound f x) (exactBound f y))
  have ⟨_,_,h₂⟩ := p (p (exactBound f x) (exactBound f x)) (exactBound f y)
  simp only [mul_zero, zero_mul, add_zero] at h₁ h₂
  simp only [Q_apply, map_sub, map_smul]
  rw [show ∀ a b c d : E, (2:ℝ) • a-b-((2:ℝ) • c-d) = (2:ℝ) • (a-c)-(b-d) by
    intros; module]
  grw [norm_sub_le, norm_smul, Real.norm_ofNat, h₁, h₂]
  ring_nf
  rfl


include hUA hUE
private theorem quadBound (x : A) {y : A} {y' : E} {r d : ℝ} (h : Bound f y y' r d) :
    Bound f (Q jA x y) (Q jE (f x) y') (‖x‖^2*r) (‖x‖^2*(6*μ*r+d)) := by
  rcases h with ⟨hr,hr',hd⟩
  refine ⟨by grw [hUA, hr], by grw [hUE, f.norm_map, hr'], ?_⟩
  calc
    _ ≤ ‖f (Q jA x y)-Q jE (f x) (f y)‖ + ‖Q jE (f x) (f y-y')‖ := by
      rw [map_sub]
      exact norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ 6*μ*‖x‖^2*r + ‖x‖^2*d := by
      grw [quadratic_error jA jE f hA hE μ hμ hdef, hUE, f.norm_map, hr, hd]
    _ = _ := by ring


/-- Radius-ball form, with radius power nine and no smallness restriction on μ. -/
theorem response_discrepancy_radius (R : ℝ) (hR : 0 ≤ R) (x y z : A)
    (hx : ‖x‖ ≤ R) (hy : ‖y‖ ≤ R) (hz : ‖z‖ ≤ R) :
    |response jA x y z - response jE (f x) (f y) (f z)| ≤ 38 * μ * R ^ 9 := by
  let u x {y y' r d} (h : Bound f y y' r d) := quadBound jA jE f hA hE hUA hUE μ hμ hdef x h
  have hF := subBound f (u x (u y (exactBound f z))) (u y (u x (exactBound f z)))
  have hH := u z (productBound jA jE f hA hE μ hμ hdef (exactBound f x) (exactBound f y))
  change |Inner.inner ℝ (commutator jA x y z) (rightFactor jA x y z) -
    Inner.inner ℝ (commutator jE (f x) (f y) (f z)) (rightFactor jE (f x) (f y) (f z))| ≤ _
  rw [← f.inner_map_map (commutator jA x y z) (rightFactor jA x y z)]
  grw [pairing_error, f.norm_map]
  simp only [commutator, rightFactor]
  grw [hF.2.2, hH.1, hF.2.1, hH.2.2]
  calc
    _ = 38 * μ * ‖x‖ ^ 3 * ‖y‖ ^ 3 * ‖z‖ ^ 3 := by ring
    _ ≤ 38 * μ * R ^ 3 * R ^ 3 * R ^ 3 := by gcongr
    _ = _ := by ring


end
end Glennie.Compact.MultiplicationDefectR01
