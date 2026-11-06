/- A univariate coefficient proof of reverse shear invariance.
This is a general polynomial lemma, not an assumed native Glennie identity. -/
module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section
namespace Glennie
section

theorem reverse_shear_of_cubic {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : E → E → ℝ)
    (hline : ∀ x z v, ∃ a b c d : ℝ, ∀ t : ℝ,
      F (x + t • z) v = a + b*t + c*t^2 + d*t^3)
    (hhom : ∀ x z (t : ℝ), F x (t • z) = t^3 * F x z)
    (hforward : ∀ x z (t : ℝ), F x (z + t • x) = F x z)
    (x z : E) (t : ℝ) : F (x + t • z) z = F x z := by
  obtain ⟨a, b, c, d, hp⟩ := hline x z z
  obtain ⟨a', b', c', d', hq⟩ := hline x z x
  have heq (r : ℝ) : r^3 * (a + b*r + c*r^2 + d*r^3) =
      -(a' + b'*r + c'*r^2 + d'*r^3) := by
    have h := hforward (x + r • z) x (-1)
    rw [show x + (-1 : ℝ) • (x + r • z) = (-r) • z by module,
      hhom, hp, hq] at h
    nlinarith only [h]
  have ha' : a' = 0 := by simpa using heq 0
  have h1 := heq 1
  have hm1 := heq (-1)
  have h2 := heq 2
  have hm2 := heq (-2)
  have h3 := heq 3
  have hm3 := heq (-3)
  norm_num [ha'] at h1 hm1 h2 hm2 h3 hm3
  -- Exact interpolation of the universally established degree-six identity.
  -- These evaluations are sufficient because the cubic line expansion is proved.
  have hb : b = 0 := by linarith
  have hc : c = 0 := by linarith
  have hd : d = 0 := by linarith
  have hconstant : F x z = a := by simpa using hp 0
  rw [hp t, hb, hc, hd]
  simpa using hconstant.symm

end
end Glennie
