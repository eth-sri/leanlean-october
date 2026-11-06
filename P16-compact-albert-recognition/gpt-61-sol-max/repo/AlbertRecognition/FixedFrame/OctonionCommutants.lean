/- Native right-multiplication commutants in the compact quaternion-pair model.
All octonion products retain their displayed parentheses. -/
module
public import Glennie.Native.Triality
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Aesop

public import AlbertRecognition.FixedFrame.QuaternionFacts
public import Mathlib.LinearAlgebra.Prod

@[expose] public section

namespace AlbertRecognition.FixedFrame
noncomputable section

open Glennie
open scoped BigOperators
open scoped Quaternion

/-- The actual real coordinate basis of compact native octonions. -/
def octBasis : Fin 8 → Octonion :=
  ![octScalar 1, (qi, 0), (qj, 0), (qk, 0), (0, 1), (0, qi), (0, qj), (0, qk)]

theorem octBasis_conj_imag (t : Fin 8) (ht : t ≠ 0) :
    octConj (octBasis t) = -octBasis t := by
  fin_cases t <;> simp_all [octBasis, octConj, qi, qj, qk]

/-- Literal eight-coordinate reconstruction; no spanning hypothesis is assumed. -/
theorem oct_decompose (x : Octonion) :
    x = ∑ t : Fin 8, octDot (octBasis t) x • octBasis t := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [Fin.sum_univ_succ, octBasis, octDot_coordinates, octScalar, qi, qj, qk, smul_eq_mul]

theorem oct_linear_ext {M : Type*} [AddCommMonoid M] [Module ℝ M]
    (f g : Octonion →ₗ[ℝ] M)
    (h : ∀ t : Fin 8, f (octBasis t) = g (octBasis t)) : f = g := by
  apply LinearMap.ext
  intro x
  rw [oct_decompose x]
  simp only [map_sum, map_smul, h]

/-- Right multiplication, with the native nonassociative product. -/
def octRight (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul x a
  map_add' x y := octMul_add_left x y a
  map_smul' r x := by
    exact octMul_smul_left r x a

/-- Left multiplication, used only as a real-linear map. -/
def octLeft (a : Octonion) : Module.End ℝ Octonion where
  toFun x := octMul a x
  map_add' x y := octMul_add_right a x y
  map_smul' r x := by
    exact octMul_smul_right r a x

def octConjLinear : Module.End ℝ Octonion := octConjEquiv.toLinearMap

/-- The native left nucleus is the real line, via two quaternion-pair tests. -/
theorem oct_left_nucleus_scalar (c : Octonion)
    (hc : ∀ x a : Octonion, octMul c (octMul x a) = octMul (octMul c x) a) :
    ∃ b : ℝ, c = octScalar b := by
  have h1 := hc (qi, 0) (qj, 0)
  have h2 := hc (0, 1) (qi, 0)
  have h3 := hc (0, 1) (qj, 0)
  clear hc
  norm_num [octMul, qi, qj, qk, Prod.ext_iff, Quaternion.ext_iff] at h1 h2 h3
  refine ⟨c.1.re, ?_⟩
  ext <;> simp [octScalar] <;> linarith

/-- The reverse associator identity needed for the imaginary anticommutant. -/
theorem oct_reverse_identity_zero (d : Octonion)
    (hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a) :
    d = 0 := by
  have h1 := hd (qi, 0) (qj, 0)
  have h2 := hd (0, 1) (qi, 0)
  have h3 := hd (0, 1) (qj, 0)
  have h4 := hd (0, 1) (qk, 0)
  clear hd
  norm_num [octMul, qi, qj, qk, Prod.ext_iff, Quaternion.ext_iff] at h1 h2 h3 h4
  ext <;> simp <;> linarith

/-- Commutation with the literal eight right multiplications forces a scalar. -/
theorem oct_right_commutant_scalar (P : Module.End ℝ Octonion)
    (hP : ∀ t : Fin 8, ∀ x : Octonion,
      P (octMul x (octBasis t)) = octMul (P x) (octBasis t)) :
    ∃ b : ℝ, P = b • LinearMap.id := by
  have hall (x a : Octonion) : P (octMul x a) = octMul (P x) a := by
    have heq : P.comp (octLeft x) = octLeft (P x) :=
      oct_linear_ext _ _ (fun t => hP t x)
    exact LinearMap.congr_fun heq a
  let c := P (octScalar 1)
  have hx (x : Octonion) : P x = octMul c x := by
    simpa [c] using hall (octScalar 1) x
  have hn : ∀ x a : Octonion, octMul c (octMul x a) = octMul (octMul c x) a := by simp_all
  obtain ⟨b, hb⟩ := oct_left_nucleus_scalar c hn
  refine ⟨b, ?_⟩
  apply LinearMap.ext
  intro x
  simpa [hb] using hx x

/-- Anticommutation with seven imaginary right multiplications forces zero. -/
theorem oct_imaginary_right_anticommutant_zero (Q : Module.End ℝ Octonion)
    (hQ : ∀ t : Fin 8, t ≠ 0 → ∀ x : Octonion,
      Q (octMul x (octBasis t)) = -octMul (Q x) (octBasis t)) : Q = 0 := by
  have hall (x a : Octonion) : Q (octMul x a) = octMul (Q x) (octConj a) := by
    have heq : Q.comp (octLeft x) = (octLeft (Q x)).comp octConjLinear := by
      apply oct_linear_ext
      intro t
      by_cases ht : t = 0
      · subst t
        change Q (octMul x (octScalar 1)) = octMul (Q x) (octConj (octScalar 1))
        simp only [octConj_scalar, octMul_scalar_right, one_smul]
      · change Q (octMul x (octBasis t)) = octMul (Q x) (octConj (octBasis t))
        rw [octBasis_conj_imag t ht, hQ t ht x]
        exact (map_neg (octLeft (Q x)) (octBasis t)).symm
    exact LinearMap.congr_fun heq a
  let d := Q (octScalar 1)
  have hx (x : Octonion) : Q x = octMul d (octConj x) := by
    simpa [d] using hall (octScalar 1) x
  have hd : ∀ a x : Octonion, octMul d (octMul a x) = octMul (octMul d x) a := by
    intro a x
    have h := hall (octConj x) (octConj a)
    rw [hx (octMul (octConj x) (octConj a)), hx (octConj x)] at h
    simpa only [octConj_mul, octConj_conj] using h
  have hd0         := oct_reverse_identity_zero d hd
  apply LinearMap.ext
  intro x
  change Q x = (0 : Octonion)
  rw [hx x, hd0, octMul_zero_left]

end
end AlbertRecognition.FixedFrame
