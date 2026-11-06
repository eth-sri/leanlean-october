/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-! Homogeneous interpolation on distinct projective points. The separating
polynomials have one common degree, so their classes belong to a single
graded coordinate space. -/

namespace CCDN
section
open MvPolynomial
variable {K : Type*} [Field K]

section
variable {n : ℕ} {x y : Projectivization K (Fin (n + 1) → K)} (hxy : x ≠ y)
include hxy

lemma exists_projective_separating_minor
    :
    ∃ a b, y.rep b * x.rep a - y.rep a * x.rep b ≠ 0 := by
  by_contra! h
  obtain ⟨b, hb⟩ := Function.ne_iff.mp y.rep_nonzero
  change y.rep b ≠ 0 at hb
  apply hxy
  have he : x.rep = (x.rep b / y.rep b) • y.rep := by
    funext a
    change x.rep a = (x.rep b / y.rep b) * y.rep a
    grind
  calc
    x = Projectivization.mk K x.rep x.rep_nonzero := x.mk_rep.symm
    _ = Projectivization.mk K y.rep y.rep_nonzero := by
      rw [Projectivization.mk_eq_mk_iff']
      grind
    _ = y := y.mk_rep

lemma exists_projective_linear_separator
    :
    ∃ f : MvPolynomial (Fin (n + 1)) K,
      f.IsHomogeneous 1 ∧ eval x.rep f = 1 ∧ eval y.rep f = 0 := by
  obtain ⟨a, b, hab⟩ := exists_projective_separating_minor hxy
  let D := y.rep b * x.rep a - y.rep a * x.rep b
  refine ⟨C D⁻¹ * (C (y.rep b) * X a - C (y.rep a) * X b), ?_, ?_, ?_⟩
  · exact ((isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)).C_mul _
  · aesop
  · simp only [eval_mul, eval_C, eval_sub, eval_X]
    ring

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Separators can be raised to any larger common degree without changing
their values on the selected representatives. -/
theorem exists_projective_point_separators_degree {n M : ℕ}
    (z : ι → Projectivization K (Fin (n + 1) → K))
    (hz : Function.Injective z) (hM : Fintype.card ι - 1 ≤ M) :
    ∃ h : ι → MvPolynomial (Fin (n + 1)) K,
      (∀ j, (h j).IsHomogeneous M) ∧
      ∀ i j, eval (z i).rep (h j) = if i = j then 1 else 0 := by
  obtain ⟨h, hhom, heval⟩ : ∃ h : ι → MvPolynomial (Fin (n + 1)) K,
      (∀ j, (h j).IsHomogeneous (Fintype.card ι - 1)) ∧
      ∀ i j, eval (z i).rep (h j) = if i = j then 1 else 0 := by
    have hex (i : ι) : ∃ f : MvPolynomial (Fin (n + 1)) K,
        f.IsHomogeneous (Fintype.card ι - 1) ∧ eval (z i).rep f = 1 ∧
        ∀ j, j ≠ i → eval (z j).rep f = 0 := by
      have hp (j : {j : ι // j ≠ i}) := exists_projective_linear_separator
        (show z i ≠ z j.val from fun he => j.property (hz he).symm)
      choose f hf hon hoff using hp
      refine ⟨∏ j, f j, ?_, ?_, ?_⟩
      · have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
          simp
        simpa
          using IsHomogeneous.prod Finset.univ f (fun _ => 1) (fun j _ => hf j)
      · simp_all
      · intro j hji
        rw [eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
          (hoff ⟨j, hji⟩)
    choose h hhom hon hoff using hex
    refine ⟨h, hhom, ?_⟩
    intro i j
    by_cases hij : i = j
    · grind
    · grind
  have hcoord (j : ι) : ∃ k, (z j).rep k ≠ 0 :=
    Function.ne_iff.mp (z j).rep_nonzero
  choose k hk using hcoord
  let L (j : ι) := C ((z j).rep (k j))⁻¹ * X (k j)
  have hL (j : ι) : (L j).IsHomogeneous 1 := isHomogeneous_C_mul_X _ _
  refine ⟨fun j => h j * L j ^ (M - (Fintype.card ι - 1)), ?_, ?_⟩
  · intro j
    convert (hhom j).mul ((hL j).pow (M - (Fintype.card ι - 1))) using 1
    grind
  · aesop

