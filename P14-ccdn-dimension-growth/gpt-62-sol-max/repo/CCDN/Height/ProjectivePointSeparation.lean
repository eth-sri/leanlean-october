/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization

/-! Homogeneous interpolation on pairwise nonproportional vectors. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K σ : Type*} [Field K]

/-- A linear form separating two nonproportional vectors. -/
lemma exists_homogeneous_linear_separator {x y : σ → K} (hy : y ≠ 0)
    (hxy : ∀ c : K, c • y ≠ x) :
    ∃ f : MvPolynomial σ K, f.IsHomogeneous 1 ∧ eval x f = 1 ∧ eval y f = 0 := by
  have hminor : ∃ a b, y b * x a - y a * x b ≠ 0 := by
    by_contra! h
    obtain ⟨b, hb⟩ := Function.ne_iff.mp hy
    change y b ≠ 0 at hb
    apply hxy (x b / y b)
    ext a
    
    change (x b / y b) * y a = x a
    grind
  obtain ⟨a, b, hab⟩ := hminor
  let D := y b * x a - y a * x b
  refine ⟨C D⁻¹ * (C (y b) * X a - C (y a) * X b),
    ((isHomogeneous_C_mul_X _ _).sub (isHomogeneous_C_mul_X _ _)).C_mul _, ?_, ?_⟩
  · simpa [D] using inv_mul_cancel₀ hab
  · simp [mul_comm (y b) (y a)]

/-- Interpolation by homogeneous polynomials of any degree at least `card ι - 1`. -/
theorem exists_homogeneous_point_separators {M : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → σ → K) (hn : ∀ i, z i ≠ 0)
    (hz : ∀ ⦃i j⦄, i ≠ j → ∀ c : K, c • z j ≠ z i) (hM : Fintype.card ι - 1 ≤ M) :
    ∃ h : ι → MvPolynomial σ K, (∀ j, (h j).IsHomogeneous M) ∧
      ∀ i j, eval (z i) (h j) = if i = j then 1 else 0 := by
  classical
  have sep (i : ι) : ∃ f : MvPolynomial σ K, f.IsHomogeneous M ∧
      ∀ j, eval (z j) f = if j = i then 1 else 0 := by
    choose f hf hon hoff using fun j : {j : ι // j ≠ i} =>
      exists_homogeneous_linear_separator (hn j) (hz (Ne.symm j.property))
    obtain ⟨k, hk⟩ := Function.ne_iff.mp (hn i)
    change z i k ≠ 0 at hk
    let L := C (z i k)⁻¹ * X k
    refine ⟨(∏ j, f j) * L ^ (M - (Fintype.card ι - 1)), ?_, ?_⟩
    · have hp : (∏ j, f j).IsHomogeneous (Fintype.card ι - 1) := by
        simpa using IsHomogeneous.prod Finset.univ f (fun _ => 1) (fun j _ => hf j)
      simpa [Nat.add_sub_of_le hM] using hp.mul
        ((isHomogeneous_C_mul_X (z i k)⁻¹ k).pow (M - (Fintype.card ι - 1)))
    · intro j
      by_cases hji : j = i
      · subst j
        simp [L, hon, hk]
      · have he : (∏ l, eval (z j) (f l)) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ (⟨j, hji⟩ : {j : ι // j ≠ i}))
          (hoff ⟨j, hji⟩)
        simp [hji, he]
  choose h hh he using sep
  exact ⟨h, hh, fun i j => he j i⟩

/-- Homogeneous interpolation on chosen representatives of distinct projective points. -/
theorem exists_projective_point_separators_degree {n M : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → Projectivization K (Fin (n + 1) → K))
    (hz : Function.Injective z) (hM : Fintype.card ι - 1 ≤ M) :
    ∃ h : ι → MvPolynomial (Fin (n + 1)) K, (∀ j, (h j).IsHomogeneous M) ∧
      ∀ i j, eval (z i).rep (h j) = if i = j then 1 else 0 := by
  refine exists_homogeneous_point_separators (fun i => (z i).rep) (fun i => (z i).rep_nonzero)
    (fun {i j} hij c hc => hij (hz ?_)) hM
  rw [← (z i).mk_rep, ← (z j).mk_rep, Projectivization.mk_eq_mk_iff']
  exact ⟨c, hc⟩

end
end CCDN
