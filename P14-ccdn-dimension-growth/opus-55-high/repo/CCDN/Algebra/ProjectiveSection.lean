/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import CCDN.Algebra.PolynomialPredicates
import CCDN.Hilbert.HomogeneousHilbert
import Mathlib.LinearAlgebra.Projectivization.Basic
import CCDN.Height.ProjectivePointSeparation
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Hilbert.FilteredIntersection

/-! Proper homogeneous sections of projective curves. The degree is the
slope of the graded Hilbert function. Homogeneous interpolation and
injective multiplication in the coordinate domain prove the section bound. -/

namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

instance homogeneousCoordinateSpace_finite {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (M : ℕ) :
    Module.Finite K (homogeneousCoordinateSpace I M) := by
  exact Module.Finite.of_fg
    ((homogeneousSubmodule_fg _ _ _).map (Ideal.Quotient.mkₐ K I).toLinearMap)

section
variable {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))

/-- The graded Hilbert function of `I`: the dimension of the degree-`M` part of the coordinate
ring `MvPolynomial (Fin (n + 1)) K ⧸ I`, that is, of the image of the homogeneous polynomials
of degree `M`. -/
def projectiveHilbertFunction
    (M : ℕ) : ℕ := Module.finrank K (homogeneousCoordinateSpace I M)

/-- The ideal `I` has projective curve degree `d`: the graded Hilbert function of
`MvPolynomial (Fin (n + 1)) K ⧸ I` eventually equals `d * M + c` for some constant `c`. For a
homogeneous prime ideal of a projective curve, `d` is the usual degree. -/
def HasProjectiveCurveDegree
    (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (projectiveHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- A projective point belongs to the zero locus when every representative
annihilates the ideal. For homogeneous ideals this is the usual projective zero locus. -/
def projectiveIdealZeroLocus :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  {x | ∀ (v : Fin (n + 1) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = x → v ∈ idealZeroLocus I}

end

/-- The chosen representative of a point of the projective zero locus of `I` lies in the affine
zero locus of `I`. -/
lemma projectiveIdealZeroLocus_rep {n : ℕ}
    {I : Ideal (MvPolynomial (Fin (n + 1)) K)} {x : Projectivization K (Fin (n + 1) → K)}
    (hx : x ∈ projectiveIdealZeroLocus I) :
    x.rep ∈ idealZeroLocus I :=
  hx x.rep x.rep_nonzero x.mk_rep

lemma homogeneousCoordinateSpace_mul_mem {n M m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous m)
    {a : MvPolynomial (Fin (n + 1)) K ⧸ I}
    (ha : a ∈ homogeneousCoordinateSpace I M) :
    (Ideal.Quotient.mk I) f * a ∈ homogeneousCoordinateSpace I (m + M) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp ha
  exact Submodule.mem_map.mpr ⟨f * g, hf.mul hg, by simp⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A proper section of degree `m` meets a degree-`d` projective prime curve
in at most `dm` distinct points over the base field. -/
theorem projective_section_card_le_degree {n d m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hdegree : HasProjectiveCurveDegree I d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous m) (hfI : f ∉ I)
    (z : ι → Projectivization K (Fin (n + 1) → K)) (hz : Function.Injective z)
    (hzI : ∀ i, z i ∈ projectiveIdealZeroLocus I)
    (hzf : ∀ i, eval (z i).rep f = 0) :
    Fintype.card ι ≤ d * m := by
  obtain ⟨N, c, hN⟩ := hdegree
  let M := max N (Fintype.card ι)
  have hlow : Fintype.card ι + projectiveHilbertFunction I M ≤ projectiveHilbertFunction I (m + M) := by
    let A := MvPolynomial (Fin (n + 1)) K ⧸ I
    let q := Ideal.Quotient.mkₐ K I
    let ψ : ι → A →ₐ[K] K := fun i =>
      Ideal.Quotient.liftₐ I (aeval (z i).rep) (by
        intro g hg
        simpa using projectiveIdealZeroLocus_rep (hzI i) g hg)
    have hψ (i : ι) (g : MvPolynomial (Fin (n + 1)) K) :
        ψ i (q g) = eval (z i).rep g := by
      rfl
    let φ : A →ₗ[K] (ι → K) := LinearMap.pi fun i => (ψ i).toLinearMap
    let V := homogeneousCoordinateSpace I (m + M)
    let W := homogeneousCoordinateSpace I M
    let U := W.map (LinearMap.mulLeft K (q f))
    have hf0 : q f ≠ 0 :=
      fun he => hfI (Ideal.Quotient.eq_zero_iff_mem.mp he)
    have hUdim :=
      (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
        (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
    obtain ⟨h, hhom, heval⟩ := exists_projective_point_separators_degree z hz (show Fintype.card ι - 1 ≤ m + M by grind)
    have htop : V.map φ = ⊤ := by
      apply top_unique
      intro w _
      refine ⟨∑ j, w j • q (h j), ?_, ?_⟩
      · apply Submodule.sum_mem
        intro j _
        apply Submodule.smul_mem
        exact Submodule.mem_map.mpr ⟨h j, hhom j, rfl⟩
      · aesop
    have h := finrank_map_add_kernel_subspace_le φ V U (by
      rintro a ha
      obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
      exact homogeneousCoordinateSpace_mul_mem I hf hb) (by
        rintro a ha
        aesop)
    rwa [htop, finrank_top, Module.finrank_pi, hUdim] at h
  have h0 := hN M (le_max_left _ _)
  have h1 := hN (m + M) (by grind)
  have hlowZ : (Fintype.card ι : ℤ) + projectiveHilbertFunction I M ≤
      projectiveHilbertFunction I (m + M) := mod_cast hlow
  rw [h0, h1] at hlowZ
  push_cast at hlowZ
  have hcard : (Fintype.card ι : ℤ) ≤ d * m := by linarith
  exact_mod_cast hcard

