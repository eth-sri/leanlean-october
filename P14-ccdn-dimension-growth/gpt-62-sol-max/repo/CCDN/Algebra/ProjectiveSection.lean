/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Hilbert.HomogeneousHilbert
public import Mathlib.LinearAlgebra.Projectivization.Basic
import CCDN.Height.ProjectivePointSeparation
import CCDN.Height.ProjectiveZeroLocus
import CCDN.Hilbert.FilteredIntersection

/-! Proper homogeneous sections of projective curves. The degree is the
slope of the graded Hilbert function. Homogeneous interpolation and
injective multiplication in the coordinate domain prove the section bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
variable {K : Type*} [Field K]

instance homogeneousCoordinateSpace_finite {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) (M : ℕ) :
    Module.Finite K (homogeneousCoordinateSpace I M) := by
  exact Module.Finite.of_fg
    ((homogeneousSubmodule_fg _ _ _).map (Ideal.Quotient.mkₐ K I).toLinearMap)

/-- The graded Hilbert function of `I`: the dimension of the degree-`M` part of the coordinate
ring `MvPolynomial (Fin (n + 1)) K ⧸ I`, that is, of the image of the homogeneous polynomials
of degree `M`. -/
def projectiveHilbertFunction {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (M : ℕ) : ℕ := Module.finrank K (homogeneousCoordinateSpace I M)

/-- The ideal `I` has projective curve degree `d`: the graded Hilbert function of
`MvPolynomial (Fin (n + 1)) K ⧸ I` eventually equals `d * M + c` for some constant `c`. For a
homogeneous prime ideal of a projective curve, `d` is the usual degree. -/
def HasProjectiveCurveDegree {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (d : ℕ) : Prop :=
  ∃ N : ℕ, ∃ c : ℤ, ∀ M : ℕ, N ≤ M →
    (projectiveHilbertFunction I M : ℤ) = (d : ℤ) * M + c

/-- A projective point belongs to the zero locus when every representative
annihilates the ideal. For homogeneous ideals this is the usual projective zero locus. -/
def projectiveIdealZeroLocus {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) K)) :
    Set (Projectivization K (Fin (n + 1) → K)) :=
  {x | ∀ (v : Fin (n + 1) → K) (hv : v ≠ 0),
    Projectivization.mk K v hv = x → v ∈ idealZeroLocus I}

/-- The chosen representative of a point of the projective zero locus of `I` lies in the affine
zero locus of `I`. -/
lemma projectiveIdealZeroLocus_rep {n : ℕ}
    {I : Ideal (MvPolynomial (Fin (n + 1)) K)} {x : Projectivization K (Fin (n + 1) → K)}
    (hx : x ∈ projectiveIdealZeroLocus I) :
    x.rep ∈ idealZeroLocus I :=
  hx x.rep x.rep_nonzero x.mk_rep

private lemma homogeneousCoordinateSpace_mul_mem {n M m : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    {f : MvPolynomial (Fin (n + 1)) K} (hf : f.IsHomogeneous m)
    {a : MvPolynomial (Fin (n + 1)) K ⧸ I}
    (ha : a ∈ homogeneousCoordinateSpace I M) :
    (Ideal.Quotient.mk I) f * a ∈ homogeneousCoordinateSpace I (m + M) := by
  obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp ha
  exact Submodule.mem_map.mpr ⟨f * g, hf.mul hg, by simp⟩

/-- Distinct points on a proper homogeneous section force a drop in the graded
Hilbert function at least as large as their number. -/
private theorem projective_section_hilbert_drop {n m M : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous m) (hfI : f ∉ I)
    (z : ι → Projectivization K (Fin (n + 1) → K)) (hz : Function.Injective z)
    (hzI : ∀ i, z i ∈ projectiveIdealZeroLocus I)
    (hzf : ∀ i, eval (z i).rep f = 0) (hM : Fintype.card ι - 1 ≤ m + M) :
    Fintype.card ι + projectiveHilbertFunction I M ≤ projectiveHilbertFunction I (m + M) := by
  classical
  let A := MvPolynomial (Fin (n + 1)) K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let ψ := AlgHom.pi fun i =>
    Ideal.Quotient.liftₐ I (aeval (z i).rep) (fun g hg => projectiveIdealZeroLocus_rep (hzI i) g hg)
  have hψ (i : ι) (g : MvPolynomial (Fin (n + 1)) K) : ψ (q g) i = eval (z i).rep g := rfl
  let V := homogeneousCoordinateSpace I (m + M)
  let W := homogeneousCoordinateSpace I M
  have h := finrank_map_add_le_of_mul_mem ψ V W (Ideal.Quotient.eq_zero_iff_mem.not.mpr hfI)
    (funext hzf) (fun _ hw => homogeneousCoordinateSpace_mul_mem I hf hw)
  obtain ⟨g, hhom, heval⟩ := exists_projective_point_separators_degree z hz hM
  have htop : V.map ψ.toLinearMap = ⊤ := by
    refine (Submodule.eq_top_iff_forall_basis_mem (Pi.basisFun K ι)).mpr fun i => ?_
    refine Submodule.mem_map.mpr ⟨q (g i), Submodule.mem_map.mpr ⟨g i, hhom i, rfl⟩, ?_⟩
    ext j
    simp [hψ, heval, Pi.single_apply]
  rwa [htop, finrank_top, Module.finrank_pi] at h

/-- A proper section of degree `m` meets a degree-`d` projective prime curve
in at most `dm` distinct points over the base field. -/
theorem projective_section_card_le_degree {n d m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hdegree : HasProjectiveCurveDegree I d)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous m) (hfI : f ∉ I)
    (z : ι → Projectivization K (Fin (n + 1) → K)) (hz : Function.Injective z)
    (hzI : ∀ i, z i ∈ projectiveIdealZeroLocus I)
    (hzf : ∀ i, eval (z i).rep f = 0) :
    Fintype.card ι ≤ d * m := by
  obtain ⟨N, c, hN⟩ := hdegree
  let M := max N (Fintype.card ι)
  have hlow := projective_section_hilbert_drop I f hf hfI z hz hzI hzf
    (show Fintype.card ι - 1 ≤ m + M by omega)
  
  
  grind

end
end CCDN
