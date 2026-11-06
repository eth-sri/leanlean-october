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
  classical
  obtain ⟨N, c, hN⟩ := hdegree
  let M := max N (Fintype.card ι)
  let A := MvPolynomial (Fin (n + 1)) K ⧸ I
  let q := Ideal.Quotient.mkₐ K I
  let ψ : ι → A →ₐ[K] K := fun i =>
    Ideal.Quotient.liftₐ I (aeval (z i).rep) fun g hg => by
      simpa only [aeval_eq_eval] using projectiveIdealZeroLocus_rep (hzI i) g hg
  have hψ (i : ι) (g : MvPolynomial (Fin (n + 1)) K) : ψ i (q g) = eval (z i).rep g := rfl
  let φ : A →ₗ[K] (ι → K) := LinearMap.pi fun i => (ψ i).toLinearMap
  let V := homogeneousCoordinateSpace I (m + M)
  let W := homogeneousCoordinateSpace I M
  let U := W.map (LinearMap.mulLeft K (q f))
  have hUV : U ≤ V := by
    rintro a ⟨b, ⟨g, hg, rfl⟩, rfl⟩
    exact Submodule.mem_map.mpr ⟨f * g, hf.mul hg, by simp [q]⟩
  have hUker : U ≤ φ.ker := by
    rintro a ⟨b, _, rfl⟩
    refine LinearMap.mem_ker.mpr (funext fun i => ?_)
    change ψ i (q f * b) = 0
    rw [map_mul, hψ, hzf, zero_mul]
  have hf0 : q f ≠ 0 := fun he => hfI (Ideal.Quotient.eq_zero_iff_mem.mp he)
  have hUdim : Module.finrank K U = projectiveHilbertFunction I M :=
    (Submodule.equivMapOfInjective (LinearMap.mulLeft K (q f))
      (fun a b h => mul_left_cancel₀ hf0 h) W).finrank_eq.symm
  obtain ⟨h, hhom, heval⟩ := exists_projective_point_separators_degree z hz
    (show Fintype.card ι - 1 ≤ m + M by dsimp [M]; omega)
  have htop : V.map φ = ⊤ := top_unique fun w _ =>
    Submodule.mem_map.mpr ⟨∑ j, w j • q (h j),
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ⟨h j, hhom j, rfl⟩,
      funext fun i => by change ψ i (∑ j, w j • q (h j)) = w i; simp [hψ, heval]⟩
  have hlow := finrank_map_add_kernel_subspace_le φ V U hUV hUker
  rw [htop, finrank_top, Module.finrank_pi, hUdim] at hlow
  have h0 := hN M (le_max_left _ _)
  have h1 := hN (m + M) (by dsimp [M]; omega)
  have hlowZ : (Fintype.card ι : ℤ) + projectiveHilbertFunction I M ≤
      projectiveHilbertFunction I (m + M) := mod_cast hlow
  rw [h0, h1] at hlowZ
  push_cast at hlowZ
  exact_mod_cast (by linarith : (Fintype.card ι : ℤ) ≤ (d : ℤ) * m)

end
end CCDN
