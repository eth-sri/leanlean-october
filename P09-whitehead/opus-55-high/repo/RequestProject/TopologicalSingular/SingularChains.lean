/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import Mathlib
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.AlgebraicTopology.TopologicalSimplex
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import RequestProject.Tac
noncomputable section


/-! # Explicit integral singular chains of actual topological spaces

The generators are continuous maps from the standard topological simplex.
The simplicial identities give the chain relation through Mathlib's
alternating-face complex. No exactness or homotopy comparison is assumed.
-/

bwd

namespace FiniteChains.TopologicalSingular

open Set Topology CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

universe u v

abbrev Domain (n : ℕ) := stdSimplex ℝ (Fin (n + 1))

abbrev Simplex (X : Type u) [TopologicalSpace X] (n : ℕ) := C(Domain n, X)

abbrev Chain (X : Type u) [TopologicalSpace X] (n : ℕ) := Simplex X n →₀ ℤ

def simplices (X : Type u) [TopologicalSpace X] : SimplicialObject (Type u) where
  obj n := Simplex X n.unop.len
  map f := TypeCat.ofHom (fun σ => σ.comp ⟨stdSimplex.map f.unop, stdSimplex.continuous_map _⟩)
  map_id n := by
    aesop
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro σ
    ext z
    exact congrArg σ (stdSimplex.map_comp_apply g.unop f.unop z).symm

def freeZ : Type u ⥤ ModuleCat.{u} ℤ where
  obj A := ModuleCat.of ℤ (A →₀ ℤ)
  map f := ModuleCat.ofHom (Finsupp.lmapDomain ℤ ℤ f.hom)
  map_id A := by
    aesop
  map_comp f g := by
    aesop

def modules (X : Type u) [TopologicalSpace X] : SimplicialObject (ModuleCat.{u} ℤ) :=
  simplices X ⋙ freeZ

def complex (X : Type u) [TopologicalSpace X] :=
  AlternatingFaceMapComplex.obj (modules X)

variable {X : Type u} [TopologicalSpace X]

def face (i : Fin (n + 2)) (σ : Simplex X (n + 1)) : Simplex X n :=
  (simplices X).δ i σ

theorem face_apply i (σ : Simplex X (n + 1)) z :
    face i σ z = σ (stdSimplex.map (SimplexCategory.δ i) z) := rfl

def boundary n : Chain X (n + 1) →ₗ[ℤ] Chain X n :=
  (AlternatingFaceMapComplex.objD (modules X) n).hom

theorem boundary_eq_sum n :
    boundary (X := X) n = ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face i) := by
  simp [boundary, AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

theorem boundary_single n (σ : Simplex X (n + 1)) a :
    boundary n (Finsupp.single σ a) =
      ∑ i : Fin (n + 2), (-1) ^ (i : ℕ) • Finsupp.single (face i σ) a := by
  rw [boundary_eq_sum]
  simp

theorem boundary_squared n :
    (boundary (X := X) n).comp (boundary (n + 1)) = 0 := congrArg ModuleCat.Hom.hom (AlternatingFaceMapComplex.d_squared (modules X) n)

theorem boundary_boundary n (c : Chain X (n + 2)) : boundary n (boundary (n + 1) c) = 0 :=
  DFunLike.congr_fun (boundary_squared n) c

theorem complex_d n : (complex X).d (n + 1) n = ModuleCat.ofHom (boundary n) := AlternatingFaceMapComplex.obj_d_eq _ n

def augmentation : Chain X 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Simplex X 0 => (1 : ℤ))

@[simp] theorem augmentation_single (σ : Simplex X 0) a :
    augmentation (Finsupp.single σ a) = a := by
  simp [augmentation]

theorem augmentation_boundary (c : Chain X 1) : augmentation (boundary 0 c) = 0 := by
  have he : augmentation.comp (boundary (X := X) 0) = 0 := by
    apply Finsupp.lhom_ext
    intro σ a
    change augmentation (boundary 0 (Finsupp.single σ a)) = 0
    rw [boundary_single]
    rw [Fin.sum_univ_two]
    simp
  exact DFunLike.congr_fun he c

def zeroSimplexEquiv : Simplex X 0 ≃ X where
  toFun σ := σ (stdSimplex.vertex 0)
  invFun x := ContinuousMap.const _ x
  left_inv σ := by
    letI : Subsingleton (Domain 0) := inferInstanceAs (Subsingleton (stdSimplex ℝ (Fin 1)))
    ext z
    exact congrArg σ (Subsingleton.elim _ _)
  right_inv x := rfl
