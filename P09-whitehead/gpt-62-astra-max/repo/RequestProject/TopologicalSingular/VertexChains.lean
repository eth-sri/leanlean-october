module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChains
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! # Integral chains of ordered vertex lists

These auxiliary chains will be realized as affine singular simplices.
Repeated vertices are allowed. The cone and its boundary are explicit;
no acyclicity or subdivision identity is assumed.
-/

noncomputable section

namespace FiniteChains.VertexChains

open CategoryTheory AlgebraicTopology

universe u v
variable (V : Type u)

variable (n : ℕ)

abbrev Vertices := Fin (n + 1) → V
abbrev Chain := Vertices V n →₀ ℤ

def simplices : SimplicialObject (Type u) where
  obj n := Vertices V n.unop.len
  map f := TypeCat.ofHom (fun v => v ∘ f.unop.toOrderHom)

def modules := simplices V ⋙ TopologicalSingular.freeZ

variable {V : Type u} {W : Type v}

theorem linearMap_ext_basis {ι M : Type*} [AddCommGroup M] [Module ℤ M]
    {f g : (ι →₀ ℤ) →ₗ[ℤ] M} (h : ∀ v, f (Finsupp.single v 1) = g (Finsupp.single v 1)) : f = g := by
  aesop

def face {n : ℕ} (i : Fin _) (v : Vertices V (n + 1)) :=
  v ∘ i.succAbove

variable (n : ℕ)

def boundary : Chain V (n + 1) →ₗ[ℤ] Chain V n :=
  (AlternatingFaceMapComplex.objD (modules V) n).hom

theorem boundary_eq_sum :
    boundary (V := V) n = ∑ i : Fin _, (-1) ^ i.val • Finsupp.lmapDomain ℤ ℤ (face i) := by
  simp only [boundary, AlternatingFaceMapComplex.objD, ModuleCat.hom_sum, ModuleCat.hom_zsmul]
  rfl

theorem boundary_single (v : Vertices V _) (r : ℤ) :
    boundary n (Finsupp.single v r) =
      ∑ i : Fin _, (-1) ^ i.val • Finsupp.single (face i v) r := by
  rw [boundary_eq_sum]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]

theorem boundary_boundary (c : Chain V _) : boundary n (boundary (n + 1) c) = 0 := DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (AlternatingFaceMapComplex.d_squared (modules V) n)) c

def augmentation : Chain V 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ : Vertices V 0 => 1)

@[simp] theorem augmentation_single (v : Vertices V 0) (r : ℤ) :
    augmentation (Finsupp.single v r) = r := by simp [augmentation]

theorem augmentation_boundary (c : Chain V 1) : augmentation (boundary 0 c) = 0 := by
  have he : augmentation.comp (boundary (V := V) 0) = 0 := by
    apply Finsupp.lhom_ext
    intro v r
    change augmentation _ = 0
    rw [boundary_single, Fin.sum_univ_two]
    simp
  exact DFunLike.congr_fun he c

variable (f : V → W) (n : ℕ)

def map : Chain V n →ₗ[ℤ] Chain W n :=
  Finsupp.lmapDomain ℤ ℤ (fun v => f ∘ v)

@[simp] theorem map_single (v : Vertices V n) (r : ℤ) :
    map f n (Finsupp.single v r) = Finsupp.single (f ∘ v) r := Finsupp.mapDomain_single

theorem map_boundary (c : Chain V _) :
    map f n (boundary n c) = boundary n (map f (n + 1) c) := by
  have he : (map f n).comp (boundary n) = (boundary n).comp (map f _) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, boundary_single, map_single, map_sum, map_zsmul]
    rfl
  exact DFunLike.congr_fun he c

variable (p : V)

variable (n : ℕ)

def cone : Chain V n →ₗ[ℤ] Chain V (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun v : Vertices V n => Fin.cons p v)

@[simp] theorem cone_single (v : Vertices V n) (r : ℤ) :
    cone p n (Finsupp.single v r) = Finsupp.single (Fin.cons p v) r := Finsupp.mapDomain_single

variable {n : ℕ}

theorem face_cone_zero (v : Vertices V n) : face 0 (Fin.cons p v) = v := rfl

theorem face_cone_succ (v : Vertices V _) (i : Fin (n + 2)) :
    face i.succ (Fin.cons p v) = Fin.cons p (face i v) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · rfl
  · simp [face]

variable (v : Vertices V 0)

theorem face_cone_one :
    face 1 (Fin.cons p v) = fun _ => p := by
  funext j
  have hj : j = 0 := by apply Fin.ext; omega
  subst j
  rfl

theorem boundary_cone_zero_single (r : ℤ) :
    boundary 0 (cone p 0 (Finsupp.single v r)) =
      Finsupp.single v r - r • Finsupp.single (fun _ : Fin 1 => p) 1 := by
  rw [cone_single, boundary_single, Fin.sum_univ_two, face_cone_zero, face_cone_one]
  simp [sub_eq_add_neg]

theorem boundary_cone_zero (c : Chain V 0) :
    boundary 0 (cone p 0 c) = c - augmentation c • Finsupp.single (fun _ : Fin 1 => p) 1 := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add v r c _ _ ih =>
    rw [map_add, map_add, boundary_cone_zero_single, ih, map_add, augmentation_single, add_smul]
    abel

variable (n : ℕ)

theorem boundary_cone_single (v : Vertices V _) (r : ℤ) :
    boundary _ (cone p (n + 1) (Finsupp.single v r)) =
      Finsupp.single v r - cone p n (boundary n (Finsupp.single v r)) := by
  rw [cone_single, boundary_single, Fin.sum_univ_succ, face_cone_zero, boundary_single]
  simp only [Fin.val_zero, pow_zero, one_smul, face_cone_succ, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib, map_sum, map_zsmul, cone_single, sub_eq_add_neg]

theorem boundary_cone (c : Chain V _) :
    boundary _ (cone p (n + 1) c) = c - cone p n (boundary n c) := by
  have he : (boundary _).comp (cone p _) =
      LinearMap.id - (cone p n).comp (boundary n) := by
    apply Finsupp.lhom_ext
    exact boundary_cone_single p n
  exact DFunLike.congr_fun he c

theorem map_cone (f : V → W) (p : V) (n : ℕ) (c : Chain V n) :
    map f _ (cone p n c) = cone (f p) n (map f n c) := by
  have he : (map f _).comp (cone p n) = (cone (f p) n).comp (map f n) := by
    apply Finsupp.lhom_ext
    intro v r
    simp only [LinearMap.comp_apply, cone_single, map_single]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  exact DFunLike.congr_fun he c

end FiniteChains.VertexChains
