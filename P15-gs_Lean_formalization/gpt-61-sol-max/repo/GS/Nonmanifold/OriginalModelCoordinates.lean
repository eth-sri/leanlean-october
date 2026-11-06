import Mathlib.Tactic

import GS.Nonmanifold.SkewCoordinates
open GS.MatrixBase




/-!
# The unbounded model containing the original g(K)

Two separate steps are constructed here:
* the original row-skew, anchored-coordinate model is homeomorphic to a
  product of unconstrained finite coordinate spaces and a genuine rank cone;
* for eta > 0 the original g(K_eta) contains a relative neighbourhood of zero
  in this unbounded model, with an explicit polynomial neighbourhood.

This is the g-side neighbourhood statement. It must not be confused with the
still-open f-side coverage of a neighbourhood in the entire GS matrix family.
-/
open GS.GlobalGeometry
namespace GS.Nonmanifold

variable (r : Fin q → ℝ)

abbrev NonzeroIndex (q : ℕ) := {i : Fin q // i.val ≠ 0}

def packRight  : NonzeroIndex q → ℝ := fun j => r j.val

def unpackRight (x : NonzeroIndex q → ℝ) := fun j => if h : j.val = 0 then 0 else x ⟨j,h⟩



theorem pack_unpackRight (x : NonzeroIndex q → ℝ) :
    packRight (unpackRight x) = x := by grind [packRight,unpackRight]



theorem continuous_unpackRight (q : ℕ) : Continuous (@unpackRight q) := by
  apply continuous_pi
  intro j
  by_cases hj : j.val = 0
  · simp_all [unpackRight,continuous_const]
  · simp_all [unpackRight,continuous_apply]

/-- The original image constraints with only the radius bounds removed. -/
def originalModelSet (q : ℕ) : Set (OriginalImageCoordinates q) :=
  {p | (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧ p.2.2.2.rank ≤ 1}

abbrev OriginalModel (q : ℕ) := ↥(originalModelSet q)

abbrev ModelCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (NonzeroIndex q → ℝ) × (UpperIndex q → ℝ) ×
    {Z : Matrix (Fin 2) (UpperIndex q) ℝ // Z.rank ≤ 1}

def encodeModel (p : OriginalModel q) : ModelCoordinates q :=
  (p.val.1, packRight p.val.2.1, packSkew p.val.2.2.1,
    ⟨packRows p.val.2.2.2, (Matrix.rank_submatrix_le _ id Subtype.val).trans p.property.2.2.2⟩)

def decodeModel (p : ModelCoordinates q) : OriginalModel q :=
  ⟨(p.1, unpackRight p.2.1, unpackSkew p.2.2.1, unpackRows p.2.2.2.val),
    (by simp_all [unpackRight]), unpackSkew_isSkew _,
    (fun r => unpackSkew_isSkew _), by

      obtain ⟨u,hu,z,hz⟩ := GS.GlobalGeometry.exists_unit_outer_of_rank_le_one _ p.2.2.2.property
      rw [← hz]
      convert rank_outer_le_one u (fun ij : Fin q × Fin q => unpackSkew z ij.1 ij.2) using 1
      congr 1
      ext r ij
      simp [unpackRows,outer,unpackSkew,mul_dite,mul_neg]⟩

theorem decode_encodeModel (p : OriginalModel q) :
    decodeModel (encodeModel p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨ell,r,c,W⟩,hr,hc,hW,hRank⟩
  change (ell, unpackRight (packRight r), unpackSkew (packSkew c),
    unpackRows (packRows W)) = (ell,r,c,W)
  have hr' : unpackRight (packRight r) = r := by grind [packRight,unpackRight]
  have hw' : unpackRows (packRows W) = W := by
    ext r ij
    exact congrFun (congrFun (unpack_packSkew (hW r)) ij.1) ij.2
  rw [hr',unpack_packSkew hc,hw']
  rfl

theorem encode_decodeModel (p : ModelCoordinates q) :
    encodeModel (decodeModel p) = p := by simp_all [decodeModel,encodeModel,pack_unpackRight,pack_unpackRows,pack_unpackSkew]

theorem continuous_encodeModel (q : ℕ) : Continuous (@encodeModel q) := by
  unfold encodeModel packRight packSkew packRows
  fun_prop

attribute [fun_prop] continuous_unpackRight continuous_unpackSkew continuous_unpackRows

theorem continuous_decodeModel (q : ℕ) : Continuous (@decodeModel q) := by
  unfold decodeModel
  fun_prop

/-- A polynomial squared radius on the full ambient g-coordinate space. -/
noncomputable def modelRadiusSq (p : OriginalImageCoordinates q) : ℝ :=
  (∑ i, p.1 i^2) + (∑ j, p.2.1 j^2) + cFrobSq p.2.2.1 + cFrobSq p.2.2.2

theorem continuous_modelRadiusSq (q : ℕ) : Continuous (@modelRadiusSq q) := by
  unfold modelRadiusSq
  simp only [cFrobSq,cFrobInner,star_trivial,RCLike.re_to_real]
  fun_prop

theorem originalG_image_subset_model (q : ℕ) (η : ℝ) :
    originalG '' originalK q η ⊆ originalModelSet q := by
  rw [originalG_image_eq]
  rintro p ⟨hell,hr,hr0,hc,hcn,hW,hRank,hWn⟩
  exact ⟨hr0,hc,hW,hRank⟩

/-- An explicit small relative neighbourhood lies in the original compact image. -/
theorem small_modelRadius_mem_originalG {η : ℝ} (hη : 0 < η)
    (p : OriginalImageCoordinates q) (hp : p ∈ originalModelSet q)
    (hn : modelRadiusSq p < η^2) : p ∈ originalG '' originalK q η := by
  rw [originalG_image_eq]
  have hL : 0 ≤ ∑ i, p.1 i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hR : 0 ≤ ∑ j, p.2.1 j^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hc := cFrobSq_nonneg p.2.2.1
  have hW := cFrobSq_nonneg p.2.2.2
  have hC : cFrobSq p.2.2.1 ≤ η^2 := by grind [modelRadiusSq]
  have hZ : cFrobSq p.2.2.2 ≤ η^2 := by grind [modelRadiusSq]
  refine ⟨?_,?_,hp.1,hp.2.1,hC,hp.2.2.1,hp.2.2.2,hZ⟩
  · intro i
    have hs : p.1 i^2 ≤ ∑ k, p.1 k^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have hh : p.1 i^2 < η^2 := by grind [modelRadiusSq]
    nlinarith [sq_abs (p.1 i)]
  · intro j
    have hs : p.2.1 j^2 ≤ ∑ k, p.2.1 k^2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hh : p.2.1 j^2 < η^2 := by grind [modelRadiusSq]
    nlinarith [sq_abs (p.2.1 j)]

end GS.Nonmanifold
