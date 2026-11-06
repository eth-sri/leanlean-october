module

public import GS.Nonmanifold.SkewCoordinates

@[expose] public section


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
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
namespace GS.Nonmanifold

abbrev NonzeroIndex (q : ℕ) := {i : Fin q // i.val ≠ 0}

def packRight {q : ℕ} (r : Fin q → ℝ) : NonzeroIndex q → ℝ := fun j => r j.val

section
variable {q : ℕ} (x : NonzeroIndex q → ℝ)
def unpackRight : Fin q → ℝ :=
  fun j => if h : j.val = 0 then 0 else x ⟨j,h⟩

theorem unpackRight_anchored :
    ∀ j : Fin q, j.val = 0 → unpackRight x j = 0 := fun j hj => by simp [unpackRight, hj]

theorem pack_unpackRight :
    packRight (unpackRight x) = x := by
  funext j
  simp [packRight, unpackRight, j.property]

end

theorem unpack_packRight (r : Fin q → ℝ)
    (hr : ∀ j : Fin q, j.val = 0 → r j = 0) :
    unpackRight (packRight r) = r := by
  funext j
  by_cases hj : j.val = 0 <;> simp [packRight, unpackRight, hj, hr j]

section
variable (q : ℕ)
theorem continuous_unpackRight : Continuous (@unpackRight q) :=
  continuous_pi fun j => by by_cases hj : j.val = 0 <;> simp only [unpackRight, hj, dite_true, dite_false] <;> fun_prop

/-- The original image constraints with only the radius bounds removed. -/
def originalModelSet : Set (OriginalImageCoordinates q) :=
  {p | (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧ p.2.2.2.rank ≤ 1}

abbrev OriginalModel := ↥(originalModelSet q)

abbrev ModelCoordinates :=
  (Fin q → ℝ) × (NonzeroIndex q → ℝ) × (UpperIndex q → ℝ) ×
    {Z : Matrix (Fin 2) (UpperIndex q) ℝ // Z.rank ≤ 1}

end

section
variable {q : ℕ}
def encodeModel (p : OriginalModel q) : ModelCoordinates q :=
  (p.val.1, packRight p.val.2.1, packSkew p.val.2.2.1,
    ⟨packRows p.val.2.2.2, packRows_rank_le_one _ p.property.2.2.2⟩)

def decodeModel (p : ModelCoordinates q) : OriginalModel q :=
  ⟨(p.1, unpackRight p.2.1, unpackSkew p.2.2.1, unpackRows p.2.2.2.val),
    unpackRight_anchored _, unpackSkew_isSkew _, unpackRows_isSkew _,
    unpackRows_rank_le_one _ p.2.2.2.property⟩

theorem decode_encodeModel (p : OriginalModel q) :
    decodeModel (encodeModel p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨ell,r,c,W⟩,hr,hc,hW,hRank⟩
  change (ell, unpackRight (packRight r), unpackSkew (packSkew c),
    unpackRows (packRows W)) = (ell,r,c,W)
  rw [unpack_packRight r hr, unpack_packSkew hc, unpack_packRows W hW]

theorem encode_decodeModel (p : ModelCoordinates q) :
    encodeModel (decodeModel p) = p := by
  simp [encodeModel, decodeModel, pack_unpackRight, pack_unpackSkew, pack_unpackRows]

end

section
variable (q : ℕ)
theorem continuous_encodeModel : Continuous (@encodeModel q) := by
  unfold encodeModel packRight packSkew packRows
  fun_prop

theorem continuous_decodeModel : Continuous (@decodeModel q) := by
  have := continuous_unpackRight q
  have := continuous_unpackSkew q
  have := continuous_unpackRows q
  unfold decodeModel
  fun_prop

end

/-- A polynomial squared radius on the full ambient g-coordinate space. -/
def modelRadiusSq (p : OriginalImageCoordinates q) : ℝ :=
  (∑ i, p.1 i^2) + (∑ j, p.2.1 j^2) + frobSq p.2.2.1 + frobSq p.2.2.2

section
variable (q : ℕ)
theorem continuous_modelRadiusSq : Continuous (@modelRadiusSq q) := by
  unfold modelRadiusSq frobSq frobInner
  fun_prop

theorem originalG_image_subset_model (η : ℝ) :
    originalG '' originalK q η ⊆ originalModelSet q := by
  rw [originalG_image_eq]
  rintro p ⟨hell,hr,hr0,hc,hcn,hW,hRank,hWn⟩
  exact ⟨hr0,hc,hW,hRank⟩

end

/-- An explicit small relative neighbourhood lies in the original compact image. -/
theorem small_modelRadius_mem_originalG {η : ℝ} (hη : 0 < η)
    (p : OriginalImageCoordinates q) (hp : p ∈ originalModelSet q)
    (hn : modelRadiusSq p < η^2) : p ∈ originalG '' originalK q η := by
  rw [originalG_image_eq]
  have := frobSq_nonneg p.2.2.1
  have := frobSq_nonneg p.2.2.2
  have : 0 ≤ ∑ i, p.1 i^2 := by positivity
  have : 0 ≤ ∑ j, p.2.1 j^2 := by positivity
  unfold modelRadiusSq at hn
  refine ⟨fun i => ?_, fun i => ?_, hp.1, hp.2.1, by linarith, hp.2.2.1, hp.2.2.2, by linarith⟩ <;>
    nlinarith [sq_abs (p.1 i), sq_abs (p.2.1 i), Finset.single_le_sum (fun k _ => sq_nonneg (p.1 k)) (Finset.mem_univ i),
      Finset.single_le_sum (fun k _ => sq_nonneg (p.2.1 k)) (Finset.mem_univ i)]

end GS.Nonmanifold
