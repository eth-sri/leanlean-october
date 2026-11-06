
import GS.OriginalLocalModel
import GS.Extensions.FiniteTopology
open GS.MatrixBase



/-!
# Exact set-theoretic description of the ORIGINAL g(K)

This module preserves the manuscript's g, K, c, z, u. It proves that the last
component of g(K) is the rank-at-most-one Frobenius ball whose two rows are
vectorized skew matrices. Normalization is an existence argument, NOT a
continuous choice of rank-one factors at the zero matrix.

The remaining reduction from row-skew matrices to exactly d=q(q-1)/2
coordinates, local coverage of the full GS family, and the nonmanifold
obstruction are deliberately NOT claimed here.
-/
open Matrix
namespace GS.GlobalGeometry
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Normalized outer factorization, including W=0. Only the EXISTENCE of
u,z is asserted; uniqueness or continuous selection is not assumed. -/
theorem exists_unit_outer_of_rank_le_one (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) : ∃ u : CircleVector, OnCircle u ∧ ∃ z : κ → ℝ, outer u z = W := by
  obtain ⟨u,hu,z,h⟩ := RankOne.exists_unit_outer (0 : Fin 2) W hW
  exact ⟨u,by aesop,z,h⟩


variable (q : ℕ)

abbrev OriginalImageCoordinates  :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ

variable (η : ℝ)

/-- A rank cone in the row-skew subspace; no Euclidean dimension is yet asserted. -/
def originalGImageSet   : Set (OriginalImageCoordinates q) :=
  {p | (∀ i, |p.1 i| ≤ η) ∧ (∀ j, |p.2.1 j| ≤ η) ∧
    (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    cFrobSq p.2.2.1 ≤ η^2 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧
    p.2.2.2.rank ≤ 1 ∧ cFrobSq p.2.2.2 ≤ η^2}

/-- Exact image equality, with the ORIGINAL definitions of g and K. -/
theorem originalG_image_eq   :
    originalG '' originalK q η = originalGImageSet q η := by
  ext p
  constructor
  · rintro ⟨⟨ell,r,c,z,u⟩,hp,rfl⟩
    rcases hp with ⟨hell,hr,hr0,hc,hz,hcn,hzn,hu⟩
    refine ⟨hell,hr,hr0,hc,hcn,?_,rank_outer_le_one _ _,?_⟩
    · intro k
      change IsSkew ((u k) • z)
      change zᵀ = -z at hz
      simp only [IsSkew, Matrix.transpose_smul, hz, smul_neg]
    · change cFrobSq (outer u (fun ij : Fin q × Fin q => z ij.1 ij.2)) ≤ η^2
      rw [frobSq_outer hu]
      simpa only [cFrobSq, cFrobInner,star_trivial,RCLike.re_to_real, Fintype.sum_prod_type, pow_two] using hzn
  · rcases p with ⟨ell,r,c,W⟩
    rintro ⟨hell,hr,hr0,hc,hcn,hrows,hRank,hWn⟩
    obtain ⟨u,hu,z,he⟩ := exists_unit_outer_of_rank_le_one W hRank
    let Z : Mat q := fun i j => z (i,j)
    have hz : IsSkew Z := by
      obtain ⟨k,hk⟩ := Function.ne_iff.mp (RankOne.nonzero (u := u)
        (by aesop))
      ext i j
      change z (j,i) = -z (i,j)
      apply mul_left_cancel₀ hk
      have h := congrFun (congrFun (hrows k) i) j
      rw [← he] at h
      change u k*z (j,i) = -(u k*z (i,j)) at h
      simpa only [mul_neg] using h
    have hn : cFrobSq Z ≤ η^2 := by
      rw [← he, frobSq_outer hu] at hWn
      simpa [Z, cFrobSq, cFrobInner, Fintype.sum_prod_type, pow_two] using hWn
    refine ⟨(ell,r,c,Z,u), ⟨hell,hr,hr0,hc,hz,hcn,hn,hu⟩,?_⟩
    change (ell,r,c,outer u (fun ij => Z ij.1 ij.2))=(ell,r,c,W)
    simpa only [Z] using congrArg (fun A => (ell,r,c,A)) he

end GS.GlobalGeometry
