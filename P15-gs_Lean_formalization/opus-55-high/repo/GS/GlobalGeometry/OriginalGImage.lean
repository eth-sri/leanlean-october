module

public import GS.OriginalLocalModel
public import GS.Extensions.FiniteTopology

@[expose] public section


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
noncomputable section
open Matrix GS GS.Extensions
namespace GS.GlobalGeometry
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Rank <= 1 forces every 2-by-2 minor to vanish. -/
theorem rank_le_one_minor {ρ : Type*} (W : Matrix ρ κ ℝ) (hW : W.rank ≤ 1) (a b : ρ) (j k : κ) :
    W a j * W b k = W a k * W b j := by
  have hd : (W.submatrix ![a,b] ![j,k]).det = 0 := by
    by_contra hn
    have := (rank_of_isUnit _ ((isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hn))).symm.trans_le
      ((rank_submatrix_le W _ _).trans hW)
    simp_all
  simpa [det_fin_two, sub_eq_zero] using (det_fin_two _).symm.trans hd

/-- Normalized outer factorization, including W=0. Only the EXISTENCE of
u,z is asserted; uniqueness or continuous selection is not assumed. -/
theorem exists_unit_outer_of_rank_le_one (W : Matrix (Fin 2) κ ℝ)
    (hW : W.rank ≤ 1) : ∃ u : CircleVector, OnCircle u ∧ ∃ z : κ → ℝ, outer u z = W := by
  by_cases hz : ∀ j, W 0 j = 0
  · refine ⟨![0,1], by norm_num [OnCircle], W 1, ?_⟩
    ext i j
    fin_cases i <;> simp [outer, hz]
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    let a := W 1 j / W 0 j
    let r := Real.sqrt (1+a^2)
    have hr : 0 < r := by positivity
    have hr0 := ne_of_gt hr
    have hrow (k : κ) : W 1 k = a * W 0 k := by
      have hm := rank_le_one_minor W hW 0 1 j k
      grind
    refine ⟨![1/r,a/r], ?_, fun k => r*W 0 k, ?_⟩
    · change (1/r)^2+(a/r)^2=1
      grind
    · ext i k
      fin_cases i
      · simp [outer, hr0]
      · change (a / r) * (r * W 0 k) = W 1 k
        grind

abbrev OriginalImageCoordinates (q : ℕ) :=
  (Fin q → ℝ) × (Fin q → ℝ) × Mat q × Matrix (Fin 2) (Fin q × Fin q) ℝ

section
variable (q : ℕ) (η : ℝ)
/-- A rank cone in the row-skew subspace; no Euclidean dimension is yet asserted. -/
def originalGImageSet : Set (OriginalImageCoordinates q) :=
  {p | (∀ i, |p.1 i| ≤ η) ∧ (∀ j, |p.2.1 j| ≤ η) ∧
    (∀ j : Fin q, j.val=0 → p.2.1 j=0) ∧ IsSkew p.2.2.1 ∧
    frobSq p.2.2.1 ≤ η^2 ∧
    (∀ r, IsSkew (fun i j => p.2.2.2 r (i,j))) ∧
    p.2.2.2.rank ≤ 1 ∧ frobSq p.2.2.2 ≤ η^2}

/-- Exact image equality, with the ORIGINAL definitions of g and K. -/
theorem originalG_image_eq :
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
    · change frobSq (outer u (fun ij : Fin q × Fin q => z ij.1 ij.2)) ≤ η^2
      rw [frobSq_outer hu]
      simpa only [frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hzn
  · rcases p with ⟨ell,r,c,W⟩
    rintro ⟨hell,hr,hr0,hc,hcn,hrows,hRank,hWn⟩
    obtain ⟨u,hu,z,rfl⟩ := exists_unit_outer_of_rank_le_one W hRank
    rw [frobSq_outer hu] at hWn
    refine ⟨(ell,r,c,fun i j => z (i,j),u), ⟨hell,hr,hr0,hc,?_,hcn,
      by simpa only [frobSq, frobInner, Fintype.sum_prod_type, pow_two] using hWn,hu⟩, by aesop⟩
    unfold IsSkew
    ext i j
    have h₀ := congrFun₂ (hrows 0) i j
    have h₁ := congrFun₂ (hrows 1) i j
    have hu : u 0^2+u 1^2 = 1 := hu
    change u 0 * z (j,i) = -(u 0 * z (i,j)) at h₀
    change u 1 * z (j,i) = -(u 1 * z (i,j)) at h₁
    change z (j,i) = -z (i,j)
    linear_combination u 0 * h₀ + u 1 * h₁ - (z (j,i) + z (i,j)) * hu

end

end GS.GlobalGeometry
