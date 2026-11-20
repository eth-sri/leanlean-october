module

public import GS.RankFactorization

public import Mathlib.Analysis.InnerProductSpace.PiL2

public import Mathlib.Analysis.Normed.Module.Normalize

public import Mathlib.Algebra.BigOperators.Field

public import Mathlib.Topology.Instances.Matrix

@[expose] public section

noncomputable section
open Matrix Submodule
namespace GS
variable {ι κ : Type*} [Fintype κ]

/-- Every real rank-at-most-one matrix has an outer presentation with a
unit first factor. -/
theorem rank_one_normalized [Fintype ι] [Nonempty ι] (W : Matrix ι κ ℝ) (h : W.rank ≤ 1) :
    ∃ u : ι → ℝ, ∑ i, u i ^ 2 = 1 ∧ ∃ z : κ → ℝ, vecMulVec u z = W := by
  classical
  obtain ⟨U,V,hW⟩ := (rank_le_card_iff_factorization (τ := Fin 1) W).mp (by simpa using h)
  let u := U.col 0
  let z := V.row 0
  have he : vecMulVec u z = W := by
    rw [hW]
    ext i j
    simp [u, z, vecMulVec_apply, Matrix.mul_apply]
  by_cases hu : u = 0
  · let a : ι := Classical.ofNonempty
    exact ⟨fun i => if i = a then 1 else 0, by simp [ite_pow], 0,
      by rw [← he, hu]; ext; simp [vecMulVec_apply]⟩
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 u
  let w := NormedSpace.normalize v
  have hw : ‖w‖ = 1 := NormedSpace.norm_normalize (by simpa [v] using hu)
  have hn : ‖v‖ • w.ofLp = u := congrArg WithLp.ofLp (NormedSpace.norm_smul_normalize v)
  refine ⟨w.ofLp, by grind [EuclideanSpace.real_norm_sq_eq], ‖v‖ • z, ?_⟩
  rw [← he, ← hn]
  simp

/-- A nonzero pivot determines the matrix from its column and row. -/
theorem rank_one_pivot [Fintype ι] [Nonempty ι] (W : Matrix ι κ ℝ) (h : W.rank ≤ 1)
    {a : ι} {j : κ} (hj : W a j ≠ 0) (b : ι) (k : κ) :
    W b j / W a j * W a k = W b k := by
  obtain ⟨u,_,z,rfl⟩ := rank_one_normalized W h
  grind [vecMulVec_apply]

end GS

set_option backward.isDefEq.respectTransparency false

namespace GS

abbrev RankOne (r : ℕ) (κ : Type*) [Fintype κ] :=
  {W : Matrix (Fin (r+1)) κ ℝ // W.rank ≤ 1}

variable {κ ν : Type*} [Fintype κ] {r : ℕ}

def rankZero : RankOne r κ := ⟨0, by simp⟩

/-- Relabel columns of the determinantal cone. -/
def rankReindex [Fintype ν] (e : κ ≃ ν) : RankOne r κ ≃ₜ RankOne r ν :=
  (show Matrix (Fin (r+1)) κ ℝ ≃ₜ Matrix (Fin (r+1)) ν ℝ from
    ⟨Matrix.reindex (.refl _) e, by fun_prop, by fun_prop⟩).subtype fun W => by
      change _ ↔ (Matrix.reindex (.refl _) e W).rank ≤ 1
      rw [Matrix.rank_reindex]

end GS
