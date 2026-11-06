module

public import GS.UnitaryLocalModel.OuterFibres
public import GS.GlobalGeometry.OriginalGImage

@[expose] public section


/-!
# The actual three-row determinantal cone

The Pauli-sphere outer map has image exactly the matrices of real rank at most
one. The result includes the zero matrix and uses mathlib's matrix rank.
-/
noncomputable section
namespace GS.UnitaryLocalModel

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

theorem rank_sphereOuter_le_one (u : AxisVector) (z : κ → ℝ) :
    Matrix.rank (sphereOuter u z) ≤ 1 :=
  Matrix.rank_vecMulVec_le u z

theorem exists_sphereOuter_of_rank_le_one (W : Matrix (Fin 3) κ ℝ)
    (hW : W.rank ≤ 1) :
    ∃ u : AxisVector, OnSphere u ∧ ∃ z : κ → ℝ, sphereOuter u z = W := by
  classical
  by_cases hzero : W = 0
  · refine ⟨fun i => if i = 0 then 1 else 0, by norm_num [OnSphere], 0, ?_⟩
    rw [hzero]
    ext i j
    simp [sphereOuter]
  have hex : ∃ i j, W i j ≠ 0 := by
    by_contra hn
    apply hzero
    ext i j
    simp_all
  obtain ⟨i₀,j₀,hij⟩ := hex
  let v := fun i => W i j₀
  let r := Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2)
  have hv : 0 < v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    have hi := hij
    have hs := sq_pos_of_ne_zero hi
    fin_cases i₀ <;> dsimp at hs <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1),
      sq_nonneg (v 2)]
  let u := fun i => v i / r
  let z := fun j => r * W i₀ j / W i₀ j₀
  refine ⟨u, ?_, z, ?_⟩
  · change (v 0/r)^2 + (v 1/r)^2 + (v 2/r)^2 = 1
    grind
  · ext i j
    have hm := GS.GlobalGeometry.rank_le_one_minor W hW i i₀ j j₀
    change (W i j₀ / r) * (r * W i₀ j / W i₀ j₀) = W i j
    grind

end GS.UnitaryLocalModel
