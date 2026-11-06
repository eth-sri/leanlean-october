module

public import GS.NonmanifoldCompletion.OriginalMembership
public import GS.NonmanifoldCompletion.BaseFibreGauges
public import GS.NonmanifoldCompletion.LocalAngles
public import GS.NonmanifoldCompletion.SmallLogarithms

@[expose] public section


/-!
# Constructing the original ell,r,c,z,u coordinates near a normalized factor tuple

All sign gauges are fixed diagonal orthogonal matrices. Small angles are
obtained from LocalAngles and small logarithms from SmallLogarithms. The
right angle is anchored at coordinate zero exactly as in originalK.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation GS.Nonmanifold
namespace GS.NonmanifoldCompletion

private theorem orthogonal_cancel_left (S : Mat 2) (hS : Orthogonal S) (X : Mat 2) :
    S*(Sᵀ*X)=X := by rw [← Matrix.mul_assoc,hS.2,Matrix.one_mul]

private theorem involution_cancel_left (D : Mat 2) (hD : D*D=1) (X : Mat 2) :
    D*(D*X)=X := by grind

/-- Conjugating the fixed reflection gives T(u) for an actual unit vector u. -/
theorem conjugate_reflection_coordinates (C : Mat 2) (hC : Orthogonal C) :
    ∃ u : CircleVector, OnCircle u ∧
      ∀ a b : ℝ, middleBlock a b u = Cᵀ * diagTwo a b * C := by
  have h1 := congrFun₂ hC.1
  have h2 := congrFun₂ hC.2
  simp [Matrix.mul_apply, Fin.sum_univ_two, one_apply, Fin.forall_fin_two] at h1 h2
  refine ⟨![C 0 0^2 - C 1 0^2, C 0 0*C 0 1 - C 1 0*C 1 1], ?_, fun a b => ?_⟩
  · simp [OnCircle]; grind
  · ext i j; fin_cases i <;> fin_cases j <;> simp [middleBlock, T, diagTwo, mul_apply, Fin.sum_univ_two] <;> grind

/-- Anchoring the right angle changes the common reflection coordinate only. -/
theorem anchored_block_formula (S : Mat 2) (α β β₀ a b : ℝ) (u : CircleVector)
    (hu : middleBlock a b u =
      (S*rotation β₀)ᵀ * diagTwo a b * (S*rotation β₀)) :
    rotation (α+β₀)*middleBlock a b u*rotation (β-β₀) =
      rotation α*Sᵀ*diagTwo a b*S*rotation β := by
  rw [hu,rotation_add,Matrix.transpose_mul]
  have htail : rotation β₀*rotation (β-β₀)=rotation β := by
    rw [← rotation_add]
    simp
  simp only [Matrix.mul_assoc,
    orthogonal_cancel_left (rotation β₀) (rotation_orthogonal β₀),htail]

/-- Diagonal sign gauges do not change the output block. -/
theorem gauged_block_formula (U V D E S : Mat 2)
    (hD : DiagonalTwo D ∧ Orthogonal D) (hE : DiagonalTwo E ∧ Orthogonal E)
    (hS : Orthogonal S) (a b : ℝ) :
    (U*D*S)*Sᵀ*diagTwo (D 0 0*a*E 0 0) (D 1 1*b*E 1 1)*S*(Sᵀ*E*V) =
      U*diagTwo a b*V := by
  rw [← diagonal_gauge_middle D E hD.1 hE.1]
  simp only [Matrix.mul_assoc,orthogonal_cancel_left S hS,
    involution_cancel_left D (diagonalTwo_involution hD.1 hD.2),
    involution_cancel_left E (diagonalTwo_involution hE.1 hE.2)]

section
variable {q : ℕ}
/-- Exact change from two small skew logarithms to c,z; all Frobenius bounds
refer to the full matrices, not unweighted upper-triangle coordinates. -/
theorem symmetric_log_coordinates (H K : Mat q) (η : ℝ)
    (hH : IsSkew H) (hK : IsSkew K) (hHn : frobSq H < η^2) (hKn : frobSq K < η^2) :
    ∃ c z : Mat q, IsSkew c ∧ IsSkew z ∧
      frobSq c < η^2 ∧ frobSq z < η^2 ∧ c+z=H ∧ c-z=K := by
  have hs (A : Mat q) : frobSq ((1/2:ℝ) • A) = frobSq A / 4 := by
    simp [frobSq, frobInner_smul_left, frobInner_comm A]; ring
  have := frobSq_add H K
  have := frobSq_sub H K
  refine ⟨(1/2:ℝ) • (H+K), (1/2:ℝ) • (H-K), isSkew_smul _ ?_, isSkew_smul _ ?_, ?_, ?_, ?_, ?_⟩
  · simp_all [IsSkew, add_comm]
  · simp_all [IsSkew, sub_eq_add_neg, add_comm]
  all_goals first | (rw [hs]; linarith [frobSq_nonneg (H+K), frobSq_nonneg (H-K)]) | (ext; simp; ring1)

/-- Local normal-form reconstruction with explicitly stated smallness inputs.
The caller below constructs these inputs on an OPEN neighbourhood of each full
fibre representative; no coverage conclusion is assumed here. -/
theorem original_coordinates_of_gauged_near (hq : 0<q)
    (Q₀ : Mat q) (η : ℝ) (hη : 0<η)
    (L : Set (Mat q))
    (hlog : ∀ A ∈ L, Orthogonal A → ∃ H : Mat q,
      IsSkew H ∧ frobSq H < η^2 ∧ originalPsi Q₀ H=A)
    (S : Mat 2) (D E : Fin q → Mat 2) (hS : Orthogonal S)
    (hD : ∀ i, DiagonalTwo (D i) ∧ Orthogonal (D i))
    (hE : ∀ j, DiagonalTwo (E j) ∧ Orthogonal (E j))
    (U V : Fin q → Mat 2) (A B : Mat q)
    (hU : ∀ i, Orthogonal (U i)) (hV : ∀ j, Orthogonal (V j))
    (hA : Orthogonal A) (hB : Orthogonal B)
    (hUl : ∀ i, U i*D i*S ∈ rotationChartDomain (η/4))
    (hVr : ∀ j, Sᵀ*E j*V j ∈ rotationChartDomain (η/4))
    (hAL : gaugeMiddle D E 0 A ∈ L) (hBL : gaugeMiddle D E 1 B ∈ L) :
    ∃ p ∈ originalK q η, originalF Q₀ p =
      flattenBlocks (blockMatrix U*centralPair A B*blockMatrix V) := by
  let i₀ : Fin q := ⟨0,hq⟩
  let α : Fin q → ℝ := fun i => localRotationAngle (U i*D i*S)
  let β : Fin q → ℝ := fun j => localRotationAngle (Sᵀ*E j*V j)
  have hα (i : Fin q) : rotation (α i)=U i*D i*S :=
    rotation_localRotationAngle _ (((hU i).mul (hD i).2).mul hS) (hUl i).1 (hUl i).2.1
  have hβ (j : Fin q) : rotation (β j)=Sᵀ*E j*V j :=
    rotation_localRotationAngle _ ((hS.transpose.mul (hE j).2).mul (hV j)) (hVr j).1 (hVr j).2.1
  obtain ⟨H,hH,hHn,hHA⟩ := hlog _ hAL (gaugeMiddle_orthogonal D E hD hE 0 A hA)
  obtain ⟨K,hK,hKn,hKB⟩ := hlog _ hBL (gaugeMiddle_orthogonal D E hD hE 1 B hB)
  obtain ⟨c,z,hc,hz,hcn,hzn,hplus,hminus⟩ := symmetric_log_coordinates H K η hH hK hHn hKn
  obtain ⟨u,hu,hconj⟩ := conjugate_reflection_coordinates (S*rotation (β i₀))
    (hS.mul (rotation_orthogonal (β i₀)))
  have h0 := (hVr i₀).2.2
  refine ⟨(fun i => α i+β i₀,fun j => β j-β i₀,c,z,u),⟨fun i => by grind [(hUl i).2.2],
    fun j => by grind [(hVr j).2.2],by grind,hc,hz,hcn.le,hzn.le,hu⟩,?_⟩
  ext i j
  let x : Fin q × Fin 2 := finProdFinEquiv.symm i
  let y : Fin q × Fin 2 := finProdFinEquiv.symm j
  change (rotation (α x.1+β i₀)*middleBlock
    (originalPsi Q₀ (c+z) x.1 y.1) (originalPsi Q₀ (c-z) x.1 y.1) u*
    rotation (β y.1-β i₀)) x.2 y.2 =
    (blockMatrix U*centralPair A B*blockMatrix V) x y
  rw [small_block_sandwich,hplus,hminus,hHA,hKB,anchored_block_formula S _ _ _ _ _ u (hconj _ _),
    hα,hβ,gaugeMiddle_apply,gaugeMiddle_apply,gauged_block_formula _ _ _ _ S (hD x.1) (hE y.1) hS]

end

end GS.NonmanifoldCompletion
