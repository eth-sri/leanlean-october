module

public import QPBT.Test.MagicSquareTheorems.Rigidity.Transfer
public import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
public import QPBT.Test.MagicSquareTheorems.Rigidity.Anticommutation
public import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget

/-!
# The joint state estimate of Magic Square rigidity

This file proves the state estimate of `thm:ms-rigidity` on the dilated
strategy: the tensor of the two players' two-qubit controlled-swap embeddings
carries the shared state to within `O(sqrt ε + sqrt δ)` of two EPR pairs
tensored with a residual bipartite vector, and that residual can be normalized
to the unit auxiliary state of the conclusion.

The argument is the coordinatewise one.  The image of the state under the two
embeddings has, at the pair of register labels `(e, f)`, the component

    `(A_e ⊗ B_f) ψ`,

where `A_e` and `B_f` are the residual factors of the two controlled swaps.
Since the two logical pairs are applied in succession, each component factors as
a second-pair component applied to a first-pair component, so the estimates of
`Rigidity/SwapPair.lean` apply twice: once on the state, once on the residual of
the first pair, whose second-pair hypotheses are supplied by
`Rigidity/SwapTransport.lean`.  Every component with `e ≠ f` is small and every
component with `e = f` is close to the one at the zero label; sixteen labels
then give the estimate.

## References

blueprint `thm:ms-rigidity`,
paper `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:612-652`;
the cited robust self-test is Coladangelo--Stark, arXiv:1709.09267v2,
Theorem 6.9, `references/cs-paper/self-testing.tex:660-730`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.MagicSquareRigidity

open MIPStarRE.LDT MIPStarRE.Quantum

noncomputable section

variable {ιA ιB : Type} [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]

/-! ## Coordinates -/

/-! ## The target state in coordinates -/

/-! ## From componentwise bounds to the joint estimate -/

/-! ## Residual factors -/

/-! ## The commutator of an anticommutator with a first-pair reflection -/

/-! ## The second-pair defects on the residual of the first swap -/

section SecondPair

variable {X₁A Z₁A X₂A Z₂A : Op ιA} {X₁B Z₁B X₂B Z₂B : Op ιB} {t : ℝ}

end SecondPair

/-! ## The joint state estimate -/

/-! ## Normalizing the residual -/

/-- The coordinate tensor is homogeneous in its second argument. -/
theorem vecTensor_smul_right {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (c : ℂ) (u : EuclideanSpace ℂ ι) (v : EuclideanSpace ℂ κ) :
    vecTensor u (c • v) = c • vecTensor u v := by
  ext p
  simp [vecTensor, EuclideanSpace.equiv]
  ring

/-- Reindexing is homogeneous. -/
theorem reindexState_smul {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (c : ℂ) (x : EuclideanSpace ℂ ι) :
    reindexState e (c • x) = c • reindexState e x := by
  ext p
  simp [reindexState, EuclideanSpace.equiv]

/-- The residual of the joint state estimate can be replaced by a unit vector at
twice the cost.  This is the normalization step of the conclusion of
`thm:ms-rigidity`, whose auxiliary state is required to be a unit vector. -/
theorem exists_unit_residual {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
    (u : EuclideanSpace ℂ ((V × ιA) × (V × ιB))) (hu : ‖u‖ = 1)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1) (c : ℝ)
    (r0 : EuclideanSpace ℂ (ιA × ιB))
    (h : ‖u - reindexState prodShuffle (vecTensor (eprState V) r0)‖ ≤ c) :
    ∃ r : EuclideanSpace ℂ (ιA × ιB), ‖r‖ = 1 ∧
      ‖u - reindexState prodShuffle (vecTensor (eprState V) r)‖ ≤ 2 * c := by
  have htarget : ∀ r : EuclideanSpace ℂ (ιA × ιB),
      ‖reindexState prodShuffle (vecTensor (eprState V) r)‖ = ‖r‖ :=
    fun r => norm_reindexState_prodShuffle_vecTensor_eprState r
  have hgap : |1 - ‖r0‖| ≤ c := by
    have h1 := abs_norm_sub_norm_le u
      (reindexState prodShuffle (vecTensor (eprState V) r0))
    rw [hu, htarget] at h1
    exact le_trans h1 h
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) hgap
  by_cases h0 : r0 = 0
  · refine ⟨ψ, hψ, ?_⟩
    have h1 : (1 : ℝ) ≤ c := by
      rw [h0, norm_zero] at hgap
      simpa using hgap
    calc ‖u - reindexState prodShuffle (vecTensor (eprState V) ψ)‖
        ≤ ‖u‖ + ‖reindexState prodShuffle (vecTensor (eprState V) ψ)‖ := norm_sub_le _ _
      _ = 2 := by rw [hu, htarget, hψ]; norm_num
      _ ≤ 2 * c := by linarith
  · have hN : 0 < ‖r0‖ := norm_pos_iff.mpr h0
    refine ⟨((‖r0‖ : ℝ) : ℂ)⁻¹ • r0, ?_, ?_⟩
    · rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hN,
        inv_mul_cancel₀ (ne_of_gt hN)]
    · have hscal : reindexState prodShuffle
          (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)) =
          ((‖r0‖ : ℝ) : ℂ)⁻¹ • reindexState prodShuffle (vecTensor (eprState V) r0) := by
        rw [vecTensor_smul_right, reindexState_smul]
      have hdiff : ‖reindexState prodShuffle (vecTensor (eprState V) r0) -
          reindexState prodShuffle
            (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0))‖ = |1 - ‖r0‖| := by
        have hcollect : reindexState prodShuffle (vecTensor (eprState V) r0) -
            ((‖r0‖ : ℝ) : ℂ)⁻¹ •
              reindexState prodShuffle (vecTensor (eprState V) r0) =
            ((1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹) •
              reindexState prodShuffle (vecTensor (eprState V) r0) := by
          module
        have hs : ‖(1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹‖ = |1 - ‖r0‖⁻¹| := by
          rw [show (1 : ℂ) - ((‖r0‖ : ℝ) : ℂ)⁻¹ = (((1 - ‖r0‖⁻¹ : ℝ)) : ℂ) by
            push_cast
            ring]
          rw [Complex.norm_real, Real.norm_eq_abs]
        have hfin : |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖| := by
          have h1 : (1 - ‖r0‖⁻¹) * ‖r0‖ = -(1 - ‖r0‖) := by
            field_simp
            ring
          calc |1 - ‖r0‖⁻¹| * ‖r0‖ = |1 - ‖r0‖⁻¹| * |‖r0‖| := by rw [abs_of_pos hN]
            _ = |(1 - ‖r0‖⁻¹) * ‖r0‖| := (abs_mul _ _).symm
            _ = |-(1 - ‖r0‖)| := by rw [h1]
            _ = |1 - ‖r0‖| := abs_neg _
        rw [hscal, hcollect, norm_smul, htarget, hs, hfin]
      have htri := norm_sub_le_norm_sub_add_norm_sub u
        (reindexState prodShuffle (vecTensor (eprState V) r0))
        (reindexState prodShuffle (vecTensor (eprState V) (((‖r0‖ : ℝ) : ℂ)⁻¹ • r0)))
      rw [hdiff] at htri
      linarith [htri, h, hgap]

end

end MIPStarRE.QPBT.MagicSquareRigidity
