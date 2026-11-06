module

public import NearlyMinimax.PaperPopulationFit
public import NearlyMinimax.DyadicPilotPointwise

@[expose] public section

/-! The true population increment in finite coordinates and its actual
inverse-polynomial approximation error. -/

noncomputable section
open Matrix MeasureTheory Set MvPolynomial
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d ℓ : ℕ}

def anchoredFinVector  (v : AnchoredIndex d ℓ → ℝ)  := fun i => v (anchoredFinIndex i)

theorem anchoredFinVector_norm  v :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v)‖ =
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v‖ := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))
  have he : e ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm (anchoredFinVector v) := by
    
    rfl
  
  exact e.norm_map _

theorem anchoredFinReindex_mulVec 
    A
    v :
    anchoredFinReindex d ℓ A *ᵥ anchoredFinVector v = anchoredFinVector (A *ᵥ v) := by
  ext i
  
  exact (Fintype.equivFin (AnchoredIndex d ℓ)).symm.sum_comp
    (fun γ : AnchoredIndex d ℓ => A (anchoredFinIndex i) γ * v γ)

theorem anchoredFinReindex_inv 
    A :
    (anchoredFinReindex d ℓ A)⁻¹ = anchoredFinReindex d ℓ A⁻¹ :=
  Matrix.inv_reindex _ _ A

theorem anchoredFinVector_sub  (v w : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector (v - w) = anchoredFinVector v - anchoredFinVector w := rfl

theorem anchoredFinVector_smul  (a : ℝ) (v : AnchoredIndex d ℓ → ℝ) :
    anchoredFinVector (a • v) = a • anchoredFinVector v := rfl

section
variable (C : ModelConstants d) (θ : RegressionParameter d) (hθ : Admissible C θ) (j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d)
include hθ hx

theorem dyadicFinPilotMoments_eq_actual   (t : Bool) :
    dyadicFinPilotMoments (ℓ := ℓ) θ j x t = anchoredFinVector
      ((dyadicKnownGram j x)⁻¹ *ᵥ (if t then dyadicConstantMoment θ j x else dyadicResponseMoment θ j x)) := by
  ext i
  cases t
  all_goals simp only [dyadicFinPilotMoments, Bool.false_eq_true, ↓reduceIte,
    anchoredFinVector]
  all_goals rw [preconditionedPilotPopulation_eq_sum C θ hθ j x hx]
  all_goals simp only [localPilotRow, localPilotReplaceRow, Matrix.mulVec, dotProduct,
    dyadicPilotPopulation_response C θ hθ j x hx, dyadicPilotPopulation_constant C θ hθ]

theorem dyadicFinPilot_fit   :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) =
        anchoredFinVector (dyadicPopulationFit θ j x) := by
  rw [dyadicFinPilotMoments_eq_actual C θ hθ j x hx false,
    dyadicFinPilotMoments_eq_actual C θ hθ j x hx true]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [← anchoredFinVector_smul, ← anchoredFinVector_sub,
    ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
  rw [dyadicFinPilotGram, anchoredFinReindex_inv, anchoredFinReindex_mulVec,
    dyadicPopulationFit_preconditioner_cancels C θ hθ]

theorem dyadicFinite_increment_eq_actual   :
    (dyadicFinPilotGram (ℓ := ℓ) θ j x)⁻¹ *ᵥ
      (dyadicFinPilotMoments θ j x false - θ.regression x • dyadicFinPilotMoments θ j x true) -
      anchoredFinTransport d ℓ *ᵥ
        ((if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x)⁻¹ *ᵥ
          ((if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) false -
            θ.regression x • (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x) true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
  rw [dyadicFinPilot_fit C θ hθ j x hx]
  cases j with
  | zero => measurability
  | succ j =>
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel_right]
    rw [dyadicFinPilot_fit C θ hθ j x hx]
    rw [anchoredFinTransport, anchoredFinReindex_mulVec, ← anchoredFinVector_sub]
    rfl
end

end


theorem incrementFinVector_eval_population {r } [NeZero r] a b
    A B T U V
    y m :
    incrementFinVector r a b T y m
      (fun i => incrementValuation A B U V ((Fintype.equivFin (incrementVariables r)).symm i)) =
        fun i => eval (incrementValuation A B U V) (incrementEntryPolynomial r a b T y m i) := by
  ext i
  simp only [incrementFinVector, incrementFinPolynomial, eval_rename, Function.comp_def,
    Equiv.symm_apply_apply]

/-- Density bounds yield the actual Hermitian charts used in the inverse
approximation. Only the explicitly displayed small increment enters this
generic deterministic helper. -/
theorem anchoredNormalized_increment_error {d ℓ } [Nonempty (AnchoredIndex d ℓ)]
    u v p q (hpmeas : Measurable p) (hqmeas : Measurable q)
    a b χ ε (ha : 0 < a) (hab : a < b)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hχ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    U V
    y T
    (hδ : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
        T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true)))‖ ≤ ε)
    m :
    ‖(EuclideanSpace.equiv (Fin (anchoredDimension d ℓ)) ℝ).symm
      ((fun i => eval (incrementValuation (anchoredFinNormalizedGram u p)
        (anchoredFinNormalizedGram v q) U V)
          (incrementEntryPolynomial (anchoredDimension d ℓ) a b T y m i)) -
        ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - y • U true) -
          T *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - y • V true))))‖ ≤
      (χ ^ 2 * b ^ (anchoredDimension d ℓ + 1) * parentInverseErrorConstant a b (anchoredDimension d ℓ)) * ε *
        ((m + 1 : ℕ)) ^ anchoredDimension d ℓ * Real.exp (-m * exteriorTau ((a + b) / (b - a))) := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let R := anchoredFinSimilarityUnit (ℓ := ℓ) v
  let G := anchoredFinNormalizedGram (ℓ := ℓ) u p
  let H := anchoredFinNormalizedGram (ℓ := ℓ) v q
  have hG : matrixSimilarity Q (matrixSimilarity Q⁻¹ G) = G := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have hH : matrixSimilarity R (matrixSimilarity R⁻¹ H) = H := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  have he := incrementEntryPolynomial_error a b ha hab
    (matrixSimilarity Q⁻¹ G) (matrixSimilarity R⁻¹ H) T
    (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_isHermitian v q)
    (anchoredFin_similarity_spectrum u p hpmeas a b ha.le hp)
    (anchoredFin_similarity_spectrum v q hqmeas a b ha.le hq)
    Q R χ hχ U V y ε (by simpa only [hG, hH] using hδ) m
  simpa only [hG, hH] using he

end NearlyMinimax
