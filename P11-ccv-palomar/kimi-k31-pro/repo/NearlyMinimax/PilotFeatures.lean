module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.GridProjection
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.FieldLiftCovariance

@[expose] public section

/-! Actual finite global coordinates for local polynomial pilots. These are
functions of the original observation, with no bounded-response model. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev PilotBasisIndex (q d ℓ : ℕ) := (Fin q × PolynomialBox d ℓ) × Bool

def pilotGlobalMonomial {d ℓ : ℕ} (γ : PolynomialBox d ℓ) (x : Covariate d) : ℝ :=
  ∏ i, (x i) ^ (γ i).val

theorem pilotGlobalMonomial_continuous {d ℓ : ℕ} (γ : PolynomialBox d ℓ) :
    Continuous (pilotGlobalMonomial γ) :=
  continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _)

theorem pilotGlobalMonomial_abs_le_one {d ℓ : ℕ} (γ : PolynomialBox d ℓ)
    (x : Covariate d) (hx : x ∈ unitCube d) : |pilotGlobalMonomial γ x| ≤ 1 := by
  unfold pilotGlobalMonomial
  rw [Finset.abs_prod]
  simp only [abs_pow]
  have hcoord (i : Fin d) : |x i| ≤ 1 := by
    rw [abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ ∏ _i : Fin d, (1 : ℝ) ^ (γ _i).val :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hcoord i) _)
    _ = 1 := by simp

/-- A fixed global coordinate: a cell indicator times a monomial, optionally
multiplied by the observed response. Local anchored features are linear
combinations of this finite basis. -/
def pilotBasisFeature {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) : ℝ :=
  if cell z.1 = a.1.1 then pilotGlobalMonomial a.1.2 z.1 * (if a.2 then z.2 else 1) else 0

theorem pilotBasisFeature_measurable {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    Measurable (pilotBasisFeature cell a) := by
  unfold pilotBasisFeature
  apply Measurable.ite
  · exact measurableSet_eq_fun (hc.comp measurable_fst) measurable_const
  · exact ((pilotGlobalMonomial_continuous a.1.2).measurable.comp measurable_fst).mul
      (by cases a.2 <;> first | exact measurable_const | exact measurable_snd)
  · exact measurable_const

theorem pilotBasisFeature_abs_bound {q d ℓ : ℕ} (cell : Covariate d → Fin q)
    (a : PilotBasisIndex q d ℓ) (z : Observation d) (hz : z.1 ∈ unitCube d) :
    |pilotBasisFeature cell a z| ≤
      (Prod.fst ⁻¹' {x | cell x = a.1.1}).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  have hmono := pilotGlobalMonomial_abs_le_one a.1.2 z.1 hz
  by_cases h : cell z.1 = a.1.1
  · rw [pilotBasisFeature, if_pos h, abs_mul]
    simp only [mem_preimage, mem_setOf_eq, h, indicator_of_mem]
    cases a.2
    · simpa using hmono.trans (le_add_of_nonneg_right (abs_nonneg z.2))
    · simp only [↓reduceIte]
      exact (mul_le_mul_of_nonneg_right hmono (abs_nonneg z.2)).trans (by linarith)
  · simp [pilotBasisFeature, h]

/-- The actual covariate marginal proves cube membership for observations. -/
theorem observationLaw_cube_ae {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)

/-- Every global pilot coordinate is genuinely L² under the original model. -/
theorem pilotBasisFeature_memLp_two {q d ℓ : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (cell : Covariate d → Fin q) (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    MemLp (pilotBasisFeature cell a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hbase : MemLp (fun z : Observation d => 1 + |z.2|) 2 (observationLaw θ) :=
    (memLp_const (1 : ℝ)).add hy
  apply hbase.mono' (pilotBasisFeature_measurable cell hc a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  rw [Real.norm_eq_abs]
  apply (pilotBasisFeature_abs_bound cell a z hz).trans
  by_cases h : cell z.1 = a.1.1 <;> simp [h] <;> positivity

/-- Coordinate indexing compatible with the paper's finite-dimensional
polynomial lift; this is an exact reindexing of the global basis. -/
def pilotRawVector {q d ℓ : ℕ} (cell : Covariate d → Fin q) (z : Observation d) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a) z

end NearlyMinimax
