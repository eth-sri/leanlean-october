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

variable {q d ℓ : ℕ} (γ : PolynomialBox d ℓ) (cell : Covariate d → Fin q) {C : ModelConstants d}
    {θ : RegressionParameter d}

def pilotGlobalMonomial (x : Covariate d) : ℝ :=
  ∏ i, (x i) ^ (γ i).val

theorem pilotGlobalMonomial_abs_le_one
    {x : Covariate d} (hx : x ∈ unitCube d) : |pilotGlobalMonomial γ x| ≤ 1 := by
  unfold pilotGlobalMonomial
  rw [Finset.abs_prod]
  simp
  have hcoord i : |x i| ≤ 1 := by
    rw [abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ ∏ _i, (1 : ℝ) ^ (γ _i).val :=
      Finset.prod_le_prod₀ (fun i _ => by positivity)
        (fun i _ => by bound)
    _ = 1 := by simp

/-- A fixed global coordinate: a cell indicator times a monomial, optionally
multiplied by the observed response. Local anchored features are linear
combinations of this finite basis. -/
def pilotBasisFeature
    (a : PilotBasisIndex q d ℓ) (z : Observation d) : ℝ :=
  if cell z.1 = a.1.1 then pilotGlobalMonomial a.1.2 z.1 * (if a.2 then z.2 else 1) else 0

theorem pilotBasisFeature_measurable {cell : Covariate d → Fin q}
    (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    Measurable (pilotBasisFeature cell a) := by
  apply Measurable.ite
  · measurability
  · exact (((continuous_finset_prod Finset.univ (fun i _ => (continuous_apply i).pow _) : Continuous
      (pilotGlobalMonomial a.1.2))).measurable.comp measurable_fst).mul
      (by measurability)
  · exact measurable_const

theorem pilotBasisFeature_abs_bound
    (a : PilotBasisIndex q d ℓ) {z : Observation d} (hz : z.1 ∈ unitCube d) :
    |pilotBasisFeature cell a z| ≤
      (Prod.fst ⁻¹' {x | cell x = a.1.1}).indicator
        (fun z => 1 + |z.2|) z := by
  have hmono := pilotGlobalMonomial_abs_le_one a.1.2 hz
  by_cases h : cell z.1 = a.1.1
  · rw [pilotBasisFeature, if_pos h, abs_mul]
    simp [h]
    cases a.2
    · simpa using hmono.trans (by bound)
    · exact (mul_le_mul_of_nonneg_right hmono (abs_nonneg z.2)).trans (by linarith)
  · simp [pilotBasisFeature, h]

/-- The actual covariate marginal proves cube membership for observations. -/
theorem observationLaw_cube_ae (hθ : Admissible C θ) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving hθ).quasiMeasurePreserving.ae
    (designLaw_cube_ae θ)

/-- Every global pilot coordinate is genuinely L² under the original model. -/
theorem pilotBasisFeature_memLp_two (hθ : Admissible C θ)
    {cell : Covariate d → Fin q} (hc : Measurable cell) (a : PilotBasisIndex q d ℓ) :
    MemLp (pilotBasisFeature cell a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  apply ((memLp_const (1 : ℝ)).add ((observationLaw_response_memLp_two hθ).norm)).mono' (pilotBasisFeature_measurable hc a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae hθ] with z hz
  apply (pilotBasisFeature_abs_bound cell a hz).trans
  by_cases h : cell z.1 = a.1.1 <;> simp [h] <;> positivity

/-- Coordinate indexing compatible with the paper's finite-dimensional
polynomial lift; this is an exact reindexing of the global basis. -/
def pilotRawVector (z : Observation d) :
    Fin (Fintype.card (PilotBasisIndex q d ℓ)) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin (PilotBasisIndex q d ℓ)).symm a) z

end NearlyMinimax
