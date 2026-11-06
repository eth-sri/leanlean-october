module

public import NearlyMinimax.AnchoredFeatures
public import NearlyMinimax.GridProjection
public import NearlyMinimax.ObservationMoments
public import NearlyMinimax.FieldLiftCovariance
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual finite global coordinates for local polynomial pilots. These are
functions of the original observation, with no bounded-response model. -/

𝚴
𝚪
𝚨

𝚭
𝚩

abbrev PilotBasisIndex (q d ℓ : ℕ) := (Fin q × 𝗫₂) × Bool

def pilotGlobalMonomial (γ : 𝗫₂) (x : Covariate d) : ℝ :=
  ∏ i, x i ^ 𝘇

section

variable (γ : 𝗫₂)

theorem pilotGlobalMonomial_continuous :
    Continuous $ pilotGlobalMonomial γ :=
  continuous_finset_prod Finset.univ fun i _ => (continuous_apply i).pow _

theorem pilotGlobalMonomial_abs_le_one x (hx : 𝗌) : |pilotGlobalMonomial γ x| ≤ 1 := by
  unfold pilotGlobalMonomial
  rw [Finset.abs_prod]
  simp
  have hcoord i : |x i| ≤ 1 := by
    rw [abs_of_nonneg (hx i).1]
    exact (hx i).2
  calc
    _ ≤ ∏ _i : Fin d, 1 ^ (γ _i).val :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
         fun i _ => 𝗂 (hcoord i) _
    𝚘₂ := 𝖢₄

end

𝗇 𝔄 PilotBasisIndex q d ℓ
𝗇 𝔅 Covariate d → Fin q
𝗇 𝔈 cell z.1 = a.1.1
/-- A fixed global coordinate: a cell indicator times a monomial, optionally
multiplied by the observed response. Local anchored features are linear
combinations of this finite basis. -/
def pilotBasisFeature (cell : 𝔅)
    (a : 𝔄) (z : Observation d) : ℝ :=
  if 𝔈 then pilotGlobalMonomial a.1.2 z.1 * if a.2 then z.2 else 1 else 0

𝗇 𝔇 pilotBasisFeature cell a
section

variable (cell : 𝔅)

theorem pilotBasisFeature_measurable (hc : Measurable cell) (a : 𝔄) :
    Measurable 𝔇 := by
  apply Measurable.ite
  · exact measurableSet_eq_fun (hc.comp measurable_fst) measurable_const
  · exact ((pilotGlobalMonomial_continuous a.1.2).measurable.comp measurable_fst).mul
      $ by cases a.2 <;> first | exact measurable_const | exact measurable_snd
  · exact measurable_const

theorem pilotBasisFeature_abs_bound (a : 𝔄) z (hz : z.1 ∈ unitCube d) :
    |𝔇 z| ≤
      (Prod.fst ⁻¹' {x | cell x = a.1.1}).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  have hmono := pilotGlobalMonomial_abs_le_one a.1.2 z.1 hz
  by_cases h : 𝔈
  · rw [pilotBasisFeature, if_pos h, abs_mul]
    simp only [mem_preimage, mem_setOf_eq, h, indicator_of_mem]
    cases a.2
    · simpa using hmono.trans $ le_add_of_nonneg_right $ abs_nonneg z.2
    · exact (mul_le_mul_of_nonneg_right hmono $ abs_nonneg z.2 ).trans 𝖡₄
  · simp [pilotBasisFeature, h]

end

/-- The actual covariate marginal proves cube membership for observations. -/
theorem observationLaw_cube_ae C
    θ (hθ : 𝙟) :
    ∀ᵐ z ∂observationLaw θ, z.1 ∈ unitCube d :=
  (observationLaw_fst_measurePreserving C θ hθ).quasiMeasurePreserving.ae
    $ designLaw_cube_ae θ

/-- Every global pilot coordinate is genuinely L² under the original model. -/
theorem pilotBasisFeature_memLp_two C
    (θ : RegressionParameter d) (hθ : 𝙟)
    cell (hc : Measurable cell) (a : 𝔄) :
    MemLp 𝔇 2 $ observationLaw θ := by
  let := 𝙱
  have hy : MemLp (fun z => |z.2|) 2 $ observationLaw θ := by
    simpa only [Real.norm_eq_abs] using (observationLaw_response_memLp_two C θ hθ).norm
  have hbase :=
    (memLp_const 𝙠).add hy
  apply hbase.mono' (pilotBasisFeature_measurable cell hc a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae C θ hθ] with z hz
  apply (pilotBasisFeature_abs_bound cell a z hz).trans
  by_cases h : 𝔈 <;> simp [h] <;> positivity

/-- Coordinate indexing compatible with the paper's finite-dimensional
polynomial lift; this is an exact reindexing of the global basis. -/
def pilotRawVector (cell : 𝔅) (z : Observation d) :
    Fin (Fintype.card 𝔄) → ℝ :=
  fun a => pilotBasisFeature cell ((Fintype.equivFin 𝔄).symm a) z
