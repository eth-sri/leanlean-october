module

public import NearlyMinimax.PilotFeatures
public import NearlyMinimax.AnchoredExpansion
public import NearlyMinimax.PairWindowGeometry

@[expose] public section

/-! The manuscript's actual raw current-cell pilot coordinates and their
original-law second-moment budget, allowing unbounded responses. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable (d j ℓ : ℕ)

abbrev LocalPilotIndex :=
  Sum (AnchoredIndex d ℓ × AnchoredIndex d ℓ) (Sum (AnchoredIndex d ℓ) (AnchoredIndex d ℓ))

def dyadicPilotScale : ℝ := ((2 : ℝ) ^ j) ^ d

theorem dyadicPilotScale_pos : 0 < dyadicPilotScale d j := by
  unfold dyadicPilotScale
  positivity

end

section
variable {d ℓ : ℕ} (j : ℕ) (x : Covariate d) (a : LocalPilotIndex d ℓ)

def dyadicPilotCell : Set (Covariate d) :=
  {z | dyadicGridLabel j z =
    dyadicGridLabel j x}

theorem dyadicPilotCell_measurable :
    MeasurableSet (dyadicPilotCell j x) :=
  measurableSet_eq_fun (regular_grid_cell_measurable _ _) measurable_const

theorem dyadicAnchoredFeature_measurable
    (γ : AnchoredIndex d ℓ) : Measurable (fun z => dyadicAnchoredFeature j x z γ) := by
  exact ((anchoredMonomial_continuous γ).comp (by fun_prop)).measurable

/-- Current-cell normalization bounds the exact anchored monomials, including
the assigned right cube boundary. -/
theorem dyadicAnchoredFeature_abs_le_one {j : ℕ} {x z : Covariate d}
    (hx : x ∈ unitCube d) (hz : z ∈ unitCube d) (hc : z ∈ dyadicPilotCell j x)
    (γ : AnchoredIndex d ℓ) : |dyadicAnchoredFeature j x z γ| ≤ 1 := by
  apply anchoredMonomial_abs_le_one
  intro i
  have hr := regular_grid_same_cell_radius (by positivity) hz hx hc i
  have hk : 0 < (2 : ℝ) ^ j := by positivity
  have he : (((2 : ℕ) ^ j : ℕ) : ℝ) = (2 : ℝ) ^ j := by simp
  rw [he] at hr
  rw [abs_mul, abs_of_pos hk]
  exact (mul_le_mul_of_nonneg_left hr hk.le).trans_eq (by field_simp)

def dyadicPilotScalar (z : Observation d) : ℝ :=
  match a with
  | Sum.inl (γ, δ) => dyadicAnchoredFeature j x z.1 γ * dyadicAnchoredFeature j x z.1 δ
  | Sum.inr (Sum.inl γ) => z.2 * dyadicAnchoredFeature j x z.1 γ
  | Sum.inr (Sum.inr γ) => dyadicAnchoredFeature j x z.1 γ

/-- The actual raw coordinates: normalized Gram, response vector, and
constant-response vector. Their mean is taken under the original law. -/
def dyadicPilotFeature (z : Observation d) : ℝ :=
  dyadicPilotScale d j * (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
    (dyadicPilotScalar j x a) z

theorem dyadicPilotScalar_measurable : Measurable (dyadicPilotScalar j x a) := by
  cases a with
  | inl a =>
    exact ((dyadicAnchoredFeature_measurable j x a.1).comp measurable_fst).mul
      ((dyadicAnchoredFeature_measurable j x a.2).comp measurable_fst)
  | inr a =>
    cases a with
    | inl γ =>
      exact measurable_snd.mul
        ((dyadicAnchoredFeature_measurable j x γ).comp measurable_fst)
    | inr γ => exact (dyadicAnchoredFeature_measurable j x γ).comp measurable_fst

theorem dyadicPilotFeature_measurable : Measurable (dyadicPilotFeature j x a) :=
  measurable_const.mul ((dyadicPilotScalar_measurable j x a).indicator
    (measurable_fst (dyadicPilotCell_measurable j x)))

end

section
variable {d ℓ : ℕ} {C : ModelConstants d} {θ : RegressionParameter d} (hθ : Admissible C θ) (j : ℕ)
    {x : Covariate d} (hx : x ∈ unitCube d) (a : LocalPilotIndex d ℓ)

theorem dyadicPilotScalar_abs_bound {j : ℕ} {x : Covariate d}
    (a : LocalPilotIndex d ℓ) {z : Observation d} (hx : x ∈ unitCube d)
    (hz : z.1 ∈ unitCube d) (hc : z.1 ∈ dyadicPilotCell j x) :
    |dyadicPilotScalar j x a z| ≤ 1 + |z.2| := by
  have hb := dyadicAnchoredFeature_abs_le_one (ℓ := ℓ) hx hz hc
  cases a with
  | inl a =>
    change |dyadicAnchoredFeature j x z.1 a.1 * dyadicAnchoredFeature j x z.1 a.2| ≤ _
    rw [abs_mul]
    apply (mul_le_mul (hb a.1) (hb a.2) (abs_nonneg _) (by norm_num)).trans
    simp
  | inr a =>
    cases a with
    | inl γ =>
      change |z.2 * dyadicAnchoredFeature j x z.1 γ| ≤ _
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hb γ) (abs_nonneg z.2)).trans (by linarith)
    | inr γ => exact (hb γ).trans (by bound)

/-- Exact geometric support and the paper's raw feature envelope. -/
theorem dyadicPilotFeature_abs_bound {z : Observation d} (hx : x ∈ unitCube d)
    (hz : z.1 ∈ unitCube d) :
    |dyadicPilotFeature j x a z| ≤ dyadicPilotScale d j *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator
        (fun z : Observation d => 1 + |z.2|) z := by
  by_cases hc : z.1 ∈ dyadicPilotCell j x
  · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
    simp only [dyadicPilotFeature, indicator_of_mem hc', abs_mul,
      abs_of_pos (dyadicPilotScale_pos d j)]
    exact mul_le_mul_of_nonneg_left (dyadicPilotScalar_abs_bound a hx hz hc)
      (dyadicPilotScale_pos d j).le
  · simp [dyadicPilotFeature, hc]

include hθ hx in
theorem dyadicPilotFeature_memLp_two :
    MemLp (dyadicPilotFeature j x a) 2 (observationLaw θ) := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    exact (observationLaw_response_memLp_two hθ).norm
  have hd : MemLp (fun z : Observation d => dyadicPilotScale d j * (1 + |z.2|))
      2 (observationLaw θ) := ((memLp_const (1 : ℝ)).add hy).const_mul _
  apply hd.mono' (dyadicPilotFeature_measurable j x a).aestronglyMeasurable
  filter_upwards [observationLaw_cube_ae hθ] with z hz
  rw [Real.norm_eq_abs]
  apply (dyadicPilotFeature_abs_bound j a hx hz).trans
  by_cases hc : z.1 ∈ dyadicPilotCell j x <;> simp [hc]
  exact mul_nonneg (dyadicPilotScale_pos d j).le (by positivity)

def dyadicPilotMomentConstant (C : ModelConstants d) : ℝ :=
  (2 * (1 + responseSecondBound C)) * C.densityUpper

theorem dyadicPilotMomentConstant_pos (C : ModelConstants d) :
    0 < dyadicPilotMomentConstant C := by
  have hden := C.one_lt_densityUpper
  have hresp := responseSecondBound_pos C
  unfold dyadicPilotMomentConstant
  positivity

include hθ hx in
/-- The order-independent raw coordinate budget `C_g K_j` follows from
the actual cell volume, design density cap, and conditional error moment. -/
theorem dyadicPilotFeature_second_le :
    (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
  let := observationLaw_isProbability C θ hθ
  have hy : MemLp (fun z : Observation d => |z.2|) 2 (observationLaw θ) := by
    exact (observationLaw_response_memLp_two hθ).norm
  have hd : Integrable (fun z : Observation d => dyadicPilotScale d j ^ 2 *
      (Prod.fst ⁻¹' dyadicPilotCell j x).indicator (fun z : Observation d => (1 + |z.2|) ^ 2) z)
      (observationLaw θ) :=
    (((memLp_const (1 : ℝ)).add hy).integrable_sq.indicator
      (measurable_fst (dyadicPilotCell_measurable j x))).const_mul _
  have hfirst : (∫ z, dyadicPilotFeature j x a z ^ 2 ∂observationLaw θ) ≤
      dyadicPilotScale d j ^ 2 *
        ((2 * (1 + responseSecondBound C)) * (designLaw θ).real (dyadicPilotCell j x)) := by
    apply (integral_mono_ae (dyadicPilotFeature_memLp_two hθ j hx a).integrable_sq hd ?_).trans
    · rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (observationLaw_localized_response_energy_le hθ
        (dyadicPilotCell_measurable j x)) (sq_nonneg _)
    · filter_upwards [observationLaw_cube_ae hθ] with z hz
      have hb := dyadicPilotFeature_abs_bound j a hx hz
      by_cases hc : z.1 ∈ dyadicPilotCell j x
      · have hc' : z ∈ Prod.fst ⁻¹' dyadicPilotCell j x := hc
        simp [indicator_of_mem hc'] at hb ⊢
        simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hb 2
      · simp [dyadicPilotFeature, hc]
  have hmass : (designLaw θ).real (dyadicPilotCell j x) ≤ C.densityUpper / dyadicPilotScale d j := by
    convert regularGridProbability_cap hθ (by positivity)
      (dyadicGridLabel j x) using 1 <;>
      simp only [dyadicPilotCell, regularGridProbability, Set.preimage, Set.mem_singleton_iff,
        dyadicPilotScale, Nat.cast_pow, Nat.cast_ofNat]
  apply hfirst.trans
  let pilotScale := dyadicPilotScale d j ^ 2 * (2 * (1 + responseSecondBound C))
  have hfactor : 0 ≤ pilotScale := by
    have := responseSecondBound_pos C
    positivity
  have hm := mul_le_mul_of_nonneg_left hmass hfactor
  have heq : pilotScale *
      (C.densityUpper / dyadicPilotScale d j) =
      dyadicPilotMomentConstant C * dyadicPilotScale d j := by
    unfold dyadicPilotMomentConstant
    grind
  linarith

end

def dyadicPilotPopulation {d ℓ : ℕ} (θ : RegressionParameter d) (j : ℕ) (x : Covariate d) :
    LocalPilotIndex d ℓ → ℝ := fun a => ∫ z, dyadicPilotFeature j x a z ∂observationLaw θ

end NearlyMinimax
