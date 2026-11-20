module

public import NearlyMinimax.HighUnionLikelihoodScore
public import NearlyMinimax.HighUnionInvariantMass


@[expose] public section

/-! Genuine Borel reset primitives for the canonical full-union source. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)]
    [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (R : HighUnionRowData d k D I E)
    {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)

/-- The actual density after appending the mark at the given window. -/
def highUnionSourceResetDensity (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (e : HighUnionMark E) (x : Covariate d) : ℝ :=
  highUnionSourceDensity C R (historyMarkedAppend
    (highNeighbors d k)
    (highNeighbors_symm d k) j (h,e)) x

theorem highUnionSourceResetDensity_inl (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E) (i : I) (e : E i) (x : Covariate d) :
    highUnionSourceResetDensity C R j h (Sum.inl ⟨i, e⟩) x =
      if x ∈ highTorusPatch d k j then
        R.rowSlope j i e x * highUnionSourceDensity C R h x + R.rowIntercept i e
      else highUnionSourceDensity C R h x := by
  unfold highUnionSourceResetDensity highUnionSourceDensity
  rw [highUnionSourceState_append]
  rfl

/-- The actual reset coefficient vector at the selected window. -/
def highUnionSourceResetCoefficient (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (e : HighUnionMark E) : HighFrameIndex d D → ℝ :=
  highUnionResponseReset R e ((highUnionSourceState C R h).2 j)

include G in
theorem highUnionSourceDensity_coarse_interval
    (h : HighUnionHistory d k E)
    (x : Covariate d) : C.densityLower ≤ highUnionSourceDensity C R h x ∧
      highUnionSourceDensity C R h x ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_interval C R G h x
  have hM : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  constructor <;> linarith [hb.1,hb.2,one_div_pos.mpr hM]

include G in
theorem highUnionSourceResetDensity_measurable (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E) :
    Measurable (Function.uncurry (highUnionSourceResetDensity C R j h)) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  have ha : Measurable (fun ex : HighUnionMark E × Covariate d =>
      historyMarkedAppend (highNeighbors d k)
        (highNeighbors_symm d k) j (h,ex.1)) :=
    (historyMarkedAppend_measurable (E := HighUnionMark E)
    (highNeighbors d k)
    (highNeighbors_symm d k) j).comp
      (measurable_const.prodMk measurable_fst)
  exact (highUnionSourceDensity_joint_measurable C R G).comp (ha.prodMk measurable_snd)

include G in
theorem highUnionSourceResetDensity_abs_le (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (e : HighUnionMark E) (x : Covariate d) :
    |highUnionSourceResetDensity C R j h e x| ≤ C.densityUpper := by
  have hb := highUnionSourceDensity_coarse_interval C R G
    (historyMarkedAppend (highNeighbors d k)
      (highNeighbors_symm d k) j (h,e)) x
  simp_all [highUnionSourceResetDensity, abs_of_nonneg (C.densityLower_pos.le.trans hb.1)]

include G in
theorem highUnionSource_reset_product_facts
    (j : HighWindowLabels d k) (h : HighUnionHistory d k E) (n : ℕ) (x : Fin n → Covariate d) :
    let Fobs := fun e => ∏ i, highUnionSourceResetDensity C R j h e (x i)
    Measurable Fobs ∧ ∀ e, ‖Fobs e‖ ≤ C.densityUpper ^ n := by
  let Fobs := fun e => ∏ i, highUnionSourceResetDensity C R j h e (x i)
  have hF : Measurable Fobs := Finset.measurable_fun_prod _ (fun i _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const))
  have hFb (e : HighUnionMark E) : ‖Fobs e‖ ≤ C.densityUpper^n := by
    simpa only [Real.norm_eq_abs,Fobs] using finite_density_product_abs_bound
      (fun i => highUnionSourceResetDensity C R j h e (x i)) C.densityUpper
      (fun i => highUnionSourceResetDensity_abs_le C R G j h e (x i))
  exact ⟨hF, hFb⟩

include G in
theorem highUnionSourceResetCoefficient_measurable (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (γ : HighFrameIndex d D) :
    Measurable (fun e => highUnionSourceResetCoefficient C R j h e γ) := by
  exact (measurable_const.sub (highUnionResponseTime_measurable R G.time_measurable)).mul
      measurable_const |>.add ((highUnionResponseTime_measurable R G.time_measurable).mul
        (highUnionResponseVector_measurable R G.vector_measurable γ))

/-- A bounded observable of the reset coefficients, weighted by the reset design. -/
def highUnionSourceResetObservable (j : HighWindowLabels d k) (h : HighUnionHistory d k E)
    {n : ℕ} (x : Fin n → Covariate d) (Φ : (HighFrameIndex d D → ℝ) → ℝ)
    (e : HighUnionMark E) : ℝ :=
  (∏ u, highUnionSourceResetDensity C R j h e (x u)) * Φ (highUnionSourceResetCoefficient C R j h e)

include G in
theorem highUnionSourceResetObservable_facts (hCfr : 0 < Cfr) (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E) {n : ℕ} (x : Fin n → Covariate d)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) (hΦ : Measurable Φ) (B : ℝ)
    (hb : ∀ v, (∑ β, |v β|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    Measurable (highUnionSourceResetObservable C R j h x Φ) ∧
      ∀ e, ‖highUnionSourceResetObservable C R j h x Φ e‖ ≤ C.densityUpper ^ n * B := by
  obtain ⟨hm, hh⟩ := highUnionSource_reset_product_facts C R G j h n x
  refine ⟨hm.mul (hΦ.comp (measurable_pi_iff.mpr
    (highUnionSourceResetCoefficient_measurable C R G j h))), fun e => ?_⟩
  rw [highUnionSourceResetObservable, norm_mul]
  apply mul_le_mul (hh e) _ (norm_nonneg _) (by positivity [C.one_lt_densityUpper])
  rw [Real.norm_eq_abs]
  exact hb _ (highUnionResponseReset_ball R Cfr hCfr G.vector_ball G.time_interval e _
    (highUnionSourceState_coefficient_ball C R G h j))

theorem highUnionSourceResetDensity_outside (j : HighWindowLabels d k)
    (h : HighUnionHistory d k E)
    (e : HighUnionMark E) (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceResetDensity C R j h e x = highUnionSourceDensity C R h x :=
  by apply highUnionSourceDensity_append_of_not_mem <;> assumption

end NearlyMinimax
