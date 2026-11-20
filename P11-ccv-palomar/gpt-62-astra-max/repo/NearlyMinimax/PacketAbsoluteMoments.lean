module

public import NearlyMinimax.HighCenteredMark

@[expose] public section

/-! Intercept bounds and actual absolute-packet slope centering, for source
reference-law mean-one balancing. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

theorem finite_even_odd_sum_zero {I : Type*} [Fintype I]
    {e : Equiv.Perm I} {w f : I → ℝ}
    (hw : ∀ i, w (e i) = w i) (hf : ∀ i, f (e i) = -f i) :
    (∑ i, w i * f i) = 0 := by
  have he : (∑ i, w i * f i) = -(∑ i, w i * f i) := by
    calc
      _ = _ := by
        symm
        apply Fintype.sum_equiv e
        intro i
        rfl
      _ = _ := by simp_rw [hw, hf, mul_neg]
      _ = _ := Finset.sum_neg_distrib _
  linarith

section
variable (ι : Type*) (a b : ℝ) (m r D : ℕ)

def densityMarkReflection : Equiv.Perm (HighDensityMarkIndex m r D) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight (fun _ : Fin r => Fin.revPerm))

def packetMarkReflection (q : ℕ) : Equiv.Perm (HighPacketMarkIndex ι m r D q) :=
  Equiv.prodCongr (densityMarkReflection m r D) (Equiv.refl _)

theorem densityPacketWeight_abs_reflection
    (h : HighDensityMarkIndex m r D) :
    |densityPacketWeight a b m r D (densityMarkReflection m r D h)| =
      |densityPacketWeight a b m r D h| := by
  change |densityPacketPrefactor a b r * exteriorWeight a b h.1 *
      (∏ l, densityDerivativeWeight (h.2 l).rev)| = _
  simp only [densityPacketWeight, abs_mul, Finset.abs_prod]
  have hp : (∏ l, |densityDerivativeWeight (h.2 l).rev|) =
      ∏ l, |densityDerivativeWeight (h.2 l)| := by
    apply Finset.prod_congr rfl
    intro l hl
    apply lobattoDerivativeWeight_abs_reflection
  rw [hp]

end

section Packet
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

section
variable (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) (B : Z → Fin r → ℝ) (ζ : Z)

def highPacketIntercept
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  (densityPacketAtom a b m r D e.2.1).1

def highPacketSlope {m r D q : ℕ} (B : Z → Fin r → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityMargin a b (highPacketIntercept a b m r D q e) / ((r : ℝ) * b) *
    ∑ l, (densityPacketAtom a b m r D e.2.1).2 l * B e.1 l

theorem highPacketIntercept_measurable :
    Measurable (highPacketIntercept (Z := Z) (ι := ι) a b m r D q) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun _ : Z => (densityPacketAtom a b m r D h.1).1)
  exact measurable_const

theorem highPacketSlope_measurable
    (hB : ∀ l, Measurable (fun ζ => B ζ l)) :
    Measurable (highPacketSlope (ι := ι) a b (m := m) (r := r) (D := D) (q := q) B) := by
  apply measurable_from_prod_countable_left
  intro h
  unfold highPacketSlope highPacketIntercept
  dsimp
  fun_prop

theorem highPacketSlope_bound {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {m r D q : ℕ} (hr : 1 ≤ r) (B : Z → Fin r → ℝ) (hB : ∀ ζ l, |B ζ l| ≤ 1)
    (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketSlope a b B e| ≤ (b - a) / (4 * b) :=
  localDensityReset_slope_bound a b ha hab r hr
    (densityPacketAtom a b m r D e.2.1).1
    (densityPacketAtom_mem a b hab.le e.2.1).1
    (densityPacketAtom a b m r D e.2.1).2
    (densityPacketAtom_mem a b hab.le e.2.1).2
    (B := (fun _ l => B e.1 l)) () (hB e.1)

theorem highPacketMarkWeight_abs_reflection (h : HighPacketMarkIndex ι m r D q) :
    |highPacketMarkWeight a b m r D q C A (ζ, packetMarkReflection ι m r D q h)| =
      |highPacketMarkWeight a b m r D q C A (ζ, h)| := by
  change |densityPacketWeight a b m r D (densityMarkReflection m r D h.1) *
      highResponseMarkWeight C (A ζ) h.2| = _
  rw [abs_mul, densityPacketWeight_abs_reflection, highPacketMarkWeight, responseTensorWeight, abs_mul]

theorem highPacketSlope_reflection (h : HighPacketMarkIndex ι m r D q) :
    highPacketSlope a b B (ζ, packetMarkReflection ι m r D q h) =
      -highPacketSlope a b B (ζ, h) := by
  change _ *
      (∑ l, lobattoNode (h.1.2 l).rev * B ζ l) = _
  simp_rw [lobattoNode_reflection (n := (derivativeOrder D)) (by unfold derivativeOrder; omega)]
  simp
  rfl

theorem highPacketSlope_absolute_finite_sum_zero :
    (∑ h : HighPacketMarkIndex ι m r D q,
      |highPacketMarkWeight a b m r D q C A (ζ, h)| * highPacketSlope a b B (ζ, h)) = 0 :=
  finite_even_odd_sum_zero
    (highPacketMarkWeight_abs_reflection a b m r D q C A ζ)
    (highPacketSlope_reflection a b m r D q B ζ)

end

theorem absoluteMarkLaw_integral {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {w : E → ℝ} (hmw : Measurable w)
    (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, F e ∂absoluteMarkLaw μ w) = (∫ e, |w e| * F e ∂μ) / signedMarkMass μ w := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun e => (ENNReal.ofReal (|w e| / signedMarkMass μ w)).toReal • F e) =
      (fun e => (|w e| * F e) / signedMarkMass μ w) := by
    funext e
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
    exact div_mul_eq_mul_div _ _ _
  rw [he, integral_div]

theorem absoluteMarkLaw_fiber_zero {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {σ : Measure Z} [IsFiniteMeasure σ] {w S : Z × I → ℝ}
    (hm : Measurable w) (hw : Integrable w (σ.prod Measure.count)) (hpos : 0 < signedMarkMass (σ.prod Measure.count) w)
    (hs : Measurable S) {K : ℝ} (hb : ∀ e, ‖S e‖ ≤ K) (hz : ∀ z, (∑ i, |w (z,i)| * S (z,i)) = 0) :
    (∫ e, S e ∂absoluteMarkLaw (σ.prod Measure.count) w) = 0 := by
  rw [absoluteMarkLaw_integral hm hpos, integral_prod _ (hw.abs.mul_bdd hs.aestronglyMeasurable (Filter.Eventually.of_forall hb))]
  simp [hz]

variable {σ : Measure Z} [IsFiniteMeasure σ] {a b : ℝ} (ha : 0 < a) (hab : a < b) {m r D q : ℕ}
    (hr : 1 ≤ r) {C : ℝ} {A : Z → ι → ι → ℝ} (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
include hA ha hab hcost hpos hr

theorem highPacketSlope_integrable
    {B : Z → Fin r → ℝ} (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    Integrable (highPacketSlope a b B) (highPacketAbsoluteLaw σ a b m r D q C A) := by
  letI := highPacketAbsoluteLaw_probability hA hcost hpos
  apply (integrable_const ((b - a) / (4 * b))).mono'
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun e => by
    exact highPacketSlope_bound ha hab hr B hB e)

/-- Absolute derivative-rule reflection kills the actual affine slope under
the genuine normalized absolute packet law. No desired slope mean is supplied. -/
theorem highPacketAbsoluteLaw_slope_integral_zero
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable (fun ζ => B ζ l))
    (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    (∫ e, highPacketSlope a b B e ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  absoluteMarkLaw_fiber_zero (w := highPacketMarkWeight a b m r D q C A)
    (tensorWeight_measurable _ q C hA) (tensorWeight_integrable _ q C hA hcost) hpos
    (highPacketSlope_measurable a b m r D q B hmB) (highPacketSlope_bound ha hab hr B hB)
    (highPacketSlope_absolute_finite_sum_zero a b m r D q C A B)

end Packet
end NearlyMinimax
