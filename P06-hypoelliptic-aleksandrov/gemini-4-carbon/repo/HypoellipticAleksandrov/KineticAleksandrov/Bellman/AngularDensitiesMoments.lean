module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
import Mathlib.Analysis.Calculus.Deriv.Support
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativeFunctionals
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.MeasureDerivativePrimitiveWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set

/-- Absolute continuity on every compact interval gives global continuity of the
representative. -/
theorem bellman_locallyAC_continuous {h : ℝ → ℝ}
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b) : Continuous h := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hle : y - 1 ≤ y + 1 := by linarith
  have hc : ContinuousOn h (Icc (y - 1) (y + 1)) := by
    simpa only [uIcc_of_le hle] using (hh (y - 1) (y + 1) hle).continuousOn
  exact hc.continuousAt (Icc_mem_nhds (by linarith) (by linarith))

/-- A continuous angular representative that is nonnegative almost everywhere is nonnegative. -/
theorem bellman_continuous_nonneg_of_ae {h : ℝ → ℝ} (hh : Continuous h)
    (hn : ∀ᵐ y ∂volume, 0 ≤ h y) : ∀ y : ℝ, 0 ≤ h y := by
  have hc : IsClosed {y : ℝ | 0 ≤ h y} := isClosed_le continuous_const hh
  have he : {y : ℝ | 0 ≤ h y} =ᵐ[volume] univ := by
    filter_upwards [hn] with y hy
    change (0 ≤ h y) = True
    exact propext ⟨fun _ => trivial, fun _ => hy⟩
  intro y
  have hy : y ∈ {y : ℝ | 0 ≤ h y} := by rw [((hc.ae_eq_univ_iff_eq (μ := volume)).mp he)]; trivial
  exact hy

/-- Almost everywhere ellipticity gives nonnegativity of the continuous angular density. -/
theorem bellmanAngularDensity_nonneg {f h : ℝ → ℝ}
    (hh : ∀ a b : ℝ, a ≤ b → AbsolutelyContinuousOnInterval h a b)
    (hf : ∀ᵐ y ∂volume, 0 ≤ f y) (hfh : ∀ᵐ y ∂volume, f y ≤ h y) :
    ∀ y : ℝ, 0 ≤ h y := by
  apply bellman_continuous_nonneg_of_ae (bellman_locallyAC_continuous hh)
  filter_upwards [hf, hfh] with y hy hfy
  exact hy.trans hfy


/-- The oriented Lebesgue primitive of a locally integrable function is locally absolutely
continuous. -/
theorem bellman_lebesguePrimitive_locallyAC (g : ℝ → ℝ) (hg : LocallyIntegrable g volume)
    (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ z in 0..x, g z) a b := by
  let l := min 0 a
  let u := max 0 b
  have hlu := (min_le_left 0 a).trans (le_max_left 0 b)
  have hi : IntervalIntegrable g volume l u :=
    (intervalIntegrable_iff').2 (hg.integrableOn_isCompact isCompact_uIcc)
  have hc := hi.absolutelyContinuousOnInterval_intervalIntegral
    (show 0 ∈ uIcc l u by
      rw [uIcc_of_le hlu]; exact ⟨min_le_left _ _, le_max_left _ _⟩)
  apply hc.mono
  rw [uIcc_of_le hab, uIcc_of_le hlu]
  exact Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)

/-- The oriented Lebesgue primitive is globally continuous. -/
theorem bellman_lebesguePrimitive_continuous (g : ℝ → ℝ)
    (hg : LocallyIntegrable g volume) : Continuous (fun x => ∫ z in 0..x, g z) :=
  bellman_locallyAC_continuous (bellman_lebesguePrimitive_locallyAC g hg)




/-- A Radon measure has a locally integrable Radon–Nikodym density against any dominating
measure. -/
theorem bellman_rnDeriv_locallyIntegrable (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact Measure.integrableOn_toReal_rnDeriv hK.measure_lt_top.ne

/-- Multiplying a locally integrable function by the density transfers local integrability. -/
theorem bellman_rnDeriv_mul_locallyIntegrable (μ ν : Measure ℝ)
    [SigmaFinite μ] [SigmaFinite ν] (hμν : μ ≪ ν) (f : ℝ → ℝ)
    (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal * f x) ν := by
  rw [locallyIntegrable_iff]
  intro K hK
  have hi :=
    (integrable_indicator_iff hK.measurableSet).2 (hf.integrableOn_isCompact hK)
  have ht := (integrable_toReal_rnDeriv_mul_iff hμν).2 hi
  rw [← integrable_indicator_iff hK.measurableSet]
  convert ht using 1
  funext x
  by_cases hx : x ∈ K <;> simp [hx]

/-- Equality on smooth tests gives equality of the two densities against a common dominator. -/
theorem bellman_test_pairing_rnDeriv_eq (μ ν : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] [SigmaFinite ν] (hμν : μ ≪ ν)
    (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hvolν : volume ≪ ν)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    ∀ᵐ x ∂ν, (μ.rnDeriv ν x).toReal = (volume.rnDeriv ν x).toReal * f x := by
  apply ae_eq_of_integral_contDiff_smul_eq
    (bellman_rnDeriv_locallyIntegrable μ ν)
    (bellman_rnDeriv_mul_locallyIntegrable volume ν hvolν f hf)
  intro φ hφ hc
  let ψ : BellmanRealTest := ⟨φ, hφ, hc, by simp⟩
  have he := ht ψ
  change (∫ x, φ x ∂μ) = ∫ x, φ x * f x at he
  simp
  calc
    (∫ x, φ x * (μ.rnDeriv ν x).toReal ∂ν) = ∫ x, φ x ∂μ := by
      rw [show (fun x => φ x * (μ.rnDeriv ν x).toReal) =
        (fun x => (μ.rnDeriv ν x).toReal * φ x) by funext x; ring]
      exact integral_toReal_rnDeriv_mul hμν
    _ = ∫ x, φ x * f x := he
    _ = ∫ x, φ x * ((volume.rnDeriv ν x).toReal * f x) ∂ν := by
      rw [show (fun x => φ x * ((volume.rnDeriv ν x).toReal * f x)) =
        (fun x => (volume.rnDeriv ν x).toReal * (φ x * f x)) by funext x; ring]
      exact (integral_toReal_rnDeriv_mul hvolν).symm

/-- A positive Radon measure represented on smooth tests has the asserted Lebesgue density. -/
theorem bellman_measure_eq_withDensity_of_test_pairing (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (f : ℝ → ℝ) (hm : Measurable f)
    (hf : LocallyIntegrable f volume)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let ν := μ + volume
  have hμν : μ ≪ ν := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hvolν : volume ≪ ν := (Measure.le_add_left le_rfl).absolutelyContinuous
  have hd : μ.rnDeriv ν =ᵐ[ν]
      (fun x => volume.rnDeriv ν x * ENNReal.ofReal (f x)) := by
    filter_upwards [(bellman_test_pairing_rnDeriv_eq μ ν hμν f hf hvolν ht), Measure.rnDeriv_lt_top μ ν, Measure.rnDeriv_lt_top volume ν]
      with x hx hμ hvol
    rw [← ENNReal.ofReal_toReal hμ.ne, hx, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hvol.ne]
  calc
    μ = ν.withDensity (μ.rnDeriv ν) := (Measure.withDensity_rnDeriv_eq μ ν hμν).symm
    _ = ν.withDensity (fun x => volume.rnDeriv ν x * ENNReal.ofReal (f x)) :=
      withDensity_congr_ae hd
    _ = (ν.withDensity (volume.rnDeriv ν)).withDensity
        (fun x => ENNReal.ofReal (f x)) :=
      withDensity_mul ν (Measure.measurable_rnDeriv volume ν) (hm.ennreal_ofReal)
    _ = volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
      rw [Measure.withDensity_rnDeriv_eq volume ν hvolν]

/-- A density representing a positive measure on smooth tests is nonnegative almost
everywhere. -/
theorem bellman_nonneg_of_test_pairing (μ : Measure ℝ)
    [IsFiniteMeasureOnCompacts μ] (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (ht : ∀ φ : BellmanRealTest, (∫ x, φ x ∂μ) = ∫ x, φ x * f x) :
    ∀ᵐ x ∂volume, 0 ≤ f x := by
  let ν := μ + volume
  have hμν : μ ≪ ν := (Measure.le_add_right le_rfl).absolutelyContinuous
  have hvolν : volume ≪ ν := (Measure.le_add_left le_rfl).absolutelyContinuous
  filter_upwards [(hvolν.ae_le (bellman_test_pairing_rnDeriv_eq μ ν hμν f hf hvolν ht)), (hvolν.ae_le (Measure.rnDeriv_lt_top volume ν)), Measure.rnDeriv_pos hvolν] with x hx ht hxpos
  have hp : 0 ≤ (volume.rnDeriv ν x).toReal * f x := by
    rw [← hx]
    exact ENNReal.toReal_nonneg
  exact nonneg_of_mul_nonneg_right hp (ENNReal.toReal_pos hxpos.ne' ht.ne)




/-- A measure with flux minus weighted-measure derivative has an actual explicit density. -/
theorem bellman_measure_density_of_flux (F H : Measure ℝ)
    [IsFiniteMeasureOnCompacts F] [IsFiniteMeasureOnCompacts H]
    (g J : ℝ → ℝ) (hg : Continuous g) (hJ : LocallyIntegrable J volume) (a : ℝ)
    (hw : ∀ φ : BellmanRealTest, (∫ x, deriv φ x ∂H) =
      a * (∫ x, g x * φ x ∂F) - (∫ x, φ x * J x)) :
    ∃ c : ℝ, H = volume.withDensity (fun x => ENNReal.ofReal
      (c + (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) ∧
      ∀ᵐ x ∂volume, 0 ≤ c + (∫ z in 0..x, J z) -
        a * bellmanMeasurePrimitive F g 0 x    := by
  have bellman_lebesguePrimitive_weak (φ : ℝ → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcφ : HasCompactSupport φ) :
      (∫ x, (∫ z in 0..x, J z) * deriv φ x) = -∫ x, J x * φ x := by
    have bellman_lebesguePrimitive_sub (r : ℝ) (x : ℝ) :
        (∫ z in 0..x, J z) - (∫ z in 0..r, J z) = ∫ z in r..x, J z := by
      have hi (a b : ℝ) : IntervalIntegrable J volume a b :=
        (intervalIntegrable_iff').2 (hJ.integrableOn_isCompact isCompact_uIcc)
      have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 r) (hi r x)
      linarith
    by_cases hn : (tsupport φ).Nonempty
    · obtain ⟨r₀, _, hmin⟩ := hcφ.exists_isMinOn hn continuousOn_id
      obtain ⟨R₀, _, hmax⟩ := hcφ.exists_isMaxOn hn continuousOn_id
      let r := r₀ - 1
      let R := R₀ + 1
      have hs : tsupport φ ⊆ Ioo r R := by
        intro x hx
        have hl : r₀ ≤ x := hmin hx
        have hr : x ≤ R₀ := hmax hx
        dsimp [r, R]
        constructor <;> linarith
      have hdr := tsupport_deriv_subset.trans hs
      have hφd := (contDiff_infty_iff_deriv.mp hφ).2
      have hlhs : (∫ x, (fun x => ∫ z in 0..x, J z) x * deriv φ x) =
          ∫ x in Icc r R, (fun x => ∫ z in 0..x, J z) x * deriv φ x := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport
          (fun hd => hx ⟨(hdr hd).1.le, (hdr hd).2.le⟩), mul_zero]
      have hrhs : (∫ x, J x * φ x ) = ∫ x in Icc r R, J x * φ x  := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [image_eq_zero_of_notMem_tsupport
          (fun hd => hx ⟨(hs hd).1.le, (hs hd).2.le⟩), mul_zero]
      have he : (∫ x in Icc r R, (fun x => ∫ z in 0..x, J z) x * deriv φ x) =
          ∫ x in Icc r R, (fun x => ∫ z in r..x, J z) x * deriv φ x := by
        have hi : IntegrableOn (fun x => (fun x => ∫ z in 0..x, J z) x * deriv φ x)
            (Icc r R) volume :=
          (((bellman_lebesguePrimitive_continuous J hJ).locallyIntegrable).integrableOn_isCompact
            isCompact_Icc).mul_continuousOn hφd.continuous.continuousOn isCompact_Icc
        have hc : IntegrableOn (fun x => (fun x => ∫ z in 0..x, J z) r * deriv φ x)
            (Icc r R) volume :=
          (hφd.continuous.continuousOn.integrableOn_Icc).const_mul _
        have hfun : (fun x => (fun x => ∫ z in r..x, J z) x * deriv φ x) =
            (fun x => (fun x => ∫ z in 0..x, J z) x * deriv φ x -
              (fun x => ∫ z in 0..x, J z) r * deriv φ x) := by
          funext x
          have hp := bellman_lebesguePrimitive_sub r x
          change (fun x => ∫ z in 0..x, J z) x - (fun x => ∫ z in 0..x, J z) r =
            (fun x => ∫ z in r..x, J z) x at hp
          rw [← hp]
          ring
        have hle : r ≤ R := by
          obtain ⟨x, hx⟩ := hn
          exact (hs hx).1.le.trans (hs hx).2.le
        have hdInt : (∫ x in Icc r R, deriv φ x) = 0 := by
          rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
            intervalIntegral.integral_deriv_of_contDiffOn_Icc
              (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).contDiffOn hle,
            (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl r) (hs h).1)), (image_eq_zero_of_notMem_tsupport (fun h => (lt_irrefl R) (hs h).2)), sub_self]
        rw [hfun, integral_sub hi hc, integral_const_mul, hdInt, mul_zero, sub_zero]
      rw [hlhs, hrhs, he]
      exact PDE.intervalPrimitive_scalar_weak_identity_Icc
        (hJ.integrableOn_isCompact isCompact_Icc)
        (hφ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))) hs
    · have hz : φ = 0 := by
        funext x
        exact image_eq_zero_of_notMem_tsupport (fun hx => hn ⟨x, hx⟩)
      rw [hz, deriv_zero]
      simp
  have bellman_fluxMeasurePrimitive_weak (φ : BellmanRealTest) :
      (∫ x, φ x * J x) - a * (∫ x, g x * φ x ∂F) =
      -(∫ x, deriv φ x *
        ((∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) := by
    have h1 := bellman_lebesguePrimitive_weak φ φ.contDiff φ.hasCompactSupport
    have hd := (contDiff_infty_iff_deriv.mp φ.contDiff).2.continuous
    have hc := φ.hasCompactSupport.deriv
    have hi1 : Integrable (fun x => deriv φ x * (∫ z in 0..x, J z)) volume := by
      exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (bellman_lebesguePrimitive_continuous J hJ).locallyIntegrable hd hc
    have hi2 : Integrable (fun x => deriv φ x * bellmanMeasurePrimitive F g 0 x) volume := by
      exact LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
        (bellmanMeasurePrimitive_locallyIntegrable F g hg) hd hc
    rw [show (fun x => deriv φ x *
        ((∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x)) =
        (fun x => deriv φ x * (∫ z in 0..x, J z) -
          a * (deriv φ x * bellmanMeasurePrimitive F g 0 x)) by funext x; ring,
      integral_sub hi1 (hi2.const_mul a), integral_const_mul]
    have hs1 : (∫ x, deriv φ x * (∫ z in 0..x, J z)) = -∫ x, φ x * J x := by
      rw [show (fun x => deriv φ x * (∫ z in 0..x, J z)) =
        (fun x => (∫ z in 0..x, J z) * deriv φ x) by funext x; ring, h1]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => mul_comm _ _
    have hs2 : (∫ x, deriv φ x * bellmanMeasurePrimitive F g 0 x) =
        -∫ x, g x * φ x ∂F := by
      rw [show (fun x => deriv φ x * bellmanMeasurePrimitive F g 0 x) =
        (fun x => bellmanMeasurePrimitive F g 0 x * deriv φ x) by funext x; ring, (bellmanMeasurePrimitive_weak F g hg φ φ.contDiff φ.hasCompactSupport)]
    rw [hs1, hs2]
    ring
  have bellman_fluxMeasurePrimitive_locallyIntegrable :
      LocallyIntegrable
      (fun x => (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x) volume := by
    convert!
      (bellman_lebesguePrimitive_continuous J hJ).locallyIntegrable.sub
        ((bellmanMeasurePrimitive_locallyIntegrable F g hg).smul a) using 1
  let p := fun x => (∫ z in 0..x, J z) - a * bellmanMeasurePrimitive F g 0 x
  have hp :=
    bellman_fluxMeasurePrimitive_locallyIntegrable
  have h1 : LocallyIntegrable (fun _ => (1 : ℝ)) H :=
    continuous_const.locallyIntegrable
  let L := bellmanWeightedTestIntegral H (fun _ => 1) - bellmanWeightedTestIntegral volume p
  have hzero : ∀ φ : BellmanRealTest, L (bellmanTestDerivative φ) = 0 := by
    intro φ
    change bellmanWeightedTestIntegral H (fun _ => 1) (bellmanTestDerivative φ) -
      bellmanWeightedTestIntegral volume p (bellmanTestDerivative φ) = 0
    rw [bellmanWeightedTestIntegral_apply H _ h1,
      bellmanWeightedTestIntegral_apply volume p hp]
    change (∫ x, deriv φ x * 1 ∂H) - (∫ x, deriv φ x * p x) = 0
    simp
    rw [hw φ]
    have he := bellman_fluxMeasurePrimitive_weak φ
    change (∫ x, φ x * J x) - a * (∫ x, g x * φ x ∂F) =
      -(∫ x, deriv φ x * p x) at he
    linarith
  obtain ⟨c, hc⟩ := bellman_test_derivative_kernel L hzero
  refine ⟨c, ?_⟩
  have hm : Measurable p :=
    (bellman_lebesguePrimitive_continuous J hJ).measurable.sub
      (measurable_const.mul
        (bellmanMeasurePrimitive_stronglyMeasurable F g hg.measurable 0).measurable)
  have hcp : LocallyIntegrable (fun x => c + p x) volume :=
    continuous_const.locallyIntegrable.add hp
  have htest : ∀ φ : BellmanRealTest,
      (∫ x, φ x ∂H) = ∫ x, φ x * (c + p x) := by
    intro φ
    have he := hc φ
    change bellmanWeightedTestIntegral H (fun _ => 1) φ -
      bellmanWeightedTestIntegral volume p φ = c * (∫ x, φ x) at he
    rw [bellmanWeightedTestIntegral_apply H _ h1,
      bellmanWeightedTestIntegral_apply volume p hp] at he
    simp at he
    have hi : Integrable (fun x => φ x * p x) volume := by
      convert! hp.integrable_smul_left_of_hasCompactSupport
        φ.contDiff.continuous φ.hasCompactSupport using 1
    have hiφ : Integrable (fun x => φ x) volume :=
      φ.contDiff.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    rw [show (fun x => φ x * (c + p x)) =
      (fun x => c * φ x + φ x * p x) by funext x; ring,
      integral_add (hiφ.const_mul c) hi, integral_const_mul]
    linarith
  constructor
  · rw [(bellman_measure_eq_withDensity_of_test_pairing H (fun x => c + p x) (measurable_const.add hm) hcp htest)]
    congr 1
    funext x
    congr 1
    dsimp [p]
    ring
  · have hn := bellman_nonneg_of_test_pairing H (fun x => c + p x) hcp htest
    filter_upwards [hn] with x hx
    dsimp [p] at hx
    linarith


/-- Measure comparison implies almost everywhere comparison of real nonnegative densities. -/
theorem bellman_density_le_of_measure_le (f h : ℝ → ℝ)
    (hmf : Measurable f) (hnf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hnh : ∀ᵐ x ∂volume, 0 ≤ h x)
    (hm : volume.withDensity (fun x => ENNReal.ofReal (f x)) ≤
      volume.withDensity (fun x => ENNReal.ofReal (h x))) :
    ∀ᵐ x ∂volume, f x ≤ h x := by
  have he : (fun x => ENNReal.ofReal (f x)) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal (h x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite hmf.ennreal_ofReal
    intro s hs _
    simpa only [← withDensity_apply _ hs] using hm s
  filter_upwards [he, hnf, hnh] with x hx hfx hhx
  simpa only [ENNReal.toReal_ofReal hfx, ENNReal.toReal_ofReal hhx] using (ENNReal.toReal_mono (by simp) hx)

/-- The Radon–Nikodym representative is an actual density of an absolutely continuous Radon
measure. -/
theorem bellman_rnDeriv_density (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hF : F ≪ volume) :
    F = volume.withDensity (fun x => ENNReal.ofReal ((F.rnDeriv volume x).toReal)) := by
  calc
    F = volume.withDensity (F.rnDeriv volume) :=
      (Measure.withDensity_rnDeriv_eq F volume hF).symm
    _ = _ := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top F volume] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm

/-- A weighted measure primitive becomes a literal moment of its Radon–Nikodym density. -/
theorem bellmanMeasurePrimitive_eq_rnMoment (F : Measure ℝ) [IsFiniteMeasureOnCompacts F]
    (hF : F ≪ volume) (g : ℝ → ℝ) (y : ℝ) :
    bellmanMeasurePrimitive F g 0 y =
      ∫ z in 0..y, g z * (F.rnDeriv volume z).toReal := by
  dsimp [bellmanMeasurePrimitive]
  rcases le_total 0 y with hy | hy
  · rw [intervalIntegral.integral_of_le hy, intervalIntegral.integral_of_le hy]
    rw [show (fun z => g z * (F.rnDeriv volume z).toReal) =
      (fun z => (F.rnDeriv volume z).toReal * g z) by funext z; ring]
    exact (setIntegral_toReal_rnDeriv_mul hF measurableSet_Ioc).symm
  · rw [intervalIntegral.integral_of_ge hy, intervalIntegral.integral_of_ge hy]
    congr 1
    rw [show (fun z => g z * (F.rnDeriv volume z).toReal) =
      (fun z => (F.rnDeriv volume z).toReal * g z) by funext z; ring]
    exact (setIntegral_toReal_rnDeriv_mul hF measurableSet_Ioc).symm


/-- Multiplying a locally integrable density by a polynomial preserves local integrability. -/
theorem bellman_polynomial_locallyIntegrable (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (n : ℕ) :
    LocallyIntegrable (fun x => x ^ n * f x) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).continuousOn_mul (by fun_prop) hK

/-- A constant function is absolutely continuous on every interval. -/
theorem bellman_const_locallyAC (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  ContDiffOn.absolutelyContinuousOnInterval
    (contDiff_const : ContDiff ℝ 1 (fun _ => c)).contDiffOn

/-- Literal moments of a locally integrable angular density are locally absolutely continuous. -/
theorem bellman_moment_locallyAC (f : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (n : ℕ) (a b : ℝ) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (fun x => ∫ z in 0..x, z ^ n * f z) a b :=
  bellman_lebesguePrimitive_locallyAC _ (bellman_polynomial_locallyIntegrable f hf n) a b hab

/-- The flux written with its first moment has the asserted almost everywhere derivative. -/
theorem bellman_momentFlux_deriv (f : ℝ → ℝ) (hf : LocallyIntegrable f volume) (j c : ℝ) :
    ∀ᵐ x ∂volume, deriv (fun y => j - c * (∫ z in 0..y, z * f z)) x = -c * x * f x := by
  have hi : LocallyIntegrable (fun x => x * f x) volume := by
    simpa using bellman_polynomial_locallyIntegrable f hf 1
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hi] with x hx
  have hd := (hasDerivAt_const x j).sub ((hx 0).const_mul c)
  convert hd.deriv using 1; ring

/-- The density written with the second moment has the asserted almost everywhere derivative. -/
theorem bellman_momentDensity_deriv (f J : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hJ : LocallyIntegrable J volume) (c : ℝ) :
    ∀ᵐ x ∂volume, deriv (fun y => c + (∫ z in 0..y, J z) -
      (1 / 3 : ℝ) * (∫ z in 0..y, z ^ 2 * f z)) x = J x - x ^ 2 * f x / 3 := by
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hJ,
    _root_.LocallyIntegrable.ae_hasDerivAt_integral (bellman_polynomial_locallyIntegrable f hf 2)] with x hx hix
  have hd := ((hasDerivAt_const x c).add (hx 0)).sub ((hix 0).const_mul (1 / 3))
  convert hd.deriv using 1; ring

end HypoellipticAleksandrov.KineticAleksandrov

