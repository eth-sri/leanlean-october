module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.ClockPushforward
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov SectionTwo TheoremA Evolution Green
open scoped ENNReal NNReal

/-- Native product coordinates become physical coordinates by exchanging the spatial fields. -/
def poleDensityPhysicalHomeomorph : (ℝ × PDE.Vec 1 × PDE.Vec 1) ≃ₜ Point :=
  ((Homeomorph.refl ℝ).prodCongr (Homeomorph.prodComm (PDE.Vec 1) (PDE.Vec 1))).trans
    (KineticPoint.homeomorphProd 1).symm

/-- The native-to-physical product coordinate map preserves the literal kinetic volume. -/
theorem poleDensityPhysical_volumePreserving :
    MeasurePreserving poleDensityPhysicalHomeomorph volume volume := by
  have hs : MeasurePreserving (Prod.map (id : ℝ → ℝ) Prod.swap)
      (volume : Measure (ℝ × PDE.Vec 1 × PDE.Vec 1)) volume :=
    (MeasurePreserving.id volume).prod Measure.measurePreserving_swap
  have hp : MeasurePreserving (KineticPoint.equivProd 1).symm volume volume :=
    ⟨KineticPoint.measurable_equivProd_symm 1, rfl⟩
  exact hp.comp hs

/-- The established Green elapsed-to-physical map is a measurable embedding at clock time zero. -/
theorem poleDensityElapsed_measurableEmbedding :
    MeasurableEmbedding (elapsedPhysicalPoint 0 (R := ⊤)) := by
  have he := (MeasurableEmbedding.subtype_coe (measurableSet_elapsedTime ⊤)).prodMap
    (MeasurableEmbedding.id : MeasurableEmbedding (id : EvolutionAmbientState 1 → _))
  have hc := poleDensityPhysicalHomeomorph.measurableEmbedding.comp he
  have heq : (poleDensityPhysicalHomeomorph ∘
      Prod.map (Subtype.val : ElapsedTime ⊤ → ℝ) id) = elapsedPhysicalPoint 0 := by
    funext q
    apply (KineticPoint.equivProd 1).injective
    change (q.1.1, q.2.2, q.2.1) = (0 + q.1.1, q.2.2, q.2.1)
    rw [zero_add]
  exact heq ▸ hc

/-- Positive physical time is the exact range of the normalized Green carrier embedding. -/
theorem poleDensityElapsed_range :
    range (elapsedPhysicalPoint 0 (R := ⊤)) = {p : Point | 0 < p.time} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    change 0 < 0 + q.1.1
    simpa using q.1.2.1
  · intro hp
    refine ⟨(⟨p.time, hp, ENNReal.ofReal_lt_top⟩, p.velocity, p.position), ?_⟩
    ext i <;> simp [elapsedPhysicalPoint]

/-- The Green Lebesgue reference maps to the literal positive-time physical Lebesgue restriction. -/
theorem poleDensityElapsed_map_volume :
    (greenLebesgue 1).map (elapsedPhysicalPoint 0) =
      (volume : Measure Point).restrict {p | 0 < p.time} := by
  have heq : elapsedPhysicalPoint 0 = poleDensityPhysicalHomeomorph ∘
      Prod.map (Subtype.val : ElapsedTime ⊤ → ℝ) id := by
    funext q
    apply (KineticPoint.equivProd 1).injective
    change (0 + q.1.1, q.2.2, q.2.1) = (q.1.1, q.2.2, q.2.1)
    rw [zero_add]
  have ht : (elapsedVolume ⊤).map (Subtype.val : ElapsedTime ⊤ → ℝ) =
      (volume : Measure ℝ).restrict (Ioi 0) := by
    have hs : {t : ℝ | 0 < t ∧ ENNReal.ofReal t < ⊤} = Ioi 0 := by
      ext t
      simp
    exact (map_comap_subtype_coe (measurableSet_elapsedTime ⊤) (volume : Measure ℝ)).trans (congrArg (fun S => volume.restrict S) hs)

  rw [heq, greenLebesgue, ← Measure.map_map poleDensityPhysicalHomeomorph.continuous.measurable
    (measurable_subtype_coe.prodMap measurable_id), ← Measure.map_prod_map _ _
      measurable_subtype_coe measurable_id, ht, Measure.map_id,
    Measure.restrict_prod_eq_prod_univ]
  have hpre : poleDensityPhysicalHomeomorph ⁻¹' {p | 0 < p.time} =
      Ioi 0 ×ˢ (univ : Set (EvolutionAmbientState 1)) := by
    ext q
    change (0 < q.1) ↔ (0 < q.1 ∧ q.2 ∈ univ)
    simp
  exact (congrArg (fun s =>
    (volume.restrict s).map poleDensityPhysicalHomeomorph) hpre).symm.trans
      ((poleDensityPhysicalHomeomorph.measurableEmbedding.restrict_map (volume : Measure (ℝ × PDE.Vec 1 × PDE.Vec 1)) {p | 0 < p.time}).symm.trans (congrArg (fun μ : Measure Point => μ.restrict {p | 0 < p.time})
        poleDensityPhysical_volumePreserving.map_eq))


/-- Extend a native Green density to the actual physical clock space by zero at nonpositive
  times. -/
def poleDensityExtend (G : GreenCarrier 1 → ℝ≥0∞) : Point → ℝ≥0∞ :=
  Function.extend (elapsedPhysicalPoint 0) G (fun _ => 0)

/-- Zero extension through the actual elapsed embedding is Borel. -/
theorem poleDensityExtend_measurable {G : GreenCarrier 1 → ℝ≥0∞} (hG : Measurable G) :
    Measurable (poleDensityExtend G) :=
  poleDensityElapsed_measurableEmbedding.measurable_extend hG measurable_const

/-- The extension equals the native density at every genuine elapsed point. -/
theorem poleDensityExtend_apply (G : GreenCarrier 1 → ℝ≥0∞) (q : GreenCarrier 1) :
    poleDensityExtend G (elapsedPhysicalPoint 0 q) = G q :=
  poleDensityElapsed_measurableEmbedding.injective.extend_apply _ _ _

/-- The physical zero extension has support only at strictly positive physical clock times. -/
theorem poleDensityExtend_support (G : GreenCarrier 1 → ℝ≥0∞) :
    Function.support (poleDensityExtend G) ⊆ {p : Point | 0 < p.time} := by
  intro p hp
  by_contra ht
  apply hp
  exact Function.extend_apply' _ _ _ (fun h => ht (poleDensityElapsed_range ▸ h))

/-- Exact zero extension preserves the full ambient physical Lebesgue norm. -/
theorem poleDensityExtend_eLpNorm {G : GreenCarrier 1 → ℝ≥0∞} (hG : Measurable G)
    (q : ℝ≥0∞) :
    eLpNorm (poleDensityExtend G) q (volume : Measure Point) =
      eLpNorm G q (greenLebesgue 1) := by
  exact (eLpNorm_restrict_eq_of_support_subset (μ := (volume : Measure Point)) (p := q) (poleDensityExtend_measurable hG).aestronglyMeasurable (poleDensityExtend_support G)).symm.trans ((congrArg (fun μ : Measure Point =>
    eLpNorm (poleDensityExtend G) q μ) poleDensityElapsed_map_volume).symm.trans
      ((poleDensityElapsed_measurableEmbedding.eLpNorm_map_measure (μ := greenLebesgue 1) (g := poleDensityExtend G) (p := q)).trans (congrArg (fun f =>
        eLpNorm f q (greenLebesgue 1)) (funext (poleDensityExtend_apply G)))))

/-- Mapping a native density through the actual elapsed embedding yields its physical extension. -/
theorem poleDensityExtend_map_withDensity {G : GreenCarrier 1 → ℝ≥0∞} (hG : Measurable G) :
    ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) =
      (volume : Measure Point).withDensity (poleDensityExtend G) := by
  have hmap : ((greenLebesgue 1).withDensity G).map (elapsedPhysicalPoint 0) =
      ((greenLebesgue 1).map (elapsedPhysicalPoint 0)).withDensity (poleDensityExtend G) := by
    apply Measure.ext
    intro S hS
    rw [poleDensityElapsed_measurableEmbedding.map_apply,
      withDensity_apply _ (poleDensityElapsed_measurableEmbedding.measurable hS),
      withDensity_apply _ hS,
      setLIntegral_map hS (poleDensityExtend_measurable hG)
        poleDensityElapsed_measurableEmbedding.measurable]
    apply lintegral_congr
    intro q
    exact (poleDensityExtend_apply G q).symm
  have hres : ((volume : Measure Point).restrict {p | 0 < p.time}).withDensity
      (poleDensityExtend G) = volume.withDensity (poleDensityExtend G) := by
    apply Measure.ext
    intro S hS
    rw [withDensity_apply _ hS, withDensity_apply _ hS,
      Measure.restrict_restrict hS]
    rw [← lintegral_indicator hS, ← lintegral_indicator
      (hS.inter (isOpen_lt continuous_const continuous_time).measurableSet)]
    have hi : (S ∩ {p : Point | 0 < p.time}).indicator (poleDensityExtend G) =
        S.indicator (poleDensityExtend G) := by
      funext p
      by_cases hp : p ∈ S
      · by_cases ht : 0 < p.time
        · rw [Set.indicator_of_mem (show p ∈ S ∩ {p : Point | 0 < p.time}
            from ⟨hp, ht⟩), Set.indicator_of_mem hp]
        · have hz : poleDensityExtend G p = 0 := by
            by_contra hn
            exact ht (poleDensityExtend_support G hn)
          simp [hp, ht, hz]
      · simp [hp]
    exact congrArg (fun f => ∫⁻ p, f p ∂volume) hi

  exact hmap.trans ((congrArg (fun μ : Measure Point => μ.withDensity (poleDensityExtend G))
    poleDensityElapsed_map_volume).trans hres)


/-- The inverse velocity weight is masked to the actual physical active interval. -/
def poleInverseVelocity (c : Clock) (p : Point) : ℝ :=
  by
    classical
    exact if p.velocity 0 ∈ c.active then 1 / |p.velocity 0| else 0

/-- The masked inverse velocity weight is Borel. -/
theorem poleInverseVelocity_measurable (c : Clock) : Measurable (poleInverseVelocity c) := by
  classical
  unfold poleInverseVelocity
  exact Measurable.ite (isOpen_Ioo.preimage ((continuous_apply 0).comp
    continuous_velocity)).measurableSet
    (measurable_const.div (((continuous_apply 0).comp continuous_velocity).abs.measurable))
    measurable_const



/-- The literal physical pole density obtained by removing the velocity weight. -/
def polePhysicalDensity (c : Clock) (e : Point) (F : Point → ℝ) (p : Point) : ℝ :=
  ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p)) * poleInverseVelocity c p

/-- The physical density formula is Borel. -/
theorem polePhysicalDensity_measurable (c : Clock) (e : Point) (F : Point → ℝ)
    (hF : Measurable F) : Measurable (polePhysicalDensity c e F) :=
  (measurable_const.mul (hF.comp (c.continuous_map e).measurable)).mul
    (poleInverseVelocity_measurable c)

/-- The physical density formula is nonnegative when the normalized density is nonnegative. -/
theorem polePhysicalDensity_nonneg (c : Clock) (e : Point) (F : Point → ℝ)
    (hF : ∀ p, 0 ≤ F p) (p : Point) : 0 ≤ polePhysicalDensity c e F p  := by
  have poleInverseVelocity_nonneg :
      0 ≤ poleInverseVelocity c p := by
    unfold poleInverseVelocity
    split
    · exact div_nonneg zero_le_one (abs_nonneg _)
    · exact le_rfl
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
    (hF _)) (poleInverseVelocity_nonneg)

/-- The actual physical Green has exactly the density computed from the actual normalized one. -/
theorem clock_physical_green_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point) (he : e.velocity 0 ∈ c.active)
    (F : Point → ℝ) (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p)
    (hFd : clockGreen hH hLE hlam hLam A c e he =
      volume.withDensity (fun p => ENNReal.ofReal (F p))) :
    stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
      volume.withDensity (fun p => ENNReal.ofReal (polePhysicalDensity c e F p))  := by
  have clock_weightedGreen_density (_hFn : ∀ p, 0 ≤ F p) :
      (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
      ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
      volume.withDensity (fun p => ENNReal.ofReal
        ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := by
    have clock_weightedGreen_inverse :
        (stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩).withDensity (fun p => ENNReal.ofReal |p.velocity 0|) =
        ENNReal.ofReal (|c.vbar| * c.r ^ 2) •
          (clockGreen hH hLE hlam hLam A c e he).map (c.inverse e) := by
      have hi (μ : Measure Point) : (μ.map (c.map e)).map (c.inverse e) = μ := by
        rw [Measure.map_map (c.continuous_inverse e).measurable (c.continuous_map e).measurable]
        have heq : c.inverse e ∘ c.map e = id := funext (c.inverse_map e)
        rw [heq, Measure.map_id]
      exact (hi _).symm.trans ((congrArg (fun μ : Measure Point => μ.map (c.inverse e)) (clock_green_pushforward hH hLE hlam hLam A c e he)).trans (Measure.map_smul _ (c.continuous_inverse
        e).measurable.aemeasurable))
    have poleDensity_clock_map_withDensity :
        ((volume : Measure Point).withDensity (fun p => ENNReal.ofReal (F p))).map (c.inverse e) =
        ((volume : Measure Point).map (c.inverse e)).withDensity
          (fun p => ENNReal.ofReal (F (c.map e p))) := by
      apply Measure.ext
      intro S hS
      rw [Measure.map_apply (c.continuous_inverse e).measurable hS,
        withDensity_apply _ ((c.continuous_inverse e).measurable hS), withDensity_apply _ hS]
      have hm := setLIntegral_map (μ := (volume : Measure Point))
        (f := fun p => ENNReal.ofReal (F (c.map e p))) hS
        (hF.comp (c.continuous_map e).measurable).ennreal_ofReal
        (c.continuous_inverse e).measurable
      refine (lintegral_congr (fun p => ?_)).trans hm.symm
      exact congrArg (fun q => ENNReal.ofReal (F q)) (c.map_inverse e p).symm
    have hD : 0 ≤ |c.vbar| * c.r ^ 2 := mul_nonneg (abs_nonneg _) (sq_nonneg _)
    have hr : 0 ≤ (c.r ^ 6)⁻¹ := inv_nonneg.mpr (pow_nonneg c.positive.le _)
    have hm := c.map_inverse_volume e
    refine clock_weightedGreen_inverse.trans ((congrArg (fun μ : Measure Point => ENNReal.ofReal (|c.vbar| * c.r ^ 2) • μ.map (c.inverse e)) hFd).trans ?_)
    rw [poleDensity_clock_map_withDensity, hm, withDensity_smul_measure, smul_smul]
    refine (withDensity_smul' (μ := (volume : Measure Point)) (ENNReal.ofReal (|c.vbar| * c.r ^ 2) * ENNReal.ofReal ((c.r ^ 6)⁻¹)) (fun p => ENNReal.ofReal (F (c.map e p))) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).symm.trans ?_
    apply congrArg (fun g => volume.withDensity g)
    funext p
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ((ENNReal.ofReal_mul (mul_nonneg hD hr)).trans
      (congrArg (fun x => x * ENNReal.ofReal (F (c.map e p)))
        (ENNReal.ofReal_mul hD))).symm
  let μ := stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩
  have hi : (μ.withDensity (fun p => ENNReal.ofReal |p.velocity 0|)).withDensity
      (fun p => ENNReal.ofReal (poleInverseVelocity c p)) = μ := by
    rw [← withDensity_mul μ clock_velocity_weight_measurable
      (poleInverseVelocity_measurable c).ennreal_ofReal]
    have hh : ((fun p => ENNReal.ofReal |p.velocity 0|) *
        fun p => ENNReal.ofReal (poleInverseVelocity c p)) =ᵐ[μ] 1 := by
      filter_upwards [stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
        ⟨e, WithTop.coe_lt_top _, he⟩] with p hp
      have hc := abs_pos.mpr c.nonzero
      have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) (c.active_abs_bounds hp.2).1
      have hpactive : p.velocity 0 ∈ c.active := hp.2
      change ENNReal.ofReal |p.velocity 0| * ENNReal.ofReal (poleInverseVelocity c p) = 1
      rw [poleInverseVelocity, ite_eq_left hpactive, ← ENNReal.ofReal_mul (abs_nonneg _),
        mul_one_div_cancel hv.ne', ENNReal.ofReal_one]
    exact (withDensity_congr_ae hh).trans withDensity_one
  have hm : Measurable (fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) := (measurable_const.mul (hF.comp
        (c.continuous_map e).measurable)).ennreal_ofReal
  have hg : ((fun p => ENNReal.ofReal
      ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ * F (c.map e p))) *
      fun p => ENNReal.ofReal (poleInverseVelocity c p)) =
      fun p => ENNReal.ofReal (polePhysicalDensity c e F p) := by
    funext p
    exact (ENNReal.ofReal_mul (mul_nonneg (mul_nonneg
      (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (inv_nonneg.mpr (pow_nonneg c.positive.le _)))
      (hFn _))).symm
  exact hi.symm.trans ((congrArg (fun ν : Measure Point => ν.withDensity
    (fun p => ENNReal.ofReal (poleInverseVelocity c p))) (clock_weightedGreen_density hFn)).trans
      ((withDensity_mul (volume : Measure Point) hm (poleInverseVelocity_measurable c).ennreal_ofReal).symm.trans (congrArg (fun g => volume.withDensity g) hg)))


/-- The actual one-sign infinite physical Green measure has a nonnegative Lebesgue density
with the exact `r^(6/q-4)` norm bound. The constant is uniform in coefficient derivatives,
clock centres, radii and starting points. The analytic classical inputs remain explicit. -/
theorem one_sign_pole_density
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (q : ℝ) (hq : 1 < q) (hq2 : q < (3 : ℝ) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ g : Point → ℝ,
      Measurable g ∧ (∀ p, 0 ≤ g p) ∧
      stripGreen hH hLE hlam hLam A c.activeInterval ⊤ ⟨e, WithTop.coe_lt_top _, he⟩ =
        volume.withDensity (fun p => ENNReal.ofReal (g p)) ∧
      eLpNorm g (ENNReal.ofReal q) volume ≤ ENNReal.ofReal (C * c.r ^ (6 / q - 4 : ℝ)) ∧
      (∀ᵐ p ∂stripGreen hH hLE hlam hLam A c.activeInterval ⊤
        ⟨e, WithTop.coe_lt_top _, he⟩, e.time < p.time ∧ p.velocity 0 ∈ c.active)   := by
  have polePhysicalDensity_eLpNorm_bound (c : Clock) (e : Point) (F : Point → ℝ) (hF : Measurable F) (hFn : ∀ p, 0 ≤ F p) (C : ℝ) (hq : 0 < q) (_hC : 0 ≤ C) (hn : eLpNorm F (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C) :
      eLpNorm (polePhysicalDensity c e F) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal (2 * C * c.r ^ (6 / q - 4 : ℝ)) := by
    have polePhysicalDensity_pointwise_bound (p : Point) :
        |polePhysicalDensity c e F p| ≤ |(2 / c.r ^ 4) * F (c.map e p)| := by
      have poleInverseVelocity_le :
          poleInverseVelocity c p ≤ 2 / |c.vbar| := by
        have hc := abs_pos.mpr c.nonzero
        unfold poleInverseVelocity
        split
        next hp =>
          have hb := (c.active_abs_bounds hp).1
          have hv : 0 < |p.velocity 0| := lt_of_lt_of_le (by linarith) hb
          apply (div_le_div_iff₀ hv hc).mpr
          nlinarith
        next => exact div_nonneg (by norm_num) hc.le
      have hK : 0 ≤ (|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹ :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
          (inv_nonneg.mpr (pow_nonneg c.positive.le _))
      have hb : ((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹) * poleInverseVelocity c p ≤
          2 / c.r ^ 4 := by
        apply (mul_le_mul_of_nonneg_left (poleInverseVelocity_le) hK).trans_eq
        field_simp [c.nonzero, ne_of_gt c.positive]
      rw [abs_of_nonneg (polePhysicalDensity_nonneg c e F hFn p),
        abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) (pow_nonneg c.positive.le _)) (hFn _))]
      exact (show polePhysicalDensity c e F p =
        (((|c.vbar| * c.r ^ 2) * (c.r ^ 6)⁻¹) * poleInverseVelocity c p) * F (c.map e p)
          from by unfold polePhysicalDensity; ring).le.trans
        (mul_le_mul_of_nonneg_right hb (hFn _))
    have poleDensity_clock_eLpNorm :
        eLpNorm (F ∘ c.map e) (ENNReal.ofReal q) volume =
        ENNReal.ofReal (c.r ^ (6 / q : ℝ)) * eLpNorm F (ENNReal.ofReal q) volume := by
      have hm := eLpNorm_map_measure (μ := (volume : Measure Point))
        (p := ENNReal.ofReal q) hF.aestronglyMeasurable (c.continuous_map e).measurable.aemeasurable
      have hc := congrArg (fun μ : Measure Point => eLpNorm F (ENNReal.ofReal q) μ) (c.map_volume e)
      have hs := eLpNorm_smul_measure_of_ne_zero_of_ne_top (μ := (volume : Measure Point))
        (f := F) (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top (ENNReal.ofReal (c.r ^ 6))
      refine hm.symm.trans (hc.trans (hs.trans ?_))
      rw [smul_eq_mul]
      congr 1
      rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hq.le,
        ENNReal.ofReal_rpow_of_pos (pow_pos c.positive 6)]
      apply congrArg ENNReal.ofReal
      rw [← Real.rpow_natCast c.r 6, ← Real.rpow_mul c.positive.le]
      simp only [Nat.cast_ofNat, div_eq_mul_inv]
    have hb := eLpNorm_mono_ae (μ := (volume : Measure Point)) (p := ENNReal.ofReal q)
      (g := fun p => (2 / c.r ^ 4) * F (c.map e p))
      (polePhysicalDensity_measurable c e F hF).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => by
        simpa only [Real.norm_eq_abs] using polePhysicalDensity_pointwise_bound p))
    have hnorm : eLpNorm (fun p => (2 / c.r ^ 4) * F (c.map e p)) (ENNReal.ofReal q) volume =
        ENNReal.ofReal (2 / c.r ^ 4) * ENNReal.ofReal (c.r ^ (6 / q : ℝ)) *
          eLpNorm F (ENNReal.ofReal q) volume := by
      have hs := eLpNorm_const_smul (2 / c.r ^ 4) (F ∘ c.map e) (ENNReal.ofReal q)
        (volume : Measure Point)
      exact hs.trans (by rw [Real.enorm_of_nonneg (by positivity),
        poleDensity_clock_eLpNorm, mul_assoc])
    apply hb.trans (hnorm.le.trans ((mul_le_mul_of_nonneg_left hn zero_le).trans_eq ?_))
    have hk : 0 ≤ 2 / c.r ^ 4 := div_nonneg (by norm_num) (pow_nonneg c.positive.le _)
    rw [← ENNReal.ofReal_mul hk,
      ← ENNReal.ofReal_mul (mul_nonneg hk (Real.rpow_nonneg c.positive.le _))]
    apply congrArg ENNReal.ofReal
    rw [Real.rpow_sub c.positive]
    rw [show c.r ^ (4 : ℝ) = c.r ^ 4 from Real.rpow_natCast c.r 4]
    field_simp [ne_of_gt c.positive]
  have clockGreen_real_density :
      ∃ C : ℝ, 0 < C ∧ ∀ (A : SmoothAutonomous lam Lam) (c : Clock) (e : Point)
      (he : e.velocity 0 ∈ c.active), ∃ F : Point → ℝ,
      Measurable F ∧ (∀ p, 0 ≤ F p) ∧
      clockGreen hH hLE hlam hLam A c e he = volume.withDensity (fun p => ENNReal.ofReal (F p)) ∧
      eLpNorm F (ENNReal.ofReal q) volume ≤ ENNReal.ofReal C := open SectionTwo TheoremA Evolution Green in by
    obtain ⟨C, hC, hc⟩ := clockNativeGreen_density hH hLE hlam hLam q hq hq2
    refine ⟨C, hC, ?_⟩
    intro A c e he
    obtain ⟨G, hm, hd, hn, -⟩ := hc A c e he
    have hphysical : clockGreen hH hLE hlam hLam A c e he =
        volume.withDensity (poleDensityExtend G) :=
      (congrArg (fun μ : Measure (GreenCarrier 1) => μ.map (elapsedPhysicalPoint 0)) hd).trans
        (poleDensityExtend_map_withDensity hm)
    have hnorm : eLpNorm (poleDensityExtend G) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C := (poleDensityExtend_eLpNorm hm _).le.trans hn
    obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound volume
      (clockGreen hH hLE hlam hLam A c e he) (poleDensityExtend G)
      (poleDensityExtend_measurable hm) hphysical q C (by linarith) hC.le hnorm
    refine ⟨F, hFm, hFn, hFd, ?_⟩
    exact (ENNReal.ofReal_toReal hFLp.eLpNorm_ne_top).symm.le.trans
      (ENNReal.ofReal_le_ofReal hFN)
  obtain ⟨C, hC, hc⟩ := clockGreen_real_density
  refine ⟨2 * C, by positivity, ?_⟩
  intro A c e he
  obtain ⟨F, hFm, hFn, hFd, hFN⟩ := hc A c e he
  exact ⟨polePhysicalDensity c e F, polePhysicalDensity_measurable c e F hFm,
    polePhysicalDensity_nonneg c e F hFn,
    clock_physical_green_density hH hLE hlam hLam A c e he F hFm hFn hFd,
    polePhysicalDensity_eLpNorm_bound c e F hFm hFn C (by linarith) hC.le hFN,
    stripGreen_infinite_ae_future_carrier hH hLE hlam hLam A c.activeInterval
      ⟨e, WithTop.coe_lt_top _, he⟩⟩

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous

