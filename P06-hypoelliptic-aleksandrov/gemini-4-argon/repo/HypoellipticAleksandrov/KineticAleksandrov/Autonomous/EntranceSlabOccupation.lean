module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabHorizon
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreenSupport
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EnlargedRecursionOccupation
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.EntranceSlabIntegrated
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.InfiniteHorizonGreen

/-! # Localized occupation domination for starts in a time slab -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory ProbabilityTheory HypoellipticAleksandrov

/- Restricting starts and shortening the horizon can only decrease actual occupation. -/
theorem entranceSlab_greenMixture_le
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : FiniteIntervalUnion) (b T : ℝ)
    (hBT : b ≤ T) (mu : Measure Point) (D : Set Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A H b ∘ₘ mu.restrict D ≤
      enlargedVisitGreenKernel hH hLE hlam hLam A H T ∘ₘ mu := by
  let G := enlargedVisitGreenKernel hH hLE hlam hLam A H b
  let GT := enlargedVisitGreenKernel hH hLE hlam hLam A H T
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.bind_apply hB G.aemeasurable, Measure.bind_apply hB GT.aemeasurable]
  apply lintegral_mono' Measure.restrict_le_self
  intro p
  have _h_xinl_0 : enlargedVisitGreenKernel hH hLE hlam hLam A H b p ≤
      (enlargedVisitGreenKernel hH hLE hlam hLam A H T p).restrict {q | q.time < b} := by
    classical
    by_cases hp : p ∈ enlargedVisitPoleSet H b
    · have hpT : p ∈ enlargedVisitPoleSet H T := ⟨hp.1.trans_le hBT, hp.2⟩
      change (if h : p ∈ enlargedVisitPoleSet H b then
        finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩) else 0) ≤
        (if h : p ∈ enlargedVisitPoleSet H T then
          finiteUnionGreen hH hLE hlam hLam A H T (enlargedVisitPole H T ⟨p, h⟩)
            else 0).restrict {q | q.time < b}
      rw [dite_eq_left hp, dite_eq_left hpT]
      have _h_xinl_0 : finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, hp.1, hp.2⟩) =
      (finiteUnionGreen hH hLE hlam hLam A H T
        (enlargedVisitPole H T ⟨p, hp.1.trans_le hBT, hp.2⟩)).restrict {q | q.time < b} := by
        let hb := hp.1
        let hv := hp.2
        let ep := enlargedVisitPole H T ⟨p, hb.trans_le hBT, hv⟩
        let i := finiteUnionPoleIndex H T ep
        let e := stripPoleInfinite (H.component i) T (finiteUnionComponentPole H T ep)
        have he : enlargedVisitPole H b ⟨p, hb, hv⟩ =
            componentPoleInclusion H i b (stripPoleFinite (H.component i) e b hb) :=
          Subtype.ext rfl
        rw [he, finiteUnionGreen_component]
        change stripGreen hH hLE hlam hLam A (H.component i) b
            (stripPoleFinite (H.component i) e b hb) =
          (stripGreen hH hLE hlam hLam A (H.component i) T
            (stripPoleFinite (H.component i) e T (hb.trans_le hBT))).restrict {q | q.time < b}
        rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e b hb,
          stripGreen_finite_restrict_infinite hH hLE hlam hLam A (H.component i) e T
            (hb.trans_le hBT),
          Measure.restrict_restrict (isOpen_lt continuous_time continuous_const).measurableSet,
          inter_eq_left.mpr (show {q : Point | q.time < b} ⊆ {q | q.time < T} from
            fun _ hq => hq.trans_le hBT)]
      exact _h_xinl_0.le
    · have hz : enlargedVisitGreenKernel hH hLE hlam hLam A H b p = 0 := by
        change (if h : p ∈ enlargedVisitPoleSet H b then
          finiteUnionGreen hH hLE hlam hLam A H b (enlargedVisitPole H b ⟨p, h⟩)
            else 0) = 0
        exact dite_eq_right hp
      rw [hz]
      exact Measure.zero_le _
  exact (_h_xinl_0.trans
    Measure.restrict_le_self) B


/- An active Green kernel lives strictly between its starting time and its horizon. -/
theorem entranceSlab_greenMixture_le_restrict
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (c : Clock) (J : Interval) (a b T : ℝ)
    (hBT : b ≤ T) (hJ : closure c.active ⊆ J.carrier) (mu : Measure Point) :
    enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ
      mu.restrict {p | p.time ∈ Ioc a b} ≤
      (enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) T ∘ₘ mu).restrict
        {q | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active} := by
  have hle := Measure.restrict_mono (subset_refl
    {q : Point | q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active})
      (entranceSlab_greenMixture_le hH hLE hlam hLam A (visitActiveUnion c J) b T hBT
        mu {p | p.time ∈ Ioc a b})
  have _h_inl_11 : ∀ᵐ q ∂(enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b ∘ₘ mu.restrict {p | p.time ∈ Ioc a b}), q.time ∈ Ioc a b ∧ q.velocity 0 ∈ c.active := by
    apply Measure.ae_comp_of_ae_ae
      ((measurableSet_Ioc.preimage continuous_time.measurable).inter
        (isOpen_Ioo.measurableSet.preimage
          ((continuous_apply 0).comp continuous_velocity).measurable))
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.preimage continuous_time.measurable)] with p hp
    have _h_inl_11 : ∀ᵐ q ∂enlargedVisitGreenKernel hH hLE hlam hLam A (visitActiveUnion c J) b p,
        p.time < q.time ∧ q.time < b ∧ q.velocity 0 ∈ c.active := by
      classical
      rw [enlarged_activeUnion_eq c J hJ]
      change ∀ᵐ q ∂(if hp : p ∈ enlargedVisitPoleSet c.activeInterval.toFiniteUnion b then
        finiteUnionGreen hH hLE hlam hLam A c.activeInterval.toFiniteUnion b
          (enlargedVisitPole _ b ⟨p, hp⟩) else 0), _
      split
      · rename_i hp
        have hv : p.velocity 0 ∈ c.activeInterval.carrier := by
          simpa only [Interval.toFiniteUnion_carrier] using hp.2
        let e : StripPole c.activeInterval ⊤ := ⟨p, WithTop.coe_lt_top _, hv⟩
        change ∀ᵐ q ∂stripGreen hH hLE hlam hLam A c.activeInterval b
          (stripPoleFinite c.activeInterval e b hp.1), _
        rw [stripGreen_finite_restrict_infinite hH hLE hlam hLam A c.activeInterval e b hp.1]
        have hf := (stripGreen_infinite_ae_future_carrier
          hH hLE hlam hLam A c.activeInterval e).filter_mono
            (ae_mono (Measure.restrict_le_self (s := {q | q.time < b})))
        have ht : ∀ᵐ q ∂(stripGreen hH hLE hlam hLam A c.activeInterval ⊤ e).restrict
            {q | q.time < b}, q.time < b :=
          ae_restrict_mem (isOpen_lt continuous_time continuous_const).measurableSet
        filter_upwards [hf, ht] with q hq hqt
        exact ⟨hq.1, hqt, hq.2⟩
      · simp only [ae_zero, Filter.eventually_bot]
    exact _h_inl_11.mono
      fun q hq => ⟨⟨hp.1.trans hq.1, hq.2.1.le⟩, hq.2.2⟩
  exact (Measure.restrict_eq_self_of_ae_mem _h_inl_11).symm.le.trans hle

/- Every finite canonical sum of new-start occupations inherits full-space slab domination. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
