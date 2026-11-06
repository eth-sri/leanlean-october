module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityIntegral
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.CapacityPrimitive
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.Setting
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.DomainDominationMeasure
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Velocity capacity of the actual finite-strip Green measure -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory HypoellipticAleksandrov

/- Velocity occupation is bounded by strip width times interval length over ellipticity. -/
theorem strip_capacity
    (hH : HormanderHypoellipticityStatement) (hLE : LiebermanEllipsoidDirichletStatement)
    {lam Lam } (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (A : SmoothAutonomous lam Lam) (H : Interval) (T : ℝ)
    (e : StripPole H (T : WithTop ℝ)) (E : Interval) :
    stripGreen hH hLE hlam hLam A H T e {p | p.velocity 0 ∈ E.carrier} ≤
      ENNReal.ofReal ((H.hi - H.lo) / lam * (E.hi - E.lo)) := by
  obtain ⟨chi, Phi, hchi, _hc, hn, h1, _hm, hPhi, hsecond, hd⟩ : ∃ chi Phi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) ∧ ContDiff ℝ (⊤ : ℕ∞) Phi ∧
      (∀ v, deriv (deriv Phi) v = 2 * chi v) ∧
      (∀ v, |deriv Phi v| ≤ 2 * (E.hi - E.lo)) := by
    obtain ⟨chi, hs, hc, hsup, hn, h1, hm⟩ : ∃ chi : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ Ioo (E.lo - (E.hi - E.lo) / 2) (E.hi + (E.hi - E.lo) / 2) ∧
      (∀ v, 0 ≤ chi v ∧ chi v ≤ 1) ∧ (∀ v ∈ Icc E.lo E.hi, chi v = 1) ∧
      (∫ v, chi v) ≤ 2 * (E.hi - E.lo) := by
      let a := E.lo - (E.hi - E.lo) / 2
      let b := E.hi + (E.hi - E.lo) / 2
      have hsub : Icc E.lo E.hi ⊆ Ioo a b := by
        intro v hv
        dsimp only [a, b]
        constructor <;> linarith [E.ordered, hv.1, hv.2]
      obtain ⟨chi, hs, hc, hsup, h01, h1⟩ :=
        exists_smooth_bump_of_isCompact_subset_isOpen (isCompact_Icc : IsCompact (Icc E.lo E.hi))
          isOpen_Ioo hsub
      refine ⟨chi, hs, hc, hsup, h01, h1, ?_⟩
      have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
      have he : (∫ v, chi v) = ∫ v in Ioo a b, chi v := by
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun v hv => image_eq_zero_of_notMem_tsupport (fun ht => hv (hsup ht)))).symm
      rw [he]
      have hm := integral_mono (hi.restrict (s := Ioo a b)) (integrable_const (1 : ℝ))
        (fun v => (h01 v).2)
      have hab : 0 ≤ b - a := by dsimp only [a, b]; linarith [E.ordered]
      have hv : (∫ _v in Ioo a b, (1 : ℝ)) = b - a := by
        simp only [integral_const, smul_eq_mul, mul_one, Measure.real,
          Measure.restrict_apply_univ, Real.volume_Ioo,
          ENNReal.toReal_ofReal hab]
      rw [hv] at hm
      exact hm.trans_eq (by dsimp only [a, b]; ring)
    let a := E.lo - (E.hi - E.lo) / 2
    let F : ℝ → ℝ := fun v => 2 * (∫ x in a..v, chi x) - ∫ x, chi x
    let Phi : ℝ → ℝ := fun v => ∫ x in 0..v, F x
    have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
      (contDiff_const.mul (capacity_primitive_smooth hs a)).sub contDiff_const
    have hdF (v : ℝ) : HasDerivAt F (2 * chi v) v := by
      have hd := intervalIntegral.integral_hasDerivAt_right
        (hs.continuous.intervalIntegrable a v)
        hs.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hs.continuous.continuousAt
      exact (hd.const_mul 2).sub_const _
    have hdPhi (v : ℝ) : HasDerivAt Phi (F v) v :=
      intervalIntegral.integral_hasDerivAt_right (hF.continuous.intervalIntegrable 0 v)
        hF.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuous.continuousAt
    have he : deriv Phi = F := funext fun v => (hdPhi v).deriv
    refine ⟨chi, Phi, hs, hc, hn, h1, hm, capacity_primitive_smooth hF 0, ?_, ?_⟩
    · intro v
      rw [he]
      exact (hdF v).deriv
    · intro v
      rw [he]
      have hi : Integrable chi volume := hs.continuous.integrable_of_hasCompactSupport hc
      have hsupport : tsupport chi ⊆ Ioi a := fun x hx => (hsup hx).1
      obtain ⟨hlo, hhi⟩ := capacity_cumulative_bounds hi (fun x => (hn x).1) hsupport v
      have ht : 0 ≤ ∫ x, chi x := integral_nonneg (fun x => (hn x).1)
      dsimp only [F]
      apply abs_le.mpr
      constructor <;> linarith
  let Γ := stripGreen hH hLE hlam hLam A H T e
  let U : Set Point := {p | p.velocity 0 ∈ E.carrier}
  have hU : MeasurableSet U :=
    isOpen_Ioo.measurableSet.preimage ((continuous_apply 0).comp continuous_velocity).measurable
  have hfin : IsFiniteMeasure Γ := by dsimp only [Γ, stripGreen]; infer_instance
  let g : Point → ℝ := fun p => 2 * A.a (p.position 0) (p.velocity 0) * chi (p.velocity 0)
  have hgc : Continuous g := by
    exact (continuous_const.mul (A.smooth.continuous.comp
      (((continuous_apply 0).comp continuous_position).prodMk
        ((continuous_apply 0).comp continuous_velocity)))).mul
      (hchi.continuous.comp ((continuous_apply 0).comp continuous_velocity))
  have hgn (p : Point) : 0 ≤ g p :=
    mul_nonneg (mul_nonneg (by norm_num)
      (hlam.trans_le (A.bounds _ _).1).le) (hn _).1
  have hgb (p : Point) : |g p| ≤ 2 * Lam := by
    rw [abs_of_nonneg (hgn p)]
    dsimp only [g]
    nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1,
      (A.bounds (p.position 0) (p.velocity 0)).2, (hn (p.velocity 0)).1,
      (hn (p.velocity 0)).2]
  have hi : Integrable g Γ := by
    apply Integrable.mono' (integrable_const (2 * Lam)) hgc.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hgb p
  have hind : Integrable (U.indicator (fun _p => (2 * lam))) Γ :=
    (integrable_const _).indicator hU
  have hlow : 2 * lam * (Γ U).toReal ≤ ∫ p, g p ∂Γ := by
    calc
      _ = ∫ p, U.indicator (fun _p => (2 * lam)) p ∂Γ := by
        rw [integral_indicator_const _ hU, Measure.real, smul_eq_mul]
        ring
      _ ≤ _ := integral_mono hind hi (fun p => by
        by_cases hp : p ∈ U
        · dsimp only [g]
          rw [indicator_of_mem hp, show chi (p.velocity 0) = 1 from
            h1 _ ⟨hp.1.le, hp.2.le⟩]
          nlinarith [(A.bounds (p.position 0) (p.velocity 0)).1]
        · rw [indicator_of_notMem hp]
          exact hgn p)
  have hD : 0 ≤ 2 * (E.hi - E.lo) := by linarith [E.ordered]
  have hupper := capacity_diffusion_integral_le hH hLE hlam hLam A H T e Phi chi
    hPhi hchi hn hsecond hD hd
  have hr : (Γ U).toReal ≤ (H.hi - H.lo) / lam * (E.hi - E.lo) := by
    have heq : ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam =
        (H.hi - H.lo) * (E.hi - E.lo) := by field_simp
    have hmul : (Γ U).toReal * lam ≤
        ((H.hi - H.lo) / lam * (E.hi - E.lo)) * lam := by
      rw [heq]
      change (∫ p, g p ∂Γ) ≤ _ at hupper
      nlinarith
    nlinarith
  have hnon : 0 ≤ (H.hi - H.lo) / lam * (E.hi - E.lo) :=
    mul_nonneg (div_nonneg (sub_pos.mpr H.ordered).le hlam.le)
      (sub_pos.mpr E.ordered).le
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top Γ U) hnon).mpr hr

end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
