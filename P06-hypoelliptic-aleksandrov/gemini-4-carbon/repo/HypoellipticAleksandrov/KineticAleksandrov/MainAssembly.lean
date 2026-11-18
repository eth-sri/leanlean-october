module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernelsVariation
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.SourceNotation
import Mathlib.Tactic.Linarith
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksContract
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.UnitBlockRetentionLift
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CorridorSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.CommonSelection
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.ContinuedPhase
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.BlockInterior
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.OppositePaths
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.BarrierGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.CaseW
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenDensityTransport
public import HypoellipticAleksandrov.KineticAleksandrov.Green.Main
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.GeometryAPI
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelGreen
import Mathlib.MeasureTheory.Integral.Bochner.Set
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsRegularity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.GreenPotentialsLocality
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelEquation
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonGeometry
public import HypoellipticAleksandrov.Coefficients.Ellipticity
import Mathlib.MeasureTheory.Measure.OpenPos
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateDensity
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateReflection
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ABPAbstract
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelSource
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.EvolutionConclusion
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.OccupationDensityEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.SmoothEstimateSource
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.AssemblySource
public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.Borel
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.Occupation
import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourier
public import HypoellipticAleksandrov.KineticAleksandrov.TheoremA.LocalisedSource
public import HypoellipticAleksandrov.KineticAleksandrov.ClassicalInputs
public import HypoellipticAleksandrov.KineticAleksandrov.Evolution.Assembly
public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.FinalAutonomous
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Assembly
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.ComparisonConstant
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ComparisonLinear
import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelPhaseMeasure
import HypoellipticAleksandrov.LinearAlgebra.LoewnerEntryBound
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Tactic

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.Parabolic
open scoped ENNReal

/-- A characterized Fourier measure at a whole-space query is the canonical Fourier kernel. -/
theorem iteration_projection_eq {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) stationary) (σ τ : ℝ) (hστ : σ ≤ τ)
    (v ξ : PDE.Vec d) (q : EvolutionQuery (wholeSpace d) stationary)
    (hq : q.1 = (σ, τ, v, 0)) (ν : ComplexMeasure (PDE.Vec d))
    (hν : IsFourierProjection K q ξ ν) : ν = fourierKernel K σ τ hστ ξ v := by
  have he : q = wholeSpaceQuery σ τ hστ v 0 := Subtype.ext hq
  subst q
  apply VectorMeasure.ext
  intro E hE
  exact (hν E hE).trans ((fourierKernel_spec K σ τ hστ ξ v E hE).symm)

/-- Each full block contributes its contraction; the leftover interval contributes at most one. -/
theorem fourier_natural_block_iteration {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K)
    (ξ : PDE.Vec d) {T c : ℝ} (hT : 0 < T) (hc : 0 ≤ c)
    (hstep : ∀ (s : ℝ) (v : PDE.Vec d),
      totalVariationNorm (fourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ v) ≤
        ENNReal.ofReal c) (k : ℕ) (σ τ : ℝ) (hστ : σ ≤ τ)
    (hk : (k : ℝ) * T ≤ τ - σ) (v : PDE.Vec d) :
    totalVariationNorm (fourierKernel K σ τ hστ ξ v) ≤ ENNReal.ofReal c ^ k := by
  induction k generalizing σ τ v with
  | zero => simpa using fourierKernel_totalVariation_le_one K σ τ hστ ξ v
  | succ k ih =>
    let r := σ + T
    have hσr : σ ≤ r := le_add_of_nonneg_right hT.le
    have hrτ : r ≤ τ := by
      have hn : 0 ≤ k := Nat.cast_nonneg k
      rw [Nat.cast_succ] at hk
      nlinarith only [hk, hT, hn]
    have hremain : (k : ℝ) * T ≤ τ - r := by
      rw [Nat.cast_succ] at hk
      dsimp [r]
      linarith only [hk]
    calc
      _ ≤ totalVariationNorm (fourierKernel K σ r hσr ξ v) *
          ⨆ w : PDE.Vec d, totalVariationNorm (fourierKernel K r τ hrτ ξ w) :=
        fourierKernel_totalVariation_composition K hcomp hcov σ r τ hσr hrτ ξ v
      _ ≤ ENNReal.ofReal c * ENNReal.ofReal c ^ k := mul_le_mul' (hstep σ v) (iSup_le fun w => ih r τ hrτ hremain w)
      _ = ENNReal.ofReal c ^ (k + 1) := by rw [pow_succ, mul_comm]


/-- The authorized evolution premise supplies all structural clauses on the given kernel. -/
theorem iteration_evolution_clauses (hEvol : IterationEvolutionStatement)
    {d : ℕ} (hd : 1 ≤ d) {lam Lam : ℝ} (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSectionTwoCoefficient lam Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) stationary)
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hreal : RealizesTerminalEvolution (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) S K) :
    IsDomainMonotoneEvolution (wholeSpace d) stationary
      (zIndependentCoefficient B) (identityDrift d) K ∧
    HasParabolicMarginalBundle (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) K ∧
    IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K := by
  obtain ⟨hBs, hBy, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  obtain ⟨P, K₀, hclass, hendpointP, hpos, hcontract, hcompP, hint,
    hsupp, hmass, hmeas, hfiber, hend, hcomp, hcov, hmono, hmargin⟩ :=
    hEvol d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl
      (wholeSpace d) stationary (zIndependentCoefficient B) (identityDrift d)
      (wholeSpace_admissible d) (zeroCurve_piecewiseC1 d) hBs hBy hBell
      (identityDrift_smooth d) (identityDrift_bounds d).1 (identityDrift_bounds d).2
  have hr₀ : RealizesTerminalEvolution (wholeSpace d) stationary MeasurableSet.univ
      (zIndependentCoefficient B) (identityDrift d) P K₀ :=
    ⟨hclass, hint, hend, hcomp⟩
  have hK := (terminalEvolution_unique (wholeSpace d) stationary (wholeSpace_admissible d)
    (zIndependentCoefficient B) (identityDrift d) S P K K₀ hreal hr₀).2
  subst K₀
  exact ⟨hmono, hmargin, hcov (fun _ _ _ _ => rfl)⟩


/-- The frequency-floor estimate follows from the actual scaled blocks and Fourier composition. -/
theorem fourier_floor_iteration_of_blocks {d : ℕ}
    (K : MovingFiberKernel (wholeSpace d) stationary)
    (hcomp : K.HasComposition MeasurableSet.univ)
    (hcov : IsTranslationCovariantEvolution (wholeSpace d) stationary MeasurableSet.univ K)
    {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ1 : δ < 1)
    (ξ : PDE.Vec d) (hξ : ξ ≠ 0)
    (hsteps : ∀ (s : ℝ) (v : PDE.Vec d)
      (q : EvolutionQuery (wholeSpace d) stationary),
      q.1 = (s, s + L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ)), v, 0) →
      ∀ ν : ComplexMeasure (PDE.Vec d), IsFourierProjection K q ξ ν → TV ν ≤ 1 - δ)
    (σ τ : ℝ) (hστ : σ < τ) (v : PDE.Vec d)
    (q : EvolutionQuery (wholeSpace d) stationary) (hq : q.1 = (σ, τ, v, 0))
    (ν : ComplexMeasure (PDE.Vec d)) (hν : IsFourierProjection K q ξ ν) :
    let x := (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) / L
    let k := Nat.floor x
    TV ν ≤ (1 - δ) ^ k ∧
      (1 - δ) ^ k ≤ (1 - δ) ^ (x - 1) ∧
      (1 - δ) ^ (x - 1) = (1 - δ)⁻¹ *
        Real.exp (-(-Real.log (1 - δ) / L) * (τ - σ) *
          PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  dsimp only
  have hN := frequency_norm_pos hξ
  let N := PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)
  have hNp : 0 < N := Real.rpow_pos_of_pos hN _
  let T := L * PDE.vecEuclideanNorm ξ ^ (-(2 / 3 : ℝ))
  have hTdef : T = L / N := by
    dsimp [T, N]
    rw [Real.rpow_neg hN.le]
    rfl
  have hT : 0 < T := by rw [hTdef]; exact div_pos hL hNp
  have ha := sub_pos.mpr hδ1
  let x := (τ - σ) * N / L
  have hxT : x * T = τ - σ := by
    rw [hTdef]
    dsimp [x]
    field_simp
  have hk : (Nat.floor x : ℝ) * T ≤ τ - σ := by
    rw [← hxT]
    exact mul_le_mul_of_nonneg_right (Nat.floor_le ((div_pos (mul_pos (sub_pos.mpr hστ) hNp) hL).le)) hT.le
  have hstep : ∀ (s : ℝ) (w : PDE.Vec d),
      totalVariationNorm (fourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ w) ≤
        ENNReal.ofReal (1 - δ) := by
    intro s w
    have hst : s ≤ s + T := le_add_of_nonneg_right hT.le
    have hs := hsteps s w (wholeSpaceQuery s (s + T) hst w 0) rfl _ (fourierKernel_spec K s (s + T) hst ξ w)
    calc
      _ = ENNReal.ofReal (TV (fourierKernel K s (s + T) hst ξ w)) :=
        (ENNReal.ofReal_toReal (ne_of_lt ((fourierKernel_totalVariation_le_one K s (s + T) hst ξ w).trans_lt ENNReal.one_lt_top))).symm
      _ ≤ ENNReal.ofReal (1 - δ) := ENNReal.ofReal_le_ofReal hs
  have hr := ENNReal.toReal_mono (by simp) (fourier_natural_block_iteration K hcomp hcov ξ hT ha.le hstep (Nat.floor x) σ τ hστ.le hk v)
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le] at hr
  rw [iteration_projection_eq K σ τ hστ.le v ξ q hq ν hν]
  exact ⟨hr, decay_floor_power ha (by linarith only [hδ]),
    decay_power_exponential ha hL (τ - σ) N⟩




/-- The Green family, conditional on the unit-block estimate and the terminal evolution statement.
-/
theorem fourierDecayFamily_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    HypoellipticAleksandrov.KineticAleksandrov.Green.FourierDecayFamily d lam Lam  := by
  have fourier_decay_whole_space_of_unitBlock :
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily univ stationary) (K : MovingFiberKernel univ stationary),
        RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient B) id S K →
      ∀ (σ τ : ℝ), σ < τ →
      ∀ (v ξ : PDE.Vec d) (q : EvolutionQuery univ stationary), q.1 = (σ, τ, v, 0) →
      ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν →
        TV ν ≤ C * Real.exp (-c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
    have fourier_decay_frequency_iteration_of_unitBlock :
        ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
        ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
        ∀ (S : TerminalOperatorFamily univ stationary) (K : MovingFiberKernel univ stationary),
          RealizesTerminalEvolution univ stationary MeasurableSet.univ
            (zIndependentCoefficient B) id S K →
        ∀ (ξ : PDE.Vec d), ξ ≠ 0 → ∀ (σ τ : ℝ), σ < τ →
        ∀ (v : PDE.Vec d) (q : EvolutionQuery univ stationary), q.1 = (σ, τ, v, 0) →
        ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν →
          let x := (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ) / L
          let k := Nat.floor x
          TV ν ≤ (1 - δ) ^ k ∧ (1 - δ) ^ k ≤ (1 - δ) ^ (x - 1) ∧
            (1 - δ) ^ (x - 1) = (1 - δ)⁻¹ *
              Real.exp (-(-Real.log (1 - δ) / L) * (τ - σ) *
                PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
      have nonzero_frequency_blocks_of_unitBlock :
          ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
          ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
          ∀ (S : TerminalOperatorFamily (univ : Set (PDE.Vec d)) stationary)
            (K : MovingFiberKernel (univ : Set (PDE.Vec d)) stationary),
            RealizesTerminalEvolution univ stationary MeasurableSet.univ
              (zIndependentCoefficient B) id S K →
          ∀ (ξ : PDE.Vec d), ξ ≠ 0 →
          ∀ (s : ℝ) (v : PDE.Vec d) (q : EvolutionQuery (univ : Set (PDE.Vec d)) stationary),
            q.1 = (s, s + L * (PDE.vecEuclideanNorm ξ) ^ (-(2 / 3 : ℝ)), v, 0) →
          ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν → TV ν ≤ 1 - δ := open HypoellipticAleksandrov.KineticAleksandrov.Scaling in by
        obtain ⟨L, δ, hL, hδ, hδ1, hunit⟩ := hblock
        refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
        intro B hB S K hreal ξ hξ s v q hq ν hν
        obtain ⟨hr, hr2, hrunit⟩ := frequency_radius_identities hξ
        let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3 : ℝ)), hr⟩
        let Φ := KineticAffineScaling.ofRadius s v 0 (identityDrift d) r
        let hm : Φ.MapsDomain univ stationary univ stationary :=
          KineticAffineScaling.mapsDomain_wholeSpace Φ
        let K' := KineticAffineScaling.pushKernel hm K
        let S' := fiberOperator K' MeasurableSet.univ
        have hB' := scaledCoefficient_sectionTwo lam Lam B hB s v r
        have hreal' :=
          realizes_ofRadius_wholeSpace s v 0 r hreal
        obtain ⟨hmono', hmargin', hcov'⟩ := iteration_evolution_clauses hEvol hd hlam hlamLam
          (scaledCoefficient B s v r) hB' S' K' hreal'
        let q' : EvolutionQuery univ stationary :=
          wholeSpaceQuery 0 L hL.le (0 : PDE.Vec d) 0
        let ν' := fourierKernel K' 0 L hL.le (r.1 ^ 3 • ξ) 0
        have hν' : IsFourierProjection K' q' (r.1 ^ 3 • ξ) ν' :=
          fourierKernel_spec K' 0 L hL.le _ 0
        have hsetting : SourceSetting lam Lam 1 1 univ (scaledCoefficient B s v r) id :=
          ⟨hB', identityDrift_smooth d, zero_lt_one, le_rfl, identityDrift_bounds d,
            Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
        have hv' : (0 : PDE.Vec d) ∈ movingDomain univ stationary 0 := by
          change 0 ∈ movingDomain (wholeSpace d) (fun _ => 0) 0
          rw [movingDomain_wholeSpace]; exact mem_univ _
        have hL0 : 0 ≤ 0 + L := by linarith only [hL]
        have hq' : movingQuery 0 (0 + L) hL0 0 0 hv' = q' := by
          apply Subtype.ext
          simp
          rfl
        have hνunit : IsFourierProjection K' (movingQuery 0 (0 + L) hL0 0 0 hv')
            (r.1 ^ 3 • ξ) ν' := by
          rw [hq']
          exact hν'
        have hunit' := hunit univ (scaledCoefficient B s v r) id hsetting rfl MeasurableSet.univ
          S' K' hreal' hmono' hmargin' hcov' (r.1 ^ 3 • ξ) hrunit
          0 0 hv' hL0 ν' hνunit
        have hquery : KineticAffineScaling.queryMap hm q' = q := by
          apply Subtype.ext
          rw [hq]
          change (s + r.1 ^ 2 * 0, s + r.1 ^ 2 * L,
            v + r.1 • 0, 0 +
              (r.1 ^ 2 * 0) • identityDrift d v + r.1 ^ 3 • 0) = _
          simp
          rw [hr2, mul_comm L]
        have hνmap : IsFourierProjection K (KineticAffineScaling.queryMap hm q') ξ ν := by
          rw [hquery]; exact hν
        have htv := (realizes_ofRadius_fourier_tv s v 0 r hreal hreal' q' ξ ν ν'
          hνmap hν').2
        unfold TV at hunit' ⊢
        change (totalVariationNorm ν).toReal ≤ 1 - δ
        rw [htv]
        exact hunit'
      obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ :=
        nonzero_frequency_blocks_of_unitBlock
      refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
      intro B hB S K hreal ξ hξ σ τ hστ v q hq ν hν
      exact fourier_floor_iteration_of_blocks K hreal.2.2.2 ((iteration_evolution_clauses hEvol hd hlam hlamLam B hB S K hreal).2.2) hL hδ hδ1 ξ hξ
        (hsteps B hB S K hreal ξ hξ) σ τ hστ v q hq ν hν
    obtain ⟨L, δ, hL, hδ, hδ1, hiter⟩ :=
      fourier_decay_frequency_iteration_of_unitBlock
    obtain ⟨hC1, hc⟩ := decay_constants hδ hδ1 hL
    refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, lt_of_lt_of_le zero_lt_one hC1, hc, ?_⟩
    intro B hB S K hreal σ τ hστ v ξ q hq ν hν
    by_cases hξ : ξ = 0
    · subst ξ
      have he := iteration_projection_eq K σ τ hστ.le v 0 q hq ν hν
      rw [he]
      have ht := ENNReal.toReal_mono ENNReal.one_ne_top
        (fourierKernel_totalVariation_le_one K σ τ hστ.le 0 v)
      have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
        PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
      simp [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), Real.exp_zero]
      have htv : TV (fourierKernel K σ τ hστ.le 0 v) ≤ 1 := by
        simpa using ht
      exact htv.trans hC1
    · obtain ⟨h1, h2, h3⟩ := hiter B hB S K hreal ξ hξ σ τ hστ v q hq ν hν
      exact (h1.trans h2).trans_eq h3
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    fourier_decay_whole_space_of_unitBlock
  refine ⟨C, c, hC, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ
  have ht := hdecay B hB S K hreal σ τ hστ v ξ
    (wholeSpaceQuery σ τ hστ.le v 0) rfl _ (fourierKernel_spec K σ τ hστ.le ξ v)
  have hf : totalVariationNorm (fourierKernel K σ τ hστ.le ξ v) ≠ ⊤ :=
    ne_of_lt ((fourierKernel_totalVariation_le_one K σ τ hστ.le ξ v).trans_lt
      ENNReal.one_lt_top)
  calc
    _ = ENNReal.ofReal (TV (fourierKernel K σ τ hστ.le ξ v)) :=
      (ENNReal.ofReal_toReal hf).symm
    _ ≤ ENNReal.ofReal (C * Real.exp
        (-c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) :=
      ENNReal.ofReal_le_ofReal ht
    _ = _ := by congr 3; ring


/-- The exact case-W unit-block conditions, conditional only on the authorized
terminal-evolution existence statement. -/
theorem unit_frequency_block_W (hEvol : IterationEvolutionStatement)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl := by
  obtain ⟨Cstar, hC, hcorr⟩ := corridors_retained_dominated d hd lam Lam hlam hlamLam
  obtain ⟨h, q0, hh, hq0, hcommon⟩ :=
    continued_common_minorant_trimming d hd lam Lam hlam hlamLam
  let δ0 := (3 / 4) * blockMass Cstar 1 1 * h * q0
  have hδ0 : 0 < δ0 := by
    exact mul_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 3 / 4)
      (Real.exp_pos _)) hh) hq0
  let δ := min δ0 (1 / 2)
  have hδ : 0 < δ := lt_min hδ0 (by norm_num)
  have hδ1 : δ < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have htime := (block_parameters Cstar h q0 1 1 hC hh hq0 zero_lt_one le_rfl).2.2.2.2.2.2.1
  refine ⟨blockTime 1 1, δ, htime, hδ, hδ1, ?_⟩
  intro D B b hsetting hDW hD S K hreal hmono hpar hcov ξ hξ σ v hv hL ν hν
  subst D
  let ρ := blockRho 1
  let η := blockEta 1 1
  let s := σ + blockL0 1
  let T := σ + blockTime 1 1
  let Ω := PDE.euclideanBall v (4 * ρ)
  have hρ : 0 < ρ := blockRho_pos zero_lt_one
  have hη : 0 < η := blockEta_pos zero_lt_one zero_lt_one
  have hηρ : η < ρ := blockEta_lt_rho zero_lt_one
  have hστ : σ ≤ s := le_add_of_nonneg_right (blockL0_pos zero_lt_one).le
  have hsT : s ≤ T := by
    dsimp only [s, T, blockTime]
    nlinarith only [sq_nonneg ρ]
  have hfit : PDE.euclideanBall v (blockOuter 1) ⊆ (univ : Set (PDE.Vec d)) := subset_univ _
  obtain ⟨α, -, -, hpaths⟩ := exists_opposite_paths 1 1 σ zero_lt_one le_rfl
    univ b hsetting.2.1 hsetting.2.2.2.2.1 ξ v hξ hfit
  let γ1 : ℝ → PDE.Vec d := fun _ => v
  let γ2 : ℝ → PDE.Vec d := fun r =>
    v + (α * tent (blockL0 1) (max 0 (min (blockL0 1) (r - σ)))) • ξ
  obtain ⟨hγ1, hγ2, hstart1, hstart2, hend1, hend2,
    hspeed1, hspeed2, htube, hphase⟩ := hpaths
  change γ1 σ = v at hstart1
  change γ2 σ = v at hstart2
  have hadm : IsAdmissibleEvolutionDomain (PDE.euclideanBall (0 : PDE.Vec d) η) :=
    Or.inr (Or.inl ⟨0, η, hη, rfl⟩)
  have hΩadm : IsAdmissibleEvolutionDomain Ω :=
    Or.inr (Or.inl ⟨v, 4 * ρ, mul_pos (by norm_num) hρ, rfl⟩)
  obtain ⟨S1, K1, hreal1, -, hpar1, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting _ γ1 hadm hγ1
  obtain ⟨S2, K2, hreal2, -, hpar2, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting _ γ2 hadm hγ2
  obtain ⟨S0, K0, hreal0, hmono0, hpar0, -⟩ :=
    exists_unitBlock_evolution hEvol hd lam Lam 1 1 univ B b hsetting Ω stationary
      hΩadm (zeroCurve_piecewiseC1 d)
  have hv1 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ1 σ := by
    rw [mem_movingDomain_euclideanBall_iff, hstart1]
    simp [PDE.vecNormSq, PDE.vecDot]
    exact sq_pos_of_pos hη
  have hv2 : v ∈ movingDomain (PDE.euclideanBall 0 η) γ2 σ := by
    rw [mem_movingDomain_euclideanBall_iff, hstart2]
    simp [PDE.vecNormSq, PDE.vecDot]
    exact sq_pos_of_pos hη
  let q1 := movingQuery σ s hστ v 0 hv1
  let q2 := movingQuery σ s hστ v 0 hv2
  let qD := movingQuery σ s hστ v 0 hv
  let qT := movingQuery σ T hL v 0 hv
  obtain ⟨-, -, -, -, hsupp1, hsupp2, hmass1, hmass2, hdom⟩ :=
    hcorr 1 1 σ univ B b hsetting S K hD hreal hmono γ1 γ2 v 0
      hγ1 hγ2 hstart1 hstart2 hend1 hend2 hspeed1 hspeed2
      (fun r => (htube r).1) (fun r => (htube r).2)
      S1 K1 S2 K2 hreal1 hreal2 hpar1 hpar2 q1 q2 qD rfl rfl rfl
  let μ1 := K1.master q1
  let μ2 := K2.master q2
  have hfμ1 : IsFiniteMeasure μ1 := ⟨(K1.mass_le_one q1).trans_lt ENNReal.one_lt_top⟩
  have hfμ2 : IsFiniteMeasure μ2 := ⟨(K2.mass_le_one q2).trans_lt ENNReal.one_lt_top⟩
  let N1 := ENNReal.ofReal (blockMass Cstar 1 1 / (2 * μ1.real univ)) • μ1
  let N2 := ENNReal.ofReal (blockMass Cstar 1 1 / (2 * μ2.real univ)) • μ2
  have hfN1 : IsFiniteMeasure N1 := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ1 univ)
  have hfN2 : IsFiniteMeasure N2 := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ2 univ)
  have hN1supp : N1 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
    rw [Measure.smul_apply, hsupp1, smul_zero]
  have hN2supp : N2 (PDE.euclideanBall v η ×ˢ univ)ᶜ = 0 := by
    rw [Measure.smul_apply, hsupp2, smul_zero]
  let R1 := N1.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState d)
  let R2 := N2.comap (Subtype.val : EvolutionState Ω stationary s → EvolutionAmbientState d)
  have hη4ρ : η ≤ 4 * ρ := by linarith only [hηρ, hρ]
  obtain ⟨hR1, hmR1, hsupport1⟩ := retained_ball_comap_properties v η (4 * ρ) s
    hη.le hη4ρ N1 hN1supp
  obtain ⟨hR2, hmR2, hsupport2⟩ := retained_ball_comap_properties v η (4 * ρ) s
    hη.le hη4ρ N2 hN2supp
  have hfR1 : IsFiniteMeasure R1 := inferInstance
  have hfR2 : IsFiniteMeasure R2 := inferInstance
  let E1 := continuedMeasure K0 hsT R1
  let E2 := continuedMeasure K0 hsT R2
  have hE1 : ∀ A, MeasurableSet A → E1 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R1 :=
    fun A hA => continuedMeasure_apply K0 hsT R1 hA
  have hE2 : ∀ A, MeasurableSet A → E2 A =
      ∫⁻ p, K0.master (movingQuery s T hsT p.1.1 p.1.2 p.2.1) A ∂R2 :=
    fun A hA => continuedMeasure_apply K0 hsT R2 hA
  let M := K.master qT
  have hfM : IsFiniteMeasure M := ⟨(K.mass_le_one qT).trans_lt ENNReal.one_lt_top⟩
  have hcontinued : E1 + E2 ≤ M := by
    apply continued_measures_dominated univ Ω hD (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet
      B b S K S0 K0 hreal hreal0 hmono hΩadm (subset_univ _) σ s T hστ hsT qD qT
      ⟨rfl, rfl⟩ rfl R1 R2 _ E1 E2 hE1 hE2
    rw [hR1, hR2]
    exact hdom
  have hs : s = T - 4 * ρ ^ 2 := by dsimp only [s, T, blockTime]; ring
  have ha : 0 < blockMass Cstar 1 1 / 2 := div_pos (Real.exp_pos _) (by norm_num)
  have hvΩ : v ∈ movingDomain Ω stationary (T - ρ ^ 2) := by
    rw [movingDomain_stationary]
    change PDE.vecNormSq (v - v) < (4 * ρ) ^ 2
    simpa [PDE.vecNormSq, PDE.vecDot] using sq_pos_of_pos (mul_pos (by norm_num) hρ)
  let qlate := scalarQuery (T - ρ ^ 2) T (sub_le_self _ (sq_nonneg ρ)) v hvΩ
  obtain ⟨-, -, hfloor, F1, F2, hF1, hF2, hFsum, hmap1, hmap2⟩ :=
    hcommon 1 1 univ B b hsetting v ρ T (mem_univ _) hρ (subset_univ _)
      S0 K0 hreal0 hpar0 hmono0 s (blockMass Cstar 1 1 / 2) η hs hsT ha hη hηρ
      R1 R2 hfR1 hfR2 (hmR1.trans hmass1) (hmR2.trans hmass2) hsupport1 hsupport2
      E1 E2 M hfM hE1 hE2 hcontinued qlate rfl
  let Θ := ENNReal.ofReal (blockMass Cstar 1 1 / 2 * h) •
    P K0 (PDE.isOpen_euclideanBall v (4 * ρ)).measurableSet qlate
  have hfE1 : IsFiniteMeasure E1 := inferInstance
  have hfE2 : IsFiniteMeasure E2 := inferInstance
  have hfF1 : IsFiniteMeasure F1 := isFiniteMeasure_of_le _ hF1
  have hfF2 : IsFiniteMeasure F2 := isFiniteMeasure_of_le _ hF2
  obtain ⟨hΦ, -, -, hf1, hf2⟩ := block_continued_phase_error hd lam Lam 1 1 Cstar σ
    univ B b hsetting hC ξ v 0 hξ hfit γ1 γ2 hγ1 hγ2 hstart1 hstart2 hend1 hend2
    (fun r => (htube r).1) (fun r => (htube r).2) hphase
    S1 K1 S2 K2 S0 K0 hreal1 hreal2 hreal0 hpar1 hpar2 hpar0 q1 q2 rfl rfl
    R1 R2 hR1 hR2 hsT E1 E2 F1 F2 hE1 hE2 hF1 hF2
  have hMone : M.real univ ≤ 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using
      ENNReal.toReal_mono ENNReal.one_ne_top (K.mass_le_one qT)
  have hmass : blockMass Cstar 1 1 * h * q0 / 2 ≤ Θ.real univ := by
    convert hfloor using 1
    ring
  have hphaseν : IsPhaseProjection (phaseCoordinate ξ 0) M ν := by
    intro A hA
    exact hν A hA
  have hcancel := (block_interior_cancellation ξ 0 M F1 F2 Θ (blockMass Cstar 1 1)
    h q0 _ _ hMone hFsum hmap1 hmap2 hmass hΦ hf1 hf2 ν hphaseν).2
  exact hcancel.trans (sub_le_sub_left (min_le_left δ0 (1 / 2)) 1)

end HypoellipticAleksandrov.KineticAleksandrov.Decay

namespace HypoellipticAleksandrov.KineticAleksandrov.TheoremA
open MeasureTheory Set HypoellipticAleksandrov.KineticAleksandrov.SectionTwo HypoellipticAleksandrov.KineticAleksandrov.Green SectionTwo Evolution Parabolic Green
open scoped ENNReal NNReal Topology MatrixOrder Matrix.Norms.Elementwise


/-- The case-W starting state `(v,z) = (V,X)` of a kinetic point `P = (σ,X,V)`. -/
def kineticStartState (d : ℕ) (P : KineticPoint d) :
    EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) P.time :=
  ⟨(P.velocity, P.position), by
    rw [evolutionStateSet, movingDomain_wholeSpace]
    exact ⟨mem_univ _, mem_univ _⟩⟩

/-- The remaining time `S_P = s₀ + R² - s` of a point `P = (s,X,v)` in a forward cylinder
with bottom time `s₀ = Z₀.time`. -/
def remainingTime {d : ℕ} (Z₀ P : KineticPoint d) (R : ℝ) : ℝ := Z₀.time + R ^ 2 - P.time

/-- Forward cylinders are open, hence measurable. -/
theorem measurableSet_forwardCylinder' {d : ℕ} (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) :
    MeasurableSet (forwardCylinder Z₀ R hR) := by
  have ht : Continuous (@KineticPoint.time d) := continuous_time
  have hv : Continuous (@KineticPoint.velocity d) := continuous_velocity
  have hrel : Continuous (fun P : KineticPoint d => relativePosition Z₀ P) :=
    ((continuous_position.sub continuous_const).sub
      ((ht.sub continuous_const).smul continuous_const))
  exact ((isOpen_lt continuous_const ht).inter ((isOpen_lt ht continuous_const).inter
    (((PDE.isOpen_euclideanBall Z₀.velocity R).preimage hv).inter
      ((PDE.isOpen_euclideanBall 0 (R ^ 3)).preimage hrel)))).measurableSet


/-- **Conditional Theorem 1.1.**  See the module docstring.  The premise `hbounds`
is the conclusion of Lemma 5.1 for all case-W coefficients and realizing `(S,K)`, with
structural constants `C_γ, c` fixed first; `C = greenConstant d (p/(p-1)) C_γ` depends only on
`d, λ, Λ, p`. -/
theorem green_density_bound_of_slabFourierBounds {d : ℕ} (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (A : CoefficientField d),
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient (kineticReflectedCoefficient A)) (identityDrift d) S K →
      ∀ P ∈ forwardCylinder (kineticReflection P₀) R hR,
      ∀ ΓP : Measure (ElapsedTime (ENNReal.ofReal (remainingTime (kineticReflection P₀) P R)) ×
          EvolutionAmbientState d),
        IsGreenMeasure K P.time (ENNReal.ofReal (remainingTime (kineticReflection P₀) P R))
          (Measure.dirac (kineticStartState d P)) ΓP →
      ∃ G : KineticPoint d → ℝ≥0∞, Measurable G ∧
        (ΓP.map (greenKineticPoint d P.time)).restrict
            (forwardCylinder (kineticReflection P₀) R hR) =
          (volume.restrict (forwardCylinder (kineticReflection P₀) R hR)).withDensity G ∧
        eLpNorm G (ENNReal.ofReal (p / (p - 1)))
            (volume.restrict (forwardCylinder (kineticReflection P₀) R hR)) ≤
          ENNReal.ofReal (C * remainingTime (kineticReflection P₀) P R ^
            ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1)))) ∧
        C * remainingTime (kineticReflection P₀) P R ^
            ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1))) ≤
          C * R ^ (2 - (4 * (d : ℝ) + 2) / p)  := by
  have greenDelta_rpow_le {S : ℝ} {R : ℝ} (hS : 0 ≤ S) (hSR : S ≤ R ^ 2) (hR : 0 < R) :
      S ^ ((1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1))) ≤
      R ^ (2 - (4 * (d : ℝ) + 2) / p) := by
    have hd : 0 ≤ d := Nat.cast_nonneg d
    have hp0 : 0 < p := by linarith
    have hp1 : 0 < p - 1 := by linarith
    have he : (1 - 2 * (d : ℝ) * (p / (p - 1) - 1)) / (p / (p - 1)) = (p - 1 - 2 * d) / p := by
      field_simp
      ring
    have h2 : 2 - (4 * (d : ℝ) + 2) / p = 2 * ((p - 1 - 2 * d) / p) := by
      field_simp
      ring
    have hnn : 0 ≤ (p - 1 - 2 * d) / p := div_nonneg (by linarith) hp0.le
    rw [he, h2, Real.rpow_mul hR.le]
    calc S ^ ((p - 1 - 2 * (d : ℝ)) / p) ≤ (R ^ 2) ^ ((p - 1 - 2 * (d : ℝ)) / p) :=
          Real.rpow_le_rpow hS hSR hnn
      _ = (R ^ (2 : ℝ)) ^ ((p - 1 - 2 * (d : ℝ)) / p) := by
          rw [Real.rpow_two]
  obtain ⟨Cγ, c, hb⟩ := hbounds
  have hd0 : 1 ≤ d := by exact_mod_cast hd
  have hp1 : 0 < p - 1 := by linarith
  have hp0 : 0 < p := by linarith
  have hq : 1 < p / (p - 1) := by
    rw [lt_div_iff₀ hp1]
    linarith
  have hqd : p / (p - 1) < 1 + 1 / (2 * (d : ℝ)) := by
    have h : p / (p - 1) = 1 + 1 / (p - 1) := by field_simp; ring
    rw [h]
    have : 1 / (p - 1) < 1 / (2 * (d : ℝ)) :=
      one_div_lt_one_div_of_lt (by positivity) (by linarith)
    linarith
  refine ⟨((greenConstant d (p / (p - 1)) Cγ : ℝ≥0) : ℝ), NNReal.coe_nonneg _, ?_⟩
  intro P₀ R hR A hsm hsymm hlo hhi S K hreal P hP ΓP hΓP
  have hP' := (mem_forwardCylinder_iff _ _ _ hR).1 hP
  have hSP : 0 < remainingTime (kineticReflection P₀) P R := by
    unfold remainingTime
    linarith [hP'.2.1]
  have hSR : remainingTime (kineticReflection P₀) P R < R ^ 2 := by
    unfold remainingTime
    linarith [hP'.1]
  have hset := (caseW_sourceSetting hlam hLam hsm hsymm hlo hhi).1
  let μ : Measure (EvolutionState (wholeSpace d) (fun _ => 0) P.time) :=
    Measure.dirac (kineticStartState d P)
  have hΓ := greenMeasure_spec K P.time ⊤ (by simp) μ
  have hbd := hb _ hset S K hreal P.time μ _ hΓ
  obtain ⟨G₀, hG₀m, hΓP', hnorm⟩ := green_density_of_slab_marginals Cγ c K P.time μ _ hΓ hbd
    hq hqd hSP ΓP hΓP
  obtain ⟨hGm, hGden, hGnorm⟩ := greenKineticPoint_density P.time _ ΓP G₀ hG₀m hΓP'
    (measurableSet_forwardCylinder' (kineticReflection P₀) R hR)
  refine ⟨_, hGm, hGden, ?_, ?_⟩
  · refine (hGnorm _).trans (hnorm.trans (le_of_eq ?_))
    have hμ : μ Set.univ = 1 := measure_univ
    rw [hμ, mul_one, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    rfl
  · exact mul_le_mul_of_nonneg_left
      (greenDelta_rpow_le hSP.le hSR.le hR) (NNReal.coe_nonneg _)

variable {d : ℕ}

/-- Whole-space Green measure ending at the cylinder's terminal time, in absolute coordinates. -/
def cylinderGreenMeasure
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (P : KineticPoint d) :
    Measure (KineticPoint d) :=
  if h : P.time < Z₀.time + R ^ 2 then
    ((greenMeasure K P.time (ENNReal.ofReal (Z₀.time + R ^ 2 - P.time))
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr h))
      (Measure.dirac (kineticStartState d P))).map (greenKineticPoint d P.time)).restrict
      (forwardCylinder Z₀ R hR)
  else 0


variable {d : ℕ}

/-- The Green source integral has the regularity, sign and equation required by abstract ABP. -/
theorem green_potentials (hH : HormanderHypoellipticityStatement)
    {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam)
    (B : CoefficientField d) (hB : IsSmoothCoefficient B)
    (hBs : IsSymmetricCoefficient B) (hlo : HasLowerEllipticity lam B)
    (hhi : HasUpperEllipticity Lam B)
    (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
    (hreal : RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
      MeasurableSet.univ (zIndependentCoefficient B) (identityDrift d) S K)
    (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R)
    (g : KineticPoint d → ℝ)
    (hgs : ContDiff ℝ (⊤ : ℕ∞) (fun z => g ((KineticPoint.equivProd d).symm z)))
    (hgc : HasCompactSupport g) (hgQ : tsupport g ⊆ forwardCylinder Z₀ R hR)
    (hg0 : ∀ P, 0 ≤ g P) :
    IsKineticC112On (fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P)
        (forwardCylinder Z₀ R hR) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        0 ≤ ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) ∧
      (∀ P ∈ forwardCylinder Z₀ R hR,
        forwardKineticOperator (ofTimeVelocityCoefficient B)
          (fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) P = -g P)  := by
  have integral_cylinderGreenMeasure (Z₀ : KineticPoint d) (R : ℝ) (hR : 0 < R) (g : KineticPoint d → ℝ) (hg0 : ∀ P, 0 ≤ g P) (hg : Continuous g) (hgc : HasCompactSupport g) (hgQ : tsupport g ⊆ forwardCylinder Z₀ R hR) (P : KineticPoint d) (hP : P.time < Z₀.time + R ^ 2) :
      (∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P) =
      duhamelPotential K (Z₀.time + R ^ 2) (g ∘ sectionTwoPoint) (sectionTwoPoint P) := by
    classical
    rw [cylinderGreenMeasure, dite_eq_left hP]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz =>
      image_eq_zero_of_notMem_tsupport (fun h => hz (hgQ h)))]
    rw [(measurableEmbedding_greenKineticPoint d P.time _).integral_map]
    symm
    have hgg : Continuous (g ∘ sectionTwoPoint) := hg.comp (continuous_sectionTwoPoint d)
    have hcc := hasCompactSupport_sectionTwoPoint hgc
    exact duhamelPotential_eq_green K MeasurableSet.univ continuous_const
      (Z₀.time + R ^ 2) (g ∘ sectionTwoPoint) (fun q => hg0 _) hgg hcc P.time hP
      (kineticStartState d P) _
      (greenMeasure_spec K P.time _ _ (Measure.dirac (kineticStartState d P)))
  let T := Z₀.time + R ^ 2
  let g₂ := g ∘ sectionTwoPoint
  let W := duhamelPotential K T g₂
  let V := W ∘ sectionTwoPoint
  let F := fun P => ∫ z, g z ∂cylinderGreenMeasure K Z₀ R hR P
  have hg : Continuous g := by
    have heq : (fun P => g ((KineticPoint.equivProd d).symm
        ((KineticPoint.homeomorphProd d) P))) = g := by
      funext P
      rfl
    rw [← heq]
    exact hgs.continuous.comp (KineticPoint.homeomorphProd d).continuous
  have hg₂ : Continuous g₂ := hg.comp (continuous_sectionTwoPoint d)
  have hgc₂ : HasCompactSupport g₂ := hasCompactSupport_sectionTwoPoint hgc
  have hgs₂ := contDiff_sectionTwoPoint_source hgs
  have hg₂0 : ∀ P, 0 ≤ g₂ P := fun P => hg0 _
  have hgU : tsupport g₂ ⊆ evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T := by
    intro P hP
    have hp := hgQ ((tsupport_comp_subset_preimage g (continuous_sectionTwoPoint d)) hP)
    have ht := ((mem_forwardCylinder_iff _ _ _ hR).1 hp).2.1
    exact ⟨ht, by simp [movingDomain_wholeSpace]⟩
  have hcoeff : IsSectionTwoCoefficient lam Lam B :=
    ⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent hB, hBs, hlo, hhi⟩
  obtain ⟨hfull, hsym, hell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hcoeff
  have hW := duhamelPotential_contDiffOn hH (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (zIndependentCoefficient B) (identityDrift d)
    S K hreal hfull hsym (identityDrift_smooth d) g₂ hg₂0 hg₂ hgc₂ hgs₂ T hgU
    hlam (by norm_num : (0 : ℝ) < 1) hell (identityDrift_bounds d).2
  have hEQ := duhamelPotential_source_equation hH (wholeSpace_admissible d)
    MeasurableSet.univ continuous_const (zIndependentCoefficient B) (identityDrift d)
    S K hreal hfull hsym (identityDrift_smooth d) g₂ hg₂0 hg₂ hgc₂ hgs₂ T hgU
    hlam (by norm_num : (0 : ℝ) < 1) hell (identityDrift_bounds d).2
  have heq : ∀ P, P.time < T → F P = V P :=
    fun P hP => integral_cylinderGreenMeasure Z₀ R hR g hg0 hg hgc hgQ P hP
  have hQ := isOpen_forwardCylinder Z₀ R hR
  have hQt : ∀ P ∈ forwardCylinder Z₀ R hR, P.time < T :=
    fun P hP => ((mem_forwardCylinder_iff _ _ _ hR).1 hP).2.1
  let swap : EvolutionVec d → EvolutionVec d := fun x =>
    packPoint (timeCoord d x) (transportedCoord d x) (diffusedCoord d x)
  have hswap : ContDiff ℝ (⊤ : ℕ∞) swap := by
    exact (evolutionProdCLE d).symm.contDiff.comp
      ((Evolution.timeCoord d).contDiff.prodMk
        ((transportedCoord d).contDiff.prodMk (diffusedCoord d).contDiff))
  have hmap : MapsTo swap (evolutionHomeomorph d ⁻¹' forwardCylinder Z₀ R hR)
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder (wholeSpace d) (fun _ => 0) T) := by
    intro x hx
    refine ⟨?_, by simp [movingDomain_wholeSpace]⟩
    simpa [swap] using hQt _ hx
  have hV : ContDiffOn ℝ (⊤ : ℕ∞) (V ∘ evolutionHomeomorph d)
      (evolutionHomeomorph d ⁻¹' forwardCylinder Z₀ R hR) := by
    have hv := hW.comp hswap.contDiffOn hmap
    convert hv using 1
    funext x
    simp [V, W, swap, evolutionHomeomorph_apply, timeCoord_packPoint, diffusedCoord_packPoint, transportedCoord_packPoint]
    rfl
  have hF := hV.congr (fun x hx => heq _ (hQt _ hx))
  refine ⟨isKineticC112On_of_contDiffOn hQ hF, ?_, ?_⟩
  · intro P hP
    exact integral_nonneg hg0
  · intro P hP
    have hn : F =ᶠ[𝓝 P] V := by
      filter_upwards [((isOpen_lt continuous_time continuous_const).mem_nhds (hQt P hP))]
        with z hz
      exact heq z hz
    rw [forwardKineticOperator_eq_of_eventuallyEq _ hn,
      forwardKineticOperator_eq_lop_identity]
    have hw : V ∘ sectionTwoPoint = W := by
      funext q
      rfl
    rw [hw]
    exact hEQ _ ⟨hQt P hP, by simp [movingDomain_wholeSpace]⟩

variable {d : ℕ}

/-- The localized smooth estimate, with its constant fixed before all coefficient and PDE data. -/
theorem smooth_estimate_of_slabFourierBounds (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hH : HormanderHypoellipticityStatement)
    (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ)
    (hevolution : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : CoefficientField d),
      IsSmoothCoefficient A → IsSymmetricCoefficient A →
      HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (u f : KineticPoint d → ℝ),
      ContinuousOn u (closure (backwardCylinder P₀ R)) →
      IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
      MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) →
      (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
      ∀ P ∈ closure (backwardCylinder P₀ R),
      u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
        C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
          (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
            (ENNReal.ofReal p) (volume.restrict (backwardCylinder P₀ R))).toReal  := by
  have ellipticity_of_smooth_ae {d : ℕ} {lam : ℝ} {Lam : ℝ} {A : CoefficientField d} (hA : IsSmoothCoefficient A) (hlo : HasLowerEllipticityAE lam A) (hhi : HasUpperEllipticityAE Lam A) :
      HasLowerEllipticity lam A ∧ HasUpperEllipticity Lam A := by
    have upperEllipticity_of_continuous_ae {Lam : ℝ} {A : CoefficientField d} (hA : IsContinuousCoefficient A) (hhi : HasUpperEllipticityAE Lam A) :
        HasUpperEllipticity Lam A := by
      have hc : IsClosed {z : ℝ × PDE.Vec d | coefficientAt A z ≤ Lam • (1 : PDE.Mat d)} :=
        isClosed_le hA continuous_const
      have hd := (volume : Measure (ℝ × PDE.Vec d)).dense_of_ae hhi
      intro t v
      exact hc.closure_subset (hd (t, v))
    have lowerEllipticity_of_continuous_ae {lam : ℝ} {A : CoefficientField d} (hA : IsContinuousCoefficient A) (hlo : HasLowerEllipticityAE lam A) :
        HasLowerEllipticity lam A := by
      have hc : IsClosed {z : ℝ × PDE.Vec d | lam • (1 : PDE.Mat d) ≤ coefficientAt A z} :=
        isClosed_le continuous_const hA
      have hd := (volume : Measure (ℝ × PDE.Vec d)).dense_of_ae hlo
      intro t v
      exact hc.closure_subset (hd (t, v))
    exact ⟨lowerEllipticity_of_continuous_ae hA.continuous hlo,
      upperEllipticity_of_continuous_ae hA.continuous hhi⟩
  obtain ⟨C, hC, hgreen⟩ := green_density_bound_of_slabFourierBounds hd lam Lam p
    hlam hLam hp hbounds
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp1 : 1 < p := by linarith
  let q := p / (p - 1)
  have hq : 1 < q := by
    dsimp only [q]
    rw [lt_div_iff₀ (by linarith : 0 < p - 1)]
    linarith
  have hqp : q / (q - 1) = p := by
    apply (div_eq_iff (by linarith : q - 1 ≠ 0)).mpr
    dsimp only [q]
    field_simp [sub_ne_zero.mpr hp1.ne']
    ring
  refine ⟨C + 1, by positivity, ?_⟩
  intro A hAs hsym hloAE hhiAE P₀ R hR u f hcont hreg hf hLp hsub P hP
  obtain ⟨hlo, hhi⟩ := ellipticity_of_smooth_ae hAs hloAE hhiAE
  let B := kineticReflectedCoefficient A
  have hBs := isSmoothCoefficient_kineticReflectedCoefficient A hAs
  have hBsym := isSymmetricCoefficient_kineticReflectedCoefficient A hsym
  have hBlo : HasLowerEllipticity lam B := fun t v => hlo (-t) v
  have hBhi : HasUpperEllipticity Lam B := fun t v => hhi (-t) v
  obtain ⟨S, K, hreal⟩ := hevolution B
    ⟨hlam, hLam, isSmoothFullKineticCoefficient_zIndependent hBs, hBsym, hBlo, hBhi⟩
  let Z₀ := kineticReflection P₀
  let Q := forwardCylinder Z₀ R hR
  let Γ := cylinderGreenMeasure K Z₀ R hR
  let U := u ∘ kineticReflection
  let g₀ := (fun P => max (f P) 0) ∘ kineticReflection
  let α := 2 - (4 * (d : ℝ) + 2) / p
  have hRp : 0 < R ^ α := Real.rpow_pos_of_pos hR _
  have hKpos : 0 < (C + 1) * R ^ α := mul_pos (by positivity) hRp
  have hAc : ContinuousOn (fun P : KineticPoint d =>
      (ofTimeVelocityCoefficient B) P.time P.position P.velocity) Q :=
    (hBs.continuous.comp (continuous_time.prodMk continuous_velocity)).continuousOn
  have hApos : ∀ P ∈ Q,
      ((ofTimeVelocityCoefficient B) P.time P.position P.velocity).PosSemidef :=
    fun P _ => (posDef_of_loewner_lower hlam (hBlo P.time P.velocity)).posSemidef
  have hpotential := green_potentials hH hlam hLam B hBs hBsym hBlo hBhi S K hreal Z₀ R hR
  have hdensity : ∀ P ∈ Q, ∃ G : KineticPoint d → ℝ, Measurable G ∧
      (∀ z, 0 ≤ G z) ∧ Γ P = (volume.restrict Q).withDensity (fun z => ENNReal.ofReal (G z)) ∧
      (eLpNorm G (ENNReal.ofReal q) (volume.restrict Q)).toReal ≤ (C + 1) * R ^ α ∧
      MemLp G (ENNReal.ofReal q) (volume.restrict Q) := by
    intro P hP
    have ht := ((mem_forwardCylinder_iff Z₀ P R hR).1 hP).2.1
    let GP := greenMeasure K P.time (ENNReal.ofReal (remainingTime Z₀ P R))
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    have hGP := greenMeasure_spec K P.time _
      (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht)) (Measure.dirac (kineticStartState d P))
    obtain ⟨G, hG, hden, hnorm, hscale⟩ := hgreen P₀ R hR A hAs hsym hlo hhi S K hreal P hP
      GP hGP
    have hnorm' : eLpNorm G (ENNReal.ofReal q) (volume.restrict Q) ≤
        ENNReal.ofReal (C * R ^ α) := hnorm.trans (ENNReal.ofReal_le_ofReal hscale)
    have hden' : Γ P = (volume.restrict Q).withDensity G := by
      dsimp only [Γ, cylinderGreenMeasure]
      rw [dite_eq_left ht]
      convert hden using 1
      rfl
    obtain ⟨F, hFm, hFn, hFd, hFN, hFLp⟩ := real_density_of_eLpNorm_bound
      (volume.restrict Q) (Γ P) G hG hden' q (C * R ^ α) (lt_trans zero_lt_one hq)
      (mul_nonneg hC hRp.le) hnorm'
    refine ⟨F, hFm, hFn, hFd, hFN.trans ?_, hFLp⟩
    exact mul_le_mul_of_nonneg_right (by linarith) hRp.le
  have hmp := measurePreserving_reflection_forward P₀ R hR
  have hUc : ContinuousOn U (closure Q) := by
    have hc := hcont.comp (continuous_kineticReflection d).continuousOn
      (fun x hx => hx : MapsTo kineticReflection
        (kineticReflection ⁻¹' closure (backwardCylinder P₀ R)) _)
    simpa only [preimage_closure_backwardCylinder_reflection P₀ R hR] using hc
  have hUr : IsKineticC112On U Q := by
    simpa only [preimage_backwardCylinder_reflection P₀ R hR] using
      isKineticC112On_kineticReflection u (backwardCylinder P₀ R) hreg
  have hgLp : MemLp g₀ (ENNReal.ofReal (q / (q - 1))) (volume.restrict Q) := by
    rw [hqp]
    exact hLp.comp_measurePreserving hmp
  have hUs : ∀ᵐ P ∂volume.restrict Q,
      -g₀ P ≤ forwardKineticOperator (ofTimeVelocityCoefficient B) U P := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsub] with P hP
    rw [reflectedKineticOperator_reflection]
    exact neg_le_neg (hP.trans (le_max_left _ _))
  have hbound := kinetic_abp_abstract_of_continuous Z₀ R hR (ofTimeVelocityCoefficient B)
    hAc hApos q hq ((C + 1) * R ^ α) hKpos Γ hpotential hdensity U g₀ hUc hUr
    (fun P _ => le_max_right _ _) hgLp hUs
  have hPr : kineticReflection P ∈ closure Q := by
    rw [← preimage_closure_backwardCylinder_reflection P₀ R hR]
    change kineticReflection (kineticReflection P) ∈ closure (backwardCylinder P₀ R)
    rw [kineticReflection_involutive P]
    exact hP
  have hresult := hbound (kineticReflection P) hPr
  have hnorm : eLpNorm ({P | 0 < U P}.indicator g₀) (ENNReal.ofReal p)
      (volume.restrict Q) =
      eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0)) (ENNReal.ofReal p)
        (volume.restrict (backwardCylinder P₀ R)) := by
    have hset : MeasurableSet (backwardCylinder P₀ R ∩ {P | 0 < u P}) :=
      (hreg.continuousOn.isOpen_inter_preimage (isOpen_backwardCylinder P₀ R hR)
        isOpen_Ioi).measurableSet
    have hEq : (backwardCylinder P₀ R ∩ {P | 0 < u P}).indicator
        (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
        {P | 0 < u P}.indicator (fun P => max (f P) 0) := by
      filter_upwards [ae_restrict_mem (isOpen_backwardCylinder P₀ R hR).measurableSet]
        with P hP
      simp [indicator, hP]
    have hL := (hLp.indicator hset).ae_eq hEq
    have hfun : {P | 0 < U P}.indicator g₀ =
        ({P | 0 < u P}.indicator (fun P => max (f P) 0)) ∘ kineticReflection := rfl
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hL.aestronglyMeasurable hmp
  rw [hqp, hnorm, boundarySup_reflection P₀ R hR u] at hresult
  simpa [U, kineticReflection_involutive P] using hresult

end HypoellipticAleksandrov.KineticAleksandrov.TheoremA

section



namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open Set MeasureTheory HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open scoped ProbabilityTheory MatrixOrder

/-- The iteration input is exactly the shared terminal evolution statement. -/
theorem iterationEvolutionStatement_of_conclusion (h : TerminalEvolutionConclusion) :
    Decay.IterationEvolutionStatement := h

/-- The occupation input is exactly the shared terminal evolution statement. -/
theorem occupationEvolutionStatement_of_conclusion (h : TerminalEvolutionConclusion) :
    Occupation.TerminalEvolutionStatement := h

/-- The premise of Theorem A follows by whole-space identity-drift specialization. -/
theorem taAssemblyEvolution_of_conclusion (h : TerminalEvolutionConclusion)
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam) :
    ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
          (zIndependentCoefficient B) σ y z = (zIndependentCoefficient B) σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
            MeasurableSet.univ K) ∧
        IsDomainMonotoneEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient B) (identityDrift d) K ∧
        HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K := by
  intro B hB
  obtain ⟨hBs, hBsym, hBell⟩ := sectionTwoCoefficient_fullBounds lam Lam B hB
  have hb := identityDrift_bounds d
  obtain ⟨S, K, hc, -, -, -, -, hi, -, -, -, -, he, hcomp, hcov, hmono, hpar⟩ :=
    h d hd lam Lam 1 1 hlam hlamLam one_pos le_rfl (wholeSpace d) (fun _ => 0)
      (zIndependentCoefficient B) (identityDrift d) (wholeSpace_admissible d)
      (zeroCurve_piecewiseC1 d) hBs hBsym hBell (identityDrift_smooth d) hb.1 hb.2
  exact ⟨S, K, ⟨hc, hi, he, hcomp⟩, hcov, hmono, hpar⟩

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory SectionTwo Green Parabolic TheoremA HypoellipticAleksandrov Autonomous Holder HypoellipticAleksandrov.Parabolic
open scoped ENNReal NNReal MatrixOrder ProbabilityTheory



/-- The time--velocity conclusion assembled from the terminal evolution and the two analytic
hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_of_terminalEvolution
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hEv : SectionTwo.TerminalEvolutionConclusion)
    (hH : HormanderHypoellipticityStatement) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal  := by
  have kinetic_aleksandrov_timeVelocity_of_slabFourierBounds (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ) (hevolution : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
          (zIndependentCoefficient B) σ y z = (zIndependentCoefficient B) σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
            MeasurableSet.univ K) ∧
        IsDomainMonotoneEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient B) (identityDrift d) K ∧
        HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K) :
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (fun P => max (f P) 0) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
    have he : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
        ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
          (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
          RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
            (zIndependentCoefficient B) (identityDrift d) S K := by
      intro B hB
      obtain ⟨S, K, hreal, hcov, hmono, hpar⟩ := hevolution B hB
      have _ := hcov
      have _ := hmono
      have _ := hpar
      exact ⟨S, K, hreal⟩
    obtain ⟨C, hC, hsmooth⟩ := smooth_estimate_of_slabFourierBounds hd lam Lam p
      hlam hLam hp hH hbounds he
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hp1 : 1 ≤ p := by linarith
    have hfull : ∀ A : CoefficientField d,
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
        ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
        ∀ u f : KineticPoint d → ℝ,
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (borelSource false u f) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
      intro A hAs hsym hlo hhi P₀ R hR u f hc hr hf hLp hsub P hP
      have hloAE : HasLowerEllipticityAE lam A :=
        Filter.Eventually.of_forall (fun z => hlo z.1 z.2)
      have hhiAE : HasUpperEllipticityAE Lam A :=
        Filter.Eventually.of_forall (fun z => hhi z.1 z.2)
      have hbound := hsmooth A hAs hsym hloAE hhiAE P₀ R hR u f hc hr hf hLp hsub P hP
      apply hbound.trans
      apply add_le_add_right
      apply mul_le_mul_of_nonneg_left
      · simpa [borelSource, Bool.false_eq_true] using
          localized_positive_source_norm_le volume (isOpen_backwardCylinder P₀ R hR)
          u f hr.continuousOn (ENNReal.ofReal p) hLp
      · exact mul_nonneg hC (Real.rpow_nonneg hR.le _)
    refine ⟨C, hC, ?_⟩
    intro P₀ R hR A hBorel hsym hlo hhi f u hf hc hr hsub hLp P hP
    have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
    let f₀ := (backwardCylinder P₀ R).indicator f
    have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
    have hae := source_indicator_ae_eq hQ f
    have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
        (fun P => max (f₀ P) 0) := by
      filter_upwards [hae] with P hP
      change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
      rw [hP]
    have hLp₀ := hLp.ae_eq hmax
    have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f₀ P := by
      filter_upwards [hsub, hae] with P hsub hEq
      change backwardOperatorOfTimeVelocityCoefficient A u P ≤
        (backwardCylinder P₀ R).indicator f P
      rw [hEq]
      exact hsub
    have hbound := kinetic_abp_smooth_to_borel lam Lam hlam hLam p hp1
      (2 - (4 * (d : ℝ) + 2) / p) C false hfull A hBorel hsym hlo hhi
      P₀ R hR u f₀ hc hr hf₀ hLp₀ hsub₀ P hP
    simpa [f₀, borelSource, Bool.false_eq_true, eLpNorm_positive_source_indicator hQ f] using hbound
  have hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
  have hOcc := Occupation.parabolicOccupationFamily_holds
    (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam
  have hBlock := Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam
  have hDecay := Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter hBlock
  exact kinetic_aleksandrov_timeVelocity_of_slabFourierBounds
    (Green.slabFourierBounds_of_occupation_decay hd lam Lam hOcc hDecay)
    (SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam)




/-- The localized conclusion assembled from evolution and the two analytic hypotheses. -/
theorem kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    (d : ℕ) (hd : 1 ≤ d) (lam Lam p : ℝ)
    (hlam : 0 < lam) (hLam : lam ≤ Lam) (hp : 2 * (d : ℝ) + 1 < p)
    (hEv : SectionTwo.TerminalEvolutionConclusion)
    (hH : HormanderHypoellipticityStatement) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal  := by
  have kinetic_aleksandrov_timeVelocity_localised_of_slabFourierBounds (hbounds : ∃ (C : ℝ → ℝ≥0) (c : ℝ), ∀ (B : CoefficientField d),
      IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
      RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
        (zIndependentCoefficient B) (identityDrift d) S K →
      ∀ (σ₀ : ℝ) (μ : Measure (EvolutionState (wholeSpace d) (fun _ => (0 : PDE.Vec d)) σ₀))
        [IsFiniteMeasure μ] (Γ : Measure (GreenCarrier d)), IsGreenMeasure K σ₀ ⊤ μ Γ →
      ∀ T : ℝ, 0 < T → SlabFourierBounds d C c (μ univ) T Γ) (hevolution : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
      ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
        (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
        RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
          (zIndependentCoefficient B) (identityDrift d) S K ∧
        (∀ (hBz : ∀ (σ : ℝ) (y z z' : PDE.Vec d),
          (zIndependentCoefficient B) σ y z = (zIndependentCoefficient B) σ y z'),
          let _ := hBz
          IsTranslationCovariantEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
            MeasurableSet.univ K) ∧
        IsDomainMonotoneEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          (zIndependentCoefficient B) (identityDrift d) K ∧
        HasParabolicMarginalBundle (wholeSpace d) (fun _ => (0 : PDE.Vec d))
          MeasurableSet.univ (zIndependentCoefficient B) K) :
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
      ∀ (A : CoefficientField d),
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (f u : KineticPoint d → ℝ),
        Measurable (fun P : backwardCylinder P₀ R => f P) →
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        Parabolic.IsKineticC112On u (backwardCylinder P₀ R) →
        (∀ᵐ P ∂(volume.restrict (backwardCylinder P₀ R)),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        ∀ P ∈ closure (backwardCylinder P₀ R),
          u P ≤ sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm ({P | 0 < u P}.indicator (fun P => max (f P) 0))
                (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
    have he : ∀ B : CoefficientField d, IsSectionTwoCoefficient lam Lam B →
        ∃ (S : TerminalOperatorFamily (wholeSpace d) (fun _ => (0 : PDE.Vec d)))
          (K : MovingFiberKernel (wholeSpace d) (fun _ => (0 : PDE.Vec d))),
          RealizesTerminalEvolution (wholeSpace d) (fun _ => (0 : PDE.Vec d)) MeasurableSet.univ
            (zIndependentCoefficient B) (identityDrift d) S K := by
      intro B hB
      obtain ⟨S, K, hreal, hcov, hmono, hpar⟩ := hevolution B hB
      have _ := hcov
      have _ := hmono
      have _ := hpar
      exact ⟨S, K, hreal⟩
    obtain ⟨C, hC, hsmooth⟩ := smooth_estimate_of_slabFourierBounds hd lam Lam p
      hlam hLam hp hH hbounds he
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have hp1 : 1 ≤ p := by linarith
    have hfull : ∀ A : CoefficientField d,
        IsSmoothCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticity lam A → HasUpperEllipticity Lam A →
        ∀ (P₀ : KineticPoint d) (R : ℝ), 0 < R →
        ∀ u f : KineticPoint d → ℝ,
        ContinuousOn u (closure (backwardCylinder P₀ R)) →
        IsKineticC112On u (backwardCylinder P₀ R) → Measurable f →
        MemLp (fun P => max (f P) 0) (ENNReal.ofReal p)
          (volume.restrict (backwardCylinder P₀ R)) →
        (∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
          backwardOperatorOfTimeVelocityCoefficient A u P ≤ f P) →
        ∀ P ∈ closure (backwardCylinder P₀ R), u P ≤
          sSup ((fun P => max (u P) 0) '' kineticBoundary P₀ R) +
            C * R ^ (2 - (4 * (d : ℝ) + 2) / p) *
              (eLpNorm (borelSource true u f) (ENNReal.ofReal p)
                (volume.restrict (backwardCylinder P₀ R))).toReal := by
      intro A hAs hsym hlo hhi P₀ R hR u f hc hr hf hLp hsub P hP
      have hloAE : HasLowerEllipticityAE lam A :=
        Filter.Eventually.of_forall (fun z => hlo z.1 z.2)
      have hhiAE : HasUpperEllipticityAE Lam A :=
        Filter.Eventually.of_forall (fun z => hhi z.1 z.2)
      simpa [borelSource] using
        hsmooth A hAs hsym hloAE hhiAE P₀ R hR u f hc hr hf hLp hsub P hP
    refine ⟨C, hC, ?_⟩
    intro P₀ R hR A hBorel hsym hlo hhi f u hf hc hr hsub hLp P hP
    have hQ := (isOpen_backwardCylinder P₀ R hR).measurableSet
    let f₀ := (backwardCylinder P₀ R).indicator f
    have hf₀ : Measurable f₀ := measurable_source_indicator hQ f hf
    have hae := source_indicator_ae_eq hQ f
    have hmax : (fun P => max (f P) 0) =ᵐ[volume.restrict (backwardCylinder P₀ R)]
        (fun P => max (f₀ P) 0) := by
      filter_upwards [hae] with P hP
      change max (f P) 0 = max ((backwardCylinder P₀ R).indicator f P) 0
      rw [hP]
    have hLp₀ := hLp.ae_eq hmax
    have hsub₀ : ∀ᵐ P ∂volume.restrict (backwardCylinder P₀ R),
        backwardOperatorOfTimeVelocityCoefficient A u P ≤ f₀ P := by
      filter_upwards [hsub, hae] with P hsub hEq
      change backwardOperatorOfTimeVelocityCoefficient A u P ≤
        (backwardCylinder P₀ R).indicator f P
      rw [hEq]
      exact hsub
    have hbound := kinetic_abp_smooth_to_borel lam Lam hlam hLam p hp1
      (2 - (4 * (d : ℝ) + 2) / p) C true hfull A hBorel hsym hlo hhi
      P₀ R hR u f₀ hc hr hf₀ hLp₀ hsub₀ P hP
    simpa [f₀, borelSource, eLpNorm_localized_source_indicator hQ f u] using hbound
  have hIter := SectionTwo.iterationEvolutionStatement_of_conclusion hEv
  have hOcc := Occupation.parabolicOccupationFamily_holds
    (SectionTwo.occupationEvolutionStatement_of_conclusion hEv) hH hd lam Lam hlam hLam
  have hBlock := Decay.unit_frequency_block_W hIter d hd lam Lam hlam hLam
  have hDecay := Decay.fourierDecayFamily_of_unitBlock d hd lam Lam hlam hLam hIter hBlock
  exact kinetic_aleksandrov_timeVelocity_localised_of_slabFourierBounds
    (Green.slabFourierBounds_of_occupation_decay hd lam Lam hOcc hDecay)
    (SectionTwo.taAssemblyEvolution_of_conclusion hEv d hd lam Lam hlam hLam)


/-- Companion paper, Corollary 9.9, with no extra hypotheses. -/
theorem kinetic_holder_timeVelocity_proof
    (d : ℕ) (hd : 1 ≤ d) (lam Lam : ℝ) (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha ≤ 1 ∧
      ∀ A : CoefficientField d,
        IsBorelCoefficient A → IsSymmetricCoefficient A →
        HasLowerEllipticityAE lam A → HasUpperEllipticityAE Lam A →
      ∀ (Omega : Set (KineticPoint d)), IsOpen Omega →
      ∀ (u : KineticPoint d → ℝ),
        (∃ M : ℝ, ∀ P ∈ Omega, |u P| ≤ M) →
        Parabolic.IsKineticC112On u Omega →
        (∀ᵐ P ∂(volume.restrict Omega),
          backwardOperatorOfTimeVelocityCoefficient A u P = 0) →
      ∀ (K : Set (KineticPoint d)), K ⊆ Omega → IsCompact K →
      ∀ (R₀ : ℝ), 0 < R₀ →
        (∀ P ∈ K, closure (backwardCylinder P (2 * R₀)) ⊆ Omega) →
      ∀ P ∈ K, ∀ P' ∈ K,
        |u P - u P'| ≤ C * oscillationOn u (holderNeighbourhood R₀ K) *
          (quasiDistance P P' / R₀) ^ alpha := by
  let p : ℝ := 2 * (d : ℝ) + 2
  obtain ⟨C_A, _, hest⟩ := kinetic_aleksandrov_timeVelocity_localised_of_terminalEvolution
    d hd lam Lam p hlam hLam (by linarith)
    (exists_terminalEvolution_of_classical liebermanEllipsoidDirichletStatement_holds
      hormanderHypoellipticityStatement_holds) hormanderHypoellipticityStatement_holds
  obtain ⟨alpha, C, ha, ha1, hholder⟩ := kinetic_holder_of_aleksandrov_aux d hd lam Lam p C_A
    hlam hLam (by linarith [Nat.cast_nonneg (α := ℝ) d, show p = 2 * (d : ℝ) + 2 from rfl])
  refine ⟨alpha, C, ha, ha1, fun A hB hS hL hU Omega hOmega u hbounded hu heq => ?_⟩
  have hop_lin {w : KineticPoint d → ℝ} {D : Set (KineticPoint d)}
      (hw : Parabolic.IsKineticC112On w D) (c : ℝ) {P : KineticPoint d} (hP : P ∈ D) :
      backwardOperatorOfTimeVelocityCoefficient A (fun Q => c * w Q) P =
        c * backwardOperatorOfTimeVelocityCoefficient A w P := by
    have ht : kineticTimeDerivative (fun Q => c * w Q) P = c * kineticTimeDerivative w P :=
      deriv_const_mul c (hw.timeSlice_differentiableAt hP)
    have hx : kineticPositionGradient (fun Q => c * w Q) P = c • kineticPositionGradient w P :=
      classicalGradient_const_mul c ((hw.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
    simp [backwardOperatorOfTimeVelocityCoefficient_apply, ht, hx, kineticVelocityHessian_eq_sliceHessian, sliceHessian_const_mul c (hw.velocitySlice_contDiffAt hP), matrixContraction_smul_right, PDE.vecDot, mul_sub, mul_add, Finset.mul_sum, mul_left_comm _ c]
  have hsup (w : KineticPoint d → ℝ) (hw : Parabolic.IsKineticC112On w Omega)
      (heqw : ∀ᵐ P ∂volume.restrict Omega, backwardOperatorOfTimeVelocityCoefficient A w P = 0) :
      IsAdmissibleSupersolution (ofTimeVelocityCoefficient A) Omega p C_A w := by
    refine ⟨hw.continuousOn, fun P₀ R hR hQ psi hpsi => ?_⟩
    let Q := backwardCylinder P₀ R
    have hQo := isOpen_backwardCylinder P₀ R hR
    obtain ⟨U, hUo, hUQ, hs⟩ := hpsi
    have hps : Parabolic.IsKineticC112On psi U :=
      TheoremA.isKineticC112On_of_contDiffOn hUo
        (hs.comp (Evolution.evolutionProdCLE d).contDiff.contDiffOn fun x hx =>
          ⟨Evolution.evolutionHomeomorph d x, hx, rfl⟩)
    have hQQ : Q ⊆ Omega := subset_closure.trans hQ
    have hpr := comparison_regular_mono hps (subset_closure.trans hUQ)
    have hwr := comparison_regular_mono hw hQQ
    have hneg := comparison_regular_const_mul hwr (-1)
    have hdiff : Parabolic.IsKineticC112On (fun P => psi P - w P) Q := by
      simpa only [neg_one_mul, sub_eq_add_neg] using comparison_regular_add hpr hneg
    have hop : ∀ᵐ P ∂volume.restrict Q,
        backwardOperatorOfTimeVelocityCoefficient A (fun z => psi z - w z) P ≤
          backwardOperatorOfTimeVelocityCoefficient A psi P := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hQQ heqw,
        ae_restrict_mem hQo.measurableSet] with P he hP
      have hadd : backwardOperatorOfTimeVelocityCoefficient A (fun z => psi z - w z) P =
          backwardOperatorOfTimeVelocityCoefficient A psi P +
            backwardOperatorOfTimeVelocityCoefficient A (fun z => -1 * w z) P := by
        have hx : kineticPositionGradient (fun z => psi z + -1 * w z) P =
            kineticPositionGradient psi P + kineticPositionGradient (fun z => -1 * w z) P :=
          classicalGradient_add ((hpr.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
            ((hneg.positionSlice_contDiffAt hP).differentiableAt (by norm_num))
        simp only [sub_eq_add_neg, show (fun z => psi z + -w z) = fun z => psi z + -1 * w z by
          funext z; ring]
        simp only [backwardOperatorOfTimeVelocityCoefficient_apply,
          comparison_time_add (u := psi) (v := fun z => -1 * w z)
            (hpr.timeSlice_differentiableAt hP) (hneg.timeSlice_differentiableAt hP), hx,
          comparison_hessian_add (u := psi) (v := fun z => -1 * w z)
            (hpr.velocitySlice_contDiffAt hP) (hneg.velocitySlice_contDiffAt hP),
          matrixContraction_add_right, PDE.vecDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      rw [hadd, hop_lin hwr (-1) hP, he]; linarith
    have hAm : Measurable (fun P : KineticPoint d => A P.time P.velocity) :=
      hB.comp (continuous_time.prodMk continuous_velocity).measurable
    have hm : Measurable (fun P : Q => backwardOperatorOfTimeVelocityCoefficient A psi P) := by
      refine (hpr.continuousOn_kineticTimeDerivative.domRestrict.measurable.add ?_).sub ?_
      · exact Finset.measurable_sum _ fun i _ =>
          (((continuous_apply i).comp continuous_velocity).measurable.comp measurable_subtype_coe).mul
            (((continuous_apply i).comp_continuousOn
              hpr.continuousOn_kineticPositionGradient).domRestrict.measurable)
      · exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
          (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hAm)).comp
            measurable_subtype_coe).mul
            (((continuous_apply j).comp_continuousOn
              ((continuous_apply i).comp_continuousOn
                hpr.continuousOn_kineticVelocityHessian)).domRestrict.measurable)
    let F : KineticPoint d → ℝ := fun P =>
      |kineticTimeDerivative psi P| + |PDE.vecDot P.velocity (kineticPositionGradient psi P)| +
        ∑ i, ∑ j, Lam * |kineticVelocityHessian psi P i j|
    have hFc : ContinuousOn F (closure Q) := by
      refine ((hps.continuousOn_kineticTimeDerivative.mono hUQ).abs.add ?_).add ?_
      · exact (continuousOn_finsetSum Finset.univ fun i _ =>
          (((continuous_apply i).comp continuous_velocity).continuousOn).mul
            ((continuous_apply i).comp_continuousOn
              (hps.continuousOn_kineticPositionGradient.mono hUQ))).abs
      · exact continuousOn_finsetSum Finset.univ fun i _ =>
          continuousOn_finsetSum Finset.univ fun j _ =>
            continuousOn_const.mul
              (((continuous_apply j).comp_continuousOn
                ((continuous_apply i).comp_continuousOn
                  (hps.continuousOn_kineticVelocityHessian.mono hUQ))).abs)
    obtain ⟨B, hB0, hFB⟩ := ((isCompact_closure_backwardCylinder P₀ R hR).bddAbove_image
      hFc).exists_ge (0 : ℝ)
    let : IsFiniteMeasure (volume.restrict Q) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using volume_backwardCylinder_lt_top P₀ hR⟩
    have hLp : MemLp (fun P => max (backwardOperatorOfTimeVelocityCoefficient A psi P) 0)
        (ENNReal.ofReal p) (volume.restrict Q) := by
      refine MemLp.of_bound ((TheoremA.measurable_source_indicator hQo.measurableSet _
        (hm.max measurable_const)).aestronglyMeasurable.restrict.congr
        (TheoremA.source_indicator_ae_eq hQo.measurableSet _)) B ?_
      filter_upwards [ae_restrict_mem hQo.measurableSet,
        ae_restrict_of_ae (borel_timeVelocity_ae_lift hL),
        ae_restrict_of_ae (borel_timeVelocity_ae_lift hU)] with P hP hl hh
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      refine max_le ((le_abs_self _).trans (((abs_sub _ _).trans
        (add_le_add (abs_add_le _ _) ?_)).trans (hFB _ (mem_image_of_mem F (subset_closure hP))))) hB0
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (HypoellipticAleksandrov.abs_apply_le_of_loewner hlam hl hh i j) (abs_nonneg _)
    have hbnd := hest P₀ R hR A hB hS hL hU
      (backwardOperatorOfTimeVelocityCoefficient A psi) (fun P => psi P - w P)
      hm ((hps.continuousOn.mono hUQ).sub (hw.continuousOn.mono hQ)) hdiff hop hLp
    apply csSup_le ((backwardCylinder_nonempty P₀ hR).closure.image _)
    rintro _ ⟨P, hP, rfl⟩
    have hn : {P | 0 < psi P - w P} = {P | w P < psi P} := Set.ext fun _ => sub_pos
    simpa only [hn, localizedSource, backwardOperatorOfTimeVelocityCoefficient] using hbnd P hP
  have hneg : Parabolic.IsKineticC112On (fun P => -u P) Omega := by
    simpa only [neg_one_mul] using comparison_regular_const_mul hu (-1)
  have hneg_eq : ∀ᵐ P ∂volume.restrict Omega,
      backwardOperatorOfTimeVelocityCoefficient A (fun Q => -u Q) P = 0 := by
    filter_upwards [heq, ae_restrict_mem hOmega.measurableSet] with P he hP
    simpa only [neg_one_mul, he, mul_zero] using hop_lin hu (-1) hP
  exact hholder (ofTimeVelocityCoefficient A)
    (hB.comp (continuous_time.prodMk continuous_velocity).measurable)
    (fun P => hS P.time P.velocity)
    (borel_timeVelocity_ae_lift hL) (borel_timeVelocity_ae_lift hU)
    Omega hOmega u hbounded ⟨hsup u hu heq, hsup _ hneg hneg_eq⟩

end HypoellipticAleksandrov.KineticAleksandrov

end

