module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIteration
public import HypoellipticAleksandrov.KineticAleksandrov.Green.SlabFourierPremises
import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationArithmetic
import HypoellipticAleksandrov.KineticAleksandrov.Decay.DecayIterationKernel
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocks
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksEvolution
import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels

/-! # Whole-space Fourier decay from the exact source predecessors

Constants precede every coefficient and supplied realization. The consumer headline
returns the Green family proposition, with only the unit-block estimate and the terminal
evolution statement as hypotheses.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open scoped ENNReal
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/- Source case W exponential decay for every characterized Fourier projection. -/
theorem fourier_decay_whole_space_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
      ∀ (S : TerminalOperatorFamily univ stationary) (K : MovingFiberKernel univ stationary),
        RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient B) id S K →
      ∀ (σ τ : ℝ), σ < τ →
      ∀ (v ξ : PDE.Vec d) (q : EvolutionQuery univ stationary), q.1 = (σ, τ, v, 0) →
      ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν →
        TV ν ≤ C * Real.exp (-c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ)) := by
  obtain ⟨L, δ, hL, hδ, hδ1, hiter⟩ :
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
    obtain ⟨L, δ, hL, hδ, hδ1, hsteps⟩ : ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
        ∀ (B : CoefficientField d), IsSectionTwoCoefficient lam Lam B →
        ∀ (S : TerminalOperatorFamily (univ : Set (PDE.Vec d)) stationary)
          (K : MovingFiberKernel (univ : Set (PDE.Vec d)) stationary),
          RealizesTerminalEvolution univ stationary MeasurableSet.univ
            (zIndependentCoefficient B) id S K →
        ∀ (ξ : PDE.Vec d), ξ ≠ 0 →
        ∀ (s : ℝ) (v : PDE.Vec d) (q : EvolutionQuery (univ : Set (PDE.Vec d)) stationary),
          q.1 = (s, s + L * (PDE.vecEuclideanNorm ξ) ^ (-(2 / 3 : ℝ)), v, 0) →
        ∀ (ν : ComplexMeasure (PDE.Vec d)), IsFourierProjection K q ξ ν → TV ν ≤ 1 - δ := by
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
      have hreal' : RealizesTerminalEvolution univ stationary MeasurableSet.univ
          (zIndependentCoefficient (scaledCoefficient B s v r)) (identityDrift d) S' K' :=
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
        change (0 : PDE.Vec d) ∈ movingDomain (wholeSpace d) (fun _ => 0) 0
        rw [movingDomain_wholeSpace]; exact mem_univ _
      have hL0 : (0 : ℝ) ≤ 0 + L := by linarith only [hL]
      have hq' : movingQuery 0 (0 + L) hL0 0 0 hv' = q' := by
        apply Subtype.ext
        simp only [movingQuery_val, zero_add]
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
          v + r.1 • (0 : PDE.Vec d), (0 : PDE.Vec d) +
            (r.1 ^ 2 * 0) • identityDrift d v + r.1 ^ 3 • (0 : PDE.Vec d)) = _
        simp only [mul_zero, add_zero, smul_zero, zero_smul]
        rw [hr2, mul_comm L]
      have hνmap : IsFourierProjection K (KineticAffineScaling.queryMap hm q') ξ ν := by
        rw [hquery]; exact hν
      have htv := (realizes_ofRadius_fourier_tv s v 0 r hreal hreal' q' ξ ν ν'
        hνmap hν').2
      unfold TV at hunit' ⊢
      change (totalVariationNorm ν).toReal ≤ 1 - δ
      rw [htv]
      exact hunit'
    refine ⟨L, δ, hL, hδ, hδ1, ?_⟩
    intro B hB S K hreal ξ hξ σ τ hστ v q hq ν hν
    have hcomp := hreal.2.2.2
    have hcov := ((iteration_evolution_clauses hEvol hd hlam hlamLam B hB S K hreal).2.2)
    have hsteps := (hsteps B hB S K hreal ξ hξ)
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
    have ha : 0 < 1 - δ := sub_pos.mpr hδ1
    let x := (τ - σ) * N / L
    have hx : 0 ≤ x := (div_pos (mul_pos (sub_pos.mpr hστ) hNp) hL).le
    have hxT : x * T = τ - σ := by
      rw [hTdef]
      dsimp [x]
      field_simp
    have hk : (Nat.floor x : ℝ) * T ≤ τ - σ := by
      rw [← hxT]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le hx) hT.le
    have hstep : ∀ (s : ℝ) (w : PDE.Vec d),
        totalVariationNorm (fourierKernel K s (s + T) (le_add_of_nonneg_right hT.le) ξ w) ≤
          ENNReal.ofReal (1 - δ) := by
      intro s w
      have hst : s ≤ s + T := le_add_of_nonneg_right hT.le
      let qs := wholeSpaceQuery s (s + T) hst w 0
      have hs := hsteps s w qs rfl _ (fourierKernel_spec K s (s + T) hst ξ w)
      have hf :=
        ne_of_lt ((fourierKernel_totalVariation_le_one K s (s + T) hst ξ w).trans_lt
          ENNReal.one_lt_top)
      calc
        _ = ENNReal.ofReal (TV (fourierKernel K s (s + T) hst ξ w)) :=
          (ENNReal.ofReal_toReal hf).symm
        _ ≤ ENNReal.ofReal (1 - δ) := ENNReal.ofReal_le_ofReal hs
    have hn := fourier_natural_block_iteration K hcomp hcov ξ hT ha.le hstep
      (Nat.floor x) σ τ hστ.le hk v
    have hr := ENNReal.toReal_mono (by simp) hn
    simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal ha.le] at hr
    rw [iteration_projection_eq K σ τ hστ.le v ξ q hq ν hν]
    exact ⟨hr, decay_floor_power ha (by linarith only [hδ]),
      decay_power_exponential ha hL (τ - σ) N⟩
  obtain ⟨hC1, hc⟩ := decay_constants hδ hδ1 hL
  refine ⟨(1 - δ)⁻¹, -Real.log (1 - δ) / L, lt_of_lt_of_le zero_lt_one hC1, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ q hq ν hν
  by_cases hξ : ξ = 0
  · subst ξ
    rw [(iteration_projection_eq K σ τ hστ.le v 0 q hq ν hν)]
    have ht := ENNReal.toReal_mono ENNReal.one_ne_top
      (fourierKernel_totalVariation_le_one K σ τ hστ.le 0 v)
    have hz : PDE.vecEuclideanNorm (0 : PDE.Vec d) = 0 :=
      PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl
    simp only [hz, Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0), mul_zero,
      Real.exp_zero, mul_one]
    have htv : TV (fourierKernel K σ τ hστ.le 0 v) ≤ 1 := by
      simpa only [ENNReal.toReal_one] using ht
    exact htv.trans hC1
  · obtain ⟨h1, h2, h3⟩ := hiter B hB S K hreal ξ hξ σ τ hστ v q hq ν hν
    exact (h1.trans h2).trans_eq h3

/- The Green family, conditional on the unit-block estimate and the terminal evolution statement.
-/
theorem fourierDecayFamily_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    HypoellipticAleksandrov.KineticAleksandrov.Green.FourierDecayFamily d lam Lam := by
  obtain ⟨C, c, hC, hc, hdecay⟩ :=
    fourier_decay_whole_space_of_unitBlock d hd lam Lam hlam hlamLam hEvol hblock
  refine ⟨C, c, hC, hc, ?_⟩
  intro B hB S K hreal σ τ hστ v ξ
  have ht := hdecay B hB S K hreal σ τ hστ v ξ
    (wholeSpaceQuery σ τ hστ.le v 0) rfl _ (fourierKernel_spec K σ τ hστ.le ξ v)
  have hf :=
    ne_of_lt ((fourierKernel_totalVariation_le_one K σ τ hστ.le ξ v).trans_lt
      ENNReal.one_lt_top)
  calc
    _ = ENNReal.ofReal (TV (fourierKernel K σ τ hστ.le ξ v)) :=
      (ENNReal.ofReal_toReal hf).symm
    _ ≤ ENNReal.ofReal (C * Real.exp
        (-c * (τ - σ) * PDE.vecEuclideanNorm ξ ^ (2 / 3 : ℝ))) :=
      ENNReal.ofReal_le_ofReal ht
    _ = _ := by congr 3; ring

end HypoellipticAleksandrov.KineticAleksandrov.Decay
