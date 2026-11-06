module

public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksEvolution
public import HypoellipticAleksandrov.KineticAleksandrov.Decay.FrequencyBlocksRadius
public import HypoellipticAleksandrov.KineticAleksandrov.Scaling.Radius
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.FourierKernels

/-! # Nonzero-frequency blocks, conditional on the exact unit-block theorem -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov.Decay
open Set MeasureTheory HypoellipticAleksandrov
open HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open HypoellipticAleksandrov.KineticAleksandrov.Scaling

/-- Source scaled blocks in case W, relative only to the authorized source predecessors. -/
theorem nonzero_frequency_blocks_of_unitBlock (d : ℕ) (hd : 1 ≤ d)
    (lam Lam : ℝ) (hlam : 0 < lam) (hlamLam : lam ≤ Lam)
    (hEvol : IterationEvolutionStatement)
    (hblock : UnitBlockStatementW d hd lam Lam 1 1 hlam hlamLam zero_lt_one le_rfl) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ δ < 1 ∧
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
  let r : {r : ℝ // 0 < r} := ⟨PDE.vecEuclideanNorm ξ ^ (-(1 / 3)), hr⟩
  let Φ := KineticAffineScaling.ofRadius s v 0 (identityDrift d) r
  let hm : Φ.MapsDomain univ stationary univ stationary :=
    KineticAffineScaling.mapsDomain_wholeSpace Φ
  let K' := KineticAffineScaling.pushKernel hm K
  let S' := fiberOperator K' MeasurableSet.univ
  have hB' := scaledCoefficient_sectionTwo lam Lam B hB s v r
  have hreal' : RealizesTerminalEvolution univ stationary MeasurableSet.univ
      _ _ S' K' :=
    realizes_ofRadius_wholeSpace s v 0 r hreal
  obtain ⟨hmono', hmargin', hcov'⟩ := iteration_evolution_clauses hEvol hd hlam hlamLam
    _ hB' S' K' hreal'
  let q' : EvolutionQuery univ stationary :=
    wholeSpaceQuery 0 L hL.le (0 : PDE.Vec d) 0
  let ν' := fourierKernel K' 0 L hL.le (r.1 ^ 3 • ξ) 0
  have hν' : IsFourierProjection K' q' _ ν' :=
    fourierKernel_spec K' 0 L hL.le _ 0
  have hsetting : SourceSetting lam Lam 1 1 univ _ id :=
    ⟨hB', identityDrift_smooth d, zero_lt_one, le_rfl, identityDrift_bounds d,
      Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
  have hv' : (0 : PDE.Vec d) ∈ movingDomain univ stationary 0 := by
    change (0) ∈ movingDomain (wholeSpace d) (fun _ => 0) 0
    rw [movingDomain_wholeSpace]; simp
  have hL0 : (0) ≤ 0 + L := by positivity
  have hq' : movingQuery 0 _ hL0 0 0 hv' = q' := by
    aesop
  have hνunit : IsFourierProjection K' (movingQuery 0 _ hL0 0 0 hv')
      (r.1 ^ 3 • ξ) ν' := by
    simp_all
  have hunit' := hunit univ _ id hsetting rfl MeasurableSet.univ
    S' K' hreal' hmono' hmargin' hcov' _ hrunit
    0 0 hv' hL0 ν' hνunit
  have hquery : KineticAffineScaling.queryMap hm q' = q := by
    apply Subtype.ext
    rw [hq]
    change (s + r.1 ^ 2 * 0, s + r.1 ^ 2 * L,
      v + r.1 • (0), (0) +
        (r.1 ^ 2 * 0) • identityDrift d v + r.1 ^ 3 • (0)) = _
    simp only [mul_zero, add_zero, smul_zero, zero_smul]
    grind
  have hνmap : IsFourierProjection K (KineticAffineScaling.queryMap hm q') ξ ν := by
    simp_all
  have htv := (realizes_ofRadius_fourier_tv s v 0 r hreal hreal' q' ξ ν ν'
    hνmap hν').2
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Decay
