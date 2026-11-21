module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.CompactRemainderEstimate
public import DedekindZetaZeroFree.Analysis.SpectralTheory.Resolvents.BelowThresholdMeromorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorResolventSpecialization

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
variable (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
variable (hR : R.adelicHaar = μG)
variable (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)

local notation "Hactual" => KPContSectorClosedLpSubspace.H F ζ hζ R U
local notation "B" => KPContActualSectorFriedrichsSynthesis.B_U
  F ζ hζ U R P H μG hμG hR realization
local notation "Δ" => KPContActualSectorFriedrichsSynthesis.Δ_U
  F ζ hζ U R P H μG hμG hR realization
local notation "d" => (Module.finrank ℚ F : ℝ) / 2

def R_U (z : ℂ) : Hactual →L[ℂ] Hactual :=
  KPResolventPencil.shiftedResolvent B z

local notation "Ractual" => R_U F ζ hζ U R P H μG hμG hR realization

structure Properties : Prop where
  threshold_positive : 0 < d

  resolvent_exact : ∀ z : ℂ, Ractual z = KPResolventPencil.shiftedResolvent B z
  norm_meromorphic : MeromorphicOn Ractual (KPBelowThresholdResolvent.domain d)
  norm_holomorphic_off_poles : AnalyticOnNhd ℂ Ractual
    (KPBelowThresholdResolvent.domain d \ KPBelowThresholdResolvent.poleSet Δ d)
  genuine_inverse_off_poles :
    ∀ z ∈ KPBelowThresholdResolvent.domain d \ KPBelowThresholdResolvent.poleSet Δ d,
      KPResolventPencil.GenuineInverse Δ z (Ractual z) ∧
      (∀ u : Hactual, Ractual z u ∈ (Δ).domain) ∧
      ∀ Q : Hactual →L[ℂ] Hactual, KPResolventPencil.GenuineInverse Δ z Q → Q = Ractual z

  poles_locally_finite : ∀ z ∈ KPBelowThresholdResolvent.domain d,
    ∃ r : ℝ, 0 < r ∧
      (KPBelowThresholdResolvent.poleSet Δ d ∩ Metric.closedBall z r).Finite

  exact_simple_poles : ∀ z ∈ KPBelowThresholdResolvent.domain d,
    z ∈ KPBelowThresholdResolvent.poleSet Δ d ↔
      meromorphicOrderAt Ractual z = ((-1 : ℤ) : WithTop ℤ)

  full_orthogonal_laurent :
    ∀ μ : ℝ, μ < d → KPBelowThreshold.eigenspace Δ μ ≠ ⊥ →
      0 ≤ μ ∧
      KPBelowThresholdResolvent.poleProjection B μ ≠ 0 ∧
      IsSelfAdjoint (KPBelowThresholdResolvent.poleProjection B μ) ∧
      KPBelowThresholdResolvent.poleProjection B μ *
        KPBelowThresholdResolvent.poleProjection B μ =
          KPBelowThresholdResolvent.poleProjection B μ ∧
      (KPBelowThresholdResolvent.poleProjection B μ).range =
        KPBelowThreshold.eigenspace Δ μ ∧
      FiniteDimensional ℂ (KPBelowThresholdResolvent.poleProjection B μ).range ∧
      (∀ u : Hactual, u ∈ KPBelowThreshold.eigenspace Δ μ →
        KPBelowThresholdResolvent.poleProjection B μ u = u) ∧
      Filter.Tendsto (fun z : ℂ => (z - (μ : ℂ)) • Ractual z)
        (𝓝[≠] (μ : ℂ)) (𝓝 (-KPBelowThresholdResolvent.poleProjection B μ)) ∧
      (¬ ∃ G : ℂ → (Hactual →L[ℂ] Hactual),
        ContinuousAt G (μ : ℂ) ∧ G =ᶠ[𝓝[≠] (μ : ℂ)] Ractual) ∧
      ∃ r : ℝ, 0 < r ∧
        Metric.ball (μ : ℂ) r ⊆ KPBelowThresholdResolvent.domain d ∧
        AnalyticOnNhd ℂ (KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹))
          (Metric.ball (μ : ℂ) r) ∧
        ∀ z : ℂ, 0 < ‖z - (μ : ℂ)‖ → ‖z - (μ : ℂ)‖ < r →
          z ∈ KPResolventPencil.resolventSet Δ ∧
          Ractual z = ((μ : ℂ) - z)⁻¹ • KPBelowThresholdResolvent.poleProjection B μ +
            KPIsolatedLaurent.holomorphicComplement B ((1 + μ)⁻¹) z

end DedekindZetaZeroFree.KPContActualSectorResolventSpecialization

namespace DedekindZetaZeroFree

theorem kp_cont_actual_sector_resolvent_specialization
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorResolventSpecialization.Properties
      F ζ hζ U R P H μG hμG hR realization := by
  classical
  let Δ := KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization
  let B := KPContActualSectorFriedrichsSynthesis.B_U F ζ hζ U R P H μG hμG hR realization
  let d : ℝ := (Module.finrank ℚ F : ℝ) / 2
  have hd : 0 < d := by
    have := Module.finrank_pos (R := ℚ) (M := F)
    dsimp [d]
    positivity
  obtain ⟨K, hK, hbound⟩ :=
    kp_cont_actual_compact_remainder_estimate F ζ hζ U R P H μG hμG hR realization
  have hfr := (kp_cont_actual_sector_test_friedrichs F ζ hζ μG hμG U R hR P H realization).friedrichs
  obtain ⟨_, _, _, _, _, hmero, _, hanalytic, hinv, hpoles, hlaurent⟩ :=
    kp_cont_below_threshold_resolvent Δ hfr.laplacian_dense B d hd hfr.laplacian_selfadjoint
      hfr.laplacian_nonnegative hfr.genuine_inverse (fun ε hε => ⟨K, hK, fun u =>
        (mul_le_mul_of_nonneg_right (sub_le_self _ hε.le) (sq_nonneg _)).trans (hbound u)⟩)
  refine ⟨hd, fun _ => rfl, hmero, hanalytic, hinv, ?_, hpoles, ?_⟩
  · -- A meromorphic function is analytic in a punctured neighborhood of each point.
    intro z hz
    obtain ⟨r, hr, h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (eventually_nhdsWithin_iff.mp (hmero z hz).eventually_analyticAt)
    refine ⟨r, hr, (Set.finite_singleton z).subset ?_⟩
    intro w hw
    by_contra hne
    have hn := (h hw.2 hne).meromorphicOrderAt_nonneg
    have hwd : w ∈ KPBelowThresholdResolvent.domain d := by
      obtain ⟨μ, hμ, _, rfl⟩ := hw.1
      rintro ⟨ν, hν, he⟩
      exact hμ.not_ge (Complex.ofReal_injective he ▸ hν)
    rw [(hpoles w hwd).mp hw.1] at hn
    exact (by decide : ¬ (0 : WithTop ℤ) ≤ ((-1 : ℤ) : WithTop ℤ)) hn
  · intro μ hμd he
    obtain ⟨hμ, hPne, hPsa, hPP, hrange, hPfd, hTend, hNonrem, hDisk⟩ := hlaurent μ hμd he
    refine ⟨hμ, hPne, hPsa, hPP, hrange, hPfd, ?_, hTend, hNonrem, hDisk⟩
    intro u hu
    rw [← hrange] at hu
    obtain ⟨v, rfl⟩ := hu
    exact DFunLike.congr_fun hPP v

end DedekindZetaZeroFree

end
