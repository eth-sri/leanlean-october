module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GenuineSector.BelowThresholdResolvent

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualChamberInverse

variable (F : Type) [Field F] [NumberField F]

def a_U (s : ℂ) : ℂ :=
  (((Module.finrank ℚ F : ℝ) / 2 : ℝ) : ℂ) *
    (1 - ((1 : ℂ) / 3 + 2 * s) ^ 2)

variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
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

def Sigma_U : Set ℂ :=
  KPContinuation.spectralDomain ∩
    (a_U F ⁻¹' KPBelowThresholdResolvent.poleSet Δ d)

local notation "Σactual" => Sigma_U F ζ hζ U R P H μG hμG hR realization

structure Properties : Prop where
  chamber_regular : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
    s ∈ KPContinuation.spectralDomain \ Σactual ∧
    a_U F s ∈ KPBelowThresholdResolvent.domain d \
      KPBelowThresholdResolvent.poleSet Δ d
  genuine_inverse : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
    KPResolventPencil.GenuineInverse Δ (a_U F s)
      (KPResolventPencil.shiftedResolvent B (a_U F s))
end DedekindZetaZeroFree.KPContActualChamberInverse

namespace DedekindZetaZeroFree

theorem kp_cont_actual_chamber_inverse
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualChamberInverse.Properties F ζ hζ U R P H μG hμG hR realization := by
  classical
  have hspec := kp_cont_actual_sector_resolvent_specialization
    F ζ hζ μG hμG U R hR P H realization
  have hd : 0 < (Module.finrank ℚ F : ℝ) / 2 := hspec.threshold_positive
  have hpole_nonneg : ∀ z ∈ KPBelowThresholdResolvent.poleSet
      (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
      ((Module.finrank ℚ F : ℝ) / 2), z ∈ Complex.ofReal '' Set.Ici (0 : ℝ) := by
    rintro z ⟨μ, hμd, he, rfl⟩
    exact ⟨μ, (hspec.full_orthogonal_laurent μ hμd he).1, rfl⟩
  have havoid : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
      KPContActualChamberInverse.a_U F s ∉ Complex.ofReal '' Set.Ici (0 : ℝ) := by
    intro s hs hmem
    rcases hmem with ⟨t, ht, htz⟩
    have him : (KPContActualChamberInverse.a_U F s).im = 0 := by rw [← htz]; simp
    have hre : 0 ≤ (KPContActualChamberInverse.a_U F s).re := by
      rw [← htz]; simpa using ht
    set u : ℂ := (1 : ℂ) / 3 + 2 * s with hu
    have hval : KPContActualChamberInverse.a_U F s =
        (((Module.finrank ℚ F : ℝ) / 2 : ℝ) : ℂ) * (1 - u ^ 2) := by
      unfold KPContActualChamberInverse.a_U; rw [hu]
    have hui : u.im = 2 * s.im := by simp [hu, Complex.add_im, Complex.mul_im]
    have hur : u.re = (1 : ℝ) / 3 + 2 * s.re := by
      simp [hu, Complex.add_re, Complex.mul_re]
    have hu_gt : 1 < u.re := by rw [hur]; linarith
    have him' : (KPContActualChamberInverse.a_U F s).im =
        -(((Module.finrank ℚ F : ℝ) / 2) * (2 * u.re * u.im)) := by
      rw [hval]
      rw [Complex.mul_im, Complex.sub_im, Complex.one_im, Complex.ofReal_re,
        Complex.ofReal_im, pow_two, Complex.mul_im, hui, hur]
      ring
    have hui0 : u.im = 0 := by
      have hprod : (Module.finrank ℚ F : ℝ) / 2 * (2 * u.re * u.im) = 0 := by
        have h := him; rw [him'] at h; linarith
      have hdne : ((Module.finrank ℚ F : ℝ) / 2) ≠ 0 := ne_of_gt hd
      have h1 : 2 * u.re ≠ 0 := by
        intro hz; linarith [hu_gt, hz]
      have h2 : 2 * u.re * u.im = 0 := (mul_eq_zero.mp hprod).resolve_left hdne
      exact (mul_eq_zero.mp h2).resolve_left h1
    have hre' : (KPContActualChamberInverse.a_U F s).re =
        ((Module.finrank ℚ F : ℝ) / 2) * (1 - u.re ^ 2) := by
      rw [hval]
      rw [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
        Complex.ofReal_im, pow_two, Complex.mul_re, hui0, hur]
      ring
    have hneg : (KPContActualChamberInverse.a_U F s).re < 0 := by
      rw [hre']
      exact mul_neg_of_pos_of_neg hd (by nlinarith [hu_gt])
    linarith
  have hchamber : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
      KPContActualChamberInverse.a_U F s ∈
        KPBelowThresholdResolvent.domain ((Module.finrank ℚ F : ℝ) / 2) \
          KPBelowThresholdResolvent.poleSet
            (KPContActualSectorFriedrichsSynthesis.Δ_U F ζ hζ U R P H μG hμG hR realization)
            ((Module.finrank ℚ F : ℝ) / 2) := by
    intro s hs
    refine ⟨?_, fun hp => havoid s hs (hpole_nonneg _ hp)⟩
    intro hmem
    rcases hmem with ⟨r, hr, hrz⟩
    exact havoid s hs ⟨r, le_trans hd.le hr, hrz⟩
  have hSigma : ∀ s : ℂ, (1 : ℝ) / 3 < s.re →
      s ∉ KPContActualChamberInverse.Sigma_U F ζ hζ U R P H μG hμG hR realization := by
    intro s hs hmem
    exact havoid s hs (hpole_nonneg _ hmem.2)
  refine ⟨?_, ?_⟩
  · intro s hs
    exact ⟨⟨KPContinuation.convergenceHalfPlane_subset_spectralDomain hs, hSigma s hs⟩,
      hchamber s hs⟩
  · intro s hs
    have h := (hspec.genuine_inverse_off_poles _ (hchamber s hs)).1
    simpa only [KPContActualSectorResolventSpecialization.R_U] using h
end DedekindZetaZeroFree

end
