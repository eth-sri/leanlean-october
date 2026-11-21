module

public import DedekindZetaZeroFree.Eisenstein.Continuation.RadialTails.CompactlySupportedSlices
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Cusps.RadialCoercivity

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree

open KPContActualSectorSmoothTestModules KPContActualSectorTestEmbeddings
open KPContActualCuspRadialFormComparison
open KPContSectorSmoothFramesSupport

theorem kp_cont_actual_cusp_exterior_form_bound
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    ∃ T : ℝ,
    (∀ c : Cusp F ζ hζ U R P H,
      ((H.atlas U).cuspAtlas c.1).threshold < T) ∧
    ∀ (c : Cusp F ζ hζ U R P H) (f : S_U F ζ hζ U R P H),
      scalarSupport f.val ⊆ endSet F ζ hζ U R P H c T →
      d F * ‖iota f‖ ^ 2 ≤
        q_U F ζ hζ U R P H μG hμG hR realization
          (coreLift F ζ hζ U R P H μG hμG hR realization f) := by
  have hd := positive_dimension_proof F
  obtain ⟨B, hB⟩ := (Set.finite_range fun c : Cusp F ζ hζ U R P H =>
    ((H.atlas U).cuspAtlas c.1).threshold).bddAbove
  let T := B + 1
  have hT' (c : Cusp F ζ hζ U R P H) : ((H.atlas U).cuspAtlas c.1).threshold < T :=
    (hB (Set.mem_range_self c)).trans_lt (lt_add_one B)
  refine ⟨T, hT', ?_⟩
  intro c f hsupp
  have hT := hT' c
  letI := finite_transverse_proof F ζ hζ U R P H c
  obtain ⟨-, hiF, hiG⟩ := radialDensities_integrable F ζ hζ U R P H realization c T hT f hsupp
  have hFint := hiF.integral_prod_left
  have hGint := hiG.integral_prod_left
  have hnorm := scalar_radial_norm F ζ hζ U R P H realization c T hT f hsupp
  have hcomp := radial_energy_comparison F ζ hζ U R P H μG hμG hR realization c T hT f hsupp
  obtain ⟨hEmb, hRange⟩ := base_embedding_proof F ζ hζ U R P H c T hT
  have hpt : ∀ y : Y_c F ζ hζ U R P H c,
      d F * (∫ t in Set.Ioi T, scalarDensity F ζ hζ U R P H f c y t ∂volume) ≤
      (d F)⁻¹ * (∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t ∂volume) := by
    intro y
    set p : KPCuspCharts.Cross F := Quotient.out y with hp
    set v : ℝ → ℂ := fun t => if T < t then
      (coefficient F ζ hζ U R P H f c p t : ℂ) else 0 with hv
    obtain ⟨hv_cd, hv_cs⟩ := KPRadialTail.radial_tail_slice_regular
      F ζ hζ U R P H realization c f p T hT hEmb hRange hsupp
    have hvan : ∀ t : ℝ, t ≤ T → v t = 0 := by
      intro t ht
      simp only [hv, if_neg (not_lt.mpr ht)]
    have hderiv : ∀ t : ℝ, T < t → deriv v t =
        deriv (fun s => (coefficient F ζ hζ U R P H f c p s : ℂ)) t := by
      intro t ht
      apply Filter.EventuallyEq.deriv_eq
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      simp only [hv, if_pos (show T < s from hs)]
    have hsd : ∀ t : ℝ, T < t → scalarDensity F ζ hζ U R P H f c y t =
        KPRadialCoercivity.density (d F) t * ‖v t‖ ^ 2 := by
      intro t ht
      have hy : v_c F ζ hζ U R P H f c t y =
          Quotient.mk _ (p, coefficient F ζ hζ U R P H f c p t) := by
        rw [← Quotient.out_eq y]
        simp only [v_c, Quotient.lift_mk]
        rw [hp]
      simp only [scalarDensity, hv, if_pos ht, hy, hermitian_norm_proof, KPRadialCoercivity.density]
      congr 1
    have hgd : ∀ t : ℝ, T < t → gradientDensity F ζ hζ U R P H f c y t =
        KPRadialCoercivity.density (d F) t * ‖deriv v t‖ ^ 2 := by
      intro t ht
      have hy : nabla_t F ζ hζ U R P H f c t y =
          Quotient.mk _ (p, (⟨radialDerivative F ζ hζ U R P H f c p t,
            radialDerivative_mem F ζ hζ U R P H f c p t⟩ : Coefficient F ζ hζ U)) := by
        rw [← Quotient.out_eq y]
        simp only [nabla_t, Quotient.lift_mk]
        rw [hp]
      rw [hderiv t ht]
      simp only [gradientDensity, hy, hermitian_norm_proof, KPRadialCoercivity.density,
        radialDerivative]
      congr 1
    have hmass : KPRadialCoercivity.weightedMass (d F) v =
        ∫ t in Set.Ioi T, scalarDensity F ζ hζ U R P H f c y t ∂volume := by
      rw [KPRadialCoercivity.weightedMass,
        setIntegral_congr_fun measurableSet_Ioi (fun t ht => hsd t ht)]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Ioi T) (f := fun t => KPRadialCoercivity.density (d F) t * ‖v t‖ ^ 2)
        (fun t ht => by rw [hvan t (le_of_not_gt ht)]; simp)).symm
    have henergy : KPRadialCoercivity.weightedEnergy (d F) (fun _ => 0) (fun _ => 0) v =
        (d F)⁻¹ * ∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t ∂volume := by
      have hE1 : KPRadialCoercivity.weightedEnergy (d F) (fun _ => 0) (fun _ => 0) v =
          (d F)⁻¹ * ∫ t, KPRadialCoercivity.density (d F) t * ‖deriv v t‖ ^ 2 := by
        rw [KPRadialCoercivity.weightedEnergy,
          show (fun t => KPRadialCoercivity.density (d F) t *
              ((d F)⁻¹ * ‖deriv v t‖ ^ 2 + ((fun _ => 0) t - (fun _ => 0) t) * ‖v t‖ ^ 2)) =
            (fun t => (d F)⁻¹ * (KPRadialCoercivity.density (d F) t * ‖deriv v t‖ ^ 2))
            from by funext t; ring]
        rw [integral_const_mul]
      have hE2 : (∫ t, KPRadialCoercivity.density (d F) t * ‖deriv v t‖ ^ 2) =
          ∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t ∂volume := by
        rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hgd t ht)]
        rw [setIntegral_congr_set (Ioi_ae_eq_Ici (a := T))]
        exact (setIntegral_eq_integral_of_forall_compl_eq_zero
          (s := Set.Ici T)
          (f := fun t => KPRadialCoercivity.density (d F) t * ‖deriv v t‖ ^ 2)
          (fun t ht => by
            have hlt : t < T := lt_of_not_ge ht
            have hev : v =ᶠ[𝓝 t] (fun _ => (0 : ℂ)) := by
              filter_upwards [isOpen_Iio.mem_nhds hlt] with s hs
              exact hvan s (le_of_lt hs)
            have hzero : deriv v t = 0 := by
              rw [Filter.EventuallyEq.deriv_eq hev]; simp
            rw [hzero]; simp)).symm
      rw [hE1, hE2]
    have hsc := KPRadialCoercivity.scalar_zero_mode_lower_bound (d F) hd (fun _ => 0)
      continuous_const (fun _ => le_refl 0) v hv_cd hv_cs
    rw [hmass, henergy] at hsc
    exact hsc
  have hmono : d F * (∫ y, ∫ t in Set.Ioi T, scalarDensity F ζ hζ U R P H f c y t
        ∂volume ∂nu_c F ζ hζ U R P H c) ≤
      (d F)⁻¹ * (∫ y, ∫ t in Set.Ioi T, gradientDensity F ζ hζ U R P H f c y t
        ∂volume ∂nu_c F ζ hζ U R P H c) := by
    have h1 := integral_mono (hFint.const_mul (d F)) (hGint.const_mul (d F)⁻¹)
      (fun y => hpt y)
    rwa [integral_const_mul, integral_const_mul] at h1
  rw [hnorm]
  exact hmono.trans hcomp

end DedekindZetaZeroFree

end
