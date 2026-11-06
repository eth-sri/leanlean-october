module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.OriginalTimeProductRepresentative

 public section

open MeasureTheory Set



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Two original-time product representatives with the same almost-everywhere
spatial slices agree almost everywhere on the time--velocity cylinder. -/
theorem originalTimeL2V_value_product_representative_ae_eq
    {d : ℕ} {Ω : PDE.VelocityRegion d}
    (r₀ r₁ : ℝ) (hΩ : IsOpen Ω)
    (u : ReverseTimeL2V hΩ (r₁ - r₀))
    (U V : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU_meas : AEMeasurable U
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hV_meas : AEMeasurable V
      (timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)))
    (hU : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => U (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y)
    (hV : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => V (r, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u (r₁ - r)) y) :
    U =ᵐ[timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω)] V := by
  let sharedTerm_d26226f6c2 := ((volume.restrict (Set.Ioo r₀ r₁)).prod (PDE.volumeOn Ω))
  have hprod :
      sharedTerm_d26226f6c2 =
        timeVelocityVolumeOn (Set.Ioo r₀ r₁ ×ˢ Ω) := by
    rw [timeVelocityVolumeOn, volume_timeVelocity_eq_prod]
    simpa only [PDE.volumeOn] using Measure.prod_restrict
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure (PDE.Vec d)))
        (Set.Ioo r₀ r₁) Ω
  rw [← hprod] at hU_meas hV_meas ⊢
  let U' := hU_meas.mk U
  let V' := hV_meas.mk V
  have hUU' : U =ᵐ[sharedTerm_d26226f6c2] U' :=
    hU_meas.ae_eq_mk
  have hVV' : V =ᵐ[sharedTerm_d26226f6c2] V' :=
    hV_meas.ae_eq_mk
  have hUV : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => U (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => V (r, y) := by
    filter_upwards [hU, hV] with r hUr hVr
    exact hUr.trans hVr.symm
  have hU'U : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => U' (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => U (r, y) :=
    (Measure.ae_ae_eq_curry_of_prod hUU').mono fun _ hr => hr.symm
  have hVV'c : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => V (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => V' (r, y) :=
    Measure.ae_ae_eq_curry_of_prod hVV'
  have hU'V' : ∀ᵐ r ∂volume.restrict (Set.Ioo r₀ r₁),
      (fun y => U' (r, y)) =ᵐ[PDE.volumeOn Ω] fun y => V' (r, y) := by
    filter_upwards [hU'U, hUV, hVV'c] with r hU'Ur hUVr hVV'r
    exact hU'Ur.trans (hUVr.trans hVV'r)
  have hU'V'_meas : MeasurableSet {z | U' z = V' z} :=
    measurableSet_eq_fun hU_meas.measurable_mk hV_meas.measurable_mk
  have hU'V'prod :
      U' =ᵐ[sharedTerm_d26226f6c2] V' :=
    (Measure.ae_prod_iff_ae_ae hU'V'_meas).2 hU'V'
  exact hUU'.trans (hU'V'prod.trans hVV'.symm)

end HypoellipticAleksandrov.Parabolic.Dirichlet
