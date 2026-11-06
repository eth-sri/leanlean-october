module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyPointwise
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierBound

/-! # Transfer of spatial energy barriers to classical representatives

Time reflection and continuity turn the closed-time variational estimate into a pointwise one.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory Set Dirichlet


/-- A continuous spatial envelope of canonical energy values bounds the classical representative. -/
theorem classicalEnergyRepresentative_abs_le_continuous_barrier {d : ℕ}
    {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (a T : ℝ) (haT : a < T)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (q : PDE.ScalarField d) (hq : Continuous q)
    (henv : ∀ τ : ℝ, ∀ hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω,
      |reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        u g hdu ⟨τ, hτ⟩ y| ≤ q y)
    (w : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ q z.2 := by



  exact abs_le_of_continuousOn_of_ae_slices hΩ a T w (fun z => q z.2)
    (hq.comp continuous_snd) hw (by
        filter_upwards [hwslice, ((sourceTimeReflection_measurePreserving a T).quasiMeasurePreserving.ae (show ∀ᵐ τ ∂reverseTimeVolume (T - a), ∀ hτ : τ ∈ Ioo 0 (T - a),
      ∀ᵐ y ∂PDE.volumeOn Ω, |valueCLM hΩ (u τ) y| ≤ q y by
            filter_upwards [(reverseTimeHilbertRepresentative_spec hΩ (T - a)
              (sub_pos.mpr haT) u g hdu).1] with τ hrep hτ
            have hb := henv τ ⟨hτ.1.le, hτ.2.le⟩
            rw [hrep hτ] at hb
            exact hb)), ae_restrict_mem measurableSet_Ioo] with t hs hr ht

        filter_upwards [hs, hr (⟨by linarith [ht.2], by linarith [ht.1]⟩)] with y hy hby
        rw [hy]
        exact hby)

end HypoellipticAleksandrov.Parabolic.LocalHolder
