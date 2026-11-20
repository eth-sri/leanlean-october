module

public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonEnergyPointwise
public import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonBarrierBound

/-! # Transfer of spatial energy barriers to classical representatives

Time reflection and continuity turn the closed-time variational estimate into a pointwise one.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Filter MeasureTheory Set Dirichlet
open scoped ENNReal Topology

/-- A continuous spatial envelope of canonical energy values bounds the classical representative. -/
theorem classicalEnergyRepresentative_abs_le_continuous_barrier {d : ℕ}
    {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (a T : ℝ) (haT : a < T)
    (u : ReverseTimeL2V hΩ (T - a)) (g : ReverseTimeL2VStar hΩ (T - a))
    (hdu : HasGelfandWeakTimeDerivative hΩ (T - a) (sub_pos.mpr haT) u g)
    (q : PDE.Vec d → ℝ) (hq : Continuous q)
    (henv : ∀ τ : ℝ, ∀ hτ : τ ∈ Icc 0 (T - a), ∀ᵐ y ∂PDE.volumeOn Ω,
      |reverseTimeHilbertRepresentative hΩ (T - a) (sub_pos.mpr haT)
        u g hdu ⟨τ, hτ⟩ y| ≤ q y)
    (w : TimeVelocity d → ℝ)
    (hw : ContinuousOn w (scalarParabolicOpenCylinder a T Ω))
    (hwslice : ∀ᵐ t ∂volume.restrict (Ioo a T),
      (fun y => w (t, y)) =ᵐ[PDE.volumeOn Ω] fun y => valueCLM hΩ (u (T - t)) y) :
    ∀ z ∈ scalarParabolicOpenCylinder a T Ω, |w z| ≤ q z.2 := 
  classicalEnergyRepresentative_abs_le_envelope hΩ a T haT u g hdu
    (q ∘ Prod.snd) (hq.comp continuous_snd) henv w hw hwslice

end HypoellipticAleksandrov.Parabolic.LocalHolder
