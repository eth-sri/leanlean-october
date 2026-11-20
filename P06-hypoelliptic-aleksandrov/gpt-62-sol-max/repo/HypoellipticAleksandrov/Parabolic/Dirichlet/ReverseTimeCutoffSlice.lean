module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotient
public import HypoellipticAleksandrov.Topology.Support
public import PDEFoundation.Sobolev.Cutoff.Basic

/-! # Cutoff translations and quotients at a fixed reverse-time slice -/

@[expose] public section
noncomputable section
open Set

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Reverse time sends the closed reversed cylinder into the original one. -/
theorem IsSmoothOnNeighborhood.reverseTimeClosedCylinder
    {d : ℕ} {Ω : Set (PDE.Vec d)} {r₀ r₁ : ℝ} {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f (scalarParabolicClosedCylinder r₀ r₁ Ω)) :
    IsSmoothOnNeighborhood (fun z => f (r₁ - z.1, z.2)) (Icc 0 (r₁ - r₀) ×ˢ closure Ω) := by
  have h : reverseTimeMap r₁ '' (Icc 0 (r₁ - r₀) ×ˢ closure Ω) ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro _ ⟨⟨t, y⟩, ⟨ht, hy⟩, rfl⟩
    simp only [reverseTimeMap_apply]
    exact ⟨⟨by linarith [ht.2], by linarith [ht.1]⟩, hy⟩
  simpa only [Function.comp_def, reverseTimeMap_apply] using IsSmoothOnNeighborhood.reverseTime r₁ h hf

/-- The translated field and difference quotient are continuous and compactly supported
once restricted by a cutoff with an admissible shift. -/
theorem cutoffSlice_translate_quotient
    {d : ℕ} {Ω inner : Set (PDE.Vec d)} {K r₀ r₁ τ : ℝ}
    (β : PDE.QuantitativeSmoothCutoff inner Ω K) (k : Fin d) (h w : ℝ)
    {f : TimeVelocity d → ℝ}
    (hf : IsSmoothOnNeighborhood f (Icc 0 (r₁ - r₀) ×ˢ closure Ω))
    (hτ : τ ∈ Icc 0 (r₁ - r₀)) (hβshift : β.ShiftMapsInto k h Ω) :
    (Continuous (fun y => w * β y * spatialTranslate k h f (τ, y)) ∧
      HasCompactSupport (fun y => w * β y * spatialTranslate k h f (τ, y))) ∧
    (Continuous (fun y => w * β y * spatialDifferenceQuotient k h f (τ, y)) ∧
      HasCompactSupport (fun y => w * β y * spatialDifferenceQuotient k h f (τ, y))) := by
  obtain ⟨V, hV, hSV, hf⟩ := hf
  let g₀ : PDE.Vec d → TimeVelocity d := fun y => (τ, y)
  let g₁ : PDE.Vec d → TimeVelocity d := fun y => (τ, y + h • PDE.basisVec k)
  let U := g₀ ⁻¹' V ∩ g₁ ⁻¹' V
  have hg₀ : Continuous g₀ := continuous_const.prodMk continuous_id
  have hg₁ : Continuous g₁ := continuous_const.prodMk (continuous_id.add continuous_const)
  have hU : IsOpen U := (hV.preimage hg₀).inter (hV.preimage hg₁)
  have hβU : tsupport β.toFun ⊆ U := fun y hy =>
    ⟨hSV ⟨hτ, subset_closure (β.tsupport_subset hy)⟩, hSV ⟨hτ, subset_closure (hβshift hy)⟩⟩
  have hf₀ : ContinuousOn (fun y => f (τ, y)) U :=
    hf.continuousOn.comp hg₀.continuousOn fun y hy => hy.1
  have hf₁' : ContinuousOn (fun y => f (τ, y + h • PDE.basisVec k)) U :=
    hf.continuousOn.comp hg₁.continuousOn fun y hy => hy.2
  have hf₁ : ContinuousOn (fun y => spatialTranslate k h f (τ, y)) U := by
    simpa only [spatialTranslate_apply, spatialShift_apply] using hf₁' 
  have hcut : Continuous (fun y => w * β y) := continuous_const.mul β.smooth.continuous
  have hcts {g : PDE.Vec d → ℝ} (hg : ContinuousOn g U) :
      Continuous (fun y => w * β y * g y) ∧ HasCompactSupport (fun y => w * β y * g y) :=
    ⟨(hcut.continuousOn.mul hg).continuous_of_tsupport_subset hU
      (tsupport_mul_subset_left.trans (tsupport_mul_subset_right.trans hβU)),
      β.hasCompactSupport.mul_left.mul_right⟩
  refine ⟨hcts hf₁, hcts ?_⟩
  simpa only [spatialDifferenceQuotient_apply, Pi.sub_def] using (hf₁.sub hf₀).div_const h

end HypoellipticAleksandrov.Parabolic.Dirichlet
