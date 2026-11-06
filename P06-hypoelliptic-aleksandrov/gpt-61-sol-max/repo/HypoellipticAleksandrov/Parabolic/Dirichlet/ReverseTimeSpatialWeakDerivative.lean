module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeProductRepresentative
public import HypoellipticAleksandrov.Parabolic.WeakDerivatives
public import Mathlib.MeasureTheory.Integral.Prod
import Aesop
import HypoellipticAleksandrov.Parabolic.LocalHolder.SourceComparisonLocalCutoff
import Lean.Elab.Tactic.SolveByElim
public import PDEFoundation.Calculus.RegularityOrder




/-!
# Reverse-time spatial weak derivatives

This module passes the spatial weak-gradient information in a reverse-time
energy carrier to its literal reverse-time product representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

variable (τ : ℝ)

private theorem isClosedEmbedding_timeSlice   :
    IsClosedEmbedding (Prod.mk τ : PDE.Vec d → TimeVelocity d) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_const.prodMk continuous_id) (fun x y h => congrArg Prod.snd h) ?_
  intro s hs
  have himage : Prod.mk τ '' s = ({τ} : Set ℝ) ×ˢ s := by
    ext z
    constructor
    · aesop
    · aesop
  rw [himage]
  exact isClosed_singleton.prod hs

private theorem hasCompactSupport_timeSlice
      (φ : HypoellipticAleksandrov.Parabolic.ScalarField d) (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun y  => φ (τ, y)) := (HasCompactSupport.of_support_subset_isCompact (IsClosedEmbedding.isCompact_preimage (isClosedEmbedding_timeSlice τ) hφ)
  fun ⦃y⦄ hy => id (fun hy => subset_tsupport φ hy) hy)

variable {Ω : PDE.VelocityRegion d}

variable {T : ℝ} (τ : ℝ) (φ : HypoellipticAleksandrov.Parabolic.ScalarField d)

private theorem tsupport_timeSlice_subset

    (hφ : tsupport φ ⊆ reverseTimeOpenInterval T ×ˢ Ω) :
    tsupport (fun y  => φ (τ, y)) ⊆ Ω := (LocalHolder.tsupport_local_cutoff_time_slice_subset φ hφ τ)

variable (hφsmooth : ContDiff ℝ PDE.smoothOrder φ) (hφcompact : HasCompactSupport φ) (hφsupport : tsupport φ ⊆ reverseTimeOpenInterval T ×ˢ Ω)

private def timeSliceWeakTestFunction

     :
    PDE.WeakTestFunction Ω where
  toFun := fun y => φ (τ, y)
  contDiff := hφsmooth.comp (contDiff_const.prodMk contDiff_id)
  hasCompactSupport := hasCompactSupport_timeSlice τ φ hφcompact
  tsupport_subset := tsupport_timeSlice_subset τ φ hφsupport

private theorem velocityGradient_timeSlice_eq_partialDeriv


    (y : PDE.Vec d) (i : Fin d) :
    velocityGradient φ (τ, y) i =
      (timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport).partialDeriv i y := by
  have hslice := (hφsmooth.differentiable (by simp) (τ, y)).hasFDerivAt.comp y
    (hasFDerivAt_prodMk_right τ y)
  change fderiv ℝ φ (τ, y) (0, Pi.single i 1) =
    fderiv ℝ (φ ∘ Prod.mk τ) y (PDE.basisVec i)
  rw [hslice.fderiv]
  rfl

private theorem h10HilbertGraph_integral_partialDeriv
      (hΩ : IsOpen Ω)
    (v : H10HilbertGraph hΩ) (i : Fin d) (ψ : PDE.WeakTestFunction Ω) :
    (∫ y, valueCLM hΩ v y * ψ.partialDeriv i y ∂PDE.volumeOn Ω) =
      -∫ y, gradientCLM hΩ v y i * ψ y ∂PDE.volumeOn Ω := by
  let w  := PDE.H1HilbertGraph.toH1Graph (v : PDE.H1HilbertGraph Ω)

  exact eq_neg_of_add_eq_zero_left ((PDE.mem_weakGradientGraph_iff_integral w.1).mp w.2 i ψ)

private theorem integrable_mul_of_memLp_two_of_continuous_compact
     {W q : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {S : HypoellipticAleksandrov.Parabolic.Region d}
    (hW : MemLp W (2 ) (timeVelocityVolumeOn S))
    (hq : Continuous q) (hqcompact : HasCompactSupport q) :
    Integrable (fun z => W z * q z) (timeVelocityVolumeOn S) := by
  have hqLp : MemLp q (2 ) (timeVelocityVolumeOn S) :=
    (hq.memLp_of_hasCompactSupport hqcompact).restrict S
  simpa only [Pi.mul_def] using hW.integrable_mul hqLp

/-- Reverse-time product representatives of a spatial Sobolev curve retain
their joint raw weak velocity derivatives. -/
theorem reverseTime_hasWeakVelocityPartialDerivOn_of_product_representatives
     {Ω : PDE.VelocityRegion d}
    (hΩ : IsOpen Ω) (T : ℝ)
    (u : ReverseTimeL2V hΩ T)
    (U : HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hU : MemLp U (2 )
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hUslice : ∀ᵐ τ ∂reverseTimeVolume T,
      (fun y => U (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => valueCLM hΩ (u τ) y)
    (G : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
    (hG : ∀ j, MemLp (G j) (2 )
      (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)))
    (hGslice : ∀ᵐ τ ∂reverseTimeVolume T, ∀ j,
      (fun y => G j (τ, y)) =ᵐ[PDE.volumeOn Ω]
        fun y => gradientCLM hΩ (u τ) y j) :
    ∀ i : Fin d,
      HasWeakVelocityPartialDerivOn
        (reverseTimeOpenInterval T ×ˢ Ω) i U (G i) := by
  intro i φ hφsmooth hφcompact hφsupport
  letI : SFinite (reverseTimeVolume T) := by
    dsimp only [reverseTimeVolume]
    infer_instance
  let ψ  := fun τ =>
    timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport
  let dφ  := fun z => velocityGradient φ z i


  have hleft  :=
    integrable_mul_of_memLp_two_of_continuous_compact hU (show Continuous dφ by
        unfold dφ velocityGradient
        exact (hφsmooth.continuous_fderiv (by simp)).clm_apply continuous_const) (show HasCompactSupport dφ by
        unfold dφ velocityGradient
        exact hφcompact.fderiv_apply (𝕜 := ℝ) _)
  have hright  :=
    integrable_mul_of_memLp_two_of_continuous_compact (hG i) hφsmooth.continuous hφcompact
  change (∫ z, U z * velocityGradient φ z i
      ∂timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)) =
    -∫ z, G i z * φ z
      ∂timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)
  change Integrable (fun z => U z * velocityGradient φ z i)
    (timeVelocityVolumeOn (reverseTimeOpenInterval T ×ˢ Ω)) at hleft
  rw [← reverseTimeVolume_prod_volumeOn_eq_timeVelocityVolumeOn T Ω] at hleft hright ⊢
  rw [integral_prod _ hleft, integral_prod _ hright]
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hUslice, hGslice] with τ hUτ hGτ
  have hleftSlice :
      (∫ y, U (τ, y) * dφ (τ, y) ∂PDE.volumeOn Ω) =
        ∫ y, valueCLM hΩ (u τ) y * (ψ τ).partialDeriv i y
          ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards [hUτ] with y hy
    rw [hy]
    change valueCLM hΩ (u τ) y * velocityGradient φ (τ, y) i =
      valueCLM hΩ (u τ) y *
        (timeSliceWeakTestFunction τ φ hφsmooth hφcompact hφsupport).partialDeriv i y
    rw [velocityGradient_timeSlice_eq_partialDeriv τ φ hφsmooth hφcompact hφsupport]
  have hrightSlice :
      (∫ y, G i (τ, y) * φ (τ, y) ∂PDE.volumeOn Ω) =
        ∫ y, gradientCLM hΩ (u τ) y i * ψ τ y ∂PDE.volumeOn Ω := by
    apply integral_congr_ae
    filter_upwards [hGτ i] with y hy
    rw [hy]
    rfl
  rw [hleftSlice, hrightSlice]
  exact h10HilbertGraph_integral_partialDeriv hΩ (u τ) i (ψ τ)

end HypoellipticAleksandrov.Parabolic.Dirichlet
