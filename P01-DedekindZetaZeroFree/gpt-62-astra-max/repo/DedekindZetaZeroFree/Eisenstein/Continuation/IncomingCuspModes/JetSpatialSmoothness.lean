module

public import DedekindZetaZeroFree.Eisenstein.Continuation.CuspCutoffs.ChartJetHolomorphy

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open Topology

namespace DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

open KPContLocalNorm KPContLocalHolomorphyUpgrade.CauchyAssembly

private alias jetContinuous := DedekindZetaZeroFree.KPContActualCutoffChartJetHolomorphy.ChartJetHolomorphy.ballJet_continuous

section

variable {n : ℕ} (A : LocalBall n) (Ω : Set ℂ)

private theorem point_holomorphic
    (g : ℂ → Space n → ℂ) (hg : KPCutoffSource.ChartSmoothHolomorphicOn A g Ω)
    (x : Space n) (hx : x ∈ A.carrier) : DifferentiableOn ℂ (fun s => g s x) Ω := by
  let K : Set (Space n) := {x}
  letI : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_singleton
  obtain ⟨j,hj,he⟩ := hg.2 K isCompact_singleton (Set.singleton_subset_iff.mpr hx) 0
  let α : MultiIndex n 0 := ⟨fun _ => 0,by simp⟩
  let L : CompactJets K 0 →L[ℂ] ℂ :=
    (ContinuousMap.evalCLM ℂ (⟨x,rfl⟩ : K)).comp (ContinuousLinearMap.proj α)
  apply (L.differentiable.comp_differentiableOn hj).congr
  intro s hs
  have hd : α.directions = [] := by
    simp only [MultiIndex.directions,α,List.replicate_zero]
    induction List.finRange n with
    | nil => rfl
    | cons i l ih => exact ih
  simpa [L,coordinateDerivative,hd,coordinateDerivativeList] using (he s hs α ⟨x,rfl⟩).symm

theorem smooth_parameter_jet_on_ball
    (hΩ : IsOpen Ω) (g : ℂ → Space n → ℂ)
    (hg : KPCutoffSource.ChartSmoothHolomorphicOn A g Ω)
    (k : ℕ) (s : ℂ) (hs : s ∈ Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => iteratedDerivWithin k (fun z => g z x) Ω s) A.carrier := by
  obtain ⟨r,hr,hrΩ⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hs)
  let ρ := r/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hdisk : Metric.closedBall s ρ ⊆ Ω :=
    (Metric.closedBall_subset_ball (by dsimp [ρ]; linarith)).trans hrΩ
  have hc := (ContourLift.coefficient_smooth_and_derivatives A Ω g hg.1
    (jetContinuous A Ω g hg) s ρ hρ hdisk k).1
  apply (show ContDiffOn ℝ (⊤ : ℕ∞)
    (fun x => (k.factorial : ℂ) * (cauchyPowerSeries (fun z => g z x) s ρ k) (fun _ => 1)) A.carrier
    from contDiffOn_const.mul hc).congr
  intro x hx
  have hh := point_holomorphic A Ω g hg x hx
  rw [iteratedDerivWithin_of_isOpen hΩ hs]
  rw [cauchyPowerSeries_apply]
  have hi := (hh.mono hdisk).circleIntegral_one_div_sub_center_pow_smul hρ k
  simp only [one_div, smul_eq_mul] at hi ⊢
  have heq : (fun z => (z-s)⁻¹ ^ k * ((z-s)⁻¹ * g z x)) =
      (fun z => ((z-s)^(k+1))⁻¹ * g z x) := by
    funext z
    rw [pow_succ, mul_inv, ← inv_pow]
    ring
  rw [heq,hi]
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  field_simp

end

open KPContActualCutoffChartJetHolomorphy KPContCotangentActualOverlap

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (C : KPGlobalTorusInducingPlan.ModelData F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (U : KPMsRationalCompactCrossPairing.Level F ζ hζ)
    {S : Type*} [NormedAddCommGroup S] [NormedSpace ℂ S] [FiniteDimensional ℂ S]
    (ι : S →ₗ[ℂ] KPContActualSphericalFlatStage.Stage F ζ hζ U)
variable {T : ℝ} (buffer : KPContActualCollarBuffer.CollarBuffer F ζ hζ
  (level F ζ hζ C R P H U) R P H T)
variable (Ω : Set ℂ) (f : ℂ → S)
    (χ : Cusps F ζ hζ C R P H U → KPCutoffSource.SmoothCuspCutoff T)
    (D : Descent F ζ hζ C R P H U ι buffer Ω f χ)

end DedekindZetaZeroFree.KPContActualCutoffSmoothDescent

end
