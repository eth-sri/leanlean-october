module
public import OAI.NumberTheory.DirichletL.Moments.AmplificationLiveMask
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationLiveEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentCommonAllocationSum CenteredMomentFirstSectors
open CenteredMomentLiveSupport CenteredMomentLiveDomain CenteredMomentSourceSmoothedAllocation
open CenteredMomentOriginalChildEnergy CenteredMomentAmplificationLiveMask
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 theorem masked_live_gaussEnergy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (B : Tuple ι) (hB : ∀ i,B i≠0) (C R s : Ideal O) (hC : Supported C)
    (hlabel : B∈allocationLabels S C) (hprod : finiteTupleProduct B=C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (f : Ideal O → ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    let c := finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)
    let Q := residualPool C hC.1 (finiteColumns (Fintype.piFinset S))
    let T := finiteColumns (liveBox S B hB)
    gaussEnergy Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => c I*f I) W K =
      gaussEnergy Finset.univ (sourceGenerator T) (sourceGenerator_supported T)
        (fun I : supportedColumns T => c I*f I) W K := by
  dsimp only
  have he (I : Ideal O) : finiteColumnCoefficient (liveBox S B hB)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I =
      finiteColumnCoefficient (liveBox S B hB)
        (liveProfile B C R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I *
          (if s∣I then 1 else 0) := column_mask _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  simp_rw [he,mul_assoc]
  exact live_gaussEnergy S hS hp B hB C R hC hlabel hprod ν Wslot P W₁ W₂
    X₁ X₂ Y₁ Y₂ B₁ B₂ (fun I=> (if s∣I then 1 else 0)*f I) W K

theorem original_masked_child_energy (S : (ι ⊕ Fin 2) → Finset (Ideal O))
    (hS : ∀ i,∀ I∈S i,I≠0) (hp : ∀ i,∀ I∈S (Sum.inl i),Prime I)
    (C R s : Ideal O) (hC : Supported C) (hsc : IsCoprime s C)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O)
    (f : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    (sourceGaussEnergy (residualPool C hC.1 (finiteColumns (Fintype.piFinset S)))
      (fun I=> if IsCoprime C I then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0) f W K).re≤
      ((actualAllocations S C).card:ℝ)*∑ B : actualAllocations S C,
        ‖frozenCoefficient B C R ν Wslot P‖^2*
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂)) f W K).re := by
  pm_647
  let d := fun (B : actualAllocations S C) (I : supportedColumns Q) =>
    finiteColumnCoefficient (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂) I*f I
  have he (I : supportedColumns Q) :
      (if IsCoprime C (I:Ideal O) then finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s) (C*I) else 0)*f I =
      ∑ B,b B*d B I := by
    pm_1206 original_masked_live_column hsc
  pm_6872 h
  have he' := funext he
  pm_6046
  rw [he']
  apply h.trans_eq
  rw [Fintype.card_coe]
  pm_241 S
  simpa only [b,d,sourceGaussEnergy] using
    congrArg (fun x : ℂ => ‖frozenCoefficient B C R ν Wslot P‖^2*x.re)
    (masked_live_gaussEnergy S hS hp B
    (allocation_data S C B (Finset.mem_filter.mp B.property).1).1 C R s hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ f W K)

end SevenEighths.CenteredMomentAmplificationLiveEnergy

end

end OAI
