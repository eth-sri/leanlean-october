module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindowGeometry
public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerClipping

@[expose] public section

namespace OAI

noncomputable section


open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialEnergyCallerState
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource InverseInitialEnergyCallerWindows InverseInitialQuotientGeometry
local notation "Eis"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda
variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem windowSource_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    windowSource p S ψ Z D B v θ H ⊆ retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ := by
  intro x hx
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,?_⟩
  have hn := (Finset.mem_filter.mp hx).2
  have hh := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  change ψ 0 (((sourceIdeal p x.common).absNorm:ℝ)/Z^B)*
    ψ 1 (((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ)≠0 at hh
  simpa only [sourceWeight,one_mul] using hh

theorem window_quotient_subset_retained
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(Z D B v θ H:ℝ) :
    quotientSet p (windowSource p S ψ Z D B v θ H) ⊆
      quotientSet p (retained p S (fun _=>1) (ψ 0) (ψ 1) Z B θ) :=
  Finset.image_subset_image (windowSource_subset_retained p S ψ Z D B v θ H)

variable (hp:∀i,p i≠0)
include hp

end SevenEighths.InverseInitialEnergyCallerState

end

end OAI
