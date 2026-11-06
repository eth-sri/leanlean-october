module

public import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindows

@[expose] public section

namespace OAI

noncomputable section

open scoped Classical
namespace SevenEighths.InverseInitialEnergyCallerWindowGeometry
open InverseInitialArithmetic
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows
open ConcreteTraceCRT
variable {ι:Type*}[DecidableEq ι](p:ι→ActualEisensteinCubic.O)

theorem retained_source_windows
    (S:Finset (Source (ι:=ι) 0))(ψ:Fin 4→ℝ→ℂ)(lo hi:Fin 4→ℝ)
    (hψ:∀i,Function.support (ψ i)⊆Set.Icc (lo i) (hi i))
    (Z D B v θ H:ℝ)(hZ:0<Z){x:Source (ι:=ι) 0}
    (hx:x∈windowSource p S ψ Z D B v θ H) :
    ((sourceIdeal p x.common).absNorm:ℝ)≤hi 0*Z^B ∧
    lo 1*Z^θ≤((sourceIdeal p x.divisor).absNorm:ℝ) ∧
    ((sourceIdeal p x.divisor).absNorm:ℝ)≤hi 1*Z^θ ∧
    ((sourceIdeal p x.overlap).absNorm:ℝ)≤hi 2*Z^v ∧
    ‖eisEmbedding x.frequency‖^2≤hi 3*Z^H := by
  have hm : sourcePoint x ∅ ∅∈pointSource ∅ (windowSource p S ψ Z D B v θ H) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    apply Finset.mem_image.mpr
    exact by simp
  have hh (i:Fin 4) := hψ i (windowSource_four_nonzero p ∅ S ψ Z D B v θ H hm i)
  have h0 := hh 0
  have h1 := hh 1
  have h2 := hh 2
  have h3 := hh 3
  change ((sourceIdeal p x.common).absNorm:ℝ)/Z^B∈Set.Icc (lo 0) (hi 0) at h0
  change ((sourceIdeal p x.divisor).absNorm:ℝ)/Z^θ∈Set.Icc (lo 1) (hi 1) at h1
  change ((sourceIdeal p x.overlap).absNorm:ℝ)/Z^v∈Set.Icc (lo 2) (hi 2) at h2
  change ‖eisEmbedding x.frequency‖^2/Z^H∈Set.Icc (lo 3) (hi 3) at h3
  exact ⟨(div_le_iff₀ (by positivity)).mp h0.2,
    (le_div_iff₀ (by positivity)).mp h1.1,
    (div_le_iff₀ (by positivity)).mp h1.2,
    (div_le_iff₀ (by positivity)).mp h2.2,
    (div_le_iff₀ (by positivity)).mp h3.2⟩

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
include hp

end SevenEighths.InverseInitialEnergyCallerWindowGeometry

end

end OAI
