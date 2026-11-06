module

public import DedekindZetaZeroFree.Theta.Whittaker.Complex.TraceCharacterLines

@[expose] public section

noncomputable section
open scoped Classical Topology NNReal
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts
open KPCplxActualImage KPCplxWhittakerUnique
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance : AddCommGroup complexCore := Submodule.addCommGroup complexCore
local instance : Module ℂ complexCore := Submodule.module complexCore
local instance : TopologicalSpace complexCore := instTopologicalSpaceSubtype

def coreSeminorm (n : ℕ) : Seminorm ℂ complexCore :=
  (chartSeminorm negativeParameter n).comp complexCore.subtype

theorem core_withSeminorms : WithSeminorms coreSeminorm :=
  complexCore.subtype.withSeminorms_induced
    (show WithSeminorms (chartSeminorm negativeParameter) from ⟨rfl⟩)

def smoothInclusion : complexCore →L[ℂ] PrincipalSeries negativeParameter :=
  ⟨complexCore.subtype, continuous_subtype_val⟩

theorem exists_harmonic_sequence (v : PrincipalSeries negativeParameter) :
    ∃ a : ℕ → complexCore, Tendsto (fun n => smoothInclusion (a n)) atTop (𝓝 v) := by
  obtain ⟨b, hb, ht⟩ := KPCplxInverseTopology.harmonic_finiteSum_approximation
    negativeParameter v
  have hm (N : ℕ) : (∑ ℓ ∈ Finset.range N, b ℓ) ∈ complexCore := by
    apply Submodule.sum_mem
    intro ℓ hℓ
    constructor
    · rw [imageSubmodule_eq_top]
      trivial
    · exact (le_iSup (fun ℓ => KPCplxIntertwinerEigenvalues.harmonicKType
        negativeParameter ℓ) ℓ) (hb ℓ)
  exact ⟨fun N => ⟨∑ ℓ ∈ Finset.range N, b ℓ, hm N⟩, ht⟩

theorem smoothInclusion_denseRange : DenseRange smoothInclusion := by
  intro v
  obtain ⟨a, ha⟩ := exists_harmonic_sequence v
  exact mem_closure_of_tendsto ha (Eventually.of_forall (fun n => ⟨a n, rfl⟩))

local instance : IsUniformAddGroup (PrincipalSeries negativeParameter) :=
  isUniformAddGroup_of_addCommGroup
local instance : IsUniformAddGroup complexCore := complexCore.toAddSubgroup.isUniformAddGroup

theorem smoothInclusion_isUniformInducing : IsUniformInducing smoothInclusion := by
  apply AddMonoidHom.isUniformInducing_of_isInducing
    (f := smoothInclusion.toLinearMap.toAddMonoidHom)
  exact ⟨rfl⟩

theorem continuous_of_native_bound (l : complexCore →ₗ[ℂ] ℂ)
    (orders : Finset ℕ) (B : ℝ≥0)
    (hb : ∀ v, ‖l v‖ ≤ B * (orders.sup coreSeminorm) v) : Continuous l := by
  apply core_withSeminorms.continuous_normedSpace_rng ℂ
  exact ⟨orders, B, hb⟩

end DedekindZetaZeroFree.FourierContinuation.ComplexLines

end
