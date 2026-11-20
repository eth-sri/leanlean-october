module

public import DedekindZetaZeroFree.Eisenstein.Continuation.ScalarBranchUniquenessAndSingularSets

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

theorem analytic_zeroSet_isolated {O : Set ℂ} (hO : IsOpen O)
    (hconn : IsPreconnected O) (q : ℂ → ℂ) (hq : AnalyticOnNhd ℂ q O)
    {a : ℂ} (ha : a ∈ O) (hqa : q a ≠ 0) :
    IsolatedPoles O {s | s ∈ O ∧ q s = 0} := by
  have hne : ∀ᶠ s in codiscreteWithin O, q s ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected hconn with hz | hn
    · exact (hqa (hz ha)).elim
    · exact hn
  intro z hz
  have hall : ∀ᶠ s in 𝓝 z, s ≠ z → s ∈ O → q s ≠ 0 := by
    simpa using
      eventually_nhdsWithin_iff.mp (eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hne z hz)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  obtain ⟨t, ht, htO⟩ := Metric.isOpen_iff.mp hO z hz
  refine ⟨min r t, lt_min hr ht,
    (Metric.ball_subset_ball (min_le_right _ _)).trans htO, ?_⟩
  intro s hs hp
  by_contra hsz
  exact hball ((Metric.mem_ball.mp hs).trans_le (min_le_left _ _)) hsz hp.1 hp.2

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourcePoleGeometry

namespace DedekindZetaZeroFree.ThetaExpansion
open MomentSources EisensteinSmoothGerms ResidueContinuity.ScalarSourcePoleGeometry
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
    {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

theorem SelectedScalarBranch.germ_eq_of_weighted_chamber
    (D : SelectedScalarBranch R B v) (q : ℂ → ℂ) (A : ℂ → Functions R)
    (hq : AnalyticOnNhd ℂ q KPContinuation.spectralDomain)
    (hq0 : q 0 ≠ 0)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (g : Group R) {s : ℂ} (hs : s ∈ KPContinuation.spectralDomain) :
    (fun z => D.E z g) =ᶠ[𝓝[≠] s] (fun z => A z g / q z) := by
  have he : (fun z => q z * D.E z g) =ᶠ[𝓝[≠] s] (fun z => A z g) := by
    apply KPMsSameContinuationGreen.ContinuationUniqueness.meromorphic_germ_unique
      (hq.meromorphicOn.mul (D.normal g).meromorphicOn) (hA g)
      KPContinuation.spectralDomain_isConnected.isPreconnected
      (isOpen_lt continuous_const Complex.continuous_re)
      KPContinuation.convergenceHalfPlane_subset_spectralDomain
      ⟨1, by norm_num⟩ _ hs
    intro z hz
    change q z * D.E z g = A z g
    rw [D.chamber z hz g, hch z hz g]
  have hne : ∀ᶠ z in codiscreteWithin KPContinuation.spectralDomain, q z ≠ 0 := by
    rcases hq.eqOn_zero_or_eventually_ne_zero_of_preconnected
      KPContinuation.spectralDomain_isConnected.isPreconnected with hz | hn
    · exact (hq0 (hz (by norm_num [KPContinuation.spectralDomain]))).elim
    · exact hn
  filter_upwards [he, (eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hne s hs),
    nhdsWithin_le_nhds (KPContinuation.spectralDomain_isOpen.mem_nhds hs)] with z he hn hz
  rw [← he, mul_div_cancel_left₀ _ (hn hz)]

theorem selectedPoleSet_of_weighted_comparison
    (D : SelectedScalarBranch R B v) (P : Set ℂ)
    (hP : P ⊆ KPContinuation.spectralDomain)
    (hi : IsolatedPoles KPContinuation.spectralDomain P)
    (q : ℂ → ℂ) (A : ℂ → Functions R)
    (hq : AnalyticOnNhd ℂ q KPContinuation.spectralDomain) (hq0 : q 0 ≠ 0)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (hreg : ∀ s ∈ KPContinuation.spectralDomain, s ∉ P →
      ∀ g, AnalyticAt ℂ (fun z => A z g) s) :
    Nonempty (SelectedPoleSet D) := by
  let Z := {s | s ∈ KPContinuation.spectralDomain ∧ q s = 0}
  apply selectedPoleSet_of_regular D (P ∪ Z)
    (fun _ hs => hs.elim (fun hp => hP hp) (fun hz => hz.1)) (hi.union (analytic_zeroSet_isolated KPContinuation.spectralDomain_isOpen
      KPContinuation.spectralDomain_isConnected.isPreconnected q hq
      (by norm_num [KPContinuation.spectralDomain]) hq0))
  intro s hs hn g
  exact D.analyticAt_of_germ g hs ((hreg s hs (fun hp => hn (Or.inl hp)) g).div (hq s hs) (fun hz => hn (Or.inr ⟨hs, hz⟩)))
    (D.germ_eq_of_weighted_chamber q A hq hq0 hA hch g hs)

end DedekindZetaZeroFree.ThetaExpansion

end
