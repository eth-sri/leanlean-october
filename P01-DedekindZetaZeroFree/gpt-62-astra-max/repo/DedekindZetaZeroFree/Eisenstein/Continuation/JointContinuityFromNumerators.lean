module

public import DedekindZetaZeroFree.Eisenstein.Continuation.FiniteWordJointNumerators
public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularBranchCauchyReconstruction

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter MeasureTheory
namespace DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity
open MomentSources ThetaExpansion
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
    {R : PrincipalMellin.ActualRecipe S η} {N : TraceHaarTransport R}
    {B : JointRootAlignedSources R N} {v : R.A.UnitQuotient}

 theorem selected_joint_from_numerators
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D)
    (Q : ℂ → ℂ) (A : ℂ → Functions R)
    (hQ : AnalyticOnNhd ℂ Q KPContinuation.spectralDomain) (hQ0 : Q 0 = 1)
    (hA : ∀ g, MeromorphicOn (fun s => A s g) KPContinuation.spectralDomain)
    (hch : ∀ s, (1 / 3 : ℝ) < s.re → ∀ g,
      A s g = Q s * KPLiteralRaw.eisenstein F R.A.zeta12 R.A.primitive_zeta12
        B.sources.K (B.sources.flat v) s g)
    (hlocal : ∀ c ∈ KPContinuation.spectralDomain,
      ∃ r : ℝ, 0 < r ∧ Metric.ball c r ⊆ KPContinuation.spectralDomain ∧
        ∃ T : ℂ → Functions R,
          (∀ g, AnalyticOnNhd ℂ (fun s => T s g) (Metric.ball c r)) ∧
          ContinuousOn (fun p : ℂ × Group R => T p.1 p.2) (Metric.ball c r ×ˢ Set.univ) ∧
          ∀ s ∈ Metric.ball c r, s ≠ c → T s = (s - c) • A s) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) := by
  have hn : ∀ᶠ z in codiscreteWithin KPContinuation.spectralDomain, Q z ≠ 0 := by
    rcases hQ.eqOn_zero_or_eventually_ne_zero_of_preconnected
      KPContinuation.spectralDomain_isConnected.isPreconnected with hz | hn
    · have he := hz (by norm_num [KPContinuation.spectralDomain] :
        (0 : ℂ) ∈ KPContinuation.spectralDomain)
      simp only [hQ0, Pi.zero_apply] at he
      exact (one_ne_zero he).elim
    · exact hn
  apply selected_regular_joint_of_punctured D P
  intro c hc
  obtain ⟨r, hr, hb, T, hTa, hTj, hTe⟩ := hlocal c hc.1
  obtain ⟨t, ht, htB⟩ := regular_ball D P c hc
  obtain ⟨u, hu, huB⟩ := Metric.mem_nhdsWithin_iff.mp (eventually_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hn c hc.1)
  let ρ := min r (min t u)
  have hρr : ρ ≤ r := min_le_left _ _
  have hρt : ρ ≤ t := (min_le_right _ _).trans (min_le_left _ _)
  have hreg : Metric.ball c ρ ⊆ KPContinuation.spectralDomain \ P.poles :=
    (Metric.ball_subset_ball hρt).trans htB
  have hqne : ∀ s ∈ Metric.ball c ρ \ {c}, Q s ≠ 0 := fun s hs => huB ⟨Metric.ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hs.1,
      hs.2⟩ (hreg hs.1).1
  refine ⟨ρ, (lt_min hr (lt_min ht hu)), hreg, ?_⟩
  let V := fun s g => T s g / ((s - c) * Q s)
  have hVj : ContinuousOn (fun p : ℂ × Group R => V p.1 p.2)
      ((Metric.ball c ρ \ {c}) ×ˢ Set.univ) := by
    apply (hTj.mono (Set.prod_mono
      (Set.inter_subset_left.trans (Metric.ball_subset_ball hρr)) (Set.Subset.refl Set.univ))).div
    · exact (((continuous_fst.sub continuous_const).continuousOn).mul
        ((hQ.continuousOn.comp continuous_fst.continuousOn
          (fun p hp => (hreg hp.1.1).1))))
    · intro p hp
      exact mul_ne_zero (sub_ne_zero.mpr (fun he => hp.1.2 (Set.mem_singleton_iff.mpr he)))
        (hqne p.1 hp.1)
  apply hVj.congr
  intro p hp
  have hz := fun he => hp.1.2 (Set.mem_singleton_iff.mpr he)
  refine ((((P.regular p.1 (hreg hp.1.1).1 (hreg hp.1.1).2 p.2).continuousAt).eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ((hTa p.2 p.1 (Metric.ball_subset_ball hρr hp.1.1)).div
    ((analyticAt_id.sub analyticAt_const).mul (hQ p.1 (hreg hp.1.1).1))
    (mul_ne_zero (sub_ne_zero.mpr hz) (hqne p.1 hp.1))).continuousAt).mp
    ((D.germ_eq_of_weighted_chamber Q A hQ (by simp [hQ0]) hA hch p.2
      (hreg hp.1.1).1).trans ?_)).eq_of_nhds
  filter_upwards [nhdsWithin_le_nhds (inter_mem (Metric.isOpen_ball.mem_nhds (Metric.ball_subset_ball hρr hp.1.1)) (isOpen_ne.mem_nhds hz))] with z hz
  have he := congrFun (hTe z hz.1 hz.2) p.2
  change T z p.2 = (z - c) * A z p.2 at he
  dsimp [V]
  rw [he, mul_div_mul_left _ _ (sub_ne_zero.mpr hz.2)]

 theorem selected_regular_joint
    (R : PrincipalMellin.ActualRecipe S η) {N : TraceHaarTransport R}
    (B : JointRootAlignedSources R N) (v : R.A.UnitQuotient)
    (D : SelectedScalarBranch R B v) (P : SelectedPoleSet D) :
    ContinuousOn (fun p : ℂ × Group R => D.E p.1 p.2)
      ((KPContinuation.spectralDomain \ P.poles) ×ˢ Set.univ) := by
  let ζ := R.A.zeta12
  let hζ := R.A.primitive_zeta12
  letI : T2Space (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).1
  letI : LocallyCompactSpace (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.1
  letI : IsTopologicalGroup (KPLiteralRaw.G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨L⟩ := KPGlobalProductPolarizationCharacter.exists_compatible_local_data F ζ hζ
  obtain ⟨C, _⟩ := KPGlobalTorusFiniteStages.compatibleModelData_exists F ζ hζ L
  obtain ⟨Haar, _, _, T, ⟨H⟩⟩ :=
    kp_ms_fixed_haar_disintegration F ζ hζ
      Measure.haar inferInstance
  obtain ⟨Q, A, hQ, hQ0, hA, hch, hlocal⟩ :=
    literal_joint_numerators F ζ hζ C Haar T H B.sources.K B.sources.iwasawa (B.sources.flat v)
  exact selected_joint_from_numerators D P Q A hQ hQ0 hA hch hlocal

end DedekindZetaZeroFree.ResidueContinuity.ScalarSourceJointContinuity

end
