module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import Mathlib.Topology.Compactness.SigmaCompact
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeak
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ClassicalTerminalWeak
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceApprox
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
section
open MeasureTheory Set Evolution Occupation Filter Function
open scoped Topology

/-- Restrict a kinetic weak solution to a subdomain without changing its source. -/
theorem boundedSource_weak_restrict {d : ℕ} {U V : Set (KineticPoint d)}
    (hUV : U ⊆ V)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f : KineticPoint d → ℝ) (h : IsKineticWeakTransportedSolution B b V u f) :
    IsKineticWeakTransportedSolution B b U u f := by
  refine ⟨h.1.mono_set hUV, fun ψ hψ hc hs => ?_⟩
  have hsV : tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' V := fun x hx => hUV (hs hx)
  have heq := h.2 ψ hψ hc hsV
  have htest : ∀ W : Set (KineticPoint d),
      tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' W →
      (∫ z in W, f z * ψ ((evolutionHomeomorph d).symm z)) =
        ∫ z, f z * ψ ((evolutionHomeomorph d).symm z) := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : (evolutionHomeomorph d).symm z ∉ tsupport ψ := by
      intro hx
      exact hz (by simpa using hW hx)
    rw [image_eq_zero_of_notMem_tsupport hn, mul_zero]
  have hadj : ∀ W : Set (KineticPoint d),
      tsupport ψ ⊆ evolutionHomeomorph d ⁻¹' W →
      (∫ z in W, u z * transportedAdjoint B b ψ ((evolutionHomeomorph d).symm z)) =
        ∫ z, u z * transportedAdjoint B b ψ ((evolutionHomeomorph d).symm z) := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    have hn : (evolutionHomeomorph d).symm z ∉ tsupport ψ := by
      intro hx
      exact hz (by simpa using hW hx)
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ hn, mul_zero]
  rw [hadj V hsV, htest V hsV] at heq
  rw [hadj U hs, htest U hs]
  exact heq

/-- Restrict an ambient homogeneous weak solution while retaining the literal adjoint. -/
theorem boundedSource_ambientWeak_restrict {d : ℕ} {U V : Set (EvolutionVec d)}
    (hUV : U ⊆ V) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u : EvolutionVec d → ℝ) (h : IsWeakTransportedSolution B b V u (fun _ => 0)) :
    IsWeakTransportedSolution B b U u (fun _ => 0) := by
  refine ⟨h.1.mono_set hUV, fun ψ hψ hc hs => ?_⟩
  have heq := h.2 ψ hψ hc (hs.trans hUV)
  have hadj : ∀ W : Set (EvolutionVec d), tsupport ψ ⊆ W →
      (∫ z in W, u z * transportedAdjoint B b ψ z) =
        ∫ z, u z * transportedAdjoint B b ψ z := by
    intro W hW
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ (fun hm => hz (hW hm)), mul_zero]
  simp at heq ⊢
  rw [hadj V (hs.trans hUV)] at heq
  rw [hadj U hs]
  exact heq

/-- Changing the source only outside the tested domain preserves the kinetic weak equation. -/
theorem boundedSource_weak_source_congr {d : ℕ} {U : Set (KineticPoint d)}
    (hU : MeasurableSet U) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (u f g : KineticPoint d → ℝ) (hfg : EqOn f g U)
    (h : IsKineticWeakTransportedSolution B b U u f) :
    IsKineticWeakTransportedSolution B b U u g := by
  refine ⟨h.1, fun ψ hψ hc hs => ?_⟩
  rw [h.2 ψ hψ hc hs]
  apply setIntegral_congr_fun hU
  intro z hz
  change f z * ψ ((evolutionHomeomorph d).symm z) = g z * ψ ((evolutionHomeomorph d).symm z)
  rw [hfg hz]


/-- A bounded potential is an actual homogeneous weak solution before its source starts. -/
theorem duhamelPotential_weak_before_source
    {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (g : KineticPoint d → ℝ) (hg : Measurable g)
    (M : ℝ) (hM : 0 ≤ M) (hgb : ∀ p, |g p| ≤ M) (s T : ℝ) (hsT : s ≤ T)
    (hgz : ∀ p : KineticPoint d, p.time < s → g p = 0) :
    IsWeakTransportedSolution B b
      (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
      (duhamelPotential K T g ∘ evolutionHomeomorph d) (fun _ => 0) := by
  have hsub : evolutionPastOpenCylinder Ω γ s ⊆ evolutionPastOpenCylinder Ω γ T :=
    fun p hp => ⟨hp.1.trans_le hsT, hp.2⟩
  have hwr := boundedSource_weak_restrict hsub B b (duhamelPotential K T g)
    (fun p => -g p) (duhamel_bounded_isKineticWeakTransportedSolution hΩa hΩ hγ B b S K hreal hB hBs hb g hg M hM hgb T)
  have hsource : EqOn (fun p => -g p) (fun _ => 0)
      (evolutionPastOpenCylinder Ω γ s) := by
    intro p hp
    change -g p = 0
    rw [hgz p hp.1, neg_zero]
  have hzero := boundedSource_weak_source_congr (isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ s).measurableSet B b
    (duhamelPotential K T g) (fun p => -g p) (fun _ => 0) hsource hwr
  exact (isWeakTransportedSolution_comp_iff B b _ _ _).2 hzero


/-- Nonnegative bounded Borel data have uniformly bounded positive smooth approximants
supported in an open domain, converging almost everywhere for the supplied finite measure. -/
theorem exists_boundedSourceSmoothApproximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (U : Set E) (hU : IsOpen U)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ x, 0 ≤ F x ∧ F x ≤ M) (hFz : ∀ x ∉ U, F x = 0) :
    ∃ f : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (f n) ∧ HasCompactSupport (f n) ∧ tsupport (f n) ⊆ U) ∧
      (∀ n x, 0 ≤ f n x ∧ f n x ≤ M + 2) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))  := by
  have exists_boundedSourceCutoffSequence :
      ∃ χ : ℕ → E → ℝ,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n) ∧ tsupport (χ n) ⊆ U) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      ∀ x ∈ U, ∀ᶠ n in atTop, χ n x = 1 := by
    classical
    let : LocallyCompactSpace U := hU.locallyCompactSpace
    let C (n : ℕ) : Set E := Subtype.val '' compactCovering U n
    have hC (n : ℕ) : IsCompact (C n) :=
      (isCompact_compactCovering U n).image continuous_subtype_val
    have hCU (n : ℕ) : C n ⊆ U := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have hex (n : ℕ) := exists_smooth_cutoff (hC n) hU (hCU n)
    choose χ hs hc hsub hb he using hex
    refine ⟨χ, fun n => ⟨hs n, hc n, hsub n⟩, hb, ?_⟩
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    filter_upwards [eventually_ge_atTop n] with m hm
    exact he m x ⟨⟨x, hx⟩, compactCovering_subset U hm hn, rfl⟩
  classical
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεp (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n ≤ 1 := by
    dsimp [ε]
    rw [div_le_iff₀ (by positivity)]
    simp
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hmem : MemLp F 1 μ := by
    apply memLp_one_iff_integrable.mpr
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    apply HasFiniteIntegral.of_bounded (C := M)
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFb x).1]
      exact (hFb x).2
  have hex (n : ℕ) := hmem.exist_eLpNorm_sub_le (by norm_num) le_rfl (hεp n)
  choose g hgc hgs hge using hex
  have hnorm : Tendsto (fun n => eLpNorm (g n - F) 1 μ) atTop (𝓝 0) := by
    have hεe : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hε0
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεe
      (fun _ => zero_le) (fun n => ?_)
    rw [eLpNorm_sub_comm]
    exact hge n
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hnorm
    ).exists_seq_tendsto_ae
  let G (n : ℕ) (x : E) : ℝ := max 0 (min M (g (σ n) x))
  have hGc (n : ℕ) : Continuous (G n) :=
    continuous_const.max (continuous_const.min (hgs (σ n)).continuous)
  have hGb (n : ℕ) (x : E) : 0 ≤ G n x ∧ G n x ≤ M := by
    exact ⟨le_max_left _ _, max_le hM (min_le_left _ _)⟩
  have hGsup (n : ℕ) : support (G n) ⊆ support (g (σ n)) := by
    intro x hx
    contrapose! hx
    simp at hx ⊢
    change max 0 (min M (g (σ n) x)) = 0
    rw [hx, min_eq_right hM, max_self]
  have hGcompact (n : ℕ) : HasCompactSupport (G n) :=
    (hgc (σ n)).mono (hGsup n)
  have hsmooth (n : ℕ) := (hGc n).exists_contDiff_approx ⊤
    (ε := fun _ => ε n) continuous_const (fun _ => hεp n)
  choose q hqs hqe hqsub using hsmooth
  have hqcompact (n : ℕ) : HasCompactSupport (q n) := (hGcompact n).mono (hqsub n)
  have hχex (n : ℕ) := exists_smooth_cutoff (hGcompact n) isOpen_univ
    (subset_univ (tsupport (G n)))
  choose χ hχs hχc hχsub hχb hχone using hχex
  obtain ⟨ρ, hρs, hρb, hρone⟩ := exists_boundedSourceCutoffSequence
  let f (n : ℕ) (x : E) := ρ n x * (q n x + ε n * χ n x)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hρs n).1.mul ((hqs n).add (contDiff_const.mul (hχs n))),
      (hρs n).2.1.mul_right, tsupport_mul_subset_left.trans (hρs n).2.2⟩
  · intro n x
    have hdist : |q n x - G n x| < ε n := by
      simpa only [Real.dist_eq] using hqe n x
    have hpos : 0 ≤ q n x + ε n * χ n x := by
      by_cases hx : x ∈ tsupport (G n)
      · rw [hχone n x hx, mul_one]
        have hh := (abs_lt.mp hdist).1
        linarith [(hGb n x).1]
      · have hz : q n x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun h => hx (closure_mono (hqsub n) h)
        rw [hz, zero_add]
        exact mul_nonneg (hεp n).le (hχb n x).1
    have hup : q n x + ε n * χ n x ≤ M + 2 := by
      have hh := (abs_lt.mp hdist).2
      have hχe := mul_le_mul_of_nonneg_left (hχb n x).2 (hεp n).le
      linarith [(hGb n x).2, hε1 n]
    exact ⟨mul_nonneg (hρb n x).1 hpos,
      (mul_le_mul_of_nonneg_right (hρb n x).2 hpos).trans (by simpa using hup)⟩
  · filter_upwards [hae] with x hx
    by_cases hxU : x ∈ U
    · have hGlim : Tendsto (fun n => G n x) atTop (𝓝 (F x)) := by
        have hMlim : Tendsto (fun _ : ℕ => M) atTop (𝓝 M) := tendsto_const_nhds
        have h0lim : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
        have hh := h0lim.max (hMlim.min hx)
        simpa only [G, min_eq_right (hFb x).2, max_eq_right (hFb x).1] using hh
      have herror : Tendsto (fun n => q n x - G n x) atTop (𝓝 0) := by
        apply squeeze_zero_norm (fun n => ?_) hε0
        simpa [Real.dist_eq] using (hqe n x).le
      have hqlim : Tendsto (fun n => q n x) atTop (𝓝 (F x)) := by
        simpa using (herror.add hGlim)
      have hχlim : Tendsto (fun n => ε n * χ n x) atTop (𝓝 0) := by
        apply squeeze_zero (fun n => mul_nonneg (hεp n).le (hχb n x).1)
          (fun n => by simpa using
            mul_le_mul_of_nonneg_left (hχb n x).2 (hεp n).le) hε0
      have heq : (fun n => f n x) =ᶠ[atTop] (fun n => q n x + ε n * χ n x) := by
        filter_upwards [hρone x hxU] with n hn
        simp [f, hn]
      have hlim' : Tendsto (fun n => q n x + ε n * χ n x) atTop (𝓝 (F x)) := by
        simpa using (hqlim.add hχlim)
      exact hlim'.congr' heq.symm
    · have hz (n : ℕ) : f n x = 0 := by
        have hρz : ρ n x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h => hxU ((hρs n).2.2 h))
        simp [f, hρz]
      simpa only [hz, hFz x hxU] using (tendsto_const_nhds :
        Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0))

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- The literal source domain strictly after a chosen separating time. -/
def boundedSourceFutureSet (Ω : Set (PDE.Vec d)) (γ : ℝ → PDE.Vec d) (s T : ℝ) :
    Set (ℝ × EvolutionAmbientState d) :=
  {q | s < q.1 ∧ q ∈ boundedSourcePast Ω γ T}

/-- The future source region is open with the original moving geometry. -/
theorem isOpen_boundedSourceFutureSet (hΩ : IsOpen Ω) (hγ : Continuous γ) (s T : ℝ) :
    IsOpen (boundedSourceFutureSet Ω γ s T) :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_boundedSourcePast hΩ hγ T)

/-- Actual positive bounded future potentials have continuous homogeneous approximants
converging for any supplied finite starting measure. -/
theorem exists_duhamelFuture_approximating_sequence
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (a s T : ℝ) (hsT : s ≤ T)
    (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (hfloor : ∀ᵐ p ∂ν, a ≤ p.time)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
    ∃ f : ℕ → KineticPoint d → ℝ,
      (∀ n, Measurable (f n)) ∧ (∀ n p, 0 ≤ f n p ∧ f n p ≤ M + 2) ∧
      (∀ n, ContinuousOn (duhamelPotential K T (f n))
        (evolutionPastClosedCylinder Ω γ T)) ∧
      (∀ n, IsWeakTransportedSolution B b
        (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
        (duhamelPotential K T (f n) ∘ evolutionHomeomorph d) (fun _ => 0)) ∧
      (∀ᵐ p ∂ν, Tendsto (fun n => duhamelPotential K T (f n) p) atTop
        (𝓝 (duhamelPotential K T F p)))  := by
  have ae_tendsto_duhamelPotential_of_action_ae (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (ν : Measure (KineticPoint d)) [IsFiniteMeasure ν] (a : ℝ) (T : ℝ) (hfloor : ∀ᵐ p ∂ν, a ≤ p.time) (f : ℕ → KineticPoint d → ℝ) (hf : ∀ n, Measurable (f n)) (F : KineticPoint d → ℝ) (hF : Measurable F) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n p, |f n p| ≤ C) (hae : ∀ᵐ q ∂boundedSourceActionMeasure K ν a T,
      Tendsto (fun n => f n ⟨q.1, q.2.1, q.2.2⟩) atTop
        (𝓝 (F ⟨q.1, q.2.1, q.2.2⟩))) :
      ∀ᵐ p ∂ν, Tendsto (fun n => duhamelPotential K T (f n) p) atTop
      (𝓝 (duhamelPotential K T F p)) := by
    classical
    let ρ := ν.prod (volume.restrict (Ioo a T))
    let η := ρ.comap ((↑) : BoundedSourcePair Ω γ → KineticPoint d × ℝ)
    let κ := boundedSourcePairKernel K
    have : ProbabilityTheory.IsFiniteKernel κ := by
      dsimp only [κ, boundedSourcePairKernel]
      infer_instance
    have hD := measurableSet_boundedSourcePairSet hΩ hγ
    have hout : ∀ᵐ q ∂η.compProd κ,
        Tendsto (fun n => f n ⟨q.1.1.2, q.2.1, q.2.2⟩) atTop
          (𝓝 (F ⟨q.1.1.2, q.2.1, q.2.2⟩)) := by
      exact ae_of_ae_map measurable_boundedSourceOutput.aemeasurable hae
    have hvalid : ∀ᵐ q ∂η,
        Tendsto (fun n => duhamelIntegrand K (f n) q.1.1 q.1.2) atTop
          (𝓝 (duhamelIntegrand K F q.1.1 q.1.2)) := by
      filter_upwards [(Measure.ae_ae_of_ae_compProd hout)] with q hq
      have : IsFiniteMeasure (κ q) := inferInstance
      have hi := tendsto_integral_of_dominated_convergence (fun _ => C)
        (fun n => (hf n).aestronglyMeasurable.comp_measurable
          ((KineticPoint.measurable_equivProd_symm d).comp
            (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))))
        (integrable_const C) (fun n => Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]
          exact hb n _) hq
      have he (g : KineticPoint d → ℝ) :
          duhamelIntegrand K g q.1.1 q.1.2 = ∫ w, g ⟨q.1.2, w.1, w.2⟩ ∂κ q := by
        unfold duhamelIntegrand
        have hqvalid : q.1.1.time ≤ q.1.2 ∧
            q.1.1.position ∈ movingDomain Ω γ q.1.1.time := q.2
        rw [dite_eq_left hqvalid]
        rfl
      change Tendsto (fun n => ∫ w, f n ⟨q.1.2, w.1, w.2⟩ ∂κ q)
        atTop (𝓝 (∫ w, F ⟨q.1.2, w.1, w.2⟩ ∂κ q)) at hi
      simpa only [← he] using hi
    have hmap : ∀ᵐ q ∂Measure.map Subtype.val η,
        Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
          (𝓝 (duhamelIntegrand K F q.1 q.2)) := by
      exact (ae_map_iff measurable_subtype_coe.aemeasurable
        (measurableSet_tendsto_fun (fun n =>
          measurable_duhamelIntegrand K hΩ hγ (f n) (hf n))
          (measurable_duhamelIntegrand K hΩ hγ F hF))).2 hvalid
    have hrestricted : ∀ᵐ q ∂ρ.restrict (boundedSourcePairSet Ω γ),
        Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
          (𝓝 (duhamelIntegrand K F q.1 q.2)) := by
      simpa only [η, map_comap_subtype_coe hD] using hmap
    have hpairs : ∀ᵐ q ∂ρ,
        Tendsto (fun n => duhamelIntegrand K (f n) q.1 q.2) atTop
          (𝓝 (duhamelIntegrand K F q.1 q.2)) := by
      filter_upwards [(ae_restrict_iff' hD).mp hrestricted] with q hq
      by_cases hqm : q ∈ boundedSourcePairSet Ω γ
      · exact hq hqm
      · have hz (g : KineticPoint d → ℝ) : duhamelIntegrand K g q.1 q.2 = 0 := by
          unfold duhamelIntegrand
          exact dite_eq_right hqm
        simpa only [hz] using (tendsto_const_nhds :
          Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0))
    filter_upwards [(Measure.ae_ae_of_ae_prod hpairs), hfloor] with p hp hpa
    have hi := tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((measurable_duhamelIntegrand K hΩ hγ (f n) (hf n)).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable.restrict)
      (integrable_const C) (fun n => Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs]
        exact abs_duhamelIntegrand_le K (f n) C hC (hb n) p r) hp
    have he (g : KineticPoint d → ℝ) := duhamelPotential_eq_integral_window K g p (T := T) hpa
    simpa [← he] using hi
  classical
  let μ := boundedSourceActionMeasure K ν a T
  let G : ℝ × EvolutionAmbientState d → ℝ :=
    fun q => F ⟨q.1, q.2.1, q.2.2⟩
  have hG : Measurable G := hF.comp (KineticPoint.measurable_equivProd_symm d)
  obtain ⟨φ, hφ, hφb, hφlim⟩ := exists_boundedSourceSmoothApproximation μ
    (boundedSourceFutureSet Ω γ s T) (isOpen_boundedSourceFutureSet (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγ s T) G hG M hM (fun q => hFb _) (by
      intro q hq
      exact hFz _ hq)
  let f (n : ℕ) := φ n ∘ KineticPoint.equivProd d
  have hfc (n : ℕ) : Continuous (f n) :=
    (hφ n).1.continuous.comp (KineticPoint.homeomorphProd d).continuous
  have hfs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × EvolutionAmbientState d =>
      f n ⟨q.1, q.2.1, q.2.2⟩) := (hφ n).1
  have hfn (n : ℕ) : ∀ p, 0 ≤ f n p := fun p => (hφb n _).1
  have hfb (n : ℕ) : ∀ p, |f n p| ≤ M + 2 := fun p => by
    rw [abs_of_nonneg (hfn n p)]
    exact (hφb n _).2
  have hfsup (n : ℕ) : tsupport (f n) ⊆ evolutionPastOpenCylinder Ω γ T := by
    intro p hp
    change p ∈ tsupport (φ n ∘ KineticPoint.equivProd d) at hp
    rw [boundedSourceTest_support] at hp
    exact ((hφ n).2.2 hp).2
  have hzero (n : ℕ) : ∀ p : KineticPoint d, p.time < s → f n p = 0 := by
    intro p hp
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    change p ∈ tsupport (φ n ∘ KineticPoint.equivProd d) at hm
    rw [boundedSourceTest_support] at hm
    exact (not_lt_of_gt hp) (((hφ n).2.2 hm).1)
  refine ⟨f, fun n => (hfc n).measurable, fun n p => hφb n _, ?_, ?_, ?_⟩
  · intro n
    exact continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal (f n) (hfn n)
      (hfc n) ((hφ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd d))
      (hfs n) T (hfsup n)
  · intro n
    exact duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb
      (f n) (hfc n).measurable (M + 2) (by linarith) (hfb n) s T hsT (hzero n)
  · exact ae_tendsto_duhamelPotential_of_action_ae hΩ hγ ν a T hfloor f
      (fun n => (hfc n).measurable) F hF (M + 2) (by linarith) hfb hφlim

end
open MeasureTheory Set Evolution Occupation Filter
open scoped Topology
section
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsOpenPosMeasure]
  (U K : Set E) (hU : IsOpen U) (hKU : K ⊆ U)
  (hK : IsCompact K) (hKi : K ⊆ closure (interior K))
  (H : Submodule ℝ (Lp ℝ 2 (μ.restrict U))) (hH : IsClosed (H : Set (Lp ℝ 2 (μ.restrict U))))
  (hrep : ∀ u : H, ∃ f : E → ℝ, ContinuousOn f U ∧
    (u.1 : E → ℝ) =ᵐ[μ.restrict U] f)

/-- Chosen continuous representative of a homogeneous L2 class. -/
def continuousWeakRepresentative (u : H) : E → ℝ := (hrep u).choose

omit [NormedSpace ℝ E] [BorelSpace E] [μ.IsOpenPosMeasure] in
/-- The chosen representative is continuous on the open domain. -/
theorem continuousWeakRepresentative_continuous (u : H) :
    ContinuousOn (continuousWeakRepresentative μ U H hrep u) U :=
  (hrep u).choose_spec.1

omit [NormedSpace ℝ E] [BorelSpace E] [μ.IsOpenPosMeasure] in
/-- The chosen representative equals its L2 class almost everywhere. -/
theorem continuousWeakRepresentative_ae (u : H) :
    (u.1 : E → ℝ) =ᵐ[μ.restrict U] continuousWeakRepresentative μ U H hrep u :=
  (hrep u).choose_spec.2

/-- Restriction of the uniquely determined continuous representative to a compact set. -/
def compactRepresentativeMap : H →ₗ[ℝ] C(K, ℝ) := by
  let f := continuousWeakRepresentative μ U H hrep
  have hc (u : H) : ContinuousOn (f u) U :=
    continuousWeakRepresentative_continuous μ U H hrep u
  have he (u : H) : (u.1 : E → ℝ) =ᵐ[μ.restrict U] f u :=
    continuousWeakRepresentative_ae μ U H hrep u
  refine { toFun := fun u => ⟨fun z => f u z, (hc u).comp_continuous
      continuous_subtype_val (fun z => hKU z.2)⟩, map_add' := ?_, map_smul' := ?_ }
  · intro u v
    have hae : f (u + v) =ᵐ[μ.restrict U] (fun z => f u z + f v z) := by
      filter_upwards [he (u + v), he u, he v, Lp.coeFn_add u.1 v.1] with z ha hb hd heq
      change (u.1 + v.1) z = f (u + v) z at ha
      simp only [Pi.add_apply] at heq
      linarith
    have hpoint := Measure.eqOn_open_of_ae_eq hae hU (hc (u + v)) ((hc u).add (hc v))
    ext z
    exact hpoint (hKU z.2)
  · intro c u
    have hae : f (c • u) =ᵐ[μ.restrict U] (fun z => c * f u z) := by
      filter_upwards [he (c • u), he u, Lp.coeFn_smul c u.1] with z ha hb heq
      change (c • u.1) z = f (c • u) z at ha
      simp only [Pi.smul_apply, smul_eq_mul] at heq
      rw [← ha, heq, hb]
    have hpoint := Measure.eqOn_open_of_ae_eq hae hU (hc (c • u))
      (continuousOn_const.mul (hc u))
    ext z
    exact hpoint (hKU z.2)

/-- Evaluation agrees pointwise with any actual continuous representative of the class. -/
theorem compactRepresentativeMap_apply_eq (u : H) (g : E → ℝ)
    (hg : ContinuousOn g U) (he : (u.1 : E → ℝ) =ᵐ[μ.restrict U] g) (z : K) :
    compactRepresentativeMap μ U K hU hKU H hrep u z = g z := by
  have hpoint := Measure.eqOn_open_of_ae_eq ((continuousWeakRepresentative_ae μ U H hrep u).symm.trans he) hU
    (continuousWeakRepresentative_continuous μ U H hrep u) hg
  exact hpoint (hKU z.2)

include hK hKi hH in
/-- Compact evaluation of the continuous representatives is a continuous linear map. -/
theorem continuous_compactRepresentativeMap :
    Continuous (compactRepresentativeMap μ U K hU hKU H hrep) := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompleteSpace H := hH.isComplete.completeSpace_coe
  apply LinearMap.continuous_of_seq_closed_graph
  intro u x y hu hy
  let f := continuousWeakRepresentative μ U H hrep
  obtain ⟨σ, hσ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp (continuous_subtype_val.tendsto x |>.comp hu)).exists_seq_tendsto_ae
  let yext : E → ℝ := fun z => if hz : z ∈ K then y ⟨z, hz⟩ else 0
  have hyc : ContinuousOn yext K := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert y.continuous using 1
    ext z
    exact dite_eq_left z.2
  have heq : yext =ᵐ[μ.restrict K] f x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hKU hae,
      ae_restrict_of_ae_restrict_of_subset hKU (ae_all_iff.mpr (fun n => continuousWeakRepresentative_ae μ U H hrep (u n))),
      ae_restrict_of_ae_restrict_of_subset hKU (continuousWeakRepresentative_ae μ U H hrep x), ae_restrict_mem hK.measurableSet]
      with z hz hs hxz hzK
    have hpσ := ((continuous_eval_const ⟨z, hzK⟩).tendsto y |>.comp hy).comp hσ.tendsto_atTop
    have hactual : Tendsto (fun n => f (u (σ n)) z) atTop (𝓝 (f x z)) := by
      rw [hxz] at hz
      exact hz.congr' (Eventually.of_forall fun n => hs (σ n))
    have hp' := hpσ
    change yext z = f x z
    rw [show yext z = y ⟨z, hzK⟩ from dite_eq_left hzK]
    exact tendsto_nhds_unique hp' hactual
  have hpoint := Measure.eqOn_of_ae_eq heq hyc ((continuousWeakRepresentative_continuous μ U H hrep x).mono hKU) hKi
  ext z
  change y z = f x z
  simpa only [yext, dite_eq_left z.2] using hpoint z.2

end
variable {d : ℕ}

/-- A genuine smooth compact test supported in the chosen open domain. -/
structure BoundedSourceSmoothTest (U : Set (EvolutionVec d)) where
  /-- The ambient smooth test function. -/
  toFun : EvolutionVec d → ℝ
  /-- Full smoothness of the test. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  /-- Compactness of the closed support. -/
  compact : HasCompactSupport toFun
  /-- The closed support lies inside the testing domain. -/
  support : tsupport toFun ⊆ U

/-- The literal adjoint of a compact smooth test is in restricted L2. -/
theorem boundedSource_testAdjoint_memLp (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U) :
    MemLp (transportedAdjoint B b φ.toFun) 2 (volume.restrict U) :=
  (contDiff_transportedAdjoint hB hb φ.smooth).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_transportedAdjoint φ.compact)

/-- Pairing a restricted L2 function with the actual kinetic adjoint test. -/
def boundedSource_testFunctional (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U) :
    Lp ℝ 2 (volume.restrict U) →L[ℝ] ℝ :=
  innerSL ℝ ((boundedSource_testAdjoint_memLp B b hB hb U φ).toLp
    (transportedAdjoint B b φ.toFun))

/-- This continuous functional is exactly the distributional test integral. -/
theorem boundedSource_testFunctional_apply (B : FullKineticCoefficient d)
    (b : PDE.Vec d → PDE.Vec d) (hB : IsSmoothFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (U : Set (EvolutionVec d)) (φ : BoundedSourceSmoothTest U)
    (u : Lp ℝ 2 (volume.restrict U)) :
    boundedSource_testFunctional B b hB hb U φ u =
      ∫ z in U, u z * transportedAdjoint B b φ.toFun z := by
  rw [boundedSource_testFunctional, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(boundedSource_testAdjoint_memLp B b hB hb U φ).coeFn_toLp] with z hz
  simp only [RCLike.inner_apply, conj_trivial, hz]







/-- Homogeneous L2 limits have a continuous representative identified by every actual
homogeneous approximating sequence at every point where that sequence converges. -/
theorem exists_continuousRepresentative_identified_by_homogeneous_limits
    (hH : HormanderHypoellipticityStatement) {d : ℕ}
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (hB : IsSmoothFullKineticCoefficient B) (hb : IsSmoothDrift b)
    (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (U K : Set (EvolutionVec d)) (hU : IsOpen U) (hK : IsCompact K)
    (hKi : K ⊆ closure (interior K)) (hKU : K ⊆ U)
    [IsFiniteMeasure (volume.restrict U)]
    (u : EvolutionVec d → ℝ) (hu : MemLp u 2 (volume.restrict U))
    (hw : IsWeakTransportedSolution B b U u (fun _ => 0)) :
    ∃ v : EvolutionVec d → ℝ, ContinuousOn v U ∧ u =ᵐ[volume.restrict U] v ∧
      ∀ (f : ℕ → EvolutionVec d → ℝ)
        (hf : ∀ n, MemLp (f n) 2 (volume.restrict U)),
        (∀ n, ContinuousOn (f n) U) →
        (∀ n, IsWeakTransportedSolution B b U (f n) (fun _ => 0)) →
        Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)) →
        ∀ z ∈ K, Tendsto (fun n => f n z) atTop (𝓝 (u z)) → u z = v z     := by
  let boundedSourceHomogeneousL2Space :=
    ⨅ φ : BoundedSourceSmoothTest U, (boundedSource_testFunctional B b hB hb U φ).ker
  have boundedSourceHomogeneousL2Space_hasContinuousRepresentative [IsFiniteMeasure (volume.restrict U)] (u : boundedSourceHomogeneousL2Space) :
      ∃ f : EvolutionVec d → ℝ, ContinuousOn f U ∧
      (u.1 : EvolutionVec d → ℝ) =ᵐ[volume.restrict U] f := open Occupation in by
    have boundedSourceHomogeneousL2Space_isWeak :
        IsWeakTransportedSolution B b U (u.1 : EvolutionVec d → ℝ) (fun _ => 0) := by
      have hi : IntegrableOn (u.1 : EvolutionVec d → ℝ) U :=
        MemLp.integrable (by norm_num) (Lp.memLp u.1)
      refine ⟨hi.locallyIntegrableOn, fun φ hφ hc hs => ?_⟩
      have hm := u.2
      change u.1 ∈ ⨅ ψ : BoundedSourceSmoothTest U,
        (boundedSource_testFunctional B b hB hb U ψ).ker at hm
      simp only [Submodule.mem_iInf] at hm
      have hz := hm (⟨φ, hφ, hc, hs⟩ : BoundedSourceSmoothTest U)
      change boundedSource_testFunctional B b hB hb U ⟨φ, hφ, hc, hs⟩ u.1 = 0 at hz
      rw [boundedSource_testFunctional_apply] at hz
      simpa [integral_zero] using hz
    obtain ⟨f, hf, he⟩ := exists_smooth_representative_transported_source hH hlam hB hell hb
      hm hcoerc hU (boundedSourceHomogeneousL2Space_isWeak) contDiffOn_const
    exact ⟨f, hf.continuousOn, he⟩
  have mem_boundedSourceHomogeneousL2Space_of_isWeak (u : EvolutionVec d → ℝ) (hu : MemLp u 2 (volume.restrict U)) (hw : IsWeakTransportedSolution B b U u (fun _ => 0)) :
      hu.toLp u ∈ boundedSourceHomogeneousL2Space := by
    change hu.toLp u ∈ ⨅ φ : BoundedSourceSmoothTest U,
      (boundedSource_testFunctional B b hB hb U φ).ker
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    intro φ
    change boundedSource_testFunctional B b hB hb U φ (hu.toLp u) = 0
    rw [boundedSource_testFunctional_apply]
    have he : (∫ z in U, (hu.toLp u) z * transportedAdjoint B b φ.toFun z) =
        ∫ z in U, u z * transportedAdjoint B b φ.toFun z := by
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp] with z hz
      rw [hz]
    rw [he]
    simpa [integral_zero] using (hw.2 φ.toFun φ.smooth φ.compact φ.support)
  have isClosed_boundedSourceHomogeneousL2Space :
      IsClosed (boundedSourceHomogeneousL2Space :
      Set (Lp ℝ 2 (volume.restrict U))) := by
    change IsClosed (↑(⨅ φ : BoundedSourceSmoothTest U,
      (boundedSource_testFunctional B b hB hb U φ).ker) : Set (Lp ℝ 2 (volume.restrict U)))
    rw [Submodule.coe_iInf]
    exact isClosed_iInter fun φ => (boundedSource_testFunctional B b hB hb U φ).isClosed_ker
  classical
  let H := boundedSourceHomogeneousL2Space
  have hrep := boundedSourceHomogeneousL2Space_hasContinuousRepresentative
  let x : H := ⟨hu.toLp u, mem_boundedSourceHomogeneousL2Space_of_isWeak u hu hw⟩
  let v := continuousWeakRepresentative volume U H hrep x
  refine ⟨v, (continuousWeakRepresentative_continuous volume U H hrep x), (hu.coeFn_toLp.symm.trans (continuousWeakRepresentative_ae volume U H hrep x)), ?_⟩
  intro f hf hfc hfw hlim z hz hp
  let fn (n : ℕ) : H := ⟨(hf n).toLp (f n),
    mem_boundedSourceHomogeneousL2Space_of_isWeak (f n) (hf n) (hfw n)⟩
  have hfn : Tendsto fn atTop (𝓝 x) := tendsto_subtype_rng.mpr hlim
  let L := compactRepresentativeMap volume U K hU hKU H hrep
  have hL := continuous_compactRepresentativeMap volume U K hU hKU hK hKi H isClosed_boundedSourceHomogeneousL2Space hrep
  have hpoint := (continuous_eval_const (⟨z, hz⟩ : K)).tendsto (L x) |>.comp ((hL.tendsto x).comp hfn)
  have heq (n : ℕ) : L (fn n) ⟨z, hz⟩ = f n z :=
    compactRepresentativeMap_apply_eq volume U K hU hKU H hrep (fn n) (f n)
      (hfc n) (hf n).coeFn_toLp ⟨z, hz⟩
  have hvlim : Tendsto (fun n => f n z) atTop (𝓝 (v z)) := by
    exact hpoint.congr' (Eventually.of_forall heq)
  exact tendsto_nhds_unique hp hvlim

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

section



namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open MeasureTheory

/-- The literal real square integral is the square of the real L2 seminorm. -/
theorem integral_square_eq_eLpNorm_two_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (f : α → ℝ) (hf : MemLp f 2 μ) :
    (∫ x, f x ^ 2 ∂μ) = (eLpNorm f 2 μ).toReal ^ 2 := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) ENNReal.ofNat_ne_top]
  simp [ENNReal.toReal_ofReal (Real.rpow_nonneg
    (integral_nonneg fun _ => sq_nonneg _) _), ENNReal.toReal_ofNat, Real.rpow_two]
  exact (Real.rpow_inv_natCast_pow
    (integral_nonneg fun _ => sq_nonneg _) (by norm_num)).symm


end HypoellipticAleksandrov.Parabolic.LocalHolder

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Filter Set Evolution
open scoped Topology

/-- Uniformly bounded functions on a finite measure space converge strongly in L2 when
an actual almost-everywhere pointwise limit is supplied. -/
theorem tendsto_toLp_two_of_bounded_ae
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    (f : ℕ → E → ℝ) (F : E → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hF : MemLp F 2 μ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ x ∂μ, |f n x| ≤ C)
    (hFb : ∀ᵐ x ∂μ, |F x| ≤ C)
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hF.toLp F)) := by
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖(f n x - F x) ^ 2‖ ≤ (2 * C) ^ 2 := by
    filter_upwards [hb n, hFb] with x hx hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hh := (sq_le_sq₀ (abs_nonneg (f n x - F x))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC)).2 (by simpa only [two_mul] using (abs_sub _ _).trans (add_le_add hx hy))
    simpa using hh
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => (f n x - F x) ^ 2) μ := by
    exact ((hf n).aestronglyMeasurable.sub hF.aestronglyMeasurable).pow 2
  have ha : ∀ᵐ x ∂μ, Tendsto (fun n => (f n x - F x) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx
    have hc : Tendsto (fun _ : ℕ => F x) atTop (𝓝 (F x)) := tendsto_const_nhds
    simpa [zero_pow (by norm_num : 2 ≠ 0)] using (hx.sub hc).pow 2
  have hlim : Tendsto (fun n => ∫ x, (f n x - F x) ^ 2 ∂μ) atTop (𝓝 0) := by
    simpa only [integral_zero] using (tendsto_integral_of_dominated_convergence (fun _ => (2 * C) ^ 2) hm (integrable_const _) hbound ha)
  have hnorm (n : ℕ) : ‖(hf n).toLp (f n) - hF.toLp F‖ ^ 2 =
      ∫ x, (f n x - F x) ^ 2 ∂μ := by
    rw [← (hf n).toLp_sub hF, Lp.norm_toLp]
    exact (Parabolic.LocalHolder.integral_square_eq_eLpNorm_two_sq (f n - F)
      ((hf n).sub hF)).symm
  have hsqrt := Real.continuous_sqrt.tendsto 0 |>.comp hlim
  change Tendsto (fun n => Real.sqrt (∫ x, (f n x - F x) ^ 2 ∂μ))
    atTop (𝓝 (Real.sqrt 0)) at hsqrt
  have hn : Tendsto (fun n => ‖(hf n).toLp (f n) - hF.toLp F‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← hnorm, Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_zero] using hsqrt
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

section
open MeasureTheory Set Filter
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}



/-- Finite-horizon potentials are additive for the actual signed bounded sources. -/
theorem duhamelPotential_add_bounded (K : MovingFiberKernel Ω γ)
    (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (f g : KineticPoint d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hfb : ∀ p, |f p| ≤ M) (hgb : ∀ p, |g p| ≤ N)
    (T : ℝ) (p : KineticPoint d) :
    duhamelPotential K T (fun p => f p + g p) p =
      duhamelPotential K T f p + duhamelPotential K T g p  := by
  have duhamelIntegrand_add_bounded (p : KineticPoint d) (r : ℝ) :
      duhamelIntegrand K (fun p => f p + g p) p r =
      duhamelIntegrand K f p r + duhamelIntegrand K g p r := by
    have duhamelSourceIntegral_add_bounded (q : EvolutionQuery Ω γ) :
        duhamelSourceIntegral K (fun p => f p + g p) q =
        duhamelSourceIntegral K f q + duhamelSourceIntegral K g q := by
      have hm : Measurable (fun w : EvolutionAmbientState d =>
          (⟨q.1.2.1, w.1, w.2⟩ : KineticPoint d)) :=
        (KineticPoint.measurable_equivProd_symm d).comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
      have hfi : Integrable (fun w : EvolutionAmbientState d => f ⟨q.1.2.1, w.1, w.2⟩)
          (K.master q) := ⟨(hf.comp hm).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]; exact hfb _)⟩
      have hgi : Integrable (fun w : EvolutionAmbientState d => g ⟨q.1.2.1, w.1, w.2⟩)
          (K.master q) := ⟨(hg.comp hm).aestronglyMeasurable,
        HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs]; exact hgb _)⟩
      exact integral_add hfi hgi
    unfold duhamelIntegrand
    split
    · exact duhamelSourceIntegral_add_bounded _
    · exact (zero_add 0).symm
  unfold duhamelPotential
  simp_rw [duhamelIntegrand_add_bounded]
  exact integral_add (integrableOn_duhamelIntegrand_bounded K hΩ hγ f hf M hM hfb p T)
    (integrableOn_duhamelIntegrand_bounded K hΩ hγ g hg N hN hgb p T)

/-- Negation is retained exactly by the master-kernel source integrand. -/
theorem duhamelIntegrand_neg (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (p : KineticPoint d) (r : ℝ) :
    duhamelIntegrand K (fun p => -g p) p r = -duhamelIntegrand K g p r := by
  unfold duhamelIntegrand
  split
  · exact integral_neg _
  · exact neg_zero.symm

/-- Negation is retained exactly by the literal finite-horizon potential. -/
theorem duhamelPotential_neg (K : MovingFiberKernel Ω γ)
    (g : KineticPoint d → ℝ) (T : ℝ) (p : KineticPoint d) :
    duhamelPotential K T (fun p => -g p) p = -duhamelPotential K T g p := by
  unfold duhamelPotential
  simp_rw [duhamelIntegrand_neg]
  exact integral_neg _



end
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/-- Every signed bounded Borel source supported in the past domain has a continuous
literal potential there, with only the Hörmander input. -/
theorem continuousOn_duhamelPotential_bounded_signed
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, |F p| ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → F p = 0) :
    ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ T)  := by
  have continuousOn_duhamelPotential_bounded_nonneg (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K) (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B) (hb : IsSmoothDrift b) (lam : ℝ) (Lam : ℝ) (m : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hell : HasEverywhereLoewnerBounds lam Lam B) (hcoerc : HasUnitDirectionDriftCoercivity m b) (T : ℝ) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M) (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → F p = 0) :
      ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ T) := open Metric in by
    have continuousOn_duhamelFuture_before_source (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K) (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B) (hb : IsSmoothDrift b) (lam : ℝ) (Lam : ℝ) (m : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hell : HasEverywhereLoewnerBounds lam Lam B) (hcoerc : HasUnitDirectionDriftCoercivity m b) (s : ℝ) (T : ℝ) (hsT : s ≤ T) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M) (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
        ContinuousOn (duhamelPotential K T F) (evolutionPastOpenCylinder Ω γ s) := by
      have continuousOn_duhamelFuture_compact_collar (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ) (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d) (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ) (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K) (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B) (hb : IsSmoothDrift b) (lam : ℝ) (Lam : ℝ) (m : ℝ) (hlam : 0 < lam) (hm : 0 < m) (hell : HasEverywhereLoewnerBounds lam Lam B) (hcoerc : HasUnitDirectionDriftCoercivity m b) (a : ℝ) (s : ℝ) (T : ℝ) (has : a ≤ s) (hsT : s ≤ T) (U : Set (EvolutionVec d)) (C : Set (EvolutionVec d)) (hU : IsOpen U) (hC : IsCompact C) (hCi : C ⊆ closure (interior C)) (hCU : C ⊆ U) [IsFiniteMeasure (volume.restrict U)] (hUpast : U ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s) (hUfloor : ∀ z ∈ U, a ≤ (evolutionHomeomorph d z).time) (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M) (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M) (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
          ContinuousOn (duhamelPotential K T F ∘ evolutionHomeomorph d) C := by
        classical
        let P := evolutionHomeomorph d
        let u := duhamelPotential K T F ∘ P
        let μ := volume.restrict U
        have hzero : ∀ p : KineticPoint d, p.time < s → F p = 0 := by
          intro p hp
          apply hFz p
          intro h
          exact (not_lt_of_gt hp) h.1
        have hw := boundedSource_ambientWeak_restrict hUpast B b u (duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb F hF M hM (fun p => by rw [abs_of_nonneg (hFb p).1]; exact (hFb p).2) s T hsT hzero)
        have hbound (g : KineticPoint d → ℝ) (Cg : ℝ) (hCg : 0 ≤ Cg)
            (hgb : ∀ p, |g p| ≤ Cg) : ∀ z ∈ U,
            |duhamelPotential K T g (P z)| ≤ (T - a) * Cg := by
          intro z hz
          exact (abs_duhamelPotential_le K g Cg hCg hgb (P z) T ((hUpast hz).1.le.trans hsT)).trans
            (mul_le_mul_of_nonneg_right (sub_le_sub_left (hUfloor z hz) T) hCg)
        have hub : ∀ᵐ z ∂μ, |u z| ≤ (T - a) * (M + 2) := by
          apply ae_restrict_of_forall_mem hU.measurableSet
          intro z hz
          exact hbound F (M + 2) (by linarith) (fun p => by
            rw [abs_of_nonneg (hFb p).1]; linarith [(hFb p).2]) z hz
        have hu : MemLp u 2 μ := MemLp.of_bound ((measurable_duhamelPotential K hΩ hγ T F hF).comp P.measurable).aestronglyMeasurable.restrict
          ((T - a) * (M + 2)) (by simpa using hub)
        obtain ⟨v, hvc, hve, hidentify⟩ :=
          exists_continuousRepresentative_identified_by_homogeneous_limits hH B b hB hb
            lam Lam m hlam hm hell hcoerc U C hU hC hCi hCU u hu hw
        have heq : EqOn u v C := by
          intro z hz
          let ν : Measure (KineticPoint d) := μ.map P + Measure.dirac (P z)
          have hfloor : ∀ᵐ p ∂ν, a ≤ p.time := by
            apply ae_add_measure_iff.mpr
            refine ⟨?_, ?_⟩
            · apply (ae_map_iff P.measurable.aemeasurable
                (measurableSet_le measurable_const continuous_time.measurable)).2
              exact ae_restrict_of_forall_mem hU.measurableSet hUfloor
            · simpa only [ae_dirac_eq, eventually_pure] using hUfloor z (hCU hz)
          obtain ⟨f, hfm, hfb, hfc, hfw, hlim⟩ := exists_duhamelFuture_approximating_sequence
            hΩa hΩ hγ B b S K hreal hB hBs hb a s T hsT ν hfloor F hF M hM hFb hFz
          let fn (n : ℕ) := duhamelPotential K T (f n) ∘ P
          have hfnm (n : ℕ) : Measurable (fn n) :=
            (measurable_duhamelPotential K hΩ hγ T (f n) (hfm n)).comp P.measurable
          have hfnb (n : ℕ) : ∀ᵐ w ∂μ, |fn n w| ≤ (T - a) * (M + 2) := by
            apply ae_restrict_of_forall_mem hU.measurableSet
            exact hbound (f n) (M + 2) (by linarith) (fun p => by
              rw [abs_of_nonneg (hfb n p).1]; exact (hfb n p).2)
          have hfn (n : ℕ) : MemLp (fn n) 2 μ :=
            MemLp.of_bound (hfnm n).aestronglyMeasurable.restrict ((T - a) * (M + 2))
              (by simpa using hfnb n)
          have hconv := ae_add_measure_iff.mp hlim
          have hae : ∀ᵐ w ∂μ, Tendsto (fun n => fn n w) atTop (𝓝 (u w)) :=
            ae_of_ae_map P.measurable.aemeasurable hconv.1
          have hp : Tendsto (fun n => fn n z) atTop (𝓝 (u z)) := by
            simpa only [ae_dirac_eq, eventually_pure, fn, u, Function.comp_def] using hconv.2
          have hfnc (n : ℕ) : ContinuousOn (fn n) U :=
            (hfc n).comp P.continuous.continuousOn (fun w hw =>
              ⟨(hUpast hw).1.le.trans hsT, subset_closure (hUpast hw).2⟩)
          have hfnw (n : ℕ) := boundedSource_ambientWeak_restrict hUpast B b (fn n) (hfw n)
          exact hidentify fn hfn hfnc hfnw (tendsto_toLp_two_of_bounded_ae μ fn u hfn hu ((T - a) * (M + 2)) (mul_nonneg (sub_nonneg.mpr (has.trans hsT)) (by linarith)) hfnb hub hae) z hz hp
        exact (hvc.mono hCU).congr (fun z hz => heq hz)
      classical
      let P := evolutionHomeomorph d
      let D := P ⁻¹' evolutionPastOpenCylinder Ω γ s
      have hD : IsOpen D :=
        (isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa)
          hγ s).preimage P.continuous
      have hc : ContinuousOn (duhamelPotential K T F ∘ P) D := by
        intro z hz
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD z hz
        let U := ball z r
        let C := closedBall z (r / 2)
        have hC : IsCompact C := isCompact_closedBall z (r / 2)
        have hCU : C ⊆ U := closedBall_subset_ball (half_lt_self hr)
        have hCi : C ⊆ closure (interior C) := by
          rw [interior_closedBall z (half_pos hr).ne', closure_ball z (half_pos hr).ne']
        have hbig : IsCompact (closedBall z r) := isCompact_closedBall z r
        let : IsFiniteMeasure (volume.restrict U) := ⟨by
          rw [Measure.restrict_apply_univ]
          exact (measure_mono ball_subset_closedBall).trans_lt hbig.measure_lt_top⟩
        have htime : Continuous (fun w : EvolutionVec d => (P w).time) :=
          continuous_time.comp P.continuous
        obtain ⟨q, hq, hmin⟩ := hbig.exists_isMinOn
          ⟨z, mem_closedBall_self hr.le⟩ htime.continuousOn
        let a := min (P q).time s
        have hfloor : ∀ w ∈ U, a ≤ (P w).time := by
          intro w hw
          exact (min_le_left _ _).trans (hmin (ball_subset_closedBall hw))
        exact ((continuousOn_duhamelFuture_compact_collar hΩa hΩ hγ B b S K hreal hB hBs hb lam Lam m hlam hm hell hcoerc a s T (min_le_right _ _) hsT U C isOpen_ball hC hCi hCU hball hfloor F hF M hM hFb hFz).continuousAt (closedBall_mem_nhds z (half_pos hr))).continuousWithinAt
      have hcomp := hc.comp P.symm.continuous.continuousOn (fun p hp => by
        simpa [D, Homeomorph.apply_symm_apply] using hp)
      simpa only [Function.comp_def, Homeomorph.apply_symm_apply] using hcomp
    have duhamelPotential_eq_short_terminal (g : KineticPoint d → ℝ) (s : ℝ) (hsT : s ≤ T) (hgz : ∀ p, s < p.time → g p = 0) (p : KineticPoint d) :
        duhamelPotential K T g p = duhamelPotential K s g p := by
      have duhamelIntegrand_zero_above_source (r : ℝ) (hr : s < r) :
          duhamelIntegrand K g p r = 0 := by
        unfold duhamelIntegrand
        split
        · change (∫ w, g ⟨r, w.1, w.2⟩ ∂K.master _) = 0
          have hz (w : EvolutionAmbientState d) : g ⟨r, w.1, w.2⟩ = 0 :=
            hgz ⟨r, w.1, w.2⟩ hr
          simp_rw [hz]
          exact integral_zero _ _
        · rfl
      unfold duhamelPotential
      apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero measurableSet_Ioc.nullMeasurableSet
        (fun r hr => ⟨hr.1, hr.2.trans hsT⟩)
      exact Eventually.of_forall fun r hr => duhamelIntegrand_zero_above_source r
        (lt_of_not_ge fun h => hr.2 ⟨hr.1.1, h⟩)
    classical
    intro p hp
    have hc : ContinuousAt (duhamelPotential K T F) p := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      let δ := min ((T - p.time) / 2) (ε / (16 * (M + 1)))
      have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hp.1)) (by positivity)
      have hδT : δ ≤ (T - p.time) / 2 := min_le_left _ _
      have hδε : δ * (16 * (M + 1)) ≤ ε :=
        (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
      let s := p.time + δ
      have hps : p.time < s := by dsimp [s]; linarith
      have hsT : s ≤ T := by dsimp [s]; linarith
      let f := {q : KineticPoint d | s < q.time}.indicator F
      let g := {q : KineticPoint d | q.time ≤ s}.indicator F
      have hfm : Measurable f := hF.indicator (measurableSet_lt measurable_const
        continuous_time.measurable)
      have hgm : Measurable g := hF.indicator (measurableSet_le continuous_time.measurable
        measurable_const)
      have hfb : ∀ q, 0 ≤ f q ∧ f q ≤ M := by
        intro q
        by_cases hq : s < q.time
        · simpa [f, indicator_apply, ite_eq_left hq] using hFb q
        · simp only [f, indicator_apply, mem_ofPred_eq, ite_eq_right hq]
          exact ⟨le_rfl, hM⟩
      have hgb : ∀ q, 0 ≤ g q ∧ g q ≤ M := by
        intro q
        by_cases hq : q.time ≤ s
        · simpa [g, indicator_apply, ite_eq_left hq] using hFb q
        · simp only [g, indicator_apply, mem_ofPred_eq, ite_eq_right hq]
          exact ⟨le_rfl, hM⟩
      have hfz : ∀ q, KineticPoint.equivProd d q ∉ boundedSourceFutureSet Ω γ s T →
          f q = 0 := by
        intro q hq
        by_cases hqt : s < q.time
        · have hqpast : KineticPoint.equivProd d q ∉ boundedSourcePast Ω γ T :=
            fun h => hq ⟨hqt, h⟩
          simp [f, indicator_apply, ite_eq_left hqt, hFz q hqpast]
        · simp [f, indicator_apply, ite_eq_right hqt]
      have hgzero : ∀ q : KineticPoint d, s < q.time → g q = 0 := by
        intro q hq
        simp [g, indicator_apply, ite_eq_right (not_le_of_gt hq)]
      have hsplit : F = (fun q => f q + g q) := by
        funext q
        by_cases hq : s < q.time
        · simp [f, g, indicator_apply, ite_eq_left hq, ite_eq_right (not_le_of_gt hq)]
        · simp [f, g, indicator_apply, ite_eq_right hq, ite_eq_left (le_of_not_gt hq)]
      have hfa : ∀ q, |f q| ≤ M := fun q => by
        rw [abs_of_nonneg (hfb q).1]; exact (hfb q).2
      have hga : ∀ q, |g q| ≤ M := fun q => by
        rw [abs_of_nonneg (hgb q).1]; exact (hgb q).2
      have heq (q : KineticPoint d) : duhamelPotential K T F q =
          duhamelPotential K T f q + duhamelPotential K T g q := by
        conv_lhs => rw [hsplit]
        exact duhamelPotential_add_bounded K hΩ hγ f g hfm hgm M M hM hM hfa hga T q
      have hfutureAt := (continuousOn_duhamelFuture_before_source hΩa hΩ hγ B b S K hreal hB hBs hb lam Lam m hlam hm hell hcoerc s T hsT f hfm M hM hfb hfz).continuousAt
        ((isOpen_evolutionPastOpenCylinder (isOpen_of_isAdmissibleEvolutionDomain hΩa)
          hγ s).mem_nhds ⟨hps, hp.2⟩)
      filter_upwards [(hfutureAt.eventually (Metric.ball_mem_nhds _ (half_pos hε))), (continuous_time.continuousAt.eventually (Metric.ball_mem_nhds p.time hδ))] with q hq hqt
      change dist (duhamelPotential K T f q) (duhamelPotential K T f p) < ε / 2 at hq
      change dist q.time p.time < δ at hqt
      rw [Real.dist_eq] at hq hqt
      have hqtime : q.time ≤ s := by
        have ht := (abs_lt.mp hqt).2
        dsimp only [s]
        linarith
      have hrecent (w : KineticPoint d) (hws : w.time ≤ s) :
          |duhamelPotential K T g w| ≤ (s - w.time) * M := by
        rw [duhamelPotential_eq_short_terminal g s hsT hgzero w]
        exact abs_duhamelPotential_le K g M hM hga w s hws
      have hbq : |duhamelPotential K T g q| ≤ 2 * δ * M := by
        have ht := (abs_lt.mp hqt).1
        exact (hrecent q hqtime).trans (mul_le_mul_of_nonneg_right (by dsimp [s]; linarith) hM)
      have hbp : |duhamelPotential K T g p| ≤ δ * M := by
        simpa only [s, add_sub_cancel_left] using hrecent p hps.le
      have habs : |duhamelPotential K T F q - duhamelPotential K T F p| ≤
          |duhamelPotential K T f q - duhamelPotential K T f p| +
            |duhamelPotential K T g q| + |duhamelPotential K T g p| := by
        rw [heq q, heq p]
        have hid (a b c d : ℝ) : (a + b) - (c + d) = (a - c) + (b - d) := by ring
        rw [hid]
        exact (abs_add_le _ _).trans (by
          have hh := abs_sub (duhamelPotential K T g q) (duhamelPotential K T g p)
          linarith)
      rw [Real.dist_eq]
      nlinarith
    exact hc.continuousWithinAt
  let f := fun p => max (F p) 0
  let g := fun p => max (-F p) 0
  have hfm : Measurable f := hF.max measurable_const
  have hgm : Measurable g := hF.neg.max measurable_const
  have hfb (p : KineticPoint d) : 0 ≤ f p ∧ f p ≤ M :=
    ⟨le_max_right _ _, max_le ((le_abs_self _).trans (hFb p)) hM⟩
  have hgb (p : KineticPoint d) : 0 ≤ g p ∧ g p ≤ M :=
    ⟨le_max_right _ _, max_le ((neg_le_abs _).trans (hFb p)) hM⟩
  have hfz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → f p = 0 := by
    intro p hp
    simp only [f, hFz p hp, max_self]
  have hgz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourcePast Ω γ T → g p = 0 := by
    intro p hp
    simp [g, hFz p hp, max_self]
  have hsplit : F = (fun p => f p + -g p) := by
    funext p
    change F p = max (F p) 0 + -max (-F p) 0
    by_cases hp : 0 ≤ F p
    · rw [max_eq_left hp, max_eq_right (neg_nonpos.mpr hp), neg_zero, add_zero]
    · rw [max_eq_right (le_of_not_ge hp), max_eq_left (by linarith), neg_neg, zero_add]
  have heq : duhamelPotential K T F =
      (fun p => duhamelPotential K T f p - duhamelPotential K T g p) := by
    funext p
    conv_lhs => rw [hsplit]
    rw [duhamelPotential_add_bounded K hΩ hγ f (fun p => -g p) hfm hgm.neg M M hM hM
      (fun p => by rw [abs_of_nonneg (hfb p).1]; exact (hfb p).2)
      (fun p => by rw [abs_neg, abs_of_nonneg (hgb p).1]; exact (hgb p).2),
      duhamelPotential_neg]
    rfl
  rw [heq]
  exact (continuousOn_duhamelPotential_bounded_nonneg hΩa hΩ hγ B b S K hreal hB hBs hb lam Lam m hlam hm hell hcoerc T f hfm M hM hfb hfz).sub (continuousOn_duhamelPotential_bounded_nonneg hΩa hΩ hγ B b S K hreal hB hBs hb lam Lam m hlam hm hell hcoerc T g hgm M hM hgb hgz)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

end

