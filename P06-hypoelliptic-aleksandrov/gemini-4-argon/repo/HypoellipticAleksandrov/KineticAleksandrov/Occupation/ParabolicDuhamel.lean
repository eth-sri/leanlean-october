module

public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import HypoellipticAleksandrov.KineticAleksandrov.Evolution.ExternalRegularity
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelWeak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Lemma 2.3: parabolic Duhamel potentials

Let `P` be the parabolic marginal kernel (`parabolicMarginalKernel`) of a moving-fiber kernel with
the parabolic marginal bundle for a `z`-independent smooth elliptic coefficient `B`, and let
`0 ≤ g ∈ C_c^∞(U₀)` with `U₀ = {(σ, v) : σ < T, v ∈ Ω_σ}`.  The parabolic Duhamel potential
`W(σ, v) = ∫_σ^T ∫ g(r, w) P_{σ,r}(v, dw) dr` is smooth in `U₀`, satisfies
`0 ≤ W ≤ (T - σ) sup g` and `∂_σ W + B : D_v² W = -g` in `U₀`, and extends continuously by zero
to the terminal face `σ = T` and the lateral frontier.  Hörmander's theorem enters only through the
explicit hypothesis `hH`.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Occupation

open MeasureTheory Set Filter
open HypoellipticAleksandrov HypoellipticAleksandrov.Parabolic
open HypoellipticAleksandrov.KineticAleksandrov.Evolution
open scoped Topology
open scoped MatrixOrder

variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- **Parabolic Duhamel lemma** (Lemma 2.3), without the transport data. -/
theorem parabolic_duhamel (hH : HormanderHypoellipticityStatement)
    (hΩ : IsAdmissibleEvolutionDomain Ω) (hγ : IsContinuousPiecewiseC1 γ) {lam Lam B} (hB : SectionTwo.IsSectionTwoCoefficient lam Lam B)
    (K : MovingFiberKernel Ω γ)
    (hP : SectionTwo.HasParabolicMarginalBundle Ω γ
      (measurableSet_of_isAdmissibleEvolutionDomain hΩ) (zIndependentCoefficient B) K)
    (T : ℝ) (g : TimeVelocity d → ℝ) (hg0 : ∀ p, 0 ≤ g p) (hgs : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1}) :
    ContDiffOn ℝ (⊤ : ℕ∞)
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1} ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        0 ≤ parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ∧
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p ≤
          (T - p.1) * ⨆ q, g q) ∧
      (∀ p ∈ {p : TimeVelocity d | p.1 < T ∧ p.2 ∈ movingDomain Ω γ p.1},
        scalarParabolicOperator B (fun _ _ => 0)
          (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
          p = -g p) ∧
      ContinuousOn
        (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g)
        {p : TimeVelocity d | p.1 ≤ T ∧ p.2 ∈ closure (movingDomain Ω γ p.1)} ∧
      (∀ p : TimeVelocity d, p.1 = T →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p = 0) ∧
      (∀ p : TimeVelocity d, p.2 ∈ frontier (movingDomain Ω γ p.1) →
        parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g p =
          0) := by
  have hΩm := measurableSet_of_isAdmissibleEvolutionDomain hΩ
  have hγc : Continuous γ := hγ.1
  obtain ⟨hsmooth, heq⟩ : ContDiffOn ℝ (⊤ : ℕ∞) (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g) (duhamelFiber Ω γ T) ∧ ∀ p ∈ duhamelFiber Ω γ T, scalarParabolicOperator B (fun _ _ => 0) (parabolicDuhamelPotential K (measurableSet_of_isAdmissibleEvolutionDomain hΩ) T g) p = -g p := by
    let hΩa := hΩ
    have hΩ := measurableSet_of_isAdmissibleEvolutionDomain hΩa
    set W := parabolicDuhamelPotential K hΩ T g with hW
    obtain ⟨hsm, hsymm, hell⟩ := SectionTwo.sectionTwoCoefficient_fullBounds lam Lam B hB
    have hlam := hB.1
    have hb : IsSmoothDrift (SectionTwo.identityDrift d) := SectionTwo.identityDrift_smooth d
    have hcoerc := (SectionTwo.identityDrift_bounds d).2
    set Qp := evolutionToTimeVelocity d with hQp
    have hU₀ : IsOpen (duhamelFiber Ω γ T) :=
      isOpen_duhamelFiber (isOpen_of_isAdmissibleEvolutionDomain hΩa) hγc T
    have hU : IsOpen (Qp ⁻¹' duhamelFiber Ω γ T) := hU₀.preimage Qp.continuous
    have hWc :=
      (continuousOn_duhamelPotential K hΩa hγc hP g hg0 hgs hgc T hgU).mono
        (duhamelFiber_subset_closedFiber T)
    have hWQ :=
      hWc.comp Qp.continuous.continuousOn (fun x hx => hx)

    have hweak : IsWeakTransportedSolution (zIndependentCoefficient B) (SectionTwo.identityDrift d)
        (Qp ⁻¹' duhamelFiber Ω γ T) (fun x => W (Qp x)) (fun x => -g (Qp x)) := by
      refine ⟨hWQ.locallyIntegrableOn hU.measurableSet, fun ψ hψ hc hs => ?_⟩
      have hfull := duhamel_weak_identity K hΩa hγc hP hsm hb g hg0 hgs hgc T hgU hψ hc hs
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
        setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simp only [neg_mul, integral_neg]
        exact hfull
      · intro x hx
        have : x ∉ tsupport ψ := fun h => hx (hs h)
        rw [image_eq_zero_of_notMem_tsupport this, mul_zero]
      · intro x hx
        have : x ∉ tsupport ψ := fun h => hx (hs h)
        rw [transportedAdjoint_eq_zero_of_notMem_tsupport ψ this, mul_zero]
    have hg' : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => -g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) :=
      ((hgs.comp Qp.contDiff).neg).contDiffOn
    obtain ⟨f, hf, hae⟩ := exists_smooth_representative_transported_source hH hlam hsm hell hb
      one_pos hcoerc hU hweak hg'
    have heq :=
      Measure.eqOn_open_of_ae_eq hae hU hWQ hf.continuousOn

    have hι : ∀ p : TimeVelocity d, Qp (packPoint p.1 p.2 (0 : PDE.Vec d)) = p := fun p => by
      simp [hQp]
    have hmaps : MapsTo (fun p : TimeVelocity d => packPoint p.1 p.2 (0 : PDE.Vec d))
        (duhamelFiber Ω γ T) (Qp ⁻¹' duhamelFiber Ω γ T) := fun p hp => by
      simpa only [mem_preimage, hι] using hp
    have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) W (duhamelFiber Ω γ T) := by
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ fun p : TimeVelocity d =>
          packPoint p.1 p.2 (0 : PDE.Vec d)) (duhamelFiber Ω γ T) :=
        hf.comp contDiff_zeroLift.contDiffOn hmaps
      refine h1.congr fun p hp => ?_
      have := heq (hmaps hp)
      simpa only [hι, Function.comp_apply] using this
    refine ⟨hsmooth, ?_⟩

    have hBc : ∀ i j, Continuous (fun p : TimeVelocity d => B p.1 p.2 i j) := fun i j =>
      (hsm i j).continuous.comp (continuous_fst.prodMk (continuous_snd.prodMk
        (continuous_const : Continuous fun _ : TimeVelocity d => (0 : PDE.Vec d))))
    have hopc := continuousOn_scalarParabolicOperator_of_contDiffOn hBc hU₀ hsmooth
    have hopQ : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x))
        (Qp ⁻¹' duhamelFiber Ω γ T) := hopc.comp Qp.continuous.continuousOn (fun x hx => hx)
    have hgQ : Continuous (fun x => g (Qp x)) := hgs.continuous.comp Qp.continuous
    have hzero : ∀ x ∈ Qp ⁻¹' duhamelFiber Ω γ T,
        scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x) = 0 := by
      have hcont : ContinuousOn (fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) +
          g (Qp x)) (Qp ⁻¹' duhamelFiber Ω γ T) := hopQ.add hgQ.continuousOn
      have hae0 := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
        (hcont.locallyIntegrableOn hU.measurableSet) (fun ψ hψ hc hs => by
          have h1 := integral_transportedAdjoint_zIndep hsm hb hU₀ hsmooth hψ hc hs
          have h2 := hweak.2 ψ hψ hc hs
          have iA := integrable_evolution_mul_test hopQ hψ.continuous hc hs
          have iG := integrable_evolution_mul_test hgQ.continuousOn hψ.continuous hc hs
          have hAeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T,
              scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x) =
              ∫ x, scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x :=
            setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
              rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero]
          have hGeq : (∫ x in Qp ⁻¹' duhamelFiber Ω γ T, -g (Qp x) * ψ x) =
              -∫ x, g (Qp x) * ψ x := by
            rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
              rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)), mul_zero])]
            simp only [neg_mul, integral_neg]
          rw [hAeq] at h1
          have h3 : (∫ x, scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x) +
              ∫ x, g (Qp x) * ψ x = 0 := by
            have := h1.symm.trans h2
            rw [hGeq] at this
            linarith
          have : (fun x => ψ x • (scalarParabolicOperator B (fun _ _ => 0) W (Qp x) + g (Qp x))) =
              fun x => scalarParabolicOperator B (fun _ _ => 0) W (Qp x) * ψ x + g (Qp x) * ψ x := by
            funext x; simp only [smul_eq_mul]; ring
          rw [this, integral_add iA iG, h3])
      have hae1 :=
        (ae_restrict_iff' hU.measurableSet).2 hae0
      exact Measure.eqOn_open_of_ae_eq hae1 hU hcont continuousOn_const
    intro p hp
    have := hzero (packPoint p.1 p.2 (0 : PDE.Vec d)) (hmaps hp)
    rw [hι] at this
    linarith
  have hg : ∀ r, Measurable (fun v : PDE.Vec d => g (r, v)) := fun r =>
    hgs.continuous.measurable.comp (measurable_const.prodMk measurable_id)
  obtain ⟨C, hC⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hbdd : BddAbove (range g) := ⟨C, by
    rintro _ ⟨p, rfl⟩
    exact (le_abs_self _).trans (by simpa using hC p)⟩
  have hgb : ∀ p, g p ≤ ⨆ q, g q := fun p => le_ciSup hbdd p
  refine ⟨hsmooth, fun p hp => ⟨parabolicDuhamelPotential_nonneg K hΩm T g hg hg0 p,
    parabolicDuhamelPotential_le K hΩm T g hg hg0 _ hgb p hp.1.le⟩, heq,
    continuousOn_duhamelPotential K hΩ hγc hP g hg0 hgs hgc T hgU,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_terminal_le K hΩm T g p hp.ge,
    fun p hp => parabolicDuhamelPotential_eq_zero_of_not_mem K hΩm T g p ?_⟩
  rw [(isOpen_movingDomain_of_isAdmissibleEvolutionDomain γ hΩ p.1).frontier_eq] at hp
  exact hp.2

end HypoellipticAleksandrov.KineticAleksandrov.Occupation
