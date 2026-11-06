module

public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureApproximation
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceHomogeneousLimit
public import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceL2Convergence
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceHomogeneousSpace
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceActionConvergence
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceFutureRegularity
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceSmoothApproximation
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.DuhamelBoundary
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceClosedGraph
import HypoellipticAleksandrov.KineticAleksandrov.Occupation.ParabolicDuhamelSmooth
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import HypoellipticAleksandrov.KineticAleksandrov.LocalA.BoundedSourceWeakMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pointwise continuity of bounded future potentials on compact collars

The starting measure is volume on the collar plus a Dirac mass at the chosen point. The
actual source approximation therefore gives both L2 convergence and that point's value.
-/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
open MeasureTheory Set Filter Evolution
open scoped Topology
open Occupation
open scoped ProbabilityTheory
variable {d : ℕ} {Ω : Set (PDE.Vec d)} {γ : ℝ → PDE.Vec d}

/- A positive bounded source supported strictly in the future gives a continuous literal
potential on every compact regular collar lying strictly before the source starts. -/
theorem continuousOn_duhamelFuture_compact_collar
    (hH : HormanderHypoellipticityStatement)
    (hΩa : IsAdmissibleEvolutionDomain Ω) (hΩ : MeasurableSet Ω) (hγ : Continuous γ)
    (B : FullKineticCoefficient d) (b : PDE.Vec d → PDE.Vec d)
    (S : TerminalOperatorFamily Ω γ) (K : MovingFiberKernel Ω γ)
    (hreal : RealizesTerminalEvolution Ω γ hΩ B b S K)
    (hB : IsSmoothFullKineticCoefficient B) (hBs : IsSymmetricFullKineticCoefficient B)
    (hb : IsSmoothDrift b) (lam Lam m : ℝ) (hlam : 0 < lam) (hm : 0 < m)
    (hell : HasEverywhereLoewnerBounds lam Lam B)
    (hcoerc : HasUnitDirectionDriftCoercivity m b)
    (a s T : ℝ) (has : a ≤ s) (hsT : s ≤ T)
    (U C ) (hU : IsOpen U) (hC : IsCompact C)
    (hCi : C ⊆ closure (interior C)) (hCU : C ⊆ U)
    [IsFiniteMeasure (volume.restrict U)]
    (hUpast : U ⊆ evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
    (hUfloor : ∀ z ∈ U, a ≤ (evolutionHomeomorph d z).time)
    (F : KineticPoint d → ℝ) (hF : Measurable F) (M : ℝ) (hM : 0 ≤ M)
    (hFb : ∀ p, 0 ≤ F p ∧ F p ≤ M)
    (hFz : ∀ p, KineticPoint.equivProd d p ∉ boundedSourceFutureSet Ω γ s T → F p = 0) :
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
  have hweak := duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb
    F hF M hM (fun p => by rw [abs_of_nonneg (hFb p).1]; exact (hFb p).2)
    s T hsT hzero
  have hw := boundedSource_ambientWeak_restrict hUpast B b u hweak
  have hbound (g : KineticPoint d → ℝ) (Cg : ℝ) (hCg : 0 ≤ Cg)
      (hgb : ∀ p, |g p| ≤ Cg) : ∀ z ∈ U,
      |duhamelPotential K T g (P z)| ≤ (T - a) * Cg := by
    intro z hz
    have hzT := (hUpast hz).1.le.trans hsT
    exact (abs_duhamelPotential_le K g Cg hCg hgb (P z) T hzT).trans
      (mul_le_mul_of_nonneg_right (sub_le_sub_left (hUfloor z hz) T) hCg)
  have hum : Measurable u := (measurable_duhamelPotential K hΩ hγ T F hF).comp P.measurable
  have hub : ∀ᵐ z ∂μ, |u z| ≤ (T - a) * (M + 2) := by
    apply ae_restrict_of_forall_mem hU.measurableSet
    intro z hz
    exact hbound F (M + 2) (by linarith) (fun p => by
      rw [abs_of_nonneg (hFb p).1]; linarith [(hFb p).2]) z hz
  have hu : MemLp u 2 μ := MemLp.of_bound hum.aestronglyMeasurable.restrict
    ((T - a) * (M + 2)) (by simpa only [Real.norm_eq_abs] using hub)
  obtain ⟨v, hvc, hve, hidentify⟩ : ∃ v : EvolutionVec d → ℝ, ContinuousOn v U ∧ u =ᵐ[volume.restrict U] v ∧
      ∀ (f : ℕ → EvolutionVec d → ℝ)
        (hf : ∀ n, MemLp (f n) 2 (volume.restrict U)),
        (∀ n, ContinuousOn (f n) U) →
        (∀ n, IsWeakTransportedSolution B b U (f n) (fun _ => 0)) →
        Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hu.toLp u)) →
        ∀ z ∈ C, Tendsto (fun n => f n z) atTop (𝓝 (u z)) → u z = v z := by
    classical
    let H := boundedSourceHomogeneousL2Space B b hB hb U
    have hclosed : IsClosed (boundedSourceHomogeneousL2Space B b hB hb U :
      Set (Lp ℝ 2 (volume.restrict U))) := by
      change IsClosed (↑(⨅ φ : BoundedSourceSmoothTest U,
        (boundedSource_testFunctional B b hB hb U φ).ker) : Set (Lp ℝ 2 (volume.restrict U)))
      rw [Submodule.coe_iInf]
      exact isClosed_iInter fun φ => (boundedSource_testFunctional B b hB hb U φ).isClosed_ker
    have hrep := boundedSourceHomogeneousL2Space_hasContinuousRepresentative hH B b hB hb
      lam Lam m hlam hm hell hcoerc U hU
    let x : H := ⟨hu.toLp u, mem_boundedSourceHomogeneousL2Space_of_isWeak B b hB hb U u hu hw⟩
    let v := continuousWeakRepresentative volume U H hrep x
    have hvc := continuousWeakRepresentative_continuous volume U H hrep x
    have hve := hu.coeFn_toLp.symm.trans
      (continuousWeakRepresentative_ae volume U H hrep x)
    refine ⟨v, hvc, hve, ?_⟩
    intro f hf hfc hfw hlim z hz hp
    let fn (n : ℕ) : H := ⟨(hf n).toLp (f n),
      mem_boundedSourceHomogeneousL2Space_of_isWeak B b hB hb U (f n) (hf n) (hfw n)⟩
    have hfn : Tendsto fn atTop (𝓝 x) := tendsto_subtype_rng.mpr hlim
    let L := compactRepresentativeMap volume U C hU hCU H hrep
    have hL := continuous_compactRepresentativeMap volume U C hU hCU hC hCi H hclosed hrep
    have hmaps := (hL.tendsto x).comp hfn
    have hpoint := (continuous_eval_const (⟨z, hz⟩ : C)).tendsto (L x) |>.comp hmaps
    have heq (n : ℕ) : L (fn n) ⟨z, hz⟩ = f n z :=
      compactRepresentativeMap_apply_eq volume U C hU hCU H hrep (fn n) (f n)
        (hfc n) (hf n).coeFn_toLp ⟨z, hz⟩
    have hvlim := hpoint.congr' (Eventually.of_forall heq)
    exact tendsto_nhds_unique hp hvlim
  have heq : EqOn u v C := by
    intro z hz
    let ν := μ.map P + Measure.dirac (P z)
    have hfloor : ∀ᵐ p ∂ν, a ≤ p.time := by
      apply ae_add_measure_iff.mpr
      refine ⟨?_, ?_⟩
      · apply (ae_map_iff P.measurable.aemeasurable
          (measurableSet_le measurable_const continuous_time.measurable)).2
        exact ae_restrict_of_forall_mem hU.measurableSet hUfloor
      · simpa only [ae_dirac_eq, eventually_pure] using hUfloor z (hCU hz)
    obtain ⟨f, hfm, hfb, hfc, hfw, hlim⟩ : ∃ f : ℕ → KineticPoint d → ℝ,
      (∀ n, Measurable (f n)) ∧ (∀ n p, 0 ≤ f n p ∧ f n p ≤ M + 2) ∧
      (∀ n, ContinuousOn (duhamelPotential K T (f n))
        (evolutionPastClosedCylinder Ω γ T)) ∧
      (∀ n, IsWeakTransportedSolution B b
        (evolutionHomeomorph d ⁻¹' evolutionPastOpenCylinder Ω γ s)
        (duhamelPotential K T (f n) ∘ evolutionHomeomorph d) (fun _ => 0)) ∧
      (∀ᵐ p ∂ν, Tendsto (fun n => duhamelPotential K T (f n) p) atTop
        (𝓝 (duhamelPotential K T F p))) := by
      classical
      let μ := boundedSourceActionMeasure K ν a T
      let G : ℝ × EvolutionAmbientState d → ℝ :=
        fun q => F ⟨q.1, q.2.1, q.2.2⟩
      have hG : Measurable G := hF.comp (KineticPoint.measurable_equivProd_symm d)
      have hU := isOpen_boundedSourceFutureSet (isOpen_of_isAdmissibleEvolutionDomain hΩa)
        hγ s T
      obtain ⟨φ, hφ, hφb, hφlim⟩ := exists_boundedSourceSmoothApproximation μ
        (boundedSourceFutureSet Ω γ s T) hU G hG M hM (fun q => hFb _) (by
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
        have hs := ((hφ n).2.2 hm).1
        exact (not_lt_of_gt hp) hs
      refine ⟨f, fun n => (hfc n).measurable, fun n p => hφb n _, ?_, ?_, ?_⟩
      · intro n
        exact continuousOn_duhamelPotential hΩa hΩ hγ B b S K hreal (f n) (hfn n)
          (hfc n) ((hφ n).2.1.comp_homeomorph (KineticPoint.homeomorphProd d))
          (hfs n) T (hfsup n)
      · intro n
        exact duhamelPotential_weak_before_source hΩa hΩ hγ B b S K hreal hB hBs hb
          (f n) (hfc n).measurable (M + 2) (by linarith) (hfb n) s T hsT (hzero n)
      ·
        have hf : ∀ n, Measurable (f n) := (fun n => (hfc n).measurable)
        let C := (M + 2)
        have hC : 0 ≤ C := by
          linarith
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
          exact ae_of_ae_map measurable_boundedSourceOutput.aemeasurable hφlim
        have hdis := Measure.ae_ae_of_ae_compProd hout
        have hvalid : ∀ᵐ q ∂η,
            Tendsto (fun n => duhamelIntegrand K (f n) q.1.1 q.1.2) atTop
              (𝓝 (duhamelIntegrand K F q.1.1 q.1.2)) := by
          filter_upwards [hdis] with q hq
          have : IsFiniteMeasure (κ q) := inferInstance
          have hi := tendsto_integral_of_dominated_convergence (fun _ => C)
            (fun n => (hf n).aestronglyMeasurable.comp_measurable
              ((KineticPoint.measurable_equivProd_symm d).comp
                (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))))
            (integrable_const C) (fun n => Eventually.of_forall fun w => by
              rw [Real.norm_eq_abs]
              exact hfb n _) hq
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
              Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        filter_upwards [(Measure.ae_ae_of_ae_prod hpairs), hfloor] with p hp hpa
        have hi := tendsto_integral_of_dominated_convergence (fun _ => C)
          (fun n => ((measurable_duhamelIntegrand K hΩ hγ (f n) (hf n)).comp
            (measurable_const.prodMk measurable_id)).aestronglyMeasurable.restrict)
          (integrable_const C) (fun n => Eventually.of_forall fun r => by
            rw [Real.norm_eq_abs]
            exact abs_duhamelIntegrand_le K (f n) C hC (hfb n) p r) hp
        have he (g : KineticPoint d → ℝ) := duhamelPotential_eq_integral_window K g p (T := T) hpa
        simpa only [Function.comp_apply, id_eq, ← he] using hi
    let fn (n : ℕ) := duhamelPotential K T (f n) ∘ P
    have hfnm (n : ℕ) : Measurable (fn n) :=
      (measurable_duhamelPotential K hΩ hγ T (f n) (hfm n)).comp P.measurable
    have hfnb (n : ℕ) : ∀ᵐ w ∂μ, |fn n w| ≤ (T - a) * (M + 2) := by
      apply ae_restrict_of_forall_mem hU.measurableSet
      exact hbound (f n) (M + 2) (by linarith) (fun p => by
        rw [abs_of_nonneg (hfb n p).1]; exact (hfb n p).2)
    have hfn (n : ℕ) : MemLp (fn n) 2 μ :=
      MemLp.of_bound (hfnm n).aestronglyMeasurable.restrict ((T - a) * (M + 2))
        (by simpa only [Real.norm_eq_abs] using hfnb n)
    have hconv := ae_add_measure_iff.mp hlim
    have hae :=
      ae_of_ae_map P.measurable.aemeasurable hconv.1
    have hp : Tendsto (fun n => fn n z) atTop (𝓝 (u z)) := by
      simpa only [ae_dirac_eq, eventually_pure, fn, u, Function.comp_def] using hconv.2
    have hstrong := tendsto_toLp_two_of_bounded_ae μ fn u hfn hu
      ((T - a) * (M + 2)) (mul_nonneg (sub_nonneg.mpr (has.trans hsT)) (by linarith))
      hfnb hub hae
    have hfnc (n : ℕ) : ContinuousOn (fn n) U :=
      (hfc n).comp P.continuous.continuousOn (fun w hw =>
        ⟨(hUpast hw).1.le.trans hsT, subset_closure (hUpast hw).2⟩)
    have hfnw (n : ℕ) := boundedSource_ambientWeak_restrict hUpast B b (fn n) (hfw n)
    exact hidentify fn hfn hfnc hfnw hstrong z hz hp
  exact (hvc.mono hCU).congr (fun z hz => heq hz)

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
