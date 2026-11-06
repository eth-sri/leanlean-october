/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Foundations
public import DOZZ.Statements.Brownian.BrownianPath
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Process.FiniteDimensionalLaws
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
/-!
# Brownian restart at bounded raw stopping times

Countable stopping fibers reduce future increment tests to deterministic weak Markov
independence. Dyadic ceilings and dominated convergence preserve finite joint laws;
projective uniqueness gives the entire future process law and stopped-past independence.
The construction stays on the original sample space and identifies the actual continuous
path law on the `BrownianPath` carrier.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
section
variable {Ω : Type*}
section
variable [mΩ : MeasurableSpace Ω]

/-- The stopped sigma algebra localizes each event to every finite stopping-time fiber. -/
theorem brownian_stopped_event_fiber (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] (A ∩ {ω | τ ω = s}) := by
  simpa only [WithTop.coe_eq_coe] using ((hτ.measurableSet_inter_eq_iff A s).mp (hA.inter (hτ.measurableSet_eq' s)))

/-- A jointly measurable scalar process can be evaluated at any measurable random time. -/
theorem measurable_brownian_random_increment (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (τ : Ω → ℝ≥0) (hτm : Measurable τ) (t : ℝ≥0) :
    Measurable (fun ω => B (τ ω+t) ω-B (τ ω) ω) := by fun_prop

/-- Every finite raw stopping time is a measurable real-time random variable. -/
theorem measurable_finite_brownian_stoppingTime (𝓕 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) : Measurable τ := by
  apply measurable_of_Iic
  intro s
  simpa only [Set.preimage,mem_Iic,WithTop.coe_le_coe] using (𝓕.le s _ (hτ.measurableSet_le s))

end
section
variable (τ : Ω → ℝ≥0) (n : ℕ)

/-- Every dyadic ceiling lies above the original finite time. -/
theorem brownianDyadicCeiling_ge (ω : Ω) :
    τ ω ≤ brownianDyadicCeiling τ n ω := by
  apply (le_div_iff₀ (show 0 < brownianDyadicMesh n from pow_pos (by norm_num) n)).mpr
  bound

/-- The dyadic ceilings have a countable range as finite nonnegative times. -/
theorem brownianDyadicCeiling_countable_range :
    (range (brownianDyadicCeiling τ n)).Countable := by
  apply Set.Countable.mono ?_ (Set.countable_range fun k : ℕ => (k : ℝ≥0)/brownianDyadicMesh n)
  rintro s ⟨ω,rfl⟩
  aesop

end
section
variable [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
section
variable (hB : IsPreBrownianReal B P)
include hB

/-- Deterministic Brownian restart preserves the full evaluation-generated process law. -/
theorem brownian_shift_process_map_eq (hm : ∀ t, Measurable (B t)) (s : ℝ≥0) :
    P.map (fun ω t => B (s+t) ω-B s ω) = P.map (fun ω t => B t ω) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (map_eq_iff_forall_finset_map_restrict_eq
    ((Measurable.of_eval (fun t => (hm _).sub (hm s))).aemeasurable)
    ((Measurable.of_eval hm).aemeasurable)).mpr
  intro I
  exact ((hB.shift s).hasLaw I).map_eq.trans (hB.hasLaw I).map_eq.symm

/-- Every finite future increment test integrates independently of the raw deterministic past. -/
theorem brownian_finite_increment_setIntegral (hm : ∀ s, Measurable (B s)) (s : ℝ≥0) {I : Type*} [Fintype I] (times : I → ℝ≥0)
    (A : Set Ω) (hA : MeasurableSet[brownianRawFiltration B hm s] A)
    (F : (I → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω in A, F (fun i => B (s+times i) ω-B s ω) ∂P) =
      P.real A*(∫ ω, F (fun i => B (times i) ω) ∂P) := by
  let G : (ℝ≥0 → ℝ) → ℝ := fun f => F (fun i => f (times i))
  have hG : Measurable G := by fun_prop
  have hind := (IndepFun_iff_Indep _ _ P).mp (hB.indepFun_shift s).symm
  rw [brownianHistorySigma_eq B s] at hind
  have hh := hind.setIntegral_eq_mul (brownianRawFiltration B hm |>.le s)
    ((Measurable.of_eval (fun t => (hm _).sub (hm s))).aemeasurable) hA hG.aestronglyMeasurable
  rw [hh]
  congr 1
  calc
    _ = ∫ f, G f ∂P.map (fun ω t => B _ ω-B s ω) := by
      simpa using (integral_map
        ((Measurable.of_eval (fun t => (hm _).sub (hm s))).aemeasurable) hG.aestronglyMeasurable).symm
    _ = ∫ f, G f ∂P.map (fun ω t => B t ω) := by rw [brownian_shift_process_map_eq hB hm s]
    _ = _ := integral_map ((Measurable.of_eval hm).aemeasurable) hG.aestronglyMeasurable

end

end
section
variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
/-- Countable-range restart retains every finite joint increment law on each stopped-past event. -/
theorem brownian_countable_stopped_finite_setIntegral (hB : IsPreBrownianReal B P)
    (hm : ∀ s, Measurable (B s)) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (brownianRawFiltration B hm) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hc : (range τ).Countable) (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
    {I : Type*} [Fintype I] (times : I → ℝ≥0) (F : (I → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ ω in A, F (fun i => B (τ ω+times i) ω-B (τ ω) ω) ∂P) =
      P.real A*(∫ ω, F (fun i => B (times i) ω) ∂P) := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let _ := hc.to_subtype
  let S (s : range τ) : Set Ω := A ∩ {ω | τ ω = s.1}
  have hs (s : range τ) : MeasurableSet[(brownianRawFiltration B hm) s.1] (S s) :=
    brownian_stopped_event_fiber _ τ hτ A hA s.1
  have hsm (s : range τ) : MeasurableSet (S s) := (brownianRawFiltration B hm).le s.1 _ (hs s)
  have hunion : (⋃ s : range τ, S s) = A := by
    ext ω
    simp only [mem_iUnion,S,mem_inter_iff,mem_ofPred_eq]
    simp
  have hdis : Pairwise (fun s u => Disjoint (S s) (S u)) := by
    intro s u hsu
    apply disjoint_left.mpr
    intro ω hsω huω
    exact hsu (Subtype.ext (hsω.2.symm.trans huω.2))
  let L := ∫ ω, F (fun i => B (times i) ω) ∂P
  let G : Ω → ℝ := fun ω => F (fun i => B (τ ω+times i) ω-B (τ ω) ω)
  have hGm := hF.comp (Measurable.of_eval (fun i => measurable_brownian_random_increment B hBm τ
    (measurable_finite_brownian_stoppingTime _ τ hτ) (times i)))
  have hlocal (s : range τ) : (∫ ω in S s, G ω ∂P) = ∫ _ in S s, L ∂P := by
    calc
      _ = ∫ ω in S s, F (fun i => B (s.1+times i) ω-B s.1 ω) ∂P := by
        apply setIntegral_congr_fun (hsm s)
        intro ω hω
        dsimp only [G]
        rw [hω.2]
      _ = P.real (S s)*L := brownian_finite_increment_setIntegral hB hm s.1 times (S s) (hs s) F hF
      _ = _ := by simp
  calc
    _ = ∑' s : range τ, ∫ ω in S s, G ω ∂P := by
      rw [← hunion]
      exact integral_iUnion hsm hdis (Integrable.of_bound hGm.aestronglyMeasurable C (ae_of_all P (fun ω => hbound _))).integrableOn
    _ = ∑' s : range τ, ∫ _ in S s, L ∂P := tsum_congr hlocal
    _ = ∫ _ in A, L ∂P := by
      rw [← hunion]
      exact (integral_iUnion hsm hdis (integrable_const L).integrableOn).symm
    _ = _ := setIntegral_const L
section
variable (hB : IsBrownianReal B P) (hm : ∀ s, Measurable (B s)) (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (τ : Ω → ℝ≥0) (hτ : IsStoppingTime (brownianRawFiltration B hm) (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T)
include hB hBm hτ hτT
section
variable (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) {I : Type*} [Fintype I] (times : I → ℝ≥0)
include hA

/-- Bounded restart preserves all finite joint increment laws independently of the stopped past. -/
theorem brownian_bounded_stopped_finite_setIntegral (F : (I → ℝ) → ℝ) (hF : Continuous F) (C : ℝ) (hbound : ∀ x, ‖F x‖ ≤ C) :
    (∫ ω in A, F (fun i => B (τ ω+times i) ω-B (τ ω) ω) ∂P) =
      P.real A*(∫ ω, F (fun i => B (times i) ω) ∂P) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨hτn,_hτnT,hτnlim,_hτnrange⟩ := brownian_dyadicCeiling_properties
    (brownianRawFiltration B hm) τ hτ T hτT
  have hAn n : MeasurableSet[(hτn n).measurableSpace] A :=
    hτ.measurableSpace_mono (hτn n)
      (fun ω => WithTop.coe_le_coe.mpr (brownianDyadicCeiling_ge τ n ω)) _ hA
  have hmean n := brownian_countable_stopped_finite_setIntegral hB.toIsPreBrownianReal hm hBm
    (brownianDyadicCeiling τ n) (hτn n) (brownianDyadicCeiling_countable_range τ n) A (hAn n) times F hF.measurable C hbound
  have hgm n : Measurable (fun ω => F (fun i => B (brownianDyadicCeiling τ n ω+times i) ω-B (brownianDyadicCeiling τ n ω) ω)) :=
    hF.measurable.comp (Measurable.of_eval (fun i => measurable_brownian_random_increment B hBm _
      (measurable_finite_brownian_stoppingTime _ _ (hτn n)) (times i)))
  have ht := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (f := fun ω => F (fun i => B (τ ω+times i) ω-B (τ ω) ω))
    (fun _ => C) (fun n => (hgm n).aestronglyMeasurable) (integrable_const C)
    (fun n => ae_of_all _ (fun ω => hbound _)) ?_
  · simp_all
  · filter_upwards [ae_restrict_of_ae hB.cont] with ω hω
    exact (hF.tendsto _).comp
      (tendsto_pi_nhds.mpr (fun i =>
        ((hω.tendsto _).comp ((hτnlim ω).add_const (times i))).sub
          ((hω.tendsto (τ ω)).comp (hτnlim ω))))

/-- Bounded stopping-time restart identifies each finite future law on every stopped event. -/
theorem brownian_bounded_stopped_finite_restrict_map :
    (P.restrict A).map (fun ω i => B (τ ω+times i) ω-B (τ ω) ω) =
      P A • P.map (fun ω i => B (times i) ω) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let V : Ω → I → ℝ := fun ω i => B (τ ω+times i) ω-B (τ ω) ω
  let U : Ω → I → ℝ := fun ω i => B (times i) ω
  have hV := Measurable.of_eval (fun i => measurable_brownian_random_increment B hBm τ
    (measurable_finite_brownian_stoppingTime _ τ hτ) (times i))
  let _ := Measure.smul_finite (P.map U) (measure_ne_top P A)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map hV.aemeasurable F.continuous.measurable.aestronglyMeasurable,
    integral_smul_measure,integral_map (Measurable.of_eval (fun i => hm (times i))).aemeasurable F.continuous.measurable.aestronglyMeasurable]
  exact brownian_bounded_stopped_finite_setIntegral hB hm hBm τ hτ T hτT A hA times
    F F.continuous ‖F‖ F.norm_coe_le_norm

end

/-- The entire evaluation-generated restarted process has the original Brownian law on every bounded stopped event. -/
theorem brownian_bounded_stopped_process_restrict_map (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω t => B (τ ω+t) ω-B (τ ω) ω) =
      P A • P.map (fun ω t => B t ω) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hV :=
    Measurable.of_eval (fun t => measurable_brownian_random_increment B hBm τ
      (measurable_finite_brownian_stoppingTime _ τ hτ) t)
  let K (I : Finset ℝ≥0) : Measure (I → ℝ) := P A • P.map (fun ω (i : I) => B i ω)
  have hK I : IsFiniteMeasure (K I) := Measure.smul_finite _ (measure_ne_top P A)
  let _ := hK
  apply IsProjectiveLimit.unique (P := K)
  · intro I
    rw [Measure.map_map (Finset.measurable_restrict I) hV]
    exact brownian_bounded_stopped_finite_restrict_map hB hm hBm τ hτ T hτT A hA
      (fun i : I => i.1)
  · intro I
    rw [Measure.map_smul (P A) (Finset.measurable_restrict I).aemeasurable,Measure.map_map (Finset.measurable_restrict I) (Measurable.of_eval hm)]
    rfl

/-- Bounded restart gives the actual original law of the whole future increment process. -/
theorem brownian_bounded_stopped_process_map_eq :
    P.map (fun ω t => B (τ ω+t) ω-B (τ ω) ω) = P.map (fun ω t => B t ω) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  simpa using
    brownian_bounded_stopped_process_restrict_map hB hm hBm τ hτ T hτT univ MeasurableSet.univ

/-- The raw stopped sigma algebra is independent of the entire future process after bounded restart. -/
theorem brownian_bounded_stopped_process_indep :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (fun ω t => B (τ ω+t) ω-B (τ ω) ω) MeasurableSpace.pi) P := by
  let V : Ω → ℝ≥0 → ℝ := fun ω t => B (τ ω+t) ω-B (τ ω) ω
  have hV := Measurable.of_eval (fun t => measurable_brownian_random_increment B hBm τ
    (measurable_finite_brownian_stoppingTime _ τ hτ) t)
  apply (Indep_iff _ _ P).mpr
  intro A E hA hE
  obtain ⟨S,hS,rfl⟩ := hE
  have hlaw := brownian_bounded_stopped_process_restrict_map hB hm hBm τ hτ T hτT A hA
  have he := congrArg (fun μ => μ S) hlaw
  rw [Measure.map_apply hV hS,Measure.restrict_apply (hS.preimage hV),Measure.smul_apply, inter_comm] at he
  change P _ = P A*P _
  rwa [← Measure.map_apply hV hS,brownian_bounded_stopped_process_map_eq hB hm hBm τ hτ T hτT]

end

end

end

/-- The continuous-path sigma algebra is the pullback of the evaluation-generated process sigma algebra. -/
theorem brownianPath_measurableSpace_eq_comap :
    (inferInstance : MeasurableSpace BrownianPath) =
      MeasurableSpace.comap (fun p : BrownianPath => fun t => p t) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval,MeasurableSpace.comap_process_pi]

/-- Equality of process laws determines equality of the actual continuous-path laws. -/
theorem brownianPath_measure_eq_of_process_map_eq (P Q : Measure BrownianPath)
    (h : P.map (fun p t => p t) = Q.map (fun p t => p t)) : P = Q := by
  have hm : Measurable (fun p : BrownianPath => fun t => p t) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  apply Measure.ext
  intro S hS
  have hS' := brownianPath_measurableSpace_eq_comap.le S hS
  obtain ⟨A,hA,rfl⟩ := hS'
  rw [← Measure.map_apply hm hA,← Measure.map_apply hm hA,h]

/-- The literal future increment path on the continuous-path carrier. -/
noncomputable def brownianShiftPath (s : ℝ≥0) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p (s+t)-p s,(p.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩

/-- Joint shift evaluation is continuous, including variation of the initial path. -/
theorem continuous_brownianShiftPath : Continuous (fun z : ℝ≥0 × BrownianPath => brownianShiftPath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ≥0 × BrownianPath) × ℝ≥0 => z.1.2 (z.1.1+z.2)-z.1.2 z.1.1)
  fun_prop

/-- Canonical Brownian path evaluation is jointly measurable. -/
theorem measurable_brownianPath_evaluation :
    Measurable (fun z : ℝ≥0 × BrownianPath => z.2 z.1) :=
  by fun_prop

/-- Bounded dyadic restart preserves the actual law on the continuous-path carrier. -/
theorem brownianPath_bounded_restart_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun (t : ℝ≥0) (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) :
    P.map (fun p => brownianShiftPath (τ p) p) = P := by
  have hm : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp ((measurable_finite_brownian_stoppingTime _ τ hτ).prodMk measurable_id)
  apply brownianPath_measure_eq_of_process_map_eq
  rw [Measure.map_map (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)) hm]
  exact brownian_bounded_stopped_process_map_eq hB (fun t => ContinuousMap.measurable_eval t)
    measurable_brownianPath_evaluation τ hτ T hτT
end DOZZ.Proofs
