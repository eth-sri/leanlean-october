module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AnnularNormalizationGeometry
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.PairSetting
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDisintegrationHomogeneity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureFubini
public import Mathlib.MeasureTheory.Integral.CompactlySupported
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.RatioNormalizationMeasure
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported

/-- The source's closed unit annulus on the punctured carrier. -/
def bellmanUnitAnnulus : Set BellmanPuncturedPlane :=
  {q | 1 ≤ bellmanGauge q.val ∧ bellmanGauge q.val ≤ 2}

/-- A dyadic annulus is the literal dilation image of the unit annulus. -/
def bellmanDyadicAnnulus (j : ℤ) : Set BellmanPuncturedPlane :=
  bellmanDilation (2 ^ j) (zpow_pos (by norm_num) j) '' bellmanUnitAnnulus

/-- Closed positive-radius shells are compact on the punctured carrier. -/
theorem bellman_shell_punctured_isCompact (a b : ℝ) (ha : 0 < a) :
    IsCompact {q : BellmanPuncturedPlane | a ≤ bellmanGauge q.val ∧
      bellmanGauge q.val ≤ b} := by
  apply Topology.IsInducing.subtypeVal.isCompact_preimage'
    (bellmanGauge_shell_isCompact a b)
  intro q hq
  refine ⟨⟨q, ?_⟩, rfl⟩
  intro he
  have hn := hq.1
  rw [he] at hn
  norm_num [bellmanGauge, bellmanGaugePower] at hn
  linarith only [hn, ha]

/-- The closed unit annulus is compact. -/
theorem bellmanUnitAnnulus_isCompact : IsCompact bellmanUnitAnnulus :=
  bellman_shell_punctured_isCompact 1 2 (by norm_num)

/-- Membership in a dyadic annulus is the corresponding gauge interval. -/
theorem mem_bellmanDyadicAnnulus_iff (j : ℤ) (q : BellmanPuncturedPlane) :
    q ∈ bellmanDyadicAnnulus j ↔
      2 ^ j ≤ bellmanGauge q.val ∧ bellmanGauge q.val ≤ 2 * 2 ^ j := by
  let r : ℝ := 2 ^ j
  have hr : 0 < r := zpow_pos (by norm_num) _
  constructor
  · rintro ⟨p, hp, rfl⟩
    change r ≤ bellmanGauge (bellmanPlaneDilation r p.val) ∧
      bellmanGauge (bellmanPlaneDilation r p.val) ≤ 2 * r
    rw [bellmanGauge_dilation r hr]
    exact ⟨by nlinarith only [hp.1, hr], by nlinarith only [hp.2, hr]⟩
  · intro hq
    let T := bellmanDilationHomeomorph r hr
    refine ⟨T.symm q, ?_, T.apply_symm_apply q⟩
    have he : bellmanGauge q.val = r * bellmanGauge (T.symm q).val := by
      have h := bellmanGauge_dilation r hr (T.symm q).val
      change bellmanGauge (T (T.symm q)).val = _ at h
      rwa [T.apply_symm_apply] at h
    constructor <;> nlinarith only [hq.1, hq.2, he, hr]

/-- Every punctured point belongs to some dyadic annulus. -/
theorem bellmanDyadicAnnulus_iUnion : (⋃ j : ℤ, bellmanDyadicAnnulus j) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (bellmanGauge_pos q.val q.property)
    (by norm_num : (1 : ℝ) < 2)
  apply mem_iUnion.mpr
  refine ⟨j, (mem_bellmanDyadicAnnulus_iff j q).mpr ⟨hj.1, ?_⟩⟩
  simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hj.2.le



/-- Adjacent dyadic radii differ by exactly two. -/
theorem bellman_dyadic_succ (j : ℤ) : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm]

/-- Open thick dyadic annuli supply the finite compact-cover argument. -/
def bellmanOpenDyadicAnnulus (j : ℤ) : Set BellmanPuncturedPlane :=
  {q | 2 ^ j < bellmanGauge q.val ∧ bellmanGauge q.val < 4 * 2 ^ j}

/-- Every open thick annulus is open in the punctured topology. -/
theorem bellmanOpenDyadicAnnulus_isOpen (j : ℤ) : IsOpen (bellmanOpenDyadicAnnulus j) :=
  (isOpen_lt continuous_const (bellmanGauge_continuous.comp continuous_subtype_val)).inter
    (isOpen_lt (bellmanGauge_continuous.comp continuous_subtype_val) continuous_const)

/-- Thick dyadic annuli cover the punctured plane by open sets. -/
theorem bellmanOpenDyadicAnnulus_iUnion :
    (⋃ j : ℤ, bellmanOpenDyadicAnnulus j) = univ := by
  apply eq_univ_of_forall
  intro q
  obtain ⟨j, hj⟩ := exists_mem_Ico_zpow (bellmanGauge_pos q.val q.property)
    (by norm_num : (1 : ℝ) < 2)
  have he : (2 : ℝ) ^ j = 2 * 2 ^ (j - 1) := by
    convert bellman_dyadic_succ (j - 1) using 1
    congr 1
    omega
  have hr : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
  refine mem_iUnion.mpr ⟨j - 1, ?_⟩
  rw [bellman_dyadic_succ] at hj
  constructor <;> nlinarith only [he, hr, hj.1, hj.2]

/-- Each thick annulus is covered by two adjacent closed source annuli. -/
theorem bellmanOpenDyadicAnnulus_subset (j : ℤ) :
    bellmanOpenDyadicAnnulus j ⊆ bellmanDyadicAnnulus j ∪ bellmanDyadicAnnulus (j + 1) := by
  intro q hq
  rcases le_or_gt (bellmanGauge q.val) (2 * 2 ^ j) with h | h
  · exact Or.inl ((mem_bellmanDyadicAnnulus_iff j q).mpr ⟨hq.1.le, h⟩)
  · apply Or.inr
    apply (mem_bellmanDyadicAnnulus_iff (j + 1) q).mpr
    rw [bellman_dyadic_succ]
    exact ⟨h.le, by linarith only [hq.2]⟩

/-- Fixed positive dilation factors are uniformly bounded over a bounded degree interval. -/
theorem bellman_degree_factor_bounded (r : ℝ) (hr : 0 < r) (a b : ℝ) :
    ∃ C : ℝ≥0, ∀ beta ∈ Icc a b, ENNReal.ofReal (r ^ (4 - beta)) ≤ C := by
  have hc : Continuous (fun beta : ℝ => r ^ (4 - beta)) :=
    (Real.continuous_const_rpow hr.ne').comp (continuous_const.sub continuous_id)
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hc.continuousOn
  refine ⟨⟨max 0 M, le_max_left _ _⟩, ?_⟩
  intro beta hbeta
  have hb : r ^ (4 - beta) ≤ max 0 M :=
    (hM (mem_image_of_mem _ hbeta)).trans (le_max_right _ _)
  exact (ENNReal.ofReal_le_ofReal hb).trans_eq (ENNReal.ofReal_eq_coe_nnreal (le_max_left 0 M))



/-- A compact ambient cutoff away from the origin remains compact on the punctured carrier. -/
theorem bellman_annular_test_compact (chi : (ℝ × ℝ) → ℝ) (hc : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4}) :
    HasCompactSupport (fun q : BellmanPuncturedPlane => chi q.val) := by
  apply bellman_test_compact_subtype hc
  intro q hq he
  have h := (hs hq).1
  rw [he] at h
  norm_num [bellmanGauge, bellmanGaugePower] at h

/-- The common cutoff has a finite strictly positive normalizing integral. -/
theorem bellman_annular_integral_pos (beta : ℝ) (mu : Measure BellmanPuncturedPlane)
    (hmu : IsBellmanRadon mu) (hn : mu ≠ 0) (hd : HasBellmanDensityDegree beta mu)
    (chi : (ℝ × ℝ) → ℝ) (hc : Continuous chi) (hcompact : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4})
    (hpos : ∀ q, 0 ≤ chi q) (hone : ∀ q, 1 ≤ bellmanGauge q →
      bellmanGauge q ≤ 2 → chi q = 1) :
    0 < ∫ q, chi q.val ∂mu  := by
  have bellmanUnitAnnulus_measure_ne_zero (hmu : mu ≠ 0) :
      mu bellmanUnitAnnulus ≠ 0 := by
    intro hzero
    have hj : ∀ j : ℤ, mu (bellmanDyadicAnnulus j) = 0 := by
      intro j
      rw [bellmanDyadicAnnulus,
        hd _ _ _ bellmanUnitAnnulus_isCompact.measurableSet, hzero, mul_zero]
    have hz : mu univ = 0 := by
      rw [← bellmanDyadicAnnulus_iUnion]
      exact measure_iUnion_null hj
    exact hmu (Measure.measure_univ_eq_zero.mp hz)
  let := hmu.1
  have hi : Integrable (fun q => chi q.val) mu :=
    (hc.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (bellman_annular_test_compact chi hcompact hs)
  apply (integral_pos_iff_support_of_nonneg
    (fun q : BellmanPuncturedPlane => hpos q.val) hi).mpr
  have hsupp : bellmanUnitAnnulus ⊆ Function.support
      (fun q : BellmanPuncturedPlane => chi q.val) := by
    intro q hq
    exact Function.mem_support.mpr (by rw [hone _ hq.1 hq.2]; norm_num)
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (bellmanUnitAnnulus_measure_ne_zero hn)) (measure_mono hsupp)

/-- Dividing by the proved positive annular mass gives integral one. -/
theorem bellman_annular_normalize (mu : Measure BellmanPuncturedPlane)
    (chi : (ℝ × ℝ) → ℝ) (hp : 0 < ∫ q, chi q.val ∂mu) :
    ∃ c : ℝ, 0 < c ∧ ∫ q, chi q.val ∂(ENNReal.ofReal c • mu) = 1 := by
  refine ⟨(∫ q, chi q.val ∂mu)⁻¹, inv_pos.mpr hp, ?_⟩
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr hp.le), smul_eq_mul,
    inv_mul_cancel₀ hp.ne']

section
open Set MeasureTheory Filter Topology

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

/-- Integration on a compact carrier is a continuous linear functional. -/
def bellmanCompactIntegral (mu : Measure X) [IsFiniteMeasure mu] : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    ({
      toFun := fun f => ∫ x, f x ∂mu
      map_add' := fun f g => integral_add
        ((BoundedContinuousFunction.mkOfCompact f).integrable mu)
        ((BoundedContinuousFunction.mkOfCompact g).integrable mu)
      map_smul' := fun c f => integral_smul c f } : C(X, ℝ) →ₗ[ℝ] ℝ)
    (mu.real univ) (fun f => by
      have hb := (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm mu
      rw [BoundedContinuousFunction.norm_mkOfCompact] at hb
      convert! hb using 1)

/-- Local mass bounds give the corresponding dual norm bounds. -/
theorem bellmanCompactIntegral_norm_le (mu : Measure X) [IsFiniteMeasure mu]
    (C : ℝ) (hC : 0 ≤ C) (hm : mu.real univ ≤ C) :
    ‖bellmanCompactIntegral mu‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  change ‖∫ x, f x ∂mu‖ ≤ C * ‖f‖
  have hb := (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm mu
  simp at hb
  convert! hb.trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _)) using 1

/-- One common subsequence for every compact-exhaustion coordinate and every measure lane. -/
theorem bellman_compact_functionals_subsequence {iota : Type*} [Countable iota]
    (Y : iota → Type*) [∀ i, TopologicalSpace (Y i)] [∀ i, CompactSpace (Y i)]
    [∀ i, SecondCountableTopology (Y i)] [∀ i, T2Space (Y i)]
    [∀ i, MeasurableSpace (Y i)]
    [∀ i, BorelSpace (Y i)] (mu : ℕ → ∀ i, Measure (Y i))
    [∀ n i, IsFiniteMeasure (mu n i)]
    (C : iota → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hm : ∀ n i, (mu n i).real univ ≤ C i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ i, ∃ ell : C(Y i, ℝ) →L[ℝ] ℝ,
        ∀ f : C(Y i, ℝ), Tendsto (fun n => ∫ x, f x ∂mu (k n) i) atTop (𝓝 (ell f)) := by
  let B (i : iota) : Set (WeakDual ℝ C(Y i, ℝ)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 (C i)
  have hb (i : iota) : IsCompact (B i) := WeakDual.isCompact_closedBall 0 (C i)
  let (i : iota) : CompactSpace (B i) := isCompact_iff_compactSpace.mp (hb i)
  let (i : iota) : TopologicalSpace.MetrizableSpace (B i) :=
    WeakDual.metrizable_of_isCompact ℝ C(Y i, ℝ) (B i) (hb i)
  let u (n : ℕ) : ∀ i, B i := fun i =>
    ⟨StrongDual.toWeakDual (bellmanCompactIntegral (mu n i)), by
      change dist (bellmanCompactIntegral (mu n i)) 0 ≤ C i
      have he : dist (bellmanCompactIntegral (mu n i)) 0 =
          ‖bellmanCompactIntegral (mu n i)‖ := by
        convert! dist_zero_right (bellmanCompactIntegral (mu n i)) using 1
      rw [he]
      exact bellmanCompactIntegral_norm_le _ _ (hC i) (hm n i)⟩
  obtain ⟨ell, k, hk, ht⟩ := CompactSpace.tendsto_subseq u
  refine ⟨k, hk, ?_⟩
  intro i
  refine ⟨WeakDual.toStrongDual (ell i).val, ?_⟩
  intro f
  have hv := continuous_subtype_val.tendsto (ell i) |>.comp ((continuous_apply i).tendsto ell |>.comp ht)
  convert! (WeakDual.eval_continuous f).tendsto (ell i).val |>.comp hv using 1

end
section
open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Restriction to a compact subtype has exactly the original compact mass. -/
theorem bellman_compact_comap_mass (K : Set X) (hK : IsCompact K) (mu : Measure X) :
    (Measure.comap (Subtype.val : K → X) mu) univ = mu K := by
  rw [(MeasurableEmbedding.subtype_coe hK.measurableSet).comap_apply]
  simp

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- A test supported in a compact set has the same integral on its compact carrier. -/
theorem bellman_compact_test_integral (K : Set X) (hK : IsCompact K)
    (mu : Measure X) (f : C_c(X, ℝ)) (hf : tsupport f ⊆ K) :
    (∫ x : K, f x.val ∂Measure.comap Subtype.val mu) = ∫ x, f x ∂mu := by
  rw [integral_subtype_comap hK.measurableSet]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))

/-- Countably many locally bounded Radon sequences have one simultaneous vague subsequence. -/
theorem bellman_radon_family_subsequence {iota : Type*} [Countable iota]
    (mu : iota → ℕ → Measure X) [∀ i n, IsFiniteMeasureOnCompacts (mu i n)]
    (hb : ∀ i, ∀ K : Set X, IsCompact K → ∃ C : ℝ≥0, ∀ n, mu i n K ≤ C) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∀ i, ∃ nu : Measure X,
      IsFiniteMeasureOnCompacts nu ∧ Measure.InnerRegular nu ∧
      ∀ f : C_c(X, ℝ), Tendsto (fun n => ∫ x, f x ∂mu i (k n)) atTop
        (𝓝 (∫ x, f x ∂nu))  := by
  have bellman_riesz_of_test_limits (mu : ℕ → Measure X) [∀ n, IsFiniteMeasureOnCompacts (mu n)] (ht : ∀ f : C_c(X, ℝ), ∃ a : ℝ,
      Tendsto (fun n => ∫ x, f x ∂mu n) atTop (𝓝 a)) :
      ∃ nu : Measure X, IsFiniteMeasureOnCompacts nu ∧ Measure.InnerRegular nu ∧
      ∀ f : C_c(X, ℝ),
        Tendsto (fun n => ∫ x, f x ∂mu n) atTop (𝓝 (∫ x, f x ∂nu)) := by
    choose L hL using ht
    have hi (n : ℕ) (f : C_c(X, ℝ)) : Integrable f (mu n) :=
      f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
    let ell : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
      { toFun := L
        map_add' := fun f g => by
          apply tendsto_nhds_unique (hL (f + g))
          convert! (hL f).add (hL g) using 1
          ext n
          exact integral_add (hi n f) (hi n g)
        map_smul' := fun c f => by
          apply tendsto_nhds_unique (hL (c • f))
          convert! (hL f).const_smul c using 1
          ext n
          exact integral_smul c f
        monotone' := fun f g hfg =>
          le_of_tendsto_of_tendsto' (hL f) (hL g) (fun n => integral_mono (hi n f) (hi n g) hfg) }
    refine ⟨(RealRMK.rieszMeasure ell), inferInstance, ?_, ?_⟩
    · infer_instance
    · intro f
      rw [RealRMK.integral_rieszMeasure ell f]
      exact hL f
  let K := CompactExhaustion.choice X
  let Y (w : iota × ℕ) := {x : X // x ∈ K w.2}
  let (w : iota × ℕ) : CompactSpace (Y w) :=
    isCompact_iff_compactSpace.mp (K.isCompact w.2)
  let m (n : ℕ) (w : iota × ℕ) : Measure (Y w) := Measure.comap Subtype.val (mu w.1 n)
  have hm (n : ℕ) (w : iota × ℕ) : m n w univ = mu w.1 n (K w.2) :=
    bellman_compact_comap_mass _ (K.isCompact _) _
  let (n : ℕ) (w : iota × ℕ) : IsFiniteMeasure (m n w) :=
    ⟨by rw [hm]; exact (K.isCompact w.2).measure_lt_top⟩
  have hbound (w : iota × ℕ) := hb w.1 (K w.2) (K.isCompact w.2)
  choose C hC using hbound
  have hmreal (n : ℕ) (w : iota × ℕ) : (m n w).real univ ≤ (C w : ℝ) := by
    rw [measureReal_def, hm]
    simpa using (ENNReal.toReal_mono (by simp : (C w : ℝ≥0∞) ≠ ∞) (hC w n))
  obtain ⟨k, hk, ht⟩ := bellman_compact_functionals_subsequence Y m
    (fun w => (C w : ℝ)) (fun w => (C w).property) hmreal
  refine ⟨k, hk, ?_⟩
  intro i
  apply bellman_riesz_of_test_limits (fun n => mu i (k n))
  intro f
  obtain ⟨j, hj⟩ := K.exists_superset_of_isCompact f.hasCompactSupport
  obtain ⟨ell, hell⟩ := ht (i, j)
  let fc : C(Y (i, j), ℝ) := ⟨fun x => f x.val, f.continuous.comp continuous_subtype_val⟩
  refine ⟨ell fc, ?_⟩
  have he (n : ℕ) : (∫ x, fc x ∂m (k n) (i, j)) = ∫ x, f x ∂mu i (k n) :=
    bellman_compact_test_integral _ (K.isCompact j) _ f hj
  simpa only [he] using hell fc

end

/-- Vague convergence tests every continuous function of compact support on the actual carrier. -/
def IsBellmanVagueLimit (mu : ℕ → Measure BellmanPuncturedPlane)
    (nu : Measure BellmanPuncturedPlane) : Prop :=
  ∀ f : BellmanPuncturedPlane → ℝ, Continuous f → HasCompactSupport f →
    Tendsto (fun n => ∫ q, f q ∂mu n) atTop (𝓝 (∫ q, f q ∂nu))

/-- Uniform bounds on each compact give one common Radon subsequence for two measure lanes. -/
theorem bellman_radon_pair_subsequence (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (hm : ∀ n, IsBellmanRadon (mu n)) (he : ∀ n, IsBellmanRadon (eta n))
    (hb : ∀ K : Set BellmanPuncturedPlane, IsCompact K → ∃ C : ℝ≥0,
      ∀ n, mu n K ≤ C ∧ eta n K ≤ C) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ muinf etainf : Measure BellmanPuncturedPlane,
      IsBellmanRadon muinf ∧ IsBellmanRadon etainf ∧
      IsBellmanVagueLimit (fun n => mu (k n)) muinf ∧
      IsBellmanVagueLimit (fun n => eta (k n)) etainf := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  let m (b : Bool) (n : ℕ) : Measure BellmanPuncturedPlane := if b then eta n else mu n
  let (b : Bool) (n : ℕ) : IsFiniteMeasureOnCompacts (m b n) := by
    cases b
    · exact (hm n).1
    · exact (he n).1
  have hbound (b : Bool) (K : Set BellmanPuncturedPlane) (hK : IsCompact K) :
      ∃ C : ℝ≥0, ∀ n, m b n K ≤ C := by
    obtain ⟨C, hC⟩ := hb K hK
    refine ⟨C, ?_⟩
    intro n
    cases b
    · exact (hC n).1
    · exact (hC n).2
  obtain ⟨k, hk, ht⟩ := bellman_radon_family_subsequence m hbound
  obtain ⟨muinf, hmf, hmr, hmt⟩ := ht false
  obtain ⟨etainf, hef, her, het⟩ := ht true
  refine ⟨k, hk, muinf, etainf, ⟨hmf, hmr⟩, ⟨hef, her⟩, ?_, ?_⟩
  · intro f hf hfc
    exact hmt (⟨⟨f, hf⟩, hfc⟩ : C_c(BellmanPuncturedPlane, ℝ))
  · intro f hf hfc
    exact het (⟨⟨f, hf⟩, hfc⟩ : C_c(BellmanPuncturedPlane, ℝ))

/-- Bounded-degree homogeneous pairs have annular normalization and a simultaneous Radon limit. -/
theorem homogeneous_pairs_subsequence (R : ℝ) (hR : 1 ≤ R)
    (beta : ℕ → ℝ) (mu eta : ℕ → Measure BellmanPuncturedPlane)
    (hp : ∀ n, IsBellmanAdjointPair 1 R (beta n) (mu n) (eta n))
    (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b) :
    ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ muinf etainf : Measure BellmanPuncturedPlane,
          IsBellmanRadon muinf ∧ IsBellmanRadon etainf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • mu (k n)) muinf ∧
          IsBellmanVagueLimit (fun n => ENNReal.ofReal (c (k n)) • eta (k n)) etainf  := by
  have bellman_pairs_annular_normalization (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b) :
      ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
      tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
      (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
      (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
      (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) ∧
      ∃ c : ℕ → ℝ, (∀ n, 0 < c n) ∧
        (∀ n, ∫ q, chi q.val ∂(ENNReal.ofReal (c n) • mu n) = 1) ∧
        ∀ K : Set BellmanPuncturedPlane, IsCompact K → ∃ C : ℝ≥0,
          ∀ n, (ENNReal.ofReal (c n) • mu n) K ≤ C ∧
            (ENNReal.ofReal (c n) • eta n) K ≤ C := by
    have exists_bellman_annular_cutoff :
        ∃ chi : (ℝ × ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) chi ∧ HasCompactSupport chi ∧
        tsupport chi ⊆ {q | 1 / 2 < bellmanGauge q ∧ bellmanGauge q < 4} ∧
        (∀ q, 0 ≤ chi q ∧ chi q ≤ 1) ∧
        (∀ q, 1 ≤ bellmanGauge q → bellmanGauge q ≤ 2 → chi q = 1) ∧
        (∃ chi0 : ℝ → ℝ, ∀ q, chi q = chi0 (bellmanGauge q)) := by
      obtain ⟨psi, hp, _hpc, hps, hpr, hp1⟩ := SectionTwo.exists_smooth_cutoff
        (C := Icc 1 64) (V := Ioo (1 / 64 : ℝ) 4096) isCompact_Icc isOpen_Ioo
        (by intro x hx; constructor <;> linarith only [hx.1, hx.2])
      let chi := psi ∘ bellmanGaugePower
      have hs : tsupport chi ⊆ bellmanGaugePower ⁻¹' tsupport psi :=
        fun _ hq => tsupport_comp_subset_preimage psi bellmanGaugePower_continuous hq
      have hb : tsupport chi ⊆ {q | bellmanGaugePower q ≤ 4096} := by
        intro q hq
        exact (hps (hs hq)).2.le
      refine ⟨chi, hp.comp bellmanGaugePower_contDiff, ((bellmanGaugePower_sublevel_isCompact 4096 (by norm_num)).of_isClosed_subset (isClosed_tsupport chi) hb), ?_,
        fun q => hpr _, ?_, ?_⟩
      · intro q hq
        have hn := hps (hs hq)
        have he := bellmanGauge_pow_six q
        constructor
        · by_contra h
          have hh := le_of_not_gt h
          have hx := pow_le_pow_left₀ (bellmanGauge_nonneg q) hh 6
          rw [he] at hx
          norm_num at hx
          linarith only [hn.1, hx]
        · exact lt_of_pow_lt_pow_left₀ 6 (by norm_num : (0 : ℝ) ≤ 4) (by
            rw [he]
            norm_num
            exact hn.2)
      · intro q hq1 hq2
        apply hp1
        have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hq1 6
        have hu := pow_le_pow_left₀ (bellmanGauge_nonneg q) hq2 6
        rw [bellmanGauge_pow_six] at hl hu
        norm_num at hl hu
        exact ⟨hl, hu⟩
      · exact ⟨fun r => psi (r ^ 6), fun q => by
          change psi (bellmanGaugePower q) = psi (bellmanGauge q ^ 6)
          rw [bellmanGauge_pow_six]⟩
    have bellman_homogeneous_compact_bound (mu : ℕ → Measure BellmanPuncturedPlane) (hd : ∀ n, HasBellmanDensityDegree (beta n) (mu n)) (hm : ∀ n, mu n bellmanUnitAnnulus ≤ 1) (hb : ∃ a b : ℝ, ∀ n, a ≤ beta n ∧ beta n ≤ b) (K : Set BellmanPuncturedPlane) (hK : IsCompact K) :
        ∃ C : ℝ≥0, ∀ n, mu n K ≤ C := by
      obtain ⟨a, b, hb⟩ := hb
      have hf (j : ℤ) := bellman_degree_factor_bounded (2 ^ j)
        (zpow_pos (by norm_num) j) a b
      choose C hC using hf
      have hclosed (n : ℕ) (j : ℤ) : mu n (bellmanDyadicAnnulus j) ≤ C j := by
        rw [bellmanDyadicAnnulus, hd n _ _ _ bellmanUnitAnnulus_isCompact.measurableSet]
        calc ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * mu n bellmanUnitAnnulus
            ≤ ENNReal.ofReal ((2 ^ j) ^ (4 - beta n)) * 1 := mul_le_mul_right (hm n) _
          _ ≤ C j := by rw [mul_one]; exact hC j _ (hb n)
      have hopen (n : ℕ) (j : ℤ) :
          mu n (bellmanOpenDyadicAnnulus j) ≤ (C j : ℝ≥0∞) + C (j + 1) :=
        (measure_mono (bellmanOpenDyadicAnnulus_subset j)).trans
          ((measure_union_le _ _).trans (add_le_add (hclosed n j) (hclosed n (j + 1))))
      obtain ⟨s, hs⟩ := hK.elim_finite_subcover bellmanOpenDyadicAnnulus
        bellmanOpenDyadicAnnulus_isOpen (by rw [bellmanOpenDyadicAnnulus_iUnion]; exact subset_univ K)
      refine ⟨∑ j ∈ s, (C j + C (j + 1)), ?_⟩
      intro n
      calc mu n K ≤ mu n (⋃ j ∈ s, bellmanOpenDyadicAnnulus j) := measure_mono hs
        _ ≤ ∑ j ∈ s, mu n (bellmanOpenDyadicAnnulus j) := measure_biUnion_finset_le _ _
        _ ≤ ∑ j ∈ s, ((C j : ℝ≥0∞) + C (j + 1)) := Finset.sum_le_sum (fun j _ => hopen n j)
        _ = _ := by simp
    obtain ⟨chi, hchi, hc, hs, hr, hone, hrad⟩ := exists_bellman_annular_cutoff
    have hpos (n : ℕ) : 0 < ∫ q, chi q.val ∂mu n :=
      bellman_annular_integral_pos _ _ (hp n).1 (hp n).left_ne_zero
        (hp n).2.2.2.2.2.2.1 chi hchi.continuous hc hs (fun q => (hr q).1) hone
    have hn (n : ℕ) := bellman_annular_normalize (mu n) chi (hpos n)
    choose c hcp hcn using hn
    let nu (n : ℕ) := ENNReal.ofReal (c n) • mu n
    have hradnu (n : ℕ) : IsBellmanRadon (nu n) :=
      (hp n).1.smul _ ENNReal.ofReal_ne_top
    let (n : ℕ) : IsFiniteMeasureOnCompacts (nu n) := (hradnu n).1
    have hdeg (n : ℕ) : HasBellmanDensityDegree (beta n) (nu n) :=
      (hp n).2.2.2.2.2.2.1.smul _
    have hunit (n : ℕ) : nu n bellmanUnitAnnulus ≤ 1 := by
      have hi : Integrable (fun q : BellmanPuncturedPlane => chi q.val) (nu n) :=
        (hchi.continuous.comp continuous_subtype_val).integrable_of_hasCompactSupport
          (bellman_annular_test_compact chi hc hs)
      have h := hi.measure_le_integral (Filter.Eventually.of_forall
        (fun q : BellmanPuncturedPlane => (hr q.val).1))
        (s := bellmanUnitAnnulus) (fun q hq => by rw [hone _ hq.1 hq.2])
      rw [hcn n, ENNReal.ofReal_one] at h
      exact h
    refine ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, ?_⟩
    intro K hK
    obtain ⟨C, hC⟩ := bellman_homogeneous_compact_bound nu hdeg hunit hb K hK
    let M : ℝ≥0 := ⟨R, zero_le_one.trans hR⟩
    refine ⟨C + M * C, ?_⟩
    intro n
    have hm : nu n K ≤ (C : ℝ≥0∞) + M * C :=
      (hC n).trans (le_add_right le_rfl)
    have he : (ENNReal.ofReal (c n) • eta n) ≤ ENNReal.ofReal R • nu n := by
      simpa only [nu, smul_smul, mul_comm] using (smul_le_smul_left (ENNReal.ofReal (c n)) (hp n).2.2.2.2.1)
    have heK := Measure.le_iff.mp he K hK.measurableSet
    rw [Measure.smul_apply, smul_eq_mul] at heK
    rw [(ENNReal.ofReal_eq_coe_nnreal (zero_le_one.trans hR))] at heK
    constructor
    · simpa only [ENNReal.coe_add, ENNReal.coe_mul] using hm
    · calc (ENNReal.ofReal (c n) • eta n) K ≤ (M : ℝ≥0∞) * nu n K := heK
        _ ≤ (M : ℝ≥0∞) * C := mul_le_mul_right (hC n) _
        _ ≤ (C : ℝ≥0∞) + M * C := le_add_left le_rfl
        _ = _ := by simp
  obtain ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, hbound⟩ :=
    bellman_pairs_annular_normalization hb
  obtain ⟨k, hk, muinf, etainf, hmf, hef, hmt, het⟩ :=
    bellman_radon_pair_subsequence (fun n => ENNReal.ofReal (c n) • mu n)
      (fun n => ENNReal.ofReal (c n) • eta n)
      (fun n => (hp n).1.smul _ ENNReal.ofReal_ne_top)
      (fun n => (hp n).2.1.smul _ ENNReal.ofReal_ne_top) hbound
  exact ⟨chi, hchi, hc, hs, hr, hone, hrad, c, hcp, hcn, k, hk,
    muinf, etainf, hmf, hef, hmt, het⟩

end HypoellipticAleksandrov.KineticAleksandrov

