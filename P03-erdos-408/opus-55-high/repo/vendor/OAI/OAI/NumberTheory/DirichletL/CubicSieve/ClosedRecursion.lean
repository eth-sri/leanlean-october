module

public import OAI.NumberTheory.DirichletL.CubicSieve.ReopeningBounds
public import OAI.NumberTheory.DirichletL.CubicSieve.CutoffOrders

@[expose] public section

namespace OAI

noncomputable section

open MulChar AddChar
open Filter Asymptotics MeasureTheory
open scoped Topology
open Real
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open Filter
open Filter
open scoped Topology
open ConcreteTraceCRT
open Filter Asymptotics
open scoped LSeries.notation
open Filter
open scoped LSeries.notation
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical
open Set
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical

open scoped Classical
namespace SecondPassArithmetic

section
open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

end

open ConcreteTraceCRT (eisEmbedding)

open ConcreteTraceCRT (eisEmbedding)
open JointLogSeparation (frequencyTwist)

end SecondPassArithmetic

open scoped Classical
namespace CompletedGauss

theorem nonresidual_count_eq_on_fiber (I J Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    (normalizedFactors I).count P=(normalizedFactors J).count P := by
  have ha := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hA
  simp only [normalizedFactors_rowPowerfulPart,Multiset.count_filter] at ha
  have ht := congrArg (fun A : Ideal ActualEisensteinCubic.O=>(normalizedFactors A).count P) hT
  simp only [rowMaskPart,normalizedFactors_squarefreeMaskPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at ht
  have hr0 : (normalizedFactors (rowResidualPart I Q)).count P=0 := by
    apply Multiset.count_eq_zero.mpr
    intro hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp hm).2
  simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
    normalizedFactors_rowSimplePart,Multiset.count_filter] at hr0
  by_cases hpq : P∣Q
  · grind
  · have hpi : P∣I := (hP.dvd_mul.mp hpool).resolve_right hpq
    have hci :=
      Multiset.count_pos.mpr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hpi⟩)
    grind

theorem nonresidual_prime_transport (I J F Q P : Ideal ActualEisensteinCubic.O)
    (hI : I≠0) (hJ : J≠0) (hP : Prime P)
    (hA : rowPowerfulPart I=rowPowerfulPart J)
    (hT : rowMaskPart I Q=rowMaskPart J Q)
    (hpool : P∣I*Q) (hr : ¬P∣rowResidualPart I Q) :
    P∣J*Q ∧ ¬P∣rowResidualPart J Q ∧ completedLocalExponent I F P=completedLocalExponent J F P := by
  have hc := nonresidual_count_eq_on_fiber I J Q P hI hP hA hT hpool hr
  have hpoolJ : P∣J*Q := by
    rcases hP.dvd_mul.mp hpool with hi|hq
    · have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mpr ⟨hP,hi⟩
      have hcj := hc ▸ Multiset.count_pos.mpr hm
      exact dvd_mul_of_dvd_left ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hJ).mp (Multiset.count_pos.mp hcj)).2 Q
    · exact dvd_mul_of_dvd_right hq J
  have hrc : (normalizedFactors (rowResidualPart I Q)).count P=
      (normalizedFactors (rowResidualPart J Q)).count P := by
    simp only [rowResidualPart,normalizedFactors_squarefreeResidualPart,
      normalizedFactors_rowSimplePart,Multiset.count_filter,hc]
  refine ⟨hpoolJ,?_,?_⟩
  · intro hd
    have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart J) Q)).mpr ⟨hP,hd⟩
    have hp := hrc.symm ▸ Multiset.count_pos.mpr hm
    exact hr ((UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero (rowSimplePart I) Q)).mp
      (Multiset.count_pos.mp hp)).2
  · simp only [completedLocalExponent,hc]

end CompletedGauss

open Filter MeasureTheory
open scoped Classical Topology

namespace CubicEisenstein

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

omit [CompleteSpace E] in
lemma compact_estimate_prod_antilipschitz (T : E→L[ℂ]F) (K : E→L[ℂ]G) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    ∃D : NNReal,AntilipschitzWith D (T.prod K) := by
  let R := max A 0+max B 0
  have hR : 0≤R := by positivity
  refine ⟨⟨Real.sqrt R,Real.sqrt_nonneg _⟩,(T.prod K).antilipschitz_of_bound (fun u => ?_)⟩
  have hT : ‖T u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (by simp)
  have hK : ‖K u‖^2≤‖(T.prod K) u‖^2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (by simp)
  have hh : ‖u‖^2≤R*‖(T.prod K) u‖^2 := calc
    _ ≤A*‖T u‖^2+B*‖K u‖^2 := hest u
    _ ≤max A 0*‖T u‖^2+max B 0*‖K u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_right (by simp) (sq_nonneg _))
        (mul_le_mul_of_nonneg_right (by simp) (sq_nonneg _))
    _ ≤max A 0*‖(T.prod K) u‖^2+max B 0*‖(T.prod K) u‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hT (by positivity))
        (mul_le_mul_of_nonneg_left hK (by positivity))
    _ = _ := by linarith
  change ‖u‖≤Real.sqrt R*‖(T.prod K) u‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow,Real.sq_sqrt hR] using hh

lemma finiteDimensional_ker_of_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) :
    FiniteDimensional ℂ T.ker := by
  let : CompleteSpace T.ker := T.isClosed_ker.completeSpace_coe
  have hc : IsCompactOperator (K.comp T.ker.subtypeL) := hK.comp_clm T.ker.subtypeL
  have hid : IsCompactOperator (ContinuousLinearMap.id ℂ T.ker) := by
    apply compact_of_norm_le_compact _ _ hc
    refine ⟨Real.sqrt (max B 0),fun u => ?_⟩
    have ht : T (u:E)=0 := u.2
    have hh := hest (u:E)
    rw [ht,norm_zero,zero_pow (by positivity),mul_zero,zero_add] at hh
    have hh' : ‖u‖^2≤max B 0*‖K (u:E)‖^2 :=
      hh.trans (mul_le_mul_of_nonneg_right (by simp) (sq_nonneg _))
    change ‖u‖≤Real.sqrt (max B 0)*‖K (u:E)‖
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    simpa only [mul_pow,Real.sq_sqrt (le_max_right B 0)] using hh'
  exact FiniteDimensional.of_isCompactOperator_id hid

lemma antilipschitz_of_injective_compact_estimate (T : E→L[ℂ]F) (K : E→L[ℂ]G)
    (hK : IsCompactOperator K) (A B : ℝ)
    (hest : ∀u,‖u‖^2≤A*‖T u‖^2+B*‖K u‖^2) (hT : Function.Injective T) :
    ∃D : NNReal,AntilipschitzWith D T := by
  by_contra hanti
  have hex (ε : ℝ) (hε : 0<ε) : ∃u : E,‖u‖=1 ∧ ‖T u‖<ε := by
    by_contra! hn
    apply hanti
    refine ⟨⟨ε⁻¹,by positivity⟩,antilipschitz_of_bound_of_norm_one T (fun u hu => ?_)⟩
    change 1≤ε⁻¹*‖T u‖
    have hh := mul_le_mul_of_nonneg_left (hn u hu) (inv_nonneg.mpr hε.le)
    simpa only [inv_mul_cancel₀ hε.ne'] using hh
  obtain ⟨eps,hepsAnti,hepsPos,heps⟩ := exists_seq_strictAnti_tendsto (0:ℝ)
  choose u hunorm huT using fun n : ℕ => hex (eps n) (hepsPos n)
  have huTlim : Tendsto (fun n => T (u n)) atTop (𝓝 0) :=
    squeeze_zero_norm (by grind) heps
  obtain ⟨S,hS,hsub⟩ := hK.image_closedBall_subset_compact 1
  obtain ⟨k,hk,seq,hseq,hklim⟩ := hS.tendsto_subseq
    (fun n => hsub ⟨u n,by simp_all,rfl⟩)
  let P := T.prod K
  obtain ⟨D,hD⟩ := compact_estimate_prod_antilipschitz T K A B hest
  have hlim : Tendsto (fun n => P (u (seq n))) atTop (𝓝 (0,k)) :=
    (huTlim.comp hseq.tendsto_atTop).prodMk_nhds hklim
  have hmem : (0,k)∈Set.range P :=
    (hD.isClosed_range P.uniformContinuous).mem_of_tendsto hlim
      (Eventually.of_forall (by grind))
  obtain ⟨v,hv⟩ := hmem
  have hvlim : Tendsto (fun n => u (seq n)) atTop (𝓝 v) := by
    apply (hD.isInducing P.continuous).tendsto_nhds_iff.mpr
    change Tendsto (fun n => P (u (seq n))) atTop (𝓝 (P v))
    rw [hv]
    exact hlim
  have hvzero : v=0 := hT (by
    have hh := congrArg Prod.fst hv
    change T v=0 at hh
    simp_all)
  have hnorm : ‖v‖=1 := tendsto_nhds_unique hvlim.norm (by simp_all)
  simp_all

end CubicEisenstein

end

end OAI
