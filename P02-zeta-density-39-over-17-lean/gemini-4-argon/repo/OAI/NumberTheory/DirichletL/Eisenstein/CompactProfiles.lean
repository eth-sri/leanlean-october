module
public import OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents

@[expose] public section

namespace OAI

noncomputable section

open scoped BigOperators Topology FourierTransform SchwartzMap Classical LSeries.notation ArithmeticFunction.Moebius ContDiff
open MulChar AddChar Filter Asymptotics MeasureTheory Real Finset Complex ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount EisensteinEmbedding ConcreteTraceCRT Ideal NumberField RingOfIntegers UniqueFactorizationMonoid Set

namespace CubicEisenstein

section
open scoped MatrixGroups Matrix Pointwise ENNReal

lemma cosetHeight_continuous (r : CuspCosets) : Continuous (cosetHeight r) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    have heq : cosetHeight (cosetOf M)=(fun w => hyperbolicHeight (complexMatrix M • w)) :=
      funext (cosetHeight_cosetOf M)
    change Continuous (cosetHeight (cosetOf M))
    rw [heq]
    exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action _)

lemma cuspCutoffCorrection_measurable (Y : ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cuspCutoffCorrection Y F) := by
  unfold cuspCutoffCorrection
  apply Measurable.tsum
  intro r
  apply Measurable.ite
  · exact (isOpen_lt continuous_const (cosetHeight_continuous r)).measurableSet
  · exact measurable_const.mul (hF.comp (cosetHeight_continuous r).measurable)
  · exact measurable_const

lemma cuspCutoffCorrection_norm_le (F : ℝ → ℂ) (C : ℝ) (hC : 0≤C)
    (hF : ∀v,‖F v‖≤C) (w : HyperbolicSpace) : ‖cuspCutoffCorrection 1 F w‖≤C := by
  by_cases hh : ∃r : CuspCosets,1<cosetHeight r w
  · obtain ⟨r,hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr,norm_mul,norm_inv,
      norm_cosetCharacter,inv_one,one_mul]
    exact hF _
  · have hz : cuspCutoffCorrection 1 F w=0 := by
      unfold cuspCutoffCorrection
      have hz : (fun r => cuspCutoffTerm 1 F r w)=(fun _ : CuspCosets => (0:ℂ)) := by
        funext r
        simp [cuspCutoffTerm,show ¬1<cosetHeight r w from fun h => hh ⟨r,h⟩]
      rw [hz,tsum_zero]
    rw [hz,norm_zero]
    exact hC

lemma smoothCuspSeedDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (smoothCuspSeedDefect a b s) :=
  cuspCutoffCorrection_measurable 1 _ (cuspSeedDefectProfile_continuous a b s ha hab).measurable

lemma smoothCuspSeedDefect_bounded (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    ∃C : ℝ, 0≤C ∧ ∀w,‖smoothCuspSeedDefect a b s w‖≤C := by
  obtain ⟨C,hC⟩ := (cuspSeedDefectProfile_hasCompactSupport a b s hab).exists_bound_of_continuous
    (cuspSeedDefectProfile_continuous a b s ha hab)
  refine ⟨max C 0,le_max_right _ _,fun w => ?_⟩
  exact cuspCutoffCorrection_norm_le _ _ (le_max_right _ _) (fun v => (hC v).trans (le_max_left _ _)) w

lemma kernelQuotientDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (kernelQuotientDefect a b s) :=
  measurable_from_quotient.mpr (smoothCuspSeedDefect_measurable a b s ha hab)

theorem kernelQuotientDefect_memLp (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    MemLp (kernelQuotientDefect a b s) 2 (integralQuotientVolume globalKubotaKernel) := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_bounded a b s ha hab
  apply MemLp.of_bound (kernelQuotientDefect_measurable a b s ha hab).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact hbound w

def kernelL2Defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  (kernelQuotientDefect_memLp a b s ha hab).toLp (kernelQuotientDefect a b s)

lemma kernelL2Defect_ae_eq (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelL2Defect a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientDefect a b s :=
  MemLp.coeFn_toLp _

end

open scoped MatrixGroups Pointwise ENNReal

lemma cuspCutoffCorrection_add (F G : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (F+G) w=cuspCutoffCorrection 1 F w+cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  rw [←(cuspCutoffTerm_summable 1 le_rfl F w).tsum_add (cuspCutoffTerm_summable 1 le_rfl G w)]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.add_apply]
  split_ifs <;> simp [mul_add]

lemma cuspCutoffCorrection_smul (c : ℂ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (c • F) w=c • cuspCutoffCorrection 1 F w := by
  unfold cuspCutoffCorrection
  rw [smul_eq_mul,←tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

def compactHeightProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) : ℝ → ℂ :=
  (Set.Icc a b).indicator (fun v => F (Set.projIcc a b hab v))

lemma compactHeightProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (compactHeightProfile a b hab F) :=
  (F.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc

lemma compactHeightProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) (v : ℝ) :
    ‖compactHeightProfile a b hab F v‖≤‖F‖ := by
  unfold compactHeightProfile
  by_cases hv : v∈Set.Icc a b
  · rw [Set.indicator_of_mem hv]
    exact F.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hv,norm_zero]
    exact norm_nonneg _

lemma compactHeightProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (F+G)=compactHeightProfile a b hab F+compactHeightProfile a b hab G := by
  funext v
  simp [compactHeightProfile,Set.indicator_add]

lemma compactHeightProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (c • F)=c • compactHeightProfile a b hab F := by
  funext v
  by_cases hv : v∈Set.Icc a b <;> simp [compactHeightProfile,hv]

def kernelCompactProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (cuspCutoffCorrection 1 (compactHeightProfile a b hab F)) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
    have he := cuspCutoffCorrection_automorphy 1 le_rfl (compactHeightProfile a b hab F)
      (⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩ : CubicKubota.levelThree) w
    rw [hchar,one_mul] at he
    exact he.symm)

lemma kernelCompactProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (kernelCompactProfile a b hab F) :=
  measurable_from_quotient.mpr (cuspCutoffCorrection_measurable 1 _
    (compactHeightProfile_measurable a b hab F))

lemma kernelCompactProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ))
    (q : IntegralOrbitQuotient globalKubotaKernel) : ‖kernelCompactProfile a b hab F q‖≤‖F‖ := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact cuspCutoffCorrection_norm_le _ _ (norm_nonneg F)
      (compactHeightProfile_norm_le a b hab F) w

lemma kernelCompactProfile_memLp (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    MemLp (kernelCompactProfile a b hab F) 2 (integralQuotientVolume globalKubotaKernel) :=
  MemLp.of_bound (kernelCompactProfile_measurable a b hab F).aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall (kernelCompactProfile_norm_le a b hab F))

lemma kernelCompactProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (F+G)=kernelCompactProfile a b hab F+kernelCompactProfile a b hab G := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_add,cuspCutoffCorrection_add]
    rfl

lemma kernelCompactProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (c • F)=c • kernelCompactProfile a b hab F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_smul,cuspCutoffCorrection_smul]
    rfl

def compactProfileL2Linear (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →ₗ[ℂ] KernelQuotientL2 where
  toFun F := (kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)
  map_add' F G := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_add,MemLp.coeFn_toLp,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_add]
  map_smul' c F := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_smul,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_smul]
    exact Filter.Eventually.of_forall (fun _ => rfl)

lemma compactProfileL2Linear_bound (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    ‖compactProfileL2Linear a b hab F‖≤
      (measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹)*‖F‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg F)
  filter_upwards [MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)] with q hq
  change ‖((kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)) q‖≤‖F‖
  rw [hq]
  exact kernelCompactProfile_norm_le a b hab F q

def compactProfileL2 (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →L[ℂ] KernelQuotientL2 :=
  (compactProfileL2Linear a b hab).mkContinuous
    ((measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹))
    (compactProfileL2Linear_bound a b hab)

lemma compactProfileL2_ae_eq (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    compactProfileL2 a b hab F =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCompactProfile a b hab F :=
  MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)

def compactLogProfile (a b : ℝ) (ha : 0<a) : C(Set.Icc a b,ℂ) :=
  ⟨fun v => (Real.log (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => (ha.trans_le v.2.1).ne'))⟩

def compactDefectSecond (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)^2*((deriv (deriv (cuspTransition a b)) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow 2 |>.mul
      (Complex.continuous_ofReal.comp (hdd.continuous.comp continuous_subtype_val))

def compactDefectFirst (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)*((deriv (cuspTransition a b) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp (hd.continuous.comp continuous_subtype_val))

def compactDefectProfile (a b : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a b,ℂ) :=
  NormedSpace.exp (s • compactLogProfile a b ha)*
    (compactDefectSecond a b+(2*s-1) • compactDefectFirst a b)

lemma compactDefectProfile_apply (a b : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a b) :
    compactDefectProfile a b ha s v=cuspSeedDefectProfile a b s v := by
  have hexp := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a b ha)
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v*
    (compactDefectSecond a b v+(2*s-1)*compactDefectFirst a b v)=_
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v=
    NormedSpace.exp ((s • compactLogProfile a b ha) v) at hexp
  rw [hexp,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,
    compactDefectSecond,compactDefectFirst,cuspSeedDefectProfile,positiveHeightPower,
    logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]
  ring

lemma compactDefectProfile_entire (a b : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactDefectProfile a b ha) := by
  have he := differentiable_exp_smul_const ℂ (compactLogProfile a b ha)
  exact he.mul ((differentiable_const _).add
    (((differentiable_const (2:ℂ)).mul differentiable_id |>.sub (differentiable_const 1)).smul
      (differentiable_const (compactDefectFirst a b))))

lemma compactHeightProfile_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactHeightProfile a b hab.le (compactDefectProfile a b ha s)=cuspSeedDefectProfile a b s := by
  funext v
  by_cases hv : v∈Set.Icc a b
  · rw [compactHeightProfile,Set.indicator_of_mem hv,Set.projIcc_of_mem hab.le hv,
      compactDefectProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem hv]
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    exact (cuspSeedDefectProfile_zero a b s v hab hout).symm

lemma compactProfileL2_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactProfileL2 a b hab.le (compactDefectProfile a b ha s)=kernelL2Defect a b ha hab s := by
  apply Lp.ext
  grw [compactProfileL2_ae_eq,kernelL2Defect_ae_eq]
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a b hab.le (compactDefectProfile a b ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s) w
    rw [compactHeightProfile_actual_defect a b ha hab s]

theorem kernelL2Defect_entire (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Differentiable ℂ (kernelL2Defect a b ha hab) := by
  have heq : kernelL2Defect a b ha hab=
      fun s => compactProfileL2 a b hab.le (compactDefectProfile a b ha s) :=
    funext (fun s => (compactProfileL2_actual_defect a b ha hab s).symm)
  rw [heq]
  exact (compactProfileL2 a b hab.le).differentiable.comp (compactDefectProfile_entire a b ha)

end CubicEisenstein


namespace SecondPassArithmetic

section
open FirstPassCubeLabels (primeProductNorm columnLog b0Label)
open SecondPassFiber

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

end

end
