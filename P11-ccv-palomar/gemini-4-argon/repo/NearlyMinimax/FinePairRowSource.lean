module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import NearlyMinimax.FinePairRows
public import NearlyMinimax.CardinalCoefficientBounds
@[expose] public section
noncomputable section
open MeasureTheory Set Function
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {X J E : Type*}
theorem finePairTimeMatrix_cost_integral  [Fintype ι]
    (d ) [NeZero d] (lo hi ) (hlo : 0 ≤ lo) (horder : lo ≤ hi) (A : ι → ι → ℝ) :
    (∫ e, separatedMatrixCost (finePairTimeMatrix d A) e ∂finePairTimeFieldMeasure d lo hi) =
      (∑ i, ∑ j, |A i j|) * ((hi ^ 2 - lo ^ 2) / 2) := by
  simp_rw [finePairTimeMatrix_cost]
  have h_finePairTimeFieldMeasure_abs_time_integral : (∫ e : ℝ × FinePairFieldMark d, |e.1| ∂finePairTimeFieldMeasure d lo hi) =
      (hi ^ 2 - lo ^ 2) / 2 := by
    have h_finePairTimeFieldMeasure_fst_integral : (∫ e : ℝ × FinePairFieldMark d, e.1 ∂finePairTimeFieldMeasure d lo hi) =
      ∫ T in Icc lo hi, T := by
      rw [finePairTimeFieldMeasure_integral d lo hi _ (finePairTimeFieldMeasure_fst_integrable d lo hi)]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
        smul_eq_mul, one_mul]
    rw [integral_congr_ae (by filter_upwards [finePairTimeFieldMeasure_ae_time d lo hi] with e he; exact abs_of_nonneg (hlo.trans he.1)), h_finePairTimeFieldMeasure_fst_integral,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le horder, integral_id]
  rw [integral_mul_const, h_finePairTimeFieldMeasure_abs_time_integral, mul_comm]
theorem response_absolute_cost_ge_one (q ) (hq : 1 ≤ q) :
    1 ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := by
  calc
    1 = |∑ j : Fin (2*q+2), responseWeight q j * responseNode q j ^ 2| := by
      have h_response_second_moment : (∑ j : Fin (2 * q + 2), responseWeight q j * responseNode q j ^ 2) = 1 := by
        simpa using response_rule_moments q 2 (by omega)
      rw [h_response_second_moment]; norm_num
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j * responseNode q j ^ 2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin (2*q+2), |responseWeight q j| := by
      apply Finset.sum_le_sum
      intro j _
      have he : |responseNode q j ^ 2| = responseNode q j ^ 2 := abs_of_nonneg (sq_nonneg _)
      rw [abs_mul, he]
      apply mul_le_of_le_one_right (abs_nonneg _)
      have hj := responseNode_mem_unit q j
      nlinarith [hj.1, hj.2, sq_nonneg (responseNode q j)]
theorem finePairRowMass_unit (d D M q a b C T₀ N) :
    finePairRowMass d D M q a b C T₀ N .unit =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      (∑ i, ∑ j, |finePairUnitMatrix d D i j|) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]
theorem finePairRowMass_coarse (d ) [NeZero d] (D M q a b C T₀ N)
    (hT : 0 ≤ T₀) :
    finePairRowMass d D M q a b C T₀ N .coarse =
      (∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (T₀^2/2)) := by
  rw [finePairRowMass, highPacketMarkMass_eq_variation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    highPacketSignedMeasure_totalVariation _ _ _ _ _ _ _ _ _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _),
    finePairTimeMatrix_cost_integral d 0 T₀ le_rfl hT]
  simp only [zero_pow (by norm_num : 2 ≠ 0), sub_zero]
theorem finePairRowMass_fine (d ) [NeZero d] (D M q a b C T₀ N)
    (hT : 0 ≤ T₀) (hTN : T₀ ≤ N) :
    finePairRowMass d D M q a b C T₀ N .fine =
      (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) *
      ((∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N^2-T₀^2)/2)) := by
  rw [finePairRowMass, finePairPacketMarkMass, signedMarkMass_eq_variation _ _ (finePairPacketWeight_integrable _ a b M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _))]
  change ((finePairPacketSignedMeasure _ a b M q C _).variation univ).toReal = _
  rw [finePairPacketSignedMeasure_totalVariation _ a b M q C _
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _),
    finePairTimeMatrix_cost_integral d T₀ N hT hTN]
  ring
theorem spatial_matrix_l1_eq_zero_iff {d F : ℕ}
    (A : HighFrameIndex d F → HighFrameIndex d F → ℝ) :
    spatialMatrixL1 A = 0 ↔ ∀ β β', A β β' = 0 := by
  constructor
  · intro h β β'
    have hentry : |A β β'| ≤ spatialMatrixL1 A := by
      calc
        _ ≤ ∑ γ, |A β γ| := Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ β')
        _ ≤ _ := by
          exact Finset.single_le_sum (f := fun β => ∑ γ, |A β γ|)
            (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
            (Finset.mem_univ β)
    exact abs_eq_zero.mp (le_antisymm (hentry.trans_eq h) (abs_nonneg _))
  · intro h
    simp [spatialMatrixL1, h]
theorem finePairUnitMatrix_l1_pos (d F : ℕ) :
    0 < spatialMatrixL1 (finePairUnitMatrix d F) := by
  apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
  intro he
  have hk := finePairUnitMatrix_kernel (d := d) (F := F)
    (n := 1) (fun _ => (0 : Covariate d)) (0 : Fin 1) 0
  simp only [spatialFrameCovariance, ((spatial_matrix_l1_eq_zero_iff _).mp he.symm), mul_zero, Finset.sum_const_zero] at hk
  norm_num at hk
theorem highPacketSlope_joint_measurable_finePair {Z : Type*} [MeasurableSpace Z]
    (d D q : ℕ) (a b : ℝ) (B : Z → Covariate d → Fin 2 → ℝ)
    (hB : ∀ l, Measurable (fun zx : Z × Covariate d => B zx.1 zx.2 l)) :
    Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      highPacketSlope a b D 2 D q (fun ζ l => B ζ ex.2 l) ex.1) := by
  have hc : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      densityMargin a b (densityPacketAtom a b D 2 D ex.1.2.1).1 / (2 * b)) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      densityMargin a b (densityPacketAtom a b D 2 D h.1).1 / (2 * b))).comp
        (measurable_snd.comp measurable_fst)
  have he (l : Fin 2) : Measurable (fun ex : (Z × HighPacketMarkIndex (HighFrameIndex d D) D 2 D q) × Covariate d =>
      (densityPacketAtom a b D 2 D ex.1.2.1).2 l) :=
    (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
      (densityPacketAtom a b D 2 D h.1).2 l)).comp (measurable_snd.comp measurable_fst)
  exact hc.mul (Finset.measurable_fun_sum _ (fun l _ => (he l).mul
    ((hB l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))))
theorem finePairRowSlope_joint_measurable (d k D M q a b j) (i : FinePairRowTag) :
    Measurable (fun ex : FinePairRowMark d D M q i × Covariate d =>
      finePairRowSlope d k D M q a b j i ex.1 ex.2) := by
  have h_finePairTimeFieldValue_measurable : Measurable (fun ex : (ℝ × FinePairFieldMark d) × Covariate d =>
      finePairTimeFieldValue ex.1 ex.2) := (boundedHyperplaneFieldValue_measurable d).comp
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hψ  :=
    h_finePairTimeFieldValue_measurable.comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  cases i
  · exact (highPacketSlope_measurable a b D 2 D q (fun _ => fun _ => 1)
      (fun _ => measurable_const)).comp measurable_fst
  · exact highPacketSlope_joint_measurable_finePair d D q a b
      (fun ζ x _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hψ)
  · exact finePairPacketSlope_joint_measurable a b M q
      (fun ζ x => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hψ
section Reference
variable (d : ℕ) [NeZero d] (k D M q : ℕ) (a b C T₀ N : ℝ)
    (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
include hpos
theorem finePairRowLaw_probability (i ) :
    IsProbabilityMeasure (finePairRowLaw d D M q a b C T₀ N i) := by
  cases i
  · exact highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
  · exact highPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
  · exact finePairPacketAbsoluteLaw_probability (finePairTimeFieldMeasure d T₀ N) a b M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
theorem finePairRowSlope_integrable (ha : 0 < a) (hab : a < b)
    (j x i) :
    Integrable (fun e => finePairRowSlope d k D M q a b j i e x)
      (finePairRowLaw d D M q a b C T₀ N i) := by
  letI := finePairRowLaw_probability d D M q a b C T₀ N hpos i
  have hm : Measurable (fun e : FinePairRowMark d D M q i => finePairRowSlope d k D M q a b j i e x) :=
    (finePairRowSlope_joint_measurable d k D M q a b j i).comp
    (measurable_id.prodMk (measurable_const (a := x)))
  apply (integrable_const ((b-a)/(4*b))).mono' hm.aestronglyMeasurable
  filter_upwards [] with e
  have h_finePairRowSlope_bound : |finePairRowSlope d k D M q a b j i e x| ≤ (b-a)/(4*b) := by
    cases i
    · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num)
        (fun _ => fun _ => 1) (by intro _ _; norm_num) e
    · exact highPacketSlope_bound a b ha hab D 2 D q (by norm_num) _
        (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le) e
    · exact finePairPacketSlope_bound a b ha hab M q _
        (fun ζ => (finePairTimeFieldValue_abs ζ _).le) e
  simpa only [Real.norm_eq_abs] using h_finePairRowSlope_bound
end Reference
theorem finePairRowMass_positive (d ) [NeZero d] (D ) (hD : 3 ≤ D)
    (M q ) (hq : 1 ≤ q) (a b ) (ha : 0 < a) (hab : a < b)
    (C ) (hC : 0 < C) (T₀ N ) (hT₀ : 0 < T₀) (hTN : T₀ < N)
    (i ) : 0 < finePairRowMass d D M q a b C T₀ N i := by
  have hr : 0 < ∑ h : Fin (2*q+2), |responseWeight q h| :=
    lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)
  have hc : 0 < 2*C^2 := mul_pos (by norm_num) (pow_pos hC _)
  have h_ordinary_density_absolute_cost_pos : 0 < ∑ h : HighDensityMarkIndex D 2 D, |densityPacketWeight a b D 2 D h| := by
    rw [densityPacketWeight_variation a b ha hab D 2 D (by norm_num)]
    have hb  := (ha.trans hab).ne'
    have hθ := densityMargin_zero_ne a b ha hab
    have hp : densityPacketPrefactor a b 2 ≠ 0 := by
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (div_ne_zero hb hθ))
    have he : 0 < derivativeOrder D := by unfold derivativeOrder; omega
    exact mul_pos (mul_pos (abs_pos.mpr hp) (Real.cosh_pos _)) (pow_pos (by exact_mod_cast he) _)
  have ho := h_ordinary_density_absolute_cost_pos
  have h_finePairDistanceMatrix_l1_pos : 0 < spatialMatrixL1 (finePairDistanceMatrix d D) := by
    apply lt_of_le_of_ne (spatial_matrix_l1_nonnegative _) ?_
    intro he
    have hz := (spatial_matrix_l1_eq_zero_iff _).mp he.symm
    let U : Fin 2 → Covariate d := fun i _ => if i = 0 then 0 else 1
    have hk := finePairDistanceMatrix_kernel hD U 0 1
    simp only [spatialFrameCovariance, hz, mul_zero, Finset.sum_const_zero] at hk
    have heU : spatialSquaredDistance (U 0) (U 1) = d := by simp [U, spatialSquaredDistance]
    rw [heU] at hk
    exact NeZero.ne d (Nat.cast_eq_zero.mp (neg_eq_zero.mp hk.symm))
  have hA₁ : 0 < ∑ i, ∑ j, |finePairDistanceMatrix d D i j| := h_finePairDistanceMatrix_l1_pos
  cases i
  · rw [finePairRowMass_unit]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) (finePairUnitMatrix_l1_pos d D)
  · rw [finePairRowMass_coarse d D M q a b C T₀ N hT₀.le]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) (mul_pos hA₁ (by positivity))
  · rw [finePairRowMass_fine d D M q a b C T₀ N hT₀.le hTN.le]
    exact mul_pos (mul_pos (mul_pos (by rw [finePairDensityWeight_variation a b ha hab M]; exact mul_pos (mul_pos (by norm_num) (abs_pos.mpr (div_ne_zero (pow_ne_zero _ (ha.trans hab).ne') (pow_ne_zero _ (densityMargin_zero_ne a b ha hab))))) (Real.cosh_pos _)) hr) hc) (mul_pos hA₁ (by nlinarith))
section
theorem historyFold_linear_extension_invariant {ι X : Type*} [PartialOrder ι]
    (dependent : ι → ι → Prop) (update : ι → X → X)
    (hcomp : ∀ x y, dependent x y → x ≤ y ∨ y ≤ x)
    (hcomm : ∀ x y, ¬ dependent x y → ∀ state,
      update y (update x state) = update x (update y state))
    {l l' : List ι} (hperm : l.Perm l')
    (hl : l.Pairwise (fun x y => ¬ y ≤ x))
    (hl' : l'.Pairwise (fun x y => ¬ y ≤ x)) (initial : X) :
    l.foldl (fun state x => update x state) initial =
      l'.foldl (fun state x => update x state) initial := by
  induction l' generalizing l initial with
  | nil =>
    have  := List.perm_nil.mp hperm
    subst l
    rfl
  | cons x xs ih =>
    obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp (hperm.mem_iff.mpr List.mem_cons_self)
    obtain ⟨hbefore, hafter, hcross⟩ := List.pairwise_append.mp hl
    have hmove : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state) := by
      intro y hy state
      have hxy  := hcross y hy x List.mem_cons_self
      have hyne : y ≠ x := by intro h; subst y; exact hxy le_rfl
      have hm  := hperm.mem_iff.mp (List.mem_append_left _ hy)
      have hyx  := (List.pairwise_cons.mp hl').1 y (by simpa only [List.mem_cons, hyne, false_or] using hm)
      have hdep  := fun hd => (hcomp x y hd).elim hxy hyx
      exact (hcomm x y hdep state).symm
    have h_historyFold_move_to_front (before : List ι) (hcomm : ∀ y ∈ before, ∀ state, update x (update y state) = update y (update x state)) : (before ++ x :: after).foldl (fun state y => update y state) initial =
        (before ++ after).foldl (fun state y => update y state) (update x initial) := by
      have hfold : ∀ state, update x (before.foldl (fun s y => update y s) state) =
          before.foldl (fun s y => update y s) (update x state) := by
        induction before with
        | nil => intro state; rfl
        | cons y ys ih =>
          intro state
          simp only [List.foldl_cons]
          rw [ih (fun z hz => hcomm z (List.mem_cons_of_mem y hz)), hcomm y List.mem_cons_self]
      simp only [List.foldl_append, List.foldl_cons]
      rw [hfold]
    rw [(h_historyFold_move_to_front before hmove)]
    exact ih ((List.perm_middle.symm.trans hperm).cons_inv) (hl.sublist (List.Sublist.append (List.Sublist.refl before) (List.Sublist.cons x (List.Sublist.refl after)))) hl'.of_cons (update x initial)
def historyWordMarkedState  (update : J → E → X → X)
    (initial : X) (word : List J) (marks : Fin word.length → E) : X :=
  historyWordState (fun p => update p.1 p.2) initial
    (List.ofFn (fun i => (word.get i, marks i)))
theorem historyHeapMarkEquiv_state  [MeasurableSpace E]
    (dependent )
    (hsymm : ∀ ⦃a b⦄, dependent a b → dependent b a)
    (update )
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    {u v : List J} (e : WordHeapPiece u dependent ≃o WordHeapPiece v dependent)
    (he : ∀ x, wordHeapLabel (e x) = wordHeapLabel x)
    (initial : X) (marks : Fin u.length → E) :
    historyWordMarkedState update initial v (historyHeapMarkEquiv e marks) =
      historyWordMarkedState update initial u marks := by
  have h_historyWordMarkedState_eq_heapFold (word : List J) (marks : Fin word.length → E) : historyWordMarkedState update initial word marks =
      (List.ofFn (fun i : Fin word.length => (⟨i⟩ : WordHeapPiece word dependent))).foldl
        (fun state x => update (wordHeapLabel x) (marks x.position) state) initial := by
    unfold historyWordMarkedState historyWordState
    have heq : (List.ofFn (fun i => (word.get i, marks i))) =
        (List.ofFn (fun i => (⟨i⟩ : WordHeapPiece word dependent))).map
          (fun x => (wordHeapLabel x, marks x.position)) := by
      rw [List.map_ofFn]
      rfl
    rw [heq, List.foldl_map]
  classical
  let l := List.ofFn (fun i => (⟨i⟩ : WordHeapPiece u dependent))
  let l' := List.ofFn (fun i => e.symm (⟨i⟩ : WordHeapPiece v dependent))
  have hl'nd  := List.nodup_ofFn.mpr (fun _ _ h =>
    congrArg WordHeapPiece.position (e.symm.injective h))
  have hp : l.Perm l' := (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr (fun _ _ h => congrArg WordHeapPiece.position h)) hl'nd).mpr (by
    intro x
    constructor
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨(e x).position, by
        have hx : (⟨(e x).position⟩ : WordHeapPiece v dependent) = e x := by cases e x; rfl
        rw [hx, e.symm_apply_apply]⟩
    · intro _
      apply List.mem_ofFn.mpr
      exact ⟨x.position, by cases x; rfl⟩)
  have hl' : l'.Pairwise (fun x y => ¬ y ≤ x) := by
    apply List.pairwise_iff_getElem.mpr
    intro i j hi hj hij hle
    simp only [l', List.getElem_ofFn] at hle
    have hh := wordHeap_reachable_position_le (e.monotone hle)
    simp only [OrderIso.apply_symm_apply] at hh
    exact (Nat.not_le_of_lt hij) hh
  let action := fun (x : WordHeapPiece u dependent) state =>
    update (wordHeapLabel x) (marks x.position) state
  have hfold := historyFold_linear_extension_invariant
    (fun x y => dependent (wordHeapLabel x) (wordHeapLabel y)) action
    (fun _ _ => wordHeap_dependent_comparable hsymm)
    (fun x y h state => hcomm _ _ h _ _ state) hp (by apply List.pairwise_iff_getElem.mpr; intro i j hi hj hij hle; simp only [l, List.getElem_ofFn] at hle; have hh := wordHeap_reachable_position_le hle; exact (Nat.not_le_of_lt hij) hh) hl' initial
  rw [h_historyWordMarkedState_eq_heapFold u marks, hfold, h_historyWordMarkedState_eq_heapFold v (historyHeapMarkEquiv e marks)]
  have hmap : l' = (List.ofFn (fun i => (⟨i⟩ : WordHeapPiece v dependent))).map e.symm := by
    rw [List.map_ofFn]
    rfl
  rw [hmap, List.foldl_map]
  congr 1
  funext state x
  have hlabel := he (e.symm x)
  have hmark := historyHeapMarkEquiv_position e marks (e.symm x)
  simp only [OrderIso.apply_symm_apply] at hlabel hmark
  simp only [action, hlabel, hmark]
section
variable {J : Type*} [Fintype J] [LinearOrder J]
def historyCanonicalWordMarks (dependent : J → J → Prop)
    (g : HistoryShape (fun a b => ¬ dependent a b)) 
    (marks : Fin (historyShapeLength dependent g) → E) : Fin g.out.length → E :=
  fun i => marks (Fin.cast (historyShapeLength_out dependent g).symm i)
theorem historyMarkedRawState_eq_wordMarkedState (dependent )
     (update : J → E → X → X) (initial : X)
    (g : HistoryShape (fun a b => ¬ dependent a b))
    (marks : Fin (historyShapeLength dependent g) → E) :
    historyMarkedRawState dependent update initial ⟨g, marks⟩ =
      historyWordMarkedState update initial g.out (historyCanonicalWordMarks dependent g marks) := by
  have hm : (List.ofFn (fun i : Fin (historyShapeLength dependent g) =>
      (historyShapeCanonicalLabels dependent g i, marks i))) =
      (List.ofFn (fun i : Fin (historyShapeLength dependent g) => i)).map
        (fun i => (historyShapeCanonicalLabels dependent g i, marks i)) := by
    rw [List.map_ofFn]
    rfl
  have ht : (List.ofFn (fun i : Fin (historyShapeLength dependent g) =>
      (historyShapeCanonicalLabels dependent g i, marks i))) =
      List.ofFn (fun i : Fin g.out.length => (g.out.get i, historyCanonicalWordMarks dependent g marks i)) := by
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact historyShapeLength_out dependent g)
    intro i hi hi'
    simp only [List.getElem_ofFn, historyShapeCanonicalLabels, historyCanonicalWordMarks]
    congr 1
  have hh := congrArg (fun l : List (J × E) =>
    l.foldl (fun state p => update p.1 p.2 state) initial) (hm.symm.trans ht)
  rw [List.foldl_map] at hh
  exact hh
def historyAppendWordMarks (dependent )
    (j : J) (g : HistoryShape (fun a b => ¬ dependent a b))
     [MeasurableSpace E] (fresh : E)
    (marks : Fin (historyShapeLength dependent g) → E) : Fin (g.out ++ [j]).length → E :=
  fun i => historyFiniteMarkAppendEquiv (historyShapeLength dependent g) (fresh, marks)
    (Fin.cast (by rw [historyShapeLength_out]; simp) i)
theorem historyMarkedRawState_append (dependent hsymm)
     [MeasurableSpace E] (update : J → E → X → X)
    (hcomm : ∀ j k, ¬ dependent j k → ∀ e f state,
      update k f (update j e state) = update j e (update k f state))
    (initial : X) (j : J) (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedRawState dependent update initial
      (historyMarkedAppend dependent hsymm j (h, fresh)) =
      update j fresh (historyMarkedRawState dependent update initial h) := by
  obtain ⟨g, marks⟩ := h
  change historyMarkedRawState dependent update initial
      ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ = _
  have h_historyCanonicalAppend_word_marks (g : HistoryShape (fun a b => ¬ dependent a b)) (fresh : E) (marks : Fin (historyShapeLength dependent g) → E) : historyCanonicalWordMarks dependent (historyShapeAppend dependent j g)
      (historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)) =
      historyHeapMarkEquiv (historyCanonicalAppendHeapIso dependent hsymm j g)
        (historyAppendWordMarks dependent j g fresh marks) := by
    let e := historyCanonicalAppendHeapIso dependent hsymm j g
    let hlen : historyShapeLength dependent g + 1 = (g.out ++ [j]).length := by
      rw [historyShapeLength_out]; simp
    have hc (x : WordHeapPiece (g.out ++ [j]) dependent) :
        historyCanonicalAppendCoordinates dependent hsymm j g (Fin.cast hlen.symm x.position) =
        Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm (e x).position := by
      unfold historyCanonicalAppendCoordinates
      change Fin.cast (historyShapeLength_out dependent (historyShapeAppend dependent j g)).symm
        (historyHeapCoordinateEquiv e (Fin.cast hlen (Fin.cast hlen.symm x.position))) = _
      rw [Fin.cast_cast, Fin.cast_refl, historyHeapCoordinateEquiv_position]
      rfl
    have hm (x : WordHeapPiece (g.out ++ [j]) dependent) :=
      MeasurableEquiv.piCongrLeft_apply_apply
        (historyCanonicalAppendCoordinates dependent hsymm j g)
        (β := fun _ => E) (historyFiniteMarkAppendEquiv _ (fresh, marks)) (Fin.cast hlen.symm x.position)
    ext i
    let x : WordHeapPiece (g.out ++ [j]) dependent := e.symm ⟨i⟩
    have hx : (e x).position = i := by simp only [x, e.apply_symm_apply]
    have hh := hm x
    rw [hc x, hx] at hh
    have ht := historyHeapMarkEquiv_position e (historyAppendWordMarks dependent j g fresh marks) x
    rw [hx] at ht
    exact hh.trans ht.symm
  have h_historyAppendWordMarkedState (g : HistoryShape (fun a b => ¬ dependent a b)) (fresh : E) (marks : Fin (historyShapeLength dependent g) → E) (update : J → E → X → X) (initial : X) : historyWordMarkedState update initial (g.out ++ [j])
      (historyAppendWordMarks dependent j g fresh marks) =
      update j fresh (historyWordMarkedState update initial g.out
        (historyCanonicalWordMarks dependent g marks)) := by
    have ht : (List.ofFn (fun i : Fin (g.out ++ [j]).length =>
        ((g.out ++ [j]).get i, historyAppendWordMarks dependent j g fresh marks i))) =
        (List.ofFn (fun i : Fin g.out.length =>
          (g.out.get i, historyCanonicalWordMarks dependent g marks i))) ++ [(j, fresh)] := by
      apply List.ext_getElem (by simp only [List.length_ofFn, List.length_append, List.length_singleton])
      intro i hi hi'
      by_cases hiold : i < g.out.length
      · rw [List.getElem_append_left (by simpa only [List.length_ofFn] using hiold)]
        simp only [List.getElem_ofFn]
        have hg : (g.out ++ [j]).get ⟨i, by simpa only [List.length_ofFn] using hi⟩ = g.out.get ⟨i, hiold⟩ := by
          simp only [List.get_eq_getElem, List.getElem_append_left hiold]
        rw [hg]
        have h_historyAppendWordMarks_old : historyAppendWordMarks dependent j g fresh marks
            (historyPrefixHeapEmbedding g.out dependent j (⟨⟨i, hiold⟩⟩ : WordHeapPiece g.out dependent)).position =
            historyCanonicalWordMarks dependent g marks (⟨⟨i, hiold⟩⟩ : WordHeapPiece g.out dependent).position := by
          unfold historyAppendWordMarks historyCanonicalWordMarks
          have he : Fin.cast (by rw [historyShapeLength_out]; simp)
              (historyPrefixHeapEmbedding g.out dependent j (⟨⟨i, hiold⟩⟩ : WordHeapPiece g.out dependent)).position =
              (Fin.cast (historyShapeLength_out dependent g).symm (⟨⟨i, hiold⟩⟩ : WordHeapPiece g.out dependent).position).castSucc := by
            apply Fin.ext
            rfl
          rw [he, historyFiniteMarkAppendEquiv_old]
        exact congrArg (fun a => (g.out.get ⟨i, hiold⟩, a))
          h_historyAppendWordMarks_old
      · have : i = g.out.length := by
          simp only [List.length_ofFn, List.length_append, List.length_singleton] at hi
          omega
        subst i
        rw [List.getElem_append_right (by simp only [List.length_ofFn]; exact le_rfl)]
        simp only [List.length_ofFn, Nat.sub_self, List.getElem_cons_zero, List.getElem_ofFn]
        have hg : (g.out ++ [j]).get ⟨g.out.length, by simpa only [List.length_ofFn] using hi⟩ = j := by
          simp only [List.get_eq_getElem, List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_cons_zero]
        rw [hg]
        have h_historyAppendWordMarks_fresh : historyAppendWordMarks dependent j g fresh marks (wordHeapAppendedPiece g.out dependent j).position = fresh := by
          unfold historyAppendWordMarks
          have he : Fin.cast (by rw [historyShapeLength_out]; simp)
              (wordHeapAppendedPiece g.out dependent j).position = Fin.last (historyShapeLength dependent g) := by
            apply Fin.ext
            exact (historyShapeLength_out dependent g).symm
          rw [he, historyFiniteMarkAppendEquiv_last]
        exact congrArg (fun a => (j, a)) h_historyAppendWordMarks_fresh
    unfold historyWordMarkedState historyWordState
    rw [ht, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [historyMarkedRawState_eq_wordMarkedState,
    h_historyCanonicalAppend_word_marks,
    historyHeapMarkEquiv_state dependent hsymm update hcomm
      (historyCanonicalAppendHeapIso dependent hsymm j g)
      (historyCanonicalAppendHeapIso_label dependent hsymm j g),
    h_historyAppendWordMarkedState, historyMarkedRawState_eq_wordMarkedState]
end
variable {J : Type*} [Fintype J] [LinearOrder J]
theorem highMarkedRawState_patch_append (d k : ℕ) [NeZero k]
    [LinearOrder (HighWindowLabels d k)]
    {E R : Type*} [MeasurableSpace E]
    (slope intercept : HighWindowLabels d k → E → Covariate d → ℝ)
    (response : HighWindowLabels d k → E → R → R)
    (initial : (Covariate d → ℝ) × (HighWindowLabels d k → R))
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) E) (fresh : E) :
    historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
      (fun j e => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e) (response j e)) initial
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, fresh)) =
    rawPatchUpdate j (highTorusPatch d k j) (slope j fresh) (intercept j fresh) (response j fresh)
      (historyMarkedRawState (fun i j => j ∈ highNeighborLabels d k i)
        (fun j e => rawPatchUpdate j (highTorusPatch d k j) (slope j e) (intercept j e) (response j e)) initial h) := by
  have hi : ∀ i j : HighWindowLabels d k, j ∉ highNeighborLabels d k i → i ≠ j := by
    intro i j h he
    subst j
    exact h (highNeighborLabels_self_mem d k i)
  have hd  :=
    fun i j h => highTorusPatch_disjoint_of_not_neighbor d k i j h
  apply historyMarkedRawState_append
  intro i j h e f state
  have h_rawPatchUpdate_commute (P) (Q) (A) (B) (C) (D) (f) (g) (hij : i ≠ j) (hPQ : Disjoint P Q) : rawPatchUpdate j Q C D g (rawPatchUpdate i P A B f state) =
      rawPatchUpdate i P A B f (rawPatchUpdate j Q C D g state) := by
    have h_affinePatchUpdate_commute : affinePatchUpdate Q C D (affinePatchUpdate P A B state.1) =
        affinePatchUpdate P A B (affinePatchUpdate Q C D state.1) := by
      classical
      funext x
      by_cases hxP : x ∈ P
      · have hxQ : x ∉ Q := fun hxQ => Set.disjoint_left.1 hPQ hxP hxQ
        simp [affinePatchUpdate, hxP, hxQ]
      · by_cases hxQ : x ∈ Q <;> simp [affinePatchUpdate, hxP, hxQ]
    have h_responseCoordinateUpdate_commute : responseCoordinateUpdate j g (responseCoordinateUpdate i f state.2) =
        responseCoordinateUpdate i f (responseCoordinateUpdate j g state.2) := by
      unfold responseCoordinateUpdate
      simp only [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
      exact Function.update_comm hij _ _ state.2
    exact Prod.ext h_affinePatchUpdate_commute
      h_responseCoordinateUpdate_commute
  exact h_rawPatchUpdate_commute _ _ _ _ _ _ _ _ (hi i j h) (hd i j h)
end
section Finite
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] (R : HighUnionRowData d k F I E)
def highUnionHistoryState (δ : ℝ) (n ) (labels : Fin n → HighWindowLabels d k)
    (initial : HighRawState d k F) (marks : Fin n → HighUnionMark E) : HighRawState d k F :=
  (List.ofFn (fun i => i)).foldl
    (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ) initial
theorem highUnionHistory_density_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ n labels initial) (hi : Measurable initial.1) :
    Measurable (fun mx : (Fin n → HighUnionMark E) × Covariate d =>
      (highUnionHistoryState R δ n labels initial mx.1).1 mx.2) := by
  exact affinePatchFold_density_joint_measurable (highTorusPatch d k)
    (highTorusPatch_measurableSet d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e)
    (fun j => highUnionSlope_joint_measurable R hSlope j)
    (fun _ => (highUnionIntercept_measurable R hOffset δ).comp measurable_fst)
    (fun _ => highUnionResponseReset R) n labels (List.ofFn (fun i => i))
    (fun _ => initial) (hi.comp measurable_snd)
theorem highUnionHistory_density_mean_one [∀ i, IsProbabilityMeasure (R.rowLaw i)]
    (hMass : ∀ i, 0 ≤ R.rowMass i) (hTotal : 0 < highRowTotalMass R.rowMass)
    (hSlope : ∀ j x i, Measurable (fun e => R.rowSlope j i e x))
    (hiSlope : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i))
    (hcSlope : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0)
    (hOffset : ∀ i, Measurable (R.rowIntercept i))
    (a b ) (hOffsetBound : ∀ i e, R.rowIntercept i e ∈ Icc a b)
    (δ ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (n labels initial) (hinit : ∀ x, initial.1 x = 1) (x ) :
    (∫ marks, (highUnionHistoryState R δ n labels initial marks).1 x
      ∂Measure.pi (fun _ => highUnionLaw R δ)) = 1 := by
  let π := highUnionLaw R δ
  letI : IsProbabilityMeasure π := highUnionLaw_probability R hMass hTotal δ hδ0 hδ1.le
  let s := fun (j : HighWindowLabels d k) (e : HighUnionMark E) =>
    if x ∈ highTorusPatch d k j then highUnionSlope R j e x else 1
  let o := fun (j : HighWindowLabels d k) (e : HighUnionMark E) =>
    if x ∈ highTorusPatch d k j then highUnionIntercept R δ e else 0
  have hs : ∀ j, Integrable (s j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _
        (highCenteredRowUnionSlope_measurable _ (hSlope j x))
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass _
          (rowSigmaFunction_measurable _ (hSlope j x)) (hiSlope j x))
    · simp only [s, if_neg hx]
      exact integrable_const _
  have ho : ∀ j, Integrable (o j) π := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [o, if_pos hx]
      exact balancedReferenceLaw_integrable _ δ _ (highUnionIntercept_measurable R hOffset δ)
        (highRowReferenceUnion_integrable R.rowLaw R.rowMass _
          (rowSigmaFunction_measurable _ hOffset)
          (fun i => boundedIntercept_integrable (R.rowLaw i) (R.rowIntercept i)
            (hOffset i) a b (hOffsetBound i)))
    · simp only [o, if_neg hx]
      exact integrable_const _
  have hmean : ∀ j, (∫ e, s j e ∂π) + (∫ e, o j e ∂π) = 1 := by
    intro j
    by_cases hx : x ∈ highTorusPatch d k j
    · simp only [s, o, if_pos hx]
      change (∫ e, highCenteredRowUnionSlope (fun i e => R.rowSlope j i e x) e
        ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) +
        (∫ e, highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ e
          ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) = 1
      have h_highCenteredRowUnionIntercept_integral_one : (∫ e, highCenteredRowUnionIntercept R.rowLaw R.rowMass R.rowIntercept δ e ∂highCenteredRowUnionLaw R.rowLaw R.rowMass δ) = 1 := by
        letI := highRowReferenceUnion_probability R.rowLaw R.rowMass hMass hTotal
        exact balancedIntercept_integral_one _ δ hδ0 hδ1 _
          (rowSigmaFunction_measurable R.rowIntercept hOffset)
          (boundedIntercept_integrable (highRowReferenceUnion R.rowLaw R.rowMass) _
            (rowSigmaFunction_measurable R.rowIntercept hOffset) a b (fun e => hOffsetBound e.1 e.2))
      rw [highCenteredRowUnionSlope_integral_zero R.rowLaw R.rowMass hMass hTotal
          _ (hSlope j x) (hiSlope j x) (hcSlope j x) δ hδ0 hδ1.le,
        h_highCenteredRowUnionIntercept_integral_one]
      norm_num
    · simp only [s, o, if_neg hx, integral_const, integral_zero,
        measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one, add_zero]
      norm_num
  convert finiteAffineHistory_integral_one π s o hs ho hmean n labels using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro marks
  exact (affinePatchFold_density_eq (highTorusPatch d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R)
    labels marks (List.ofFn (fun i => i)) initial x).trans (by rw [hinit x]; rfl)
theorem highUnionHistory_density_interval (δ a b)
    (hLegal : ∀ j e x v, v ∈ Icc a b →
      highUnionSlope R j e x * v + highUnionIntercept R δ e ∈ Icc a b)
    (n labels initial)
    (hi : ∀ x, initial.1 x ∈ Icc a b) (marks x) :
    (highUnionHistoryState R δ n labels initial marks).1 x ∈ Icc a b :=
  affineRawHistory_density_interval (highTorusPatch d k) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R)
    labels (List.ofFn (fun i => i)) marks a b hLegal initial hi x
theorem highUnionHistory_coefficient_ball (δ Cfr ) (hCfr : 0 < Cfr)
    (hVector : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹)
    (hTime : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1)
    (n labels initial)
    (hi : ∀ j, (∑ γ, |initial.2 j γ|) ≤ Cfr⁻¹) (marks : Fin n → HighUnionMark E) :
    ∀ j, (∑ γ, |(highUnionHistoryState R δ n labels initial marks).2 j γ|) ≤ Cfr⁻¹ := by
  have hf : ∀ indices : List (Fin n), ∀ initial : HighRawState d k F,
      (∀ j, (∑ γ, |initial.2 j γ|) ≤ Cfr⁻¹) → ∀ j,
      (∑ γ, |(indices.foldl (fun θ i => highUnionRawUpdate R δ (labels i) (marks i) θ)
        initial).2 j γ|) ≤ Cfr⁻¹ := by
    intro indices
    induction indices with
    | nil => intro initial hi j; exact hi j
    | cons i indices ih =>
      intro initial hi
      apply ih
      intro j
      by_cases hj : j = labels i
      · subst j
        change (∑ γ, |(Function.update initial.2 (labels i)
          (highUnionResponseReset R (marks i) (initial.2 (labels i)))) (labels i) γ|) ≤ _
        rw [Function.update_self]
        exact highUnionResponseReset_ball R Cfr hCfr hVector hTime _ _ (hi _)
      · simpa only [highUnionRawUpdate, rawPatchUpdate, responseCoordinateUpdate,
          Function.update_of_ne hj] using hi j
  exact hf _ initial hi
end Finite
section Canonical
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (R : HighUnionRowData d k F I E)
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)
def highUnionMarkedState (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) : HighRawState d k F :=
  historyMarkedRawState dependent (highUnionRawUpdate R δ) initial h
def highUnionMarkedDensity (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) (x : Covariate d) : ℝ :=
  (highUnionMarkedState R dependent δ initial h).1 x
def highUnionMarkedMass (δ : ℝ) (initial : HighRawState d k F)
    (h : HistoryMarked dependent (HighUnionMark E)) : ℝ :=
  ∫ x, highUnionMarkedDensity R dependent δ initial h x ∂cubeVolume d
theorem highUnionMarkedDensity_joint_measurable [∀ i, StandardBorelSpace (E i)]
    (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2))
    (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ initial) (hi : Measurable initial.1) :
    Measurable (fun hx : HistoryMarked dependent (HighUnionMark E) × Covariate d =>
      highUnionMarkedDensity R dependent δ initial hx.1 hx.2) := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let X := fun g : HistoryShape (fun i j => ¬ dependent i j) =>
    Fin (historyShapeLength dependent g) → HighUnionMark E
  let G : Sigma (fun g => X g × Covariate d) → ℝ := fun hx =>
    highUnionMarkedDensity R dependent δ initial ⟨hx.1,hx.2.1⟩ hx.2.2
  have hG : Measurable G := by
    apply (historySigma_measurable_iff G).mpr
    intro g
    exact highUnionHistory_density_joint_measurable R hSlope hOffset δ
      (historyShapeLength dependent g) (historyShapeCanonicalLabels dependent g) initial hi
  exact hG.comp (historySigmaProdMeasurableEquiv X (Covariate d)).measurable
end Canonical
structure HighUnionSourceGuards {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d) (M Cfr : ℝ)
    (R : HighUnionRowData d k F I E) : Prop where
  resolution : highCenterResolutionThreshold C ≤ M
  frame : 1 ≤ Cfr
  row_probability : ∀ i, IsProbabilityMeasure (R.rowLaw i)
  mass_nonneg : ∀ i, 0 ≤ R.rowMass i
  total_positive : 0 < highRowTotalMass R.rowMass
  activation_measurable : ∀ i, Measurable (R.rowActivation i)
  activation_bound : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i
  activation_centered : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0
  slope_measurable : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)
  slope_integrable : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i)
  slope_centered : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0
  intercept_measurable : ∀ i, Measurable (R.rowIntercept i)
  intercept_interval : ∀ i e, R.rowIntercept i e ∈
    Icc (C.densityLower + 1/M) (C.densityUpper - 1/M)
  row_reset_interval : ∀ j i e x v, v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
    R.rowSlope j i e x * v + R.rowIntercept i e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M)
  vector_measurable : ∀ i γ, Measurable (fun e => R.rowVector i e γ)
  time_measurable : ∀ i, Measurable (R.rowTime i)
  vector_ball : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹
  time_interval : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1
section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)
def highUnionVacuum : HighRawState d k F := ((fun _ => 1), 0)
def highUnionSourceState
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    HighRawState d k F :=
  highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) (highCenterMix C)
    highUnionVacuum h
def highUnionSourceDensity
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ := (highUnionSourceState C R h).1 x
def highUnionSourceMass
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) : ℝ :=
  ∫ x, highUnionSourceDensity C R h x ∂cubeVolume d
variable {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G
theorem highUnionSourceLaw_probability : IsProbabilityMeasure (highUnionLaw R (highCenterMix C)) := by
  letI := G.row_probability
  exact highUnionLaw_probability R G.mass_nonneg G.total_positive _
    (highCenterMix_mem C).1.le (highCenterMix_mem C).2.le
theorem highUnionSource_reset_interval (j e x v) (hv : v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highUnionSlope R j e x * v + highUnionIntercept R (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := G.row_probability
  exact highCenteredRowUnion_reset_source_legal C R.rowLaw R.rowMass
    G.mass_nonneg G.total_positive (fun i e => R.rowSlope j i e x) R.rowIntercept
    G.intercept_measurable M G.resolution G.intercept_interval
    (fun i e v hv => G.row_reset_interval j i e x v hv) e v hv
theorem highUnionSource_vacuum_interval :
    1 ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  have := highCenterResolution_guards C M G.resolution
  have := highCenterRadius_le_margins C
  constructor <;> linarith [highCenterRadius_pos C]
theorem highUnionSourceDensity_interval
    (h x) :
    highUnionSourceDensity C R h x ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) :=
  highUnionHistory_density_interval R (highCenterMix C) _ _
    (highUnionSource_reset_interval C R G) (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => highUnionSource_vacuum_interval C R G) h.2 x
theorem highUnionSourceState_coefficient_ball
    (h ) :
    ∀ j, (∑ γ, |(highUnionSourceState C R h).2 j γ|) ≤ Cfr⁻¹ := by
  exact highUnionHistory_coefficient_ball R (highCenterMix C) Cfr
    (by linarith [G.frame]) G.vector_ball G.time_interval (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => by simpa [highUnionVacuum] using
      (inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr))) h.2
theorem highUnionSourceDensity_joint_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceDensity C R hx.1 hx.2) :=
  highUnionMarkedDensity_joint_measurable R (fun i j => j ∈ highNeighborLabels d k i)
    G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const
theorem highUnionSourceMass_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (highUnionSourceMass C R) :=
  have h_highUnionMarkedMass_measurable (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop) (hSlope : ∀ j i, Measurable (fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2)) (hOffset : ∀ i, Measurable (R.rowIntercept i)) (δ) : Measurable (highUnionMarkedMass R dependent δ highUnionVacuum) := by
    letI := cubeVolume_isProbability d
    exact (highUnionMarkedDensity_joint_measurable R dependent hSlope hOffset δ highUnionVacuum measurable_const).stronglyMeasurable.integral_prod_right'.measurable
  (h_highUnionMarkedMass_measurable (fun i j => j ∈ highNeighborLabels d k i) G.slope_measurable G.intercept_measurable (highCenterMix C))
theorem highUnionSourceDensity_fiber_mean_one
    (g x) :
    (∫ marks, highUnionSourceDensity C R ⟨g,marks⟩ x
      ∂Measure.pi (fun _ => highUnionLaw R (highCenterMix C))) = 1 := by
  letI := G.row_probability
  exact highUnionHistory_density_mean_one R G.mass_nonneg G.total_positive
    (fun j x i => (G.slope_measurable j i).comp (measurable_id.prodMk measurable_const))
    G.slope_integrable G.slope_centered G.intercept_measurable _ _ G.intercept_interval
    (highCenterMix C) (highCenterMix_mem C).1.le (highCenterMix_mem C).2
    (historyShapeLength _ g) (historyShapeCanonicalLabels _ g) highUnionVacuum (fun _ => rfl) x
theorem highUnionSourceMass_interval [∀ i, StandardBorelSpace (E i)]
    (h ) :
    highUnionSourceMass C R h ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := cubeVolume_isProbability d
  exact boundedIntercept_mean_mem (cubeVolume d) (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    _ _ (highUnionSourceDensity_interval C R G h)
theorem highUnionSourceMass_fiber_mean_one [∀ i, StandardBorelSpace (E i)]
    (g ) :
    (∫ marks, highUnionSourceMass C R ⟨g,marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C))) = 1 := by
  letI := highUnionSourceLaw_probability C R G
  letI := cubeVolume_isProbability d
  let f := fun mx : (Fin (historyShapeLength _ g) → HighUnionMark E) × Covariate d =>
    highUnionSourceDensity C R ⟨g,mx.1⟩ mx.2
  have hm : Measurable f := highUnionHistory_density_joint_measurable R G.slope_measurable
    G.intercept_measurable (highCenterMix C) (historyShapeLength _ g)
    (historyShapeCanonicalLabels _ g) highUnionVacuum measurable_const
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards C M G.resolution).1
    linarith
  have hi : Integrable f ((Measure.pi (fun _ : Fin (historyShapeLength _ g) =>
      highUnionLaw R (highCenterMix C))).prod (cubeVolume d)) := by
    apply (integrable_const C.densityUpper).mono' hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro mx
    have hb := highUnionSourceDensity_interval C R G ⟨g,mx.1⟩ mx.2
    change ‖f mx‖ ≤ C.densityUpper
    rw [Real.norm_eq_abs, abs_of_nonneg (by
      dsimp [f]; linarith [hb.1, C.densityLower_pos, one_div_pos.mpr hM0])]
    exact hb.2.trans (by linarith [one_div_pos.mpr hM0])
  change (∫ marks, ∫ x, f (marks,x) ∂cubeVolume d
    ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C))) = 1
  rw [integral_integral_swap hi]
  have he (x : Covariate d) :
      (∫ marks, f (marks,x) ∂Measure.pi (fun _ : Fin (historyShapeLength _ g) =>
        highUnionLaw R (highCenterMix C))) = 1 := highUnionSourceDensity_fiber_mean_one C R G g x
  simp_rw [he]
  simp
theorem highUnionSourceMass_block_oscillation [∀ i, StandardBorelSpace (E i)] (hk : 2 ≤ k)
    (g marks marks' j)
    (hMarks : ∀ i, historyShapeCanonicalLabels _ g i ≠ j → marks i = marks' i) :
    |highUnionSourceMass C R ⟨g,marks⟩ - highUnionSourceMass C R ⟨g,marks'⟩| ≤
      (2 / k)^d * (C.densityUpper-C.densityLower) := by
  have h := highAffineMarkedMass_block_oscillation d k hk
    (fun i j => j ∈ highNeighborLabels d k i) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R (highCenterMix C) e)
    (fun j e => (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_const.prodMk measurable_id)) (fun _ _ => measurable_const)
    (fun _ => highUnionResponseReset R) (C.densityLower+1/M) (C.densityUpper-1/M)
    (by linarith [(highUnionSource_vacuum_interval C R G).1,
      (highUnionSource_vacuum_interval C R G).2])
    (highUnionSource_reset_interval C R G) highUnionVacuum measurable_const
    (fun _ => highUnionSource_vacuum_interval C R G) g marks marks' j hMarks
  apply h.trans
  have hM0 : 0 < M := by
    have := (highCenterResolution_guards C M G.resolution).1
    linarith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith [one_div_pos.mpr hM0]
end
theorem finePairSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N) :
    HighUnionSourceGuards C ↑M Cfr (finePairRowData d k D M q (C.densityLower+1/M)
    (C.densityUpper-1/↑M) Cfr T₀ N) := by
  let a := C.densityLower+1/↑M
  let b := C.densityUpper-1/↑M
  have hg := highCenterResolution_guards C ↑M hM
  have hM0 : (0 : ℝ) < M := by linarith [hg.1]
  have := highCenterRadius_pos C
  have hmargin := highCenterRadius_le_margins C
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hab : a < b := by dsimp [a,b]; linarith [hg.2]
  have hCf : 0 < Cfr := by linarith
  have hpos := finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf T₀ N hT₀ hTN
  refine {
    resolution := hM
    frame := hCfr
    row_probability := ?_
    mass_nonneg := ?_
    total_positive := ?_
    activation_measurable := ?_
    activation_bound := ?_
    activation_centered := ?_
    slope_measurable := ?_
    slope_integrable := ?_
    slope_centered := ?_
    intercept_measurable := ?_
    intercept_interval := ?_
    row_reset_interval := ?_
    vector_measurable := ?_
    time_measurable := ?_
    vector_ball := ?_
    time_interval := ?_ }
  · exact finePairRowLaw_probability d D M q a b Cfr T₀ N hpos
  · exact finePairRowMass_nonneg d D M q a b Cfr T₀ N
  · exact Finset.sum_pos' (fun i _ => (hpos i).le) ⟨.unit, Finset.mem_univ _, hpos .unit⟩
  · intro i
    cases i
    · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q Cfr _
        (fun _ _ => measurable_const))
    · exact absoluteActivation_measurable _ _ (highPacketMarkWeight_measurable a b D 2 D q Cfr _
        (finePairTimeMatrix_measurable d _))
    · exact absoluteActivation_measurable _ _ (finePairPacketWeight_measurable a b M q Cfr _
        (finePairTimeMatrix_measurable d _))
  · intro i e
    cases i <;> exact absoluteActivation_bound _ _ _
  · intro i
    cases i
    · exact highPacketActivation_centered (Measure.dirac ()) a b D 2 D q Cfr (fun _ => finePairUnitMatrix d D)
        (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
    · exact highPacketActivation_centered (finePairTimeFieldMeasure d 0 T₀) a b D 2 D q Cfr _
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
    · exact finePairPacketActivation_centered (finePairTimeFieldMeasure d T₀ N) a b M q Cfr _
        (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
  · exact finePairRowSlope_joint_measurable d k D M q a b
  · exact finePairRowSlope_integrable d k D M q a b Cfr T₀ N hpos ha hab
  · intro j x i
    have hm : Measurable (fun ζ =>
        finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) :=
      (boundedHyperplaneFieldValue_section_measurable d _).comp measurable_snd
    cases i
    · exact highPacketAbsoluteLaw_slope_integral_zero (Measure.dirac ()) a b ha hab D 2 D q (by norm_num)
        Cfr (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _) (hpos .unit)
        (fun _ => fun _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)
    · exact highPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d 0 T₀) a b ha hab
        D 2 D q (by norm_num) Cfr _ (finePairTimeMatrix_measurable d _)
        (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse)
        (fun ζ _ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) (fun _ => hm)
        (fun ζ _ => (finePairTimeFieldValue_abs ζ _).le)
    · exact finePairPacketAbsoluteLaw_slope_integral_zero (finePairTimeFieldMeasure d T₀ N) a b M q
        Cfr _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine)
        ha hab (fun ζ => finePairTimeFieldValue ζ (highLocalCoordinates d k j x)) hm
        (fun ζ => (finePairTimeFieldValue_abs ζ _).le)
  · intro i
    cases i
    · exact highPacketIntercept_measurable a b D 2 D q
    · exact highPacketIntercept_measurable a b D 2 D q
    · apply measurable_from_prod_countable_left
      intro h
      change Measurable (fun _ => (finePairDensityAtom a b M h.1).1)
      exact measurable_const
  have h_finePairRowIntercept_mem (i : FinePairRowTag) (e : FinePairRowMark d D M q i) : finePairRowIntercept d D M q a b i e ∈ Icc a b := by
    cases i
    · exact (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
    · exact (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
    · exact finePairPacketIntercept_mem a b hab.le M q e
  · exact h_finePairRowIntercept_mem
  have h_finePairRow_reset_interval (j : HighWindowLabels d k) (i : FinePairRowTag) (e : FinePairRowMark d D M q i) (x : Covariate d) (v : ℝ) (hv : v ∈ Icc a b) : finePairRowSlope d k D M q a b j i e x * v + finePairRowIntercept d D M q a b i e ∈ Icc a b := by
    cases i
    · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
        (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
        (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
        (fun _ : Unit => v) (fun _ _ => 1) () hv (by intro _; norm_num)
      convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
        highPacketIntercept, localDensityReset] <;> ring
    · have h := localDensityReset_mem_interval a b ha hab 2 (by norm_num)
        (densityPacketAtom a b D 2 D e.2.1).1 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).1
        (densityPacketAtom a b D 2 D e.2.1).2 (densityPacketAtom_mem a b hab.le D 2 D e.2.1).2
        (fun _ : Unit => v) (fun _ _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x))
        () hv (fun _ => (finePairTimeFieldValue_abs e.1 _).le)
      convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, highPacketSlope,
        highPacketIntercept, localDensityReset] <;> ring
    · have h := finePairDensityReset_mem_interval a b ha hab _ _
        (finePairPacketIntercept_mem a b hab.le M q e) (fineModulationNode_bound e.2.1.2)
        (fun _ : Unit => v) (fun _ => finePairTimeFieldValue e.1 (highLocalCoordinates d k j x)) () hv
        (finePairTimeFieldValue_abs e.1 _).le
      convert h using 1 <;> dsimp [finePairRowSlope, finePairRowIntercept, finePairPacketSlope,
        finePairPacketIntercept, finePairDensityReset, finePairDensityAtom] <;> ring
  · exact h_finePairRow_reset_interval
  have h_finePairRowVector_measurable (i : FinePairRowTag) (γ : HighFrameIndex d D) : Measurable (fun e => finePairRowVector d D M q Cfr i e γ) := by
    cases i
    · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
        (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
    · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
        (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
    · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
        (highResponseMarkAtom Cfr q h.2).2 γ)).comp measurable_snd
  · exact h_finePairRowVector_measurable
  have h_finePairRowTime_measurable (i : FinePairRowTag) : Measurable (finePairRowTime d D M q i) := by
    cases i
    · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
        (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd
    · exact (measurable_of_countable (fun h : HighPacketMarkIndex (HighFrameIndex d D) D 2 D q =>
        (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd
    · exact (measurable_of_countable (fun h : FinePairPacketIndex (HighFrameIndex d D) M q =>
        (highResponseMarkAtom 0 q h.2).1)).comp measurable_snd
  · exact h_finePairRowTime_measurable
  have h_finePairRowVector_ball (i : FinePairRowTag) (e : FinePairRowMark d D M q i) : (∑ γ, |finePairRowVector d D M q Cfr i e γ|) ≤ Cfr⁻¹ := by
    cases i <;> exact covarianceAtom_mem_ball Cfr hCf _ _ _ _
  · exact h_finePairRowVector_ball
  have h_finePairRowTime_unit (i : FinePairRowTag) (e : FinePairRowMark d D M q i) : finePairRowTime d D M q i e ∈ Icc (0 : ℝ) 1 := by
    cases i <;> exact responseNode_mem_unit q _
  · exact h_finePairRowTime_unit
end NearlyMinimax
