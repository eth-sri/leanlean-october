module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Kernel.Composition.WithDensity
public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HighResponseRemainder
public import NearlyMinimax.LowMixtureLaw

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax

-- ============================================================================
-- 1. Fair Cell Signs, Finite Sigma Borel Spaces, Frame Norms, and Torus Geometry
-- ============================================================================

section FoundationsAndGeometry
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def fairSignValue (b : Fin 2) : ℝ := if b = 0 then 1 else -1

def fairSignLaw : Measure (Fin 2) :=
  ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 0 + ENNReal.ofReal (1 / 2 : ℝ) • Measure.dirac 1

instance fairSignLaw_probability : IsProbabilityMeasure fairSignLaw := by
  constructor
  change fairSignLaw Set.univ = 1
  simp only [fairSignLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

private lemma fairSign_integral (f : Fin 2 → ℝ) :
    (∫ b, f b ∂fairSignLaw) = (f 0 + f 1) / 2 := by
  unfold fairSignLaw
  rw [integral_add_measure
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)
    ((integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]; norm_num; ring

theorem fairSignValue_abs (b : Fin 2) : |fairSignValue b| = 1 := by
  fin_cases b <;> norm_num [fairSignValue]

private lemma fairSign_power_moment (k : ℕ) :
    (∫ b, fairSignValue b ^ k ∂fairSignLaw) = if Even k then 1 else 0 := by
  rw [fairSign_integral]; simp only [fairSignValue]; norm_num
  by_cases h : Even k
  · simp [h, h.neg_one_pow]
  · simp [h, (Nat.not_even_iff_odd.mp h).neg_one_pow]

def cellSignLaw (I : Type*) [Fintype I] : Measure (I → Fin 2) := Measure.pi fun _ => fairSignLaw

instance cellSignLaw_probability (I : Type*) [Fintype I] : IsProbabilityMeasure (cellSignLaw I) := by
  unfold cellSignLaw; infer_instance

theorem cellSign_covariance {I : Type*} [Fintype I] [DecidableEq I] (i j : I) :
    (∫ b, fairSignValue (b i) * fairSignValue (b j) ∂cellSignLaw I) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst hij
    have hsq (b : Fin 2) : fairSignValue b ^ 2 = 1 := by fin_cases b <;> norm_num [fairSignValue]
    simp [← pow_two, hsq]
  · have hi : IndepFun (fun b : I → Fin 2 => b i) (fun b : I → Fin 2 => b j) (cellSignLaw I) :=
      (iIndepFun_pi fun _ => measurable_id.aemeasurable).indepFun hij
    rw [hi.integral_fun_comp_mul_comp (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable Measurable.of_discrete.aestronglyMeasurable
      Measurable.of_discrete.aestronglyMeasurable]
    have hm (l : I) : (∫ b, fairSignValue (b l) ∂cellSignLaw I) = 0 := by
      change (∫ b, fairSignValue (b l) ∂Measure.pi fun _ : I => fairSignLaw) = 0
      rw [integral_comp_eval (μ := fun _ : I => fairSignLaw) (f := fairSignValue) (i := l) (by fun_prop),
        fairSign_integral]
      norm_num [fairSignValue]
    simp [hm, hij]

theorem cellSign_product_moment {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (p : J → I) :
    (∫ b, ∏ j, fairSignValue (b (p j)) ∂cellSignLaw I) =
      if ∀ i, Even ((Finset.univ.filter fun j => p j = i).card) then (1 : ℝ) else 0 := by
  classical
  simp_rw [show ∀ b : I → Fin 2, (∏ j, fairSignValue (b (p j))) =
      ∏ i, fairSignValue (b i) ^ (Finset.univ.filter fun j => p j = i).card from fun b => by
    rw [← Finset.prod_fiberwise_of_maps_to' (s := Finset.univ) (t := Finset.univ)
      (g := p) (fun _ _ => Finset.mem_univ _) (fun i => fairSignValue (b i))]
    simp only [Finset.prod_const, smul_eq_mul]]
  change (∫ b, ∏ i, fairSignValue (b i) ^ (Finset.univ.filter fun j => p j = i).card
    ∂Measure.pi fun _ : I => fairSignLaw) = _
  rw [integral_fintype_prod_eq_prod fun i b => fairSignValue b ^ (Finset.univ.filter fun j => p j = i).card]
  simp_rw [fairSign_power_moment]; rw [Fintype.prod_boole]

theorem measurable_sigma_mk_actual {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] (i : ι) : Measurable (Sigma.mk i : E i → Sigma E) :=
  Measurable.of_le_map (iInf_le _ i)

theorem measurable_sigma_of_fibers {ι : Type*} {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] {X : Type*} [MeasurableSpace X]
    (f : Sigma E → X) (hf : ∀ i, Measurable fun e : E i => f ⟨i, e⟩) : Measurable f := by
  apply Measurable.of_le_map
  change _ ≤ (⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i)).map f
  rw [MeasurableSpace.map_iInf]
  exact le_iInf fun i => by rw [MeasurableSpace.map_comp]; exact (hf i).le_map

theorem sigma_borelSpace_actual {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] :
    BorelSpace (Sigma E) := by
  constructor
  refine le_antisymm (fun s hs => ?_) (MeasurableSpace.generateFrom_le fun s hs => ?_)
  · have himage (i : ι) : MeasurableSet[borel (Sigma E)] (Sigma.mk i '' (Sigma.mk i ⁻¹' s)) := by
      letI : MeasurableSpace (Sigma E) := borel (Sigma E)
      letI : BorelSpace (Sigma E) := ⟨rfl⟩
      exact Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image.mpr
        (hs.preimage (measurable_sigma_mk_actual i))
    rw [show s = ⋃ i : ι, Sigma.mk i '' (Sigma.mk i ⁻¹' s) by
      ext z; exact ⟨fun hz => mem_iUnion.mpr ⟨z.1, ⟨z.2, hz, Sigma.eta z⟩⟩,
        fun hz => by rcases mem_iUnion.mp hz with ⟨i, e, he, rfl⟩; exact he⟩]
    exact MeasurableSet.iUnion himage
  · change MeasurableSet[⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i)] s
    exact MeasurableSpace.measurableSet_iInf.mpr fun i => (hs.preimage continuous_sigmaMk).measurableSet

theorem sigma_standardBorel_actual {ι : Type*} [Countable ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] : StandardBorelSpace (Sigma E) := by
  letI : ∀ i, TopologicalSpace (E i) := fun i => (upgradeStandardBorel (E i)).toTopologicalSpace
  letI : ∀ i, BorelSpace (E i) := fun i => (upgradeStandardBorel (E i)).toBorelSpace
  letI : ∀ i, PolishSpace (E i) := fun i => (upgradeStandardBorel (E i)).toPolishSpace
  letI : BorelSpace (Sigma E) := sigma_borelSpace_actual
  infer_instance

section FrameAndWindows
attribute [local instance] Classical.propDecidable

def highWindowHolderConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 : ℝ) ^ d * (((d + C.order).choose d : ℝ) + 2)

theorem highWindowHolderConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by unfold highWindowHolderConstant; positivity

theorem highFrameField_original_model_bounds {d : ℕ} (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_model_bounds C
  refine ⟨Cfr, hCfr, fun k hk0 hk cf hcf P hP => ?_⟩
  letI := hk0
  obtain ⟨hv, hs, hm⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, fun U => ?_⟩
  convert holderNorm_of_global_mixed_bounds_binomial U _ C.order C.alpha
    ((2 : ℝ) ^ d * cf) (2 * ((2 : ℝ) ^ d * cf)) (by positivity) (by positivity) hs hm using 1
  congr 1; unfold highWindowHolderConstant; ring

theorem highFrame_ternary_amplitude_guards {d : ℕ} {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ (2 : ℝ) ^ d * η ≤ Q.ρ / 2 := by
  refine ⟨min (Real.sqrt Q.ρ) (Q.ρ / (2 * (2 : ℝ) ^ d)),
    lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity)), fun η hη hηU => ?_⟩
  have h1 := hηU.trans (min_le_left _ _)
  have h2 := (le_div_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ d)).mp (hηU.trans (min_le_right _ _))
  exact ⟨by nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ], by nlinarith⟩

theorem frameCoefficientL1_sum_monomial_le {d : ℕ} {I : Type*} [Fintype I]
    (e : I → Fin d →₀ ℕ) (c : I → ℝ) :
    frameCoefficientL1 (∑ i, MvPolynomial.monomial (e i) (c i)) ≤ ∑ i, |c i| := by
  let P : MvPolynomial (Fin d) ℝ := ∑ i, MvPolynomial.monomial (e i) (c i)
  change (∑ β ∈ P.support, |P.coeff β|) ≤ _
  refine ((Finset.sum_le_sum fun β _ => by
      change |(∑ i, MvPolynomial.monomial (e i) (c i)).coeff β| ≤ _
      rw [MvPolynomial.coeff_sum]
      simpa only [Real.norm_eq_abs] using norm_sum_le Finset.univ fun i =>
        (MvPolynomial.monomial (e i) (c i)).coeff β).trans_eq Finset.sum_comm).trans
    (Finset.sum_le_sum fun i _ => ?_)
  simp only [MvPolynomial.coeff_monomial, apply_ite abs, abs_zero]
  rw [Finset.sum_ite_eq]; split_ifs <;> [exact le_rfl; exact abs_nonneg _]

def highFramePolynomial {d D : ℕ} (c : HighFrameIndex d D → ℝ) : MvPolynomial (Fin d) ℝ :=
  ∑ γ, MvPolynomial.monomial (polynomialBoxExponent γ.val) (c γ)

theorem highFramePolynomial_coefficientL1_le {d D : ℕ} (c : HighFrameIndex d D → ℝ) :
    frameCoefficientL1 (highFramePolynomial c) ≤ ∑ γ, |c γ| :=
  frameCoefficientL1_sum_monomial_le _ _

theorem highFramePolynomial_scaled_eval {d D : ℕ} (c : HighFrameIndex d D → ℝ) (x : Covariate d) :
    MvPolynomial.eval x (frameScaledPolynomial (highFramePolynomial c)) =
      ∑ γ, c γ * highFrameFeature x γ := by
  rw [frameScaledPolynomial_eval]
  simp only [highFramePolynomial, map_sum, MvPolynomial.eval_monomial, highFrameFeature]
  refine Finset.sum_congr rfl fun γ _ => ?_
  congr 1; rw [Finsupp.prod_fintype _ _ fun _ => by simp]
  simp only [polynomial_box_exponent_apply]

private lemma frameCoefficientL1_mul {d : ℕ} (P Q : MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (P * Q) ≤ frameCoefficientL1 P * frameCoefficientL1 Q := by
  have hP := P.as_sum.trans (Finset.sum_coe_sort P.support fun β => monomial β (P.coeff β)).symm
  have hQ := Q.as_sum.trans (Finset.sum_coe_sort Q.support fun β => monomial β (Q.coeff β)).symm
  have hprod : P * Q = ∑ β : P.support × Q.support,
      monomial (β.1.val + β.2.val) (P.coeff β.1.val * Q.coeff β.2.val) := by
    rw [congrArg₂ (· * ·) hP hQ]
    simp_rw [Finset.sum_mul, Finset.mul_sum, monomial_mul_monomial]; rw [Fintype.sum_prod_type]
  rw [hprod]
  refine (frameCoefficientL1_sum_monomial_le _ _).trans_eq ?_
  simp_rw [Fintype.sum_prod_type, abs_mul]
  calc
    _ = ∑ β : P.support, |P.coeff β.val| * frameCoefficientL1 Q := Finset.sum_congr rfl fun β _ => by
      rw [← Finset.mul_sum Finset.univ (fun γ : Q.support => |Q.coeff γ.val|) |P.coeff β.val|,
        Finset.sum_coe_sort Q.support fun γ => |Q.coeff γ|]; rfl
    _ = frameCoefficientL1 P * frameCoefficientL1 Q := by
      rw [← Finset.sum_mul Finset.univ (fun β : P.support => |P.coeff β.val|) (frameCoefficientL1 Q),
        Finset.sum_coe_sort P.support fun β => |P.coeff β|]; rfl

theorem frameCoefficientL1_one {d : ℕ} :
    frameCoefficientL1 (1 : MvPolynomial (Fin d) ℝ) = 1 := by
  simp [frameCoefficientL1, MvPolynomial.support_one]

theorem frameCoefficientL1_prod {d : ℕ} {I : Type*} (s : Finset I)
    (P : I → MvPolynomial (Fin d) ℝ) :
    frameCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, frameCoefficientL1 (P i) := by
  induction s using Finset.induction_on with
  | empty => simp [frameCoefficientL1_one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (frameCoefficientL1_mul _ _).trans (mul_le_mul_of_nonneg_left ih (frameCoefficientL1_nonneg _))

theorem highFrameCoefficients_sum_abs_le {d D : ℕ} (P : MvPolynomial (Fin d) ℝ) :
    (∑ γ : HighFrameIndex d D, |highFrameCoefficients P γ|) ≤ frameCoefficientL1 P := by
  let e : HighFrameIndex d D → Fin d →₀ ℕ := fun γ => polynomialBoxExponent γ.val
  rw [show (∑ γ : HighFrameIndex d D, |highFrameCoefficients P γ|) =
      ∑ β ∈ Finset.univ.image e, |P.coeff β| by
    rw [Finset.sum_image fun _ _ _ _ h => Subtype.ext (polynomial_box_exponent_injective h)]; rfl]
  rw [← Finset.sum_subset (s₁ := Finset.univ.image e ∩ P.support) (s₂ := Finset.univ.image e)
    Finset.inter_subset_left fun β hβ hnot => by
      simp [MvPolynomial.notMem_support_iff.mp fun hm => hnot (Finset.mem_inter.mpr ⟨hβ, hm⟩)]]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right fun _ _ _ => abs_nonneg _

def highTorusPatch (d k : ℕ) (j : HighWindowLabels d k) : Set (Covariate d) :=
  {x | ∃ z : Fin d → ℤ, (∀ r, (z r : ZMod k) = j r) ∧ ∀ r, |(k : ℝ) * x r - z r| < 1}

theorem highTorusPatch_measurableSet (d k : ℕ) (j : HighWindowLabels d k) :
    MeasurableSet (highTorusPatch d k j) := by
  unfold highTorusPatch; simp_rw [setOf_exists]
  refine MeasurableSet.iUnion fun z => ?_
  by_cases hz : ∀ r, (z r : ZMod k) = j r
  · rw [show {x : Covariate d | (∀ r, (z r : ZMod k) = j r) ∧ ∀ r, |(k : ℝ) * x r - z r| < 1} =
        {x : Covariate d | ∀ r, |(k : ℝ) * x r - z r| < 1} by ext; exact and_iff_right hz]
    simp_rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun _ => (isOpen_lt (by fun_prop) continuous_const).measurableSet
  · simp [hz]

private def highPatchCoordinate (k : ℕ) (j : ZMod k) : Set ℝ :=
  if j = 0 then Icc 0 (1 / (k : ℝ)) ∪ Icc (1 - 1 / (k : ℝ)) 1 else
    Icc (((j.val : ℝ) - 1) / k) (((j.val : ℝ) + 1) / k)

theorem highTorusPatch_volume_le (d k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (j : HighWindowLabels d k) :
    cubeVolume d (highTorusPatch d k j) ≤ ENNReal.ofReal (2 / (k : ℝ)) ^ d := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsub : highTorusPatch d k j ∩ unitCube d ⊆ Set.pi Set.univ fun r => highPatchCoordinate k (j r) := by
    rintro x ⟨⟨z, hz, hclose⟩, hxu⟩ r -
    have hkv : ((j r).val : ℤ) < k := by exact_mod_cast ZMod.val_lt (j r)
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_iff k (z r) (j r)).mp (hz r)
    have hcl := abs_lt.mp (hclose r)
    have hxr := hxu r
    have hzz : 0 ≤ z r ∧ z r ≤ (k : ℤ) := by
      have hzL : (-1 : ℤ) < z r := by exact_mod_cast (by nlinarith [mul_nonneg hkR.le hxr.1] : (-1 : ℝ) < z r)
      have hzU : z r < (k : ℤ) + 1 := by exact_mod_cast (by nlinarith [mul_le_mul_of_nonneg_left hxr.2 hkR.le] : (z r : ℝ) < k + 1)
      omega
    have hqs : q = 0 ∨ q = 1 := by
      have hj0 : (0 : ℤ) ≤ (j r).val := Int.natCast_nonneg _
      have hkZ : (0 : ℤ) < k := by exact_mod_cast (by omega : 0 < k)
      have hqL : 0 ≤ q := by
        by_contra h
        have hneg : q ≤ -1 := by omega
        nlinarith
      have hqU : q ≤ 1 := by
        by_contra h
        have hbig : 2 ≤ q := by omega
        nlinarith
      omega
    rcases hqs with hq0 | hq1
    · have hzvalR : (z r : ℝ) = (j r).val := by exact_mod_cast (by simpa only [hq0, mul_zero, add_zero] using hq : z r = ((j r).val : ℤ))
      change x r ∈ highPatchCoordinate k (j r); unfold highPatchCoordinate; split_ifs with hj
      · rw [hj] at hzvalR; simp only [ZMod.val_zero, Nat.cast_zero] at hzvalR
        exact Or.inl ⟨hxr.1, (le_div_iff₀ hkR).mpr (by nlinarith)⟩
      · exact ⟨(div_le_iff₀ hkR).mpr (by nlinarith), (le_div_iff₀ hkR).mpr (by nlinarith)⟩
    · have hjval : (j r).val = 0 := by rw [hq1, mul_one] at hq; omega
      have hj : j r = 0 := by have hv := ZMod.natCast_zmod_val (j r); rw [hjval, Nat.cast_zero] at hv; exact hv.symm
      have hzR : (z r : ℝ) = k := by
        exact_mod_cast (by simp only [hjval, Nat.cast_zero, hq1, mul_one, zero_add] at hq; exact hq : z r = (k : ℤ))
      change x r ∈ highPatchCoordinate k (j r); unfold highPatchCoordinate; rw [ite_eq_left hj]
      refine Or.inr ⟨?_, hxr.2⟩
      have hr : ((k : ℝ) - 1) / k ≤ x r := (div_le_iff₀ hkR).mpr (by nlinarith)
      convert hr using 1; field_simp
  have hcoord (m : ZMod k) : volume (highPatchCoordinate k m) ≤ ENNReal.ofReal (2 / (k : ℝ)) := by
    unfold highPatchCoordinate; split_ifs
    · refine (measure_union_le _ _).trans_eq ?_
      rw [Real.volume_Icc, Real.volume_Icc, show (1 : ℝ) / k - 0 = 1 / k by ring,
        show (1 : ℝ) - (1 - 1 / k) = 1 / k by ring, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1; ring
    · rw [Real.volume_Icc]; apply ENNReal.ofReal_le_ofReal; ring_nf; exact le_rfl
  rw [cubeVolume, Measure.restrict_apply (highTorusPatch_measurableSet d k j)]
  exact (measure_mono hsub).trans ((volume_pi_pi _).trans_le
    ((Finset.prod_le_prod fun r _ => hcoord (j r)).trans_eq (by simp)))

def highNeighborLabels (d k : ℕ) (j : HighWindowLabels d k) : Finset (HighWindowLabels d k) :=
  Fintype.piFinset fun r => {j r - 1, j r, j r + 1}

theorem highNeighborLabels_card_le (d k : ℕ) [NeZero k] (j : HighWindowLabels d k) :
    (highNeighborLabels d k j).card ≤ 3 ^ d := by
  rw [highNeighborLabels, Fintype.card_piFinset]
  exact (Finset.prod_le_prod' fun _ _ => Finset.card_le_three).trans_eq (by simp)

theorem highNeighborLabels_self_mem (d k : ℕ) (j : HighWindowLabels d k) :
    j ∈ highNeighborLabels d k j := Fintype.mem_piFinset.mpr fun _ => by simp

theorem highNeighborLabels_symmetric (d k : ℕ) (j l : HighWindowLabels d k)
    (h : l ∈ highNeighborLabels d k j) : j ∈ highNeighborLabels d k l := by
  refine Fintype.mem_piFinset.mpr fun r => ?_
  have hr := Fintype.mem_piFinset.mp h r
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢
  rcases hr with hr | hr | hr
  · exact Or.inr (Or.inr (by rw [hr]; ring))
  · exact Or.inr (Or.inl hr.symm)
  · exact Or.inl (by rw [hr]; ring)

theorem highTorusPatch_disjoint_of_not_neighbor (d k : ℕ) [NeZero k]
    (j l : HighWindowLabels d k) (h : l ∉ highNeighborLabels d k j) :
    Disjoint (highTorusPatch d k j) (highTorusPatch d k l) :=
  Set.disjoint_left.mpr fun x ⟨z, hz, hc⟩ ⟨q, hq, hd⟩ => h <| Fintype.mem_piFinset.mpr fun r => by
    have hdiff := (abs_sub_le (q r : ℝ) ((k : ℝ) * x r) (z r : ℝ)).trans_lt
      (by rw [abs_sub_comm] at *; linarith [hc r, hd r] : |(q r : ℝ) - (k : ℝ) * x r| + |(k : ℝ) * x r - z r| < 2)
    have hh := abs_lt.mp hdiff
    have hL : (-2 : ℤ) < q r - z r := by exact_mod_cast hh.1
    have hU : q r - z r < (2 : ℤ) := by exact_mod_cast hh.2
    have hcases : q r = z r - 1 ∨ q r = z r ∨ q r = z r + 1 := by omega
    rcases hcases with he | he | he
    · rw [show l r = j r - 1 by rw [← hq r, he, Int.cast_sub, ← hz r]; simp]; simp
    · rw [show l r = j r by rw [← hq r, he, hz r]]; simp
    · rw [show l r = j r + 1 by rw [← hq r, he, Int.cast_add, ← hz r]; simp]; simp

theorem highPeriodicTensor_supported_patch (d k : ℕ) (j : HighWindowLabels d k) :
    support (highPeriodicTensor d k j) ⊆ highTorusPatch d k j := fun x hx => by
  obtain ⟨z, hz, hclose⟩ := highPeriodicTensor_support_lift d k j x hx
  exact ⟨z, hz, fun r => (hclose r).trans (by norm_num)⟩

abbrev HighRawState (d k D : ℕ) :=
  (Covariate d → ℝ) × (HighWindowLabels d k → (HighFrameIndex d D → ℝ))

end FrameAndWindows

section LocalScores
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

def highDensityResponseAction (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (b : E → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ e, weights e * b e * responseMatrixAction q C (A e) c Φ

omit [DecidableEq ι] in
theorem high_response_product_normalized {n : ℕ} (a V η : ℝ) (ha : a ≠ 0)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) :
    ∑ y : Fin n → Fin 3, highResponseProduct a V η g w φ c y = 1 := by
  unfold highResponseProduct; rw [← Fintype.prod_sum]; simp [ternary_normalized a _ V ha]

omit [DecidableEq ι] in
theorem high_response_variance_term_sum_zero {n : ℕ} (a V η : ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (i : Fin n) :
    ∑ y : Fin n → Fin 3, highResponseVarianceTerm a V η g w φ c y i = 0 := by
  simpa only [highResponseVarianceTerm, patchVarianceTerm, zero_mul, add_zero] using
    patch_variance_term_sum_zero n a V 0 (coefficientRegression η g w φ c) (fun _ => 0) 0 i

def highResponsePacketCost (C : ℝ) (weights : E → ℝ) (A : E → ι → ι → ℝ) : ℝ :=
  ∑ e, |weights e| * (2 * C ^ 2 * ∑ k, ∑ l, |A e k l|)

def highLocalDerivativeConstant (q : ℕ) (a ρ : ℝ) : ℝ :=
  (∑ j : Fin (2 * q + 2), |responseWeight q j|) * (4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2))

theorem finite_density_product_abs_bound {n : ℕ} (p : Fin n → ℝ) (pPlus : ℝ)
    (_hpPlus : 0 ≤ pPlus) (hp : ∀ i, |p i| ≤ pPlus) :
    |∏ i, p i| ≤ pPlus ^ n := by
  rw [Finset.abs_prod]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (p i)) fun i _ => hp i

omit [DecidableEq ι] in
theorem high_response_variance_term_abs_bound {n : ℕ} (a V η : ℝ) (ha : 0 < a)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) (i : Fin n) :
    |highResponseVarianceTerm a V η g w φ c y i| ≤ 1 / a ^ 2 := by
  have hprod : |∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (g := fun _ => (1 : ℝ)) (fun _ _ => abs_nonneg _) fun l _ => by
      rw [abs_of_nonneg (hp l (y l))]; exact ternary_mass_le_one a _ V ha.ne' (hp l) (y l)).trans_eq Finset.prod_const_one
  unfold highResponseVarianceTerm; rw [abs_mul]
  exact (mul_le_mul (ternary_variance_derivative_abs_bound a ha (y i)) hprod
    (abs_nonneg _) (by positivity : 0 ≤ 1 / a ^ 2)).trans_eq (mul_one _)

theorem high_density_response_product_abs_bound {n : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ pPlus : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (weights : E → ℝ) (A : E → ι → ι → ℝ) (pReset : E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (y : Fin n → Fin 3) :
    |highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
      (fun c => highResponseProduct a V η g w φ c y)| ≤
      pPlus ^ n * highResponsePacketCost C weights A *
        (highLocalDerivativeConstant q a ρ * (n : ℝ) ^ 2 * η ^ 2) := by
  unfold highDensityResponseAction
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    ((Finset.sum_le_sum (g := fun e => (|weights e| * pPlus ^ n) *
        ((2 * C ^ 2 * ∑ k, ∑ l, |A e k l|) * (highLocalDerivativeConstant q a ρ * (n : ℝ) ^ 2 * η ^ 2)))
      fun e _ => ?_).trans_eq ?_)
  · rw [abs_mul, abs_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (finite_density_product_abs_bound (pReset e) pPlus hpPlus (hReset e)) (abs_nonneg _))
      ((high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ (A e) g w φ c y hc hg hw hφ hp).trans_eq
        (by unfold highLocalDerivativeConstant; ring))
      (abs_nonneg _) (by positivity)
  · unfold highResponsePacketCost; rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring

end LocalScores
end FoundationsAndGeometry

-- ============================================================================
-- 2. Reference Balancing, High Observation Kernels, Mass Tilts, and History Evolution
-- ============================================================================

section BalancingAndExperiments
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section AbsoluteMarkAndBalancing
variable {E : Type*} [MeasurableSpace E]

def signedMarkMass (μ : Measure E) (w : E → ℝ) : ℝ := ∫ e, |w e| ∂μ

def absoluteMarkLaw (μ : Measure E) (w : E → ℝ) : Measure E :=
  μ.withDensity fun e => ENNReal.ofReal (|w e| / signedMarkMass μ w)

def absoluteActivation (μ : Measure E) (w : E → ℝ) (e : E) : ℝ :=
  signedMarkMass μ w * (w e / |w e|)

theorem signedMarkMass_nonneg (μ : Measure E) (w : E → ℝ) :
    0 ≤ signedMarkMass μ w := integral_nonneg fun _ => abs_nonneg _

theorem signedMarkMass_eq_variation (μ : Measure E) (w : E → ℝ) (hw : Integrable w μ) :
    signedMarkMass μ w = ((μ.withDensityᵥ w).variation univ).toReal := by
  rw [Measure.variation_withDensityᵥ hw, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ, ← integral_norm_eq_lintegral_enorm hw.aestronglyMeasurable,
    signedMarkMass, Real.norm_eq_abs]

theorem absoluteMarkLaw_probability (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hpos : 0 < signedMarkMass μ w) :
    IsProbabilityMeasure (absoluteMarkLaw μ w) := by
  constructor
  rw [absoluteMarkLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hw.abs.div_const _)
      (Eventually.of_forall fun e => div_nonneg (abs_nonneg (w e)) hpos.le), integral_div]
  change ENNReal.ofReal (signedMarkMass μ w / signedMarkMass μ w) = 1
  simp only [div_self hpos.ne', ENNReal.ofReal_one]

theorem absoluteActivation_measurable (μ : Measure E) (w : E → ℝ) (hw : Measurable w) :
    Measurable (absoluteActivation μ w) := (hw.div hw.abs).const_mul _

theorem absoluteActivation_bound (μ : Measure E) (w : E → ℝ) (e : E) :
    |absoluteActivation μ w e| ≤ signedMarkMass μ w := by
  rw [absoluteActivation, abs_mul, abs_of_nonneg (signedMarkMass_nonneg μ w)]
  have hb : |w e / (|w e|)| ≤ 1 := by
    by_cases he : w e = 0
    · simp [he]
    · rw [abs_div, abs_abs, div_self (abs_ne_zero.mpr he)]
  exact (mul_le_mul_of_nonneg_left hb (signedMarkMass_nonneg μ w)).trans_eq (mul_one _)

theorem absoluteMarkLaw_activation_integral (μ : Measure E) (w : E → ℝ)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) = ∫ e, w e * F e ∂μ := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun e => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul, absoluteActivation]
  by_cases he : w e = 0 <;> [simp [he]; field_simp]

theorem absoluteActivation_centered (μ : Measure E) (w : E → ℝ)
    (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w) (hzero : ∫ e, w e ∂μ = 0) :
    (∫ e, absoluteActivation μ w e ∂absoluteMarkLaw μ w) = 0 := by
  have h := absoluteMarkLaw_activation_integral μ w hmw hpos fun _ => 1
  simp only [mul_one] at h; exact h.trans hzero

theorem absoluteMarkLaw_signed_action (μ : Measure E) (w : E → ℝ)
    (hw : Integrable w μ) (hmw : Measurable w) (hpos : 0 < signedMarkMass μ w)
    (F : E → ℝ) (hF : Measurable F) (M : ℝ) (hbound : ∀ e, ‖F e‖ ≤ M) :
    (∫ e, absoluteActivation μ w e * F e ∂absoluteMarkLaw μ w) = ∫ᵛ e, F e ∂<•(μ.withDensityᵥ w) := by
  rw [absoluteMarkLaw_activation_integral μ w hmw hpos F, signedDensity_integral μ w hw hmw F hF M hbound]

theorem absoluteMarkLaw_integral (μ : Measure E) (w : E → ℝ) (hmw : Measurable w)
    (hpos : 0 < signedMarkMass μ w) (F : E → ℝ) :
    (∫ e, F e ∂absoluteMarkLaw μ w) = (∫ e, |w e| * F e ∂μ) / signedMarkMass μ w := by
  rw [absoluteMarkLaw, integral_withDensity_eq_integral_toReal_smul
    (hmw.abs.div_const _).ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    show (fun e => (ENNReal.ofReal (|w e| / signedMarkMass μ w)).toReal • F e) =
      fun e => |w e| * F e / signedMarkMass μ w from funext fun e => by
        rw [ENNReal.toReal_ofReal (div_nonneg (abs_nonneg (w e)) hpos.le), smul_eq_mul, div_mul_eq_mul_div],
    integral_div]

end AbsoluteMarkAndBalancing

theorem finite_even_odd_sum_zero {I : Type*} [Fintype I]
    (e : Equiv.Perm I) (w f : I → ℝ)
    (hw : ∀ i, w (e i) = w i) (hf : ∀ i, f (e i) = -f i) :
    (∑ i, w i * f i) = 0 := by
  have he : (∑ i, w i * f i) = -(∑ i, w i * f i) :=
    (Fintype.sum_equiv e (fun i => w (e i) * f (e i)) (fun i => w i * f i) fun _ => rfl).symm.trans
      (by simp_rw [hw, hf, mul_neg]; exact Finset.sum_neg_distrib _)
  linarith

section HighPacketAbsolute
variable {Z ι : Type*} [MeasurableSpace Z] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

def highPacketMarkMass (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ) : ℝ :=
  signedMarkMass (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketAbsoluteLaw (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Measure (Z × HighPacketMarkIndex ι m r D q) :=
  absoluteMarkLaw (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

def highPacketActivation (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) : Z × HighPacketMarkIndex ι m r D q → ℝ :=
  absoluteActivation (σ.prod Measure.count) (highPacketMarkWeight a b m r D q C A)

theorem highPacketMarkMass_eq_variation (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ) :
    highPacketMarkMass σ a b m r D q C A =
      ((highPacketSignedMeasure σ a b m r D q C A).variation univ).toReal :=
  signedMarkMass_eq_variation _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost)

theorem highPacketAbsoluteLaw_probability (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    IsProbabilityMeasure (highPacketAbsoluteLaw σ a b m r D q C A) :=
  absoluteMarkLaw_probability _ _ (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) hpos

theorem highPacketActivation_centered (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A) :
    (∫ e, highPacketActivation σ a b m r D q C A e ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  refine absoluteActivation_centered _ _ (highPacketMarkWeight_measurable a b m r D q C A hA) hpos ?_
  have h := highPacketSignedMeasure_zero_mass σ a b m r D q C A hA hcost
  rwa [highPacketSignedMeasure, withDensityᵥ_apply
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) MeasurableSet.univ,
    Measure.restrict_univ] at h

theorem highPacketActivation_bound (σ : Measure Z) (a b : ℝ) (m r D q : ℕ) (C : ℝ)
    (A : Z → ι → ι → ℝ) (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketActivation σ a b m r D q C A e| ≤ highPacketMarkMass σ a b m r D q C A :=
  absoluteActivation_bound _ _ _

def highPacketIntercept (a b : ℝ) (m r D q : ℕ) (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  (densityPacketAtom a b m r D e.2.1).1

def highPacketSlope (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (e : Z × HighPacketMarkIndex ι m r D q) : ℝ :=
  densityMargin a b (highPacketIntercept a b m r D q e) / ((r : ℝ) * b) *
    ∑ l, (densityPacketAtom a b m r D e.2.1).2 l * B e.1 l

theorem highPacketIntercept_measurable (a b : ℝ) (m r D q : ℕ) :
    Measurable (highPacketIntercept (Z := Z) (ι := ι) a b m r D q) :=
  measurable_from_prod_countable_left fun _ => by dsimp [highPacketIntercept]; exact measurable_const

theorem highPacketSlope_measurable (a b : ℝ) (m r D q : ℕ) (B : Z → Fin r → ℝ)
    (hB : ∀ l, Measurable fun ζ => B ζ l) :
    Measurable (highPacketSlope (ι := ι) a b m r D q B) :=
  measurable_from_prod_countable_left fun _ => by
    dsimp [highPacketSlope, highPacketIntercept]
    exact (Finset.measurable_fun_sum _ fun l _ => (hB l).const_mul _).const_mul _

theorem highPacketSlope_bound (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (m r D q : ℕ) (hr : 1 ≤ r) (B : Z → Fin r → ℝ) (hB : ∀ ζ l, |B ζ l| ≤ 1)
    (e : Z × HighPacketMarkIndex ι m r D q) :
    |highPacketSlope a b m r D q B e| ≤ (b - a) / (4 * b) :=
  localDensityReset_slope_bound a b ha hab r hr
    (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom_mem a b hab.le m r D e.2.1).1
    (densityPacketAtom a b m r D e.2.1).2 (densityPacketAtom_mem a b hab.le m r D e.2.1).2
    (fun _ l => B e.1 l) () (hB e.1)

theorem highPacketSlope_integrable (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable fun ζ => B ζ l) (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    Integrable (highPacketSlope a b m r D q B) (highPacketAbsoluteLaw σ a b m r D q C A) := by
  letI := highPacketAbsoluteLaw_probability σ a b m r D q C A hA hcost hpos
  exact (integrable_const ((b - a) / (4 * b))).mono'
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
    (Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e)

theorem highPacketAbsoluteLaw_slope_integral_zero (σ : Measure Z) [IsFiniteMeasure σ]
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (m r D q : ℕ) (hr : 1 ≤ r) (C : ℝ)
    (A : Z → ι → ι → ℝ) (hA : ∀ i j, Measurable fun ζ => A ζ i j)
    (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (B : Z → Fin r → ℝ) (hmB : ∀ l, Measurable fun ζ => B ζ l) (hB : ∀ ζ l, |B ζ l| ≤ 1) :
    (∫ e, highPacketSlope a b m r D q B e ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 := by
  have hi := (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost).abs.mul_bdd
    (highPacketSlope_measurable a b m r D q B hmB).aestronglyMeasurable
    (Eventually.of_forall fun e => by
      simpa only [Real.norm_eq_abs] using highPacketSlope_bound a b ha hab m r D q hr B hB e)
  rw [highPacketAbsoluteLaw, absoluteMarkLaw_integral _ _
    (highPacketMarkWeight_measurable a b m r D q C A hA) hpos, integral_prod _ hi]
  let refl : Equiv.Perm (HighPacketMarkIndex ι m r D q) :=
    Equiv.prodCongr (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun _ : Fin r => Fin.revPerm)) (Equiv.refl _)
  have hsum0 (ζ : Z) : (∑ h : HighPacketMarkIndex ι m r D q,
      |highPacketMarkWeight a b m r D q C A (ζ, h)| * highPacketSlope a b m r D q B (ζ, h)) = 0 :=
    finite_even_odd_sum_zero refl _ _
      (fun h => by
        change |densityPacketPrefactor a b r * exteriorWeight a b (m + r) h.1.1 *
            (∏ l, densityDerivativeWeight D (h.1.2 l).rev) * highResponseMarkWeight C q (A ζ) h.2| = _
        simp only [highPacketMarkWeight, densityPacketWeight, abs_mul, Finset.abs_prod]
        rw [show (∏ l, |densityDerivativeWeight D (h.1.2 l).rev|) = ∏ l, |densityDerivativeWeight D (h.1.2 l)| from
          Finset.prod_congr rfl fun l _ => lobattoDerivativeWeight_abs_reflection ((D - 1) / 2) (h.1.2 l)])
      fun h => by
        change densityMargin a b (exteriorNode a b (m + r) h.1.1) / ((r : ℝ) * b) *
          (∑ l, lobattoNode (derivativeOrder D) (h.1.2 l).rev * B ζ l) = _
        simp_rw [lobattoNode_reflection (derivativeOrder D) (by unfold derivativeOrder; omega)]
        simp only [neg_mul, Finset.sum_neg_distrib, mul_neg]; rfl
  simp only [integral_count, hsum0, integral_zero, zero_div]

end HighPacketAbsolute

def highCenterRadius {d : ℕ} (C : ModelConstants d) : ℝ :=
  min (1 - C.densityLower) (C.densityUpper - 1) / 2

def highCenterMix {d : ℕ} (C : ModelConstants d) : ℝ :=
  highCenterRadius C / (2 * (C.densityUpper - C.densityLower))

theorem highCenterRadius_pos {d : ℕ} (C : ModelConstants d) : 0 < highCenterRadius C :=
  div_pos (lt_min (sub_pos.mpr C.densityLower_lt_one) (sub_pos.mpr C.one_lt_densityUpper)) (by norm_num)

theorem highCenterRadius_le_margins {d : ℕ} (C : ModelConstants d) :
    2 * highCenterRadius C ≤ 1 - C.densityLower ∧ 2 * highCenterRadius C ≤ C.densityUpper - 1 := by
  dsimp [highCenterRadius]
  exact ⟨by linarith [min_le_left (1 - C.densityLower) (C.densityUpper - 1)],
    by linarith [min_le_right (1 - C.densityLower) (C.densityUpper - 1)]⟩

theorem highCenterMix_mem {d : ℕ} (C : ModelConstants d) :
    0 < highCenterMix C ∧ highCenterMix C < 1 := by
  have hgap : 0 < C.densityUpper - C.densityLower := by linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have hm := highCenterRadius_le_margins C
  exact ⟨div_pos (highCenterRadius_pos C) (mul_pos (by norm_num) hgap),
    (div_lt_iff₀ (mul_pos (by norm_num) hgap)).mpr (by nlinarith)⟩

def balancedResetAnchor (δ q : ℝ) : ℝ := (1 - δ * q) / (1 - δ)

private lemma balancedResetAnchor_identity (δ q : ℝ) (hδ : δ < 1) :
    δ * q + (1 - δ) * balancedResetAnchor δ q = 1 := by
  unfold balancedResetAnchor; field_simp [(sub_pos.mpr hδ).ne']; ring

theorem sourceBalancedResetAnchor_mem {d : ℕ} (C : ModelConstants d)
    (M q : ℝ) (hM : 0 < M) (hmargin : 1 / M ≤ highCenterRadius C)
    (hq : q ∈ Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M)) :
    balancedResetAnchor (highCenterMix C) q ∈ Icc (C.densityLower + 1 / M) (C.densityUpper - 1 / M) := by
  let a := C.densityLower + 1 / M
  let b := C.densityUpper - 1 / M
  let δ := highCenterMix C
  let r := highCenterRadius C
  let W := C.densityUpper - C.densityLower
  have hr := highCenterRadius_pos C
  have hδ := highCenterMix_mem C
  have hm := highCenterRadius_le_margins C
  have hg : C.densityUpper - C.densityLower ≠ 0 := by linarith [C.densityLower_lt_one, C.one_lt_densityUpper]
  have hi := balancedResetAnchor_identity δ q hδ.2
  have hW : b - a ≤ W := by dsimp [a, b, W]; linarith [one_div_pos.mpr hM]
  have hδW : δ * W ≤ r / 2 := by dsimp [δ, r, W, highCenterMix]; field_simp; linarith
  have hl : δ * (q - a) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.2]) hδ.1.le
  have hu : δ * (b - q) ≤ δ * W := mul_le_mul_of_nonneg_left (by linarith [hq.1]) hδ.1.le
  have ha : a + r ≤ 1 := by dsimp [a, r]; linarith [hm.1]
  have hb : 1 + r ≤ b := by dsimp [b, r]; linarith [hm.2]
  have hd : 0 < 1 - δ := sub_pos.mpr hδ.2
  have hm1 : r / 2 ≤ (1 - δ) * (balancedResetAnchor δ q - a) := by nlinarith
  have hm2 : r / 2 ≤ (1 - δ) * (b - balancedResetAnchor δ q) := by nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

def balancedReferenceLaw {E : Type*} [MeasurableSpace E] (μ : Measure E) (δ : ℝ) : Measure (E ⊕ Unit) :=
  ENNReal.ofReal δ • μ.map Sum.inl + ENNReal.ofReal (1 - δ) • Measure.dirac (Sum.inr ())

theorem balancedReferenceLaw_probability {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    IsProbabilityMeasure (balancedReferenceLaw μ δ) := by
  constructor
  rw [balancedReferenceLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ]
  simp only [preimage_univ, measure_univ, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hδ0 (sub_nonneg.mpr hδ1)]; simp

def balancedIntercept {E : Type*} (B : E → ℝ) (δ q : ℝ) : E ⊕ Unit → ℝ :=
  Sum.elim B fun _ => balancedResetAnchor δ q

def balancedSlope {E : Type*} (A : E → ℝ) : E ⊕ Unit → ℝ := Sum.elim A fun _ => 0

def balancedActivation {E : Type*} (w : E → ℝ) (δ : ℝ) : E ⊕ Unit → ℝ :=
  Sum.elim (fun e => w e / δ) fun _ => 0

theorem balancedReferenceLaw_integrable {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    Integrable F (balancedReferenceLaw μ δ) :=
  integrable_add_measure.mpr
    ⟨((integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi).smul_measure ENNReal.ofReal_ne_top,
     (integrable_dirac' hF.stronglyMeasurable (by finiteness)).smul_measure ENNReal.ofReal_ne_top⟩

private lemma balancedReferenceLaw_integral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (F : E ⊕ Unit → ℝ) (hF : Measurable F) (hFi : Integrable (fun e => F (Sum.inl e)) μ) :
    ∫ e, F e ∂balancedReferenceLaw μ δ =
      δ * (∫ e, F (Sum.inl e) ∂μ) + (1 - δ) * F (Sum.inr ()) := by
  have hm := (integrable_map_measure hF.aestronglyMeasurable measurable_inl.aemeasurable).mpr hFi
  have hd : Integrable F (Measure.dirac (Sum.inr ())) := integrable_dirac' hF.stronglyMeasurable (by finiteness)
  rw [balancedReferenceLaw, integral_add_measure
    (hm.smul_measure ENNReal.ofReal_ne_top) (hd.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_inl.aemeasurable hF.aestronglyMeasurable,
    integral_dirac' _ _ hF.stronglyMeasurable,
    ENNReal.toReal_ofReal hδ0, ENNReal.toReal_ofReal (sub_nonneg.mpr hδ1)]; rfl

theorem balancedIntercept_measurable {E : Type*} [MeasurableSpace E]
    (B : E → ℝ) (hB : Measurable B) (δ q : ℝ) : Measurable (balancedIntercept B δ q) :=
  hB.sumElim measurable_const

theorem balancedSlope_measurable {E : Type*} [MeasurableSpace E]
    (A : E → ℝ) (hA : Measurable A) : Measurable (balancedSlope A) :=
  hA.sumElim measurable_const

theorem balancedActivation_measurable {E : Type*} [MeasurableSpace E]
    (w : E → ℝ) (hw : Measurable w) (δ : ℝ) : Measurable (balancedActivation w δ) :=
  (hw.div_const δ).sumElim measurable_const

theorem balancedIntercept_integral_one {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (B : E → ℝ) (hB : Measurable B) (hBi : Integrable B μ) :
    ∫ e, balancedIntercept B δ (∫ e, B e ∂μ) e ∂balancedReferenceLaw μ δ = 1 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1.le _ (balancedIntercept_measurable B hB _ _) hBi]
  exact balancedResetAnchor_identity δ _ hδ1

theorem balancedSlope_integral_zero {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (A : E → ℝ) (hA : Measurable A) (hAi : Integrable A μ) (hcenter : ∫ e, A e ∂μ = 0) :
    ∫ e, balancedSlope A e ∂balancedReferenceLaw μ δ = 0 := by
  rw [balancedReferenceLaw_integral μ δ hδ0 hδ1 _ (balancedSlope_measurable A hA) hAi]
  simp only [balancedSlope, Sum.elim_inl, Sum.elim_inr, hcenter, mul_zero, add_zero]

theorem balancedActivation_bound {E : Type*} (w : E → ℝ) (δ W : ℝ) (hδ : 0 < δ) (hW0 : 0 ≤ W)
    (hW : ∀ e, |w e| ≤ W) (e : E ⊕ Unit) : |balancedActivation w δ e| ≤ W / δ := by
  cases e with
  | inl e => change |w e / δ| ≤ _; rw [abs_div, abs_of_pos hδ]; exact div_le_div_of_nonneg_right (hW e) hδ.le
  | inr _ => simpa only [balancedActivation, Sum.elim_inr, abs_zero] using div_nonneg hW0 hδ.le

theorem balancedActivation_integral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (w : E → ℝ) (hw : Measurable w) (F : E ⊕ Unit → ℝ) (hF : Measurable F)
    (hWF : Integrable (fun e => w e * F (Sum.inl e)) μ) :
    ∫ e, balancedActivation w δ e * F e ∂balancedReferenceLaw μ δ =
      ∫ e, w e * F (Sum.inl e) ∂μ := by
  have hFi : Integrable (fun e => balancedActivation w δ (Sum.inl e) * F (Sum.inl e)) μ := by
    convert hWF.div_const δ using 1; funext e; change w e / δ * F (Sum.inl e) = _; ring
  rw [balancedReferenceLaw_integral μ δ hδ.le hδ1 (fun e => balancedActivation w δ e * F e)
    ((balancedActivation_measurable w hw δ).mul hF) hFi]
  simp only [balancedActivation, Sum.elim_inl, Sum.elim_inr, zero_mul, mul_zero, add_zero]
  rw [show (fun e => w e / δ * F (Sum.inl e)) = fun e => w e * F (Sum.inl e) / δ from funext fun _ => by ring,
    integral_div]
  field_simp

theorem balancedActivation_integral_zero {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (w : E → ℝ) (hw : Measurable w) (hwi : Integrable w μ) (hc : ∫ e, w e ∂μ = 0) :
    ∫ e, balancedActivation w δ e ∂balancedReferenceLaw μ δ = 0 := by
  simpa only [mul_one, hc] using balancedActivation_integral μ δ hδ hδ1 w hw (fun _ => 1)
    measurable_const (by simpa only [mul_one] using hwi)

theorem boundedIntercept_integrable {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : Integrable B μ :=
  (integrable_const (max |a| |b|)).mono' hB.aestronglyMeasurable <| Eventually.of_forall fun e => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_abs_le a, le_max_left |a| |b|, (hb e).1],
      (hb e).2.trans ((le_abs_self b).trans (le_max_right _ _))⟩

theorem boundedIntercept_mean_mem {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (B : E → ℝ) (hB : Measurable B)
    (a b : ℝ) (hb : ∀ e, B e ∈ Icc a b) : (∫ e, B e ∂μ) ∈ Icc a b :=
  have hBi := boundedIntercept_integrable μ B hB a b hb
  ⟨by simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono (integrable_const a) hBi fun e => (hb e).1,
   by simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using
      integral_mono hBi (integrable_const b) fun e => (hb e).2⟩

-- High observation laws, kernels, real encodings, and mass-power tilts

private lemma highRawDensity_integrable_of_interval {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a) (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    Integrable p (cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  refine (integrable_const b).mono' hp.aestronglyMeasurable ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (ha.le.trans hx.1)]; exact hx.2

theorem highRawDensityMass_mem_Icc {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a) (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    highRawDensityMass p ∈ Icc a b := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval p hp a b ha hb
  exact ⟨by simpa [highRawDensityMass] using integral_mono_ae (integrable_const a) hi (hb.mono fun _ hx => hx.1),
    by simpa [highRawDensityMass] using integral_mono_ae hi (integrable_const b) (hb.mono fun _ hx => hx.2)⟩

theorem normalizedDensityTernaryParameter_design_probability {d : ℕ}
    (p : Covariate d → ℝ) (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) :
    IsProbabilityMeasure ((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)) := by
  let _ := cubeVolume_isProbability d
  have hi := highRawDensity_integrable_of_interval p hp a b ha hb
  have hm := highRawDensityMass_mem_Icc p hp a b ha hb
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simpa using highNormalizedDensity_normalized p hi (hb.mono fun _ hx => ha.le.trans hx.1) (ha.trans_le hm.1)

private lemma normalizedDensityTernaryParameter_sample_index_map {d : ℕ}
    (p : Covariate d → ℝ)
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)))
    (n : ℕ) (a V : ℝ) (F : Covariate d → ℝ) (hF : Measurable F) (ha : a ≠ 0)
    (hp : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi fun _ : Fin n => (cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)).compProd
      (responseSampleIndexKernel n a V F hF)).map (encodeDesignResponse a) =
      sampleLaw (normalizedDensityTernaryParameter p F a V hF ha hp) n := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  let _ := responseIndexKernel_markov a V F hF ha hp
  let _ := responseSampleIndexKernel_markov n a V F hF ha hp
  let _ := ternaryErrorKernel_markov a V F hF ha hp
  have henc : Measurable fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2) :=
    measurable_fst.prodMk ((measurable_of_countable _).comp measurable_snd)
  have hobs : (((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)).compProd
      (responseIndexKernel a V F hF)).map (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2)) =
      observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp) := by
    have hreal : Measurable fun z : Covariate d × ℝ => (z.1, F z.1 + z.2) :=
      measurable_fst.prodMk ((hF.comp measurable_fst).add measurable_snd)
    ext s hs
    rw [Measure.map_apply henc hs, observationLaw]
    change _ = (((designLaw (normalizedDensityTernaryParameter p F a V hF ha hp)).compProd
      (ternaryErrorKernel a V F hF)).map fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) s
    rw [Measure.map_apply hreal hs]
    change _ = (((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)).compProd
      (ternaryErrorKernel a V F hF)) ((fun z : Covariate d × ℝ => (z.1, F z.1 + z.2)) ⁻¹' s)
    rw [Measure.compProd_apply (hs.preimage henc), Measure.compProd_apply (hs.preimage hreal)]
    refine lintegral_congr fun x => ?_
    have hSr : MeasurableSet {u : ℝ | (x, F x + u) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_const.add measurable_id))
    have hSi : MeasurableSet {y : Fin 3 | (x, ternaryValue a y) ∈ s} :=
      hs.preimage (measurable_const.prodMk (measurable_of_countable _))
    simp only [responseIndexKernel_apply, ternaryErrorKernel_apply, Measure.finsetSum_apply,
      Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    change Measure.dirac y {y | (x, ternaryValue a y) ∈ s} =
      Measure.dirac (ternaryValue a y - F x) {u | (x, F x + u) ∈ s}
    rw [Measure.dirac_apply' _ hSi, Measure.dirac_apply' _ hSr]
    have he : F x + (ternaryValue a y - F x) = ternaryValue a y := by ring
    by_cases h : (x, ternaryValue a y) ∈ s <;> simp [Set.indicator, he, h]
  have hsingle : MeasurePreserving (fun z : Covariate d × Fin 3 => (z.1, ternaryValue a z.2))
      (((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)).compProd (responseIndexKernel a V F hF))
      (observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp)) := ⟨henc, hobs⟩
  let _ : IsProbabilityMeasure (observationLaw (normalizedDensityTernaryParameter p F a V hF ha hp)) := by
    rw [← hsingle.map_eq]; infer_instance
  have h := (measurePreserving_pi _ _ fun _ : Fin n => hsingle).map_eq
  rw [← responseSampleIndexKernel_joint_map
      ((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)) n a V F hF ha hp,
    Measure.map_map] at h
  · exact h
  · exact Measurable.of_eval fun i => henc.comp (measurable_pi_apply i)
  · fun_prop

def highSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∏ i, p (z.1 i)) / highRawDensityMass p ^ n * ∏ i, ternaryMass a (F (z.1 i)) V (z.2 i)

theorem highSample_index_density {d : ℕ} (n : ℕ) (p F : Covariate d → ℝ)
    (hp : Measurable p) (hF : Measurable F) (a V : ℝ)
    (hdesign : IsProbabilityMeasure ((cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)))
    (hraw : ∀ x, 0 ≤ p x) (hm : 0 < highRawDensityMass p)
    (hq0 : ∀ x y, 0 ≤ ternaryMass a (F x) V y) :
    ((Measure.pi fun _ : Fin n => (cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)).compProd
      (responseSampleIndexKernel n a V F hF)) =
    ((Measure.pi fun _ : Fin n => cubeVolume d).prod
      (Measure.count : Measure (Fin n → Fin 3))).withDensity
        fun z => ENNReal.ofReal (highSampleLikelihood n a V p F z) := by
  let _ := cubeVolume_isProbability d
  let _ := hdesign
  have hf : Measurable fun x => ENNReal.ofReal (highNormalizedDensity p x) :=
    ENNReal.measurable_ofReal.comp (highNormalizedDensity_measurable p hp)
  have hpi : Measure.pi (fun _ : Fin n => (cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)) =
      (Measure.pi fun _ : Fin n => cubeVolume d).withDensity
        fun x => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)) := by
    apply Measure.pi_eq; intro s hs
    rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
    simp_rw [show ∀ x : Fin n → Covariate d,
        (Set.pi Set.univ s).indicator (fun x => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i))) x =
          ∏ i, (s i).indicator (fun x => ENNReal.ofReal (highNormalizedDensity p x)) (x i) from fun x => by
      by_cases h : ∀ i, x i ∈ s i
      · simp [Set.indicator_of_mem, Set.mem_pi, h]
      · obtain ⟨i, hi⟩ := not_forall.mp h
        rw [Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)]
        exact Set.indicator_of_notMem (by simp only [Set.mem_pi, Set.mem_univ, forall_true_left]; exact not_forall.mpr ⟨i, hi⟩) _]
    let G : Fin n → Covariate d → ℝ≥0∞ := fun i => (s i).indicator fun x => ENNReal.ofReal (highNormalizedDensity p x)
    have hG : ∀ i, Measurable (G i) := fun i => hf.indicator (hs i)
    change (∫⁻ x, ∏ i, G i (x i) ∂Measure.pi fun _ : Fin n => cubeVolume d) = _
    rw [lintegral_prod_eq_prod_lintegral_of_indepFun _ _
      (iIndepFun_pi fun i => (hG i).aemeasurable) fun i => (hG i).comp (measurable_pi_apply i)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [(measurePreserving_eval (fun _ : Fin n => cubeVolume d) i).lintegral_comp (hG i)]
    change (∫⁻ b, (s i).indicator (fun x => ENNReal.ofReal (highNormalizedDensity p x)) b ∂cubeVolume d) = _
    rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]
  have hq : Measurable fun z : (Fin n → Covariate d) × (Fin n → Fin 3) =>
      ENNReal.ofReal (∏ i, ternaryMass a (F (z.1 i)) V (z.2 i)) :=
    measurable_from_prod_countable_left fun y => ENNReal.measurable_ofReal.comp
      (Finset.measurable_prod _ fun i _ => ternaryMass_measurable_comp a V
        (fun x : Fin n → Covariate d => F (x i)) (hF.comp (measurable_pi_apply i)) (y i))
  have hrk : responseSampleIndexKernel n a V F hF =
      (Kernel.const (Fin n → Covariate d) (Measure.count : Measure (Fin n → Fin 3))).withDensity
        fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)) := by
    ext x : 1; rw [Kernel.withDensity_apply _ hq]
    simp only [Kernel.const_apply, count_withDensity, Measure.sum_fintype, responseSampleIndexKernel_apply]
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun x y => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
    (Kernel.const (Fin n → Covariate d) (Measure.count : Measure (Fin n → Fin 3))) fun _ _ => ENNReal.ofReal_ne_top
  rw [hpi, hrk, Measure.withDensity_compProd_withDensity
      (f := fun x : Fin n → Covariate d => ∏ i, ENNReal.ofReal (highNormalizedDensity p (x i)))
      (g := fun (x : Fin n → Covariate d) (y : Fin n → Fin 3) => ENNReal.ofReal (∏ i, ternaryMass a (F (x i)) V (y i)))
      (Finset.measurable_prod _ fun i _ => hf.comp (measurable_pi_apply i)) hq,
    Measure.compProd_const]
  congr 1; funext z
  have hpn (i : Fin n) : 0 ≤ highNormalizedDensity p (z.1 i) := div_nonneg (hraw (z.1 i)) hm.le
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ => hpn i,
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hpn i)]
  congr 1; simp [highSampleLikelihood, highNormalizedDensity, Finset.prod_div_distrib]

section KernelAndTilt
variable {Ω : Type*} [MeasurableSpace Ω]

theorem highRawDensityMass_joint_measurable {d : ℕ} (p : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) :
    Measurable fun ω => highRawDensityMass (p ω) := by
  let _ := cubeVolume_isProbability d
  exact hp.stronglyMeasurable.integral_prod_right.measurable

theorem ternaryMass_joint_measurable {α : Type*} [MeasurableSpace α]
    (a V : ℝ) (F : α → ℝ) (hF : Measurable F) :
    Measurable fun z : α × Fin 3 => ternaryMass a (F z.1) V z.2 :=
  measurable_from_prod_countable_left fun y => ternaryMass_measurable_comp a V F hF y

private lemma highSampleLikelihood_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highSampleLikelihood n a V (p z.1) (F z.1) z.2 := by
  have hx (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact ((Finset.measurable_prod _ fun i _ => hp.comp (hx i)).div
    (((highRawDensityMass_joint_measurable p hp).comp measurable_fst).pow_const n)).mul
    (Finset.measurable_prod _ fun i _ =>
      (ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx i).prodMk (hy i)))

def highSampleReference (d n : ℕ) : Measure ((Fin n → Covariate d) × (Fin n → Fin 3)) :=
  (Measure.pi fun _ : Fin n => cubeVolume d).prod Measure.count

instance highSampleReference_isFinite (d n : ℕ) : IsFiniteMeasure (highSampleReference d n) := by
  let _ := cubeVolume_isProbability d
  unfold highSampleReference; infer_instance

def highSampleIndexKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Kernel Ω ((Fin n → Covariate d) × (Fin n → Fin 3)) := by
  let _ := cubeVolume_isProbability d
  exact (Kernel.const Ω (highSampleReference d n)).withDensity
    fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)

theorem highSampleIndexKernel_apply {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highSampleIndexKernel n a V p F hp hF ω =
      (highSampleReference d n).withDensity
        fun z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z) := by
  let _ := cubeVolume_isProbability d
  have hl : Measurable (Function.uncurry fun ω z =>
      ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) :=
    ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)
  change ((Kernel.const Ω (highSampleReference d n)).withDensity
    fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) ω = _
  exact Kernel.withDensity_apply _ hl ω

theorem highSampleIndexKernel_markov {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highSampleIndexKernel n a V p F hp hF) := by
  constructor; intro ω
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  let hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  let _ := hd
  let _ := responseSampleIndexKernel_markov n a V (F ω) hFω ha (hq ω)
  have hm : 0 < highRawDensityMass (p ω) :=
    haRaw.trans_le (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw (Eventually.of_forall (hraw ω))).1
  rw [highSampleIndexKernel_apply, highSampleReference,
    ← highSample_index_density n (p ω) (F ω) hpω hFω a V hd (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  infer_instance

def highRealSampleKernel {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : Kernel Ω (Fin n → Observation d) :=
  (highSampleIndexKernel n a V p F hp hF).map (encodeDesignResponse a)

theorem highRealSampleKernel_apply {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      (highSampleIndexKernel n a V p F hp hF ω).map (encodeDesignResponse a) :=
  Kernel.map_apply _ (encodeDesignResponse_measurable a) ω

theorem highRealSampleKernel_markov {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) :
    IsMarkovKernel (highRealSampleKernel n a V p F hp hF) := by
  let _ := highSampleIndexKernel_markov n a V p F hp hF aRaw bRaw haRaw hraw ha hq
  exact Kernel.IsMarkovKernel.map _ (encodeDesignResponse_measurable a)

theorem highRealSampleKernel_eq_sampleLaw {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) (ha : a ≠ 0)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y) (ω : Ω) :
    highRealSampleKernel n a V p F hp hF ω =
      sampleLaw (normalizedDensityTernaryParameter (p ω) (F ω) a V hF.of_uncurry_left ha (hq ω)) n := by
  have hpω : Measurable (p ω) := hp.of_uncurry_left
  have hFω : Measurable (F ω) := hF.of_uncurry_left
  have hd := normalizedDensityTernaryParameter_design_probability (p ω) hpω aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hm : 0 < highRawDensityMass (p ω) :=
    haRaw.trans_le (highRawDensityMass_mem_Icc (p ω) hpω aRaw bRaw haRaw (Eventually.of_forall (hraw ω))).1
  rw [highRealSampleKernel_apply, highSampleIndexKernel_apply, highSampleReference,
    ← highSample_index_density n (p ω) (F ω) hpω hFω a V hd (fun x => haRaw.le.trans (hraw ω x).1) hm (hq ω)]
  exact normalizedDensityTernaryParameter_sample_index_map (p ω) hd n a V (F ω) hFω ha (hq ω)

def massPowerNormalizer (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : ℝ := ∫ ω, m ω ^ n ∂μ

def massPowerTilt (μ : Measure Ω) (m : Ω → ℝ) (n : ℕ) : Measure Ω :=
  μ.withDensity fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer μ m n)

theorem massPower_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : Integrable (fun ω => m ω ^ n) μ :=
  (integrable_const (b ^ n)).mono' (hm.pow_const n).aestronglyMeasurable <| Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n)]
    exact pow_le_pow_left₀ (ha.le.trans (hbound ω).1) (hbound ω).2 n

theorem massPowerNormalizer_pos (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : 0 < massPowerNormalizer μ m n :=
  (pow_pos ha n).trans_le <| by
    simpa [massPowerNormalizer] using integral_mono_ae (integrable_const (a ^ n))
      (massPower_integrable μ m hm n a b ha hbound)
      (Eventually.of_forall fun ω => pow_le_pow_left₀ ha.le (hbound ω).1 n)

theorem massPowerTilt_isProbability (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : Ω → ℝ) (hm : Measurable m) (n : ℕ) (a b : ℝ) (ha : 0 < a)
    (hbound : ∀ ω, a ≤ m ω ∧ m ω ≤ b) : IsProbabilityMeasure (massPowerTilt μ m n) := by
  have hi := massPower_integrable μ m hm n a b ha hbound
  have hG := massPowerNormalizer_pos μ m hm n a b ha hbound
  constructor
  rw [massPowerTilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Eventually.of_forall fun ω => div_nonneg (pow_nonneg (ha.le.trans (hbound ω).1) n) hG.le),
    integral_div]
  change ENNReal.ofReal (massPowerNormalizer μ m n / massPowerNormalizer μ m n) = 1
  rw [div_self hG.ne', ENNReal.ofReal_one]

theorem massPowerNormalizer_eq_of_massLaw (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    massPowerNormalizer μ m n = massPowerNormalizer ν m n := by
  have hμ := integral_map_of_stronglyMeasurable (μ := μ) hm
    (measurable_id.pow_const n : Measurable fun x : ℝ => x ^ n).stronglyMeasurable
  have hν := integral_map_of_stronglyMeasurable (μ := ν) hm
    (measurable_id.pow_const n : Measurable fun x : ℝ => x ^ n).stronglyMeasurable
  rw [hlaw] at hμ; exact hμ.symm.trans hν

theorem massPowerTilt_massLaw_eq (μ ν : Measure Ω) (m : Ω → ℝ)
    (hm : Measurable m) (n : ℕ) (hlaw : μ.map m = ν.map m) :
    (massPowerTilt μ m n).map m = (massPowerTilt ν m n).map m := by
  have hpb (ρ : Measure Ω) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
      (ρ.withDensity fun ω => f (m ω)).map m = (ρ.map m).withDensity f :=
    Measure.ext_of_lintegral _ fun G hG => by
      have hfm : Measurable fun ω => f (m ω) := hf.comp hm
      have hGm : Measurable fun ω => G (m ω) := hG.comp hm
      rw [lintegral_map hG hm, lintegral_withDensity_eq_lintegral_mul _ hfm hGm,
        lintegral_withDensity_eq_lintegral_mul _ hf hG, lintegral_map (hf.mul hG) hm]; rfl
  unfold massPowerTilt
  rw [massPowerNormalizer_eq_of_massLaw μ ν m hm n hlaw]
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (x ^ n / massPowerNormalizer ν m n) :=
    ENNReal.measurable_ofReal.comp ((measurable_id.pow_const n).div_const _)
  rw [hpb μ _ hf, hpb ν _ hf, hlaw]

def highRawSampleLikelihood {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  ∏ i, p (z.1 i) * ternaryMass a (F (z.1 i)) V (z.2 i)

theorem highRawSampleLikelihood_joint_measurable {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 := by
  have hx (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => (z.1, z.2.1 i) :=
    measurable_fst.prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hy (i : Fin n) : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) => z.2.2 i :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  exact Finset.measurable_prod _ fun i _ => (hp.comp (hx i)).mul
    ((ternaryMass_joint_measurable a V (Function.uncurry F) hF).comp ((hx i).prodMk (hy i)))

theorem highSampleLikelihood_mass_cancellation {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Covariate d → ℝ) (hm : highRawDensityMass p ≠ 0)
    (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    highRawDensityMass p ^ n * highSampleLikelihood n a V p F z = highRawSampleLikelihood n a V p F z := by
  simp only [highSampleLikelihood, highRawSampleLikelihood, Finset.prod_mul_distrib]; field_simp

instance highSampleIndexKernel_isSFinite {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : Measurable (Function.uncurry p))
    (hF : Measurable (Function.uncurry F)) : IsSFiniteKernel (highSampleIndexKernel n a V p F hp hF) := by
  change IsSFiniteKernel ((Kernel.const Ω (highSampleReference d n)).withDensity
    fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
  exact Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel _ fun _ _ => ENNReal.ofReal_ne_top

theorem massPowerTilt_highSample_compProd {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw) :
    (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF) =
      (ν.prod (highSampleReference d n)).withDensity fun z =>
        ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 /
          massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hm : Measurable m := highRawDensityMass_joint_measurable p hp
  have hbound (ω : Ω) : aRaw ≤ m ω ∧ m ω ≤ bRaw :=
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hG := massPowerNormalizer_pos ν m hm n aRaw bRaw haRaw hbound
  let _ := Kernel.isSFiniteKernel_withDensity_of_isFiniteKernel
    (f := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
    (Kernel.const Ω (highSampleReference d n)) fun _ _ => ENNReal.ofReal_ne_top
  change (ν.withDensity fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n)).compProd
    ((Kernel.const Ω (highSampleReference d n)).withDensity
      fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z)) = _
  rw [Measure.withDensity_compProd_withDensity
      (f := fun ω => ENNReal.ofReal (m ω ^ n / massPowerNormalizer ν m n))
      (g := fun ω z => ENNReal.ofReal (highSampleLikelihood n a V (p ω) (F ω) z))
      (ENNReal.measurable_ofReal.comp ((hm.pow_const n).div_const _))
      (ENNReal.measurable_ofReal.comp (highSampleLikelihood_joint_measurable n a V p F hp hF)),
    Measure.compProd_const]
  congr 1; funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (pow_nonneg (haRaw.le.trans (hbound z.1).1) n) hG.le)]
  congr 1
  rw [div_mul_eq_mul_div, highSampleLikelihood_mass_cancellation n a V (p z.1) (F z.1) (haRaw.trans_le (hbound z.1).1).ne']

theorem massPowerTilt_highSample_integral {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw) (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ) :
    (∫ z, H z ∂(massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n).compProd
      (highSampleIndexKernel n a V p F hp hF)) =
      (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
        ∫ z, highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 * H z ∂ν.prod (highSampleReference d n) := by
  let m : Ω → ℝ := fun ω => highRawDensityMass (p ω)
  have hG := massPowerNormalizer_pos ν m (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw fun ω =>
    highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hu0 (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) :
      0 ≤ highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 :=
    Finset.prod_nonneg fun i _ => mul_nonneg (haRaw.le.trans (hraw z.1 (z.2.1 i)).1) (hq z.1 (z.2.1 i) (z.2.2 i))
  have hD : Measurable fun z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      ENNReal.ofReal (highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 / massPowerNormalizer ν m n) :=
    ENNReal.measurable_ofReal.comp ((highRawSampleLikelihood_joint_measurable n a V p F hp hF).div_const _)
  rw [massPowerTilt_highSample_compProd ν n a V p F hp hF aRaw bRaw haRaw hraw,
    integral_withDensity_eq_integral_toReal_smul hD (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hu0 _) hG.le), smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun _ => by ring)

end KernelAndTilt

-- History expectation derivative, label decomposition, weak transport, and observable product rule

section HistoryWeakEvolution
variable {J : Type*} [Fintype J] [LinearOrder J]

def historyMarkedExpectation (dependent : J → J → Prop) (ρ : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E))
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) (t : ℝ) : ℝ :=
  ∫ h, F h * historyMarkedDensity dependent ρ t a h ∂μ

private lemma historyMarkedExpectation_hasDerivAt (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (ρ T B t : ℝ) (hρ : 0 < ρ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsFiniteMeasure μ]
    (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    HasDerivAt (historyMarkedExpectation dependent ρ μ a F)
      (∫ h, F h * historyMarkedDensityDerivative dependent ρ t a h ∂μ) t := by
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hs (u : ℝ) (hu : u ∈ Ioo 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB) hρ.le).trans hsmall
  have hFM (u : ℝ) : Measurable fun h => F h * historyMarkedDensity dependent ρ u a h :=
    hF.mul (historyMarkedDensity_measurable dependent ρ u a ha)
  have hInt : Integrable (fun h => F h * historyMarkedDensity dependent ρ t a h) μ :=
    Integrable.of_bound (hFM t).aestronglyMeasurable (M * C) <| Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_mul]
      have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht.le hB a habound (hs t ⟨ht, htT⟩) h
      have hn : 0 ≤ historyMarkedDensity dependent ρ t a h := (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
      rw [abs_of_nonneg hn]; exact mul_le_mul (hFbound h) hb.2 hn hM
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun u h => F h * historyMarkedDensity dependent ρ u a h)
    (F' := fun u h => F h * historyMarkedDensityDerivative dependent ρ u a h)
    (bound := fun _ => M * D) (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hFM u).aestronglyMeasurable) hInt
    (hF.mul (historyMarkedDensityDerivative_measurable dependent ρ t a ha)).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hFbound h)
        (historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B hρ hu.1.le hB a habound (hs u hu) h)
        (abs_nonneg _) hM)
    (integrable_const (M * D))
    (Eventually.of_forall fun h u _ => (historyMarkedDensity_hasDerivAt dependent ρ u a h).const_mul (F h))).2

private def historyMarkedLabelTerm (dependent : J → J → Prop) (ρ t : ℝ) {E : Type*}
    (a : E → ℝ) (j : J) (h : HistoryMarked dependent E) : ℝ :=
  ∑ x ∈ historyMaximalPieces Finset.univ,
    if wordHeapLabel x = j then historyMarkedPieceWeight dependent a h x *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a h) ρ (Finset.univ.erase x) t else 0

private lemma historyMarkedLabelTerm_eq_zero (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} (a : E → ℝ) (j : J) (h : HistoryMarked dependent E)
    (hn : h ∉ historyMarkedTerminalSet dependent j) : historyMarkedLabelTerm dependent ρ t a j h = 0 := by
  classical
  exact Finset.sum_eq_zero fun x hx => by
    have hl : wordHeapLabel x ≠ j := fun he => hn ((historyShape_terminal_iff_maximal dependent hsymm j h.1).2 ⟨x, hx, he⟩)
    simp [hl]

private lemma historyMarkedLabelTerm_append (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ρ t : ℝ) {E : Type*} [MeasurableSpace E] (a : E → ℝ) (j : J)
    (h : HistoryMarked dependent E) (fresh : E) :
    historyMarkedLabelTerm dependent ρ t a j (historyMarkedAppend dependent hsymm j (h, fresh)) =
      a fresh * historyMarkedDensity dependent ρ t a h := by
  classical
  rcases h with ⟨g, marks⟩
  let x := historyCanonicalAppendedPiece dependent hsymm j g
  unfold historyMarkedLabelTerm
  change (∑ y ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece (historyShapeAppend dependent j g).out dependent)),
    if wordHeapLabel y = j then historyMarkedPieceWeight dependent a
      ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩ y *
      historyScaledUpperDensity (historyMarkedPieceWeight dependent a
        ⟨historyShapeAppend dependent j g, historyCanonicalMarkAppendEquiv dependent hsymm j g (fresh, marks)⟩)
        ρ (Finset.univ.erase y) t else 0) = _
  rw [Finset.sum_eq_single x]
  · rw [ite_eq_left (historyCanonicalAppendedPiece_label dependent hsymm j g)]
    exact congrArg₂ (· * ·)
      (congrArg a (historyCanonicalMarkAppendEquiv_fresh dependent hsymm j g fresh marks))
      (historyCanonicalAppend_density_delete dependent hsymm j g fresh marks a ρ t)
  · intro y hy hne
    have hn : wordHeapLabel y ≠ j := fun hj => hne
      (wordHeap_maximal_label_injective hrefl hsymm Finset.univ hy
        (historyCanonicalAppendedPiece_maximal dependent hsymm j g)
        (hj.trans (historyCanonicalAppendedPiece_label dependent hsymm j g).symm))
    simp [hn]
  · exact fun hn => (hn (historyCanonicalAppendedPiece_maximal dependent hsymm j g)).elim

private lemma historyMarkedLabelTerm_measurable (dependent : J → J → Prop) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (a : E → ℝ) (ha : Measurable a) (j : J) :
    Measurable (historyMarkedLabelTerm dependent ρ t a j) := by
  classical
  rw [historyMarked_measurable_iff]; intro g
  change Measurable fun marks : Fin (historyShapeLength dependent g) → E =>
    ∑ x ∈ historyMaximalPieces (Finset.univ : Finset (WordHeapPiece g.out dependent)),
      if wordHeapLabel x = j then
        a (marks (Fin.cast (historyShapeLength_out dependent g).symm x.position)) *
        historyScaledUpperDensity (historyMarkedPieceWeight dependent a ⟨g, marks⟩) ρ (Finset.univ.erase x) t else 0
  refine Finset.measurable_fun_sum _ fun x _ => ?_
  split_ifs
  · exact (ha.comp (measurable_pi_apply (Fin.cast (historyShapeLength_out dependent g).symm x.position))).mul
      (historyMarkedSubdensity_fiber_measurable dependent ρ t a ha g (Finset.univ.erase x))
  · exact measurable_const

def historyMarkedGeneratorExpectation (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (ρ t : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) (π : Measure E)
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2 *
      historyMarkedDensity dependent ρ t a p.1 ∂μ.prod π

private lemma historyMarkedDensityDerivative_integral_eq_generator (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    (∫ h, F h * historyMarkedDensityDerivative dependent (historyReferenceRho Δ) t a h
      ∂historyMarkedReference dependent Δ π) =
      historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F := by
  classical
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  have hρ := historyReferenceRho_pos Δ
  have hbd (j : J) (h : HistoryMarked dependent E) :
      |historyMarkedLabelTerm dependent ρ t a j h| ≤ B * (3 / 2 : ℝ) ^ Fintype.card J := by
    by_cases hn : h ∈ historyMarkedTerminalSet dependent j
    · rcases h with ⟨g, marks⟩; obtain ⟨old, rfl⟩ := hn
      let p := (historyCanonicalMarkAppendEquiv dependent hsymm j old (E := E)).symm marks
      rw [← (historyCanonicalMarkAppendEquiv dependent hsymm j old).apply_symm_apply marks]
      change |historyMarkedLabelTerm dependent ρ t a j (historyMarkedAppend dependent hsymm j (⟨old, p.2⟩, p.1))| ≤ _
      rw [historyMarkedLabelTerm_append dependent hrefl hsymm, abs_mul]
      have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B hρ ht hB a habound hsmall ⟨old, p.2⟩
      have hp : 0 ≤ historyMarkedDensity dependent ρ t a ⟨old, p.2⟩ :=
        (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
      rw [abs_of_nonneg hp]; exact mul_le_mul (habound _) hb.2 hp hB
    · rw [historyMarkedLabelTerm_eq_zero dependent hsymm ρ t a j h hn, abs_zero]; positivity
  have hi (j : J) : Integrable (fun h => F h * historyMarkedLabelTerm dependent ρ t a j h) μ :=
    Integrable.of_bound (hF.mul (historyMarkedLabelTerm_measurable dependent ρ t a ha j)).aestronglyMeasurable
      (M * (B * (3 / 2 : ℝ) ^ Fintype.card J)) <| Eventually.of_forall fun h => by
        change ‖F h * historyMarkedLabelTerm dependent ρ t a j h‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hFbound h) (hbd j h) (abs_nonneg _) hM
  have hp (h : HistoryMarked dependent E) :
      F h * historyMarkedDensityDerivative dependent ρ t a h =
        ρ⁻¹ * ∑ j, F h * historyMarkedLabelTerm dependent ρ t a j h := by
    have hls : historyMarkedDensityDerivative dependent ρ t a h =
        ρ⁻¹ * ∑ j, historyMarkedLabelTerm dependent ρ t a j h := by
      unfold historyMarkedDensityDerivative historyMarkedLabelTerm
      rw [Finset.sum_comm]; congr 1; refine Finset.sum_congr rfl fun _ _ => ?_; simp
    rw [hls, show F h * (ρ⁻¹ * ∑ j, historyMarkedLabelTerm dependent ρ t a j h) =
      ρ⁻¹ * (F h * ∑ j, historyMarkedLabelTerm dependent ρ t a j h) by ring, Finset.mul_sum]
  have hterm (j : J) : (∫ h, F h * historyMarkedLabelTerm dependent ρ t a j h ∂μ) =
      ρ * ∫ p : HistoryMarked dependent E × E,
        F (historyMarkedAppend dependent hsymm j p) * a p.2 *
          historyMarkedDensity dependent ρ t a p.1 ∂μ.prod π := by
    let G := fun h : HistoryMarked dependent E => F h * historyMarkedLabelTerm dependent ρ t a j h
    have hG : Measurable G := hF.mul (historyMarkedLabelTerm_measurable dependent ρ t a ha j)
    have he := congrArg (fun ν : Measure (HistoryMarked dependent E) => ∫ h, G h ∂ν)
      (historyMarkedReference_append_restrict dependent hrefl hsymm Δ j π)
    rw [integral_smul_measure, integral_map (historyMarkedAppend_measurable dependent hsymm j).aemeasurable
      hG.aestronglyMeasurable] at he
    have hind : (historyMarkedTerminalSet dependent j).indicator G = G := funext fun h => by
      by_cases ht' : h ∈ historyMarkedTerminalSet dependent j
      · simp [ht']
      · simp [ht', G, historyMarkedLabelTerm_eq_zero dependent hsymm ρ t a j h ht']
    rw [← integral_indicator (historyMarkedTerminalSet_measurable dependent j), hind,
      ENNReal.toReal_ofReal hρ.le] at he
    change ρ * (∫ p : HistoryMarked dependent E × E, G (historyMarkedAppend dependent hsymm j p) ∂μ.prod π) =
      ∫ h, G h ∂μ at he
    simp_rw [show ∀ p : HistoryMarked dependent E × E, G (historyMarkedAppend dependent hsymm j p) =
      F (historyMarkedAppend dependent hsymm j p) * a p.2 * historyMarkedDensity dependent ρ t a p.1 from fun p => by
        dsimp only [G]; rw [historyMarkedLabelTerm_append dependent hrefl hsymm]; ring] at he
    exact he.symm
  change (∫ h, F h * historyMarkedDensityDerivative dependent ρ t a h ∂μ) = _
  simp_rw [hp]
  rw [integral_const_mul, integral_finsetSum Finset.univ fun j _ => hi j]
  change ρ⁻¹ * (∑ j, ∫ h, F h * historyMarkedLabelTerm dependent ρ t a j h ∂μ) = _
  simp_rw [hterm]; unfold historyMarkedGeneratorExpectation
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ hρ.ne', one_mul]

theorem historyMarkedExpectation_weak_transport (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B t : ℝ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (M : ℝ) (hM : 0 ≤ M) (hFbound : ∀ h, |F h| ≤ M) :
    HasDerivAt (historyMarkedExpectation dependent (historyReferenceRho Δ)
      (historyMarkedReference dependent Δ π) a F)
      (historyMarkedGeneratorExpectation dependent hsymm (historyReferenceRho Δ) t
        (historyMarkedReference dependent Δ π) π a F) t := by
  let _ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  have hs : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htT.le hB) (historyReferenceRho_pos Δ).le).trans hsmall
  have hd := historyMarkedExpectation_hasDerivAt dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) T B t (historyReferenceRho_pos Δ) ht htT hB
    (historyMarkedReference dependent Δ π) a ha habound hsmall F hF M hM hFbound
  rwa [historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
    t B ht.le hB π a ha habound hs F hF M hM hFbound] at hd

theorem historyMarkedPrior_integral_eq_expectation (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (t B : ℝ) (ht : 0 ≤ t) (hB : 0 ≤ B) {E : Type*} [MeasurableSpace E]
    (π : Measure E) (a : E → ℝ) (ha : Measurable a) (habound : ∀ e, |a e| ≤ B)
    (hsmall : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (F : HistoryMarked dependent E → ℝ) :
    (∫ h, F h ∂historyMarkedPrior dependent Δ t π a) =
      historyMarkedExpectation dependent (historyReferenceRho Δ) (historyMarkedReference dependent Δ π) a F t := by
  rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
    integral_withDensity_eq_integral_toReal_smul
      (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels
    (historyReferenceRho Δ) t B (historyReferenceRho_pos Δ) ht hB a habound hsmall h
  have hp : 0 ≤ historyMarkedDensity dependent (historyReferenceRho Δ) t a h :=
    (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
  simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]; ring

def historyMarkedPriorGenerator (dependent : J → J → Prop)
    (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i) (Δ : ℕ) (t : ℝ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) (a : E → ℝ)
    (F : HistoryMarked dependent E → ℝ) : ℝ :=
  ∑ j, ∫ p : HistoryMarked dependent E × E,
    F (historyMarkedAppend dependent hsymm j p) * a p.2
      ∂(historyMarkedPrior dependent Δ t π a).prod π

theorem historyMarkedPrior_observable_product_rule (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B t : ℝ) (ht : 0 < t) (htT : t < T) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (G G' : ℝ → HistoryMarked dependent E → ℝ)
    (hGM : ∀ u, Measurable (G u)) (hG'M : ∀ u, Measurable (G' u))
    (M M' : ℝ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hGb : ∀ u ∈ Ioo 0 T, ∀ h, |G u h| ≤ M)
    (hG'b : ∀ u ∈ Ioo 0 T, ∀ h, |G' u h| ≤ M')
    (hGD : ∀ h u, u ∈ Ioo 0 T → HasDerivAt (fun v => G v h) (G' u h) u) :
    HasDerivAt (fun u => ∫ h, G u h ∂historyMarkedPrior dependent Δ u π a)
      ((∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
        historyMarkedPriorGenerator dependent hsymm Δ t π a (G t)) t := by
  let μ := historyMarkedReference dependent Δ π
  let _ : IsProbabilityMeasure μ := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  let ρ := historyReferenceRho Δ
  let C : ℝ := (3 / 2 : ℝ) ^ Fintype.card J
  let D : ℝ := ρ⁻¹ * (Fintype.card J : ℝ) * B * C
  have hs (u : ℝ) (hu : u ∈ Ioo 0 T) : u * B / ρ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hB) (historyReferenceRho_pos Δ).le).trans hsmall
  have hφ (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensity dependent ρ u a h| ≤ C := by
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ u B
      (historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
    rw [abs_of_nonneg ((by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1)]
    exact hb.2
  have hφd (u : ℝ) (hu : u ∈ Ioo 0 T) (h : HistoryMarked dependent E) :
      |historyMarkedDensityDerivative dependent ρ u a h| ≤ D :=
    historyMarkedDensityDerivative_bound dependent hrefl hsymm Δ hlabels ρ u B
      (historyReferenceRho_pos Δ) hu.1.le hB a habound (hs u hu) h
  let H : ℝ → HistoryMarked dependent E → ℝ := fun u h => G u h * historyMarkedDensity dependent ρ u a h
  let H' : ℝ → HistoryMarked dependent E → ℝ := fun u h =>
    G' u h * historyMarkedDensity dependent ρ u a h + G u h * historyMarkedDensityDerivative dependent ρ u a h
  have hHM (u : ℝ) : Measurable (H u) := (hGM u).mul (historyMarkedDensity_measurable dependent ρ u a ha)
  have hH'M (u : ℝ) : Measurable (H' u) :=
    ((hG'M u).mul (historyMarkedDensity_measurable dependent ρ u a ha)).add
      ((hGM u).mul (historyMarkedDensityDerivative_measurable dependent ρ u a ha))
  have hi : Integrable (H t) μ := Integrable.of_bound (hHM t).aestronglyMeasurable (M * C)
    (Eventually.of_forall fun h => by
      rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hGb t ⟨ht, htT⟩ h) (hφ t ⟨ht, htT⟩ h) (abs_nonneg _) hM)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := H) (F' := H') (bound := fun _ => M' * C + M * D)
    (s := Ioo 0 T) (Ioo_mem_nhds ht htT)
    (Eventually.of_forall fun u => (hHM u).aestronglyMeasurable) hi (hH'M t).aestronglyMeasurable
    (Eventually.of_forall fun h u hu => by
      rw [Real.norm_eq_abs]
      exact (abs_add_le _ _).trans (add_le_add
        (by rw [abs_mul]; exact mul_le_mul (hG'b u hu h) (hφ u hu h) (abs_nonneg _) hM')
        (by rw [abs_mul]; exact mul_le_mul (hGb u hu h) (hφd u hu h) (abs_nonneg _) hM)))
    (integrable_const (M' * C + M * D))
    (Eventually.of_forall fun h u hu => (hGD h u hu).mul (historyMarkedDensity_hasDerivAt dependent ρ u a h))).2
  have hi1 : Integrable (fun h => G' t h * historyMarkedDensity dependent ρ t a h) μ :=
    Integrable.of_bound ((hG'M t).mul (historyMarkedDensity_measurable dependent ρ t a ha)).aestronglyMeasurable (M' * C)
      (Eventually.of_forall fun h => by
        change ‖G' t h * historyMarkedDensity dependent ρ t a h‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hG'b t ⟨ht, htT⟩ h) (hφ t ⟨ht, htT⟩ h) (abs_nonneg _) hM')
  have hi2 : Integrable (fun h => G t h * historyMarkedDensityDerivative dependent ρ t a h) μ :=
    Integrable.of_bound ((hGM t).mul (historyMarkedDensityDerivative_measurable dependent ρ t a ha)).aestronglyMeasurable (M * D)
      (Eventually.of_forall fun h => by
        change ‖G t h * historyMarkedDensityDerivative dependent ρ t a h‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hGb t ⟨ht, htT⟩ h) (hφd t ⟨ht, htT⟩ h) (abs_nonneg _) hM)
  have hfirst := historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G' t)
  unfold historyMarkedExpectation at hfirst
  have hsecond := historyMarkedDensityDerivative_integral_eq_generator dependent hrefl hsymm Δ hΔ hlabels
    t B ht.le hB π a ha habound (hs t ⟨ht, htT⟩) (G t) (hGM t) M hM (hGb t ⟨ht, htT⟩)
  have hrefG : historyMarkedPriorGenerator dependent hsymm Δ t π a (G t) =
      historyMarkedGeneratorExpectation dependent hsymm ρ t μ π a (G t) := by
    unfold historyMarkedPriorGenerator historyMarkedGeneratorExpectation
    refine Finset.sum_congr rfl fun j _ => ?_
    have hm : Measurable fun p : HistoryMarked dependent E × E =>
        ENNReal.ofReal (historyMarkedDensity dependent ρ t a p.1) :=
      (historyMarkedDensity_measurable dependent ρ t a ha).ennreal_ofReal.comp measurable_fst
    rw [historyMarkedPrior_eq_withDensity dependent Δ t π a ha,
      prod_withDensity_left (historyMarkedDensity_measurable dependent _ t a ha).ennreal_ofReal,
      integral_withDensity_eq_integral_toReal_smul hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have hb := historyMarkedDensity_bounds dependent hrefl hsymm Δ hlabels ρ t B
      (historyReferenceRho_pos Δ) ht.le hB a habound (hs t ⟨ht, htT⟩) p.1
    have hp : 0 ≤ historyMarkedDensity dependent ρ t a p.1 :=
      (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ Fintype.card J).trans hb.1
    simp only [ENNReal.toReal_ofReal hp, smul_eq_mul]; ring
  rw [← hrefG] at hsecond
  change HasDerivAt (fun u => ∫ h, H u h ∂μ) _ t at hd
  rw [show (∫ h, H' t h ∂μ) = (∫ h, G' t h ∂historyMarkedPrior dependent Δ t π a) +
      historyMarkedPriorGenerator dependent hsymm Δ t π a (G t) by
    rw [integral_add hi1 hi2, ← hfirst, hsecond]] at hd
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  exact historyMarkedPrior_integral_eq_expectation dependent hrefl hsymm Δ hlabels
    u B hu.1.le hB π a ha habound (hs u hu) (G u)

end HistoryWeakEvolution
end BalancingAndExperiments

-- ============================================================================
-- 3. Scale Tails, Interpolation Bias, Gaussian Tensor Moments, and Separated Kernel
-- ============================================================================

section CardinalScalesAndSeparatedKernel
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

section ScaleChangeAndTails

private def exponentialScaleMap {ι : Type*} (s : ι → ℝ) : ι → ℝ := fun j => Real.exp (s j) - 1

private def exponentialScaleDerivative {ι : Type*} [Fintype ι] (s : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun j => Real.exp (s j) • ContinuousLinearMap.proj j

private lemma exponential_scale_hasFDerivAt {ι : Type*} [Fintype ι] (s : ι → ℝ) :
    HasFDerivAt exponentialScaleMap (exponentialScaleDerivative s) s :=
  hasFDerivAt_pi.mpr fun j => by
    have h : HasFDerivAt (fun x : ι → ℝ => Real.exp (x j))
        (Real.exp (s j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) s := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_exp (s j)).comp_hasFDerivAt s (hasFDerivAt_apply j s)
    exact h.sub_const 1

private lemma exponential_scale_derivative_det {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → ℝ) :
    |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
  have hd : (exponentialScaleDerivative s).det = ∏ j, Real.exp (s j) := by
    have he : (exponentialScaleDerivative s).toLinearMap =
        LinearMap.pi fun j => ((Real.exp (s j)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj j) := by
      ext; rfl
    change (exponentialScaleDerivative s).toLinearMap.det = _
    rw [he, LinearMap.det_pi]
    simp only [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
  rw [hd, abs_of_nonneg (Finset.prod_nonneg fun _ _ => Real.exp_nonneg _)]

private lemma exponential_scale_injective {ι : Type*} :
    Function.Injective (exponentialScaleMap : (ι → ℝ) → (ι → ℝ)) := fun s t h =>
  funext fun j => Real.exp_injective (by
    have hj := congrFun h j; change Real.exp (s j) - 1 = Real.exp (t j) - 1 at hj; linarith)

private lemma exponential_scale_image_orthant {ι : Type*} :
    exponentialScaleMap '' Ici (0 : ι → ℝ) = Ici (0 : ι → ℝ) := by
  ext t; refine ⟨?_, fun ht => ⟨fun j => Real.log (1 + t j),
    fun j => Real.log_nonneg (by have : (0 : ℝ) ≤ t j := ht j; linarith),
    funext fun j => by
      change Real.exp (Real.log (1 + t j)) - 1 = t j
      rw [Real.exp_log (by have : (0 : ℝ) ≤ t j := ht j; linarith)]; ring⟩⟩
  rintro ⟨s, hs, rfl⟩ j; change 0 ≤ Real.exp (s j) - 1; linarith [Real.one_le_exp_iff.mpr (hs j)]

private lemma integral_exponential_scale_change {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) :
    (∫ t : ι → ℝ in Ici 0, f t) =
      ∫ s : ι → ℝ in Ici 0, (∏ j, Real.exp (s j)) * f (exponentialScaleMap s) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (ι → ℝ))
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt) exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  simpa only [exponential_scale_derivative_det, smul_eq_mul] using h

private lemma integrableOn_exponential_scale_change_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) :
    IntegrableOn f (Ici 0) ↔
      IntegrableOn (fun s : ι → ℝ => (∏ j, Real.exp (s j)) * f (exponentialScaleMap s)) (Ici 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (ι → ℝ))
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt) exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  simpa only [exponential_scale_derivative_det, smul_eq_mul] using h

private def logScaleTail {ι : Type*} [Fintype ι] (b A : ℝ) (t : ι → ℝ) : ℝ :=
  if A ≤ ∑ j, Real.log (1 + t j) then ∏ j, (1 + t j) ^ (-b - 1 : ℝ) else 0

private lemma log_scale_tail_change_pointwise {ι : Type*} [Fintype ι] (b A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s) =
      if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0 := by
  classical
  have he (j : ι) : 1 + exponentialScaleMap s j = Real.exp (s j) := by unfold exponentialScaleMap; ring
  unfold logScaleTail; simp_rw [he, Real.log_exp]; split_ifs
  · rw [← Finset.prod_mul_distrib]
    simp_rw [show ∀ j : ι, Real.exp (s j) * Real.exp (s j) ^ (-b - 1 : ℝ) = Real.exp (-(b * s j)) from
      fun j => by rw [← Real.exp_mul, ← Real.exp_add]; congr 1; ring]
    rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum, Finset.sum_neg_distrib]
  · exact mul_zero _

private lemma log_scale_tail_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (b A : ℝ) (s : κ → ℝ) :
    logScaleTail b A ((MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s) = logScaleTail b A s := by
  classical
  have hs := e.sum_comp fun j : ι => Real.log (1 + (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s j)
  have hp := e.prod_comp fun j : ι => (1 + (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e) s j) ^ (-b - 1 : ℝ)
  simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs hp
  unfold logScaleTail; rw [← hs, ← hp]

private lemma log_scale_tail_integrable_of_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (hcard : Fintype.card ι = m + 1) {b : ℝ} (hb : 0 < b) (A : ℝ) :
    IntegrableOn (logScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  let e : Fin (m + 1) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict]
  refine (hp.integrable_comp_emb (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e).measurableEmbedding).mp ?_
  rw [show logScaleTail b A ∘ MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e =
    (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) from funext (log_scale_tail_reindex e b A)]
  have h : IntegrableOn (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) (Ici 0) := by
    apply (integrableOn_exponential_scale_change_iff _).mpr
    have ht := finite_orthant_tail_integrable (m := m) hb A
    rwa [exponential_orthant_measure_eq_restrict,
      ← show (fun s : Fin (m + 1) → ℝ => (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s)) =
        finiteOrthantTail b A from funext (log_scale_tail_change_pointwise b A)] at ht
  rwa [IntegrableOn, ← exponential_orthant_measure_eq_restrict] at h

private lemma log_scale_tail_integral_uniform_of_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (hcard : Fintype.card ι = m + 1) {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) ≤ 8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  let e : Fin (m + 1) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [← exponential_orthant_measure_eq_restrict, show (∫ t, logScaleTail b A t ∂exponentialOrthantMeasure ι) =
      ∫ s : Fin (m + 1) → ℝ in Ici 0, logScaleTail b A s by
    unfold exponentialOrthantMeasure
    rw [← hp.integral_comp']; simp_rw [log_scale_tail_reindex]; rw [← exponential_orthant_measure_eq_restrict]; rfl]
  rw [integral_exponential_scale_change,
    show (∫ s : Fin (m + 1) → ℝ in Ici 0, (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s)) =
      ∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin (m + 1)) by
      rw [exponential_orthant_measure_eq_restrict]
      exact integral_congr_ae (Eventually.of_forall (log_scale_tail_change_pointwise b A))]
  exact finite_orthant_tail_integral_uniform hb hA

theorem spatial_scale_index_card {n : ℕ} (i : Fin n) : Fintype.card (SpatialScaleIndex i) = n - 1 := by
  simpa [SpatialScaleIndex] using Fintype.card_subtype_compl fun j : Fin n => j = i

private lemma spatialScaleLogSum_of_nonneg {n : ℕ} (i : Fin n) {t : SpatialScaleVector i}
    (ht : t ∈ Ici (0 : SpatialScaleVector i)) :
    spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
  unfold spatialScaleLogSum
  exact Finset.sum_congr rfl fun j _ => by have htj : (0 : ℝ) ≤ t j := ht j; rw [max_eq_right htj]

private lemma spatial_scale_complement_eq {n : ℕ} (i : Fin n) (T : ℝ) :
    {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} ∩ Ici 0 =
      Ici 0 \ spatialScaleDomain i T := by
  ext t; constructor
  · rintro ⟨hlog, ht⟩
    change 2 * Real.log T < ∑ j, Real.log (1 + t j) at hlog
    refine ⟨ht, fun hD => ?_⟩
    have hle : spatialScaleLogSum i t ≤ 2 * Real.log T := hD.2
    rw [spatialScaleLogSum_of_nonneg i ht] at hle
    exact (not_lt_of_ge hle) hlog
  · rintro ⟨ht, hD⟩
    refine ⟨by_contra fun h => hD ⟨ht, ?_⟩, ht⟩
    change spatialScaleLogSum i t ≤ 2 * Real.log T
    rw [spatialScaleLogSum_of_nonneg i ht]; exact le_of_not_gt h

theorem spatial_scale_complement_power_integrable {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {b : ℝ} (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
      (Ici 0 \ spatialScaleDomain i T) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by rw [spatial_scale_index_card]; omega
  have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp (measurable_const.add (measurable_pi_apply j)))
  refine (((log_scale_tail_integrable_of_card hcard hb (2 * Real.log T)).indicator hm).mono_set
    (Set.diff_subset : Ici (0 : SpatialScaleVector i) \ spatialScaleDomain i T ⊆ Ici 0)).congr_fun
    (fun t ht => ?_) (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  rw [← spatial_scale_complement_eq] at ht
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := ht.1
  simp only [Set.indicator_of_mem ht.1, logScaleTail, ite_eq_left hlog.le]

theorem spatial_scale_complement_power_integral_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {b T : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hT : 1 ≤ T) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) ≤
      16 ^ (n - 1) * T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by rw [spatial_scale_index_card]; omega
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp (measurable_const.add (measurable_pi_apply j)))
  have heq : (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T, ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
      ∫ t : SpatialScaleVector i in Ici 0,
        ({t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)}).indicator
          (logScaleTail b (2 * Real.log T)) t := by
    rw [integral_indicator hm, Measure.restrict_restrict hm, spatial_scale_complement_eq]
    refine setIntegral_congr_fun (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet) fun t ht => ?_
    rw [← spatial_scale_complement_eq] at ht
    exact (if_pos (ht.1 : 2 * Real.log T < _).le).symm
  have hle1 : (∫ t : SpatialScaleVector i in Ici 0,
        ({t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)}).indicator
          (logScaleTail b (2 * Real.log T)) t) ≤
      ∫ t : SpatialScaleVector i in Ici 0, logScaleTail b (2 * Real.log T) t :=
    integral_mono_ae ((log_scale_tail_integrable_of_card hcard hbpos _).indicator hm)
      (log_scale_tail_integrable_of_card hcard hbpos _) <| by
        filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : SpatialScaleVector i)))] with t ht
        by_cases hh : t ∈ {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)}
        · simp [Set.indicator_of_mem hh]
        · rw [Set.indicator_of_notMem hh]; unfold logScaleTail; split_ifs
          · exact Finset.prod_nonneg fun j _ => Real.rpow_nonneg (by have : (0 : ℝ) ≤ t j := ht j; linarith) _
          · exact le_rfl
  have h := (heq.trans_le hle1).trans (log_scale_tail_integral_uniform_of_card hcard hb (by linarith))
  rw [show Real.exp (-(b * (2 * Real.log T))) = T ^ (-2 * b : ℝ) by
    rw [Real.rpow_def_of_pos (lt_of_lt_of_le one_pos hT)]; congr 1; ring] at h
  have hpow : (1 + 2 * Real.log T) ^ (n - 2) ≤ (2 : ℝ) ^ (n - 2) * (1 + Real.log T) ^ (n - 2) := by
    simpa only [mul_pow] using pow_le_pow_left₀ (by positivity)
      (by linarith : 1 + 2 * Real.log T ≤ 2 * (1 + Real.log T)) (n - 2)
  have hconst : (8 : ℝ) ^ (n - 2 + 1) * 2 ^ (n - 2) ≤ 16 ^ (n - 1) := by
    rw [show n - 2 + 1 = n - 1 by omega]
    exact (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)) (by positivity)).trans_eq
        (by rw [← mul_pow]; norm_num)
  have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ (8 : ℝ) ^ (n - 2 + 1) * T ^ (-2 * b : ℝ))
  have hc := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2))
  exact h.trans (by nlinarith [hh, hc])

private def finiteOrthantCutoff {q : ℕ} (A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0

private def orthantSumCutoff {ι : Type*} [Fintype ι] (A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if z.1 + ∑ j, z.2 j ≤ A then Real.exp (z.1 + ∑ j, z.2 j) else 0

private def logScaleCutoff {ι : Type*} [Fintype ι] (A : ℝ) (t : ι → ℝ) : ℝ :=
  if ∑ j, Real.log (1 + t j) ≤ A then 1 else 0

private lemma spatial_scale_domain_volume_le_uniform {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {T : ℝ} (hT : 1 ≤ T) :
    (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      2 ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hA : 0 ≤ 2 * Real.log T := by linarith
  have hcutInt {q : ℕ} : Integrable (finiteOrthantCutoff (2 * Real.log T) : (Fin q → ℝ) → ℝ)
      (exponentialOrthantMeasure (Fin q)) := by
    have hm : Measurable (finiteOrthantCutoff (2 * Real.log T) : (Fin q → ℝ) → ℝ) :=
      Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const)
        (Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)) measurable_const
    apply (orthant_cube_indicator_integrable (2 * Real.log T) (Real.exp (2 * Real.log T))).mono' hm.aestronglyMeasurable
    rw [exponential_orthant_measure_eq_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin q → ℝ)))] with s hs
    unfold finiteOrthantCutoff
    by_cases hsum : ∑ j, s j ≤ 2 * Real.log T
    · have hcube : s ∈ Icc (0 : Fin q → ℝ) fun _ => 2 * Real.log T :=
        ⟨hs, fun j => (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum⟩
      rw [ite_eq_left hsum, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Set.indicator_of_mem hcube]
      exact Real.exp_le_exp.mpr hsum
    · rw [ite_eq_right hsum, norm_zero]; exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  let m := n - 2
  have hcard : Fintype.card (SpatialScaleIndex i) = m + 1 := by rw [spatial_scale_index_card]; omega
  let A := 2 * Real.log T
  have hpairInt : Integrable (orthantSumCutoff A : (ℝ × (Fin m → ℝ)) → ℝ)
      ((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) := by
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm
    convert (hp.integrable_comp_emb
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurableEmbedding).mpr
        (hcutInt (q := m + 1)) using 1
    · funext z
      simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
        Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero, A]
    · rfl
  have hfinLe : (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      Real.exp A * A ^ m := by
    have hsplit : (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) =
        ∫ z : ℝ × (Fin m → ℝ), orthantSumCutoff A z
          ∂((volume.restrict (Ici (0 : ℝ))).prod (exponentialOrthantMeasure (Fin m))) := by
      unfold exponentialOrthantMeasure
      rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm).integral_comp']
      exact integral_congr_ae (Eventually.of_forall fun z => by
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
          Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero])
    rw [hsplit, integral_prod_symm _ hpairInt]
    have hdom : (fun s : Fin m → ℝ => ∫ v : ℝ in Ici 0, orthantSumCutoff A (v, s)) ≤ᵐ[
        exponentialOrthantMeasure (Fin m)]
        (Icc (0 : Fin m → ℝ) fun _ => A).indicator fun _ => Real.exp A := by
      rw [exponential_orthant_measure_eq_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin m → ℝ)))] with s hs
      have hsc (S : ℝ) : (∫ v : ℝ in Ici 0, if v + S ≤ A then Real.exp (v + S) else 0) =
          if S ≤ A then Real.exp A - Real.exp S else 0 := by
        rw [show (fun v : ℝ => if v + S ≤ A then Real.exp (v + S) else 0) =
            (Iic (A - S)).indicator fun v : ℝ => Real.exp (v + S) from funext fun v => by
              simp only [Set.indicator, mem_Iic, show (v + S ≤ A ↔ v ≤ A - S) by constructor <;> intro h <;> linarith],
          integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
          show Iic (A - S) ∩ Ici (0 : ℝ) = Icc 0 (A - S) by ext; simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_Icc]; tauto]
        by_cases h : S ≤ A
        · rw [ite_eq_left h, show (fun v : ℝ => Real.exp (v + S)) = fun v => Real.exp S * Real.exp v from
            funext fun v => by rw [Real.exp_add]; ring, integral_const_mul, integral_Icc_eq_integral_Ioc,
            ← intervalIntegral.integral_of_le (by linarith : 0 ≤ A - S), integral_exp,
            Real.exp_zero, mul_sub, ← Real.exp_add, mul_one, show S + (A - S) = A by ring]
        · rw [ite_eq_right h, Icc_eq_empty_of_lt (by linarith : A - S < 0)]; simp
      change (∫ v : ℝ in Ici 0, if v + ∑ j, s j ≤ A then Real.exp (v + ∑ j, s j) else 0) ≤ _
      rw [hsc]
      by_cases hcube : s ∈ Icc (0 : Fin m → ℝ) fun _ => A
      · rw [Set.indicator_of_mem hcube]; split_ifs <;> [linarith [Real.exp_nonneg (∑ j, s j)]; exact Real.exp_nonneg _]
      · have hsum : ¬ ∑ j, s j ≤ A := fun hsum => hcube ⟨hs, fun j =>
          (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum⟩
        rw [ite_eq_right hsum, Set.indicator_of_notMem hcube]
    have h := integral_mono_ae hpairInt.integral_prod_right (orthant_cube_indicator_integrable A (Real.exp A)) hdom
    rw [orthant_cube_indicator_integral hA] at h
    simpa only [Fintype.card_fin, mul_comm] using h
  have hvolEq : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) =
      ∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1)) := by
    have hmS : MeasurableSet {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ A} :=
      measurableSet_le (Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
        (measurable_const.add (measurable_pi_apply j))) measurable_const
    have hdomEq : {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ A} ∩ Ici 0 = spatialScaleDomain i T := by
      ext t; refine ⟨fun ⟨hl, ht⟩ => ⟨ht, ?_⟩, fun ⟨ht, hl⟩ => ⟨?_, ht⟩⟩
      · change spatialScaleLogSum i t ≤ A; rwa [spatialScaleLogSum_of_nonneg i ht]
      · change spatialScaleLogSum i t ≤ A at hl; rwa [spatialScaleLogSum_of_nonneg i ht] at hl
    have hv1 : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) =
        ∫ t : SpatialScaleVector i in Ici 0, logScaleCutoff A t := by
      rw [show (logScaleCutoff A : SpatialScaleVector i → ℝ) =
        {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ A}.indicator fun _ => 1 from
          funext fun _ => by simp only [logScaleCutoff, Set.indicator, mem_setOf_eq],
        integral_indicator hmS, Measure.restrict_restrict hmS, hdomEq, integral_const]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
    let e : Fin (m + 1) ≃ SpatialScaleIndex i := (Fintype.equivFinOfCardEq hcard).symm
    have hp := measurePreserving_piCongrLeft (fun _ : SpatialScaleIndex i => volume.restrict (Ici (0 : ℝ))) e
    rw [hv1, ← exponential_orthant_measure_eq_restrict, show (∫ t, logScaleCutoff A t ∂exponentialOrthantMeasure (SpatialScaleIndex i)) =
        ∫ t : Fin (m + 1) → ℝ in Ici 0, logScaleCutoff A t by
      unfold exponentialOrthantMeasure
      rw [← hp.integral_comp', ← exponential_orthant_measure_eq_restrict]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      have hs := e.sum_comp fun j : SpatialScaleIndex i => Real.log (1 + (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s j)
      simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs
      unfold logScaleCutoff; dsimp only; rw [← hs]]
    rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    have he (j : Fin (m + 1)) : 1 + exponentialScaleMap s j = Real.exp (s j) := by unfold exponentialScaleMap; ring
    unfold logScaleCutoff finiteOrthantCutoff; simp_rw [he, Real.log_exp]
    split_ifs <;> [rw [mul_one, ← Real.exp_sum]; exact mul_zero _]
  have hvle : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      T ^ 2 * (2 * Real.log T) ^ (n - 2) := by
    rw [hvolEq]; convert hfinLe using 1
    have hTpos : 0 < T := lt_of_lt_of_le one_pos hT
    have he : Real.exp (2 * Real.log T) = T ^ 2 := by
      simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 2
    dsimp [A, m]; rw [he]
  have h1 := pow_le_pow_left₀ hlog (by linarith : Real.log T ≤ 1 + Real.log T) (n - 2)
  have h2 := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by positivity)) (sq_nonneg T)
  exact hvle.trans (by rw [mul_pow]; nlinarith [h3])

end ScaleChangeAndTails

-- Anchored patch configuration and cardinal interpolation bias

def anchoredPatchConfiguration {d n : ℕ} (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : Fin n → Covariate d :=
  fun j => if h : j ≠ i then Y ⟨j, h⟩ else x

def spatialPatchDesignMeasure {n : ℕ} (i : Fin n) (d : ℕ) :
    Measure (SpatialScaleIndex i → Covariate d) :=
  Measure.pi fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d)

instance spatialPatchCube_finite (d : ℕ) :
    IsFiniteMeasure ((volume : Measure (Covariate d)).restrict (spatialPatchBox d)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_ne_top

instance spatialPatchDesignMeasure_finite {n : ℕ} (i : Fin n) (d : ℕ) :
    IsFiniteMeasure (spatialPatchDesignMeasure i d) := by
  unfold spatialPatchDesignMeasure; infer_instance

theorem anchored_configuration_same {d n : ℕ} (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : anchoredPatchConfiguration i x Y i = x := by
  simp [anchoredPatchConfiguration]

theorem anchored_configuration_other {d n : ℕ} (i : Fin n) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) (j : SpatialScaleIndex i) :
    anchoredPatchConfiguration i x Y j.val = Y j := by
  simp [anchoredPatchConfiguration, j.property]

private def anchoredCardinalScaleWeight {d n : ℕ} (i : Fin n) (lam : ℝ) (x : Covariate d)
    (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  spatialCardinalWeight lam (spatialScaleExtend i t) (anchoredPatchConfiguration i x Y) i

private lemma anchored_cardinal_tail_joint_integrable {d n : ℕ} (i : Fin n) {lam : ℝ}
    (hlam : 0 ≤ lam) (T : ℝ) (x : Covariate d) :
    Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0 \ spatialScaleDomain i T)).prod (spatialPatchDesignMeasure i d)) := by
  have hc : Continuous fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2 := by
    simp_rw [show ∀ (t : SpatialScaleVector i) (Y : SpatialScaleIndex i → Covariate d),
      anchoredCardinalScaleWeight i lam x t Y = ∏ j, spatialUnaryWeight lam (t j) x (Y j) from fun _ _ => by
        unfold anchoredCardinalScaleWeight; rw [spatial_cardinal_weight_scale_product]
        simp_rw [anchored_configuration_same, anchored_configuration_other]]
    unfold spatialUnaryWeight spatialSquaredDistance; fun_prop
  have hj : Integrable (fun z : SpatialScaleVector i × (SpatialScaleIndex i → Covariate d) =>
      anchoredCardinalScaleWeight i lam x z.1 z.2)
      ((volume.restrict (Ici 0)).prod (spatialPatchDesignMeasure i d)) :=
    (integrable_prod_iff' hc.aestronglyMeasurable).mpr
      ⟨Eventually.of_forall fun Y => spatial_cardinal_weight_orthant_integrable i lam hlam (anchoredPatchConfiguration i x Y),
       (integrable_const (1 : ℝ)).mono' hc.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
        (Eventually.of_forall fun Y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
            integral_congr_ae (by
              filter_upwards [spatial_cardinal_weight_orthant_nonnegative i lam (anchoredPatchConfiguration i x Y)] with t ht
              exact (Real.norm_eq_abs _).trans (abs_of_nonneg ht))]
          exact spatial_cardinal_weight_orthant_integral_le_one i lam hlam (anchoredPatchConfiguration i x Y))⟩
  exact hj.mono_measure (Measure.prod_mono (Measure.restrict_mono_set _ Set.diff_subset) le_rfl)

def anchoredCardinalDefect {d n : ℕ} (i : Fin n) (lam T : ℝ) (x : Covariate d)
    (Y : SpatialScaleIndex i → Covariate d) : ℝ :=
  1 - integratedCardinalWeight lam T (anchoredPatchConfiguration i x Y) i

theorem anchored_cardinal_defect_square_integral_le {d n : ℕ} (hd : 0 < d) (hn : 2 ≤ n)
    (i : Fin n) (x : Covariate d) (hx : x ∈ spatialPatchBox d) {T : ℝ} (hT : 1 ≤ T) :
    (∫ Y, anchoredCardinalDefect i (spatialInterpolationLambda d) T x Y ^ 2
      ∂spatialPatchDesignMeasure i d) ≤
      (16 * spatialUnaryIntegralConstant d) ^ (n - 1) * T ^ (-(d : ℝ)) * (1 + Real.log T) ^ (n - 2) := by
  let lam := spatialInterpolationLambda d
  have hlam : 0 < lam := by dsimp [lam, spatialInterpolationLambda]; positivity
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hjoint := anchored_cardinal_tail_joint_integrable i hlam.le T x
  have hae : (fun Y => anchoredCardinalDefect i lam T x Y) =ᵐ[spatialPatchDesignMeasure i d]
      fun Y => ∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
        anchoredCardinalScaleWeight i lam x t Y := by
    letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have hnull : ∀ᵐ Y ∂spatialPatchDesignMeasure i d, ∀ j : SpatialScaleIndex i, Y j ≠ x :=
      ae_all_iff.mpr fun j => Measure.ae_eval_ne (fun _ : SpatialScaleIndex i => volume.restrict (spatialPatchBox d)) j x
    filter_upwards [hnull] with Y hY
    refine integrated_cardinal_weight_defect_eq_complement i lam T hlam (anchoredPatchConfiguration i x Y) fun j hj => ?_
    rw [anchored_configuration_same, show anchoredPatchConfiguration i x Y j = Y ⟨j, hj⟩ by simp [anchoredPatchConfiguration, hj]]
    exact (hY ⟨j, hj⟩).symm
  have hdefInt : Integrable (anchoredCardinalDefect i lam T x) (spatialPatchDesignMeasure i d) :=
    hjoint.integral_prod_right.congr hae.symm
  have hunit (Y) : anchoredCardinalDefect i lam T x Y ∈ Icc (0 : ℝ) 1 := by
    have h := integrated_cardinal_weight_mem_unit i lam T hlam.le (anchoredPatchConfiguration i x Y)
    unfold anchoredCardinalDefect; exact ⟨by linarith [h.2], by linarith [h.1]⟩
  have hsqInt : Integrable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2) (spatialPatchDesignMeasure i d) := by
    have hm : AEStronglyMeasurable (fun Y => anchoredCardinalDefect i lam T x Y ^ 2) (spatialPatchDesignMeasure i d) := by
      have hh := hdefInt.aestronglyMeasurable.mul hdefInt.aestronglyMeasurable
      change AEStronglyMeasurable (fun Y => anchoredCardinalDefect i lam T x Y * anchoredCardinalDefect i lam T x Y) _ at hh
      simpa only [pow_two] using hh
    exact hdefInt.mono' hm (Eventually.of_forall fun Y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; nlinarith [(hunit Y).1, (hunit Y).2])
  refine (integral_mono_ae hsqInt hdefInt (Eventually.of_forall fun Y => by nlinarith [(hunit Y).1, (hunit Y).2])).trans
    ((integral_congr_ae hae).trans_le ?_)
  rw [(integral_prod_symm _ hjoint).symm.trans (integral_prod _ hjoint)]
  have hpowint := (spatial_scale_complement_power_integrable hn i (by positivity : (0 : ℝ) < (d : ℝ) / 2) T).const_mul
    ((spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  have hdom : (fun t : SpatialScaleVector i =>
      ∫ Y, anchoredCardinalScaleWeight i lam x t Y ∂spatialPatchDesignMeasure i d) ≤ᵐ[
        volume.restrict (Ici 0 \ spatialScaleDomain i T)]
      fun t => (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i) *
        ∏ j, (1 + t j) ^ (-((d : ℝ) / 2) - 1) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)] with t ht
    have hprod : (∫ Y, anchoredCardinalScaleWeight i lam x t Y ∂spatialPatchDesignMeasure i d) =
        ∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y := by
      simp_rw [show ∀ Y : SpatialScaleIndex i → Covariate d,
        anchoredCardinalScaleWeight i lam x t Y = ∏ j, spatialUnaryWeight lam (t j) x (Y j) from fun _ => by
          unfold anchoredCardinalScaleWeight; rw [spatial_cardinal_weight_scale_product]
          simp_rw [anchored_configuration_same, anchored_configuration_other]]
      unfold spatialPatchDesignMeasure
      exact integral_fintype_prod_eq_prod fun (j : SpatialScaleIndex i) (y : Covariate d) => spatialUnaryWeight lam (t j) x y
    rw [hprod, show -((d : ℝ) / 2) - 1 = -(d : ℝ) / 2 - 1 by ring]
    have hle : (∏ j : SpatialScaleIndex i, ∫ y in spatialPatchBox d, spatialUnaryWeight lam (t j) x y) ≤
        ∏ j : SpatialScaleIndex i, spatialUnaryIntegralConstant d * (1 + t j) ^ (-(d : ℝ) / 2 - 1) :=
      Finset.prod_le_prod₀ (fun j _ => integral_nonneg fun _ => by
        have : (0 : ℝ) ≤ t j := ht.1 j; unfold spatialUnaryWeight; positivity)
        fun j _ => spatial_unary_patch_integral_decay hd (t j) (ht.1 j) x hx
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] using hle
  have h := integral_mono_ae hjoint.integral_prod_left hpowint hdom
  rw [integral_const_mul, spatial_scale_index_card] at h
  have hh := mul_le_mul_of_nonneg_left
    (spatial_scale_complement_power_integral_le hn i (by linarith : (1 / 2 : ℝ) ≤ (d : ℝ) / 2) hT)
    (by unfold spatialUnaryIntegralConstant; positivity : 0 ≤ (spatialUnaryIntegralConstant d) ^ Fintype.card (SpatialScaleIndex i))
  rw [spatial_scale_index_card, show -2 * ((d : ℝ) / 2) = -(d : ℝ) by ring] at hh
  exact h.trans (by simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using hh)

-- Gaussian primitive separated marks, monomial products, tensor moments, and cardinal separated kernel

abbrev GaussianPrimitiveIndex (d : ℕ) := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark (d : ℕ) := Covariate d × GaussianPrimitiveIndex d

def gaussianPrimitiveMeasure (d : ℕ) : Measure (GaussianPrimitiveMark d) :=
  (standardGaussianPi d).prod Measure.count

instance gaussianPrimitiveMeasure_isFinite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) := by
  unfold gaussianPrimitiveMeasure; infer_instance

def gaussianTrig {d : ℕ} (lam t : ℝ) (Z x : Covariate d) (s : Bool) : ℝ :=
  if s then Real.sin (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
  else Real.cos (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)

private lemma gaussianTrig_abs_le_one {d : ℕ} (lam t : ℝ) (Z x : Covariate d) (s : Bool) :
    |gaussianTrig lam t Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

def gaussianAffinePolynomial {d : ℕ} (a : Fin d) (s : Bool) : MvPolynomial (Fin d) ℝ :=
  if s then C (-8) * X a else C 2

def gaussianAffineFactor {d : ℕ} (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2

private lemma gaussianAffineFactor_abs_le_one {d : ℕ} (a : Fin d) (s : Bool) (y : Covariate d)
    (hy : |y a| ≤ 2) : |gaussianAffineFactor a s y| ≤ 1 := by
  cases s
  · simp only [gaussianAffineFactor, Bool.false_eq_true, ite_false, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hy)
  · simp [gaussianAffineFactor]

def gaussianPrimitiveLeft {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 x e.2.2.2

def gaussianPrimitiveRight {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (y : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 y e.2.2.2 *
    gaussianAffineFactor e.2.1.1 e.2.2.1.1 y * gaussianAffineFactor e.2.1.2 e.2.2.1.2 y

def gaussianPrimitiveAmplitude {d : ℕ} (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : Fin d →₀ ℕ) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'

private lemma gaussianPrimitiveLeft_bound {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) :
    |gaussianPrimitiveLeft lam t e x| ≤ 1 := gaussianTrig_abs_le_one _ _ _ _ _

private lemma gaussianPrimitiveRight_bound {d : ℕ} (lam t : ℝ) (e : GaussianPrimitiveMark d)
    (y : Covariate d) (hy : ∀ a, |y a| ≤ 2) : |gaussianPrimitiveRight lam t e y| ≤ 1 := by
  unfold gaussianPrimitiveRight; rw [abs_mul, abs_mul]
  exact (mul_le_mul (mul_le_mul (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2)
    (gaussianAffineFactor_abs_le_one e.2.1.1 e.2.2.1.1 y (hy _)) (abs_nonneg _) (by norm_num))
    (gaussianAffineFactor_abs_le_one e.2.1.2 e.2.2.1.2 y (hy _)) (abs_nonneg _) (by norm_num)).trans_eq (by ring)

private lemma gaussianPrimitiveLeft_scale_measurable {d : ℕ} (lam : ℝ) (x : Covariate d) :
    Measurable fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x := by
  have hm : Measurable fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveLeft lam z.1.1 (z.1.2, z.2) x := by
    apply measurable_from_prod_countable_left; intro h
    change Measurable fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

private lemma gaussianPrimitiveRight_scale_measurable {d : ℕ} (lam : ℝ) (y : Covariate d) :
    Measurable fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 y := by
  have hm : Measurable fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
      gaussianPrimitiveRight lam z.1.1 (z.1.2, z.2) y := by
    apply measurable_from_prod_countable_left; intro h
    change Measurable fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2 *
      gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y
    have ht : Measurable fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 y h.2.2 := by
      cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
        unfold gaussianPhase <;> fun_prop
    exact (ht.mul_const _).mul_const _
  exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))

private lemma gaussianPrimitive_observable_integrable {d : ℕ} (lam t : ℝ) (x y : Covariate d)
    (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveLeft lam t e x *
      gaussianPrimitiveRight lam t e y * gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) := by
  have haM : Measurable fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β' :=
    measurable_from_prod_countable_left fun h => by
      dsimp [gaussianPrimitiveAmplitude]
      exact ((((measurable_const.sub ((measurable_pi_apply h.1.1).mul (measurable_pi_apply h.1.2))).const_mul _).mul_const _).mul_const _)
  have haI : Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) :=
    joint_finite_integrable _ _ (fun h => haM.comp (measurable_id.prodMk measurable_const)) fun h => by
      change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z *
        (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
        (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') (standardGaussianPi d)
      exact ((((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _)
  let L := ∑ h : GaussianPrimitiveIndex d,
    |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|
  have hm : Measurable fun e : GaussianPrimitiveMark d =>
      gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y :=
    ((gaussianPrimitiveLeft_scale_measurable lam x).comp (measurable_const.prodMk measurable_id)).mul
      ((gaussianPrimitiveRight_scale_measurable lam y).comp (measurable_const.prodMk measurable_id))
  convert haI.mul_bdd hm.aestronglyMeasurable (Eventually.of_forall fun e => by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2)
      (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2) (abs_nonneg _) (by norm_num)
    have hl : |gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y| ≤ L := by
      dsimp [L]; rw [← abs_mul]
      exact Finset.single_le_sum
        (f := fun h : GaussianPrimitiveIndex d =>
          |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ e.2)
    rw [show |gaussianTrig lam t e.1 x e.2.2.2| * (|gaussianTrig lam t e.1 y e.2.2.2| *
        |gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) =
      (|gaussianTrig lam t e.1 x e.2.2.2| * |gaussianTrig lam t e.1 y e.2.2.2|) *
        (|gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) by ring]
    exact (mul_le_mul_of_nonneg_right htrig (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans (by simpa using hl)) using 1
  funext; ring

private lemma gaussianPrimitive_separated_exact {d : ℕ} (lam t : ℝ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y : Covariate d) (β β' : Fin d →₀ ℕ) :
    t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
      (spatialCardinalAffine x y).coeff β * (spatialCardinalAffine x y).coeff β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveAmplitude lam e β β' ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ (gaussianPrimitive_observable_integrable lam t x y β β')]
  have hcos (Z : Covariate d) : Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) =
      ∑ s : Bool, gaussianTrig lam t Z x s * gaussianTrig lam t Z y s := by
    rw [show gaussianPhase (gaussianSpatialFrequency lam t x y) Z =
      gaussianPhase (fun l => Real.sqrt (2 * lam * t) * y l) Z -
        gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z by
      simp only [gaussianPhase, gaussianSpatialFrequency, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring, Real.cos_sub]
    simp only [Fintype.sum_bool, gaussianTrig, Bool.false_eq_true, ite_false, ite_true]; ring
  have hfin (Z : Covariate d) : (∑ h : GaussianPrimitiveIndex d,
      gaussianPrimitiveLeft lam t (Z, h) x * gaussianPrimitiveRight lam t (Z, h) y *
        gaussianPrimitiveAmplitude lam (Z, h) β β') =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d, gaussianHermite a b Z *
        (∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
        (∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β') *
        Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) := by
    classical
    simp only [Fintype.sum_prod_type]; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp_rw [show ∀ s s' : Bool,
      (∑ p : Bool, gaussianPrimitiveLeft lam t (Z, ((a, b), ((s, s'), p))) x *
        gaussianPrimitiveRight lam t (Z, ((a, b), ((s, s'), p))) y *
          gaussianPrimitiveAmplitude lam (Z, ((a, b), ((s, s'), p))) β β') =
      (lam / 2 * gaussianHermite a b Z * Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
        (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
        (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') from fun s s' => by
      rw [hcos]; simp only [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by
        unfold gaussianPrimitiveLeft gaussianPrimitiveRight gaussianPrimitiveAmplitude; dsimp only; ring]
    have he := Fintype.sum_mul_sum
      (fun s : Bool => gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β)
      (fun s' : Bool => gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')
    rw [show (∑ s : Bool, ∑ s' : Bool,
        (lam / 2 * gaussianHermite a b Z * Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')) =
      (lam / 2 * gaussianHermite a b Z * Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
        ∑ s : Bool, ∑ s' : Bool,
          (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') by
      simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring,
      ← he]
    ring
  simp only [integral_count, hfin]
  let va := fun a : Fin d => ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β
  let vb := fun b : Fin d => ∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
  have hi (a b : Fin d) : Integrable (fun Z : Covariate d => gaussianHermite a b Z * va a * vb b *
      Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) (standardGaussianPi d) :=
    (((gaussianHermite_integrable a b).mul_const (va a)).mul_const (vb b)).mul_bdd
      (by unfold gaussianPhase; fun_prop : Measurable fun Z : Covariate d =>
        Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)).aestronglyMeasurable
      (Eventually.of_forall fun _ => by rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  change _ = ∫ Z, lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
    gaussianHermite a b Z * va a * vb b * Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)
      ∂standardGaussianPi d
  rw [integral_const_mul, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hi a b]
  simp_rw [integral_finsetSum _ fun b _ => hi _ b]
  have hcoeff (γ : Fin d →₀ ℕ) : (spatialCardinalAffine x y).coeff γ =
      ∑ a : Fin d, (y a - x a) * ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff γ := by
    rw [show spatialCardinalAffine x y = ∑ a : Fin d, C (y a - x a) *
        ∑ s : Bool, C (gaussianAffineFactor a s y) * gaussianAffinePolynomial a s by
      unfold spatialCardinalAffine
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial, Bool.false_eq_true, ite_false, ite_true]
      rw [← C_mul, show y a / 2 * 2 = y a by ring]; simp only [C_1, one_mul, map_mul, map_neg]; ring]
    simp only [coeff_sum, coeff_C_mul]
  rw [hcoeff β, hcoeff β']
  have hbilin (ua ub : Fin d → ℝ) :
      t * lam ^ 2 * Real.exp (-(t * lam * spatialSquaredDistance x y)) *
        (∑ a, (y a - x a) * ua a) * (∑ b, (y b - x b) * ub b) =
        lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
          ∫ Z, gaussianHermite a b Z * ua a * ub b *
            Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d := by
    simp_rw [standardGaussian_hermite_cos_integral_const, gaussianSpatialFrequency_squared lam t hlam ht x y]
    rw [show -(2 * lam * t * spatialSquaredDistance x y) / 2 = -(t * lam * spatialSquaredDistance x y) by ring]
    unfold gaussianSpatialFrequency
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)
    calc
      _ = lam / 2 * (2 * lam * t) * (y a - x a) * (y b - x b) * ua a * ub b *
          Real.exp (-(t * lam * spatialSquaredDistance x y)) := by ring
      _ = lam / 2 * (Real.sqrt (2 * lam * t) ^ 2) * (y a - x a) * (y b - x b) * ua a * ub b *
          Real.exp (-(t * lam * spatialSquaredDistance x y)) := by rw [hs]
      _ = _ := by ring
  exact hbilin va vb

def gaussianAffineExponent {d : ℕ} (a : Fin d) (s : Bool) : Fin d →₀ ℕ :=
  if s then Finsupp.single a 1 else 0

def gaussianAffineCoefficient (s : Bool) : ℝ := if s then -8 else 2

def gaussianPolynomialProduct {κ : Type*} [Fintype κ] {d : ℕ}
    (a : κ → Fin d) (s : κ → Bool) : MvPolynomial (Fin d) ℝ := ∏ i, gaussianAffinePolynomial (a i) (s i)

private lemma gaussianPolynomialProduct_frame_cost {κ : Type*} [Fintype κ] {d D : ℕ}
    (a : κ → Fin d) (s : κ → Bool) :
    (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) ≤
      (8 : ℝ) ^ Fintype.card κ := by
  classical
  have hmon : gaussianPolynomialProduct a s =
      monomial (∑ i, gaussianAffineExponent (a i) (s i)) (∏ i, gaussianAffineCoefficient (s i)) := by
    unfold gaussianPolynomialProduct
    simp_rw [show ∀ i : κ, gaussianAffinePolynomial (a i) (s i) =
      monomial (gaussianAffineExponent (a i) (s i)) (gaussianAffineCoefficient (s i)) from
      fun i => by cases s i <;> simp only [gaussianAffinePolynomial, gaussianAffineExponent,
        gaussianAffineCoefficient, Bool.false_eq_true, ite_false, ite_true, C_apply, X,
        monomial_mul_monomial, zero_add, mul_one]]
    exact (monomial_sum_prod _ _ _).symm
  rw [hmon]
  simp_rw [show ∀ β : HighFrameIndex d D,
    |highFrameCoefficients (monomial (∑ i, gaussianAffineExponent (a i) (s i))
      (∏ i, gaussianAffineCoefficient (s i))) β| =
      |∏ i, gaussianAffineCoefficient (s i)| *
        (if (∑ i, gaussianAffineExponent (a i) (s i)) = polynomialBoxExponent β.val then 1 else 0) from
    fun _ => by simp only [highFrameCoefficients, coeff_monomial]; split_ifs <;> simp]
  rw [← Finset.mul_sum]
  have hinj : Function.Injective fun β : HighFrameIndex d D => polynomialBoxExponent β.val :=
    fun _ _ h => Subtype.ext (polynomial_box_exponent_injective h)
  have hind : (∑ β : HighFrameIndex d D,
      if (∑ i, gaussianAffineExponent (a i) (s i)) = polynomialBoxExponent β.val then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hx : ∃ β : HighFrameIndex d D, polynomialBoxExponent β.val = ∑ i, gaussianAffineExponent (a i) (s i)
    · obtain ⟨β₀, hβ₀⟩ := hx
      simp_rw [show ∀ β : HighFrameIndex d D,
        ((∑ i, gaussianAffineExponent (a i) (s i)) = polynomialBoxExponent β.val ↔ β = β₀) from
        fun β => by rw [← hβ₀]; exact ⟨fun h => (hinj h).symm, fun h => by rw [h]⟩]
      simp
    · have he (β : HighFrameIndex d D) : (∑ i, gaussianAffineExponent (a i) (s i)) ≠ polynomialBoxExponent β.val :=
        fun h => hx ⟨β, h.symm⟩
      simp only [ite_eq_right (he _), Finset.sum_const_zero]; norm_num
  refine (mul_le_mul_of_nonneg_left hind (abs_nonneg _)).trans ?_
  rw [mul_one, Finset.abs_prod]
  exact (Finset.prod_le_prod₀ (g := fun _ => (8 : ℝ)) (fun _ _ => abs_nonneg _) fun i _ => by
    cases s i <;> norm_num [gaussianAffineCoefficient]).trans_eq (by simp)

private lemma gaussianPolynomialProduct_rankone_cost {κ κ' : Type*} [Fintype κ] [Fintype κ']
    {d D : ℕ} (a : κ → Fin d) (s : κ → Bool) (b : κ' → Fin d) (s' : κ' → Bool) (c : ℝ) :
    (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) ≤
      |c| * (8 : ℝ) ^ (Fintype.card κ + Fintype.card κ') := by
  rw [show (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) =
      |c| * (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) *
      (∑ β' : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct b s') β'|) by
    simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm], pow_add, mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (gaussianPolynomialProduct_frame_cost a s) (gaussianPolynomialProduct_frame_cost b s')
      (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity))
    (abs_nonneg c)

section TensorMoments
variable {σ E F : Type*} [DecidableEq σ] [MeasurableSpace E] [MeasurableSpace F]

private def polynomialPairMoment (w : E → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : E) : ℝ := w e * (P e).coeff β * (P' e).coeff β'

private lemma polynomialPairMoment_mul_expansion
    (w : E → ℝ) (v : F → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (Q Q' : F → MvPolynomial σ ℝ) (β β' : σ →₀ ℕ) (z : E × F) :
    polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β' z =
      ∑ b ∈ _root_.Finset.HasAntidiagonal.antidiagonal β,
        ∑ b' ∈ _root_.Finset.HasAntidiagonal.antidiagonal β',
          polynomialPairMoment w P P' b.1 b'.1 z.1 * polynomialPairMoment v Q Q' b.2 b'.2 z.2 := by
  unfold polynomialPairMoment; rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private def tensorPolynomialPairMoment {n : ℕ} (w : Fin n → E → ℝ)
    (P P' : Fin n → E → MvPolynomial σ ℝ) (β β' : σ →₀ ℕ) (e : Fin n → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'

private lemma tensorPolynomialPairMoment_fin
    (μ : Measure E) [SigmaFinite μ] (n : ℕ)
    (w : Fin n → E → ℝ) (P P' : Fin n → E → MvPolynomial σ ℝ)
    (p p' : Fin n → MvPolynomial σ ℝ) (a : Fin n → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') :
    ∀ β β', Integrable (tensorPolynomialPairMoment w P P' β β') (Measure.pi fun _ => μ) ∧
      (∫ e, tensorPolynomialPairMoment w P P' β β' e ∂Measure.pi fun _ => μ) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  induction n with
  | zero =>
    intro β β'
    let _ : IsProbabilityMeasure (Measure.pi fun _ : Fin 0 => μ) := ⟨by rw [Measure.pi_empty_univ]⟩
    refine ⟨?_, ?_⟩
    · change Integrable (fun e : Fin 0 → E => tensorPolynomialPairMoment w P P' β β' e) _
      simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty]; exact integrable_const _
    · simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty,
        integral_const, probReal_univ, one_smul]
  | succ n ih =>
    intro β β'
    let W (x : Fin n → E) := ∏ j, w j.succ (x j)
    let Q (x : Fin n → E) := ∏ j, P j.succ (x j)
    let Q' (x : Fin n → E) := ∏ j, P' j.succ (x j)
    have htail := ih (fun j => w j.succ) (fun j => P j.succ) (fun j => P' j.succ)
      (fun j => p j.succ) (fun j => p' j.succ) (fun j => a j.succ)
      (fun j => hi j.succ) (fun j => he j.succ)
    have hiTail (b b') : Integrable (polynomialPairMoment W Q Q' b b')
        (Measure.pi fun _ : Fin n => μ) := (htail b b').1
    have heTail (b b') : (∫ e, polynomialPairMoment W Q Q' b b' e
        ∂Measure.pi fun _ : Fin n => μ) =
        (∏ j : Fin n, a j.succ) * (∏ j : Fin n, p j.succ).coeff b *
          (∏ j : Fin n, p' j.succ).coeff b' := (htail b b').2
    let G := polynomialPairMoment (fun z : E × (Fin n → E) => w 0 z.1 * W z.2)
      (fun z => P 0 z.1 * Q z.2) (fun z => P' 0 z.1 * Q' z.2) β β'
    have hGi : Integrable G (μ.prod (Measure.pi fun _ : Fin n => μ)) := by
      change Integrable (fun z => polynomialPairMoment (fun z : E × (Fin n → E) => w 0 z.1 * W z.2)
        (fun z => P 0 z.1 * Q z.2) (fun z => P' 0 z.1 * Q' z.2) β β' z) _
      simp_rw [polynomialPairMoment_mul_expansion]
      exact integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ =>
        (hi 0 b.1 b'.1).mul_prod (hiTail b.2 b'.2)
    have hGe : (∫ z, G z ∂μ.prod (Measure.pi fun _ : Fin n => μ)) =
        (a 0 * ∏ j : Fin n, a j.succ) * (p 0 * ∏ j : Fin n, p j.succ).coeff β *
          (p' 0 * ∏ j : Fin n, p' j.succ).coeff β' := by
      dsimp only [G]; simp_rw [polynomialPairMoment_mul_expansion]
      rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
        (hi 0 c.1 c'.1).mul_prod (hiTail c.2 c'.2)]
      simp_rw [integral_finsetSum _ fun (c' : (σ →₀ ℕ) × (σ →₀ ℕ)) _ =>
        (hi 0 _ c'.1).mul_prod (hiTail _ c'.2), integral_prod_mul, he 0, heTail]
      rw [coeff_mul, coeff_mul]; simp only [Finset.sum_mul, Finset.mul_sum]
      conv_rhs => rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hcomp : tensorPolynomialPairMoment w P P' β β' ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm = G := funext fun z => by
      simp only [Function.comp_def, tensorPolynomialPairMoment,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove, G, W, Q, Q',
        polynomialPairMoment, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, cast_eq]
    refine ⟨by rwa [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp], ?_⟩
    rw [← hmp.integral_comp']
    change (∫ x, (tensorPolynomialPairMoment w P P' β β' ∘
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm) x
      ∂μ.prod (Measure.pi fun _ : Fin n => μ)) = _
    rw [hcomp, hGe]; simp only [Fin.prod_univ_succ]

private def tensorPolynomialPairMoment_fintype {κ : Type*} [Fintype κ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : κ → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'

private lemma tensorPolynomialPairMoment_fintype_integral {κ : Type*} [Fintype κ]
    (μ : Measure E) [SigmaFinite μ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (p p' : κ → MvPolynomial σ ℝ) (a : κ → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') (β β' : σ →₀ ℕ) :
    Integrable (tensorPolynomialPairMoment_fintype w P P' β β') (Measure.pi fun _ => μ) ∧
      (∫ e, tensorPolynomialPairMoment_fintype w P P' β β' e ∂Measure.pi fun _ => μ) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have h := tensorPolynomialPairMoment_fin μ (Fintype.card κ) (fun j => w (e j)) (fun j => P (e j)) (fun j => P' (e j))
    (fun j => p (e j)) (fun j => p' (e j)) (fun j => a (e j))
    (fun j => hi (e j)) (fun j => he (e j)) β β'
  have hmp := measurePreserving_piCongrLeft (fun _ : κ => μ) e
  have hcomp : tensorPolynomialPairMoment_fintype w P P' β β' ∘
      MeasurableEquiv.piCongrLeft (fun _ : κ => E) e =
      tensorPolynomialPairMoment (fun j => w (e j)) (fun j => P (e j)) (fun j => P' (e j)) β β' := funext fun x => by
    simp only [Function.comp_def, tensorPolynomialPairMoment_fintype, tensorPolynomialPairMoment,
      ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  refine ⟨by rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]; exact h.1, ?_⟩
  rw [← hmp.integral_comp']
  change (∫ x, (tensorPolynomialPairMoment_fintype w P P' β β' ∘
    MeasurableEquiv.piCongrLeft (fun _ : κ => E) e) x ∂Measure.pi fun _ : Fin (Fintype.card κ) => μ) = _
  rw [hcomp, h.2]; simp only [e.prod_comp]

end TensorMoments

-- Gaussian tensor amplitudes and cost

abbrev GaussianTensorMark (κ : Type*) (d : ℕ) := κ → GaussianPrimitiveMark d

def gaussianTensorMeasure (κ : Type*) [Fintype κ] (d : ℕ) : Measure (GaussianTensorMark κ d) :=
  Measure.pi fun _ => gaussianPrimitiveMeasure d

instance gaussianTensorMeasure_finite (κ : Type*) [Fintype κ] (d : ℕ) :
    IsFiniteMeasure (gaussianTensorMeasure κ d) := by
  unfold gaussianTensorMeasure; infer_instance

def gaussianPrimitiveScalar (d : ℕ) (lam : ℝ) (e : GaussianPrimitiveMark d) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1

def gaussianTensorScalar {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveScalar d lam (e i)

def gaussianTensorLeftPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.1) fun i => (e i).2.2.1.1

def gaussianTensorRightPolynomial {κ : Type*} [Fintype κ] {d : ℕ} (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.2) fun i => (e i).2.2.1.2

def gaussianTensorFrameAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) : ℝ :=
  gaussianTensorScalar lam e * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'

private def gaussianTensorAmplitude {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) : ℝ :=
  gaussianTensorScalar lam e * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'

private def gaussianTensorObservable {κ : Type*} [Fintype κ] {d : ℕ} (lam : ℝ) (t : κ → ℝ)
    (x y : κ → Covariate d) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveLeft lam (t i) (e i) (x i) * gaussianPrimitiveRight lam (t i) (e i) (y i)

def realMatrixSymmetrize {I : Type*} (A : I → I → ℝ) (i j : I) : ℝ := (A i j + A j i) / 2

def gaussianTensorSymmetricAmplitude {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (e : GaussianTensorMark κ d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e)

private lemma gaussianTensorSymmetricAmplitude_measurable {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable fun e : GaussianTensorMark κ d => gaussianTensorSymmetricAmplitude lam e β β' := by
  have hpM (d₀ : ℕ) : Measurable (gaussianPrimitiveScalar d₀ lam) :=
    measurable_from_prod_countable_left fun h => by
      dsimp [gaussianPrimitiveScalar]
      exact (measurable_const.sub ((measurable_pi_apply h.1.1).mul (measurable_pi_apply h.1.2))).const_mul _
  have hsM : Measurable (gaussianTensorScalar (κ := κ) (d := d) lam) :=
    Finset.measurable_fun_prod _ fun i _ => (hpM d).comp (measurable_pi_apply i)
  have hcM (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) (γ : Fin d →₀ ℕ) :
      Measurable fun e : GaussianTensorMark κ d =>
        (gaussianPolynomialProduct (fun i => a (e i).2) fun i => s (e i).2).coeff γ :=
    (measurable_of_countable _ : Measurable fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct (fun i => a (h i)) fun i => s (h i)).coeff γ).comp
      (measurable_pi_iff.mpr fun i => measurable_snd.comp (measurable_pi_apply i))
  have hfM (γ γ' : HighFrameIndex d D) :
      Measurable fun e : GaussianTensorMark κ d => gaussianTensorFrameAmplitude lam e γ γ' :=
    ((hsM.mul (hcM (fun h => h.1.1) (fun h => h.2.1.1) (polynomialBoxExponent γ.val))).mul
      (hcM (fun h => h.1.2) (fun h => h.2.1.2) (polynomialBoxExponent γ'.val)))
  exact ((hfM β β').add (hfM β' β)).div_const 2

private lemma gaussianTensorSymmetricAmplitude_cost {κ : Type*} [Fintype κ] {d D : ℕ} (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) ∧
      (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam) e
        ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
  have hpM : Measurable (gaussianPrimitiveScalar d lam) :=
    measurable_from_prod_countable_left fun h => by
      dsimp [gaussianPrimitiveScalar]
      exact (measurable_const.sub ((measurable_pi_apply h.1.1).mul (measurable_pi_apply h.1.2))).const_mul _
  have hpI : Integrable (gaussianPrimitiveScalar d lam) (gaussianPrimitiveMeasure d) :=
    joint_finite_integrable _ _ (fun h => hpM.comp (measurable_id.prodMk measurable_const))
      fun h => (gaussianHermite_integrable h.1.1 h.1.2).const_mul _
  have hpAbs : (∫ e, |gaussianPrimitiveScalar d lam e| ∂gaussianPrimitiveMeasure d) ≤
      8 * |lam| * (d : ℝ) ^ 2 := by
    have hs (h : GaussianPrimitiveIndex d) :
        (∫ Z, |gaussianPrimitiveScalar d lam (Z, h)| ∂standardGaussianPi d) ≤ |lam| := by
      change (∫ Z, |lam / 2 * gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ |lam|
      simp only [abs_mul, integral_const_mul]
      have hm := mul_le_mul_of_nonneg_left (standardGaussian_hermite_abs_integral_le_two h.1.1 h.1.2) (abs_nonneg (lam / 2))
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm ⊢
      exact hm.trans_eq (by ring)
    rw [gaussianPrimitiveMeasure, integral_prod_symm _ hpI.abs, integral_count]
    convert Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h) using 1 <;>
      simp [GaussianPrimitiveIndex, Fintype.card_prod, pow_two] <;> ring
  have hsI : Integrable (gaussianTensorScalar (κ := κ) (d := d) lam) (gaussianTensorMeasure κ d) :=
    Integrable.fintype_prod fun _ : κ => hpI
  have hsAbs : (∫ e, |gaussianTensorScalar (κ := κ) (d := d) lam e| ∂gaussianTensorMeasure κ d) ≤
      (8 * |lam| * (d : ℝ) ^ 2) ^ Fintype.card κ := by
    unfold gaussianTensorScalar gaussianTensorMeasure; simp only [Finset.abs_prod]
    rw [integral_fintype_prod_eq_prod fun (_ : κ) e => |gaussianPrimitiveScalar d lam e|]
    exact (Finset.prod_le_prod₀ (g := fun _ => 8 * |lam| * (d : ℝ) ^ 2)
      (fun _ _ => integral_nonneg fun _ => abs_nonneg _) fun _ _ => hpAbs).trans_eq (by simp)
  have hsymLe (e : GaussianTensorMark κ d) :
      separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e ≤
        |gaussianTensorScalar lam e| * (8 : ℝ) ^ (2 * Fintype.card κ) := by
    have h1 : separatedMatrixCost (gaussianTensorSymmetricAmplitude (D := D) lam) e ≤
        separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e := by
      refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        show |realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e) i j| ≤
          (|gaussianTensorFrameAmplitude lam e i j| + |gaussianTensorFrameAmplitude lam e j i|) / 2 by
          unfold realMatrixSymmetrize; rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)).trans_eq ?_
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : HighFrameIndex d D => |gaussianTensorFrameAmplitude lam e j i|)]
      unfold separatedMatrixCost; ring
    refine h1.trans ?_
    simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
      gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using
      gaussianPolynomialProduct_rankone_cost (D := D)
        (fun i : κ => (e i).2.1.1) (fun i => (e i).2.2.1.1)
        (fun i : κ => (e i).2.1.2) (fun i => (e i).2.2.1.2) (gaussianTensorScalar lam e)
  have hsymM : Measurable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam)) :=
    Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (gaussianTensorSymmetricAmplitude_measurable lam β β').abs
  have hsymI : Integrable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) :=
    (hsI.abs.mul_const ((8 : ℝ) ^ (2 * Fintype.card κ))).mono' hsymM.aestronglyMeasurable
      (Eventually.of_forall fun e => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)]
        exact hsymLe e)
  refine ⟨hsymI, ?_⟩
  have hm := integral_mono hsymI (hsI.abs.mul_const ((8 : ℝ) ^ (2 * Fintype.card κ))) hsymLe
  rw [integral_mul_const] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_right hsAbs (by positivity)).trans_eq
    (by rw [pow_mul, ← mul_pow]; congr 1; ring))

-- Cardinal separated composition, permutation invariance, and separated kernel

theorem spatial_cardinal_polynomial_scale_product {d n : ℕ} (i : Fin n) (U : Fin n → Covariate d) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, spatialCardinalAffine (U i) (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun _ => by simp) fun j : Fin n => spatialCardinalAffine (U i) (U j)]

theorem spatial_cardinal_scale_product {d n : ℕ} (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalScale lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, t j * lam ^ 2 *
        Real.exp (-(t j * lam * spatialSquaredDistance (U i) (U j.val))) := by
  unfold spatialCardinalScale
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun _ => by simp) fun j : Fin n => spatialScaleExtend i t j * lam ^ 2 *
      Real.exp (-(spatialScaleExtend i t j * lam * spatialSquaredDistance (U i) (U j)))]
  exact Finset.prod_congr rfl fun j _ => by simp only [spatialScaleExtend, dite_eq_left j.property]

private lemma gaussian_tensor_cardinal_moments {κ : Type*} [Fintype κ] {d : ℕ}
    (lam : ℝ) (hlam : 0 ≤ lam) (t : κ → ℝ) (ht : ∀ j, 0 ≤ t j)
    (x y : κ → Covariate d) (β β' : Fin d →₀ ℕ) :
    Integrable (fun e : GaussianTensorMark κ d => gaussianTensorObservable lam t x y e *
      gaussianTensorAmplitude lam e β β') (gaussianTensorMeasure κ d) ∧
      (∫ e, gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β'
        ∂gaussianTensorMeasure κ d) =
        (∏ j, t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j)))) *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β' := by
  let w := fun (j : κ) (e : GaussianPrimitiveMark d) =>
    gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
      gaussianPrimitiveScalar d lam e
  let P := fun (_ : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.1 e.2.2.1.1
  let P' := fun (_ : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.2 e.2.2.1.2
  have hpair (j : κ) (b b' : Fin d →₀ ℕ) :
      polynomialPairMoment (w j) (P j) (P' j) b b' =
        fun e => gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
          gaussianPrimitiveAmplitude lam e b b' := funext fun e => by
    dsimp [w, P, P', polynomialPairMoment, gaussianPrimitiveAmplitude, gaussianPrimitiveScalar]; ring
  have h := tensorPolynomialPairMoment_fintype_integral (gaussianPrimitiveMeasure d) w P P'
    (fun j => spatialCardinalAffine (x j) (y j)) (fun j => spatialCardinalAffine (x j) (y j))
    (fun j => t j * lam ^ 2 * Real.exp (-(t j * lam * spatialSquaredDistance (x j) (y j))))
    (fun j b b' => by rw [hpair]; exact gaussianPrimitive_observable_integrable lam (t j) (x j) (y j) b b')
    (fun j b b' => by rw [hpair]; exact (gaussianPrimitive_separated_exact lam (t j) hlam (ht j) (x j) (y j) b b').symm)
    β β'
  rwa [show tensorPolynomialPairMoment_fintype w P P' β β' =
    fun e : GaussianTensorMark κ d => gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β' from
      funext fun e => by
        unfold tensorPolynomialPairMoment_fintype gaussianTensorObservable gaussianTensorAmplitude
          gaussianTensorScalar gaussianTensorLeftPolynomial gaussianTensorRightPolynomial gaussianPolynomialProduct
        dsimp [w, P, P']; rw [Finset.prod_mul_distrib]; ring] at h

abbrev CenteredCardinalMark (d n : ℕ) (i : Fin n) :=
  SpatialScaleVector i × GaussianTensorMark (SpatialScaleIndex i) d

def centeredCardinalMeasure {n : ℕ} (i : Fin n) (d : ℕ) (T : ℝ) :
    Measure (CenteredCardinalMark d n i) :=
  (spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d)

def centeredCardinalAmplitude {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  gaussianTensorSymmetricAmplitude lam z.2

def centeredCardinalFactor {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) : ℝ :=
  if h : l ≠ i then gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x
    else ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x

private lemma centered_cardinal_factor_abs_le_one {d n : ℕ} (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |centeredCardinalFactor i lam z l x| ≤ 1 := by
  unfold centeredCardinalFactor; split_ifs
  · exact gaussianPrimitiveRight_bound lam _ _ x hx
  · rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (g := fun _ => (1 : ℝ)) (fun _ _ => abs_nonneg _)
      fun _ _ => gaussianPrimitiveLeft_bound lam _ _ x).trans_eq (by simp)

private lemma centered_cardinal_factor_measurable {d n : ℕ} (i : Fin n) (lam : ℝ)
    (l : Fin n) (x : Covariate d) :
    Measurable fun z : CenteredCardinalMark d n i => centeredCardinalFactor i lam z l x := by
  unfold centeredCardinalFactor; split_ifs with h
  · have hm : Measurable fun z : CenteredCardinalMark d n i => (z.1 ⟨l, h⟩, z.2 ⟨l, h⟩) :=
      ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_fst).prodMk
        ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_snd)
    exact (gaussianPrimitiveRight_scale_measurable lam x).comp hm
  · refine Finset.measurable_fun_prod _ fun j _ => ?_
    have hm : Measurable fun z : CenteredCardinalMark d n i => (z.1 j, z.2 j) :=
      ((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd)
    exact (gaussianPrimitiveLeft_scale_measurable lam x).comp hm

private lemma centered_cardinal_amplitude_measurable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable fun z : CenteredCardinalMark d n i => centeredCardinalAmplitude i lam z β β' :=
  (gaussianTensorSymmetricAmplitude_measurable lam β β').comp measurable_snd

private lemma centered_cardinal_measure_finite {n : ℕ} (i : Fin n) (d : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  unfold centeredCardinalMeasure; infer_instance

private lemma centered_cardinal_cost_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam))
      (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  have h := (integrable_const (1 : ℝ) (μ := spatialScaleMeasure i T)).mul_prod
    (gaussianTensorSymmetricAmplitude_cost (κ := SpatialScaleIndex i) (d := d) (D := D) lam).1
  change Integrable (fun z : CenteredCardinalMark d n i =>
    separatedMatrixCost (gaussianTensorSymmetricAmplitude lam) z.2)
      ((spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d))
  simpa only [one_mul] using h

private lemma centered_cardinal_cost_integral_le {d n D : ℕ} (hn : 2 ≤ n) (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) ≤
      (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  letI : SFinite (spatialScaleMeasure i T) := by unfold spatialScaleMeasure; infer_instance
  have heq : (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) =
      (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) *
        ∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i)
          (d := d) (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d := by
    have h := integral_prod_mul (μ := spatialScaleMeasure i T)
      (ν := gaussianTensorMeasure (SpatialScaleIndex i) d) (fun _ => (1 : ℝ))
      (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i) (d := d) (D := D) lam))
    simp only [one_mul, integral_const, smul_eq_mul, mul_one] at h
    simpa only [centeredCardinalMeasure, centeredCardinalAmplitude, separatedMatrixCost,
      spatialScaleMeasure, Measure.real, Measure.restrict_apply_univ] using h
  rw [heq]
  have hcost := (gaussianTensorSymmetricAmplitude_cost (κ := SpatialScaleIndex i) (d := d) (D := D) lam).2
  rw [spatial_scale_index_card] at hcost
  have hvol := spatial_scale_domain_volume_le_uniform hn i hT
  have hlog := Real.log_nonneg hT
  have h := mul_le_mul hvol hcost
    (integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (by positivity : 0 ≤ (2 : ℝ) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2))
  convert h using 1
  rw [show (1024 * |lam| * (d : ℝ) ^ 2) = 2 * (512 * |lam| * (d : ℝ) ^ 2) by ring, mul_pow]; ring

private lemma centered_cardinal_product_entry_integrable {d n D : ℕ} (i : Fin n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, centeredCardinalFactor i lam z l (U l)) *
      centeredCardinalAmplitude i lam z β β') (centeredCardinalMeasure i d T) := by
  have hm : Measurable fun z : CenteredCardinalMark d n i => ∏ l, centeredCardinalFactor i lam z l (U l) :=
    Finset.measurable_fun_prod _ fun l _ => centered_cardinal_factor_measurable i lam l (U l)
  have hb (z : CenteredCardinalMark d n i) : |∏ l, centeredCardinalFactor i lam z l (U l)| ≤ 1 := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (g := fun _ => (1 : ℝ)) (fun _ _ => abs_nonneg _)
      fun l _ => centered_cardinal_factor_abs_le_one i lam z l (U l) (hU l)).trans_eq (by simp)
  have h := (separatedMatrix_entry_integrable _ _ (centered_cardinal_amplitude_measurable i lam)
    (centered_cardinal_cost_integrable i lam hT) β β').mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb z)
  exact h.congr (Eventually.of_forall fun _ => mul_comm _ _)

private lemma centered_cardinal_integrated_separated_exact {d n D : ℕ} (i : Fin n)
    (lam : ℝ) (hlam : 0 ≤ lam) {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d)
    (hU : ∀ l r, |U l r| ≤ 2) (β β' : HighFrameIndex d D) :
    (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) =
      ∫ z, (∏ l, centeredCardinalFactor i lam z l (U l)) * centeredCardinalAmplitude i lam z β β'
        ∂centeredCardinalMeasure i d T := by
  letI := spatial_scale_measure_finite i T hT
  symm
  rw [centeredCardinalMeasure, integral_prod _ (centered_cardinal_product_entry_integrable i lam hT U hU β β')]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (spatial_scale_domain_isClosed i T).measurableSet] with t ht
  have hfprod (z : CenteredCardinalMark d n i) :
      (∏ l, centeredCardinalFactor i lam z l (U l)) =
        gaussianTensorObservable lam z.1 (fun _ : SpatialScaleIndex i => U i) (fun j => U j.val) z.2 := by
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
      (fun l => centeredCardinalFactor i lam z l (U l)) (Finset.mem_univ i),
      show centeredCardinalFactor i lam z i (U i) =
        ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) (U i) by simp [centeredCardinalFactor],
      Finset.prod_subtype (p := fun l : Fin n => l ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
        (fun _ => by simp) fun l : Fin n => centeredCardinalFactor i lam z l (U l),
      show (∏ j : SpatialScaleIndex i, centeredCardinalFactor i lam z j.val (U j.val)) =
        ∏ j : SpatialScaleIndex i, gaussianPrimitiveRight lam (z.1 j) (z.2 j) (U j.val) from
        Finset.prod_congr rfl fun j _ => by simp only [centeredCardinalFactor, dite_eq_left j.property],
      ← Finset.prod_mul_distrib]
    rfl
  simp_rw [hfprod]
  have hraw (γ γ' : HighFrameIndex d D) := gaussian_tensor_cardinal_moments lam hlam t (fun j => ht.1 j)
    (fun _ => U i) (fun j => U j.val) (polynomialBoxExponent γ.val) (polynomialBoxExponent γ'.val)
  have hrawI (γ γ' : HighFrameIndex d D) :
      Integrable (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
        gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
          gaussianTensorFrameAmplitude lam e γ γ') (gaussianTensorMeasure (SpatialScaleIndex i) d) :=
    (hraw γ γ').1
  have hrawE (γ γ' : HighFrameIndex d D) :
      (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
        gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
          gaussianTensorFrameAmplitude lam e γ γ' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
        spatialCenteredCardinalMatrix i lam U t γ γ' := by
    simpa only [gaussianTensorFrameAmplitude, gaussianTensorAmplitude, spatialCenteredCardinalMatrix, highFrameCoefficients,
      spatial_cardinal_scale_product, spatial_cardinal_polynomial_scale_product] using (hraw γ γ').2
  change (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
    gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
      gaussianTensorSymmetricAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) = _
  rw [show (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β') =
    fun e => (gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' +
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β' β) / 2 from funext fun _ => by
      unfold gaussianTensorSymmetricAmplitude realMatrixSymmetrize; ring,
    integral_div, integral_add (hrawI β β') (hrawI β' β), hrawE β β', hrawE β' β]
  unfold spatialCenteredCardinalMatrix; ring

private def spatialScalePermutation {n : ℕ} (τ : Equiv.Perm (Fin n)) (i : Fin n) :
    SpatialScaleIndex i ≃ SpatialScaleIndex (τ i) where
  toFun j := ⟨τ j.val, fun h => j.property (τ.injective h)⟩
  invFun j := ⟨τ.symm j.val, fun h => j.property ((τ.apply_symm_apply j.val).symm.trans (congrArg τ h))⟩
  left_inv j := Subtype.ext (τ.symm_apply_apply j.val)
  right_inv j := Subtype.ext (τ.apply_symm_apply j.val)

theorem integrated_cardinal_matrix_perm {d n D : ℕ} (τ : Equiv.Perm (Fin n))
    (lam T : ℝ) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T (U ∘ τ) β β' = integratedCardinalMatrix lam T U β β' := by
  have hc (i : Fin n) :
      (∫ t, spatialCenteredCardinalMatrix i lam (U ∘ τ) t β β' ∂spatialScaleMeasure i T) =
        ∫ t, spatialCenteredCardinalMatrix (τ i) lam U t β β' ∂spatialScaleMeasure (τ i) T := by
    let reidx : SpatialScaleVector i ≃ᵐ SpatialScaleVector (τ i) :=
      MeasurableEquiv.piCongrLeft (fun _ => ℝ) (spatialScalePermutation τ i)
    have hre_app (t : SpatialScaleVector i) (j : SpatialScaleIndex i) :
        reidx t (spatialScalePermutation τ i j) = t j :=
      MeasurableEquiv.piCongrLeft_apply_apply (spatialScalePermutation τ i)
        (β := fun _ : SpatialScaleIndex (τ i) => ℝ) t j
    have hpv (j : SpatialScaleIndex i) : (spatialScalePermutation τ i j).val = τ j.val := rfl
    have hmp : MeasurePreserving reidx (spatialScaleMeasure i T) (spatialScaleMeasure (τ i) T) := by
      have hp := measurePreserving_piCongrLeft (fun _ : SpatialScaleIndex (τ i) => (volume : Measure ℝ))
        (spatialScalePermutation τ i)
      have hr := hp.restrict_preimage (spatial_scale_domain_isClosed (τ i) T).measurableSet
      have hpre : reidx ⁻¹' spatialScaleDomain (τ i) T = spatialScaleDomain i T := by
        ext t
        have horth : reidx t ∈ Ici 0 ↔ t ∈ Ici 0 :=
          ⟨fun h j => by simpa only [Pi.zero_apply, hre_app] using h (spatialScalePermutation τ i j),
           fun h j => by
             obtain ⟨j', rfl⟩ := (spatialScalePermutation τ i).surjective j
             simpa only [Pi.zero_apply, hre_app] using h j'⟩
        have hlog : spatialScaleLogSum (τ i) (reidx t) = spatialScaleLogSum i t := by
          simpa only [spatialScaleLogSum, hre_app] using
            ((spatialScalePermutation τ i).sum_comp fun j => Real.log (1 + max 0 (reidx t j))).symm
        simp only [mem_preimage, spatialScaleDomain, mem_inter_iff, mem_setOf_eq, hlog, horth]
      rwa [hpre] at hr
    rw [← hmp.integral_comp']
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have hpol : spatialCardinalPolynomial (U ∘ τ) i = spatialCardinalPolynomial U (τ i) := by
      rw [spatial_cardinal_polynomial_scale_product, spatial_cardinal_polynomial_scale_product]
      simpa only [Function.comp_def, hpv] using
        (spatialScalePermutation τ i).prod_comp fun j => spatialCardinalAffine (U (τ i)) (U j.val)
    have hsc : spatialCardinalScale lam (spatialScaleExtend i t) (U ∘ τ) i =
        spatialCardinalScale lam (spatialScaleExtend (τ i) (reidx t)) U (τ i) := by
      rw [spatial_cardinal_scale_product, spatial_cardinal_scale_product]
      simpa only [Function.comp_def, hre_app, hpv] using
        (spatialScalePermutation τ i).prod_comp fun j => reidx t j * lam ^ 2 *
          Real.exp (-(reidx t j * lam * spatialSquaredDistance (U (τ i)) (U j.val)))
    simp only [Function.comp_apply, spatialCenteredCardinalMatrix, hpol, hsc]
  simp only [integratedCardinalMatrix, hc]
  exact Equiv.sum_comp τ fun i => ∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T

abbrev CardinalSeparatedMark (d n : ℕ) := Σ i : Fin n, CenteredCardinalMark d n i

def cardinalSeparatedMeasure (d n : ℕ) (T : ℝ) : Measure (CardinalSeparatedMark d n) :=
  ∑ i : Fin n, Measure.map (Sigma.mk i) (centeredCardinalMeasure i d T)

def cardinalSeparatedAmplitude {d n D : ℕ} (lam : ℝ)
    (z : CardinalSeparatedMark d n) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  centeredCardinalAmplitude z.1 lam z.2

def cardinalSeparatedFactor {d n : ℕ} (lam : ℝ) (z : CardinalSeparatedMark d n)
    (l : Fin n) (x : Covariate d) : ℝ :=
  centeredCardinalFactor z.1 lam z.2 l x

theorem cardinal_separated_mark_standardBorel (d n : ℕ) : StandardBorelSpace (CardinalSeparatedMark d n) :=
  sigma_standardBorel_actual

theorem cardinal_separated_measure_finite (d n : ℕ) {T : ℝ} (hT : 1 ≤ T) :
    IsFiniteMeasure (cardinalSeparatedMeasure d n T) := by
  letI : ∀ i : Fin n, IsFiniteMeasure (centeredCardinalMeasure i d T) :=
    fun i => centered_cardinal_measure_finite i d hT
  unfold cardinalSeparatedMeasure; infer_instance

theorem cardinal_separated_amplitude_measurable {d n D : ℕ} (lam : ℝ) (β β' : HighFrameIndex d D) :
    Measurable fun z : CardinalSeparatedMark d n => cardinalSeparatedAmplitude lam z β β' :=
  measurable_sigma_of_fibers _ fun i => centered_cardinal_amplitude_measurable i lam β β'

theorem cardinal_separated_factor_measurable {d n : ℕ} (lam : ℝ) (l : Fin n) (x : Covariate d) :
    Measurable fun z : CardinalSeparatedMark d n => cardinalSeparatedFactor lam z l x :=
  measurable_sigma_of_fibers _ fun i => centered_cardinal_factor_measurable i lam l x

theorem cardinal_separated_factor_abs_le_one {d n : ℕ} (lam : ℝ) (z : CardinalSeparatedMark d n)
    (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |cardinalSeparatedFactor lam z l x| ≤ 1 :=
  centered_cardinal_factor_abs_le_one z.1 lam z.2 l x hx

private lemma cardinal_separated_fibers {d n : ℕ} (T : ℝ)
    (f : CardinalSeparatedMark d n → ℝ) (hf : Measurable f)
    (hi : ∀ i : Fin n, Integrable (fun z => f ⟨i, z⟩) (centeredCardinalMeasure i d T)) :
    Integrable f (cardinalSeparatedMeasure d n T) ∧
      (∫ z, f z ∂cardinalSeparatedMeasure d n T) =
        ∑ i : Fin n, ∫ z, f ⟨i, z⟩ ∂centeredCardinalMeasure i d T := by
  unfold cardinalSeparatedMeasure
  have hm (i : Fin n) := (integrable_map_measure hf.aestronglyMeasurable (measurable_sigma_mk_actual i).aemeasurable).mpr (hi i)
  refine ⟨integrable_finsetSum_measure.mpr fun i _ => hm i, ?_⟩
  rw [integral_finsetSum_measure fun i _ => hm i]
  exact Finset.sum_congr rfl fun i _ => integral_map (measurable_sigma_mk_actual i).aemeasurable hf.aestronglyMeasurable

theorem cardinal_separated_cost_integrable {d n D : ℕ} (lam : ℝ) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam)) (cardinalSeparatedMeasure d n T) :=
  (cardinal_separated_fibers T (separatedMatrixCost (cardinalSeparatedAmplitude (d := d) (n := n) (D := D) lam))
    (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (cardinal_separated_amplitude_measurable lam β β').abs)
    fun i => centered_cardinal_cost_integrable i lam hT).1

theorem cardinal_separated_cost_integral_le {d n D : ℕ} (hn : 2 ≤ n) (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (cardinalSeparatedAmplitude (D := D) lam) z ∂cardinalSeparatedMeasure d n T) ≤
      (n : ℝ) * (1024 * |lam| * (d : ℝ) ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  rw [(cardinal_separated_fibers T (separatedMatrixCost (cardinalSeparatedAmplitude (d := d) (n := n) (D := D) lam))
    (Finset.measurable_fun_sum _ fun β _ => Finset.measurable_fun_sum _ fun β' _ =>
      (cardinal_separated_amplitude_measurable lam β β').abs)
    fun i => centered_cardinal_cost_integrable i lam hT).2]
  change (∑ i : Fin n, ∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z
    ∂centeredCardinalMeasure i d T) ≤ _
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc] using
    Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      fun i _ => centered_cardinal_cost_integral_le (d := d) (D := D) hn i lam hT

private lemma cardinal_separated_product_entry_integrable {d n D : ℕ} (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, cardinalSeparatedFactor lam z l (U l)) * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) :=
  (cardinal_separated_fibers T _
    ((Finset.measurable_fun_prod _ fun l _ => cardinal_separated_factor_measurable lam l (U l)).mul
      (cardinal_separated_amplitude_measurable lam β β'))
    fun i => centered_cardinal_product_entry_integrable i lam hT U hU β β').1

def cardinalSeparatedSymmetricFactor {d n : ℕ} (lam : ℝ)
    (z : CardinalSeparatedMark d n) (U : Fin n → Covariate d) : ℝ :=
  (∑ τ : Equiv.Perm (Fin n), ∏ l, cardinalSeparatedFactor lam z l (U (τ l))) / (n.factorial : ℝ)

theorem cardinal_separated_symmetric_entry_integrable {d n D : ℕ} (lam : ℝ)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β')
      (cardinalSeparatedMeasure d n T) := by
  simpa only [cardinalSeparatedSymmetricFactor, Function.comp_apply, Finset.sum_mul, div_mul_eq_mul_div] using
    (integrable_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) fun (τ : Equiv.Perm (Fin n)) _ =>
      cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β').div_const (n.factorial : ℝ)

theorem integrated_cardinal_symmetric_separated_exact {d n D : ℕ} (lam : ℝ) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    integratedCardinalMatrix lam T U β β' =
      ∫ z, cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T := by
  simp_rw [show ∀ z : CardinalSeparatedMark d n,
    cardinalSeparatedSymmetricFactor lam z U * cardinalSeparatedAmplitude lam z β β' =
      (∑ τ : Equiv.Perm (Fin n),
        (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β') / (n.factorial : ℝ) from
    fun _ => by simp only [cardinalSeparatedSymmetricFactor, Finset.sum_mul, div_mul_eq_mul_div]]
  have hsum := integral_finsetSum (Finset.univ : Finset (Equiv.Perm (Fin n))) fun (τ : Equiv.Perm (Fin n)) _ =>
    cardinal_separated_product_entry_integrable lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β'
  change (∫ z, ∑ τ : Equiv.Perm (Fin n),
    (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
    ∂cardinalSeparatedMeasure d n T) = ∑ τ : Equiv.Perm (Fin n),
      ∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T at hsum
  rw [integral_div, hsum]
  have hs (τ : Equiv.Perm (Fin n)) :
      (∫ z, (∏ l, cardinalSeparatedFactor lam z l (U (τ l))) * cardinalSeparatedAmplitude lam z β β'
        ∂cardinalSeparatedMeasure d n T) = integratedCardinalMatrix lam T U β β' := by
    have hex : integratedCardinalMatrix lam T (U ∘ τ) β β' =
        ∫ z, (∏ l, cardinalSeparatedFactor lam z l ((U ∘ τ) l)) * cardinalSeparatedAmplitude lam z β β'
          ∂cardinalSeparatedMeasure d n T := by
      have hmF : Measurable fun z : CardinalSeparatedMark d n =>
          (∏ l, cardinalSeparatedFactor lam z l ((U ∘ τ) l)) * cardinalSeparatedAmplitude lam z β β' :=
        (Finset.measurable_fun_prod _ fun l _ => cardinal_separated_factor_measurable lam l ((U ∘ τ) l)).mul
          (cardinal_separated_amplitude_measurable lam β β')
      rw [(cardinal_separated_fibers T _ hmF
        fun i => centered_cardinal_product_entry_integrable i lam hT (U ∘ τ) (fun l r => hU (τ l) r) β β').2]
      exact Finset.sum_congr rfl fun i _ =>
        centered_cardinal_integrated_separated_exact i lam hlam hT (U ∘ τ) (fun l r => hU (τ l) r) β β'
    simpa only [Function.comp_apply] using hex.symm.trans (integrated_cardinal_matrix_perm τ lam T U β β')
  simp_rw [hs]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem cardinal_density_separated_sym_eq {d n : ℕ} (lam : ℝ)
    (z : CardinalSeparatedMark d n) (U : Fin n → Covariate d) :
    densitySeparatedSym n (fun i l => cardinalSeparatedFactor lam z l (U i)) Finset.univ =
      cardinalSeparatedSymmetricFactor lam z U := by
  classical
  let e : Fin n ≃ (Finset.univ : Finset (Fin n)) :=
    (Equiv.subtypeUnivEquiv fun i : Fin n => Finset.mem_univ i).symm
  rw [densitySeparatedSym_eq_permutation_average n _ Finset.univ e]
  unfold cardinalSeparatedSymmetricFactor; congr 1
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin n))) _ _ fun τ => ?_
  simpa only [e, Equiv.subtypeUnivEquiv_symm_apply, Equiv.symm_apply_apply,
    Equiv.inv_apply, Equiv.Perm.inv_def] using
      Equiv.prod_comp τ fun l => cardinalSeparatedFactor lam z l (U (τ.symm l))

end CardinalScalesAndSeparatedKernel
end NearlyMinimax
