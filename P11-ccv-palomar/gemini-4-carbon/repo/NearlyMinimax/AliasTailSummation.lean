module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Bounds
public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.LowerSaddle

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal
namespace NearlyMinimax

attribute [local instance] Classical.propDecidable

-- 1. Poisson & factorial tail summation (`PoissonEnergyBounds`, `AliasTailSummation`, `DefectTailSummation`, `FieldTailSummation`)

theorem polynomial_count_factor_le (k r : ℕ) : (k : ℝ) ^ r ≤ ((2 : ℝ) ^ r) ^ k := by
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
  simpa only [← pow_mul, Nat.mul_comm] using pow_le_pow_left₀ (Nat.cast_nonneg k) hk r

theorem poissonCountWeight_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    poissonCountWeight x k ≤ poissonCountWeight y k :=
  div_le_div_of_nonneg_right (pow_le_pow_left₀ hx hxy k) (Nat.cast_nonneg _)

theorem finite_poissonCountWeight_tail_le {x : ℝ} (hx : 0 ≤ x) (a J : ℕ) :
    (∑ j ∈ Finset.range J, poissonCountWeight x (a + j)) ≤
      Real.exp x * poissonCountWeight x a :=
  (((poissonCountWeight_summable x).comp_injective fun _ _ h => Nat.add_left_cancel h).sum_le_tsum _
    fun _ _ => poissonCountWeight_nonneg hx _).trans (poissonCountWeight_tail_le hx a)

def aliasTailConstant (A Csharp C L : ℝ) : ℝ :=
  1 + A * Real.exp (Csharp * C) + Csharp * C * Real.exp L

theorem aliasTailConstant_ge_one {A Csharp C L : ℝ} (hA : 0 ≤ A) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) :
    1 ≤ aliasTailConstant A Csharp C L := by
  unfold aliasTailConstant
  linarith [show 0 ≤ A * Real.exp (Csharp * C) by positivity, show 0 ≤ Csharp * C * Real.exp L by positivity]

theorem finite_alias_energy_tail_le {A P Csharp C L mu : ℝ}
    (hA : 0 ≤ A) (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (M J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (M + 1 + j) ≤ A * P * Real.exp (L * M) * C ^ (M + 1 + j)) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j)) ≤
      aliasTailConstant A Csharp C L * P *
        poissonCountWeight (aliasTailConstant A Csharp C L * mu) (M + 1) := by
  let K := aliasTailConstant A Csharp C L
  have hK0 : 0 ≤ K := zero_le_one.trans (aliasTailConstant_ge_one hA hCs hC)
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (M + 1 + j) * R (M + 1 + j) ≤
      (A * P * Real.exp (L * M)) * poissonCountWeight (Csharp * C * mu) (M + 1 + j) := by
    have h := mul_le_mul_of_nonneg_left (hR j hj) (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (M + 1 + j))
    convert h using 1 <;> unfold poissonCountWeight <;> rw [mul_pow, mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := finite_poissonCountWeight_tail_le (by positivity : 0 ≤ Csharp * C * mu) (M + 1) J
  have hm := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ A * P * Real.exp (L * M))
  have hexp : Real.exp (Csharp * C * mu) ≤ Real.exp (Csharp * C) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hCs hC, hmu1])
  have habs_exp : Real.exp (L * M) * poissonCountWeight (Csharp * C * mu) (M + 1) ≤
      poissonCountWeight ((Csharp * C * mu) * Real.exp L) (M + 1) := by
    have h := mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith only [hL] : L * M ≤ L * ((M : ℝ) + 1)))
      (poissonCountWeight_nonneg (by positivity : 0 ≤ Csharp * C * mu) (M + 1))
    rw [show L * ((M : ℝ) + 1) = (M + 1 : ℕ) * L by push_cast; ring, Real.exp_nat_mul] at h
    simpa only [poissonCountWeight, mul_pow, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  have hpref : A * Real.exp (Csharp * C) ≤ K := by
    unfold K aliasTailConstant; linarith [show 0 ≤ Csharp * C * Real.exp L by positivity]
  have hbase : Csharp * C * Real.exp L * mu ≤ K * mu :=
    mul_le_mul_of_nonneg_right (by unfold K aliasTailConstant; linarith [show 0 ≤ A * Real.exp (Csharp * C) by positivity]) hmu
  calc _ ≤ (A * P * Real.exp (L * M)) * (Real.exp (Csharp * C * mu) * poissonCountWeight (Csharp * C * mu) (M + 1)) := hs.trans hm
    _ ≤ (A * P * Real.exp (L * M)) * (Real.exp (Csharp * C) * poissonCountWeight (Csharp * C * mu) (M + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp (poissonCountWeight_nonneg (by positivity) _)) (by positivity)
    _ = (A * Real.exp (Csharp * C) * P) * (Real.exp (L * M) * poissonCountWeight (Csharp * C * mu) (M + 1)) := by ring
    _ ≤ (A * Real.exp (Csharp * C) * P) * poissonCountWeight ((Csharp * C * mu) * Real.exp L) (M + 1) :=
        mul_le_mul_of_nonneg_left habs_exp (by positivity)
    _ ≤ (K * P) * poissonCountWeight (K * mu) (M + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hpref hP)
          (poissonCountWeight_mono (by positivity) (by nlinarith only [hbase]) _)
          (poissonCountWeight_nonneg (by positivity) _) (mul_nonneg hK0 hP)

def defectTailConstant (Csharp C : ℝ) : ℝ := Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 2

def fieldTailConstant (Csharp C : ℝ) : ℝ := Real.exp (Csharp * C) * poissonCountWeight (Csharp * C) 4

theorem finite_interpolation_defect_tail_le {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C) (hmu : 0 < mu) (J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) / mu ^ j) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp C * P * mu ^ 2 := by
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j) ≤
      P * mu ^ 2 * poissonCountWeight (Csharp * C) (2 + j) := by
    refine (mul_le_mul_of_nonneg_left (hR j hj) (poissonCountWeight_nonneg (mul_nonneg hCs hmu.le) (2 + j))).trans_eq ?_
    unfold poissonCountWeight; rw [mul_pow, mul_pow, pow_add mu]; field_simp
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  exact (hs.trans (mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC) 2 J)
    (mul_nonneg hP (sq_nonneg mu)))).trans_eq (by unfold defectTailConstant; ring)

lemma finite_polynomial_shifted_tail_le (m : ℕ) {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (m + j) ≤ P * C ^ (m + j) * (m + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (m + j) * R (m + j)) ≤
      (Real.exp (Csharp * (C * 2 ^ a)) * poissonCountWeight (Csharp * (C * 2 ^ a)) m) * P * mu ^ m := by
  let C' := C * 2 ^ a
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hb (j : ℕ) (hj : j ∈ Finset.range J) :
      poissonCountWeight (Csharp * mu) (m + j) * R (m + j) ≤
      P * mu ^ m * poissonCountWeight (Csharp * C') (m + j) := by
    have h1 : R (m + j) ≤ P * C' ^ (m + j) :=
      (hR j hj).trans (by
        simpa only [C', mul_pow, ← mul_assoc] using
          mul_le_mul_of_nonneg_left (polynomial_count_factor_le (m + j) a) (by positivity : 0 ≤ P * C ^ (m + j)))
    have h2 := mul_le_mul_of_nonneg_left h1 (poissonCountWeight_nonneg (mul_nonneg hCs hmu) (m + j))
    have hp : mu ^ (m + j) ≤ mu ^ m := by
      rw [pow_add]
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hmu hmu1) (pow_nonneg hmu m)).trans_eq (mul_one _)
    have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hP (poissonCountWeight_nonneg (mul_nonneg hCs hC') (m + j)))
    exact h2.trans (by convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring)
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  exact (hs.trans (mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le (mul_nonneg hCs hC') m J)
    (mul_nonneg hP (pow_nonneg hmu m)))).trans_eq (by ring)

theorem finite_taylor_count_energy_tail_le {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (2 + j) ≤ P * C ^ (2 + j) * (2 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (2 + j) * R (2 + j)) ≤
      defectTailConstant Csharp (C * 2 ^ a) * P * mu ^ 2 :=
  finite_polynomial_shifted_tail_le 2 hP hCs hC hmu hmu1 a J R hR

theorem finite_polynomial_field_count_tail_le {P Csharp C mu : ℝ}
    (hP : 0 ≤ P) (hCs : 0 ≤ Csharp) (hC : 0 ≤ C)
    (hmu : 0 ≤ mu) (hmu1 : mu ≤ 1) (a J : ℕ) (R : ℕ → ℝ)
    (hR : ∀ j ∈ Finset.range J, R (4 + j) ≤ P * C ^ (4 + j) * (4 + j : ℕ) ^ a) :
    (∑ j ∈ Finset.range J, poissonCountWeight (Csharp * mu) (4 + j) * R (4 + j)) ≤
      fieldTailConstant Csharp (C * 2 ^ a) * P * mu ^ 4 :=
  finite_polynomial_shifted_tail_le 4 hP hCs hC hmu hmu1 a J R hR

-- 2. Fine-pair spatial L2, count-two energy & ordinary fine-alias spatial energy
--    (`SpatialFineAliasPairL2`, `FinePairAliasSpatialEnergy`, `FinePairCountTwoEnergy`,
--     `OrdinaryFineAliasSpatialEnergy`, `OrdinaryFineAliasAggregation`, `HighCompleteSourceSpatialTail`)

section SpatialEnergies
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem fullSpatialPatchDesign_real_univ (d n : ℕ) :
    (fullSpatialPatchDesign d n).real univ = (2 : ℝ) ^ (d * n) := by
  simp only [fullSpatialPatchDesign, measureReal_def, Measure.pi_univ,
    Measure.restrict_apply_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  change (volume.real (spatialPatchBox d)) ^ n = _
  rw [spatialPatchBox_real_volume, pow_mul]

lemma finite_pair_kernel_integrable_and_integral_le {X : Type*}
    [MeasurableSpace X] (ν : Measure X) [SigmaFinite ν] (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : μ ≤ ν) (f : X × X → ℝ) (hm : Measurable f) (hn : ∀ z, 0 ≤ f z) (K : ℝ)
    (hi : ∀ x, Integrable (fun y => f (x, y)) ν) (hb : ∀ x, (∫ y, f (x, y) ∂ν) ≤ K) :
    Integrable f (μ.prod μ) ∧ (∫ z, f z ∂μ.prod μ) ≤ μ.real univ * K := by
  have hsection (x : X) : Integrable (fun y => f (x, y)) μ := (hi x).mono_measure hμ
  have hsectionBound (x : X) : (∫ y, f (x, y) ∂μ) ≤ K :=
    (integral_mono_measure hμ (Filter.Eventually.of_forall fun y => hn (x, y)) (hi x)).trans (hb x)
  have hinner : Integrable (fun x => ∫ y, ‖f (x, y)‖ ∂μ) μ :=
    (integrable_const K).mono' hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
        exact hsectionBound x)
  have hf : Integrable f (μ.prod μ) :=
    (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall hsection, hinner⟩
  refine ⟨hf, ?_⟩
  rw [integral_prod _ hf]
  simpa only [integral_const, smul_eq_mul] using integral_mono hf.integral_prod_left (integrable_const K) hsectionBound

theorem finePairTimeSubsetMoment_two_subset_square_integrable_and_le {d n : ℕ} [NeZero d]
    (hd : 4 < d) {lo hi : ℝ} (hlo : 0 < lo) (hhi : lo ≤ hi)
    (S : Finset (Fin n)) (hS : S.card = 2) :
    Integrable (fun U : Fin n → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ) ^ (d * (n - 2)) * (6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / lo ^ (d - 4)) := by
  have hm := ((fineAliasLaplaceKernel_measurable lo hi hhi).comp
    (exactEuclideanDistance_continuous (d := d)).measurable).pow_const 2
  have hpair0 := finite_pair_kernel_integrable_and_integral_le volume (volume.restrict (spatialPatchBox d))
    Measure.restrict_le_self _ hm (fun _ => sq_nonneg _) (6 * spatialInverseFourConstant d / lo ^ (d - 4))
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hlo hhi x).1)
    (fun x => (fineAlias_spatial_squared_integrable_and_integral_le hd hlo hhi x).2)
  have hp2 := measurePreserving_finTwoArrow (volume.restrict (spatialPatchBox d))
  have hfull2_int := hp2.integrable_comp_of_integrable hpair0.1
  have hfull2_le : (∫ U : Fin 2 → Covariate d, fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2
      ∂fullSpatialPatchDesign d 2) ≤ 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / lo ^ (d - 4) := by
    refine (hp2.integral_comp
      (MeasurableEquiv.finTwoArrow : (Fin 2 → Covariate d) ≃ᵐ (Covariate d × Covariate d)).measurableEmbedding _).trans_le
      (hpair0.2.trans_eq ?_)
    rw [measureReal_def, Measure.restrict_apply_univ]
    change volume.real (spatialPatchBox d) * _ = _
    rw [spatialPatchBox_real_volume]; ring
  have hU_ae : ∀ᵐ U ∂fullSpatialPatchDesign d 2, ∀ i, U i ∈ hyperplaneCube d := by
    have hbox : ∀ᵐ U ∂fullSpatialPatchDesign d 2, ∀ i, U i ∈ spatialPatchBox d :=
      ae_all_iff.mpr fun i => (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin 2 => volume.restrict (spatialPatchBox d))
        (i := i)).eventually (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hbox] with U hU i r; exact abs_le.mpr ⟨(hU i).1 r, (hU i).2 r⟩
  have he_ae : (fun U : Fin 2 → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) =ᵐ[fullSpatialPatchDesign d 2]
      fun U => fineAliasLaplaceKernel lo hi (exactEuclideanDistance (U 0) (U 1)) ^ 2 := by
    filter_upwards [hU_ae] with U hU
    congr 1; unfold finePairTimeSubsetMoment; simp only [Fin.prod_univ_two]
    rw [finePairTimeFieldValue_weighted_covariance d lo hi hlo.le _ _ (hU 0) (hU 1),
      exactEuclideanDistance_eq_euclideanNorm]
    unfold fineAliasLaplaceKernel
    rw [intervalIntegral.integral_of_le hhi, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae <| Filter.Eventually.of_forall fun _ => by dsimp; rw [neg_mul]
  have hpair_card : Integrable (fun U : Fin S.card → Covariate d => finePairTimeSubsetMoment lo hi U Finset.univ ^ 2)
      (fullSpatialPatchDesign d S.card) ∧
      (∫ U : Fin S.card → Covariate d, finePairTimeSubsetMoment lo hi U Finset.univ ^ 2
        ∂fullSpatialPatchDesign d S.card) ≤ 6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / lo ^ (d - 4) := by
    rw [hS]; exact ⟨hfull2_int.congr he_ae.symm, (integral_congr_ae he_ae).trans_le hfull2_le⟩
  refine ⟨by simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
             exact spatial_subset_square_integrable_enumerated S _ hpair_card.1, ?_⟩
  rw [finePairTimeSubsetMoment_square_integral_reindex]
  simpa only [hS] using mul_le_mul_of_nonneg_left hpair_card.2 (by positivity : 0 ≤ (2 : ℝ) ^ (d * (n - S.card)))

def finePairAliasActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 *
      (n.choose 2 : ℝ) ^ 2 * (2 : ℝ) ^ (d * (n - 2)) *
        (6 * (2 : ℝ) ^ d * spatialInverseFourConstant d / T0 ^ (d - 4))

def finePairDistanceFactor {d : ℕ} (N : ℝ) (x y : Covariate d) : ℝ :=
  (1 + N * exactEuclideanDistance x y) * Real.exp (-(N * exactEuclideanDistance x y))

lemma finePairDistanceFactor_square_absorption {d : ℕ} {N : ℝ} (hN : 0 ≤ N) (x y : Covariate d) :
    finePairDistanceFactor N x y ^ 2 ≤ 6 * Real.exp (-(N * exactEuclideanDistance x y)) := by
  unfold finePairDistanceFactor
  rw [mul_pow, ← Real.exp_nat_mul]; norm_num only [Nat.cast_ofNat]
  rw [show (2 : ℝ) * -(N * exactEuclideanDistance x y) = -(2 * (N * exactEuclideanDistance x y)) by ring]
  exact pair_defect_exponential_absorption _ (mul_nonneg hN (exactEuclideanDistance_nonneg x y))

lemma finePairDistance_exp_integrable {d : ℕ} {N : ℝ} (hN : 0 < N) :
    Integrable (fun xy : Covariate d × Covariate d => Real.exp (-(N * exactEuclideanDistance xy.1 xy.2)))
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) :=
  Integrable.of_bound (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp).measurable.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hN.le (exactEuclideanDistance_nonneg _ _))))

theorem finePairDistanceFactor_square_integrable {d : ℕ} {N : ℝ} (hN : 0 < N) :
    Integrable (fun xy : Covariate d × Covariate d => finePairDistanceFactor N xy.1 xy.2 ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) := by
  have hm : Measurable fun xy : Covariate d × Covariate d => finePairDistanceFactor N xy.1 xy.2 ^ 2 :=
    (((continuous_const.add (exactEuclideanDistance_continuous.const_mul N)).mul
      (exactEuclideanDistance_continuous.const_mul N |>.neg |>.rexp)).measurable).pow_const 2
  refine ((finePairDistance_exp_integrable hN).const_mul 6).mono' hm.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun _ => by
    rw [Real.norm_eq_abs, abs_sq]; exact finePairDistanceFactor_square_absorption hN.le _ _

theorem finePairDistanceFactor_square_integral_le {d : ℕ} (hd : 0 < d) {N : ℝ} (hN : 0 < N) :
    (∫ xy : Covariate d × Covariate d, finePairDistanceFactor N xy.1 xy.2 ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (volume.restrict (spatialPatchBox d))) ≤
      6 * (2 : ℝ) ^ d * spatialExponentialConstant d / N ^ d := by
  have hi := integral_mono (finePairDistanceFactor_square_integrable (d := d) hN)
    ((finePairDistance_exp_integrable (d := d) hN).const_mul 6)
    fun xy => finePairDistanceFactor_square_absorption hN.le xy.1 xy.2
  rw [integral_const_mul] at hi
  exact hi.trans ((mul_le_mul_of_nonneg_left (spatialPatchBox_pair_exponential_integral_le hd hN)
    (by norm_num : (0 : ℝ) ≤ 6)).trans_eq (by ring))

def finePairCountTwoRawNumerator {d F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (D M q : ℕ) (C a V η : ℝ)
    (U : Fin 2 → Covariate d) (p g w : Fin 2 → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) : ℝ :=
  finePairThreeRowFirstAction ad bd T0 N D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η ^ 2 * (p 0 * p 1) * ∑ i, (w i) ^ 2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

theorem finePairCountTwoRawNumerator_sum_square_le {d F : ℕ} [NeZero d] (hF : 3 ≤ F)
    (ad bd T0 N : ℝ) (haD : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q : ℕ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ρ : ℝ) (hC : C ≠ 0) (ha : 0 < a) (hρ : 0 ≤ ρ)
    (U : Fin 2 → Covariate d) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ)
    (hf : ∀ i, |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ) :
    (∑ y : Fin 2 → Fin 3, (finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y) ^ 2) ≤
      9 * (η ^ 2 * bd ^ 2 * ((2 * ρ + a) / a ^ 2) ^ 2) ^ 2 * finePairDistanceFactor N (U 0) (U 1) ^ 2 := by
  let L := (2 * ρ + a) / a ^ 2
  let d_fac := finePairDistanceFactor N (U 0) (U 1)
  have hd_fac : 0 ≤ d_fac := mul_nonneg
    (by have := exactEuclideanDistance_nonneg (U 0) (U 1); have := hT0.trans hN; positivity) (Real.exp_pos _).le
  have hb0 : 0 ≤ bd := (haD.trans hab).le
  have hL0 : 0 ≤ L := by dsimp [L]; positivity
  have hy (y : Fin 2 → Fin 3) :
      finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y ^ 2 ≤ (η ^ 2 * bd ^ 2 * L ^ 2 * d_fac) ^ 2 := by
    have habs : |finePairCountTwoRawNumerator ad bd T0 N D M q C a V η U p g w c y| ≤ η ^ 2 * bd ^ 2 * L ^ 2 * d_fac := by
      unfold finePairCountTwoRawNumerator
      rw [finePairThreeRow_count_two_numerator hF ad bd T0 N haD hab hT0 hN D M q hD hM hq C a V η hC U hU p hp g w c y]
      have hw01 : |w 0 * w 1| ≤ 1 := by
        rw [abs_mul]; exact (mul_le_mul (hw 0) (hw 1) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
      have hp01 : |p 0 * p 1| ≤ bd ^ 2 := by
        rw [abs_mul, pow_two]
        exact mul_le_mul (by rw [abs_of_pos (haD.trans_le (hp 0).1)]; exact (hp 0).2)
          (by rw [abs_of_pos (haD.trans_le (hp 1).1)]; exact (hp 1).2) (abs_nonneg _) hb0
      have hm0 := ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 0) (y 0)
      have hm1 := ternary_mean_derivative_abs_bound a _ ρ ha hρ (hf 1) (y 1)
      let f_reg := coefficientRegression η g w (fun i => highFrameFeature (U i)) c
      have hm01 : |ternaryMeanDerivative a (f_reg 0) (y 0) * ternaryMeanDerivative a (f_reg 1) (y 1)| ≤ L ^ 2 := by
        rw [abs_mul, pow_two]; exact mul_le_mul hm0 hm1 (abs_nonneg _) hL0
      have hprod := mul_le_mul (mul_le_mul hw01 hp01 (abs_nonneg _) zero_le_one) hm01
        (abs_nonneg _) (by positivity : 0 ≤ 1 * bd ^ 2)
      have hs := mul_le_mul_of_nonneg_left hprod (mul_nonneg (sq_nonneg η) hd_fac)
      change |η ^ 2 * w 0 * w 1 * p 0 * p 1 * d_fac * _ * _| ≤ _
      calc |η ^ 2 * w 0 * w 1 * p 0 * p 1 * d_fac * _ * _|
        _ = (η ^ 2 * d_fac) * ((|w 0 * w 1| * |p 0 * p 1|) * |_ * _|) := by
            simp only [abs_mul, abs_sq, abs_of_nonneg hd_fac]; ring
        _ ≤ (η ^ 2 * d_fac) * ((1 * bd ^ 2) * L ^ 2) := hs
        _ = _ := by ring
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr habs
  exact (Finset.sum_le_sum fun y _ => hy y).trans_eq (by simp [L, d_fac]; ring)

def ordinaryFineAliasRawAction {d n F : ℕ} (ad bd lam L T : ℝ) (M r q : ℕ)
    (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  densityCountCoefficient ad bd M r n *
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
      (∏ i ∈ S, p i) * responseMatrixAction q C
        (globalCardinalBandMatrix lam L T (spatialSubsetConfiguration S U)) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)

def ordinaryAliasResponseConstant (q : ℕ) (C a ρ : ℝ) : ℝ :=
  (2 * C ^ 2) * (∑ j : Fin (2 * q + 2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

theorem ordinaryFineAliasRawAction_abs_bound_of_chart {d n F M r R : ℕ}
    (ad bd c0 lam L T : ℝ) (haD : 0 < ad)
    (hshrink : ad + (M : ℝ)⁻¹ < bd - (M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hr : 1 ≤ r) (hrR : r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V η ρ : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc (ad + (M : ℝ)⁻¹) (bd - (M : ℝ)⁻¹))
    (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u) (y : Fin n → Fin 3) :
    |ordinaryFineAliasRawAction (ad + (M : ℝ)⁻¹) (bd - (M : ℝ)⁻¹) lam L T M r q C a V η U p g w c y| ≤
      ((1 + bd) ^ n * (1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R *
        Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a ρ * (n : ℝ) ^ 2 * η ^ 2) *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
          spatialMatrixL1 (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U)) := by
  let ad' := ad + (M : ℝ)⁻¹; let bd' := bd - (M : ℝ)⁻¹
  have ht : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hab : ad < bd := by linarith
  have hap : 0 < ad' := by dsimp [ad']; linarith
  have hbp : 0 < bd' := hap.trans hshrink
  have he : exteriorTau ((ad' + bd') / (bd' - ad')) = shrunkDensityExponent ad bd M :=
    exteriorTau_sqrt_ratio ad' bd' hap hshrink
  have hb_sh := ordinaryDensityActivityBase_shrunk_le haD ht hshrink htau
  have hterm (S : Finset (Fin n)) (hmem : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :
      |densityCountCoefficient ad' bd' M r n * (∏ i ∈ S, p i)| ≤
        (1 + bd) ^ n * (1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R *
          Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M) := by
    have hS : S.card = r := (Finset.mem_powersetCard.mp hmem).2
    have hcard : r ≤ n := by simpa only [hS, Finset.card_univ, Fintype.card_fin] using Finset.card_le_univ S
    have hm : 0 < |densityMargin ad' bd' 0| := abs_pos.mpr (densityMargin_zero_ne ad' bd' hap hshrink)
    have hτ : 0 ≤ exteriorTau ((ad' + bd') / (bd' - ad')) := by rw [he]; exact (densityIntervalExponent_pos hap hshrink).le
    have hprod : |∏ i ∈ S, p i| ≤ bd' ^ r := by
      rw [Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => by
        simpa only [abs_of_pos (hap.trans_le (hpD i).1)] using (hpD i).2).trans_eq (by rw [Finset.prod_const, hS])
    have hcoeff := densityCountCoefficient_abs_bound ad' bd' hap hshrink M r n hr
    have hcosh : Real.cosh ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) ≤
        Real.exp ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) := by
      rw [Real.cosh_eq]
      have := Real.exp_le_exp.mpr (show -((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) ≤
        ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) by linarith [mul_nonneg (Nat.cast_nonneg (M + r)) hτ])
      linarith
    have hj_le : (bd' - ad') / 4 ≤ bd' := by linarith [hap, hbp]
    have hb_act : (bd' - ad') / 4 / |densityMargin ad' bd' 0| * Real.exp (exteriorTau ((ad' + bd') / (bd' - ad'))) ≤
        ordinaryDensityActivityBase ad' bd' := by
      unfold ordinaryDensityActivityBase; rw [abs_div, abs_of_pos hbp]
      have hexp1 : Real.exp (exteriorTau ((ad' + bd') / (bd' - ad'))) ≤
          Real.exp (1 + exteriorTau ((ad' + bd') / (bd' - ad'))) := Real.exp_le_exp.mpr (by linarith)
      exact (mul_le_mul (div_le_div_of_nonneg_right hj_le hm.le) hexp1
        (Real.exp_pos _).le (div_nonneg hbp.le hm.le)).trans_eq (by ring)
    have h1 := mul_le_mul hcoeff hprod (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcosh
      (show 0 ≤ (bd' ^ (n - r) * ((bd' - ad') / 4) ^ r / |densityMargin ad' bd' 0| ^ r) * bd' ^ r by positivity)
    have hid : ((bd' ^ (n - r) * ((bd' - ad') / 4) ^ r / |densityMargin ad' bd' 0| ^ r) * bd' ^ r) *
        Real.exp ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) =
        bd' ^ n * (((bd' - ad') / 4 / |densityMargin ad' bd' 0|) * Real.exp (exteriorTau ((ad' + bd') / (bd' - ad')))) ^ r *
          Real.exp ((M : ℝ) * exteriorTau ((ad' + bd') / (bd' - ad'))) := by
      have heq : Real.exp ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) =
          Real.exp ((M : ℝ) * exteriorTau ((ad' + bd') / (bd' - ad'))) *
            Real.exp (exteriorTau ((ad' + bd') / (bd' - ad'))) ^ r := by
        rw [Nat.cast_add, add_mul, Real.exp_add]; congr 1
        simpa only [mul_comm] using Real.exp_nat_mul (exteriorTau ((ad' + bd') / (bd' - ad'))) r
      rw [heq]
      generalize (bd' - ad') / 4 = J
      generalize |densityMargin ad' bd' 0| = H
      generalize Real.exp (exteriorTau ((ad' + bd') / (bd' - ad'))) = X
      generalize Real.exp ((M : ℝ) * exteriorTau ((ad' + bd') / (bd' - ad'))) = Y
      rw [mul_pow, div_pow]
      have hpw : bd' ^ (n - r) * bd' ^ r = bd' ^ n := by rw [← pow_add, Nat.sub_add_cancel hcard]
      calc _ = (bd' ^ (n - r) * bd' ^ r) * (J ^ r / H ^ r) * X ^ r * Y := by ring
        _ = _ := by rw [hpw]; ring
    have h3 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb_act r) (pow_nonneg hbp.le n))
      (Real.exp_pos ((M : ℝ) * exteriorTau ((ad' + bd') / (bd' - ad')))).le
    have hraw_p : |densityCountCoefficient ad' bd' M r n * (∏ i ∈ S, p i)| ≤
        bd' ^ n * ordinaryDensityActivityBase ad' bd' ^ r * Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M) := by
      rw [← he]
      have h1' : |densityCountCoefficient ad' bd' M r n * (∏ i ∈ S, p i)| ≤
          (bd' ^ (n - r) * ((bd' - ad') / 4) ^ r / |densityMargin ad' bd' 0| ^ r) * bd' ^ r *
            Real.cosh ((M + r : ℕ) * exteriorTau ((ad' + bd') / (bd' - ad'))) := by
        simpa only [abs_mul, mul_assoc, mul_left_comm, mul_comm] using h1
      exact h1'.trans (h2.trans (hid.trans_le h3))
    have hB0 : 0 ≤ uniformOrdinaryDensityActivityBase ad bd c0 := by unfold uniformOrdinaryDensityActivityBase; positivity
    have hbase0 : 0 ≤ ordinaryDensityActivityBase ad' bd' := by unfold ordinaryDensityActivityBase; positivity
    exact hraw_p.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul (pow_le_pow_left₀ hbp.le (by dsimp [bd']; linarith) n)
        ((pow_le_pow_left₀ hbase0 (hb_sh.trans (by linarith)) r).trans (pow_le_pow_right₀ (by linarith) hrR))
        (pow_nonneg hbase0 r) (pow_nonneg (by linarith) n)) (Real.exp_pos _).le)
  unfold ordinaryFineAliasRawAction
  rw [Finset.mul_sum, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hmem => ?_)
  have hresp := high_response_matrix_all_count_bound q hn C a V η ρ
    (lt_of_lt_of_le zero_lt_one hC) ha hη hρ hηρ
    (globalCardinalBandMatrix (D := F) lam L T (spatialSubsetConfiguration S U))
    g w (fun i => highFrameFeature (U i)) c y hc hg hw
    (fun v hv i => highFrameProfile_abs_le_one C hC (U i) (hU i) v hv) hp
  have hh := mul_le_mul (hterm S hmem) hresp (abs_nonneg _)
    (by have hbd0 : 0 < bd := haD.trans hab; unfold uniformOrdinaryDensityActivityBase; positivity)
  simpa only [abs_mul, mul_assoc] using hh.trans_eq
    (by unfold ordinaryAliasResponseConstant highSeparatedDerivativeBudget spatialMatrixL1; ring)

theorem ordinaryFineAliasKernel_sum_square_integrable_and_le {d n F r : ℕ}
    (hd : 5 ≤ d) (hr : 2 ≤ r) {L T : ℝ} (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : Fin n → Covariate d =>
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U))) ^ 2) (fullSpatialPatchDesign d n) ∧
    (∫ U : Fin n → Covariate d,
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
        spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
          (spatialSubsetConfiguration S U))) ^ 2 ∂fullSpatialPatchDesign d n) ≤
      (n.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (n - r)) *
        ((r : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalBandSquareBudget d r L) := by
  let f (S : Finset (Fin n)) (V : Fin S.card → Covariate d) :=
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T V)
  have hf (S : Finset (Fin n)) : Measurable (f S) :=
    Finset.measurable_sum _ fun γ _ => Finset.measurable_sum _ fun δ _ =>
      (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT γ δ).measurable.abs
  have hs (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) : S.card = r :=
    (Finset.mem_powersetCard.mp hS).2
  have hi (S) (hS : S ∈ (Finset.univ : Finset (Fin n)).powersetCard r) :
      Integrable (fun V => f S V ^ 2) (fullSpatialPatchDesign d S.card) :=
    globalCardinalBandMatrix_square_integrable hd (by rw [hs S hS]; exact hr) hL hT hLT
  have h1 := finite_sum_abs_square_integrable (fullSpatialPatchDesign d n)
    ((Finset.univ : Finset (Fin n)).powersetCard r)
    (fun S U => f S (spatialSubsetConfiguration S U))
    (fun S _ => (hf S).comp (spatialSubsetConfiguration_measurable S))
    fun S hS => spatial_subset_square_integrable_enumerated S (f S) (hi S hS)
  refine ⟨by simpa only [f, abs_of_nonneg (spatial_matrix_l1_nonnegative _)] using h1,
    spatial_subset_sum_square_integral_le f _ (fun S _ => hf S) hi fun S hS => by
      simpa only [f, hs S hS] using
        globalCardinalBandMatrix_square_integral_le (D := F) hd (show 2 ≤ S.card by rw [hs S hS]; exact hr) hL hT hLT⟩

def ordinaryFineAliasSpatialBudget (d n M r R q : ℕ) (ad bd c0 C a ρ η L : ℝ) : ℝ :=
  (((1 + bd) ^ n * (1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R *
      Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M)) *
    (ordinaryAliasResponseConstant q C a ρ * (n : ℝ) ^ 2 * η ^ 2)) ^ 2 *
      ((n.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (n - r)) *
        ((r : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalBandSquareBudget d r L))

def ordinaryAliasSpatialPrefactor (d q R : ℕ) (ad bd c0 C a ρ : ℝ) : ℝ :=
  ((1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R) ^ 2 *
    ordinaryAliasResponseConstant q C a ρ ^ 2 * lowerAliasSpatialA d R

def ordinaryAliasSpatialCountBase (d : ℕ) (bd : ℝ) : ℝ := 64 * (2 : ℝ) ^ d * (1 + bd) ^ 2

def ordinaryAliasSpatialResponseBase (d : ℕ) (bd : ℝ) : ℝ := 3 * ordinaryAliasSpatialCountBase d bd

theorem ordinaryAliasSpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a ρ : ℝ) :
    0 ≤ ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ :=
  mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (lowerAliasSpatialA_nonneg d R)

theorem ordinaryFineAliasSpatialBudget_source_scale_le {d n M r R : ℕ}
    (hd : 5 ≤ d) (hrR : r ≤ R) {ad bd c0 C a ρ η D K N : ℝ}
    (hbd : 0 ≤ bd) (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0)
    (hDK : D ≤ K * M) (hN : 0 < N) (hell : 1 ≤ N * Real.exp (-c0 * D))
    (hH : Real.log (1 + Real.log N) ≤ M) (q : ℕ) :
    ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N * Real.exp (-c0 * D)) ≤
      ordinaryAliasSpatialPrefactor d q R ad bd c0 C a ρ *
        η ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M) * N ^ (4 - (d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K * M) * (ordinaryAliasSpatialCountBase d bd) ^ n := by
  have hkernel := cardinalBandSquareBudget_cutoff_le (by omega : 4 ≤ d) hrR
    (Nat.cast_nonneg M) hD hK hc0 hDK hN hell hH
  have hcount : ((1 + bd) ^ n) ^ 2 * (n : ℝ) ^ 4 * (n.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (n - r)) ≤
      (64 * (2 : ℝ) ^ d * (1 + bd) ^ 2) ^ n := by
    have hn : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
    have hc : (n.choose r : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.choose_le_two_pow n r
    have hn4 : (n : ℝ) ^ 4 ≤ (16 : ℝ) ^ n := by
      convert pow_le_pow_left₀ (Nat.cast_nonneg n) hn 4 using 1 <;> rw [← pow_mul, Nat.mul_comm n 4, pow_mul] <;> norm_num
    have hc2 : (n.choose r : ℝ) ^ 2 ≤ (4 : ℝ) ^ n := by
      convert pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2 using 1 <;> rw [← pow_mul, Nat.mul_comm n 2, pow_mul] <;> norm_num
    have hv : (2 : ℝ) ^ (d * (n - r)) ≤ ((2 : ℝ) ^ d) ^ n := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left d (Nat.sub_le n r))
    refine (mul_le_mul (mul_le_mul (mul_le_mul (le_refl (((1 + bd) ^ n) ^ 2)) hn4
      (by positivity) (by positivity)) hc2 (by positivity) (by positivity)) hv (by positivity) (by positivity)).trans_eq ?_
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]; congr 1; ring
  let P := ((1 + uniformOrdinaryDensityActivityBase ad bd c0) ^ R) ^ 2 *
    ordinaryAliasResponseConstant q C a ρ ^ 2 * η ^ 4 * Real.exp (2 * shrunkDensityExponent ad bd M * M)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have he : Real.exp ((M : ℝ) * shrunkDensityExponent ad bd M) ^ 2 = Real.exp (2 * shrunkDensityExponent ad bd M * M) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hid : ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a ρ η (N * Real.exp (-c0 * D)) =
      P * (((1 + bd) ^ n) ^ 2 * (n : ℝ) ^ 4 * (n.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (n - r))) *
        ((r : ℝ) ^ 2 * (2 : ℝ) ^ d * cardinalBandSquareBudget d r (N * Real.exp (-c0 * D))) := by
    unfold ordinaryFineAliasSpatialBudget P
    rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, he]; ring
  rw [hid]
  refine (mul_le_mul (mul_le_mul_of_nonneg_left hcount hP) hkernel
    (by unfold cardinalBandSquareBudget
        have := cardinalBandDimensionConstant_nonneg d
        have : 0 ≤ 1 + Real.log (N * Real.exp (-c0 * D)) := by linarith [Real.log_nonneg hell]
        positivity) (by positivity)).trans_eq ?_
  unfold P ordinaryAliasSpatialPrefactor ordinaryAliasSpatialCountBase; ring

def ordinaryFineAliasTargetSet (d D : ℕ) (L N mu : ℝ) : Finset ℕ :=
  (Finset.range (D + 1)).filter fun r => 3 ≤ r ∧ L < higherBandTargetScale d r N mu

def ordinaryFineAliasFamilyRawAction {d n F : ℕ} (I : Finset ℕ)
    (ad bd lam L : ℝ) (T : ℕ → ℝ) (M q : ℕ) (C a V eta : ℝ)
    (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) : ℝ :=
  ∑ r ∈ I, ordinaryFineAliasRawAction ad bd lam L (T r) M r q C a V eta U p g w c y

def ordinaryAliasFamilySpatialPrefactor (d q R : ℕ) (ad bd c0 C a rho : ℝ) : ℝ :=
  ((R + 1 : ℕ) : ℝ) ^ 2 * ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho

theorem ordinaryAliasFamilySpatialPrefactor_nonneg (d q R : ℕ) (ad bd c0 C a rho : ℝ) :
    0 ≤ ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho :=
  mul_nonneg (sq_nonneg _) (ordinaryAliasSpatialPrefactor_nonneg _ _ _ _ _ _ _ _ _)

structure OrdinaryFineAliasSaddleGuards (s : ℝ) (d : ℕ) (ad bd Cw x : ℝ) : Prop where
  dimension : 5 ≤ d
  shrunkInterval : ad + (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹ <
    bd - (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)⁻¹
  exponent : shrunkDensityExponent ad bd
    (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x) ≤ densityIntervalExponent ad bd + 1
  degree : (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ) ≤
    (((d : ℝ) + 8) / 4 + 1) * (lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x : ℝ)
  cutoff : 1 ≤ lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd + 1)
    (shrunkDensityExponent ad bd) x
  logarithm : Real.log (1 + Real.log (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
    (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)) ≤
      lowerSaddleM (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x
  targets : ∀ r ∈ ordinaryFineAliasTargetSet d
    (lowerSaddleD d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd)) x)
    (lowerAliasCutoff s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (densityIntervalExponent ad bd + 1)
      (shrunkDensityExponent ad bd) x)
    (lowerSaddleN s d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw (shrunkDensityExponent ad bd) x)
    (lowerSaddleMu d (lowerSaddleCoefficient s d (densityIntervalExponent ad bd))
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) Cw x),
    2 ≤ r ∧ r ≤ lowerAliasFineTargetBound d
      (lowerSaddleTheta s d (densityIntervalExponent ad bd)) (densityIntervalExponent ad bd + 1)

theorem eventually_ordinaryFineAlias_saddle_guards {s ad bd : ℝ} {d : ℕ}
    (hs : 1 < s) (hd : 4 * s < (d : ℝ)) (haD : 0 < ad) (hab : ad < bd) (Cw : ℝ) :
    ∀ᶠ x in atTop, OrdinaryFineAliasSaddleGuards s d ad bd Cw x := by
  let tau := densityIntervalExponent ad bd
  let m := lowerSaddleCoefficient s d tau
  have htau : 0 < tau := densityIntervalExponent_pos haD hab
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd htau
  have hM := lowerSaddleM_tendsto_atTop hm
  filter_upwards [actual_lowerAlias_hierarchy hs hd haD hab (Cact := 1) (Cs := 1) (by norm_num) (by norm_num) Cw,
    hM.eventually (eventually_ge_atTop (1 : ℝ)),
    hM.inv_tendsto_atTop.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < (bd - ad) / 2))] with x hh hM1 hsmall
  simp only [Pi.inv_apply] at hsmall
  rcases hh with ⟨hell, hτ, _, hlog, _, _, _, _, _, _, _, hactive⟩
  have hd0 : (0 : ℝ) < d := by linarith
  have hd5 : 5 ≤ d := by
    have h : (4 : ℝ) < d := by linarith
    have h' : 4 < d := by exact_mod_cast h
    omega
  refine ⟨hd5, by change ad + (lowerSaddleM m x : ℝ)⁻¹ < bd - (lowerSaddleM m x : ℝ)⁻¹; linarith,
    hτ, lowerSaddleD_le_fixed_linear hd0 hM1, hell.le, hlog, fun r hr => ?_⟩
  have hrmem := (Finset.mem_filter.mp hr).2
  exact ⟨by omega, hactive r hrmem.2⟩

end SpatialEnergies

-- 3. Source row activity & higher-band activity summation
--    (`FinePairRowActivity`, `SourceRowActivity`, `HighActivitySummation`, `SourceActivitySummation`)

section SourceActivities
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

def sourceResponseCost (q : ℕ) (C : ℝ) : ℝ := (∑ h : Fin (2 * q + 2), |responseWeight q h|) * (2 * C ^ 2)

theorem sourceResponseCost_nonneg (q : ℕ) (C : ℝ) : 0 ≤ sourceResponseCost q C := by
  unfold sourceResponseCost; positivity

theorem finePairRowMass_unit_le (d D M q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) :
    finePairRowMass d D M q a b C ℓ N .unit ≤
      ordinaryDensityActivityBase a b ^ 2 * (D : ℝ) ^ 2 *
        Real.exp ((D : ℝ) * exteriorTau ((a + b) / (b - a))) * sourceResponseCost q C := by
  rw [finePairRowMass_unit]
  have hm := mul_le_mul (densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD)
    (finePairUnitMatrix_l1_le d D) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (sourceResponseCost_nonneg q C)
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *; nlinarith only [hh]

theorem finePairRowMass_coarse_le (d : ℕ) [NeZero d] (D M q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) (hℓ : 0 ≤ ℓ) :
    finePairRowMass d D M q a b C ℓ N .coarse ≤
      ordinaryDensityActivityBase a b ^ 2 * (D : ℝ) ^ 2 *
        Real.exp ((D : ℝ) * exteriorTau ((a + b) / (b - a))) * sourceResponseCost q C *
          ((128 * (d : ℝ)) * ℓ ^ 2) := by
  rw [finePairRowMass_coarse d D M q a b C ℓ N hℓ]
  have hm := mul_le_mul (densityPacketWeight_exponential_cost a b ha hab D 2 D (by norm_num) hD)
    (mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D) (by positivity : 0 ≤ ℓ ^ 2 / 2))
    (by positivity : 0 ≤ (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * (ℓ ^ 2 / 2)) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (sourceResponseCost_nonneg q C)
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *; nlinarith only [hh]

theorem finePairRowMass_fine_le (d : ℕ) [NeZero d] (D M q : ℕ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C ℓ N : ℝ) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N) :
    finePairRowMass d D M q a b C ℓ N .fine ≤
      ordinaryDensityActivityBase a b ^ 2 *
        Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) * sourceResponseCost q C *
          ((256 * (d : ℝ)) * N ^ 2) := by
  rw [finePairRowMass_fine d D M q a b C ℓ N hℓ hℓN]
  have hden : (∑ h : FinePairDensityIndex M, |finePairDensityWeight a b M h|) ≤
      2 * ordinaryDensityActivityBase a b ^ 2 * Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) := by
    have hp : |finePairDensityPrefactor a b| = |b / densityMargin a b 0| ^ 2 := by
      simp only [finePairDensityPrefactor, abs_div, abs_pow, div_pow]
    have he : Real.exp (2 * exteriorTau ((a + b) / (b - a))) ≤ Real.exp (1 + exteriorTau ((a + b) / (b - a))) ^ 2 := by
      rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.mpr (by norm_num)
    refine (finePairDensityWeight_exponential_cost a b ha hab M).trans ?_
    rw [hp, ordinaryDensityActivityBase, mul_pow]
    have h0 := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * |b / densityMargin a b 0| ^ 2)
    exact mul_le_mul_of_nonneg_right (by nlinarith only [h0]) (Real.exp_pos _).le
  have hmat' : (∑ i, ∑ j, |finePairDistanceMatrix d D i j|) * ((N ^ 2 - ℓ ^ 2) / 2) ≤ (128 * (d : ℝ)) * N ^ 2 :=
    (mul_le_mul_of_nonneg_right (finePairDistanceMatrix_l1_le d D) (by nlinarith)).trans
      (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; nlinarith [sq_nonneg ℓ])
  have hh := mul_le_mul_of_nonneg_left
    (mul_le_mul hden hmat'
      (mul_nonneg (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (by nlinarith))
      (by positivity : 0 ≤ 2 * ordinaryDensityActivityBase a b ^ 2 * Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a)))))
    (sourceResponseCost_nonneg q C)
  dsimp [ordinaryDensityActivityBase, sourceResponseCost, spatialMatrixL1] at *; nlinarith only [hh]

theorem sourceRowTotalMass_eq (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass =
      highRowTotalMass (finePairRowData d k D M q a b C ℓ N).rowMass + singletonRowMass d D q a b C +
      highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass := by
  simp only [highRowTotalMass, Fintype.sum_sum_type, sourceRowData, sourceRowComponent,
    highUnionRowRestrict, Fintype.sum_unique, singletonRowData, higherBandFamilyData, add_assoc]

theorem higherBandFamily_activity_bound {d k D M q : ℕ} (hd : 0 < d) (hD : 1 ≤ D)
    (a b C lam ℓ N μ B q1 q2 : ℝ) (ha : 0 < a) (hab : a < b)
    (hℓ : 0 ≤ ℓ) (hN : 1 ≤ N) (hμ : 0 ≤ μ) (hbase1 : μ * (1 + Real.log N) ≤ 1)
    (hB : 0 ≤ B) (hbB : ordinaryDensityActivityBase a b ≤ B)
    (hq1 : q1 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1 + Real.log N) (μ * (1 + Real.log N)) 1)
    (hq2 : q2 = higherBandGeometricRatio d D
      (higherBandGeometricConstant B (higherBandInterpolationBase d lam)) (1 + Real.log N) (μ * (1 + Real.log N)) 2)
    (hq1h : q1 ≤ 1 / 2) (hq21 : q2 ≤ q1) (hsmall : (D : ℝ) ^ 2 * q1 ≤ 1)
    (hcoarse : Real.exp ((D : ℝ) * exteriorTau ((a + b) / (b - a))) * ℓ ≤ N) :
    highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass ≤
      4 * higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C) *
        N ^ 2 * Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hfin_tail {K qr : ℝ} (hK : 0 ≤ K) (hqr : 0 ≤ qr) (hqrh : qr ≤ 1 / 2) (m : ℕ)
      (Bv : Fin m → ℝ) (hBv : ∀ j, Bv j ≤ K * qr ^ (j.val + 1)) : (∑ j, Bv j) ≤ 2 * K * qr := by
    have hgeom : (∑ j ∈ Finset.range m, qr ^ (j + 1)) ≤ 2 * qr := by
      calc (∑ j ∈ Finset.range m, qr ^ (j + 1))
        _ = qr * ∑ j ∈ Finset.range m, qr ^ j := by simp_rw [pow_succ]; rw [Finset.mul_sum]; ring
        _ ≤ qr * ∑ j ∈ Finset.range m, (1 / (2 : ℝ)) ^ j :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => pow_le_pow_left₀ hqr hqrh j) hqr
        _ ≤ qr * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le m) hqr
        _ = 2 * qr := mul_comm _ _
    calc (∑ j, Bv j)
      _ ≤ ∑ j : Fin m, K * qr ^ (j.val + 1) := Finset.sum_le_sum fun j _ => hBv j
      _ = K * ∑ j ∈ Finset.range m, qr ^ (j + 1) :=
          (Finset.mul_sum _ _ _).symm.trans (congrArg (K * ·) (Fin.sum_univ_eq_sum_range (fun j => qr ^ (j + 1)) m))
      _ ≤ K * (2 * qr) := mul_le_mul_of_nonneg_left hgeom hK
      _ = 2 * K * qr := by ring
  let flt (i : Fin (D - 2) × Bool) : ℝ :=
    if HigherBandFamilySelected d D M q a b C lam ℓ N μ i then
      higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
        a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2 else 0
  have htot_eq : highRowTotalMass (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass =
      (∑ j : Fin (D - 2), flt (j, false)) + ∑ j : Fin (D - 2), flt (j, true) := by
    change (∑ i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ,
      higherBandRowMass d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
        a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2) = _
    rw [← Finset.sum_subtype (Finset.univ.filter (HigherBandFamilySelected d D M q a b C lam ℓ N μ))
      (by intro; simp) fun i => higherBandRowMass d (higherBandFamilyTarget i)
        (higherBandFamilyGuardDegree M i) D q a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2,
      Finset.sum_filter, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, flt, Finset.sum_add_distrib]; exact add_comm _ _
  let K := higherBandGeometricPrefactor B (higherBandInterpolationBase d lam) (sourceResponseCost q C)
  let ED := Real.exp ((D : ℝ) * exteriorTau ((a + b) / (b - a)))
  let EM := Real.exp ((M : ℝ) * exteriorTau ((a + b) / (b - a)))
  have hK : 0 ≤ K := by dsimp [K, higherBandGeometricPrefactor, higherBandInterpolationBase, sourceResponseCost]; positivity
  have hH : 0 ≤ 1 + Real.log N := by linarith [Real.log_nonneg hN]
  have hq10 : 0 ≤ q1 := by rw [hq1]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
  have hq20 : 0 ≤ q2 := by rw [hq2]; unfold higherBandGeometricRatio higherBandGeometricConstant higherBandInterpolationBase; positivity
  have hτ : 0 ≤ exteriorTau ((a + b) / (b - a)) := by
    apply exteriorTau_nonneg; apply (le_div_iff₀ (sub_pos.mpr hab)).mpr; linarith
  have hEM : 1 ≤ EM := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg M) hτ)
  have hc := hfin_tail (K := K * (D : ℝ) ^ 2 * ED * N * ℓ) (by positivity) hq10 hq1h (D - 2)
    (fun j => flt (j, false)) fun j => by
      dsimp only [flt]; split_ifs with hi
      · have hmass : higherBandRowMass d (j.val + 3) D D q a b C lam ℓ
            (min ℓ (higherBandTargetScale d (j.val + 3) N μ)) false ≤
            higherBandRowActivityCap d (j.val + 3) D D q a b C lam (min ℓ (higherBandTargetScale d (j.val + 3) N μ)) :=
          higherBandRowMass_le_activityCap d (j.val + 3) D D q (by omega) hD a b ha hab C lam 1
            (min ℓ (higherBandTargetScale d (j.val + 3) N μ)) hi.1 hi.1 false
        have hcap := higherBandRowActivityCap_coarse_geometric_le (r := j.val + 3) (D := D) (q := q)
          hd (by omega) a b C lam N μ ℓ B hN hμ hbase1 hi.1 hB hbB
        simpa [← hq1, K, ED, mul_assoc, higherBandFamilyTarget, higherBandFamilyGuardDegree,
          higherBandFamilyUpper, sourceResponseCost] using hmass.trans hcap
      · positivity
  have hf := hfin_tail (K := K * (D : ℝ) ^ 2 * EM * N ^ 2) (by positivity) hq20 (hq21.trans hq1h) (D - 2)
    (fun j => flt (j, true)) fun j => by
      dsimp only [flt]; split_ifs with hi
      · have hLT : ℓ ≤ higherBandTargetScale d (j.val + 3) N μ := by
          simpa [higherBandFamilyTarget] using (hi.2.1 rfl).le
        have hmass := higherBandRowMass_le_activityCap d (j.val + 3) M D q (by omega) hD a b ha hab C lam ℓ
          (higherBandTargetScale d (j.val + 3) N μ) hi.1 hLT true
        have hcap := higherBandRowActivityCap_fine_geometric_le (r := j.val + 3) (M := M) (D := D) (q := q)
          hd (by omega) a b C lam N μ B hN hμ hbase1 hi.1 hB hbB
        simpa [← hq2, K, EM, higherBandFamilyTarget, higherBandFamilyGuardDegree,
          higherBandFamilyUpper, sourceResponseCost] using hmass.trans hcap
      · positivity
  have hc' : (∑ j, flt (j, false)) ≤ 2 * K * N ^ 2 :=
    hc.trans <| by
      calc _ = (2 * K * N) * (ED * ℓ) * ((D : ℝ) ^ 2 * q1) := by ring
        _ ≤ (2 * K * N) * N * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoarse (by positivity)) hsmall (by positivity) (by positivity)
        _ = 2 * K * N ^ 2 := by ring
  have hf' : (∑ j, flt (j, true)) ≤ 2 * K * N ^ 2 * EM :=
    hf.trans <| by
      have hsm2 : (D : ℝ) ^ 2 * q2 ≤ 1 := (mul_le_mul_of_nonneg_left hq21 (sq_nonneg _)).trans hsmall
      calc _ = (2 * K * N ^ 2 * EM) * ((D : ℝ) ^ 2 * q2) := by ring
        _ ≤ (2 * K * N ^ 2 * EM) * 1 := mul_le_mul_of_nonneg_left hsm2 (by positivity)
        _ = _ := mul_one _
  rw [htot_eq]
  have hm := mul_le_mul_of_nonneg_left hEM (by positivity : 0 ≤ 2 * K * N ^ 2)
  change _ ≤ 4 * K * N ^ 2 * EM
  nlinarith only [hc', hf', hm]

end SourceActivities

-- 4. Raw packet decomposition, count cancellations & higher-band collapse
--    (`HighSourceRawDecomposition`, `HighSourceCountCancellation`, `HigherBandOmissions`,
--     `HigherBandTargetAction`, `HighSourceFineAliasIdentification`, `HigherBandFamilyCollapse`)

section RawPacketDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def higherBandFirstAction {d n : ℕ} (ad bd lam L T : ℝ) (r m D q : ℕ)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd m r D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
      (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ e
    ∂<•higherBandSignedRow d r m D q ad bd C lam L T fine

lemma higherBandFirstAction_count_expansion {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (separatedSubsetMatrix (higherBandCarrierMeasure d r L T fine) r
              (fun ζ i l => higherBandCarrierFactor d r lam fine ζ l (U i))
              (higherBandCarrierAmplitude d r D lam fine) S) c Φ := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hm (i : Fin n) (l : Fin r) : Measurable fun ζ => higherBandCarrierFactor d r lam fine ζ l (U i) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp (measurable_id.prodMk measurable_const)
  have hG (z : ℝ) (eps : Fin r → ℝ) : Measurable fun ζ =>
      ∏ i, localDensityReset ad bd r z eps p (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i :=
    Finset.measurable_fun_prod _ fun i _ =>
      measurable_const.add ((Finset.measurable_fun_sum _ fun l _ => (hm i l).const_mul (eps l)).const_mul _)
  have hb (ζ : HigherBandCarrier d r fine) (e : HighDensityMarkIndex m r D) (i : Fin n) :
      |localDensityReset ad bd r (densityPacketAtom ad bd m r D e).1 (densityPacketAtom ad bd m r D e).2 p
        (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le m r D e
    have hh := localDensityReset_mem_interval ad bd ha hab r hr _ he.1 _ he.2 p
      (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i (hp i)
      fun l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i)
    rw [abs_of_nonneg (ha.le.trans hh.1)]; exact hh.2
  have hpack : higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      highSeparatedPacketAction (higherBandCarrierMeasure d r L T fine)
        ad bd m r D q C (higherBandCarrierAmplitude d r D lam fine) c
        (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
          (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ :=
    highPacketSignedMeasure_factor_integral _ ad bd m r D q C _
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
      c _ hG (bd ^ n) (pow_nonneg (ha.trans hab).le n)
      (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb ζ e))
      Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)
  rw [hpack]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    highSeparatedPacketAction_row (higherBandCarrierMeasure d r L T fine) ad bd ha hab
      m r D q hr hD Finset.univ (by simpa using hnD) p _ hm
      (fun ζ i l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i)) C _
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine) c Φ

lemma higherBandFirstAction_zero_small_count {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD C fine U hU p hp c Φ,
    Finset.powersetCard_eq_empty.mpr (by simpa using hnr), Finset.sum_empty, mul_zero]

lemma higherBandFirstAction_zero_other_count {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q : ℕ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnm : n ≤ m) (hne : n ≠ r) (C : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  by_cases hnr : n < r
  · exact higherBandFirstAction_zero_small_count ad bd lam L T ha hab hT r m D q hr hD hnD hnr C fine U hU p hp c Φ
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD C fine U hU p hp c Φ,
    densityCountCoefficient_exact ad bd ha hab m r n hr (by omega) hnm, if_neg hne, zero_mul]

def higherBandActualMatrix {d n D : ℕ} (lam L T : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  if fine then globalCardinalBandMatrix lam L T U else integratedCardinalMatrix lam T U

lemma higherBandFirstAction_actual_count_expansion {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r m D q : ℕ) (hr : 2 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U)) c Φ := by
  have hcard_sym {S : Finset (Fin n)} (z : CardinalSeparatedMark d S.card) :
      densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z l (U i)) S =
        cardinalSeparatedSymmetricFactor lam z (spatialSubsetConfiguration S U) := by
    let e : Fin S.card ≃ S := ((Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))).symm
    rw [densitySeparatedSym_eq_permutation_average S.card _ S e]
    unfold cardinalSeparatedSymmetricFactor; congr 1
    refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin S.card))) _ _ fun τ => ?_
    have h := Equiv.prod_comp τ fun l => cardinalSeparatedFactor lam z l (U (e (τ.symm l)).val)
    simp only [Equiv.symm_apply_apply] at h
    convert h using 1
    exact Finset.prod_congr rfl fun _ _ => rfl
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q (by omega) hD hnD C fine U hU p hp c Φ]
  congr 1; refine Finset.sum_congr rfl fun S hS => ?_
  have he := (Finset.mem_powersetCard.mp hS).2
  subst r
  have hmat : separatedSubsetMatrix (higherBandCarrierMeasure d S.card L T fine) S.card
      (fun ζ i l => higherBandCarrierFactor d S.card lam fine ζ l (U i))
      (higherBandCarrierAmplitude d S.card D lam fine) S =
      higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U) := by
    have hb : ∀ l j, |spatialSubsetConfiguration S U l j| ≤ 2 := fun _ => hU _
    funext β β'
    cases fine
    · change (∫ z, densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z l (U i)) S *
        cardinalSeparatedAmplitude lam z β β' ∂cardinalSeparatedMeasure d S.card T) = _
      simp_rw [hcard_sym]
      exact (integrated_cardinal_symmetric_separated_exact lam hlam hT _ hb β β').symm
    · change (∫ z, densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z.2 l (U i)) S *
        cardinalBandAmplitude lam z β β' ∂cardinalBandMeasure d S.card L T) = _
      simp_rw [hcard_sym]
      exact (integrated_cardinal_actual_band_separated_exact hr lam hlam hL hT _ hb β β').symm
  rw [hmat]

theorem higherBandFirstAction_fine_eq_aliasRawAction {d n : ℕ}
    (ad bd lam L T : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r M D q : ℕ) (hr : 2 ≤ r)
    (hD : 1 ≤ D) (hnD : n ≤ D) (C a V η : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    higherBandFirstAction ad bd lam L T r M D q C true U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      ordinaryFineAliasRawAction ad bd lam L T M r q C a V η U p g w c y := by
  rw [higherBandFirstAction_actual_count_expansion ad bd lam L T ha hab hlam hL hT r M D q hr hD hnD C true U hU p hp c]
  simp only [ordinaryFineAliasRawAction, higherBandActualMatrix, ite_true]

def singletonFirstAction {d n : ℕ} (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 1 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 1 D q C (fun _ => finePairUnitMatrix d D)

lemma singletonFirstAction_eq_packet {d n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ =
      highSeparatedPacketAction (Measure.dirac ()) ad bd D 1 D q C
        (fun _ => finePairUnitMatrix d D) c
        (fun _ z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i) Φ := by
  have hb (e : HighDensityMarkIndex D 1 D) (i : Fin n) :
      |localDensityReset ad bd 1 (densityPacketAtom ad bd D 1 D e).1
        (densityPacketAtom ad bd D 1 D e).2 p (fun _ _ => 1) i| ≤ bd := by
    have he := densityPacketAtom_mem ad bd hab.le D 1 D e
    have hh := localDensityReset_mem_interval ad bd ha hab 1 (by norm_num) _ he.1 _ he.2 p
      (fun _ _ => 1) i (hp i) fun _ => by norm_num
    rw [abs_of_nonneg (ha.le.trans hh.1)]; exact hh.2
  exact highPacketSignedMeasure_factor_integral (Z := Unit) (ι := HighFrameIndex d D)
    (Measure.dirac ()) ad bd D 1 D q C
    (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
    c (fun (_ : Unit) z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i)
    (fun _ _ => measurable_const) (bd ^ n) (pow_nonneg (ha.trans hab).le n)
    (fun _ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)

theorem singletonFirstAction_zero_other_count {d n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (D q : ℕ) (hD : 1 ≤ D)
    (hnD : n ≤ D) (hne : n ≠ 1) (C : ℝ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ = 0 := by
  rw [singletonFirstAction_eq_packet ad bd ha hab D q C p hp c Φ]
  by_cases hn : n = 0
  · subst n; unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right,
      density_packet_product_zero_of_small_count (Finset.univ : Finset (Fin 0))
        ad bd ha hab D 1 D (by norm_num) hD (by simp) (by simp) p (fun _ _ => 1), zero_mul]
    exact integral_zero _ _
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg hne] using
    highSeparatedPacketAction_count_selector (Measure.dirac ()) ad bd ha hab D 1 D q
      (by norm_num) hD (Finset.univ : Finset (Fin n)) (by simpa using hnD)
      (by simpa using hnD) (by simpa using (show 1 ≤ n by omega)) p
      (fun _ : Unit => fun _ _ => (1 : ℝ)) (fun _ _ => measurable_const)
      (by intro _ _ _; norm_num) C (fun _ => finePairUnitMatrix d D)
      (fun _ _ => measurable_const) (integrable_const _) c Φ

def higherBandFamilyFirstAction {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
    higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
      (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ

def completeSourceSignedFirstAction {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
    singletonFirstAction ad bd D q C p c Φ +
    higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ

theorem completeSourceSignedFirstAction_eq_family {d n : ℕ}
    (ad bd lam ℓ N μ : ℝ) (D M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
      finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
        singletonFirstAction ad bd D q C p c Φ +
        higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ := rfl

def completeSourceRawNumerator {d n : ℕ} (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) : ℝ :=
  completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i

lemma higherBandFamilyFirstAction_zero_small_count {d n : ℕ}
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hD : 1 ≤ D) (hnD : n ≤ D) (hn : n ≤ 2) (C : ℝ)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ = 0 :=
  Finset.sum_eq_zero fun i _ => by
    have := (higherBandFamily_target_bounds d D M q ad bd C lam ℓ N μ i).1
    exact higherBandFirstAction_zero_small_count ad bd lam ℓ _ ha hab i.property.1
      _ _ D q (by omega) hD hnD (by omega) C i.val.2 U hU p hp c Φ

theorem completeSourceRawNumerator_count_zero {d : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hD : 1 ≤ D) (C a V η : ℝ)
    (U : Fin 0 → Covariate d) (p g w : Fin 0 → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin 0 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y = 0 := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count (by omega) ad bd ℓ N ha hab D M q hD C U p (fun i => Fin.elim0 i) c,
    singletonFirstAction_zero_other_count ad bd ha hab D q hD (by omega) (by omega) C p (fun i => Fin.elim0 i) c,
    higherBandFamilyFirstAction_zero_small_count ad bd lam ℓ N μ ha hab D M q hD
      (by omega) (by omega) C U (fun i => Fin.elim0 i) p (fun i => Fin.elim0 i) c]
  simp

theorem completeSourceRawNumerator_count_one {d : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd)
    (D M q : ℕ) (hD : 1 ≤ D) (hq : 1 ≤ q) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin 1 → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p g w : Fin 1 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin 1 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y = 0 := by
  have hsingle_one : singletonFirstAction ad bd D q C p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) =
      η ^ 2 * (∏ i, p i) * ∑ i, (w i) ^ 2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
    rw [singletonFirstAction_eq_packet ad bd ha hab D q C p hp c]
    unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right]
    have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 1))
      ad bd ha hab D 1 D (by norm_num) hD (by simpa using hD) (by simpa using hD) p (fun _ _ => 1)
    have hpow : (Finset.univ : Finset (Fin 1)).powersetCard 1 = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 1))
    have hsym1 : densitySeparatedSym 1 (fun _ _ => (1 : ℝ)) (Finset.univ : Finset (Fin 1)) = 1 := by
      let e : Fin 1 ≃ (Finset.univ : Finset (Fin 1)) :=
        ((Fintype.equivFin _).trans (finCongr ((Fintype.card_coe _).trans (by simp)))).symm
      rw [densitySeparatedSym_eq_permutation_average 1 _ _ e]; simp
    simp only [Finset.card_univ, Fintype.card_fin, ite_true, hpow, Finset.sum_singleton, hsym1, mul_one] at hh
    simp_rw [hh]; simp only [integral_dirac]
    rw [high_response_matrix_heat q hq C a V η (finePairUnitMatrix d D) hC
      (finePairUnitMatrix_symmetric d D) g w (fun i => highFrameFeature (U i)) c y (fun _ => 1)
      fun i l => by simp only [finePairUnitMatrix_kernel, Subsingleton.elim i l, ite_true]]
    simp only [mul_one]; ring
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    finePairThreeRowFirstAction_small_count (by omega) ad bd ℓ N ha hab D M q hD C U p hp c,
    higherBandFamilyFirstAction_zero_small_count ad bd lam ℓ N μ ha hab D M q hD hD (by omega) C U hU p hp c,
    hsingle_one]
  ring

theorem completeSourceRawNumerator_count_two {d : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (ha : 0 < ad) (hab : ad < bd) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (D M q : ℕ) (hD : 3 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin 2 → Covariate d)
    (hU : ∀ i j, |U i j| ≤ 2) (hQ : ∀ i, U i ∈ hyperplaneCube d)
    (p g w : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (y : Fin 2 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      η ^ 2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ad bd ha hab D q (by omega) (by omega) (by omega) C p hp c,
    higherBandFamilyFirstAction_zero_small_count ad bd lam ℓ N μ ha hab D M q (by omega) (by omega) (by omega) C U hU p hp c]
  simp only [add_zero, Fin.prod_univ_two]
  exact finePairThreeRow_count_two_numerator hD ad bd ℓ N ha hab hℓ hℓN D M q (by omega) hM hq C a V η hC U hQ p hp g w c y

lemma higherBand_coarse_below_one_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 0 < T) (hT1 : T < 1) : higherBandSignedRow d r m D q a b C lam L T false = 0 := by
  have hc : cardinalSeparatedMeasure d r T = 0 := by
    unfold cardinalSeparatedMeasure
    have h0 (i : Fin r) : centeredCardinalMeasure i d T = 0 := by
      simp only [centeredCardinalMeasure, spatialScaleMeasure,
        spatial_scale_domain_empty_below_one i hT hT1, Measure.restrict_empty, Measure.zero_prod]
    simp_rw [h0, Measure.map_zero]; exact Finset.sum_const_zero
  rw [higherBandSignedRow, higherBandCarrierMeasure, hc, highPacketSignedMeasure, Measure.zero_prod]
  ext1 s hs; rw [withDensityᵥ_apply (by simp : Integrable _ (0 : Measure _)) hs]; simp

def higherBandCoarseFirstAction {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (r D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  higherBandFirstAction ad bd lam ell (min ell (higherBandTargetScale d r N mu)) r D D q C false U p c Φ

def higherBandFineFirstAction {d n : ℕ} (ad bd lam ell N mu : ℝ)
    (r M D q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  if ell < higherBandTargetScale d r N mu then
    higherBandFirstAction ad bd lam ell (higherBandTargetScale d r N mu) r M D q C true U p c Φ else 0

theorem higherBandFamilyFirstAction_matched_and_fine_below {d n : ℕ}
    (ad bd lam ell N mu : ℝ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hell : 1 ≤ ell)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D - 2), 0 < higherBandTargetScale d (j.val + 3) N mu)
    (hFine : ∀ j : Fin (D - 2), ell < higherBandTargetScale d (j.val + 3) N mu → j.val + 3 ≤ M)
    (C : ℝ) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ +
      ∑ j : Fin (D - 2), if j.val + 3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ else 0 := by
  have hD : 1 ≤ D := by omega
  have hell0 : 0 < ell := by linarith
  let phys (i : Fin (D - 2) × Bool) : ℝ :=
    if i.2 = true then
      if ell < higherBandTargetScale d (higherBandFamilyTarget i) N mu then
        higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
          (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ else 0
    else higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i)
      (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q C i.2 U p c Φ
  have hcf_split : higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c Φ =
      (∑ j : Fin (D - 2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val + 3) D q C U p c Φ) +
      ∑ j : Fin (D - 2), higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ := by
    have hset : higherBandFamilyFirstAction ad bd lam ell N mu D M q C U p c Φ = ∑ i : Fin (D - 2) × Bool, phys i := by
      refine (Finset.sum_congr_set {i | HigherBandFamilySelected d D M q ad bd C lam ell N mu i} phys
        (fun i => higherBandFirstAction ad bd lam ell (higherBandFamilyUpper d ell N mu i.val)
          (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ)
        (fun i hi => by
          dsimp only [phys]; by_cases hf : i.2 = true
          · rw [ite_eq_left hf, ite_eq_left (hi.2.1 hf)]
          · rw [ite_eq_right hf])
        fun ⟨j, fine⟩ hi => ?_).symm
      cases fine
      · simp only [phys, Bool.false_eq_true, ite_false]
        have hT := lt_min hell0 (hnu j)
        by_cases hT1 : 1 ≤ min ell (higherBandTargetScale d (j.val + 3) N mu)
        · have hz : higherBandRowMass d (j.val + 3) D D q ad bd C lam ell
              (min ell (higherBandTargetScale d (j.val + 3) N mu)) false = 0 :=
            le_antisymm (le_of_not_gt fun hp0 => hi ⟨hT1, (fun h => by cases h),
              (by simp only [higherBandFamilyTarget, higherBandFamilyGuardDegree, Bool.false_eq_true, ↓reduceIte]
                  have := j.isLt; omega), hp0⟩)
              (higherBandRowMass_nonneg d (j.val + 3) D D q ad bd C lam ell _ false)
          have hzero : higherBandSignedRow d (higherBandFamilyTarget (j, false))
              (higherBandFamilyGuardDegree M (j, false)) D q ad bd C lam ell
              (higherBandFamilyUpper d ell N mu (j, false)) false = 0 :=
            higherBand_zero_mass_signed_zero d (j.val + 3) D D q ad bd C lam ell _ hT1 false hz
          unfold higherBandFirstAction; rw [hzero]; simp
        · have hzero : higherBandSignedRow d (higherBandFamilyTarget (j, false))
              (higherBandFamilyGuardDegree M (j, false)) D q ad bd C lam ell
              (higherBandFamilyUpper d ell N mu (j, false)) false = 0 :=
            higherBand_coarse_below_one_signed_zero d (j.val + 3) D D q ad bd C lam ell _ hT (not_le.mp hT1)
          unfold higherBandFirstAction; rw [hzero]; simp
      · simp only [phys, ite_true, higherBandFamilyTarget]
        by_cases hact : ell < higherBandTargetScale d (j.val + 3) N mu
        · rw [ite_eq_left hact]
          have hT1 := hell.trans hact.le
          have hz : higherBandRowMass d (j.val + 3) M D q ad bd C lam ell
              (higherBandTargetScale d (j.val + 3) N mu) true = 0 :=
            le_antisymm (le_of_not_gt fun hp0 => hi ⟨hT1, fun _ => hact, hFine j hact, hp0⟩)
              (higherBandRowMass_nonneg d (j.val + 3) M D q ad bd C lam ell _ true)
          have hzero : higherBandSignedRow d (j.val + 3)
              (higherBandFamilyGuardDegree M (j, true)) D q ad bd C lam ell
              (higherBandFamilyUpper d ell N mu (j, true)) true = 0 :=
            higherBand_zero_mass_signed_zero d (j.val + 3) M D q ad bd C lam ell _ hT1 true hz
          unfold higherBandFirstAction; rw [hzero]; simp
        · rw [ite_eq_right hact]
    rw [hset, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, phys, higherBandFamilyTarget, higherBandFamilyUpper, higherBandFamilyGuardDegree,
      Bool.false_eq_true, ite_false, ite_true, higherBandCoarseFirstAction, higherBandFineFirstAction, Finset.sum_add_distrib]
    exact add_comm _ _
  let b : Fin (D - 2) := ⟨n - 3, by omega⟩
  have hb : b.val + 3 = n := by dsimp [b]; omega
  have hcSum : (∑ j : Fin (D - 2), higherBandCoarseFirstAction ad bd lam ell N mu (j.val + 3) D q C U p c Φ) =
      higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ := by
    rw [Finset.sum_eq_single b (fun j _ hj => ?_) (fun h => (h (Finset.mem_univ b)).elim), hb]
    have hne : n ≠ j.val + 3 := fun h => hj (Fin.ext (by dsimp [b]; omega))
    unfold higherBandCoarseFirstAction
    by_cases hT : 1 ≤ min ell (higherBandTargetScale d (j.val + 3) N mu)
    · exact higherBandFirstAction_zero_other_count ad bd lam ell _ ha hab hT
        (j.val + 3) D D q (by omega) hD hnD hnD hne C false U hU p hp c Φ
    · unfold higherBandFirstAction
      rw [higherBand_coarse_below_one_signed_zero d (j.val + 3) D D q ad bd C lam ell _ (lt_min hell0 (hnu j)) (not_le.mp hT)]
      simp
  have hfSum : (∑ j : Fin (D - 2), higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ) =
      higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ +
      ∑ j : Fin (D - 2), if j.val + 3 < n then
        higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ else 0 := by
    have hfPt (j : Fin (D - 2)) :
        higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ =
          (if j = b then higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ else 0) +
          (if j.val + 3 < n then higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ else 0) := by
      by_cases hj : j = b
      · subst j; simp only [hb, ite_true, lt_self_iff_false, ite_false, add_zero]
      · by_cases hlt : j.val + 3 < n
        · simp only [ite_eq_right hj, ite_eq_left hlt, zero_add]
        · have hgt : n < j.val + 3 := by have : j.val + 3 ≠ n := fun he => hj (Fin.ext (by dsimp [b]; omega)); omega
          have hz : higherBandFineFirstAction ad bd lam ell N mu (j.val + 3) M D q C U p c Φ = 0 := by
            unfold higherBandFineFirstAction; split_ifs with hact
            · exact higherBandFirstAction_zero_small_count ad bd lam ell _ ha hab (hell.trans hact.le)
                (j.val + 3) M D q (by omega) hD hnD hgt C true U hU p hp c Φ
            · rfl
          simp only [ite_eq_right hj, ite_eq_right hlt, add_zero, hz]
    rw [Finset.sum_congr rfl fun j _ => hfPt j, Finset.sum_add_distrib]; simp
  have hnupos : 0 < higherBandTargetScale d n N mu := by simpa only [hb] using hnu b
  have hFineN : ell < higherBandTargetScale d n N mu → n ≤ M := by simpa only [hb] using hFine b
  have htarget_act {T : ℝ} (hT : 1 ≤ T) {m : ℕ} (hnm : n ≤ m) (fine : Bool) :
      higherBandFirstAction ad bd lam ell T n m D q C fine U p c Φ =
        (∏ i, p i) * responseMatrixAction q C (higherBandActualMatrix lam ell T fine U) c Φ := by
    have hfull_sub : (higherBandActualMatrix lam ell T fine (spatialSubsetConfiguration Finset.univ U) :
        HighFrameIndex d D → _ → ℝ) = higherBandActualMatrix lam ell T fine U := by
      have hcard_full (T' : ℝ) (β β' : HighFrameIndex d D) :
          integratedCardinalMatrix lam T' (spatialSubsetConfiguration Finset.univ U) β β' =
            integratedCardinalMatrix lam T' U β β' := by
        let S : Finset (Fin n) := Finset.univ
        have hSc : S.card = n := by simp [S]
        let e : Fin S.card ≃ S := (finCongr (Fintype.card_coe S).symm).trans (Fintype.equivFin S).symm
        let v : S ≃ Fin n := ⟨Subtype.val, fun j => ⟨j, Finset.mem_univ j⟩, fun _ => rfl, fun _ => rfl⟩
        let τ : Equiv.Perm (Fin n) := ((finCongr hSc).symm.trans e).trans v
        have hcast {m' : ℕ} (hm' : m' = n) (W : Fin n → Covariate d) :
            integratedCardinalMatrix lam T' (W ∘ finCongr hm') β β' = integratedCardinalMatrix lam T' W β β' := by
          subst hm'; rfl
        have hc_cfg : spatialSubsetConfiguration S U = (U ∘ τ) ∘ finCongr hSc := funext fun _ => rfl
        rw [hc_cfg, hcast hSc]; exact integrated_cardinal_matrix_perm τ lam T' U β β'
      funext β β'
      cases fine <;> simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
        globalCardinalBandMatrix, hcard_full]
    rw [higherBandFirstAction_actual_count_expansion ad bd lam ell T ha hab hlam hell0 hT n m D q (by omega) hD hnD C fine U hU p hp c Φ,
      densityCountCoefficient_exact ad bd ha hab m n n (by omega) le_rfl hnm]
    have hS : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
    simp only [ite_true, hS, Finset.sum_singleton, one_mul, hfull_sub]
  have hmatched : higherBandCoarseFirstAction ad bd lam ell N mu n D q C U p c Φ +
      higherBandFineFirstAction ad bd lam ell N mu n M D q C U p c Φ =
      (∏ i, p i) * responseMatrixAction q C (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U) c Φ := by
    by_cases hT : 1 ≤ higherBandTargetScale d n N mu
    · unfold higherBandCoarseFirstAction higherBandFineFirstAction
      rw [htarget_act (le_min hell hT) hnD false]
      by_cases hact : ell < higherBandTargetScale d n N mu
      · rw [ite_eq_left hact, htarget_act hT (hFineN hact) true]
        simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, ite_true,
          min_eq_left hact.le, globalCardinalBandMatrix]
        rw [← mul_add, ← responseMatrixAction_matrix_add]
        congr 2; funext _ _; unfold globalCardinalBandMatrix; ring
      · rw [ite_eq_right hact]
        simp only [higherBandActualMatrix, Bool.false_eq_true, ite_false, min_eq_right (le_of_not_gt hact), add_zero]
    · have hTlt := not_le.mp hT
      have hmin : min ell (higherBandTargetScale d n N mu) = higherBandTargetScale d n N mu :=
        min_eq_right (hTlt.le.trans hell)
      unfold higherBandCoarseFirstAction higherBandFineFirstAction higherBandFirstAction
      rw [higherBand_coarse_below_one_signed_zero d n D D q ad bd C lam ell _ (lt_min hell0 hnupos)
        (by rw [hmin]; exact hTlt), ite_eq_right (show ¬ ell < higherBandTargetScale d n N mu by linarith)]
      simp only [VectorMeasure.integral_zero_vectorMeasure, add_zero]
      rw [show (integratedCardinalMatrix lam (higherBandTargetScale d n N mu) U : HighFrameIndex d D → _ → ℝ) =
        fun _ _ => 0 from funext fun i => funext fun j =>
          integrated_cardinal_matrix_below_one_eq_zero ⟨0, by omega⟩ lam hnupos hTlt U i j]
      simp [responseMatrixAction, covarianceAction, covarianceWeight]
  rw [hcf_split, hcSum, hfSum, ← add_assoc, hmatched]

end RawPacketDecomposition

-- 5. Complete-source union signed action & all-count field tail
--    (`HighSourceUnionAction`, `HighSourceCanonicalAction`, `HighCompleteSourceTail`, `HighCompleteSourceFrameTail`)

section UnionActionAndTail
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

def sourceRowSignedMeasure (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SignedMeasure (SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl .unit => highPacketSignedMeasure (Measure.dirac ()) a b D 2 D q C (fun _ => finePairUnitMatrix d D)
  | .inl .coarse => highPacketSignedMeasure (finePairTimeFieldMeasure d 0 ℓ) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inl .fine => finePairPacketSignedMeasure (finePairTimeFieldMeasure d ℓ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inr (.inl _) => highPacketSignedMeasure (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
  | .inr (.inr i) => higherBandSignedRow d (higherBandFamilyTarget i.val)
      (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2

def highMarkedLocalScoreNumerator {ι E : Type*} [Fintype ι] [MeasurableSpace E] {n : ℕ}
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η ^ 2 * (∏ u, p u) * ∑ u, (w u) ^ 2 * highResponseVarianceTerm a V η g w φ c y u

theorem completeSourceNumerator_original_field_bound {d : ℕ} [NeZero d]
    (C : ModelConstants d) (Q : LowSmoothnessTernaryConstants C) :
    ∃ Cfr0 η0 : ℝ, 1 ≤ Cfr0 ∧ 0 < η0 ∧
      ∀ k D M q n : ℕ, ∀ (_ : NeZero k), ∀ (_ : LinearOrder (HighWindowLabels d k)),
      4 ≤ k → 3 ≤ D → 1 ≤ q → 1 ≤ n →
      highCenterResolutionThreshold C ≤ (M : ℝ) →
      ∀ Cfr lam ℓ N μ cf : ℝ, Cfr0 ≤ Cfr → 0 < ℓ → ℓ < N → 0 ≤ cf →
      cf * (k : ℝ) ^ (-C.smoothness) ≤ η0 →
      ∀ V : ℝ, |V - Q.v| ≤ Q.ρ →
      ∀ j : HighWindowLabels d k,
      ∀ h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
        (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ)),
      ∀ x : Fin n → Covariate d, ∀ y : Fin n → Fin 3,
      let R := completeSourceRows C k D M q Cfr lam ℓ N μ
      let η := cf * (k : ℝ) ^ (-C.smoothness)
      let c := (highUnionSourceState C R h).2
      |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) Q.a V η
        (fun u => highUnionSourceDensity C R h (x u))
        (fun e u => highUnionSourceResetDensity C R j h e (x u))
        (highUnionSourceResetCoefficient C R j h)
        (fun u => highLocalFieldWithout d k D η c j (x u))
        (fun u => highPeriodicTensor d k j (x u))
        (fun u => highLocalFrameFeature k j (x u)) (c j) y| ≤
        (highSeparatedScoreExponentialConstant Q.a Q.ρ C.densityUpper 1 1) ^ n *
          η ^ 2 * (highRowTotalMass R.rowMass + 1) := by
  obtain ⟨Cfr0, hfr0, hfield⟩ := highFrameField_original_model_bounds C
  let η0 := Q.ρ / (2 * ((2 : ℝ) ^ d + 1))
  refine ⟨Cfr0, η0, hfr0, div_pos Q.ρ_pos (by positivity),
    fun k D M q n hk0 horder hk hD hq hn hM Cfr lam ℓ N μ cf hfr hℓ hℓN hcf hη V hV j h x y => ?_⟩
  letI := hk0; letI := horder
  let ad := C.densityLower + 1 / (M : ℝ); let bd := C.densityUpper - 1 / (M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  have hCfr : 1 ≤ Cfr := hfr0.trans hfr
  have hCf : 0 < Cfr := by linarith
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let g := fun u : Fin n => highLocalFieldWithout d k D η c j (x u)
  let w := fun u : Fin n => highPeriodicTensor d k j (x u)
  let φ : Fin n → HighFrameIndex d D → ℝ := fun u => highLocalFrameFeature k j (x u)
  have hηn : 0 ≤ η := by dsimp [η]; positivity
  have hamp : ((2 : ℝ) ^ d + 1) * η ≤ Q.ρ / 2 := by
    have ht := (le_div_iff₀ (by positivity : 0 < 2 * ((2 : ℝ) ^ d + 1))).mp hη; nlinarith
  have hηρ : η ≤ Q.ρ / 2 := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) d]
  have hP (l) : frameCoefficientL1 (highFramePolynomial (c l)) ≤ Cfr0⁻¹ :=
    (highFramePolynomial_coefficientL1_le _).trans
      ((highUnionSourceState_coefficient_ball C R G h l).trans ((inv_le_inv₀ hCf (by linarith)).mpr hfr))
  have hF := (hfield k hk0 hk cf hcf (fun l => highFramePolynomial (c l)) hP).1
  have hw (u) : |w u| ≤ 1 := by
    rw [abs_of_nonneg (highPeriodicTensor_nonneg d k j (x u))]
    exact highPeriodicTensor_le_one d k (by omega) j (x u)
  have hφ (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) (u) : |∑ γ, φ u γ * v γ| ≤ 1 :=
    highLocalFrameFeature_ball_abs_le_one k j (x u) Cfr hCfr v hv
  have hc_ball := highUnionSourceState_coefficient_ball C R G h j
  have hg (u) : |g u| ≤ Q.ρ / 2 := by
    have hh : |η * w u * (∑ γ, φ u γ * c j γ)| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) (hφ (c j) hc_ball u) (abs_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    have hd := highFrameField_local_decomposition d k D hk η c j (x u)
    rw [show g u = highFrameField d k η (fun l => highFramePolynomial (c l)) (x u) -
      η * w u * (∑ γ, φ u γ * c j γ) by dsimp [g, w, φ]; linarith [hd]]
    exact (abs_sub _ _).trans ((add_le_add (hF (x u)) hh).trans (by nlinarith only [hamp]))
  have hp_mass (f : ℝ) (hf : |f| ≤ Q.ρ) (z : Fin 3) : 0 ≤ ternaryMass Q.a f V z :=
    Q.c_pos.le.trans ((Q.legal f V hf hV).2.2.1 z)
  have hresp_ball (v : HighFrameIndex d D → ℝ) (hv : ∑ γ, |v γ| ≤ Cfr⁻¹) :
      |highResponseProduct Q.a V η g w φ v y| ≤ 1 := by
    refine highMarkedResponseProduct_abs_le_one Q.a V η Q.a_pos.ne' g w φ v (fun u b => hp_mass _ ?_ b) y
    have hh : |η * w u * (∑ γ, φ u γ * v γ)| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) (hφ v hv u) (abs_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    change |g u + η * w u * (∑ γ, φ u γ * v γ)| ≤ Q.ρ
    exact (abs_add_le _ _).trans (by linarith [hg u])
  obtain ⟨had, hadbd⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq ad bd had hadbd Cfr hCf lam ℓ N μ hℓ hℓN
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) := highUnionMark_standardBorel
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0, by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀, β₀), (false, false), 0)
  let reset (i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ)
      (z : SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ i) (u : Fin n) : ℝ :=
    highUnionSourceResetDensity C R j h (Sum.inl ⟨i, sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u)
  have hresetMeas (i u) : Measurable fun z => reset i z u :=
    (highUnionSourceResetDensity_measurable C R G j h).comp
      ((measurable_inl.comp ((rowSigmaMk_measurable i).comp
        (sourceRowDensityLift_measurable d D M q ad bd Cfr lam ℓ N μ r₀ i))).prodMk measurable_const)
  have hirrel (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i, e⟩) (x u) =
      reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e) u := by
    dsimp only [reset]; unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append, highUnionSourceState_append]
    change (if x u ∈ highTorusPatch d k j then R.rowSlope j i e (x u) * _ + R.rowIntercept i e else _) =
      (if x u ∈ highTorusPatch d k j then R.rowSlope j i _ (x u) * _ + R.rowIntercept i _ else _)
    simp only [R, completeSourceRows, ad, bd]
    rw [sourceRow_density_projection_slope d k D M q ad bd Cfr lam ℓ N μ r₀ j i e (x u),
      sourceRow_density_projection_intercept d k D M q ad bd Cfr lam ℓ N μ r₀ i e]
  let O (e) := (∏ u, highUnionSourceResetDensity C R j h e (x u)) *
    highResponseProduct Q.a V η g w φ (highUnionSourceResetCoefficient C R j h e) y
  have hmO : Measurable O := (Finset.measurable_fun_prod _ fun _ _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const)).mul
      (highMarkedResponseProduct_measurable Q.a V η _ (highUnionSourceResetCoefficient_measurable C R G j h) g w φ y)
  have hbU0 : 0 ≤ C.densityUpper := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hOb (e) : ‖O e‖ ≤ C.densityUpper ^ n := by
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u)) * highResponseProduct Q.a V η g w φ _ y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ C.densityUpper hbU0
      fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u))
      (hresp_ball _ (highUnionResponseReset_ball R Cfr hCf G.vector_ball G.time_interval e (c j) hc_ball))
      (abs_nonneg _) (pow_nonneg hbU0 _)).trans_eq (mul_one _)
  have haction : |highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) Q.a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y| ≤
      (C.densityUpper ^ n * highSeparatedDerivativeBudget Q.a Q.ρ * (n : ℝ) ^ 2 * η ^ 2) * highRowTotalMass R.rowMass := by
    have he_act : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
        (highUnionActivation R (highCenterMix C)) Q.a V η
        (fun e u => highUnionSourceResetDensity C R j h e (x u))
        (highUnionSourceResetCoefficient C R j h) g w φ y =
        ∑ i, highMarkedResponseAction (R.rowLaw i) (R.rowActivation i) Q.a V η
          (fun e => reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e))
          (fun e => coefficientReset (c j) (R.rowVector i e) (R.rowTime i e)) g w φ y := by
      unfold highMarkedResponseAction; simp_rw [mul_assoc]
      rw [highUnionSource_bounded_action C R G hpos O hmO (C.densityUpper ^ n) hOb]
      exact Finset.sum_congr rfl fun i _ => integral_congr_ae <| Filter.Eventually.of_forall fun e => by
        simp only [O, hirrel, highUnionSourceResetCoefficient, highUnionResponseReset,
          highUnionResponseVector, highUnionResponseTime, Sum.elim_inl]
        ring
    rw [he_act]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ =>
      sourceRow_reference_all_count_bound d k D M q hn ad bd Cfr lam ℓ N μ Q.a V η Q.ρ C.densityUpper
        hCf Q.a_pos hηn Q.ρ_pos.le hηρ hbU0 hpos i (reset i) (hresetMeas i)
        (fun _ _ => highUnionSourceResetDensity_abs_le C R G j h _ _)
        g w φ (c j) hc_ball hg hw hφ hp_mass y).trans_eq (Finset.mul_sum ..).symm)
  have hpCurrent (u b) : 0 ≤ ternaryMass Q.a (coefficientRegression η g w φ (c j) u) V b := by
    refine hp_mass _ ?_ b
    have hh : |η * w u * (∑ γ, φ u γ * c j γ)| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_nonneg hηn]
      have ht := mul_le_mul (hw u) (hφ (c j) hc_ball u) (abs_nonneg _) zero_le_one
      nlinarith [mul_le_mul_of_nonneg_left ht hηn]
    change |g u + η * w u * (∑ γ, φ u γ * c j γ)| ≤ Q.ρ
    exact (abs_add_le _ _).trans (by linarith [hg u])
  have hIncoming (u) : |highUnionSourceDensity C R h (x u)| ≤ C.densityUpper := by
    have hi := highUnionSourceDensity_coarse_interval C R G h (x u)
    rw [abs_of_nonneg (C.densityLower_pos.le.trans hi.1)]; exact hi.2
  have hcorrection := high_response_variance_correction_abs_bound hn Q.a V η C.densityUpper
    Q.a_pos hbU0 (fun u => highUnionSourceDensity C R h (x u)) g w φ (c j) hw hIncoming hpCurrent y
  have hraw : |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) Q.a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ (c j) y| ≤
      C.densityUpper ^ n * (highSeparatedDerivativeBudget Q.a Q.ρ * highRowTotalMass R.rowMass + 1 / Q.a ^ 2) *
        (n : ℝ) ^ 2 * η ^ 2 := by
    unfold highMarkedLocalScoreNumerator
    exact ((abs_sub _ _).trans (add_le_add haction hcorrection)).trans_eq (by ring)
  exact hraw.trans (by
    simpa only [mul_one, div_one] using highSeparated_score_budget_absorb n hn Q.a Q.ρ C.densityUpper
      1 1 η (highRowTotalMass R.rowMass) hbU0 (by norm_num) (by norm_num) G.total_positive.le)

end UnionActionAndTail

section CanonicalSignedAction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

lemma completeSourceUnion_signed_action {d k D M q : ℕ} [NeZero d]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (F : HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
      (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ) → ℝ) (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e * F e ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ᵛ e, F (Sum.inl ⟨i, e⟩)
        ∂<•sourceRowSignedMeasure d k D M q (C.densityLower + 1 / (M : ℝ))
          (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ i := by
  dsimp only
  let a := C.densityLower + 1 / (M : ℝ); let b := C.densityUpper - 1 / (M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  obtain ⟨ha, hab⟩ := high_source_interval_numeric C (M : ℝ) hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq a b ha hab Cfr (by linarith) lam ℓ N μ hℓ hℓN
  rw [highUnionSource_bounded_action C R G hpos F hF L hFbound]
  refine Finset.sum_congr rfl fun i _ => ?_
  let Fi (e : SourceRowMark d D M q a b Cfr lam ℓ N μ i) := F (Sum.inl ⟨i, e⟩)
  have hFi : Measurable Fi := hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))
  have hFib (e) : ‖Fi e‖ ≤ L := hFbound _
  cases i with
  | inl p =>
    cases p
    · exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
        (highPacketMarkWeight a b D 2 D q Cfr (fun _ => finePairUnitMatrix d D))
        (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 2 D q Cfr _ (fun _ _ => measurable_const) (integrable_const _))
        (highPacketMarkWeight_measurable a b D 2 D q Cfr _ fun _ _ => measurable_const)
        (hpos (.inl .unit)) Fi hFi L hFib
    · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d 0 ℓ).prod Measure.count)
        (highPacketMarkWeight a b D 2 D q Cfr (finePairTimeMatrix d (finePairDistanceMatrix d D)))
        (highPacketMarkWeight_integrable _ a b D 2 D q Cfr _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 ℓ _))
        (highPacketMarkWeight_measurable a b D 2 D q Cfr _ (finePairTimeMatrix_measurable d _))
        (hpos (.inl .coarse)) Fi hFi L hFib
    · exact absoluteMarkLaw_signed_action ((finePairTimeFieldMeasure d ℓ N).prod Measure.count)
        (finePairPacketWeight a b M q Cfr (finePairTimeMatrix d (finePairDistanceMatrix d D)))
        (finePairPacketWeight_integrable _ a b M q Cfr _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d ℓ N _))
        (finePairPacketWeight_measurable a b M q Cfr _ (finePairTimeMatrix_measurable d _))
        (hpos (.inl .fine)) Fi hFi L hFib
  | inr i =>
    cases i with
    | inl _ =>
      exact absoluteMarkLaw_signed_action ((Measure.dirac ()).prod Measure.count)
        (highPacketMarkWeight a b D 1 D q Cfr (fun _ => finePairUnitMatrix d D))
        (highPacketMarkWeight_integrable (Measure.dirac ()) a b D 1 D q Cfr _ (fun _ _ => measurable_const) (integrable_const _))
        (highPacketMarkWeight_measurable a b D 1 D q Cfr _ fun _ _ => measurable_const)
        (hpos (.inr (.inl ()))) Fi hFi L hFib
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ T i.property.1 i.val.2
      exact absoluteMarkLaw_signed_action ((higherBandCarrierMeasure d r ℓ T i.val.2).prod Measure.count)
        (highPacketMarkWeight a b m r D q Cfr (higherBandCarrierAmplitude d r D lam i.val.2))
        (highPacketMarkWeight_integrable _ a b m r D q Cfr _
          (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
          (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ T i.property.1 i.val.2))
        (highPacketMarkWeight_measurable a b m r D q Cfr _ (higherBandCarrierAmplitude_measurable d r D lam i.val.2))
        (hpos (.inr (.inr i))) Fi hFi L hFib

theorem completeSourceCanonicalAction_eq_signed_first_action
    {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark (SourceRowMark d D M q (C.densityLower + 1 / (M : ℝ))
        (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ)))
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) (hmΦ : Measurable Φ)
    (B : ℝ) (hB : 0 ≤ B) (hΦ : ∀ v : HighFrameIndex d D → ℝ, (∑ γ, |v γ|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e *
      ((∏ u, highUnionSourceResetDensity C R j h e (x u)) *
        Φ (highUnionSourceResetCoefficient C R j h e)) ∂highUnionLaw R (highCenterMix C)) =
      completeSourceSignedFirstAction (C.densityLower + 1 / (M : ℝ))
        (C.densityUpper - 1 / (M : ℝ)) lam ℓ N μ D M q Cfr
        (fun u => highLocalCoordinates d k j (x u))
        (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j) Φ := by
  dsimp only
  let ad := C.densityLower + 1 / (M : ℝ); let bd := C.densityUpper - 1 / (M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2 j
  let p := fun u : Fin n => highUnionSourceDensity C R h (x u)
  let U := fun u : Fin n => highLocalCoordinates d k j (x u)
  let O (e) := (∏ u, highUnionSourceResetDensity C R j h e (x u)) *
    Φ (highUnionSourceResetCoefficient C R j h e)
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) := highUnionMark_standardBorel
  have hc := highUnionSourceState_coefficient_ball C R G h j
  have hmO : Measurable O := (Finset.measurable_fun_prod _ fun _ _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp (measurable_id.prodMk measurable_const)).mul
      (hmΦ.comp (measurable_pi_iff.mpr (highUnionSourceResetCoefficient_measurable C R G j h)))
  have hbU0 : 0 ≤ C.densityUpper := (zero_lt_one.trans C.one_lt_densityUpper).le
  have hOb (e) : ‖O e‖ ≤ C.densityUpper ^ n * B := by
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u)) * Φ _| ≤ _; rw [abs_mul]
    exact mul_le_mul (finite_density_product_abs_bound _ C.densityUpper hbU0
      fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u))
      (hΦ _ (highUnionResponseReset_ball R Cfr (by linarith) G.vector_ball G.time_interval e c hc))
      (abs_nonneg _) (pow_nonneg hbU0 n)
  have hreset (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i, e⟩) (x u) = R.rowSlope j i e (x u) * p u + R.rowIntercept i e := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append]
    change (if x u ∈ highTorusPatch d k j then R.rowSlope j i e (x u) * _ + R.rowIntercept i e else _) = _
    rw [if_pos (hx u)]; dsimp only [p]; unfold highUnionSourceDensity; rfl
  have hO (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) :
      O (Sum.inl ⟨i, e⟩) = (∏ u, (R.rowSlope j i e (x u) * p u + R.rowIntercept i e)) *
        Φ (coefficientReset c (R.rowVector i e) (R.rowTime i e)) := by
    simp only [O, hreset, highUnionSourceResetCoefficient, highUnionResponseReset,
      highUnionResponseVector, highUnionResponseTime, Sum.elim_inl, c]
  rw [completeSourceUnion_signed_action C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN O hmO (C.densityUpper ^ n * B) hOb]
  change (∑ i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ,
      ∫ᵛ e, O (Sum.inl ⟨i, e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ i) =
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q Cfr U p c Φ
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have hunit : (∫ᵛ e, O (Sum.inl ⟨Sum.inl .unit, e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .unit)) =
      finePairUnitFirstAction ad bd D q Cfr p c Φ := by
    unfold finePairUnitFirstAction sourceRowSignedMeasure; congr 1; funext e; rw [hO]
    refine congrArg (· * Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1))
      (Finset.prod_congr rfl fun _ _ => ?_)
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict,
      finePairRowData, finePairRowSlope, finePairRowIntercept, highPacketSlope, highPacketIntercept,
      highPacketObservable, localDensityReset]; ring
  have hcoarse : (∫ᵛ e, O (Sum.inl ⟨Sum.inl .coarse, e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .coarse)) =
      finePairCoarseFirstAction ad bd ℓ D q Cfr U p c Φ := by
    unfold finePairCoarseFirstAction sourceRowSignedMeasure; congr 1; funext e; rw [hO]
    refine congrArg (· * Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1))
      (Finset.prod_congr rfl fun _ _ => ?_)
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict,
      finePairRowData, finePairRowSlope, finePairRowIntercept, highPacketSlope, highPacketIntercept,
      highPacketObservable, localDensityReset, U]; ring
  have hfine : (∫ᵛ e, O (Sum.inl ⟨Sum.inl .fine, e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inl .fine)) =
      finePairFineFirstAction ad bd ℓ N M q Cfr U p c Φ := by
    unfold finePairFineFirstAction sourceRowSignedMeasure; congr 1; funext e; rw [hO]
    refine congrArg (· * Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1))
      (Finset.prod_congr rfl fun _ _ => ?_)
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict,
      finePairRowData, finePairRowSlope, finePairRowIntercept, finePairPacketSlope, finePairPacketIntercept,
      finePairPacketObservable, finePairDensityReset, U]; ring
  have hsingle : (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inl ()), e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inl ()))) =
      singletonFirstAction ad bd D q Cfr p c Φ := by
    unfold singletonFirstAction sourceRowSignedMeasure; congr 1; funext e; rw [hO]
    refine congrArg (· * Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1))
      (Finset.prod_congr rfl fun _ _ => ?_)
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, singletonRowData,
      highPacketSlope, highPacketIntercept, highPacketObservable, localDensityReset]; ring
  have hhigher (i : HigherBandFamilyIndex d D M q ad bd Cfr lam ℓ N μ) :
      (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inr i), e⟩) ∂<•sourceRowSignedMeasure d k D M q ad bd Cfr lam ℓ N μ (.inr (.inr i))) =
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q Cfr i.val.2 U p c Φ := by
    unfold higherBandFirstAction sourceRowSignedMeasure; congr 1; funext e; rw [hO]
    refine congrArg (· * Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2 (highResponseMarkAtom Cfr q e.2.2).1))
      (Finset.prod_congr rfl fun _ _ => ?_)
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, higherBandFamilyComponent,
      higherBandRowData, highPacketSlope, highPacketIntercept, highPacketObservable, localDensityReset, U]; ring
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} := by decide
  simp only [htags]
  simp [hunit, hcoarse, hfine, hsingle, hhigher, Fintype.sum_unique,
    completeSourceSignedFirstAction, finePairThreeRowFirstAction, higherBandFamilyFirstAction, add_assoc]

end CanonicalSignedAction

-- 6. Marked design factorial, patch product chart & conditional/raw score energy
--    (`HighPatchProductMeasure`, `HighMarkedDesignFactorial`, `HighMarkedMeasurable`,
--     `HighSpatialScoreTransfer`, `HighRawScoreEnergy`, `HighConditionalScoreEnergy`, `HighMarkedSpatialDesign`)

section DesignFactorialAndRawScore
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def highPatchProductChart {I : Type*} (d k : ℕ) (j : HighWindowLabels d k)
    (x : I → Covariate d) : I → Covariate d := fun i => highLocalCoordinates d k j (x i)

lemma highPatchProductChart_map_le {I : Type*} [Fintype I] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) :
    Measure.map (highPatchProductChart (I := I) d k j)
      (Measure.pi fun _ : I => (cubeVolume d).restrict (highTorusPatch d k j)) ≤
    ENNReal.ofReal (((2 / (k : ℝ)) ^ d) ^ Fintype.card I) •
      Measure.pi fun _ : I => volume.restrict (spatialPatchBox d) := by
  letI := cubeVolume_isProbability d
  letI := (volume.restrict (spatialPatchBox d)).smul_finite (c := ENNReal.ofReal ((2 / (k : ℝ)) ^ d)) ENNReal.ofReal_ne_top
  change Measure.map (fun x : I → Covariate d => fun i => highLocalCoordinates d k j (x i)) _ ≤ _
  rw [Measure.pi_map_pi fun _ => (highLocalCoordinates_measurable d k j).aemeasurable]
  have hpi_mono : Measure.pi (fun _ : I => Measure.map (highLocalCoordinates d k j)
      ((cubeVolume d).restrict (highTorusPatch d k j))) ≤
      Measure.pi fun _ : I => ENNReal.ofReal ((2 / (k : ℝ)) ^ d) • volume.restrict (spatialPatchBox d) := by
    have ho : OuterMeasure.pi (fun _ : I =>
        (Measure.map (highLocalCoordinates d k j) ((cubeVolume d).restrict (highTorusPatch d k j))).toOuterMeasure) ≤
        OuterMeasure.pi (fun _ : I => (ENNReal.ofReal ((2 / (k : ℝ)) ^ d) • volume.restrict (spatialPatchBox d)).toOuterMeasure) :=
      OuterMeasure.le_pi.mpr fun S _ => (OuterMeasure.pi_pi_le _ S).trans
        (Finset.prod_le_prod fun i _ => highLocalCoordinates_patch_map_le hk j (S i))
    refine Measure.le_iff.mpr fun S hS => ?_
    rw [Measure.pi_def, toMeasure_apply _ _ hS, Measure.pi_def, toMeasure_apply _ _ hS]; exact ho S
  exact hpi_mono.trans_eq (by rw [spatialPi_const_smul, ← ENNReal.ofReal_pow (by positivity)])

def highMarkedResponseMass {α ι : Type*} [Fintype ι] (a V η : ℝ) (g w : α → ℝ) (φ : α → ι → ℝ)
    (c : ι → ℝ) (x : α) (y : Fin 3) : ℝ :=
  ternaryMass a (g x + η * w x * ∑ γ, φ x γ * c γ) V y

def highMarkedSampleNumerator {α ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) (y : Fin r → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset
    (g ∘ x) (w ∘ x) (φ ∘ x) y - η ^ 2 * (∏ i, p (x i)) *
      ∑ i, (w (x i)) ^ 2 * highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i

def highMarkedSampleConditionalEnergy {α ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) : ℝ :=
  selectedConditionalScoreEnergy p (highMarkedResponseMass a V η g w φ c)
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x

theorem high_marked_sample_score_eq_ratio {α ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α) (y : Fin r → Fin 3) :
    highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y =
    highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y /
      selectedRawLikelihood p (highMarkedResponseMass a V η g w φ c) x y := rfl

theorem high_marked_sample_energy_integral {α ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (r : ℕ) (π : Measure E) (activation : E → ℝ)
    (a V η : ℝ) (ha : a ≠ 0) (p : α → ℝ) (pReset : E → α → ℝ) (cReset : E → ι → ℝ)
    (g w : α → ℝ) (φ : α → ι → ℝ) (c : ι → ℝ) (x : Fin r → α)
    (hp : ∀ z y, 0 < highMarkedResponseMass a V η g w φ c z y) :
    (∫ y, highMarkedLocalScore π activation a V η (p ∘ x) (fun z => pReset z ∘ x) cReset
      (g ∘ x) (w ∘ x) (φ ∘ x) c y ^ 2
      ∂Measure.pi fun i => ternaryIndexMeasure a
        (coefficientRegression η (g ∘ x) (w ∘ x) (φ ∘ x) c i) V ha fun y => (hp (x i) y).le) =
    highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c x := by
  rw [ternary_index_product_integral]
  unfold highMarkedSampleConditionalEnergy selectedConditionalScoreEnergy
  simp_rw [← high_marked_sample_score_eq_ratio r π activation a V η p pReset cReset g w φ c x]
  exact Finset.sum_congr (by ext; simp) fun _ _ => rfl

theorem highMarkedResponseMass_measurable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
    (a V η : ℝ) (g w : α → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : α → ι → ℝ) (hφ : ∀ γ, Measurable fun x => φ x γ) (c : ι → ℝ) (y : Fin 3) :
    Measurable fun x => highMarkedResponseMass a V η g w φ c x y :=
  ternaryMass_measurable_comp a V _
    (hg.add ((measurable_const.mul hw).mul (Finset.measurable_sum _ fun γ _ => (hφ γ).mul_const (c γ)))) y

theorem highMarkedSampleNumerator_measurable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [MeasurableSpace E]
    (r : ℕ) (π : Measure E) [SFinite π]
    (activation : E → ℝ) (hAct : Measurable activation) (a V η : ℝ)
    (p : α → ℝ) (hp : Measurable p) (pReset : E → α → ℝ)
    (hpReset : Measurable (Function.uncurry pReset)) (cReset : E → ι → ℝ)
    (hcReset : ∀ γ, Measurable fun e => cReset e γ)
    (g w : α → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : α → ι → ℝ) (hφ : ∀ γ, Measurable fun x => φ x γ) (c : ι → ℝ) (y : Fin r → Fin 3) :
    Measurable fun x => highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y := by
  have hReset (i : Fin r) : Measurable fun z : E × (Fin r → α) => pReset z.1 (z.2 i) :=
    hpReset.comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
  have hreg (i : Fin r) : Measurable fun z : E × (Fin r → α) =>
      coefficientRegression η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) i :=
    (hg.comp ((measurable_pi_apply i).comp measurable_snd)).add
      ((measurable_const.mul (hw.comp ((measurable_pi_apply i).comp measurable_snd))).mul
        (Finset.measurable_sum _ fun γ _ =>
          ((hφ γ).comp ((measurable_pi_apply i).comp measurable_snd)).mul ((hcReset γ).comp measurable_fst)))
  have hMarked : Measurable fun z : E × (Fin r → α) =>
      activation z.1 * (∏ i, pReset z.1 (z.2 i)) *
        highResponseProduct a V η (g ∘ z.2) (w ∘ z.2) (φ ∘ z.2) (cReset z.1) y :=
    ((hAct.comp measurable_fst).mul (Finset.measurable_prod _ fun i _ => hReset i)).mul
      (Finset.measurable_prod _ fun i _ => ternaryMass_measurable_comp a V _ (hreg i) (y i))
  have hAction : Measurable fun x : Fin r → α =>
      highMarkedResponseAction π activation a V η (fun z => pReset z ∘ x) cReset (g ∘ x) (w ∘ x) (φ ∘ x) y :=
    hMarked.stronglyMeasurable.integral_prod_left'.measurable
  have hvar (i : Fin r) : Measurable fun x : Fin r → α =>
      highResponseVarianceTerm a V η (g ∘ x) (w ∘ x) (φ ∘ x) c y i :=
    measurable_const.mul (Finset.measurable_prod _ fun l _ =>
      (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c (y l)).comp (measurable_pi_apply l))
  exact hAction.sub ((measurable_const.mul (Finset.measurable_prod _ fun i _ => hp.comp (measurable_pi_apply i))).mul
    (Finset.measurable_sum _ fun i _ => ((hw.comp (measurable_pi_apply i)).pow_const 2).mul (hvar i)))

theorem high_marked_original_design_spatial_series {ι E : Type*}
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] {d k : ℕ} [NeZero k]
    (hk : 4 ≤ k) (j : HighWindowLabels d k) (n : ℕ)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (hAct : Measurable activation)
    (a V η : ℝ) (ha : a ≠ 0) (pMinus pPlus cMass : ℝ)
    (hpMinus : 0 < pMinus) (hcMass : 0 < cMass)
    (p : Covariate d → ℝ) (hpMeas : Measurable p) (hraw : ∀ x, pMinus ≤ p x ∧ p x ≤ pPlus)
    (pReset : E → Covariate d → ℝ) (hpReset : Measurable (Function.uncurry pReset))
    (cReset : E → ι → ℝ) (hcReset : ∀ γ, Measurable fun e => cReset e γ)
    (g w : Covariate d → ℝ) (hg : Measurable g) (hw : Measurable w)
    (φ : Covariate d → ι → ℝ) (hφ : ∀ γ, Measurable fun x => φ x γ) (c : ι → ℝ)
    (hq : ∀ x y, cMass ≤ highMarkedResponseMass a V η g w φ c x y)
    (hwo : ∀ x, x ∉ highTorusPatch d k j → w x = 0)
    (hro : ∀ e x, x ∉ highTorusPatch d k j → pReset e x = p x)
    (H : (r : ℕ) → (Fin r → Covariate d) → ℝ)
    (hH : ∀ r, Integrable (H r) (Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d)))
    (hH0 : ∀ r u, 0 ≤ H r u)
    (hdom : ∀ r x, (∀ i, x i ∈ highTorusPatch d k j) →
      selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x ≤
        H r (highPatchProductChart d k j x)) :
    Integrable (highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c)
      (Measure.pi fun _ : Fin n => highNormalizedDesignLaw p) ∧
    (∫ x, highMarkedSampleConditionalEnergy n π activation a V η p pReset cReset g w φ c x
      ∂Measure.pi fun _ : Fin n => highNormalizedDesignLaw p) ≤
      ∑ r ∈ Finset.range (n + 1),
        ((n : ℝ) * highFixedScoreDenominator pMinus cMass * (2 / (k : ℝ)) ^ d) ^ r /
          (r.factorial : ℝ) * ∫ u, H r u
            ∂Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d) := by
  let _ := cubeVolume_isProbability d
  let A := highTorusPatch d k j
  have hA := highTorusPatch_measurableSet d k j
  have hprob := high_normalized_design_probability p hpMeas pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)
  have hm : pMinus ≤ highRawDensityMass p :=
    (highRawDensityMass_mem_Icc p hpMeas pMinus pPlus hpMinus (Filter.Eventually.of_forall hraw)).1
  have hR (r : ℕ) (y : Fin r → Fin 3) : Measurable fun x =>
      highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c x y :=
    highMarkedSampleNumerator_measurable r π activation hAct a V η p hpMeas pReset hpReset cReset hcReset g w hg hw φ hφ c y
  have hRaw (r : ℕ) :
      Integrable (selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c))
        (Measure.pi fun _ : Fin r => (cubeVolume d).restrict A) ∧
      (∫ x, selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
        ∂Measure.pi fun _ : Fin r => (cubeVolume d).restrict A) ≤
        ((2 / (k : ℝ)) ^ d) ^ r * ∫ u, H r u ∂Measure.pi fun _ : Fin r => volume.restrict (spatialPatchBox d) := by
    have hchart_meas : Measurable (highPatchProductChart (I := Fin r) d k j) :=
      measurable_pi_iff.mpr fun i => (highLocalCoordinates_measurable d k j).comp (measurable_pi_apply i)
    have hhs := (hH r).smul_measure (c := ENNReal.ofReal (((2 / (k : ℝ)) ^ d) ^ Fintype.card (Fin r))) ENNReal.ofReal_ne_top
    have hmap_int := hhs.mono_measure (highPatchProductChart_map_le (I := Fin r) hk j)
    have heval : Integrable (fun x => H r (highPatchProductChart d k j x))
        (Measure.pi fun _ : Fin r => (cubeVolume d).restrict A) := hmap_int.comp_measurable hchart_meas
    have hmem : ∀ᵐ x ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict A), ∀ i, x i ∈ A :=
      ae_all_iff.mpr fun i => Measure.tendsto_eval_ae_ae.eventually (ae_restrict_mem hA)
    have hrawI : Integrable (selectedRawSquareEnergy (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c))
        (Measure.pi fun _ : Fin r => (cubeVolume d).restrict A) :=
      heval.mono' (Finset.measurable_sum _ fun y _ => (hR r y).pow_const 2).aestronglyMeasurable
        (hmem.mono fun x hx => by
          rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
          exact hdom r x hx)
    refine ⟨hrawI, (integral_mono_ae hrawI heval (hmem.mono fun x hx => hdom r x hx)).trans ?_⟩
    rw [← integral_map hchart_meas.aemeasurable hmap_int.aestronglyMeasurable]
    refine (integral_mono_measure (highPatchProductChart_map_le (I := Fin r) hk j)
      (Filter.Eventually.of_forall (hH0 r)) hhs).trans_eq ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul, Fintype.card_fin]
  let μ := highNormalizedDesignLaw p
  let _ : IsProbabilityMeasure μ := hprob
  let F_en (r : ℕ) := highMarkedSampleConditionalEnergy r π activation a V η p pReset cReset g w φ c
  let enum (S : Finset (Fin n)) : Fin S.card ≃ S := (S.orderIsoOfFin rfl).toEquiv
  let emb (S : Finset (Fin n)) : Fin S.card ↪ Fin n := (S.orderEmbOfFin rfl).toEmbedding
  let Hs (S : Finset (Fin n)) (z : S → Covariate d) : ℝ := F_en S.card (z ∘ enum S)
  let J (r : ℕ) := ∫ x, selectedRawSquareEnergy
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) x
      ∂Measure.pi fun _ : Fin r => (cubeVolume d).restrict A
  have hp0 (x : Covariate d) : p x ≠ 0 := (hpMinus.trans_le (hraw x).1).ne'
  have hq0 (x : Covariate d) (y : Fin 3) : 0 < highMarkedResponseMass a V η g w φ c x y := hcMass.trans_le (hq x y)
  have hFI (r : ℕ) := normalized_selected_score_energy_integrable_bound (cubeVolume d) A hA (highRawDensityMass p) pMinus cMass
    hpMinus hcMass hm p hpMeas (highMarkedResponseMass a V η g w φ c)
    (highMarkedResponseMass_measurable a V η g w hg hw φ hφ c)
    (highMarkedSampleNumerator r π activation a V η p pReset cReset g w φ c) (hR r) hprob
    (fun x _ => (hraw x).1) (fun x _ y => hq x y) (hRaw r).1
  have hHI (S : Finset (Fin n)) : Integrable (Hs S) (Measure.pi fun _ : S => μ.restrict A) :=
    finite_pi_reindex_integrable (μ.restrict A) (enum S).symm (F_en S.card) (hFI S.card).1
  have hEq (S : Finset (Fin n)) (x : Fin n → Covariate d) (hx : x ∈ designMembershipCell n A S) :
      F_en n x = Hs S fun i : S => x i.val := by
    have hmem := (design_membership_cell_iff n A S x).mp hx
    have hmap : Finset.univ.map (emb S) = S := Finset.map_orderEmbOfFin_univ S rfl
    have he := high_marked_selected_response_energy (emb S) π activation a V η ha
      (p ∘ x) (fun z => pReset z ∘ x) cReset (g ∘ x) (w ∘ x) (φ ∘ x) c
      (fun i => hp0 (x i)) (fun i y => hq0 (x i) y)
      (fun i hi => by rw [hmap] at hi; exact hwo _ fun h => hi ((hmem i).mp h))
      fun e i hi => by rw [hmap] at hi; exact hro e _ fun h => hi ((hmem i).mp h)
    rw [high_marked_sample_energy_integral n π activation a V η ha p pReset cReset g w φ c x hq0] at he
    exact he.trans (high_marked_sample_energy_integral S.card π activation a V η ha p pReset cReset g w φ c (x ∘ emb S) hq0)
  have hFn : Integrable (F_en n) (Measure.pi fun _ : Fin n => μ) := by
    have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ :=
      Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr
        ⟨Finset.univ.filter fun i => x i ∈ A, (design_membership_cell_iff n A _ x).mpr fun _ => by simp⟩
    have hi : IntegrableOn (F_en n) (⋃ S : Finset (Fin n), designMembershipCell n A S) (Measure.pi fun _ : Fin n => μ) :=
      integrableOn_finite_iUnion.mpr fun S => by
        have hsel : IntegrableOn (fun x : Fin n → Covariate d => Hs S fun i : S => x i.val)
            (designMembershipCell n A S) (Measure.pi fun _ : Fin n => μ) := by
          rw [IntegrableOn, designMembershipCell, Measure.restrict_pi_pi]
          have hsp := measurePreserving_piEquivPiSubtypeProd
            (fun i : Fin n => μ.restrict (if i ∈ S then A else Aᶜ)) fun i => i ∈ S
          rw [show (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S from Subsingleton.elim _ _,
            show (fun i : S => μ.restrict (if i.val ∈ S then A else Aᶜ)) = fun _ : S => μ.restrict A from funext fun i => by rw [ite_eq_left i.property],
            show (fun i : {i : Fin n // i ∉ S} => μ.restrict (if i.val ∈ S then A else Aᶜ)) = fun _ => μ.restrict Aᶜ from funext fun i => by rw [ite_eq_right i.property]] at hsp
          exact hsp.integrable_comp_of_integrable ((hHI S).comp_fst _)
        refine hsel.congr ?_
        filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
        exact (hEq S x hx).symm
    simpa only [hcover, integrableOn_univ] using hi
  have hser := iid_local_energy_le_factorial_spatial_series μ n A hA (F_en n) hFn Hs hHI
    (fun S _ => selected_conditional_score_energy_nonneg p (highMarkedResponseMass a V η g w φ c)
      (fun x y => (hq0 x y).le) _ _) (fun S x hx => (hEq S x hx).le)
    (highFixedScoreDenominator pMinus cMass) (high_fixed_score_denominator_pos hpMinus hcMass).le J
    (fun _ => integral_nonneg fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) fun S => by
      change (∫ z, F_en S.card (z ∘ enum S) ∂Measure.pi fun _ : S => μ.restrict A) ≤ _
      have he : (∫ z, F_en S.card (z ∘ enum S) ∂Measure.pi fun _ : S => μ.restrict A) =
          ∫ z, F_en S.card z ∂Measure.pi fun _ : Fin S.card => μ.restrict A :=
        finite_pi_reindex_integral (μ.restrict A) (enum S).symm (F_en S.card)
      rw [he]
      have hs := (hFI S.card).2
      simp only [Fintype.card_fin] at hs
      exact hs
  refine ⟨hFn, hser.trans (Finset.sum_le_sum fun r _ => ?_)⟩
  have hco : 0 ≤ ((n : ℝ) * highFixedScoreDenominator pMinus cMass) ^ r / (r.factorial : ℝ) :=
    div_nonneg (pow_nonneg (mul_nonneg (Nat.cast_nonneg n) (high_fixed_score_denominator_pos hpMinus hcMass).le) r) (Nat.cast_nonneg _)
  exact (mul_le_mul_of_nonneg_left (hRaw r).2 hco).trans_eq (by rw [mul_pow]; ring)

def finiteResponseSquareEnergy {α : Type*} [MeasurableSpace α] (n : ℕ)
    (a V : ℝ) (F : α → ℝ) (S : ((Fin n → α) × (Fin n → Fin 3)) → ℝ) (x : Fin n → α) : ℝ :=
  ∑ y : Fin n → Fin 3, (∏ i, ternaryMass a (F (x i)) V (y i)) * (S (x, y)) ^ 2

theorem response_sample_square_integrable_integral {α : Type*} [MeasurableSpace α]
    (n : ℕ) (μ : Measure (Fin n → α)) [SFinite μ] (a V : ℝ) (ha : a ≠ 0)
    (F : α → ℝ) (hF : Measurable F) (hq : ∀ x y, 0 ≤ ternaryMass a (F x) V y)
    (S : ((Fin n → α) × (Fin n → Fin 3)) → ℝ) (hS : Measurable S)
    (hE : Integrable (finiteResponseSquareEnergy n a V F S) μ) :
    Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) ∧
    (∫ z, S z ^ 2 ∂μ.compProd (responseSampleIndexKernel n a V F hF)) =
      ∫ x, finiteResponseSquareEnergy n a V F S x ∂μ := by
  let _ := responseSampleIndexKernel_markov n a V F hF ha hq
  have he (x : Fin n → α) : (∫ y, ‖S (x, y) ^ 2‖ ∂responseSampleIndexKernel n a V F hF x) =
      finiteResponseSquareEnergy n a V F S x := by
    simp_rw [Real.norm_eq_abs, abs_sq]
    exact responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _
  have hi : Integrable (fun z => S z ^ 2) (μ.compProd (responseSampleIndexKernel n a V F hF)) :=
    (Measure.integrable_compProd_iff (hS.pow_const 2).aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall fun _ => Integrable.of_finite, by simpa only [he] using hE⟩
  refine ⟨hi, ?_⟩
  rw [Measure.integral_compProd hi]
  exact integral_congr_ae <| Filter.Eventually.of_forall fun x =>
    responseSampleIndexKernel_integral n a V F hF x (fun i y => hq (x i) y) _

theorem high_raw_joint_fisher_integrable_bound {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν] (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (aRaw bRaw : ℝ) (haRaw : 0 < aRaw)
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (D : Ω → ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ)
    (hD : Measurable (Function.uncurry D)) (B : ℝ) (hB : 0 ≤ B)
    (hscore : ∀ ω, Integrable (fun z => (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2)
      (highSampleIndexKernel n a V p F hp hF ω))
    (hbound : ∀ ω, (∫ z, (D ω z / highRawSampleLikelihood n a V (p ω) (F ω) z) ^ 2
      ∂highSampleIndexKernel n a V p F hp hF ω) ≤ B) :
    Integrable (fun z => D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2)
      (ν.prod (highSampleReference d n)) ∧
    (∫ z, D z.1 z.2 ^ 2 / highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
      ∂ν.prod (highSampleReference d n)) ≤
      massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n * B := by
  let μ := highSampleReference d n
  let c (ω : Ω) := highRawDensityMass (p ω) ^ n
  let L (ω : Ω) := highRawSampleLikelihood n a V (p ω) (F ω)
  have hLm : Measurable (Function.uncurry L) := highRawSampleLikelihood_joint_measurable n a V p F hp hF
  have hpos (ω : Ω) (z) : 0 < L ω z :=
    Finset.prod_pos fun i _ => mul_pos (haRaw.trans_le (hraw ω (z.1 i)).1) (hq ω _ _)
  have hmBound (ω : Ω) := highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw
    (Filter.Eventually.of_forall (hraw ω))
  have hm (ω : Ω) : 0 < highRawDensityMass (p ω) := haRaw.trans_le (hmBound ω).1
  have hc (ω : Ω) : 0 < c ω := pow_pos (hm ω) n
  have hci : Integrable c ν :=
    (integrable_const (bRaw ^ n)).mono' ((highRawDensityMass_joint_measurable p hp).pow_const n).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hc ω).le]
        exact pow_le_pow_left₀ (hm ω).le (hmBound ω).2 n)
  have hkern_eq (ω : Ω) : highSampleIndexKernel n a V p F hp hF ω =
      μ.withDensity (fun z => ENNReal.ofReal (L ω z / c ω)) := by
    rw [highSampleIndexKernel_apply]; congr 1; funext z; congr 1
    refine (eq_div_iff (hc ω).ne').mpr ?_
    simpa only [c, L, mul_comm] using highSampleLikelihood_mass_cancellation n a V (p ω) (F ω) (hm ω).ne' z
  let W : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ := fun z => D z.1 z.2 ^ 2 / L z.1 z.2
  have hW : Measurable W := (hD.pow_const 2).div hLm
  have htransf (ω : Ω) :
      Integrable (fun z => W (ω, z)) μ ∧
      (∫ z, W (ω, z) ∂μ) = c ω * ∫ z, (D ω z / L ω z) ^ 2 ∂highSampleIndexKernel n a V p F hp hF ω := by
    have hf : Measurable fun z => ENNReal.ofReal (L ω z / c ω) := ENNReal.measurable_ofReal.comp (hLm.of_uncurry_left.div_const (c ω))
    have halg (z) : (ENNReal.ofReal (L ω z / c ω)).toReal * (D ω z / L ω z) ^ 2 = (c ω)⁻¹ * W (ω, z) := by
      dsimp [W]; rw [ENNReal.toReal_ofReal (div_nonneg (hpos ω z).le (hc ω).le)]
      field_simp [(hpos ω z).ne', (hc ω).ne']
    have hsc : Integrable (fun z => (D ω z / L ω z) ^ 2) (μ.withDensity fun z => ENNReal.ofReal (L ω z / c ω)) := by
      rw [← hkern_eq ω]; exact hscore ω
    rw [integrable_withDensity_iff_integrable_smul' hf (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hsc
    simp only [smul_eq_mul, halg] at hsc
    have hwi : Integrable (fun z => W (ω, z)) μ :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (inv_ne_zero (hc ω).ne')) _).mp hsc
    refine ⟨hwi, ?_⟩
    rw [hkern_eq ω]
    have hi := integral_withDensity_eq_integral_toReal_smul (μ := μ) hf
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) fun z => (D ω z / L ω z) ^ 2
    change (∫ z, (D ω z / L ω z) ^ 2 ∂μ.withDensity _) = ∫ z, (ENNReal.ofReal (L ω z / c ω)).toReal * (D ω z / L ω z) ^ 2 ∂μ at hi
    rw [hi]; simp_rw [halg]; rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ (hc ω).ne', one_mul]
  have hnormI : Integrable (fun ω => ∫ z, ‖W (ω, z)‖ ∂μ) ν :=
    (hci.mul_const B).mono' hW.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        have heN : (fun z => ‖W (ω, z)‖) = fun z => W (ω, z) := funext fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (hpos ω z).le)]
        rw [heN, (htransf ω).2]; exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le)
  have hWI : Integrable W (ν.prod μ) :=
    (integrable_prod_iff hW.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall fun ω => (htransf ω).1, hnormI⟩
  refine ⟨hWI, ?_⟩
  rw [integral_prod _ hWI]
  refine (integral_mono_ae hWI.integral_prod_left (hci.mul_const B)
    (Filter.Eventually.of_forall fun ω => ?_)).trans_eq (integral_mul_const _ _)
  change (∫ z, W (ω, z) ∂μ) ≤ c ω * B
  rw [(htransf ω).2]; exact mul_le_mul_of_nonneg_left (hbound ω) (hc ω).le

end DesignFactorialAndRawScore

-- 7. Posterior score contraction, marginal score derivative/centering & time likelihood measurability
--    (`PosteriorScoreEnergy`, `HighMarginalScoreEnergy`, `HighMarginalScoreDerivative`,
--     `HighMarginalScoreCenter`, `HighTimeLikelihood`)

section PosteriorAndTimeLikelihood
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def posteriorMeanScore {Ω Z : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (L D : Ω × Z → ℝ) (z : Z) : ℝ :=
  (∫ ω, D (ω, z) ∂ν) / ∫ ω, L (ω, z) ∂ν

theorem posteriorMeanScore_memLp_energy {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (μ : Measure Z) [SFinite μ] (L D : Ω × Z → ℝ)
    (hLm : Measurable L) (hDm : Measurable D) (hLp : ∀ z, 0 < L z)
    (LC DC G : ℝ) (hG : 0 < G) (hLb : ∀ z, L z ≤ LC) (hDb : ∀ z, |D z| ≤ DC)
    (hE : Integrable (fun z => D z ^ 2 / L z) (ν.prod μ)) :
    let ρ := μ.withDensity fun z => ENNReal.ofReal ((∫ ω, L (ω, z) ∂ν) / G)
    MemLp (posteriorMeanScore ν L D) 2 ρ ∧
      (∫ z, posteriorMeanScore ν L D z ^ 2 ∂ρ) ≤ G⁻¹ * ∫ z, D z ^ 2 / L z ∂ν.prod μ := by
  let M (z : Z) := ∫ ω, L (ω, z) ∂ν
  let A (z : Z) := ∫ ω, D (ω, z) ∂ν
  let E (z : Z) := ∫ ω, D (ω, z) ^ 2 / L (ω, z) ∂ν
  let R := posteriorMeanScore ν L D
  let ρ := μ.withDensity fun z => ENNReal.ofReal (M z / G)
  have hM : Measurable M := hLm.stronglyMeasurable.integral_prod_left'.measurable
  have hR : Measurable R := hDm.stronglyMeasurable.integral_prod_left'.measurable.div hM
  have hden (z) : 0 < M z := integral_likelihood_pos ν _
    (hLm.comp (measurable_id.prodMk measurable_const)) LC (fun ω => hLp (ω, z)) fun ω => hLb (ω, z)
  have hiL (z) : Integrable (fun ω => L (ω, z)) ν :=
    Integrable.of_bound (hLm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable LC
      (Eventually.of_forall fun _ => by change ‖L (_, z)‖ ≤ LC; rw [Real.norm_eq_abs, abs_of_nonneg (hLp _).le]; exact hLb _)
  have hiD (z) : Integrable (fun ω => D (ω, z)) ν :=
    Integrable.of_bound (hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable DC
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hDb (ω, z))
  have hEnergy : ∀ᵐ z ∂μ, (M z / G) * R z ^ 2 ≤ G⁻¹ * E z := by
    filter_upwards [hE.prod_left_ae] with z hEz
    have hc := weighted_score_energy_contraction ν (fun ω => L (ω, z)) (fun ω => D (ω, z))
      (fun ω => hLp (ω, z)) (hiL z) (hiD z) hEz (hden z)
    rw [show (M z / G) * R z ^ 2 = G⁻¹ * (A z ^ 2 / M z) by
      dsimp only [R, posteriorMeanScore, A, M]; field_simp [(hden z).ne', hG.ne']]
    exact mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hG.le)
  have hiE : Integrable (fun z => G⁻¹ * E z) μ := hE.integral_prod_right.const_mul _
  have hweighted : Integrable (fun z => (M z / G) * R z ^ 2) μ :=
    hiE.mono' ((hM.div_const _).mul (hR.pow_const 2)).aestronglyMeasurable
      (hEnergy.mono fun z hz => by
        change ‖(M z / G) * R z ^ 2‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (hden z).le hG.le) (sq_nonneg _))]; exact hz)
  have hdens : Measurable fun z => ENNReal.ofReal (M z / G) := (hM.div_const G).ennreal_ofReal
  have hsquare : Integrable (fun z => R z ^ 2) ρ := by
    refine (integrable_withDensity_iff_integrable_smul' hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2 ?_
    simpa only [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul] using hweighted
  refine ⟨(memLp_two_iff_integrable_sq hR.aestronglyMeasurable).2 hsquare, ?_⟩
  change (∫ z, R z ^ 2 ∂ρ) ≤ _
  rw [integral_withDensity_eq_integral_toReal_smul hdens (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (div_nonneg (hden _).le hG.le), smul_eq_mul]
  exact (integral_mono_ae hweighted hiE hEnergy).trans_eq (by rw [integral_const_mul, ← MeasureTheory.integral_prod_symm _ hE])

section MarginalScoreAndDeriv
variable {J : Type*} [Fintype J] [LinearOrder J]

theorem highMarginalRealScore_memLp_energy {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (hE : Integrable (fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2) ^ 2 /
        highRawSampleLikelihood n a V (p z.1) (F z.1) z.2) (ν.prod (highSampleReference d n))) :
    let P := (highRealSampleKernel n a V p F hp hF) ∘ₘ (massPowerTilt ν (fun ω => highRawDensityMass (p ω)) n)
    MemLp (highMarginalRealScore dependent hsymm ν π activation n a V η p F) 2 P ∧
      (∫ z, (highMarginalRealScore dependent hsymm ν π activation n a V η p F z) ^ 2 ∂P) ≤
        (massPowerNormalizer ν (fun ω => highRawDensityMass (p ω)) n)⁻¹ *
          ∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
            (highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2) ^ 2 /
              highRawSampleLikelihood n a V (p z.1) (F z.1) z.2 ∂ν.prod (highSampleReference d n) := by
  let μ := highSampleReference d n
  let L : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ :=
    fun z => highRawSampleLikelihood n a V (p z.1) (F z.1) z.2
  let D : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) → ℝ :=
    fun z => highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
  let m := fun ω => highRawDensityMass (p ω)
  let G := massPowerNormalizer ν m n
  have hG : 0 < G := massPowerNormalizer_pos ν m (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw
    fun ω => highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]; exact (hraw ω x).2.trans (le_abs_self _)
  have he := posteriorMeanScore_memLp_energy ν μ L D
    (highRawSampleLikelihood_joint_measurable n a V p F hp hF)
    (highHistoryLikelihoodDerivative_measurable dependent hsymm π activation ham n a V η p F hp hF)
    (fun z => highRawSampleLikelihood_pos n a V p F (fun ω x => haRaw.trans_le (hraw ω x).1) hq z.1 z.2)
    (|bRaw| ^ n) _ G hG
    (fun z => (le_abs_self _).trans (highRawSampleLikelihood_abs_le n a V |bRaw| (abs_nonneg _) _ _ (hpb z.1) ha.ne'
      (fun x y => (hq z.1 x y).le) z.2))
    (fun z => highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa habound
      n a V η |bRaw| (abs_nonneg _) ha p F hpb (fun ω x y => (hq ω x y).le) z.1 z.2) hE
  have hden := highMassTilt_index_marginal_density ν n a V p F hp hF aRaw bRaw haRaw ha.ne'
    hraw fun ω x y => (hq ω x y).le
  let Pi := (highSampleIndexKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n
  have hpost : posteriorMeanScore ν L D = highMarginalIndexScore dependent hsymm ν π activation n a V η p F := rfl
  change MemLp (posteriorMeanScore ν L D) 2 (μ.withDensity fun z => ENNReal.ofReal ((∫ ω, L (ω, z) ∂ν) / G)) ∧ _ at he
  change Pi = μ.withDensity fun z => ENNReal.ofReal ((∫ ω, L (ω, z) ∂ν) / G) at hden
  rw [hpost, ← hden] at he
  have hmap : (highRealSampleKernel n a V p F hp hF) ∘ₘ massPowerTilt ν m n = Pi.map (encodeDesignResponse a) :=
    (Measure.map_comp _ _ (encodeDesignResponse_measurable a)).symm
  have hR := highMarginalRealScore_measurable dependent hsymm ν π activation ham n a V η p F hp hF
  have hcomp : (fun z => highMarginalRealScore dependent hsymm ν π activation n a V η p F (encodeDesignResponse a z)) =
      highMarginalIndexScore dependent hsymm ν π activation n a V η p F :=
    funext fun z => congrArg (highMarginalIndexScore dependent hsymm ν π activation n a V η p F)
      (decodeDesignResponse_encode a ha z)
  dsimp only; rw [hmap]
  refine ⟨(memLp_map_measure_iff hR.aestronglyMeasurable (encodeDesignResponse_measurable a).aemeasurable).2
    (by simpa only [Function.comp_def, hcomp] using he.1), ?_⟩
  rw [integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) (hR.pow_const 2).stronglyMeasurable]
  simp_rw [fun z => congrFun hcomp z]; exact he.2

section DataMeanDeriv
variable (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T Ba : ℝ) (hBa : 0 ≤ Ba)
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E]
    (π : Measure E) [IsProbabilityMeasure π] (activation : E → ℝ) (hactivation : Measurable activation)
    (hcenter : ∫ e, activation e ∂π = 0) (habound : ∀ e, |activation e| ≤ Ba)
    (hsmall : T * Ba / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    {d : ℕ} (n : ℕ) (a v η aRaw bRaw : ℝ) (ha : 0 < a) (haRaw : 0 < aRaw)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hraw : ∀ ω x, aRaw ≤ p ω x ∧ p ω x ≤ bRaw)
include hrefl hsymm hΔ hlabels Ba hBa hactivation hcenter habound hsmall aRaw bRaw ha haRaw hp hF hraw

lemma historyMarkedPrior_dataMean_score_hasDerivAt
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B)
    (t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n))
      (∫ z, H z * highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η ^ 2 * t) η p F z
        ∂(highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) t := by
  have hq0 (u : ℝ) (hu : u ∈ Icc 0 T) (ω) (x) (y) := (hq u hu ω x y).le
  have hint : Integrable activation π := Integrable.of_bound hactivation.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  have hprob (u : ℝ) (hu : u ∈ Icc 0 T) : IsProbabilityMeasure (historyMarkedPrior dependent Δ u π activation) :=
    historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π activation hint hcenter habound
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa) (historyReferenceRho_pos Δ).le).trans hsmall)
  let _ := hprob t ⟨ht.le, htT.le⟩
  have hd := historyMarkedPrior_tiltedObservable_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq0 hmass H hH B hB hHb t ht htT
  have hpb (ω : HistoryMarked dependent E) (x : Covariate d) : |p ω x| ≤ |bRaw| := by
    rw [abs_of_nonneg (haRaw.le.trans (hraw ω x).1)]; exact (hraw ω x).2.trans (le_abs_self _)
  have he := highMarginalRealScore_integral dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) π activation hactivation Ba hBa habound
    n a (v - η ^ 2 * t) η aRaw bRaw B ha haRaw hB p F hp hF hraw (hq t ⟨ht.le, htT.le⟩) H hH hHb
  have hi := highHistoryLikelihoodDerivative_observable π dependent hsymm
    (historyMarkedPrior dependent Δ t π activation) activation hactivation Ba hBa habound
    n a (v - η ^ 2 * t) η |bRaw| B (abs_nonneg _) hB ha p F hp hF hpb (hq0 t ⟨ht.le, htT.le⟩) H hH hHb
  rw [hi, massPowerNormalizer_eq_of_massLaw _ _ _ (highRawDensityMass_joint_measurable p hp) n (hmass t ⟨ht.le, htT.le⟩)] at he
  rw [he]
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht htT] with u hu
  let _ := hprob u ⟨hu.1.le, hu.2.le⟩
  exact (highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
    n a (v - η ^ 2 * u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw (hq0 u ⟨hu.1.le, hu.2.le⟩) H hH hHb).symm

theorem historyMarkedPrior_dataMean_absolutelyContinuous
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 ≤ ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) (hT : 0 ≤ T) :
    AbsolutelyContinuousOnInterval
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n)) 0 T := by
  obtain ⟨K, hK⟩ := historyMarkedPrior_tiltedObservable_exists_lipschitz dependent hrefl hsymm
    Δ hΔ hlabels T Ba hBa π activation hactivation hcenter habound hsmall
    n a v η aRaw bRaw ha haRaw p F hp hF hraw hq hmass H hH B hB hHb
  have hint : Integrable activation π := Integrable.of_bound hactivation.aestronglyMeasurable Ba
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  have he (u : ℝ) (hu : u ∈ Icc 0 T) :
      highTiltedObservableMean (historyMarkedPrior dependent Δ u π activation) n a (v - η ^ 2 * u) p F hp hF H =
      ∫ z, H z ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation) (fun ω => highRawDensityMass (p ω)) n) := by
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1 hBa π activation hint hcenter habound
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2 hBa) (historyReferenceRho_pos Δ).le).trans hsmall)
    exact highTiltedObservableMean_eq_dataMean (historyMarkedPrior dependent Δ u π activation)
      n a (v - η ^ 2 * u) aRaw bRaw B ha.ne' haRaw hB p F hp hF hraw (hq u hu) H hH hHb
  have hKd : LipschitzOnWith K
      (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation) (fun ω => highRawDensityMass (p ω)) n)) (Icc 0 T) :=
    LipschitzOnWith.of_dist_le_mul fun u hu w hw => by rw [← he u hu, ← he w hw]; exact hK.dist_le_mul u hu w hw
  rw [← uIcc_of_le hT] at hKd; exact hKd.absolutelyContinuousOnInterval

theorem historyMarkedPrior_dataMean_score_hasDerivAt_ae
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω)))
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : 0 ≤ B) (hHb : ∀ z, |H z| ≤ B) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      HasDerivAt (fun u => ∫ z, H z ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
        (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
          (fun ω => highRawDensityMass (p ω)) n))
        (∫ z, H z * highMarginalRealScore dependent hsymm
          (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η ^ 2 * t) η p F z
          ∂(highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
            (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
              (fun ω => highRawDensityMass (p ω)) n)) t := by
  filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) by simp [ae_iff],
    show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T by simp [ae_iff]] with t ht0 htT ht
  exact historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass H hH B hB hHb t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)

theorem historyMarkedPrior_dataScore_centered_ae
    (hq : ∀ u ∈ Icc 0 T, ∀ ω x y, 0 < ternaryMass a (F ω x) (v - η ^ 2 * u) y)
    (hmass : ∀ u ∈ Icc 0 T,
      (historyMarkedPrior dependent Δ u π activation).map (fun ω => highRawDensityMass (p ω)) =
      (historyMarkedPrior dependent Δ 0 π activation).map (fun ω => highRawDensityMass (p ω))) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 T →
      (∫ z, highMarginalRealScore dependent hsymm
        (historyMarkedPrior dependent Δ t π activation) π activation n a (v - η ^ 2 * t) η p F z
        ∂(highRealSampleKernel n a (v - η ^ 2 * t) p F hp hF) ∘ₘ
          (massPowerTilt (historyMarkedPrior dependent Δ t π activation)
            (fun ω => highRawDensityMass (p ω)) n)) = 0 := by
  filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ (0 : ℝ) by simp [ae_iff],
    show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ T by simp [ae_iff]] with t ht0 htT ht
  have hd := historyMarkedPrior_dataMean_score_hasDerivAt dependent hrefl hsymm Δ hΔ hlabels
    T Ba hBa π activation hactivation hcenter habound hsmall n a v η aRaw bRaw ha haRaw p F hp hF
    hraw hq hmass (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num)
    t (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)
  have he : (fun u => ∫ _, (1 : ℝ) ∂(highRealSampleKernel n a (v - η ^ 2 * u) p F hp hF) ∘ₘ
      (massPowerTilt (historyMarkedPrior dependent Δ u π activation)
        (fun ω => highRawDensityMass (p ω)) n)) =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (lt_of_le_of_ne ht.2 htT)] with u hu
    have hint : Integrable activation π := Integrable.of_bound hactivation.aestronglyMeasurable Ba
      (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
    let _ := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels u Ba hu.1.le hBa π activation hint hcenter habound
      ((div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu.2.le hBa) (historyReferenceRho_pos Δ).le).trans hsmall)
    let _ := massPowerTilt_isProbability (historyMarkedPrior dependent Δ u π activation)
      _ (highRawDensityMass_joint_measurable p hp) n aRaw bRaw haRaw
      fun ω => highRawDensityMass_mem_Icc (p ω) hp.of_uncurry_left aRaw bRaw haRaw (Eventually.of_forall (hraw ω))
    let _ := highRealSampleKernel_markov n a (v - η ^ 2 * u) p F hp hF aRaw bRaw haRaw hraw ha.ne'
      fun ω x y => (hq u ⟨hu.1.le, hu.2.le⟩ ω x y).le
    simp
  simpa only [one_mul] using hd.unique ((hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq he)

end DataMeanDeriv

theorem historyMarkedDensity_joint_measurable {E : Type*} [MeasurableSpace E]
    (dependent : J → J → Prop) (ρ : ℝ) (activation : E → ℝ) (ham : Measurable activation) :
    Measurable fun z : ℝ × HistoryMarked dependent E =>
      historyMarkedDensity dependent ρ z.1 activation z.2 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (ω : HistoryMarked dependent E) => historyMarkedDensity dependent ρ t activation ω)
    (fun ω => continuous_iff_continuousAt.mpr fun t => (historyMarkedDensity_hasDerivAt dependent ρ t activation ω).continuousAt)
    fun t => historyMarkedDensity_measurable dependent ρ t activation ham

theorem highRawSampleLikelihood_time_measurable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (n : ℕ) (a v η : ℝ) (p F : Ω → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : ℝ × (Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v - η ^ 2 * z.1) (p z.2.1) (F z.2.1) z.2.2 :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun (t : ℝ) (z : Ω × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleLikelihood n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2)
    (fun z => continuous_iff_continuousAt.mpr fun t =>
      (highRawSampleLikelihood_hasDerivAt_path n a v η t (p z.1) (F z.1) z.2).continuousAt)
    fun t => highRawSampleLikelihood_joint_measurable n a (v - η ^ 2 * t) p F hp hF

theorem highHistoryLikelihoodDerivative_time_measurable {E : Type*} [MeasurableSpace E]
    [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a v η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a (v - η ^ 2 * z.1) η p F z.2.1 z.2.2 := by
  have hvar : Measurable fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highRawSampleVarianceDerivative n a (v - η ^ 2 * z.1) (p z.2.1) (F z.2.1) z.2.2 := by
    refine measurable_uncurry_of_continuous_of_measurable
      (u := fun (t : ℝ) (z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
        highRawSampleVarianceDerivative n a (v - η ^ 2 * t) (p z.1) (F z.1) z.2)
      (fun z => ?_) fun t => highRawSampleVarianceDerivative_joint_measurable n a (v - η ^ 2 * t) p F hp hF
    unfold highRawSampleVarianceDerivative
    refine continuous_const.mul (continuous_finset_sum _ fun _ _ => (continuous_finset_prod _ fun _ _ => ?_).mul continuous_const)
    have htm (f : ℝ) (y : Fin 3) : Continuous fun V => ternaryMass a f V y := by
      fin_cases y <;> simp only [ternaryMass, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> fun_prop
    exact (htm _ _).comp (by fun_prop)
  have happ (j : J) : Measurable fun z : ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))) =>
      highAppendLikelihoodAction dependent hsymm π activation n a (v - η ^ 2 * z.1) p F j z.2.1 z.2.2 := by
    have hc : Measurable fun z :
        (ℝ × (HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)))) × E =>
        (z.1.1, (historyMarkedAppend dependent hsymm j (z.1.2.1, z.2), z.1.2.2)) :=
      (measurable_fst.comp measurable_fst).prodMk
        (((historyMarkedAppend_measurable dependent hsymm j).comp
          ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_fst)))
    exact ((ham.comp measurable_snd).mul
      ((highRawSampleLikelihood_time_measurable n a v η p F hp hF).comp hc)).stronglyMeasurable.integral_prod_right'.measurable
  exact (Finset.measurable_sum _ fun j _ => happ j).sub (hvar.const_mul (η ^ 2))

end MarginalScoreAndDeriv
end PosteriorAndTimeLikelihood
end NearlyMinimax
