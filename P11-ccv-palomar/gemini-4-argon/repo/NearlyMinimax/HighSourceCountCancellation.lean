module
public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.SpatialSubsetIntegral
public import NearlyMinimax.FinePairUnionMassAnnihilation
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
variable {d n F : ℕ} {T0 N : ℝ}
def pairLaplaceKernel (N r : ℝ) : ℝ := ∫ T in 0..N, T * Real.exp (-(T*r))
def fineAliasLaplaceKernel (T0 N r : ℝ) : ℝ := ∫ T in T0..N, T * Real.exp (-(T*r))
theorem exactEuclideanDistance_eq_euclideanNorm  (x y : Covariate d) :
    exactEuclideanDistance x y = euclideanNorm (fun i => x i - y i) := by
  unfold exactEuclideanDistance spatialSquaredDistance euclideanNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring
theorem laplace_linear_tail_integral  (hr : 0 < r) (A ) :
    (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) =
      (1 + A*r) * Real.exp (-(A*r)) / r^2 := by
  have he : (∫ T : ℝ in Ici A, T * Real.exp (-(T*r))) =
      Real.exp (-(r*A)) * (1/r^2 + A/r) := by
    simpa [Finset.sum_range_succ, mul_comm] using (gamma_polynomial_tail_integral hr A 1)
  rw [he, mul_comm r A]
  field_simp
theorem laplace_linear_tail_integrable  (hr : 0 < r) (A ) :
    IntegrableOn (fun T => T * Real.exp (-(T*r))) (Ici A) := by
  simpa [mul_comm] using gamma_polynomial_tail_integrable hr A 1
theorem pairLaplaceKernel_defect (N r ) (hr : 0 ≤ r) :
    1 - r^2 * pairLaplaceKernel N r = (1+N*r) * Real.exp (-(N*r)) := by
  by_cases hr0 : r = 0
  · simp [hr0]
  have h_pairLaplaceKernel_formula N : pairLaplaceKernel N r = (1 - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
    have hr  := (lt_of_le_of_ne hr (Ne.symm hr0))
    unfold pairLaplaceKernel
    rw [← intervalIntegral.integral_Ici_sub_Ici'
      (laplace_linear_tail_integrable hr 0) (laplace_linear_tail_integrable hr N),
      laplace_linear_tail_integral hr 0, laplace_linear_tail_integral hr N]
    simp only [zero_mul, add_zero, neg_zero, Real.exp_zero, mul_one]
    ring
  · rw [h_pairLaplaceKernel_formula]
    field_simp
    ring
theorem fineAliasLaplaceKernel_measurable (T0 N : ℝ) (hN : T0 ≤ N) :
    Measurable (fineAliasLaplaceKernel T0 N) := by
  unfold fineAliasLaplaceKernel
  simp_rw [intervalIntegral.integral_of_le hN]
  have hm : Measurable (fun rt : ℝ × ℝ => rt.2 * Real.exp (-(rt.2*rt.1))) := by fun_prop
  exact hm.stronglyMeasurable.integral_prod_right'.measurable
def spatialInverseFourConstant (d : ℕ) : ℝ :=
  d * volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) * ((d-5).factorial : ℝ)
theorem radial_inverse_four_monomial  (hd : 4 < d)  (hr : r ≠ 0) (T ) :
    r^(d-1) * (Real.exp (-(T*r))/r^4) = r^(d-5) * Real.exp (-(T*r)) := by
  calc
    _ = (r^(d-1)/r^4) * Real.exp (-(T*r)) := by ring
    _ = _ := by
      rw [show d-1 = d-5+4 by omega, pow_add]
      field_simp
theorem euclidean_fineAlias_squared_integrable_and_integral_le  (hd : 4 < d)
     (hT0 : 0 < T0) (hN : T0 ≤ N) :
    Integrable (fun z : EuclideanSpace ℝ (Fin d) => (fineAliasLaplaceKernel T0 N ‖z‖)^2) volume ∧
      (∫ z : EuclideanSpace ℝ (Fin d), (fineAliasLaplaceKernel T0 N ‖z‖)^2) ≤
        6 * spatialInverseFourConstant d / T0^(d-4) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
  have h_euclidean_inverse_four_exponential_integrable {T} (hT : 0 < T) : Integrable (fun z : EuclideanSpace ℝ (Fin d) => Real.exp (-(T*‖z‖))/‖z‖^4) volume := by
    let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
    apply (integrable_fun_norm_addHaar volume (f := fun r => Real.exp (-(T*r))/r^4)).2
    apply ((gamma_monomial_integrable hT (d-5)).mono_set Ioi_subset_Ici_self).congr_fun _ measurableSet_Ioi
    intro r hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
    exact (radial_inverse_four_monomial hd hr.ne' T).symm
  have henv := (h_euclidean_inverse_four_exponential_integrable hT0)
  have hb : ∀ᵐ z : EuclideanSpace ℝ (Fin d) ∂volume,
      (fineAliasLaplaceKernel T0 N ‖z‖)^2 ≤ 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) := by
    filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin d))] with z hz
    have hr  := norm_pos_iff.mpr hz
    have h_fineAliasLaplaceKernel_nonneg_le {r} (hr : 0 < r) (hT0 : 0 ≤ T0) : 0 ≤ fineAliasLaplaceKernel T0 N r ∧
        fineAliasLaplaceKernel T0 N r ≤ (1+T0*r)*Real.exp (-(T0*r))/r^2 := by
      constructor
      · unfold fineAliasLaplaceKernel
        apply intervalIntegral.integral_nonneg hN
        intro T hT
        exact mul_nonneg (hT0.trans hT.1) (Real.exp_pos _).le
      have h_fineAliasLaplaceKernel_formula T0 N : fineAliasLaplaceKernel T0 N r =
          ((1+T0*r)*Real.exp (-(T0*r)) - (1+N*r)*Real.exp (-(N*r))) / r^2 := by
        unfold fineAliasLaplaceKernel
        rw [← intervalIntegral.integral_Ici_sub_Ici'
          (laplace_linear_tail_integrable hr T0) (laplace_linear_tail_integrable hr N),
          laplace_linear_tail_integral hr T0, laplace_linear_tail_integral hr N]
        ring
      · rw [h_fineAliasLaplaceKernel_formula]
        exact div_le_div_of_nonneg_right (sub_le_self _ (by have := hT0.trans hN; positivity)) (sq_nonneg _)
    have hw := (h_fineAliasLaplaceKernel_nonneg_le hr hT0.le)
    have hp := pair_defect_exponential_absorption (T0*‖z‖) (mul_nonneg hT0.le hr.le)
    calc
      _ ≤ ((1+T0*‖z‖)*Real.exp (-(T0*‖z‖))/‖z‖^2)^2 := pow_le_pow_left₀ hw.1 hw.2 2
      _ = (1+T0*‖z‖)^2 * Real.exp (-(2*T0*‖z‖)) / ‖z‖^4 := by
        rw [div_pow, mul_pow, ← Real.exp_nat_mul,
          show (‖z‖^2)^2 = ‖z‖^4 by ring,
          show ((2 : ℕ) : ℝ) * -(T0*‖z‖) = -(2*T0*‖z‖) by ring]
      _ ≤ 6 * Real.exp (-(T0*‖z‖)) / ‖z‖^4 :=
        div_le_div_of_nonneg_right (by simpa only [mul_assoc] using hp) (by positivity)
      _ = _ := by ring
  have hi  :=
    (henv.const_mul 6).mono' (((fineAliasLaplaceKernel_measurable T0 N hN).comp continuous_norm.measurable).pow_const 2).aestronglyMeasurable (hb.mono fun z hz => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hz)
  refine ⟨hi, ?_⟩
  have h_euclidean_inverse_four_exponential_integral {T} (hT : 0 < T) : (∫ z : EuclideanSpace ℝ (Fin d), Real.exp (-(T*‖z‖))/‖z‖^4) =
      spatialInverseFourConstant d / T^(d-4) := by
    let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (by omega)
    rw [integral_fun_norm_addHaar volume (fun r => Real.exp (-(T*r))/r^4)]
    simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
    rw [(setIntegral_congr_fun measurableSet_Ioi (fun r hr => radial_inverse_four_monomial hd hr.ne' T)), ← integral_Ici_eq_integral_Ioi, gamma_monomial_integral hT, show d-5+1 = d-4 by omega]
    unfold spatialInverseFourConstant
    ring
  calc
    _ ≤ ∫ z : EuclideanSpace ℝ (Fin d), 6 * (Real.exp (-(T0*‖z‖))/‖z‖^4) :=
      integral_mono_ae hi (henv.const_mul 6) hb
    _ = _ := by rw [integral_const_mul, (h_euclidean_inverse_four_exponential_integral hT0)]; ring
theorem finePairTime_response_integral  [Fintype ι] [DecidableEq ι]
    (d ) [NeZero d] (lo hi ) (hlo : 0 ≤ lo)
    (u v ) (hu : u ∈ hyperplaneCube d) (hv : v ∈ hyperplaneCube d)
    (q C A c) (Φ : (ι → ℝ) → ℝ) :
    (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      responseMatrixAction q C (finePairTimeMatrix d A e) c Φ
      ∂finePairTimeFieldMeasure d lo hi) =
      (∫ T in Icc lo hi, T * Real.exp (-T * euclideanNorm (fun r => u r - v r))) *
        responseMatrixAction q C A c Φ := by
  change (∫ e, finePairTimeFieldValue e u * finePairTimeFieldValue e v *
    responseMatrixAction q C (fun i j => e.1 * A i j) c Φ
    ∂finePairTimeFieldMeasure d lo hi) = _
  simp_rw [responseMatrixAction_scalar_matrix]
  have he (e : ℝ × FinePairFieldMark d) : finePairTimeFieldValue e u * finePairTimeFieldValue e v *
      (e.1 * responseMatrixAction q C A c Φ) =
      (e.1 * (finePairTimeFieldValue e u * finePairTimeFieldValue e v)) *
        responseMatrixAction q C A c Φ := by ring
  simp_rw [he]
  rw [integral_mul_const, finePairTimeFieldValue_weighted_covariance d lo hi hlo u v hu hv]
section SignedPacket
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]
def finePairResponseAtomBound (q : ℕ) (C : ℝ) (c : ι → ℝ) (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ h : HighResponseMarkIndex ι q,
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|
theorem finePairResponseAtomBound_le (q C c Φ)
    (h : HighResponseMarkIndex ι q) :
    |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)| ≤
      finePairResponseAtomBound q C c Φ := by
  exact Finset.single_le_sum
    (f := fun h =>
      |Φ (coefficientReset c (highResponseMarkAtom C q h).2 (highResponseMarkAtom C q h).1)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ h)
theorem ordinaryPairReset_measurable  (a b p)
    (ψ : Z → Fin n → ℝ) (hψ : ∀ i, Measurable (fun ζ => ψ ζ i))
    (z : ℝ) (eps : Fin 2 → ℝ) (i : Fin n) :
    Measurable (fun ζ => localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) := by
  exact measurable_const.add ((Finset.measurable_fun_sum _
    (fun l _ => (hψ i).const_mul (eps l))).const_mul _)
theorem ordinaryPairReset_atom_abs_le  (a b ) (ha : 0 < a) (hab : a < b)
    (m D p) (hp : ∀ i, p i ∈ Icc a b)
    (ψ : Fin n → ℝ) (hψ : ∀ i, |ψ i| ≤ 1)
    (e ) (i : Fin n) :
    |localDensityReset a b 2 (densityPacketAtom a b m 2 D e).1
      (densityPacketAtom a b m 2 D e).2 p (fun i _ => ψ i) i| ≤ b := by
  have hz := densityPacketAtom_mem a b hab.le m 2 D e
  have hh := localDensityReset_mem_interval a b ha hab 2 (by omega) _ hz.1 _ hz.2 p
    (fun i _ => ψ i) i
    (hp i) (fun _ => hψ i)
  rw [abs_of_nonneg (ha.le.trans hh.1)]
  exact hh.2
theorem ordinaryPairPacket_pair_action (σ ) [IsFiniteMeasure σ]
    (a b ) (ha : 0 < a) (hab : a < b) (m D q ) (hm : 2 ≤ m) (hD : 2 ≤ D)
    (C A) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : Fin 2 → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin 2 → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) =
      (p 0 * p 1) * (∫ ζ, ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^2) (by positivity)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have h_ordinaryPairDensity_action (p : Fin 2 → ℝ) (ψ : Fin 2 → ℝ) : densityPacketAction a b m 2 D (fun z eps =>
      ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ i) i) =
      p 0 * p 1 * ψ 0 * ψ 1 := by
    have hh := density_packet_product_count_selector (Finset.univ : Finset (Fin 2))
      a b ha hab m 2 D (by omega) (by omega) (by simpa using hD)
      (by simpa using hm) p (fun i _ => ψ i)
    have h_densitySeparatedSym_identical_columns : densitySeparatedSym 2 (fun i _ => ψ i) Finset.univ = ψ 0 * ψ 1 := by
      let e : Fin 2 ≃ (Finset.univ : Finset (Fin 2)) :=
        (Equiv.subtypeUnivEquiv (fun i : Fin 2 => Finset.mem_univ i)).symm
      rw [densitySeparatedSym_eq_permutation_average 2 _ Finset.univ e]
      simp only [e, Equiv.subtypeUnivEquiv_symm_apply, Fin.prod_univ_two]
      simp [Fintype.card_perm]
    simpa only [Finset.card_univ, Fintype.card_fin, ite_true, (by simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin 2))), Finset.sum_singleton,
      Fin.prod_univ_two, h_densitySeparatedSym_identical_columns, mul_assoc] using hh
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, h_ordinaryPairDensity_action]
  have he (ζ : Z) : p 0 * p 1 * ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ =
      (p 0 * p 1) * (ψ ζ 0 * ψ ζ 1 * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [he]
  exact integral_const_mul _ _
theorem ordinaryPairPacket_small_count  (hn : n < 2)
    (σ ) [IsFiniteMeasure σ] (a b ) (ha : 0 < a) (hab : a < b)
    (m D q ) (hD : 1 ≤ D) (C A) (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, highPacketObservable a b m 2 D q C c
      (fun ζ z eps => ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ ζ i) i) Φ e
      ∂<•highPacketSignedMeasure σ a b m 2 D q C A) = 0 := by
  rw [highPacketSignedMeasure_factor_integral σ a b m 2 D q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => ordinaryPairReset_measurable a b p ψ hmψ z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (ordinaryPairReset_atom_abs_le a b ha hab m D p hp (ψ ζ) (hbψ ζ) e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have h_ordinaryPairDensity_action_small_count (p : Fin n → ℝ) (ψ : Fin n → ℝ) : densityPacketAction a b m 2 D (fun z eps =>
      ∏ i, localDensityReset a b 2 z eps p (fun i _ => ψ i) i) = 0 := by
    exact density_packet_product_zero_of_small_count Finset.univ a b ha hab m 2 D
      (by omega) hD (by simpa using (show n ≤ D by omega)) (by simpa using hn) p _
  unfold highSeparatedPacketAction
  simp_rw [densityPacketAction_mul_right, h_ordinaryPairDensity_action_small_count,
    zero_mul]
  exact integral_zero _ _
theorem finePairPacket_small_count  (hn : n < 2)
    (σ ) [IsFiniteMeasure σ] (a b ) (ha : 0 < a) (hab : a < b)
    (M q ) (C ) (A )
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) = 0 := by
  have hm (z eps : ℝ) (i : Fin n) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) i) := by
    exact measurable_const.add ((hmψ i).const_mul _)
  have h_finePairDensity_action_small_count (p : Fin n → ℝ) (ψ : Fin n → ℝ) : (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p ψ i)
      ∂<•finePairDensitySignedRule a b M) = 0 := by
    rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
    · simpa only [Finset.univ_eq_empty, Finset.prod_empty] using
        (by rw [finePairDensitySignedRule_integral a b M (fun _ _ => 1)]; simp [(by simpa only [pow_zero, mul_one] using fineModulation_moment_zero)])
    have h_finePairDensitySignedRule_linear_zero : (∫ᵛ e, finePairDensityReset a b e.1 e.2 p ψ (0 : Fin 1)
      ∂<•finePairDensitySignedRule a b M) = 0 := by
      rw [finePairDensitySignedRule_integral a b M (fun z eps => finePairDensityReset a b z eps p ψ (0 : Fin 1))]
      have he (z eps : ℝ) : finePairDensityReset a b z eps p ψ (0 : Fin 1) =
          z + (densityMargin a b z / b * p (0 : Fin 1) * ψ (0 : Fin 1)) * eps := by
        unfold finePairDensityReset
        ring
      simp_rw [he, fineModulation_affine_zero]
      simp
    · simpa only [Fin.prod_univ_one] using
        h_finePairDensitySignedRule_linear_zero
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n) (fun ζ e => finite_density_product_abs_bound _ b (ha.trans hab).le
      (fun i => finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ (ζ,e) i))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  simp_rw [h_finePairDensity_action_small_count, zero_mul]
  exact integral_zero _ _
end SignedPacket
theorem responseMatrixAction_matrix_add  [Fintype ι] [DecidableEq ι]
    (q C A B c) (Φ : (ι → ℝ) → ℝ) :
    responseMatrixAction q C (fun i j => A i j + B i j) c Φ =
      responseMatrixAction q C A c Φ + responseMatrixAction q C B c Φ := by
  simp only [responseMatrixAction_entry_sum, add_mul, Finset.sum_add_distrib]
section ActualRows
variable {d F : ℕ} [NeZero d]
def finePairUnitFirstAction  (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 2 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 2 D q C (fun _ => finePairUnitMatrix d F)
def finePairCoarseFirstAction  (ad bd T0 : ℝ) (D q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 2 D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd 2 z eps p
      (fun i _ => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•highPacketSignedMeasure (finePairTimeFieldMeasure d 0 T0) ad bd D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))
def finePairFineFirstAction  (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, finePairPacketObservable ad bd M q C c
    (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p
      (fun i => finePairTimeFieldValue ζ (U i)) i) Φ e
    ∂<•finePairPacketSignedMeasure (finePairTimeFieldMeasure d T0 N) ad bd M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d F))
def finePairThreeRowFirstAction  (ad bd T0 N : ℝ) (D M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  finePairUnitFirstAction ad bd D q C p c Φ + finePairCoarseFirstAction ad bd T0 D q C U p c Φ +
    finePairFineFirstAction ad bd T0 N M q C U p c Φ
theorem finePairThreeRow_count_two_numerator (hF : 3 ≤ F)
    (ad bd T0 N ) (ha : 0 < ad) (hab : ad < bd) (hT0 : 0 ≤ T0) (hN : T0 ≤ N)
    (D M q ) (hD : 2 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ) (hC : C ≠ 0)
    (U ) (hU : ∀ i, U i ∈ hyperplaneCube d)
    (p ) (hp : ∀ i, p i ∈ Icc ad bd) (g w )
    (c : HighFrameIndex d F → ℝ) (y : Fin 2 → Fin 3) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2 * (p 0 * p 1) * ∑ i, (w i)^2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η^2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  have h_finePairThreeRowFirstAction_pair (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) : finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = (p 0 * p 1) *
      responseMatrixAction q C
        (finePairCombinedMatrix d F (pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)))) c Φ := by
    have h_finePairUnitFirstAction_pair (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) : finePairUnitFirstAction ad bd D q C p c Φ =
        p 0 * p 1 * responseMatrixAction q C (finePairUnitMatrix d F) c Φ := by
      rw [finePairUnitFirstAction, ordinaryPairPacket_pair_action (Measure.dirac ()) ad bd ha hab D D q hD hD C
        (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const)
        (integrable_const _) c p hp (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num)]
      simp
    have h_finePairCoarseFirstAction_pair (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) : finePairCoarseFirstAction ad bd T0 D q C U p c Φ = (p 0 * p 1) *
        ((∫ T in Icc 0 T0, T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) *
          responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
      rw [finePairCoarseFirstAction, ordinaryPairPacket_pair_action _ ad bd ha hab D D q hD hD C
        _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T0 _)
        c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
        (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
        (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le), finePairTime_response_integral d 0 T0 (le_refl 0) (U 0) (U 1) (hU 0) (hU 1)]
    have h_finePairFineFirstAction_pair (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) : finePairFineFirstAction ad bd T0 N M q C U p c Φ = (p 0 * p 1) *
        ((∫ T in Icc T0 N, T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) *
          responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) := by
      unfold finePairFineFirstAction
      simp only [Fin.prod_univ_two]
      rw [finePairPacketSignedMeasure_pair_action _ ad bd ha hab M q hM C
        _ (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _)
        c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
        (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
        (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) 0 1
        Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ), finePairTime_response_integral d T0 N hT0 (U 0) (U 1) (hU 0) (hU 1)]
    rw [finePairThreeRowFirstAction, h_finePairUnitFirstAction_pair,
      h_finePairCoarseFirstAction_pair,
      h_finePairFineFirstAction_pair]
    change _ = (p 0 * p 1) * responseMatrixAction q C
      (fun i j => finePairUnitMatrix d F i j +
        pairLaplaceKernel N (exactEuclideanDistance (U 0) (U 1)) * finePairDistanceMatrix d F i j) c Φ
    rw [responseMatrixAction_matrix_add, responseMatrixAction_scalar_matrix, exactEuclideanDistance_eq_euclideanNorm]
    have h_pairLaplaceKernel_split (r) : (∫ T in Icc 0 T0, T * Real.exp (-(T*r))) +
        (∫ T in Icc T0 N, T * Real.exp (-(T*r))) = pairLaplaceKernel N r := by
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hT0, ← intervalIntegral.integral_of_le hN]
      exact intervalIntegral.integral_add_adjacent_intervals
        (by apply Continuous.intervalIntegrable; fun_prop)
        (by apply Continuous.intervalIntegrable; fun_prop)
    have hsplit := (h_pairLaplaceKernel_split (euclideanNorm (fun r => U 0 r - U 1 r)))
    have he : (fun T => T * Real.exp (-T * euclideanNorm (fun r => U 0 r - U 1 r))) =
        (fun T => T * Real.exp (-(T * euclideanNorm (fun r => U 0 r - U 1 r)))) := by
      funext T
      congr 2
      ring
    rw [he, ← hsplit]
    ring
  have h_finePairResponseCountTwo_numerator (W) : (p 0 * p 1) * responseMatrixAction q C (finePairCombinedMatrix d F W) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η ^ 2 * (p 0 * p 1) * ∑ i, (w i) ^ 2 *
        highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i =
      η ^ 2 * w 0 * w 1 * p 0 * p 1 *
        (1 - W * spatialSquaredDistance (U 0) (U 1)) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
    rw [high_response_matrix_two_general q hq C a V η (finePairCombinedMatrix d F W) hC
      (finePairCombinedMatrix_symmetric d F W), Fin.sum_univ_two]
    simp only [finePairCombinedMatrix_kernel hF, spatialSquaredDistance, sub_self,
      zero_pow (by norm_num : ↑2 ≠ 0), Finset.sum_const_zero, mul_zero, sub_zero, mul_one]
    ring
  rw [h_finePairThreeRowFirstAction_pair,
    (h_finePairResponseCountTwo_numerator _)]
  have hr : 0 ≤ exactEuclideanDistance (U 0) (U 1) := Real.sqrt_nonneg _
  have hsq : (exactEuclideanDistance (U 0) (U 1))^2 = spatialSquaredDistance (U 0) (U 1) :=
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [← hsq, mul_comm (pairLaplaceKernel _ _), pairLaplaceKernel_defect N _ hr]
theorem finePairThreeRowFirstAction_small_count  (hn : n < 2)
    (ad bd T0 N ) (ha : 0 < ad) (hab : ad < bd) (D M q ) (hD : 1 ≤ D)
    (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairThreeRowFirstAction ad bd T0 N D M q C U p c Φ = 0 := by
  have hunit : finePairUnitFirstAction ad bd D q C p c Φ = 0 := by
    exact ordinaryPairPacket_small_count hn (Measure.dirac ()) ad bd ha hab D D q hD C
      (fun _ => finePairUnitMatrix d F) (fun _ _ => measurable_const) (integrable_const _) c p hp
      (fun _ _ => 1) (fun _ => measurable_const) (by intro _ _; norm_num) Φ
  have hcoarse : finePairCoarseFirstAction ad bd T0 D q C U p c Φ = 0 := by
    exact ordinaryPairPacket_small_count hn _ ad bd ha hab D D q hD C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d 0 T0 _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  have hfine : finePairFineFirstAction ad bd T0 N M q C U p c Φ = 0 := by
    exact finePairPacket_small_count hn _ ad bd ha hab M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _) c p hp
      (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le) Φ
  simp only [finePairThreeRowFirstAction, hunit, hcoarse, hfine, add_zero]
end ActualRows
def finePairEvenSelector (j : ℕ) : ℝ := if j = 0 then 0 else if Even j then 1 else 0
theorem finePairEvenSelector_split (j ) :
    finePairEvenSelector j = (if j = 2 then 1 else 0) +
      (if 4 ≤ j ∧ Even j then 1 else 0) := by
  by_cases hj0 : j = 0
  · simp [finePairEvenSelector, hj0]
  by_cases hj2 : j = 2
  · simp [finePairEvenSelector, hj2]
  by_cases hj : Even j
  · have hj4 : 4 ≤ j := by rcases hj with ⟨l, hl⟩; omega
    simp [finePairEvenSelector, hj0, hj2, hj, hj4]
  · simp [finePairEvenSelector, hj0, hj2, hj]
theorem finePairTimeField_product_measurable  (U : Fin n → Covariate d)
    (S : Finset (Fin n)) :
    Measurable (fun e : ℝ × FinePairFieldMark d => ∏ i ∈ S, finePairTimeFieldValue e (U i)) :=
  Finset.measurable_fun_prod S (fun i _ =>
    (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
theorem finePairTimeField_product_abs  (U : Fin n → Covariate d)
    (S : Finset (Fin n)) (e : ℝ × FinePairFieldMark d) :
    |∏ i ∈ S, finePairTimeFieldValue e (U i)| = 1 := by
  rw [Finset.abs_prod]
  simp only [finePairTimeFieldValue_abs, Finset.prod_const_one]
theorem finePairTimeField_weighted_product_integrable  [NeZero d]
    (lo hi ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    Integrable (fun e : ℝ × FinePairFieldMark d =>
      e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i))) (finePairTimeFieldMeasure d lo hi) :=
  (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
    (finePairTimeField_product_measurable U S).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, finePairTimeField_product_abs])
def finePairTimeSubsetMoment  (lo hi : ℝ) (U : Fin n → Covariate d)
    (S : Finset (Fin n)) : ℝ :=
  ∫ e : ℝ × FinePairFieldMark d,
    e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) ∂finePairTimeFieldMeasure d lo hi
theorem finePairTimeSubsetMoment_actual  [NeZero d]
    (lo hi : ℝ) (U : Fin n → Covariate d) (S : Finset (Fin n)) :
    finePairTimeSubsetMoment lo hi U S =
      ∫ T in Icc lo hi, T * (∫ z, ∏ i ∈ S, boundedHyperplaneFieldValue z (U i)
        ∂boundedHyperplaneFieldLaw d T) := by
  rw [finePairTimeSubsetMoment, finePairTimeFieldMeasure_integral d lo hi _
    (finePairTimeField_weighted_product_integrable lo hi U S)]
  simp only [finePairTimeFieldValue, integral_const_mul]
section Generic
variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace ι]
  [MeasurableSingletonClass ι] [MeasurableSpace Z]
theorem finePairPacket_even_subset_expansion 
    (σ ) [IsFiniteMeasure σ] (a b ) (ha : 0 < a) (hab : a < b)
    (M q C A)
    (hA : ∀ i j, Measurable (fun ζ => A ζ i j))
    (hcost : Integrable (separatedMatrixCost A) σ) (c )
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc a b) (ψ : Z → Fin n → ℝ)
    (hmψ : ∀ i, Measurable (fun ζ => ψ ζ i)) (hbψ : ∀ ζ i, |ψ ζ i| ≤ 1)
    (Φ : (ι → ℝ) → ℝ) :
    (∫ᵛ e, finePairPacketObservable a b M q C c
      (fun ζ z eps => ∏ i, finePairDensityReset a b z eps p (ψ ζ) i) Φ e
      ∂<•finePairPacketSignedMeasure σ a b M q C A) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          (∫ ζ, (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ ∂σ) := by
  have hm (z eps : ℝ) (i : Fin n) :
      Measurable (fun ζ => finePairDensityReset a b z eps p (ψ ζ) i) := by
    exact measurable_const.add ((hmψ i).const_mul _)
  rw [finePairPacketSignedMeasure_factor_integral σ a b M q C A hA hcost c _
    (fun z eps => Finset.measurable_fun_prod _ (fun i _ => hm z eps i))
    (b^n) (pow_nonneg (ha.trans hab).le n) (fun ζ e =>
      finite_density_product_abs_bound _ b (ha.trans hab).le
        (fun i => finePairFieldReset_abs_le a b ha hab M p hp ψ hbψ (ζ,e) i))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hi (W : Finset (Fin n)) :
      Integrable (fun ζ => (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) σ := by
    apply (responseMatrixAction_integrable σ q C A (separatedMatrix_entry_integrable σ A hA hcost) c Φ).bdd_mul (c := 1)
      (Finset.measurable_fun_prod W (fun i _ => hmψ i)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ζ => by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => hbψ ζ i)).trans_eq
        (Finset.prod_const_one)
  have hsubset (ζ : Z) :
      (∫ᵛ e, (∏ i, finePairDensityReset a b e.1 e.2 p (ψ ζ) i)
        ∂<•finePairDensitySignedRule a b M) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
          finePairEvenSelector W.card := by
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, finePairEvenSelector] using
      finePairDensitySignedRule_product_expansion a b M Finset.univ p (ψ ζ)
  simp_rw [hsubset]
  have he (W : Finset (Fin n)) (ζ : Z) :
      finePairCountCoefficient a b M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
        finePairEvenSelector W.card * responseMatrixAction q C (A ζ) c Φ =
      (finePairCountCoefficient a b M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card) *
        ((∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) := by ring
  simp_rw [Finset.sum_mul, he]
  rw [integral_finsetSum _ (fun W _ => (hi W).const_mul _)]
  simp only [integral_const_mul]
end Generic
def finePairPairAliasAction  (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * (if W.card = 2 then 1 else 0) *
      finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ
def finePairEvenFieldAction  (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) *
      (if 4 ≤ W.card ∧ Even W.card then 1 else 0) *
        finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ
theorem finePairFineFirstAction_alias_even_field  [NeZero d]
    (ad bd T0 N ) (ha : 0 < ad) (hab : ad < bd) (M q C)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      finePairPairAliasAction ad bd T0 N M q C U p c Φ +
        finePairEvenFieldAction ad bd T0 N M q C U p c Φ := by
  have h_finePairFineFirstAction_even_subset_expansion : finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * finePairEvenSelector W.card *
          finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by
    rw [finePairFineFirstAction, finePairPacket_even_subset_expansion _ ad bd ha hab M q C _
      (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _)
      c p hp (fun ζ i => finePairTimeFieldValue ζ (U i))
      (fun i => (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd)
      (fun ζ i => (finePairTimeFieldValue_abs ζ (U i)).le)]
    apply Finset.sum_congr rfl
    intro W _
    change _ * (∫ e : ℝ × FinePairFieldMark d, (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
      responseMatrixAction q C (fun i j => e.1 * finePairDistanceMatrix d F i j) c Φ
      ∂finePairTimeFieldMeasure d T0 N) = _
    simp_rw [responseMatrixAction_scalar_matrix]
    have he (e : ℝ × FinePairFieldMark d) :
        (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
          (e.1 * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) =
        (e.1 * (∏ i ∈ W, finePairTimeFieldValue e (U i))) *
          responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by ring
    simp_rw [he]
    rw [integral_mul_const]
    unfold finePairTimeSubsetMoment
    ring
  rw [h_finePairFineFirstAction_even_subset_expansion]
  simp only [finePairEvenSelector_split, finePairPairAliasAction, finePairEvenFieldAction,
    mul_add, add_mul, Finset.sum_add_distrib]
end
section
variable {d n D : ℕ} {L T : ℝ}
theorem centeredCardinalBandMatrix_eq_difference  (i : Fin n) (lam : ℝ)
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T)
    (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    centeredCardinalBandMatrix i lam L T U β β' =
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i T) -
      (∫ t, spatialCenteredCardinalMatrix i lam U t β β' ∂spatialScaleMeasure i L) := by
  have h_spatial_scale_domain_mono : spatialScaleDomain i L ⊆ spatialScaleDomain i T := by
    have hL : 0 < L := lt_of_lt_of_le (by norm_num) hL
    intro t ht
    refine ⟨ht.1, ?_⟩
    exact (show spatialScaleLogSum i t ≤ 2 * Real.log L from ht.2).trans
      (mul_le_mul_of_nonneg_left (Real.log_le_log hL hLT) (by norm_num))
  exact setIntegral_sdiff (spatial_scale_domain_isClosed i L).measurableSet
    (spatial_centered_cardinal_matrix_integrable i lam T hT U β β')
    h_spatial_scale_domain_mono
theorem centeredCardinalBandMatrix_continuous  (i : Fin n) (lam : ℝ)
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) (β β' : HighFrameIndex d D) :
    Continuous (fun U => centeredCardinalBandMatrix i lam L T U β β') := by
  simp_rw [centeredCardinalBandMatrix_eq_difference i lam hL hT hLT]
  exact (continuous_parametric_integral_of_continuous
    (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
    (spatial_scale_domain_isCompact i T hT)).sub
      (continuous_parametric_integral_of_continuous
        (spatial_centered_cardinal_matrix_joint_continuous i lam β β')
        (spatial_scale_domain_isCompact i L hL))
theorem centeredCardinalBandMatrix_l1_square_measurable  (i : Fin n) (lam : ℝ)
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Measurable (fun U : Fin n → Covariate d => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2) := by
  exact (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
    (fun β' _ => (centeredCardinalBandMatrix_continuous i lam hL hT hLT β β').measurable.abs))).pow_const 2
def cardinalBandSquareBudget (d n : ℕ) (L : ℝ) : ℝ :=
  ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) *
    L ^ (4 - (d : ℝ)) * (1 + Real.log L) ^ (n - 2)
theorem centeredCardinalBandMatrix_joint_integrable  (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n)  (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun z : Covariate d × (SpatialScaleIndex i → Covariate d) =>
      spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
        (spatialInterpolationLambda d) L T z.1 z.2) ^ 2)
      ((volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) := by
  let f : Covariate d × (SpatialScaleIndex i → Covariate d) → ℝ := fun z =>
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
  have hm : Measurable f := (centeredCardinalBandMatrix_l1_square_measurable
    (D := D) i (spatialInterpolationLambda d) hL hT hLT).comp (cardinalHeadSplit i).symm.measurable
  have hx : ∀ᵐ x ∂volume.restrict (spatialPatchBox d), x ∈ spatialPatchBox d :=
    ae_restrict_mem measurableSet_Icc
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hx.mono (fun x hx => anchored_centered_band_matrix_l1_square_integrable i
    (by unfold spatialInterpolationLambda; positivity) hT L x hx), ?_⟩
  apply (integrable_const (cardinalBandSquareBudget d n L)).mono' (hm.norm.stronglyMeasurable.integral_prod_right.aestronglyMeasurable)
  filter_upwards [hx] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
  simp only [f, Real.norm_eq_abs, abs_sq]
  exact anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT
theorem centeredCardinalBandMatrix_full_integrable  (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n)  (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2) (fullSpatialPatchDesign d n) := by
  exact (((cardinalHeadSplit_measurePreserving i (volume.restrict (spatialPatchBox d))).symm).integrable_comp_emb (cardinalHeadSplit i).symm.measurableEmbedding).mp
      (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)
theorem centeredCardinalBandMatrix_full_integral_le  (hd : 5 ≤ d) (hn : 2 ≤ n)
    (i : Fin n)  (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ U, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T U) ^ 2 ∂fullSpatialPatchDesign d n) ≤
      (2 : ℝ) ^ d * cardinalBandSquareBudget d n L := by
  rw [fullSpatialPatchDesign_split i _]
  change (∫ z : Covariate d × (SpatialScaleIndex i → Covariate d),
    spatialMatrixL1 (anchoredCenteredCardinalBandMatrix (D := D) i
      (spatialInterpolationLambda d) L T z.1 z.2) ^ 2
      ∂(volume.restrict (spatialPatchBox d)).prod (spatialPatchDesignMeasure i d)) ≤ _
  rw [integral_prod _ (centeredCardinalBandMatrix_joint_integrable hd hn i hL hT hLT)]
  apply (integral_mono_ae ((centeredCardinalBandMatrix_joint_integrable (D := D) hd hn i hL hT hLT).integral_prod_left) (integrable_const _) (by filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx; exact anchored_centered_band_matrix_l1_square_integral_le hd hn i x hx hL hT)).trans_eq
  simp only [integral_const, smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  change volume.real (spatialPatchBox d) * cardinalBandSquareBudget d n L = _
  rw [spatialPatchBox_real_volume]
def globalCardinalBandMatrix  (lam L T : ℝ) (U : Fin n → Covariate d)
    (β β' : HighFrameIndex d D) : ℝ :=
  integratedCardinalMatrix lam T U β β' - integratedCardinalMatrix lam L U β β'
theorem cardinal_matrix_l1_sum_le   [Fintype I]
    (A : I → HighFrameIndex d D → HighFrameIndex d D → ℝ) :
    spatialMatrixL1 (fun β β' => ∑ i, A i β β') ≤ ∑ i, spatialMatrixL1 (A i) := by
  calc
    _ ≤ ∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D, ∑ i : I, |A i β β'| :=
      Finset.sum_le_sum (fun β _ => Finset.sum_le_sum (fun β' _ => Finset.abs_sum_le_sum_abs _ _))
    _ = ∑ β : HighFrameIndex d D, ∑ i : I, ∑ β' : HighFrameIndex d D, |A i β β'| := by
      apply Finset.sum_congr rfl
      intro β _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm
theorem globalCardinalBandMatrix_square_le_sum  (lam )
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) (U : Fin n → Covariate d) :
    spatialMatrixL1 (globalCardinalBandMatrix (D := D) lam L T U) ^ 2 ≤
      ↑n * ∑ i, spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U) ^ 2 := by
  have he : globalCardinalBandMatrix (D := D) lam L T U =
      fun β β' => ∑ i, centeredCardinalBandMatrix i lam L T U β β' := by
    funext β β'
    simp only [globalCardinalBandMatrix, integratedCardinalMatrix, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ =>
      (centeredCardinalBandMatrix_eq_difference i lam hL hT hLT U β β').symm)
  rw [he]
  have hsum := cardinal_matrix_l1_sum_le (fun i : Fin n =>
    centeredCardinalBandMatrix (D := D) i lam L T U)
  apply ((sq_le_sq₀ (spatial_matrix_l1_nonnegative _)
    (Finset.sum_nonneg (fun i _ => spatial_matrix_l1_nonnegative _))).mpr hsum).trans
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin n => ↑1) (fun i => spatialMatrixL1 (centeredCardinalBandMatrix (D := D) i lam L T U))
theorem globalCardinalBandMatrix_square_integrable  (hd : 5 ≤ d) (hn : 2 ≤ n)
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    Integrable (fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2)
      (fullSpatialPatchDesign d n) := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul ↑n
  have hm : Measurable (fun U : Fin n → Covariate d =>
      spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2) := by
    exact (Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT β β').measurable.abs))).pow_const 2
  apply hi.mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs, abs_sq]
    exact globalCardinalBandMatrix_square_le_sum (spatialInterpolationLambda d) hL hT hLT U)
theorem globalCardinalBandMatrix_square_integral_le  (hd : 5 ≤ d) (hn : 2 ≤ n)
     (hL : 1 ≤ L) (hT : 1 ≤ T) (hLT : L ≤ T) :
    (∫ U, spatialMatrixL1 (globalCardinalBandMatrix (D := D) (spatialInterpolationLambda d) L T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ n ^ 2 * 2 ^ d * cardinalBandSquareBudget d n L := by
  have hi := (integrable_finsetSum Finset.univ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)).const_mul ↑n
  have hh := integral_mono (globalCardinalBandMatrix_square_integrable (D := D) hd hn hL hT hLT)
    hi (globalCardinalBandMatrix_square_le_sum (spatialInterpolationLambda d) hL hT hLT)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ =>
    centeredCardinalBandMatrix_full_integrable (D := D) hd hn i hL hT hLT)] at hh
  apply hh.trans
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun i _ =>
    centeredCardinalBandMatrix_full_integral_le (D := D) hd hn i hL hT hLT)
  convert (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n)) using 1 <;> simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] <;> ring
theorem integratedCardinalMatrix_full_square_integrable  (hd : 5 ≤ d) (hn : 2 ≤ n)
     (hT : 1 ≤ T) :
    Integrable (fun U => spatialMatrixL1 (integratedCardinalMatrix (D := D)
      (spatialInterpolationLambda d) T U) ^ 2) (fullSpatialPatchDesign d n) := by
  have he (U : Fin n → Covariate d) : globalCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hi := globalCardinalBandMatrix_square_integrable (D := D) hd hn (le_refl 1) hT hT
  simp_rw [he] at hi
  exact hi
theorem integratedCardinalMatrix_full_square_integral_le  (hd : 5 ≤ d) (hn : 2 ≤ n)
     (hT : 1 ≤ T) :
    (∫ U, spatialMatrixL1 (integratedCardinalMatrix (D := D) (spatialInterpolationLambda d) T U) ^ 2
      ∂fullSpatialPatchDesign d n) ≤ n ^ 2 * 2 ^ d *
      ((100 * d) ^ 2 * 16 * spatialScaleIntegralConstant d) ^ (n - 1) := by
  have he (U : Fin n → Covariate d) : globalCardinalBandMatrix (D := D)
      (spatialInterpolationLambda d) 1 T U =
      integratedCardinalMatrix (spatialInterpolationLambda d) T U := by
    unfold globalCardinalBandMatrix
    rw [integrated_cardinal_matrix_one_eq_zero hn]
    simp
  have hb := globalCardinalBandMatrix_square_integral_le (D := D) hd hn (le_refl 1) hT hT
  simp_rw [he] at hb
  simpa only [cardinalBandSquareBudget, Real.one_rpow, Real.log_one, add_zero, one_pow, mul_one] using hb
end
variable {d n : ℕ}
def higherBandFirstAction  (ad bd lam L T : ℝ) (r m D q : ℕ)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd m r D q C c
    (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
      (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ e
    ∂<•higherBandSignedRow d r m D q ad bd C lam L T fine
theorem higherBandFirstAction_count_expansion 
    (ad bd lam L T ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C fine U) (hU : ∀ i j, |U i j| ≤ 2)
    (p ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c Φ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (separatedSubsetMatrix (higherBandCarrierMeasure d r L T fine) r
              (fun ζ i l => higherBandCarrierFactor d r lam fine ζ l (U i))
              (higherBandCarrierAmplitude d r D lam fine) S) c Φ := by
  have h_higherBandFirstAction_eq_packet : higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      highSeparatedPacketAction (higherBandCarrierMeasure d r L T fine)
        ad bd m r D q C (higherBandCarrierAmplitude d r D lam fine) c
        (fun ζ z eps => ∏ i, localDensityReset ad bd r z eps p
          (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) Φ := by
    letI := higherBandCarrierMeasure_finite d r L T hT fine
    have hm (i : Fin n) (l : Fin r) :
        Measurable (fun ζ => higherBandCarrierFactor d r lam fine ζ l (U i)) :=
      (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
        (measurable_id.prodMk measurable_const)
    have hG z (eps : Fin r → ℝ) : Measurable
        (fun ζ => ∏ i, localDensityReset ad bd r z eps p
          (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i) := by
      apply Finset.measurable_fun_prod
      intro i _
      exact measurable_const.add ((Finset.measurable_fun_sum _
        (fun l _ => (hm i l).const_mul (eps l))).const_mul _)
    have hb (ζ : HigherBandCarrier d r fine) (e : HighDensityMarkIndex m r D)
        (i : Fin n) : |localDensityReset ad bd r
          (densityPacketAtom ad bd m r D e).1 (densityPacketAtom ad bd m r D e).2 p
          (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i| ≤ bd := by
      have he := densityPacketAtom_mem ad bd hab.le m r D e
      have hh := localDensityReset_mem_interval ad bd ha hab r hr _ he.1 _ he.2 p
        (fun i l => higherBandCarrierFactor d r lam fine ζ l (U i)) i (hp i)
        (fun l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i))
      rw [abs_of_nonneg (ha.le.trans hh.1)]
      exact hh.2
    exact highPacketSignedMeasure_factor_integral _ ad bd m r D q C _
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
      c _ hG (bd^n) (pow_nonneg (ha.trans hab).le n)
      (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb ζ e))
      Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)
  rw [h_higherBandFirstAction_eq_packet]
  have hm (i : Fin n) (l : Fin r) :
      Measurable (fun ζ => higherBandCarrierFactor d r lam fine ζ l (U i)) :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_id.prodMk measurable_const)
  simpa only [Finset.card_univ, Fintype.card_fin] using
    highSeparatedPacketAction_row (higherBandCarrierMeasure d r L T fine) ad bd ha hab
      m r D q hr hD Finset.univ (by simpa using hnD) p _ hm
      (fun ζ i l => higherBandCarrierFactor_bound d r lam fine ζ l (U i) (hU i)) C _
      (higherBandCarrierAmplitude_measurable d r D lam fine)
      (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine) c Φ
theorem higherBandFirstAction_zero_small_count 
    (ad bd lam L T ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D) (hnr : n < r)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ]
  have he : (Finset.univ : Finset (Fin n)).powersetCard r = ∅ :=
    Finset.powersetCard_eq_empty.mpr (by simpa using hnr)
  simp only [he, Finset.sum_empty, mul_zero]
theorem higherBandFirstAction_zero_other_count 
    (ad bd lam L T ) (ha : 0 < ad) (hab : ad < bd) (hT : 1 ≤ T)
    (r m D q ) (hr : 1 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (hnm : n ≤ m) (hne : n ≠ r) (C fine)
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ = 0 := by
  by_cases hnr : n < r
  · exact higherBandFirstAction_zero_small_count ad bd lam L T ha hab hT r m D q hr hD hnD
      hnr C fine U hU p hp c Φ
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q hr hD hnD
    C fine U hU p hp c Φ,
    densityCountCoefficient_exact ad bd ha hab m r n hr (by omega) hnm, if_neg hne, zero_mul]
def higherBandActualMatrix {d n D : ℕ} (lam L T : ℝ) (fine : Bool)
    (U : Fin n → Covariate d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  if fine then globalCardinalBandMatrix lam L T U else integratedCardinalMatrix lam T U
theorem higherBandFirstAction_actual_count_expansion 
    (ad bd lam L T ) (ha : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    (hL : 0 < L) (hT : 1 ≤ T) (r m D q ) (hr : 2 ≤ r) (hD : 1 ≤ D) (hnD : n ≤ D)
    (C : ℝ) (fine : Bool) (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFirstAction ad bd lam L T r m D q C fine U p c Φ =
      densityCountCoefficient ad bd m r n *
        ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, (∏ i ∈ S, p i) *
          responseMatrixAction q C
            (higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U)) c Φ := by
  have h_cardinal_density_subset_sym_eq (lam : ℝ) (S : Finset (Fin n)) (z : CardinalSeparatedMark d S.card) (U : Fin n → Covariate d) : densitySeparatedSym S.card (fun i l => cardinalSeparatedFactor lam z l (U i)) S =
      cardinalSeparatedSymmetricFactor lam z (spatialSubsetConfiguration S U) := by
    let e : Fin S.card ≃ S :=
      ((Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))).symm
    rw [densitySeparatedSym_eq_permutation_average S.card _ S e]
    congr 1
    apply Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin S.card)))
    intro τ
    have h := Equiv.prod_comp τ
      (fun l => cardinalSeparatedFactor lam z l (U (e (τ.symm l)).val))
    simp only [Equiv.symm_apply_apply] at h
    convert h using 1
    apply Finset.prod_congr rfl
    intro l _
    rfl
  rw [higherBandFirstAction_count_expansion ad bd lam L T ha hab hT r m D q (by omega)
    hD hnD C fine U hU p hp c Φ]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  have := (Finset.mem_powersetCard.mp hS).2
  have h_higherBand_subset_matrix_actual : separatedSubsetMatrix (higherBandCarrierMeasure d S.card L T fine) S.card
      (fun ζ i l => higherBandCarrierFactor d S.card lam fine ζ l (U i))
      (higherBandCarrierAmplitude d S.card D lam fine) S =
      higherBandActualMatrix lam L T fine (spatialSubsetConfiguration S U) := by
    have hS : 2 ≤ S.card := by omega
    have hb : ∀ l j, |spatialSubsetConfiguration S U l j| ≤ 2 := fun l => hU _
    funext β β'
    cases fine
    · change (∫ z, densitySeparatedSym S.card
          (fun i l => cardinalSeparatedFactor lam z l (U i)) S *
          cardinalSeparatedAmplitude lam z β β' ∂cardinalSeparatedMeasure d S.card T) = _
      simp_rw [h_cardinal_density_subset_sym_eq]
      exact (integrated_cardinal_symmetric_separated_exact lam hlam hT _ hb β β').symm
    · change (∫ z, densitySeparatedSym S.card
          (fun i l => cardinalSeparatedFactor lam z.2 l (U i)) S *
          cardinalBandAmplitude lam z β β' ∂cardinalBandMeasure d S.card L T) = _
      simp_rw [h_cardinal_density_subset_sym_eq]
      exact (integrated_cardinal_actual_band_separated_exact hS lam hlam hL hT _ hb β β').symm
  subst r
  rw [h_higherBand_subset_matrix_actual]
def singletonFirstAction  (ad bd : ℝ) (D q : ℕ) (C : ℝ)
    (p : Fin n → ℝ) (c : HighFrameIndex d D → ℝ)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∫ᵛ e, highPacketObservable ad bd D 1 D q C c
    (fun _ z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i) Φ e
    ∂<•highPacketSignedMeasure (Measure.dirac ()) ad bd D 1 D q C
      (fun _ => finePairUnitMatrix d D)
set_option maxHeartbeats 120000 in
theorem singletonFirstAction_eq_packet 
    (ad bd ) (ha : 0 < ad) (hab : ad < bd) (D q C)
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
      (fun _ _ => 1) i (hp i) (by intro _; norm_num)
    rw [abs_of_nonneg (ha.le.trans hh.1)]
    exact hh.2
  exact highPacketSignedMeasure_factor_integral (Z := Unit) (ι := HighFrameIndex d D)
    (Measure.dirac ()) ad bd D 1 D q C
    (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
    c (fun (_ : Unit) z eps => ∏ i, localDensityReset ad bd 1 z eps p (fun _ _ => 1) i)
    (fun _ _ => measurable_const) (bd^n) (pow_nonneg (ha.trans hab).le n)
    (fun _ e => finite_density_product_abs_bound _ bd (ha.trans hab).le (hb e))
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)
theorem singletonFirstAction_zero_other_count 
    (ad bd ) (ha : 0 < ad) (hab : ad < bd) (D q ) (hD : 1 ≤ D)
    (hnD : n ≤ D) (hne : n ≠ 1) (C )
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    singletonFirstAction ad bd D q C p c Φ = 0 := by
  rw [singletonFirstAction_eq_packet ad bd ha hab D q C p hp c Φ]
  by_cases hn : n = 0
  · subst n
    unfold highSeparatedPacketAction
    simp_rw [densityPacketAction_mul_right,
      density_packet_product_zero_of_small_count (Finset.univ : Finset (Fin 0))
        ad bd ha hab D 1 D (by norm_num) hD (by simp) (by simp) p (fun _ _ => 1), zero_mul]
    exact integral_zero _ _
  have hh := highSeparatedPacketAction_count_selector (Measure.dirac ()) ad bd ha hab D 1 D q
    (by norm_num) hD (Finset.univ : Finset (Fin n)) (by simpa using hnD)
    (by simpa using hnD) (by simpa using (show 1 ≤ n by omega)) p
    (fun _ => fun _ _ => 1) (fun _ _ => measurable_const)
    (by intro _ _ _; norm_num) C (fun _ => finePairUnitMatrix d D)
    (fun _ _ => measurable_const) (integrable_const _) c Φ
  simpa only [Finset.card_univ, Fintype.card_fin, if_neg hne] using hh
theorem densitySeparatedSym_one  [DecidableEq α] (r )
    (S : Finset α) (hS : S.card = r) : densitySeparatedSym r (fun _ _ => 1) S = 1 := by
  rw [densitySeparatedSym_eq_permutation_average r _ S (((Fintype.equivFin S).trans (finCongr ((Fintype.card_coe S).trans hS))).symm)]
  simp only [Finset.prod_const_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_perm, Fintype.card_fin]
  exact div_self (by positivity)
def completeSourceSignedFirstAction  (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
    singletonFirstAction ad bd D q C p c Φ +
    ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ
def completeSourceRawNumerator  (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C a V η : ℝ) (U : Fin n → Covariate d) (p g w : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) : ℝ :=
  completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c
    (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
    η^2 * (∏ i, p i) * ∑ i, (w i)^2 *
      highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i
def higherBandFamilyFirstAction  (ad bd lam ℓ N μ : ℝ)
    (D M q : ℕ) (C : ℝ) (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) : ℝ :=
  ∑ i : HigherBandFamilyIndex d D M q ad bd C lam ℓ N μ,
    higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
      (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q C i.val.2 U p c Φ
theorem higherBandFamilyFirstAction_zero_small_count 
    (ad bd lam ℓ N μ ) (ha : 0 < ad) (hab : ad < bd)
    (D M q ) (hD : 1 ≤ D) (hnD : n ≤ D) (hn : n ≤ 2) (C )
    (U : Fin n → Covariate d) (hU : ∀ i j, |U i j| ≤ 2)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have := (higherBandFamily_target_bounds d D M q ad bd C lam ℓ N μ i).1
  exact higherBandFirstAction_zero_small_count ad bd lam ℓ _ ha hab i.property.1
    _ _ D q (by omega) hD hnD (by omega) C i.val.2 U hU p hp c Φ
theorem completeSourceSignedFirstAction_eq_family 
    (ad bd lam ℓ N μ D M q C)
    (U : Fin n → Covariate d) (p : Fin n → ℝ)
    (c : HighFrameIndex d D → ℝ) (Φ : (HighFrameIndex d D → ℝ) → ℝ) :
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q C U p c Φ =
      finePairThreeRowFirstAction ad bd ℓ N D M q C U p c Φ +
        singletonFirstAction ad bd D q C p c Φ +
        higherBandFamilyFirstAction ad bd lam ℓ N μ D M q C U p c Φ := rfl
theorem completeSourceRawNumerator_count_two  [NeZero d]
    (ad bd lam ℓ N μ ) (ha : 0 < ad) (hab : ad < bd) (hℓ : 0 ≤ ℓ) (hℓN : ℓ ≤ N)
    (D M q ) (hD : 3 ≤ D) (hM : 2 ≤ M) (hq : 2 ≤ q)
    (C a V η ) (hC : C ≠ 0) (U )
    (hU : ∀ i j, |U i j| ≤ 2) (hQ : ∀ i, U i ∈ hyperplaneCube d)
    (p g w ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c ) (y : Fin 2 → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      η^2 * w 0 * w 1 * p 0 * p 1 *
        ((1 + N * exactEuclideanDistance (U 0) (U 1)) *
          Real.exp (-(N * exactEuclideanDistance (U 0) (U 1)))) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 0) (y 0) *
        ternaryMeanDerivative a (coefficientRegression η g w (fun i => highFrameFeature (U i)) c 1) (y 1) := by
  unfold completeSourceRawNumerator
  rw [completeSourceSignedFirstAction_eq_family,
    singletonFirstAction_zero_other_count ad bd ha hab D q (by omega) (by omega) (by omega)
      C p hp c,
    higherBandFamilyFirstAction_zero_small_count ad bd lam ℓ N μ ha hab D M q (by omega)
      (by omega) (by omega) C U hU p hp c]
  simp only [add_zero, Fin.prod_univ_two]
  exact finePairThreeRow_count_two_numerator hD ad bd ℓ N ha hab hℓ hℓN D M q
    (by omega) hM hq C a V η hC U hQ p hp g w c y
end NearlyMinimax
