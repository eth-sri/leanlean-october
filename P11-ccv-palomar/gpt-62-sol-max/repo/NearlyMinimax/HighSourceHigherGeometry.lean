module

public import NearlyMinimax.HighSpatialEnvelopes
public import NearlyMinimax.HigherBandRawCollapse
public import NearlyMinimax.HighSourceHigherCounts
public import NearlyMinimax.OrdinaryFineAliasGeometryEnvelope

@[expose] public section

/-! Actual full higher-count source numerator and a deterministic geometric
square envelope. All signed rows are summed before the one heat correction. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem highCardinalRawNumerator_eq_matrix_heat {d n F : ℕ}
    (ad bd lam : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam)
    {T : ℝ} (hT : 1 ≤ T) (m D q : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m)
    (hnD : n ≤ D) (hnF : n ≤ F) (C a V η : ℝ) (hC : C ≠ 0)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3) :
    highCardinalRawNumerator ad bd lam T m D q C a V η U p g w c y =
      (∏ i, p i)*responseMatrixAction q C (integratedCardinalMatrix lam T U) c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) -
      η^2*(∏ i, p i)*∑ i, (w i)^2*highResponseVarianceTerm a V η g w (fun i => highFrameFeature (U i)) c y i := by
  rw [highCardinalRawNumerator_eq_alias_defect ad bd lam haD hab hlam hT m D q hn hnm hnD hnF
    C a V η hC U hU p g w hp c y, integrated_cardinal_response_heat hnF q C a V η lam T hC hT U g w c y]
  simp only [mul_sub, sub_mul, mul_one, Finset.sum_sub_distrib]
  ring

 theorem higherBandTargetScale_pos_of_physical {d n D : ℕ} (hn : 3 ≤ n) (hnD : n ≤ D)
    (N μ : ℝ) (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ) :
    0 < higherBandTargetScale d n N μ := by
  let j : Fin (D-2) := ⟨n-3, by omega⟩
  have hj : j.val+3 = n := by dsimp [j]; omega
  simpa only [hj] using hnu j

 theorem completeSourceRawNumerator_higher_components {d n : ℕ} [NeZero d]
    (ad bd lam ℓ N μ : ℝ) (haD : 0 < ad) (hab : ad < bd) (hlam : 0 ≤ lam) (hℓ : 1 ≤ ℓ)
    (D M q : ℕ) (hn : 3 ≤ n) (hnD : n ≤ D)
    (hnu : ∀ j : Fin (D-2), 0 < higherBandTargetScale d (j.val+3) N μ)
    (hFine : ∀ j : Fin (D-2), ℓ < higherBandTargetScale d (j.val+3) N μ → j.val+3 ≤ M)
    (C a V η : ℝ) (hC : C ≠ 0) (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (c : HighFrameIndex d D → ℝ) (y : Fin n → Fin 3) :
    completeSourceRawNumerator ad bd lam ℓ N μ D M q C a V η U p g w c y =
      highCardinalRawNumerator ad bd lam (max 1 (higherBandTargetScale d n N μ)) D D q C a V η U p g w c y +
      (if M<n then ordinaryFineAliasFamilyRawAction (ordinaryFineAliasTargetSet d D ℓ N μ)
        ad bd lam ℓ (fun r => higherBandTargetScale d r N μ) M q C a V η U p g w c y else 0) +
      (if M<n then finePairPairAliasAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) else 0) +
      finePairEvenFieldAction ad bd ℓ N M q C U p c
        (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y) := by
  have hnuN := higherBandTargetScale_pos_of_physical hn hnD N μ hnu
  have hmat : integratedCardinalMatrix (D := D) lam (max 1 (higherBandTargetScale d n N μ)) U =
      integratedCardinalMatrix lam (higherBandTargetScale d n N μ) U := by
    funext γ δ
    apply integrated_cardinal_matrix_max_one <;> omega
  rw [completeSourceRawNumerator_higher ad bd lam ℓ N μ haD hab D M q hn hnD C a V η U p g w hp c y,
    higherBandFamilyFirstAction_matched_and_full_fine_alias ad bd lam ℓ N μ haD hab hlam hℓ D M q hn hnD hnu hFine
      C a V η U hU p g w hp c y,
    highCardinalRawNumerator_eq_matrix_heat ad bd lam haD hab hlam (le_max_left _ _) D D q (by omega) hnD hnD hnD
      C a V η hC U hU p g w hp c y, hmat]
  by_cases hnM : M<n
  · simp only [if_pos hnM]
    ring
  · simp [if_neg hnM, finePairPairAliasAction_zero_selected_count ad bd ℓ N haD hab M q hn (le_of_not_gt hnM) C U p c] <;> ring

/-- Fixed scales and numerical parameters common to the four spatial energy components. -/
structure SourceGeometry (d : ℕ) where
  (D M R q : ℕ)
  (aD bD c0 ell N mu C a rho eta : ℝ)

namespace SourceGeometry
variable {d n : ℕ} (S : SourceGeometry d)

abbrev ad : ℝ := S.aD+(S.M : ℝ)⁻¹
abbrev bd : ℝ := S.bD-(S.M : ℝ)⁻¹
abbrev tau : ℝ := exteriorTau ((S.ad+S.bd)/(S.bd-S.ad))
abbrev scale (r : ℕ) := higherBandTargetScale d r S.N S.mu
abbrev targets := ordinaryFineAliasTargetSet d S.D S.ell S.N S.mu

abbrev cardinal (U : Fin n → Covariate d) :=
  cardinalGeometryEnvelope (F := S.D) S.q S.bd S.C S.a S.rho S.eta (max 1 (S.scale n)) U
abbrev ordinary (U : Fin n → Covariate d) :=
  ordinaryFineAliasFamilyResponseSquareEnvelope (F := S.D) S.targets
    S.M S.R S.q S.aD S.bD S.c0 S.C S.a S.rho S.eta S.ell S.scale U
abbrev aliasEnvelope (U : Fin n → Covariate d) :=
  finePairAliasGeometryEnvelope S.ad S.bd S.ell S.N S.M S.q S.C S.a S.rho S.eta U
abbrev field (U : Fin n → Covariate d) :=
  fineFieldGeometryEnvelope S.ad S.bd S.ell S.N S.M S.q S.C S.a S.rho S.eta U

def components (U : Fin n → Covariate d) : Fin 4 → ℝ :=
  ![S.cardinal U, if S.M<n then S.ordinary U else 0,
    if S.M<n then S.aliasEnvelope U else 0, S.field U]

def higherEnvelope (U : Fin n → Covariate d) : ℝ := 4 * ∑ i, S.components U i

theorem higherEnvelope_nonneg (U : Fin n → Covariate d) : 0 ≤ S.higherEnvelope U := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro i _
  fin_cases i <;> simp only [components, apply_ite]
  · exact cardinalGeometryEnvelope_nonneg _ _ _ _ _ _ _ U
  · split_ifs
    · exact ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ U
    · exact le_rfl
  · split_ifs
    · exact finePairAliasGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ U
    · exact le_rfl
  · exact fineFieldGeometryEnvelope_nonneg _ _ _ _ _ _ _ _ _ _ U

end SourceGeometry

 theorem completeSourceRawNumerator_higher_square_le_geometry {d n : ℕ} [NeZero d]
    (S : SourceGeometry d) (haD : 0 < S.aD) (hell : 1 ≤ S.ell)
    (hshrink : S.ad < S.bd) (htau : shrunkDensityExponent S.aD S.bD S.M ≤ S.c0)
    (hn : 3 ≤ n) (hnD : n ≤ S.D) (hq : 1 ≤ S.q)
    (hnu : ∀ j : Fin (S.D-2), 0 < S.scale (j.val+3))
    (hFine : ∀ j : Fin (S.D-2), S.ell < S.scale (j.val+3) → j.val+3 ≤ S.M)
    (hI : ∀ r ∈ S.targets, 1 ≤ r ∧ r ≤ S.R)
    (V : ℝ) (hC : 1 ≤ S.C) (ha : 0 < S.a) (heta : 0 ≤ S.eta) (hrho : 0 ≤ S.rho) (hetarho : S.eta ≤ S.rho/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : Fin n → ℝ) (hpD : ∀ i, p i ∈ Icc (S.ad) (S.bd))
    (hg : ∀ i, |g i| ≤ S.rho/2) (hw : ∀ i, |w i| ≤ 1) (c : HighFrameIndex d S.D → ℝ)
    (hc : ∑ γ, |c γ| ≤ S.C⁻¹) (hp : ∀ f : ℝ, |f| ≤ S.rho → ∀ u, 0 ≤ ternaryMass S.a f V u) :
    (∑ y : Fin n → Fin 3, completeSourceRawNumerator (S.ad) (S.bd)
      (spatialInterpolationLambda d) S.ell S.N S.mu S.D S.M S.q S.C S.a V S.eta U p g w c y^2) ≤
      S.higherEnvelope U := by
  let ad := S.ad
  let bd := S.bd
  have had : 0 < ad := by positivity
  have hlam : 0 ≤ spatialInterpolationLambda d := by unfold spatialInterpolationLambda; positivity
  let A := fun y => highCardinalRawNumerator ad bd (spatialInterpolationLambda d)
    (max 1 (S.scale n)) S.D S.D S.q S.C S.a V S.eta U p g w c y
  let B := fun y => if S.M<n then ordinaryFineAliasFamilyRawAction (S.targets)
    ad bd (spatialInterpolationLambda d) S.ell S.scale S.M S.q S.C S.a V S.eta U p g w c y else 0
  let P := fun y => if S.M<n then finePairPairAliasAction ad bd S.ell S.N S.M S.q S.C U p c
    (fun v => highResponseProduct S.a V S.eta g w (fun i => highFrameFeature (U i)) v y) else 0
  let F := fun y => finePairEvenFieldAction ad bd S.ell S.N S.M S.q S.C U p c
    (fun v => highResponseProduct S.a V S.eta g w (fun i => highFrameFeature (U i)) v y)
  have hA := highCardinalRawNumerator_sum_square_le_geometry (T := max 1 (S.scale n)) ad bd had hshrink (le_max_left _ _) S.D S.D S.q
    (by omega) hnD hnD hnD hq S.C S.a V S.eta S.rho hC ha heta hrho hetarho U hU p g w hpD hg hw c hc hp
  have hB : (∑ y, B y^2) ≤ (if S.M<n then S.ordinary U else 0) := by
    by_cases hMn : S.M<n
    · simp only [B, if_pos hMn]
      exact ordinaryFineAliasFamilyResponseSquareEnvelope_dominates _ S.aD S.bD S.c0 S.ell _ haD hshrink htau hI S.q
        (by omega) S.C S.a V S.eta S.rho hC ha heta hrho hetarho U hU (fun _ => p) (fun _ => g) (fun _ => w) (fun _ => c)
          (fun _ => hpD) (fun _ => hg) (fun _ => hw) (fun _ => hc) hp
    · simp [B, hMn]
  have hP : (∑ y, P y^2) ≤ (if S.M<n then S.aliasEnvelope U else 0) := by
    by_cases hMn : S.M<n
    · simp only [P, if_pos hMn]
      apply finePairPairAliasAction_sum_square_le_geometry <;> omega
    · simp [P, hMn]
  have hF := finePairEvenFieldAction_sum_square_le_geometry ad bd S.ell S.N had hshrink S.M S.q (by omega) S.C S.a V S.eta S.rho
    hC ha heta hrho hetarho U hU p g w hpD c hc hg hw hp
  have hb (y : Fin n → Fin 3) : completeSourceRawNumerator ad bd (spatialInterpolationLambda d) S.ell S.N S.mu
      S.D S.M S.q S.C S.a V S.eta U p g w c y^2 ≤ 4*(A y^2+B y^2+P y^2+F y^2) := by
    rw [completeSourceRawNumerator_higher_components ad bd _ S.ell S.N S.mu had hshrink hlam hell S.D S.M S.q hn hnD
      hnu hFine S.C S.a V S.eta (lt_of_lt_of_le zero_lt_one hC).ne' U hU p g w hpD c y]
    change (A y+B y+P y+F y)^2 ≤ _
    nlinarith only [sq_nonneg (A y-B y), sq_nonneg (P y-F y), sq_nonneg (A y+B y-P y-F y)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hb y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  apply h.trans
  rw [SourceGeometry.higherEnvelope, Fin.sum_univ_four]
  simp only [SourceGeometry.components, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three]
  exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hA hB) hP) hF) (by norm_num)

private theorem integrable_gate {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (P : Prop) [Decidable P] (hf : Integrable f μ) : Integrable (fun x => if P then f x else 0) μ := by
  by_cases h : P <;> simp [h, hf]

theorem SourceGeometry.higherEnvelope_integrable_and_eq {d r : ℕ} [NeZero d]
    (S : SourceGeometry d) (hd : 5 ≤ d) (hr : 2 ≤ r) (hell : 1 ≤ S.ell) (hellN : S.ell ≤ S.N) :
    Integrable (S.higherEnvelope (n := r)) (fullSpatialPatchDesign d r) ∧
    (∫ U, S.higherEnvelope U ∂fullSpatialPatchDesign d r) =
      4 * ∑ i, ∫ U, S.components U i ∂fullSpatialPatchDesign d r := by
  have hA := (cardinalGeometryEnvelope_integrable_and_le (d := d) (n := r) (F := S.D) hd hr S.q
    (S.bd) S.C S.a S.rho S.eta (T := max 1 (S.scale r)) (le_max_left _ _)).1
  have hB := ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (d := d) (n := r) (F := S.D) hd
    (S.targets) S.M S.R S.q S.aD S.bD S.c0 S.C S.a S.rho S.eta S.ell
    S.scale hell (fun t ht => by
      have h := (Finset.mem_filter.mp ht).2
      grind)
  have hP := (finePairAliasGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (S.ad) (S.bd) S.ell S.N (lt_of_lt_of_le zero_lt_one hell) hellN S.M S.q S.C S.a S.rho S.eta).1
  have hF := (fineFieldGeometryEnvelope_integrable_and_le (d := d) (n := r) (by omega)
    (S.ad) (S.bd) S.ell S.N (lt_of_lt_of_le zero_lt_one hell) S.M S.q S.C S.a S.rho S.eta).1
  have hi (i : Fin 4) : Integrable (fun U => S.components U i)
      (fullSpatialPatchDesign d r) := by
    fin_cases i
    · exact hA
    · exact integrable_gate (S.M < r) hB
    · exact integrable_gate (S.M < r) hP
    · exact hF
  unfold higherEnvelope
  refine ⟨(integrable_finsetSum _ (fun i _ => hi i)).const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]

end NearlyMinimax
