module

public import NearlyMinimax.OrdinaryFineAliasAggregation

@[expose] public section

/-! Deterministic response-summed square envelopes for ordinary fine aliases.
They depend only on actual geometric matrix kernels and fixed scalar data,
never on the density/regression/window/coefficient nuisance values. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def ordinaryFineAliasAmplitudeFactor (n M R q : ℕ) (ad bd c0 C a rho eta : ℝ) : ℝ :=
  ((1+bd)^n * (1+uniformOrdinaryDensityActivityBase ad bd c0)^R *
    Real.exp ((M : ℝ)*shrunkDensityExponent ad bd M)) *
      (ordinaryAliasResponseConstant q C a rho * (n : ℝ)^2 * eta^2)

section
variable {d n F : ℕ} (I : Finset ℕ) (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ)
    (U : DesignSample d n)

def ordinaryFineAliasGeometryKernel (r : ℕ) (L T : ℝ)
    (U : DesignSample d n) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      (spatialSubsetConfiguration S U))

/-- The actual universal envelope on the full Q^n spatial domain. -/
def ordinaryFineAliasResponseSquareEnvelope (r R q : ℕ)
    (ad bd c0 C a rho eta L T : ℝ) (U : DesignSample d n) : ℝ :=
  (3 : ℝ)^n * (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2 *
    (ordinaryFineAliasGeometryKernel (F := F) r L T U)^2

/-- Sum the actual geometric bands before squaring. This is the genuine
triangle/Cauchy envelope for the sum of fine signed-row actions. -/
def ordinaryFineAliasFamilyResponseSquareEnvelope : ℝ :=
  (3 : ℝ)^n *
    (∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U)^2

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg :
    0 ≤ ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope
  positivity

end

variable {d n F M R : ℕ}

theorem ordinaryFineAliasGeometryKernel_measurable (r : ℕ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T) := by
  exact Finset.measurable_sum _ (fun S _ => Finset.measurable_sum _
    (fun gamma _ => Finset.measurable_sum _ (fun beta _ =>
      ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
        (spatialSubsetConfiguration_measurable S))))

theorem ordinaryFineAliasKernel_energy (hd : 5 ≤ d) {r : ℕ} (hr : 2 ≤ r)
    {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) (c : ℝ) :
    Integrable (fun U => (c * ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T U)^2)
        (fullSpatialPatchDesign d n) ∧
      (∫ U, (c * ordinaryFineAliasGeometryKernel (F := F) r L T U)^2 ∂fullSpatialPatchDesign d n) ≤
        c^2 * ((n.choose r : ℝ)^2 * 2^(d*(n-r)) * ((r : ℝ)^2 * 2^d * cardinalBandSquareBudget d r L)) := by
  simp [mul_pow, integral_const_mul]
  obtain ⟨hi, hb⟩ := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n) hd hr hL (hL.trans hLT) hLT
  exact ⟨hi.const_mul _, mul_le_mul_of_nonneg_left hb (sq_nonneg _)⟩

/-- Actual pointwise square domination for the entire fine family,
separately uniform over each response's nuisance tuple. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_dominates
    {I : Finset ℕ} (ad bd c0 L : ℝ) (T : ℕ → ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hI : ∀ r ∈ I, 1 ≤ r ∧ r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) {C a V eta rho : ℝ} (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    {U : DesignSample d n} (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (TernaryVector n) → Fin n → ℝ)
    (c : (TernaryVector n) → HighFrameVector d F)
    (hpD : ∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : TernaryVector n,
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M q C a V eta U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  let H := ∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hb (y : TernaryVector n) :
      |ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y| ≤ H := by
    apply (Finset.abs_sum_le_sum_abs _ I).trans
    exact Finset.sum_le_sum (fun r hr =>
      ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L (T r)
        haD hshrink htau (hI r hr).1 (hI r hr).2 q hn hC ha heta hrho hetarho hU (hpD y) (hg y) (hw y) (hc y) hp y)
  have hsq (y : TernaryVector n) :
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y^2 ≤ H^2 := by
    simpa using (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans (hb y))).mpr (hb y)
  have hs := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hsq y)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, ordinaryFineAliasFamilyResponseSquareEnvelope, H] using hs

/-- True integrability and geometric scale for the response-summed family
envelope itself; independent of every nuisance field and chart inverse. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le
    (hd : 5 ≤ d) {I : Finset ℕ} (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) {T : ℕ → ℝ}
    (hLT : ∀ r ∈ I, N*Real.exp (-c0*D) ≤ T r) (q : ℕ) :
    let expScale := Real.exp (-c0*D)
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta (N*expScale) T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*expScale) T U ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  intro expScale
  let f := fun r (U : DesignSample d n) =>
    ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r (N*expScale) (T r) U
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase
    positivity
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hell (hell.trans (hLT r hr))).const_mul _
  have hk (r) (hr : r ∈ I) := ordinaryFineAliasKernel_energy (F := F) (n := n)
    hd (hI r hr).1 hell (hLT r hr) (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := (hk r hr).1
  have hb (r) (hr : r ∈ I) : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤ B :=
    (hk r hr).2.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0 hDK hN hell hH q)
  have hs := finite_sum_square_integrable _ I f hm hi
  have hcard : I.card^2 ≤ ((R+1 : ℕ) : ℝ)^2 := by
    have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr (by grind)
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm hi hb).trans
    (mul_le_mul_of_nonneg_right hcard hB)
  refine ⟨hs.const_mul ((3 : ℝ)^n), ?_⟩
  rw [show (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*expScale) T U ∂fullSpatialPatchDesign d n) =
      (3 : ℝ)^n * (∫ U, (∑ r ∈ I, f r U)^2 ∂fullSpatialPatchDesign d n) by
    rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    ring)

end NearlyMinimax
