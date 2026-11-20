module

public import NearlyMinimax.TernarySquareSum

public import NearlyMinimax.OrdinaryFineAliasAggregation
public import NearlyMinimax.FinePairSpatialEnergy

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

def ordinaryFineAliasGeometryKernel {d n F : ℕ} (r : ℕ) (L T : ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    spatialMatrixL1 (globalCardinalBandMatrix (D := F) (spatialInterpolationLambda d) L T
      (spatialSubsetConfiguration S U))

/-- Sum the actual geometric bands before squaring. This is the genuine
triangle/Cauchy envelope for the sum of fine signed-row actions. -/
def ordinaryFineAliasFamilyResponseSquareEnvelope {d n F : ℕ} (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ)
    (U : Fin n → Covariate d) : ℝ :=
  (3 : ℝ)^n *
    (∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r L (T r) U)^2

section
variable {d n F : ℕ}

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_nonneg (I : Finset ℕ)
    (M R q : ℕ) (ad bd c0 C a rho eta L : ℝ) (T : ℕ → ℝ) (U : Fin n → Covariate d) :
    0 ≤ ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  unfold ordinaryFineAliasFamilyResponseSquareEnvelope
  positivity

theorem ordinaryFineAliasGeometryKernel_measurable (r : ℕ) {L T : ℝ}
    (hL : 1 ≤ L) (hT : 1 ≤ T) :
    Measurable (ordinaryFineAliasGeometryKernel (d := d) (n := n) (F := F) r L T) := by
  exact Finset.measurable_sum _ (fun S _ => Finset.measurable_sum _
      (fun gamma _ => Finset.measurable_sum _ (fun beta _ =>
        ((integrated_cardinal_band_continuous (spatialInterpolationLambda d) hL hT gamma beta).measurable.abs).comp
          (spatialSubsetConfiguration_measurable S))))

end

section
variable {d n F M R : ℕ}

/-- Actual pointwise square domination for the entire fine family,
separately uniform over each response's nuisance tuple. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_dominates
    (I : Finset ℕ) (ad bd c0 L : ℝ) (T : ℕ → ℝ) (haD : 0 < ad)
    (hshrink : ad+(M : ℝ)⁻¹ < bd-(M : ℝ)⁻¹)
    (htau : shrunkDensityExponent ad bd M ≤ c0) (hI : ∀ r ∈ I, 1 ≤ r ∧ r ≤ R)
    (q : ℕ) (hn : 1 ≤ n) (C a V eta rho : ℝ) (hC : 1 ≤ C) (ha : 0 < a)
    (heta : 0 ≤ eta) (hrho : 0 ≤ rho) (hetarho : eta ≤ rho/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (p g w : (Fin n → Fin 3) → Fin n → ℝ)
    (c : (Fin n → Fin 3) → HighFrameIndex d F → ℝ)
    (hpD : ∀ y i, p y i ∈ Icc (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹))
    (hg : ∀ y i, |g y i| ≤ rho/2) (hw : ∀ y i, |w y i| ≤ 1)
    (hc : ∀ y, ∑ gamma, |c y gamma| ≤ C⁻¹)
    (hp : ∀ f : ℝ, |f| ≤ rho → ∀ u, 0 ≤ ternaryMass a f V u) :
    (∑ y : Fin n → Fin 3,
      ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹) (spatialInterpolationLambda d)
        L T M q C a V eta U (p y) (g y) (w y) (c y) y^2) ≤
      ordinaryFineAliasFamilyResponseSquareEnvelope (F := F) I M R q ad bd c0 C a rho eta L T U := by
  let H := ∑ r ∈ I, ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hb (y : Fin n → Fin 3) :
      |ordinaryFineAliasFamilyRawAction I (ad+(M : ℝ)⁻¹) (bd-(M : ℝ)⁻¹)
        (spatialInterpolationLambda d) L T M q C a V eta U (p y) (g y) (w y) (c y) y| ≤ H := by
    apply (Finset.abs_sum_le_sum_abs _ I).trans
    exact Finset.sum_le_sum (fun r hr =>
      ordinaryFineAliasRawAction_abs_bound_of_chart ad bd c0 (spatialInterpolationLambda d) L (T r)
        haD hshrink htau (hI r hr).1 (hI r hr).2 q hn C a V eta rho hC ha heta hetarho
        U hU (p y) (g y) (w y) (hpD y) (hg y) (hw y) (c y) (hc y) hp y)
  exact ternary_sum_sq_le hb

section
variable (hd : 5 ≤ d) (I : Finset ℕ)
include hd

private theorem ordinaryFineAliasEnvelope_terms (M R q : ℕ)
    (ad bd c0 C a ρ η L : ℝ) (T : ℕ → ℝ) (hL : 1 ≤ L)
    (hI : ∀ r ∈ I, 2 ≤ r ∧ L ≤ T r) :
    let f := fun r (U : Fin n → Covariate d) =>
      ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η *
        ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
    (∀ r ∈ I, Measurable (f r)) ∧
      (∀ r ∈ I, Integrable (fun U => f r U ^ 2) (fullSpatialPatchDesign d n)) := by
  let f := fun r (U : Fin n → Covariate d) => ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η *
    ordinaryFineAliasGeometryKernel (F := F) r L (T r) U
  have hm (r) (hr : r ∈ I) : Measurable (f r) :=
    (ordinaryFineAliasGeometryKernel_measurable r hL (hL.trans (hI r hr).2)).const_mul _
  have hi (r) (hr : r ∈ I) : Integrable (fun U => f r U^2) (fullSpatialPatchDesign d n) := by
    have h := (ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
      hd (hI r hr).1 hL (hL.trans (hI r hr).2) (hI r hr).2).1.const_mul
        ((ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a ρ η)^2)
    convert h using 1
    funext U
    dsimp [f, ordinaryFineAliasGeometryKernel]
    ring
  exact ⟨hm, hi⟩

theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable (M R q : ℕ) (ad bd c0 C a ρ η L : ℝ)
    (T : ℕ → ℝ) (hL : 1 ≤ L) (hI : ∀ r ∈ I, 2 ≤ r ∧ L ≤ T r) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a ρ η L T) (fullSpatialPatchDesign d n) := by
  obtain ⟨hm, hi⟩ := ordinaryFineAliasEnvelope_terms (n := n) (F := F) hd I M R q ad bd c0 C a ρ η L T hL hI
  exact (finite_sum_square_integrable _ I _ hm hi).const_mul _

/-- True integrability and geometric scale for the response-summed family
envelope itself; independent of every nuisance field and chart inverse. -/
theorem ordinaryFineAliasFamilyResponseSquareEnvelope_integrable_and_scale_le (hI : ∀ r ∈ I, 2 ≤ r ∧ r ≤ R)
    (ad bd c0 C a rho eta D K N : ℝ) (hbd : 0 ≤ bd)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hc0 : 0 ≤ c0) (hDK : D ≤ K*M)
    (hN : 0 < N) (hell : 1 ≤ N*Real.exp (-c0*D))
    (hH : Real.log (1+Real.log N) ≤ M) (T : ℕ → ℝ)
    (hLT : ∀ r ∈ I, N*Real.exp (-c0*D) ≤ T r) (q : ℕ) :
    Integrable (ordinaryFineAliasFamilyResponseSquareEnvelope (d := d) (n := n) (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T) (fullSpatialPatchDesign d n) ∧
    (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) ≤
      ordinaryAliasFamilySpatialPrefactor d q R ad bd c0 C a rho *
        eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
          Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialResponseBase d bd)^n := by
  let f := fun r (U : Fin n → Covariate d) =>
    ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta *
      ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U
  let B := ordinaryAliasSpatialPrefactor d q R ad bd c0 C a rho *
    eta^4 * Real.exp (2*shrunkDensityExponent ad bd M*M) * N^(4-(d : ℝ)) *
      Real.exp (lowerAliasSpatialL d R c0 K*M) * (ordinaryAliasSpatialCountBase d bd)^n
  have hB : 0 ≤ B := by
    dsimp [B]
    have := ordinaryAliasSpatialPrefactor_nonneg d q R ad bd c0 C a rho
    unfold ordinaryAliasSpatialCountBase
    positivity
  obtain ⟨hm, hi⟩ := ordinaryFineAliasEnvelope_terms (n := n) (F := F) hd I M R q ad bd c0 C a rho eta
    (N * Real.exp (-c0 * D)) T hell (fun r hr => ⟨(hI r hr).1, hLT r hr⟩)
  have hk (r) (hr : r ∈ I) := ordinaryFineAliasKernel_sum_square_integrable_and_le (F := F) (n := n)
    hd (hI r hr).1 hell (hell.trans (hLT r hr)) (hLT r hr)
  have hb (r) (hr : r ∈ I) : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤ B := by
    have h : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) ≤
        ordinaryFineAliasSpatialBudget d n M r R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) := by
      have hid : (∫ U, f r U^2 ∂fullSpatialPatchDesign d n) =
          (ordinaryFineAliasAmplitudeFactor n M R q ad bd c0 C a rho eta)^2 *
            (∫ U, (ordinaryFineAliasGeometryKernel (F := F) r (N*Real.exp (-c0*D)) (T r) U)^2
              ∂fullSpatialPatchDesign d n) := by
        rw [← integral_const_mul]
        congr 1
        funext U
        ring
      rw [hid]
      exact (mul_le_mul_of_nonneg_left (hk r hr).2 (sq_nonneg _)).trans_eq (by
        rfl)
    exact h.trans (ordinaryFineAliasSpatialBudget_source_scale_le hd (hI r hr).2 hbd hD hK hc0
      hDK hN hell hH q)
  have hs := finite_sum_square_integrable (fullSpatialPatchDesign d n) I f hm hi
  have hcard : (I.card : ℝ)^2 ≤ ((R+1 : ℕ) : ℝ)^2 := by
    have hsub : I ⊆ Finset.range (R+1) := fun r hr => Finset.mem_range.mpr (by have := (hI r hr).2; omega)
    have h := Finset.card_le_card hsub
    rw [Finset.card_range] at h
    exact_mod_cast Nat.pow_le_pow_left h 2
  have hsum := (finite_sum_square_integral_le (fullSpatialPatchDesign d n) I f B hm hi hb).trans
    (mul_le_mul_of_nonneg_right hcard hB)
  refine ⟨hs.const_mul ((3 : ℝ)^n), ?_⟩
  rw [show (∫ U, ordinaryFineAliasFamilyResponseSquareEnvelope (F := F)
      I M R q ad bd c0 C a rho eta (N*Real.exp (-c0*D)) T U ∂fullSpatialPatchDesign d n) =
      (3 : ℝ)^n * (∫ U, (∑ r ∈ I, f r U)^2 ∂fullSpatialPatchDesign d n) by
    rw [← integral_const_mul]; rfl]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (3 : ℝ)^n)).trans_eq (by
    unfold B ordinaryAliasFamilySpatialPrefactor ordinaryAliasSpatialResponseBase
    ring)

end

end

end NearlyMinimax
