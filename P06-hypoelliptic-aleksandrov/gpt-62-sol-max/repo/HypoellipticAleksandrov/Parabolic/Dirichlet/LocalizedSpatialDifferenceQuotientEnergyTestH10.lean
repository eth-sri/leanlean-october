module

public import Mathlib.Analysis.Normed.Operator.Extend
import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientH10
public import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientPointwise
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SmoothH10DenseRange
import HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyWeakTest

/-!
# Localized spatial difference-quotient energy-test operator on `H¹₀`

This module constructs the bounded extension of the literal localized
backward energy test and proves its canonical value-space pivot.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

open HypoellipticAleksandrov.Parabolic.Dirichlet

/-- The literal smooth B core is linear before any completion argument. -/
noncomputable def energyTestSmoothCoreLinearMap
    {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ}
    (hΩ : IsOpen Ω) (η : PDE.QuantitativeSmoothCutoff inner outer K)
    (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω) :
    PDE.WeakTestFunction Ω →ₗ[ℝ] H10HilbertGraph hΩ where
  toFun φ := smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ
    (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift)
  map_add' φ ψ := by
    rw [← map_add]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    exact id (congrFun (localizedSpatialDifferenceQuotientEnergyTest_add η k h φ.toFun ψ.toFun) y)
  map_smul' c φ := by
    rw [← map_smul]
    congr 1
    apply PDE.WeakTestFunction.ext
    funext y
    simpa only [localizedSpatialDifferenceQuotientEnergyWeakTest, PDE.WeakTestFunction.smul_toFun,
      Pi.smul_def, smul_eq_mul, RingHom.id_apply] using
      congrFun (localizedSpatialDifferenceQuotientEnergyTest_smul c η k h
        (φ : PDE.Vec d → ℝ)) y

private theorem neg_backwardQuotient_eq_of_ae
    {d : ℕ} {Ω : Set (PDE.Vec d)} (hΩ : IsOpen Ω) (k : Fin d) (h : ℝ)
    {F G : PDE.ScalarLp Ω 2} {f g : PDE.Vec d → ℝ}
    (hf : ⇑F =ᵐ[PDE.volumeOn Ω] f) (hg : ⇑G =ᵐ[PDE.volumeOn Ω] g)
    (hs : Function.support g ⊆ Ω)
    (hfg : ∀ y, f y = (g (y + (-h) • PDE.basisVec k) - g y) / h) :
    F = -unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) G := by
  apply Lp.ext
  filter_upwards [hf,
    unweightedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq hΩ.measurableSet k (-h) G g hg hs,
    Lp.coeFn_neg (unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h) G)] with y hy hq hn
  rw [hy, hn, Pi.neg_apply, hq, hfg, div_neg, neg_neg]

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ) (hηΩ : tsupport η.toFun ⊆ Ω)
  (hηshift : η.ShiftMapsInto k h Ω)
include inner outer K η k h hηΩ hηshift

private theorem exists_energyTestSmoothCoreLinearMap_bound :
    ∃ C : ℝ, ∀ φ : PDE.WeakTestFunction Ω,
      ‖energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift φ‖ ≤ C *
        ‖smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ‖ := by
  have hsq : η.sq.ShiftMapsInto k h Ω := fun y hy => hηshift (sq_tsupport_subset η hy)
  let A := localizedSpatialDifferenceQuotientH10CLM hΩ η.sq k h
    ((sq_tsupport_subset η).trans hηΩ) hsq
  let Q := -unweightedSpatialDifferenceQuotientL2 hΩ.measurableSet k (-h)
  let J j := (PDE.hilbertVectorLpCoord Ω 2 j).comp (gradientCLM hΩ)
  refine exists_smoothH10Core_bound hΩ (Q.comp ((valueCLM hΩ).comp A))
    (PDE.hilbertVectorLpAssemble fun j => Q.comp ((J j).comp A)) ?_ ?_
  · intro φ
    dsimp only [ContinuousLinearMap.comp_apply, A]
    rw [localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η.sq k h φ _ hsq]
    apply neg_backwardQuotient_eq_of_ae hΩ k h
      (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift))
      (ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientWeakTest η.sq k h φ ((sq_tsupport_subset η).trans hηΩ)))
    · exact (subset_tsupport _).trans (PDE.WeakTestFunction.tsupport_subset _)
    · intro y
      change localizedSpatialDifferenceQuotientEnergyTest η k h φ y = _
      simp only [localizedSpatialDifferenceQuotientEnergyTest_apply, localizedSpatialDifferenceQuotientWeakTest_apply,
        localizedSpatialDifferenceQuotient_apply, PDE.QuantitativeSmoothCutoff.sq_toFun,
        pow_two, neg_smul, sub_eq_add_neg]
      ring
  · intro φ
    apply PDE.hilbertVectorLp_ext
    intro j
    rw [PDE.hilbertVectorLpCoord_hilbertVectorLpAssemble]
    dsimp only [ContinuousLinearMap.comp_apply, A, J]
    rw [localizedSpatialDifferenceQuotientH10CLM_apply_smooth hΩ η.sq k h φ _ hsq]
    have coord (ψ : PDE.WeakTestFunction Ω) :=
      (PDE.coeFn_hilbertVectorLpCoord Ω 2 j (gradientCLM hΩ
        (smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ ψ))).trans
      (ae_gradientCoordCLM_smoothCompactlySupportedH1HilbertGraph hΩ ψ j)
    refine neg_backwardQuotient_eq_of_ae hΩ k h (coord _) (coord _) ?_ ?_
    · exact (subset_tsupport _).trans <| (tsupport_fderiv_apply_subset ℝ (PDE.basisVec j)).trans
        (PDE.WeakTestFunction.tsupport_subset _)
    · exact energyWeakTest_partialDeriv_eq_backwardSquare η k h φ hηΩ hηshift j

/-- The bounded H10 extension of the localized spatial energy test. -/
noncomputable def localizedSpatialDifferenceQuotientEnergyTestH10CLM :
    H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
  (energyTestSmoothCoreLinearMap hΩ η k h hηΩ hηshift).extendOfNorm
    (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)

end

section
variable {d : ℕ} {Ω inner outer : Set (PDE.Vec d)} {K : ℝ} (hΩ : IsOpen Ω)
  (η : PDE.QuantitativeSmoothCutoff inner outer K) (k : Fin d) (h : ℝ)

/-- The energy-test extension agrees with the literal bundled smooth core. -/
theorem localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth (φ : PDE.WeakTestFunction Ω)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω) :
    localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
      smoothCompactlySupportedH1HilbertGraphToH10HilbertGraph hΩ
        (localizedSpatialDifferenceQuotientEnergyWeakTest η k h φ φ.contDiff hηΩ hηshift) := by
  exact LinearMap.extendOfNorm_eq
    (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ)
    (exists_energyTestSmoothCoreLinearMap_bound hΩ η k h hηΩ hηshift) φ

/-- The energy-test value pairing is the localized quotient inner product. -/
theorem inner_value_localizedSpatialDifferenceQuotientEnergyTestH10CLM_eq (u v : H10HilbertGraph hΩ)
    (hηΩ : tsupport η.toFun ⊆ Ω)
    (hηshift : η.ShiftMapsInto k h Ω) :
    Inner.inner ℝ (valueCLM hΩ u)
      (valueCLM hΩ
        (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift v)) =
    Inner.inner ℝ
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift u))
      (valueCLM hΩ (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift v)) := by
  let V := valueCLM hΩ
  let B := V.comp (localizedSpatialDifferenceQuotientEnergyTestH10CLM hΩ η k h hηΩ hηshift)
  let A := V.comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift)
  change Inner.inner ℝ (V u) (B v) = Inner.inner ℝ (A u) (A v)
  refine (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ).induction_on₂
    (p := fun u v => Inner.inner ℝ (V u) (B v) = Inner.inner ℝ (A u) (A v))
    (isClosed_eq ((V.continuous.comp continuous_fst).inner (B.continuous.comp continuous_snd))
      ((A.continuous.comp continuous_fst).inner (A.continuous.comp continuous_snd))) ?_ u v
  intro φ ψ
  simp only [A, B, V, ContinuousLinearMap.comp_apply,
    localizedSpatialDifferenceQuotientEnergyTestH10CLM_apply_smooth]
  change _ = Inner.inner ℝ
    (((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ))
    (((valueCLM hΩ).comp (localizedSpatialDifferenceQuotientH10CLM hΩ η k h hηΩ hηshift))
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ ψ))
  rw [valueCLM_comp_localizedSpatialDifferenceQuotientH10CLM]
  have hval (χ : PDE.WeakTestFunction Ω) := ae_valueCLM_smoothCompactlySupportedH1HilbertGraph hΩ χ
  have hquot (χ : PDE.WeakTestFunction Ω) := localizedSpatialDifferenceQuotientL2_apply_ae_of_ae_eq
    hΩ.measurableSet η k h _ χ (hval χ) hηshift
  calc
    _ = ∫ y in Ω, φ y * localizedSpatialDifferenceQuotientEnergyTest η k h ψ y :=
      (Analysis.integral_mul_eq_inner_L2 (hval φ).symm
        (hval (localizedSpatialDifferenceQuotientEnergyWeakTest η k h ψ ψ.contDiff hηΩ hηshift)).symm).symm
    _ = ∫ y in Ω, localizedSpatialDifferenceQuotient η k h φ y *
        localizedSpatialDifferenceQuotient η k h ψ y :=
      setIntegral_mul_localizedSpatialDifferenceQuotientEnergyTest_eq
        η k h φ ψ φ.contDiff.continuous ψ.contDiff.continuous hηΩ hηshift
    _ = _ := Analysis.integral_mul_eq_inner_L2 (hquot φ).symm (hquot ψ).symm

end


end HypoellipticAleksandrov.Parabolic.Dirichlet
