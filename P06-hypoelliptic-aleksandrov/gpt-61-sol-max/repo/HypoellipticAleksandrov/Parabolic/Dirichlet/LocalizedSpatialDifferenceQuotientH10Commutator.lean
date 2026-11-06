module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.H10CommutatorSmoothCore
public import
  HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedReverseTimeSourceSpatialDifferenceQuotient
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialCoefficientCutoffFields
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSmoothness
public import HypoellipticAleksandrov.Parabolic.Dirichlet.SpatialCoordinateShiftCarrier
public import HypoellipticAleksandrov.Parabolic.Dirichlet.CompactlySupportedSpatialL2
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialFormOperatorBase
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSourceBochner
public import HypoellipticAleksandrov.Parabolic.Dirichlet.ReverseTimeSpatialRawAmplitudeMajorant
public import HypoellipticAleksandrov.Topology.Support
import Aesop
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10

section
open private HypoellipticAleksandrov.Parabolic.Dirichlet.inner_scalarLp_eq_integral_mul_of_ae_eq from HypoellipticAleksandrov.Parabolic.Dirichlet.LocalizedSpatialDifferenceQuotientEnergyTestH10
private alias _sharedProof_88_0 := HypoellipticAleksandrov.Parabolic.Dirichlet.inner_scalarLp_eq_integral_mul_of_ae_eq
end


/-!
# Arbitrary-`H¹₀` fixed-time localized commutators

This module lifts the smooth fixed-time localized commutator identity to the
zero-boundary Sobolev graph by quotient-safe spatial `L²` representatives and
the dense smooth core.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Matrix.Norms.Elementwise

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ}

variable (q : HypoellipticAleksandrov.Parabolic.ScalarField d)

private theorem continuous_timeVelocity_slice
      (hq : Continuous q) (τ : ℝ) :
    Continuous (fun y  => q (τ, y)) := hq.comp (continuous_const.prodMk continuous_id)

private theorem hasCompactSupport_timeVelocity_slice
      (hqcompact : HasCompactSupport q) (τ : ℝ) :
    HasCompactSupport (fun y  => q (τ, y)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hqcompact.image continuous_snd)
  intro y hy
  exact ⟨(τ, y), subset_tsupport q hy, rfl⟩

private theorem norm_timeVelocity_slice_le   (C : ℝ)
    (hqBound : ∀ z, ‖q z‖ ≤ C) (τ : ℝ) : ∀ y : PDE.Vec d, ‖q (τ, y)‖ ≤ C :=
  fun y => hqBound (τ, y)

variable {Ω : PDE.VelocityRegion d}

private theorem inner_scalarLp_eq_setIntegral_of_ae_eq
    (f g : PDE.ScalarLp Ω (2 )) (p q : PDE.ScalarField d)
    (hf : ⇑f =ᵐ[PDE.volumeOn Ω] p) (hg : ⇑g =ᵐ[PDE.volumeOn Ω] q) :
    inner ℝ f g = ∫ y in Ω, p y * q y := (_sharedProof_88_0 f g p q hf hg)


private theorem inner_add_scalarL2Multiplier_eq_setIntegral
    (p q : PDE.ScalarField d)
    (hp : AEStronglyMeasurable p (PDE.volumeOn Ω))
    (hq : AEStronglyMeasurable q (PDE.volumeOn Ω)) (Cp Cq : ℝ) (hCp : 0 ≤ Cp) (hCq : 0 ≤ Cq)
    (hpBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖p y‖ ≤ Cp) (hqBound : ∀ᵐ y ∂PDE.volumeOn Ω, ‖q y‖ ≤ Cq)
    (f g r : PDE.ScalarLp Ω (2 )) : inner ℝ
        (scalarL2Multiplier p hp Cp hCp hpBound f +
          scalarL2Multiplier q hq Cq hCq hqBound g) r =
      ∫ y in Ω, (p y * f y + q y * g y) * r y := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hadd := MeasureTheory.Lp.coeFn_add
    (scalarL2Multiplier p hp Cp hCp hpBound f)
    (scalarL2Multiplier q hq Cq hCq hqBound g)
  filter_upwards [hadd, scalarL2Multiplier_apply_ae p hp Cp hCp hpBound f,
    scalarL2Multiplier_apply_ae q hq Cq hCq hqBound g] with y hadd hpq hqq
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hpq, hqq]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

private theorem continuous_reverseTimeSpatialForm_apply_energyTest
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω)) (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ) :
    Continuous (fun u => reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) := by
  let O := reverseTimeSpatialFormOperator
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc ⟨τ, hτ⟩

  convert (O.continuous.clm_apply B.continuous) using 1
  funext u
  exact (reverseTimeSpatialFormOperator_apply
    r₀ r₁ h₀₁ hΩ hΩbounded a b c ha hb hc ⟨τ, hτ⟩ u (B u)).symm

private abbrev continuousCompactBoundedField {d : ℕ} (C : ℝ) (q : HypoellipticAleksandrov.Parabolic.ScalarField d) : Prop :=
  Continuous q ∧ HasCompactSupport q ∧ ∀ z, ‖q z‖ ≤ C

private theorem continuousCompactBoundedField_reverseTimeSource_of_fixedStepRawAmplitude
    {d : ℕ} {Ω inner : PDE.VelocityRegion d} {Kη : ℝ} (r₀ r₁ : ℝ)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1) (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (k : Fin d) (h : ℝ)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k)
      (tsupport η.toFun) Ω)
    (M : ℝ) (hM : 0 ≤ M)
    (hsourceDQ : ∀ (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport η.toFun →
      |spatialDifferenceQuotient k h
        (fun w  => F (r₁ - w.1) w.2) (τ, y)| ≤ M) :
    continuousCompactBoundedField M (fun z  =>
      ζ z.1 * η z.2 * spatialDifferenceQuotient k h
        (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z) := by
  let sharedTerm_805dd799fc := ((fun z : TimeVelocity d => F (r₁ - z.1) z.2))
  let S : HypoellipticAleksandrov.Parabolic.Region d := tsupport (ζ : ℝ → ℝ) ×ˢ tsupport η.toFun
  let β : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * η z.2
  have hS : IsCompact S :=
    ζ.hasCompactSupport.prod η.hasCompactSupport

  have hβS : tsupport β ⊆ S := by
    apply closure_minimal
    · intro z hz
      have hmul : ζ z.1 * η z.2 ≠ 0 := hz
      refine ⟨?_, ?_⟩
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
    · exact hS.isClosed
  have hβcompact : HasCompactSupport β :=
    hS.of_isClosed_subset (isClosed_tsupport _) hβS

  rcases hFSmooth with ⟨V, hVopen, hCV, hV⟩
  let U  := reverseTimeMap r₁ ⁻¹' V
  let W  := U ∩ (spatialShift k h) ⁻¹' U
  have hU : IsOpen U :=
    (contDiff_reverseTimeMap r₁).continuous.isOpen_preimage V hVopen
  have hshiftcont : Continuous (spatialShift k h) := by
    simpa only [spatialShift] using!
      (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous
  have hW : IsOpen W := hU.inter (hshiftcont.isOpen_preimage U hU)


  have hqU : ContinuousOn sharedTerm_805dd799fc U :=
    (show ContDiffOn ℝ 1
      sharedTerm_805dd799fc U by


        simpa only [Function.comp_def, reverseTimeMap_apply] using
          (show ContDiffOn ℝ 1 (fun z : TimeVelocity d => F z.1 z.2) V from hV.of_le (by simp)).comp (show ContDiffOn ℝ 1 (reverseTimeMap r₁ : TimeVelocity d → TimeVelocity d) U from (contDiff_reverseTimeMap r₁).of_le (by simp) |>.contDiffOn) (fun z hz => hz)).continuousOn
  have htranslateW : ContinuousOn
      (spatialTranslate k h sharedTerm_805dd799fc) W := by
    change ContinuousOn (fun z => F (r₁ - (spatialShift k h z).1) (spatialShift k h z).2) W
    exact hqU.comp' hshiftcont.continuousOn fun z hz => hz.2

  have hdqW : ContinuousOn
      (spatialDifferenceQuotient k h sharedTerm_805dd799fc) W := by
    rw [show spatialDifferenceQuotient k h sharedTerm_805dd799fc =
      fun z => (spatialTranslate k h sharedTerm_805dd799fc z -
        F (r₁ - z.1) z.2) / h from rfl]
    exact (htranslateW.sub (hqU.mono fun z hz => hz.1)).div_const h

  simpa only [max_eq_left hM] using
    (HypoellipticAleksandrov.continuous_hasCompactSupport_norm_le_cutoff_mul hW
      (show Continuous β by
          exact (ζ.contDiff.continuous.comp continuous_fst).mul
            (η.smooth.continuous.comp continuous_snd)).continuousOn hβcompact (show tsupport β ⊆ W by
                intro z hz
                have hzS : z ∈ S := hβS hz
                have hztime : z.1 ∈ Set.Ioo 0 (r₁ - r₀) := ζ.tsupport_subset hzS.1
                have hzΩ  := η.tsupport_subset hzS.2
                refine ⟨?_, ?_⟩
                · change reverseTimeMap r₁ z ∈ V
                  apply hCV
                  exact (mem_scalarParabolicClosedCylinder_iff).2
                    ⟨by simpa only using (show r₀ ≤ r₁ - z.1 from by linarith [hztime.2]),
                      by simpa only using (show r₁ - z.1 ≤ r₁ from by linarith [hztime.1]),
                      subset_closure hzΩ⟩
                · change reverseTimeMap r₁ (spatialShift k h z) ∈ V
                  apply hCV
                  exact (mem_scalarParabolicClosedCylinder_iff).2
                    ⟨by
                        have hshift_time : (spatialShift k h z).1 = z.1 := by
                          rcases z with ⟨τ, y⟩
                          simp
                        rw [hshift_time]
                        linarith [hztime.2],
                      by
                        have hshift_time : (spatialShift k h z).1 = z.1 := by
                          rcases z with ⟨τ, y⟩
                          simp
                        rw [hshift_time]
                        linarith [hztime.1],
                      (id (subset_closure (hηshift hzS.right)))⟩) (show ∀ z, ‖β z‖ ≤ 1 by
                intro z
                rw [show β z = ζ z.1 * η z.2 from rfl, norm_mul]

                calc
                  ‖ζ z.1‖ * ‖η z.2‖ ≤ 1 * 1 :=
                    mul_le_mul (hζunit z.1) (by
                        rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg _)]
                        exact η.le_one _) (norm_nonneg _) (by norm_num)
                  _ = 1 := one_mul 1) hdqW (show ∀ z ∈ tsupport β,
      ‖spatialDifferenceQuotient k h
        sharedTerm_805dd799fc z‖ ≤ M by
          rintro ⟨τ, y⟩ hz
          rw [Real.norm_eq_abs]
          apply hsourceDQ τ y
          · exact ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
              le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
          · exact (hβS hz).2))

private abbrev twoSpatialFields
    {d : ℕ} (C : ℝ) (β q : HypoellipticAleksandrov.Parabolic.ScalarField d) (k : Fin d) (h : ℝ) : Prop :=
  continuousCompactBoundedField C (fun z => β z * spatialTranslate k h q z) ∧
    continuousCompactBoundedField C (fun z =>
      β z * spatialDifferenceQuotient k h q z)

private theorem exists_common_norm_bound_of_finite_continuousOn
    {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {S : Set X} (hS : IsCompact S) (q : ι → X → ℝ)
    (hq : ∀ i, ContinuousOn (q i) S) :
    ∃ C : ℝ, ∀ (i : ι) (z : X), z ∈ S → ‖q i z‖ ≤ C := by
  classical
  have hfold : ∀ t : Finset ι, ∃ C : ℝ,
      ∀ (i : ι), i ∈ t → ∀ (z : X), z ∈ S → ‖q i z‖ ≤ C := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        aesop
    | insert i t hit ih =>
        obtain ⟨Ci, hCi⟩ := hS.exists_bound_of_continuousOn (hq i)
        obtain ⟨Ct, hCt⟩ := ih
        refine ⟨max Ci Ct, ?_⟩
        intro j hj z hz
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact (hCi z hz).trans (le_max_left _ _)
        · exact (hCt j hj z hz).trans (le_max_right _ _)
  obtain ⟨C, hC⟩ := hfold Finset.univ
  exact ⟨C, fun i z hz => hC i (Finset.mem_univ _) z hz⟩

variable {d : ℕ}

private theorem twoSpatialFields_of_smoothOnNeighborhood_of_fixedStep_bounds
     {S : HypoellipticAleksandrov.Parabolic.Region d}
    (C : ℝ) (β q : HypoellipticAleksandrov.Parabolic.ScalarField d) (k : Fin d) (h : ℝ)
    (hC : 0 ≤ C)
    (hβcont : Continuous β) (hβcompact : HasCompactSupport β)
    (hβunit : ∀ z, ‖β z‖ ≤ 1)
    (hqsmooth : IsSmoothOnNeighborhood q S)
    (hβS : tsupport β ⊆ S)
    (hβshiftS : ∀ z ∈ tsupport β, spatialShift k h z ∈ S)
    (htranslate : ∀ z ∈ tsupport β, ‖spatialTranslate k h q z‖ ≤ C)
    (hdq : ∀ z ∈ tsupport β, ‖spatialDifferenceQuotient k h q z‖ ≤ C) :
    twoSpatialFields C β q k h := by
  rcases hqsmooth with ⟨V, hVopen, hSV, hV⟩
  let W  := V ∩ (spatialShift k h) ⁻¹' V
  have hshiftcont : Continuous (spatialShift k h) := by
    simpa only [spatialShift] using!
      (Homeomorph.addRight ((0, h • PDE.basisVec k) : TimeVelocity d)).continuous
  have hW : IsOpen W := hVopen.inter (hshiftcont.isOpen_preimage V hVopen)
  have hβW : tsupport β ⊆ W := by
    intro z hz
    exact ⟨hSV (hβS hz), hSV (hβshiftS z hz)⟩

  have htranslateW : ContinuousOn (spatialTranslate k h q) W := by
    change ContinuousOn (fun z => q (spatialShift k h z)) W
    exact hV.continuousOn.comp' hshiftcont.continuousOn fun z hz => hz.2

  constructor
  · simpa only [max_eq_left hC] using
      (HypoellipticAleksandrov.continuous_hasCompactSupport_norm_le_cutoff_mul hW
        hβcont.continuousOn hβcompact hβW hβunit htranslateW htranslate)
  · simpa only [max_eq_left hC] using
      (HypoellipticAleksandrov.continuous_hasCompactSupport_norm_le_cutoff_mul hW
        hβcont.continuousOn hβcompact hβW hβunit (by
            rw [show spatialDifferenceQuotient k h q =
              fun z => (spatialTranslate k h q z - q z) / h from rfl]
            exact (htranslateW.sub (hV.continuousOn.mono fun z hz => hz.1)).div_const h) hdq)

variable {Ω inner : PDE.VelocityRegion d}

private theorem exists_fixedStep_reverseTimeCoefficientFields_of_majorants
      {Kχ : ℝ}
    (r₀ r₁ : ℝ)
    (χ : PDE.QuantitativeSmoothCutoff inner Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ M : ℝ) (hM : 0 ≤ M)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (ha : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hb : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hc : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (k : Fin d) (h : ℝ) (hh : |h| ≤ δ)
    (hADQ : ∀ (i j : Fin d) (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) (τ, y)| ≤ M)
    (hBT : ∀ (j : Fin d) (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ M)
    (hBDQ : ∀ (j : Fin d) (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) (τ, y)| ≤ M)
    (hcT : ∀ (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialTranslate k h
        (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ M)
    (hcDQ : ∀ (τ : ℝ) (y : PDE.Vec d),
      τ ∈ Set.Icc 0 (r₁ - r₀) → y ∈ tsupport χ.toFun →
      |spatialDifferenceQuotient k h
        (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) (τ, y)| ≤ M) :
    ∃ CA : ℝ, 0 ≤ CA ∧
      (∀ i j, twoSpatialFields CA
        (fun z => ζ z.1 * χ z.2)
        (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) k h) ∧
      (∀ j, twoSpatialFields CA
        (fun z => ζ z.1 * χ z.2)
        (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) k h) ∧
      twoSpatialFields CA
        (fun z => ζ z.1 * χ z.2)
        (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) k h := by
  let sharedTerm_4b50c150d7 := ((fun z : TimeVelocity d => ζ z.1))
  let sharedTerm_bac6b91142 := ((fun z : TimeVelocity d => χ z.2))
  let Kδ  := spatialCoordinateShiftCarrier (tsupport χ.toFun) δ
  let Sstar : HypoellipticAleksandrov.Parabolic.Region d :=
    tsupport (ζ : ℝ → ℝ) ×ˢ (tsupport χ.toFun ∪ Kδ)
  let β : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => ζ z.1 * χ z.2

  have hSstar : IsCompact Sstar :=
    ζ.hasCompactSupport.prod (χ.hasCompactSupport.isCompact.union (IsCompact.spatialCoordinateShiftCarrier χ.hasCompactSupport.isCompact δ))
  have hβcont : Continuous β := by
    exact (ζ.contDiff.continuous.comp continuous_fst).mul
      (χ.smooth.continuous.comp continuous_snd)
  have hβS : tsupport β ⊆ Sstar := by
    apply closure_minimal
    · intro z hz
      have hmul : ζ z.1 * χ z.2 ≠ 0 := hz
      refine ⟨?_, Or.inl ?_⟩
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
      · apply subset_tsupport
        intro hzero
        exact hmul (by simp [hzero])
    · exact hSstar.isClosed

  have hβχ : ∀ z ∈ tsupport β, z.2 ∈ tsupport χ.toFun := by


    exact fun z hz => (show tsupport sharedTerm_bac6b91142 ⊆
        (fun z  => z.2) ⁻¹' tsupport χ.toFun by
        apply closure_minimal
        · intro z hz
          exact subset_tsupport _ hz
        · exact (isClosed_tsupport _).preimage continuous_snd) ((show tsupport β ⊆ tsupport sharedTerm_bac6b91142 by
        simpa only [β] using
          (tsupport_mul_subset_right (f := sharedTerm_4b50c150d7)
            (g := sharedTerm_bac6b91142))) hz)
  have hβcompact : HasCompactSupport β :=
    hSstar.of_isClosed_subset (isClosed_tsupport _) hβS
  have hβunit : ∀ z, ‖β z‖ ≤ 1 := by
    intro z
    rw [show β z = ζ z.1 * χ z.2 from rfl, norm_mul]

    calc
      ‖ζ z.1‖ * ‖χ z.2‖ ≤ 1 * 1 :=
        mul_le_mul (hζunit z.1) (by
            rw [Real.norm_eq_abs, abs_of_nonneg (χ.nonneg _)]
            exact χ.le_one _) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hβshiftS : ∀ z ∈ tsupport β, spatialShift k h z ∈ Sstar := by
    intro z hz
    refine ⟨?_, Or.inr ?_⟩
    · have htime : (spatialShift k h z).1 = z.1 := by
        rcases z with ⟨τ, y⟩
        simp
      rw [htime]
      exact (show ∀ z ∈ tsupport β, z.1 ∈ tsupport (ζ : ℝ → ℝ) by


          exact fun z hz => (show tsupport sharedTerm_4b50c150d7 ⊆
              (fun z  => z.1) ⁻¹' tsupport (ζ : ℝ → ℝ) by
              apply closure_minimal
              · intro z hz
                exact subset_tsupport _ hz
              · exact (isClosed_tsupport _).preimage continuous_fst) ((show tsupport β ⊆ tsupport sharedTerm_4b50c150d7 by
              simpa only [β] using
                (tsupport_mul_subset_left (f := sharedTerm_4b50c150d7)
                  (g := sharedTerm_bac6b91142))) hz)) z hz
    · change z.2 + h • PDE.basisVec k ∈ Kδ
      exact mem_spatialCoordinateShiftCarrier_of_mem_of_abs_le (hβχ z hz) hh
  have hreverseSstar : reverseTimeMap r₁ '' Sstar ⊆
      scalarParabolicClosedCylinder r₀ r₁ Ω := by
    rintro w ⟨z, hz, rfl⟩
    rcases hz with ⟨hτ, hy⟩
    have hτinterval : z.1 ∈ Set.Ioo 0 (r₁ - r₀) := ζ.tsupport_subset hτ
    rw [mem_scalarParabolicClosedCylinder_iff]
    refine ⟨?_, ?_, subset_closure ?_⟩
    · simp only [reverseTimeMap_apply]
      linarith [hτinterval.2]
    · simp only [reverseTimeMap_apply]
      linarith [hτinterval.1]
    · rcases hy with hy | hy
      · exact χ.tsupport_subset hy
      · exact hcarrier hy
  have hmatrixsmooth (i j : Fin d) : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) Sstar := by
    change IsSmoothOnNeighborhood
      ((fun z : TimeVelocity d => a z.1 z.2 i j) ∘ reverseTimeMap r₁) Sstar
    exact IsSmoothOnNeighborhood.reverseTime r₁ hreverseSstar
      (IsSmoothOnNeighborhood.coefficientEntry a ha i j)
  have hdriftsmooth (j : Fin d) : IsSmoothOnNeighborhood
      (fun z : TimeVelocity d => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) Sstar := by
    change IsSmoothOnNeighborhood
      ((fun z  =>
        scalarSpatialCoefficientDivergence a z j - b z.1 z.2 j) ∘ reverseTimeMap r₁) Sstar
    exact IsSmoothOnNeighborhood.reverseTime r₁ hreverseSstar
      (IsSmoothOnNeighborhood.divergenceDriftEntry a b ha hb j)

  have hmatrixcont (i j : Fin d) : ContinuousOn
      (fun z : TimeVelocity d => reverseTimeCoefficient r₁ a z.1 z.2 i j) Sstar := by
    rcases hmatrixsmooth i j with ⟨V, hVopen, hSV, hV⟩
    exact hV.continuousOn.mono hSV
  obtain ⟨CA₀, hCA₀⟩ := exists_common_norm_bound_of_finite_continuousOn hSstar
    (fun ij : Fin d × Fin d => fun z =>
      reverseTimeCoefficient r₁ a z.1 z.2 ij.1 ij.2)
    (fun ij => hmatrixcont ij.1 ij.2)
  let CA : ℝ := max (max CA₀ 0) M
  have hCA : 0 ≤ CA := hM.trans (le_max_right _ _)
  refine ⟨CA, hCA, ?_, ?_, ?_⟩
  · intro i j
    apply twoSpatialFields_of_smoothOnNeighborhood_of_fixedStep_bounds CA β
      _ k h hCA hβcont hβcompact
      hβunit (hmatrixsmooth i j) hβS hβshiftS
    · intro z hz
      change ‖reverseTimeCoefficient r₁ a (spatialShift k h z).1
        (spatialShift k h z).2 i j‖ ≤ CA
      exact (hCA₀ (i, j) _ (hβshiftS z hz)).trans
        (le_trans (le_max_left _ _) (le_max_left _ _))
    · rintro ⟨τ, y⟩ hz
      rw [Real.norm_eq_abs]
      exact (hADQ i j τ y
        ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
          le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
        (hβχ (τ, y) hz)).trans (le_max_right _ _)
  · intro j
    apply twoSpatialFields_of_smoothOnNeighborhood_of_fixedStep_bounds CA β
      _ k h hCA hβcont hβcompact
      hβunit (hdriftsmooth j) hβS hβshiftS
    · rintro ⟨τ, y⟩ hz
      rw [Real.norm_eq_abs]
      exact (hBT j τ y
        ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
          le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
        (hβχ (τ, y) hz)).trans (le_max_right _ _)
    · rintro ⟨τ, y⟩ hz
      rw [Real.norm_eq_abs]
      exact (hBDQ j τ y
        ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
          le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
        (hβχ (τ, y) hz)).trans (le_max_right _ _)
  · apply twoSpatialFields_of_smoothOnNeighborhood_of_fixedStep_bounds CA β
      _ k h hCA hβcont hβcompact
      hβunit ((id (IsSmoothOnNeighborhood.reverseTime r₁ hreverseSstar hc))) hβS hβshiftS
    · rintro ⟨τ, y⟩ hz
      rw [Real.norm_eq_abs]
      exact (hcT τ y
        ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
          le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
        (hβχ (τ, y) hz)).trans (le_max_right _ _)
    · rintro ⟨τ, y⟩ hz
      rw [Real.norm_eq_abs]
      exact (hcDQ τ y
        ⟨le_of_lt (ζ.tsupport_subset (hβS hz).1).1,
          le_of_lt (ζ.tsupport_subset (hβS hz).1).2⟩
        (hβχ (τ, y) hz)).trans (le_max_right _ _)

private def h10CommutatorLhsLocal
      {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d) (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let B := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift
  ζ τ *
    (reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
      reverseTimeSpatialForm hΩ r₁ τ a b c u (B u))

private def h10CommutatorRawLeafLocal
     {Ω : PDE.VelocityRegion d}
    (sourceD V : PDE.ScalarField d)
    (aT aD : Fin d → Fin d → PDE.ScalarField d)
    (E H U : Fin d → PDE.ScalarField d)
    (driftT driftD : Fin d → PDE.ScalarField d)
    (γT γD U₀ : PDE.ScalarField d) : ℝ :=
  -(∫ y in Ω, sourceD y * V y) -
    (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
      (aT i j y * E j y + aD i j y * U j y) * H i y) -
    (∑ j : Fin d, ∫ y in Ω,
      (driftT j y * E j y + driftD j y * U j y) * V y) +
    ∫ y in Ω, (γT y * V y + γD y * U₀ y) * V y

private def h10CommutatorRawRhsLocal
     {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ}
    (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁)
    (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (F : PDE.TimeScalarField d)
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (ζ : ReverseTimeScalarTest (r₁ - r₀))
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ)
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : ℝ :=
  let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
    localizedSpatialDifferenceQuotientH10CLM hΩ η k h η.tsupport_subset hηshift
  let V : PDE.ScalarField d := fun y => valueCLM hΩ (A u) y
  let G : Fin d → PDE.ScalarField d := fun i y =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A u)) y
  let W : Fin d → PDE.ScalarField d := fun i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h (valueCLM hΩ u) y
  let E : Fin d → PDE.ScalarField d := fun i y => G i y - W i y
  let H : Fin d → PDE.ScalarField d := fun i y => G i y + W i y
  let U : Fin d → PDE.ScalarField d := fun j y => η y *
    PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ u) y
  let U₀ : PDE.ScalarField d := fun y => η y * valueCLM hΩ u y
  let source : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => F (r₁ - z.1) z.2
  let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
  let sourceD : PDE.ScalarField d := fun y => ζ τ * η y *
    spatialDifferenceQuotient k h source (τ, y)
  let aT : Fin d → Fin d → PDE.ScalarField d := fun i j y =>
    ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
  let aD : Fin d → Fin d → PDE.ScalarField d := fun i j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (α i j) (τ, y)
  let driftT : Fin d → PDE.ScalarField d := fun j y =>
    ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
  let driftD : Fin d → PDE.ScalarField d := fun j y =>
    ζ τ * χ y * spatialDifferenceQuotient k h (drift j) (τ, y)
  let γT : PDE.ScalarField d := fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
  let γD : PDE.ScalarField d := fun y =>
    ζ τ * χ y * spatialDifferenceQuotient k h γ (τ, y)
  h10CommutatorRawLeafLocal (Ω := Ω) sourceD V aT aD E H U driftT driftD γT γD U₀

variable {Ω inner : PDE.VelocityRegion d} {Kη Kχ : ℝ} (r₀ r₁ : ℝ) (h₀₁ : r₀ < r₁) (hΩ : IsOpen Ω) (hΩbounded : Bornology.IsBounded Ω)

variable (a : CoefficientField d) (b : PDE.TimeVectorField d) (c : PDE.TimeScalarField d) (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (F : PDE.TimeScalarField d) (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2) (scalarParabolicClosedCylinder r₀ r₁ Ω)) (ζ : ReverseTimeScalarTest (r₁ - r₀))

variable (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) (k : Fin d) (h τ : ℝ)

private def h10CommutatorFixedStepOutputLocal


     (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) : Prop :=
  h10CommutatorLhsLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ k h τ
      hηshift u =
    h10CommutatorRawRhsLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
      hcSmooth F hFSmooth ζ η χ k h τ hηshift u

private theorem h10CommutatorFixedStepOutputLocal_of_smoothCore



    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (φ : PDE.WeakTestFunction Ω) :
    h10CommutatorFixedStepOutputLocal

      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ η χ k h τ hτ hηshift
      (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) := by
  change h10CommutatorLhsLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ k h τ
      hηshift (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ) =
    h10CommutatorRawRhsLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
      F hFSmooth ζ η χ k h τ hηshift
        (smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ φ)
  simpa only [h10CommutatorFixedStepOutput, h10CommutatorLhsLocal,
    h10CommutatorRawRhsLocal, h10CommutatorRawLeafLocal] using
    (smoothCore_fixedStep_reverseTimeSource_sub_reverseTimeSpatialForm_eq_commutator
      r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
      ζ η χ k h τ hηshift hτ φ)

private theorem h10CommutatorFixedStepOutputLocal_of_denseSmoothCore


     (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) (rightInner : H10HilbertGraph hΩ → ℝ)
    (hleft : Continuous (h10CommutatorLhsLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth
      ζ η χ k h τ hηshift))
    (hright : Continuous rightInner)
    (hinnerRaw : ∀ v, rightInner v = h10CommutatorRawRhsLocal r₀ r₁ h₀₁ hΩ hΩbounded
      a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ η χ k h τ hηshift v) :
    h10CommutatorFixedStepOutputLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
      hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u := (id
  (Eq.trans
    (congrFun
      (DenseRange.equalizer (denseRange_smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) hleft hright
        (funext fun φ =>
          id
            (Eq.trans
              (h10CommutatorFixedStepOutputLocal_of_smoothCore r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F
                hFSmooth ζ η χ k h τ hηshift hτ φ)
              (Eq.symm (hinnerRaw ((smoothCompactlySupportedH1HilbertGraphToH10LinearMap hΩ) φ))))))
      u)
    (hinnerRaw u)))

private def h10CommutatorOutput

     (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
      ∃ hχshift : Set.MapsTo
        (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω,
      ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ),
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy
          apply subset_tsupport
          change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]
          exact one_ne_zero
        let hηshift : Set.MapsTo
            (fun y  => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω := hχshift.mono_left hηχ
        h10CommutatorFixedStepOutputLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
          hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u

private theorem h10CommutatorAtFixedStepFromFields


    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (k : Fin d) (h τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
    (hηshift : Set.MapsTo
      (fun y  => y + h • PDE.basisVec k) (tsupport η.toFun) Ω)
    (u : H10HilbertGraph hΩ) (CF CA : ℝ) (hCA : 0 ≤ CA)
    (hsourceJoint : continuousCompactBoundedField CF (fun z  =>
      ζ z.1 * η z.2 * spatialDifferenceQuotient k h
        (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z))
    (hmatrixFields : ∀ i j : Fin d,
      twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
        (fun z  => reverseTimeCoefficient r₁ a z.1 z.2 i j) k h)
    (hdriftFields : ∀ j : Fin d,
      twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
        (fun z  => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) k h)
    (hscalarFields : twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
      (fun z  => reverseTimeScalarCoefficient r₁ c z.1 z.2) k h) :
    h10CommutatorFixedStepOutputLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth
      hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u := by
  let sharedTerm_afb709f12d := (Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d)
  classical
  let X := H10HilbertGraph hΩ
  let L := PDE.ScalarLp Ω (2 )
  let A : X →L[ℝ] X := localizedSpatialDifferenceQuotientH10CLM
    hΩ η k h η.tsupport_subset hηshift
  let B : X →L[ℝ] X := localizedSpatialDifferenceQuotientEnergyTestH10CLM
    hΩ η k h η.tsupport_subset hηshift

  let sourceJoint  := fun z =>
    ζ z.1 * η z.2 * spatialDifferenceQuotient k h (fun z => F (r₁ - z.1) z.2) z



  let α : sharedTerm_afb709f12d := fun i j z =>
    reverseTimeCoefficient r₁ a z.1 z.2 i j
  let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d := fun j z =>
    reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
  let γ : HypoellipticAleksandrov.Parabolic.ScalarField d := fun z =>
    reverseTimeScalarCoefficient r₁ c z.1 z.2
  let aTJoint : sharedTerm_afb709f12d := fun i j z =>
    ζ z.1 * χ z.2 * spatialTranslate k h (α i j) z
  let aDJoint : sharedTerm_afb709f12d := fun i j z =>
    ζ z.1 * χ z.2 * spatialDifferenceQuotient k h (α i j) z
  let driftTJoint  := fun j z =>
    ζ z.1 * χ z.2 * spatialTranslate k h (drift j) z
  let driftDJoint  := fun j z =>
    ζ z.1 * χ z.2 * spatialDifferenceQuotient k h (drift j) z
  let γTJoint  := fun z =>
    ζ z.1 * χ z.2 * spatialTranslate k h γ z
  let γDJoint  := fun z =>
    ζ z.1 * χ z.2 * spatialDifferenceQuotient k h γ z
  have haFields (i j : Fin d) := hmatrixFields i j
  have haTJointCont (i j : Fin d) : Continuous (aTJoint i j) := by
    exact (haFields i j).1.1

  have haTJointBound (i j : Fin d) : ∀ z, ‖aTJoint i j z‖ ≤ CA := by
    exact (haFields i j).1.2.2
  have haDJointCont (i j : Fin d) : Continuous (aDJoint i j) := by
    exact (haFields i j).2.1

  have haDJointBound (i j : Fin d) : ∀ z, ‖aDJoint i j z‖ ≤ CA := by
    exact (haFields i j).2.2.2
  have hdriftTJointCont (j : Fin d) : Continuous (driftTJoint j) := by
    exact (hdriftFields j).1.1

  have hdriftTJointBound (j : Fin d) : ∀ z, ‖driftTJoint j z‖ ≤ CA := by
    exact (hdriftFields j).1.2.2
  have hdriftDJointCont (j : Fin d) : Continuous (driftDJoint j) := by
    exact (hdriftFields j).2.1

  have hdriftDJointBound (j : Fin d) : ∀ z, ‖driftDJoint j z‖ ≤ CA := by
    exact (hdriftFields j).2.2.2






  let sourceD  := fun y => sourceJoint (τ, y)
  let aT  := fun i j y => aTJoint i j (τ, y)
  let aD  := fun i j y => aDJoint i j (τ, y)
  let driftT  := fun j y => driftTJoint j (τ, y)
  let driftD  := fun j y => driftDJoint j (τ, y)
  let γT  := fun y => γTJoint (τ, y)
  let γD  := fun y => γDJoint (τ, y)
  have hsourceDCont : Continuous sourceD := by
    exact continuous_timeVelocity_slice sourceJoint (hsourceJoint.1) τ
  have hsourceDCompact : HasCompactSupport sourceD := by
    exact hasCompactSupport_timeVelocity_slice sourceJoint (hsourceJoint.2.1) τ

  have haTCont (i j : Fin d) : Continuous (aT i j) := by
    exact continuous_timeVelocity_slice (aTJoint i j) (haTJointCont i j) τ

  have haTBound (i j : Fin d) : ∀ y, ‖aT i j y‖ ≤ CA := by
    exact norm_timeVelocity_slice_le (aTJoint i j) CA (haTJointBound i j) τ
  have haDCont (i j : Fin d) : Continuous (aD i j) := by
    exact continuous_timeVelocity_slice (aDJoint i j) (haDJointCont i j) τ

  have haDBound (i j : Fin d) : ∀ y, ‖aD i j y‖ ≤ CA := by
    exact norm_timeVelocity_slice_le (aDJoint i j) CA (haDJointBound i j) τ
  have hdriftTCont (j : Fin d) : Continuous (driftT j) := by
    exact continuous_timeVelocity_slice (driftTJoint j) (hdriftTJointCont j) τ

  have hdriftTBound (j : Fin d) : ∀ y, ‖driftT j y‖ ≤ CA := by
    exact norm_timeVelocity_slice_le (driftTJoint j) CA (hdriftTJointBound j) τ
  have hdriftDCont (j : Fin d) : Continuous (driftD j) := by
    exact continuous_timeVelocity_slice (driftDJoint j) (hdriftDJointCont j) τ

  have hdriftDBound (j : Fin d) : ∀ y, ‖driftD j y‖ ≤ CA := by
    exact norm_timeVelocity_slice_le (driftDJoint j) CA (hdriftDJointBound j) τ






  have haTMeas (i j : Fin d) : AEStronglyMeasurable (aT i j) (PDE.volumeOn Ω) :=
    (haTCont i j).aestronglyMeasurable
  have haTBoundAE (i j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖aT i j y‖ ≤ CA :=
    Filter.Eventually.of_forall (haTBound i j)
  have haDMeas (i j : Fin d) : AEStronglyMeasurable (aD i j) (PDE.volumeOn Ω) :=
    (haDCont i j).aestronglyMeasurable
  have haDBoundAE (i j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖aD i j y‖ ≤ CA :=
    Filter.Eventually.of_forall (haDBound i j)
  have hdriftTMeas (j : Fin d) : AEStronglyMeasurable (driftT j) (PDE.volumeOn Ω) :=
    (hdriftTCont j).aestronglyMeasurable
  have hdriftTBoundAE (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖driftT j y‖ ≤ CA :=
    Filter.Eventually.of_forall (hdriftTBound j)
  have hdriftDMeas (j : Fin d) : AEStronglyMeasurable (driftD j) (PDE.volumeOn Ω) :=
    (hdriftDCont j).aestronglyMeasurable
  have hdriftDBoundAE (j : Fin d) : ∀ᵐ y ∂PDE.volumeOn Ω, ‖driftD j y‖ ≤ CA :=
    Filter.Eventually.of_forall (hdriftDBound j)
  have hγTMeas : AEStronglyMeasurable γT (PDE.volumeOn Ω) := (show Continuous γT by
      exact continuous_timeVelocity_slice γTJoint (hscalarFields.1.1) τ).aestronglyMeasurable
  have hγTBoundAE : ∀ᵐ y ∂PDE.volumeOn Ω, ‖γT y‖ ≤ CA :=
    Filter.Eventually.of_forall (by
        exact norm_timeVelocity_slice_le γTJoint CA (hscalarFields.1.2.2) τ)
  have hγDMeas : AEStronglyMeasurable γD (PDE.volumeOn Ω) := (show Continuous γD by
      exact continuous_timeVelocity_slice γDJoint (hscalarFields.2.1) τ).aestronglyMeasurable
  have hγDBoundAE : ∀ᵐ y ∂PDE.volumeOn Ω, ‖γD y‖ ≤ CA :=
    Filter.Eventually.of_forall (by
        exact norm_timeVelocity_slice_le γDJoint CA (hscalarFields.2.2.2) τ)
  let sourceDLp : L := compactlySupportedContinuousToScalarLp
     sourceD hsourceDCont hsourceDCompact

  let MaT (i j : Fin d) := scalarL2Multiplier (aT i j) (haTMeas i j)
    CA hCA (haTBoundAE i j)
  let MaD (i j : Fin d) := scalarL2Multiplier (aD i j) (haDMeas i j)
    CA hCA (haDBoundAE i j)
  let MdriftT (j : Fin d) := scalarL2Multiplier (driftT j) (hdriftTMeas j)
    CA hCA (hdriftTBoundAE j)
  let MdriftD (j : Fin d) := scalarL2Multiplier (driftD j) (hdriftDMeas j)
    CA hCA (hdriftDBoundAE j)
  let MγT := scalarL2Multiplier γT hγTMeas CA hCA hγTBoundAE
  let MγD := scalarL2Multiplier γD hγDMeas CA hCA hγDBoundAE
  let gradCoord : Fin d → X →L[ℝ] L := fun i =>
    (PDE.hilbertVectorLpCoord Ω (2 ) i).comp (gradientCLM hΩ)
  let Vop : X →L[ℝ] L := (valueCLM hΩ).comp A
  let Gop  := fun i => (gradCoord i).comp A
  let Wop : Fin d → X →L[ℝ] L := fun i =>
    (cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h).comp
      (valueCLM hΩ)
  let Eop : Fin d → X →L[ℝ] L := fun i => Gop i - Wop i
  let Hop : Fin d → X →L[ℝ] L := fun i => Gop i + Wop i
  have hηMeas : AEStronglyMeasurable η.toFun (PDE.volumeOn Ω) :=
    η.smooth.continuous.aestronglyMeasurable
  have hηBoundAE : ∀ᵐ y ∂PDE.volumeOn Ω, ‖η y‖ ≤ (1 : ℝ) :=
    ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (η.nonneg y)]
      exact η.le_one y
  let Mη : L →L[ℝ] L := scalarL2Multiplier η.toFun hηMeas 1 zero_le_one hηBoundAE
  let Uop : Fin d → X →L[ℝ] L := fun j => Mη.comp (gradCoord j)
  let U₀op : X →L[ℝ] L := Mη.comp (valueCLM hΩ)
  let Vraw  := fun v y => valueCLM hΩ (A v) y
  let Graw  := fun v i y =>
    PDE.hilbertVectorLpCoord Ω (2 ) i (gradientCLM hΩ (A v)) y
  let Wraw : X → Fin d → PDE.ScalarField d := fun v i y =>
    cutoffGradientSpatialDifferenceQuotientL2 hΩ.measurableSet η i k h
      (valueCLM hΩ v) y
  let Eraw  := fun v i y =>
    Graw v i y - Wraw v i y
  let Hraw  := fun v i y =>
    Graw v i y + Wraw v i y
  let Uraw : X → Fin d → PDE.ScalarField d := fun v j y => η y *
    PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ v) y
  let U₀raw : X → PDE.ScalarField d := fun v y => η y * valueCLM hΩ v y
  have hVAE (v : X) : ⇑(Vop v) =ᵐ[PDE.volumeOn Ω] Vraw v := by
    dsimp only [Vop, Vraw, ContinuousLinearMap.comp_apply]
    exact Filter.Eventually.of_forall fun _ => rfl
  have hGAE (v : X) (i : Fin d) : ⇑(Gop i v) =ᵐ[PDE.volumeOn Ω] Graw v i := by
    dsimp only [Gop, Graw, ContinuousLinearMap.comp_apply]
    exact Filter.Eventually.of_forall fun _ => rfl
  have hWAE (v : X) (i : Fin d) : ⇑(Wop i v) =ᵐ[PDE.volumeOn Ω] Wraw v i := by
    dsimp only [Wop, Wraw, ContinuousLinearMap.comp_apply]
    exact Filter.Eventually.of_forall fun _ => rfl
  have hEAE (v : X) (i : Fin d) : ⇑(Eop i v) =ᵐ[PDE.volumeOn Ω] Eraw v i := by
    change ⇑(Gop i v - Wop i v) =ᵐ[PDE.volumeOn Ω] Eraw v i
    filter_upwards [MeasureTheory.Lp.coeFn_sub (Gop i v) (Wop i v), hGAE v i,
      hWAE v i] with y hsub hG hW
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hG, hW]
  have hHAE (v : X) (i : Fin d) : ⇑(Hop i v) =ᵐ[PDE.volumeOn Ω] Hraw v i := by
    change ⇑(Gop i v + Wop i v) =ᵐ[PDE.volumeOn Ω] Hraw v i
    filter_upwards [MeasureTheory.Lp.coeFn_add (Gop i v) (Wop i v), hGAE v i,
      hWAE v i] with y hadd hG hW
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hG, hW]
  have hUAE (v : X) (j : Fin d) : ⇑(Uop j v) =ᵐ[PDE.volumeOn Ω] Uraw v j := by
    simpa only [Uop, Uraw, Mη, gradCoord, ContinuousLinearMap.comp_apply] using
      scalarL2Multiplier_apply_ae η.toFun hηMeas 1 zero_le_one hηBoundAE
        (PDE.hilbertVectorLpCoord Ω (2 ) j (gradientCLM hΩ v))
  have hU₀AE (v : X) : ⇑(U₀op v) =ᵐ[PDE.volumeOn Ω] U₀raw v := by
    simpa only [U₀op, U₀raw, Mη, ContinuousLinearMap.comp_apply] using
      scalarL2Multiplier_apply_ae η.toFun hηMeas 1 zero_le_one hηBoundAE
        (valueCLM hΩ v)
  let left : X → ℝ := h10CommutatorLhsLocal
    r₀ r₁ h₀₁ hΩ hΩbounded a b c F hFSmooth ζ η χ k h τ hηshift
  let rightInner : X → ℝ := fun v =>
    -Inner.inner ℝ sourceDLp (Vop v) -
      (∑ i : Fin d, ∑ j : Fin d,
        Inner.inner ℝ (MaT i j (Eop j v) + MaD i j (Uop j v)) (Hop i v)) -
      (∑ j : Fin d,
        Inner.inner ℝ (MdriftT j (Eop j v) + MdriftD j (Uop j v)) (Vop v)) +
      Inner.inner ℝ (MγT (Vop v) + MγD (U₀op v)) (Vop v)
  let rightRaw : X → ℝ := h10CommutatorRawRhsLocal
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth ζ η χ k h τ hηshift
  have hsourceInner (v : X) :
      Inner.inner ℝ sourceDLp (Vop v) =
        ∫ y in Ω, sourceD y * Vraw v y :=
    inner_scalarLp_eq_setIntegral_of_ae_eq
      sourceDLp (Vop v) sourceD (Vraw v) ((id (coeFn_compactlySupportedContinuousToScalarLp sourceD hsourceDCont hsourceDCompact))) (hVAE v)
  have hprincipalInner (v : X) (i j : Fin d) :
      Inner.inner ℝ (MaT i j (Eop j v) + MaD i j (Uop j v)) (Hop i v) =
        ∫ y in Ω,
          (aT i j y * Eraw v j y + aD i j y * Uraw v j y) * Hraw v i y := by
    calc
      _ = ∫ y in Ω,
          (aT i j y * Eop j v y + aD i j y * Uop j v y) * Hop i v y := by
        simpa only [MaT, MaD] using
          inner_add_scalarL2Multiplier_eq_setIntegral
            (aT i j) (aD i j) (haTMeas i j) (haDMeas i j) CA CA hCA hCA
            (haTBoundAE i j) (haDBoundAE i j) (Eop j v) (Uop j v) (Hop i v)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hEAE v j, hUAE v j, hHAE v i] with y hE hU hH
        rw [hE, hU, hH]
  have hdriftInner (v : X) (j : Fin d) :
      Inner.inner ℝ (MdriftT j (Eop j v) + MdriftD j (Uop j v)) (Vop v) =
        ∫ y in Ω,
          (driftT j y * Eraw v j y + driftD j y * Uraw v j y) * Vraw v y := by
    calc
      _ = ∫ y in Ω,
          (driftT j y * Eop j v y + driftD j y * Uop j v y) * Vop v y := by
        simpa only [MdriftT, MdriftD] using
          inner_add_scalarL2Multiplier_eq_setIntegral
            (driftT j) (driftD j) (hdriftTMeas j) (hdriftDMeas j) CA CA hCA hCA
            (hdriftTBoundAE j) (hdriftDBoundAE j) (Eop j v) (Uop j v) (Vop v)
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hEAE v j, hUAE v j, hVAE v] with y hE hU hV
        rw [hE, hU, hV]
  have hscalarInner (v : X) :
      Inner.inner ℝ (MγT (Vop v) + MγD (U₀op v)) (Vop v) =
        ∫ y in Ω,
          (γT y * Vraw v y + γD y * U₀raw v y) * Vraw v y := by
    calc
      _ = ∫ y in Ω,
          (γT y * Vop v y + γD y * U₀op v y) * Vop v y := (id
  (inner_add_scalarL2Multiplier_eq_setIntegral γT γD hγTMeas hγDMeas CA CA hCA hCA hγTBoundAE hγDBoundAE (Vop v)
    (U₀op v) (Vop v)))
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hVAE v, hU₀AE v] with y hV hU₀
        rw [hV, hU₀]
  have hInnerRaw (v : X) : rightInner v = rightRaw v := by
    dsimp only [rightInner, rightRaw]
    simp_rw [hsourceInner, hprincipalInner, hdriftInner, hscalarInner]
    rfl


  have hprincipalContinuous (i j : Fin d) : Continuous (fun v  =>
      Inner.inner ℝ (MaT i j (Eop j v) + MaD i j (Uop j v)) (Hop i v)) :=
    continuous_inner.comp
      ((((MaT i j).continuous.comp (Eop j).continuous).add
        ((MaD i j).continuous.comp (Uop j).continuous)).prodMk (Hop i).continuous)
  have hdriftContinuous (j : Fin d) : Continuous (fun v  =>
      Inner.inner ℝ (MdriftT j (Eop j v) + MdriftD j (Uop j v)) (Vop v)) :=
    continuous_inner.comp
      ((((MdriftT j).continuous.comp (Eop j).continuous).add
        ((MdriftD j).continuous.comp (Uop j).continuous)).prodMk Vop.continuous)
  have hscalarContinuous : Continuous (fun v  =>
      Inner.inner ℝ (MγT (Vop v) + MγD (U₀op v)) (Vop v)) :=
    continuous_inner.comp
      (((MγT.continuous.comp Vop.continuous).add
        (MγD.continuous.comp U₀op.continuous)).prodMk Vop.continuous)

  exact h10CommutatorFixedStepOutputLocal_of_denseSmoothCore
    r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F hFSmooth
    ζ η χ k h τ hτ hηshift u rightInner (show Continuous left by
        dsimp only [left]
        exact continuous_const.mul
          (((reverseTimeNegativeSourceRaw r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ).continuous.comp
            B.continuous).sub
            (continuous_reverseTimeSpatialForm_apply_energyTest
              r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth τ hτ B))) (by
        dsimp only [rightInner]
        exact (((continuous_inner.comp (continuous_const.prodMk Vop.continuous)).neg.sub
          (continuous_finset_sum _ fun i _ =>
            continuous_finset_sum _ fun j _ => hprincipalContinuous i j)).sub
          (continuous_finset_sum _ fun j _ => hdriftContinuous j)).add hscalarContinuous) hInnerRaw

variable (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1) (η : PDE.QuantitativeSmoothCutoff inner Ω Kη) (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)

private theorem h10CommutatorFromFields

    (δχ δF CF δA CA : ℝ) (hδχ : 0 < δχ) (hδF : 0 < δF)
    (hδA : 0 < δA) (hCF : 0 ≤ CF) (hCA : 0 ≤ CA)
    (hshift : ∀ (k : Fin d) (h : ℝ), |h| ≤ δχ →
      Set.MapsTo (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω)
    (hsourceFields : ∀ (k : Fin d) (h : ℝ), |h| ≤ δF →
      continuousCompactBoundedField CF (fun z  => ζ z.1 * η z.2 *
        spatialDifferenceQuotient k h (fun w : TimeVelocity d => F (r₁ - w.1) w.2) z))
    (hmatrixFields : ∀ (i j k : Fin d) (h : ℝ), |h| ≤ δA →
      twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
        (fun z => reverseTimeCoefficient r₁ a z.1 z.2 i j) k h)
    (hdriftFields : ∀ (j k : Fin d) (h : ℝ), |h| ≤ δA →
      twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
        (fun z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j) k h)
    (hscalarFields : ∀ (k : Fin d) (h : ℝ), |h| ≤ δA →
      twoSpatialFields CA (fun z  => ζ z.1 * χ z.2)
        (fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2) k h) :
    h10CommutatorOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth F
      hFSmooth ζ hζunit η χ := by
  classical
  refine ⟨min δχ (min δF δA), lt_min hδχ (lt_min hδF hδA), ?_⟩
  intro k h hh
  have hhχ : |h| ≤ δχ := hh.trans (min_le_left _ _)

  have hhA : |h| ≤ δA := hh.trans (min_le_right _ _ |>.trans (min_le_right _ _))
  refine ⟨hshift k h hhχ, ?_⟩
  intro τ hτ u

  let hηshift  :=
    (hshift k h hhχ).mono_left (by
        intro y hy
        apply subset_tsupport
        change χ y ≠ 0
        rw [χ.eq_one_on_inner y hy]
        exact one_ne_zero)
  exact h10CommutatorAtFixedStepFromFields r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u CF CA hCA
    (hsourceFields k h (hh.trans (min_le_right _ _ |>.trans (min_le_left _ _)))) (fun i j => hmatrixFields i j k h hhA)
    (fun j => hdriftFields j k h hhA) (hscalarFields k h hhA)

include haSmooth hbSmooth hcSmooth hζunit in
/-- For all sufficiently small signed spatial steps, the arbitrary-`H¹₀`
localized energy test satisfies the literal reverse-time fixed-slice
source-minus-form commutator identity. -/
theorem exists_smallStep_reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator
        :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        ∃ hχshift : Set.MapsTo
          (fun y  => y + h • PDE.basisVec k)
          (tsupport χ.toFun) Ω,
        ∀ (τ : ℝ) (hτ : τ ∈ Set.Icc 0 (r₁ - r₀))
          (u : H10HilbertGraph hΩ),
        let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
          intro y hy
          apply subset_tsupport
          change χ y ≠ 0
          rw [χ.eq_one_on_inner y hy]
          exact one_ne_zero
        let hηshift : Set.MapsTo
            (fun y  => y + h • PDE.basisVec k)
            (tsupport η.toFun) Ω :=
          hχshift.mono_left hηχ
        let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
          localizedSpatialDifferenceQuotientEnergyTestH10CLM
            hΩ η k h η.tsupport_subset hηshift
        let V : PDE.ScalarField d :=
          fun y => valueCLM hΩ (A u) y
        let G : Fin d → PDE.ScalarField d :=
          fun i y =>
            PDE.hilbertVectorLpCoord Ω (2 ) i
              (gradientCLM hΩ (A u)) y
        let W : Fin d → PDE.ScalarField d :=
          fun i y =>
            cutoffGradientSpatialDifferenceQuotientL2
              hΩ.measurableSet η i k h (valueCLM hΩ u) y
        let E : Fin d → PDE.ScalarField d :=
          fun i y => G i y - W i y
        let H : Fin d → PDE.ScalarField d :=
          fun i y => G i y + W i y
        let U : Fin d → PDE.ScalarField d :=
          fun j y =>
            η y *
              PDE.hilbertVectorLpCoord Ω (2 ) j
                (gradientCLM hΩ u) y
        let U₀ : PDE.ScalarField d :=
          fun y => η y * valueCLM hΩ u y
        let source : HypoellipticAleksandrov.Parabolic.ScalarField d :=
          fun z => F (r₁ - z.1) z.2
        let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
          fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
        let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
          fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
        let γ : HypoellipticAleksandrov.Parabolic.ScalarField d :=
          fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
        let sourceD : PDE.ScalarField d :=
          fun y =>
            ζ τ * η y *
              spatialDifferenceQuotient k h source (τ, y)
        let aT : Fin d → Fin d → PDE.ScalarField d :=
          fun i j y =>
            ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
        let aD : Fin d → Fin d → PDE.ScalarField d :=
          fun i j y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h (α i j) (τ, y)
        let driftT : Fin d → PDE.ScalarField d :=
          fun j y =>
            ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
        let driftD : Fin d → PDE.ScalarField d :=
          fun j y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h (drift j) (τ, y)
        let γT : PDE.ScalarField d :=
          fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
        let γD : PDE.ScalarField d :=
          fun y =>
            ζ τ * χ y *
              spatialDifferenceQuotient k h γ (τ, y)
        ζ τ *
            (reverseTimeNegativeSourceRaw
                r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
              reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) =
          -(∫ y in Ω, sourceD y * V y) -
            (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
              (aT i j y * E j y + aD i j y * U j y) *
                H i y) -
            (∑ j : Fin d, ∫ y in Ω,
              (driftT j y * E j y + driftD j y * U j y) *
                V y) +
            ∫ y in Ω,
              (γT y * V y + γD y * U₀ y) * V y := by
  change h10CommutatorOutput r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    F hFSmooth ζ hζunit η χ
  let K : HypoellipticAleksandrov.Parabolic.Region d := ({0} : Set ℝ) ×ˢ tsupport χ.toFun
  let U : HypoellipticAleksandrov.Parabolic.Region d := Set.univ ×ˢ Ω



  obtain ⟨δχ, hδχ, -, hcollar⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar (show IsCompact K by
        dsimp only [K]
        exact isCompact_singleton.prod χ.hasCompactSupport.isCompact) (show IsOpen U by
        dsimp only [U]
        exact isOpen_univ.prod hΩ) (show K ⊆ U by
        intro z hz
        exact ⟨mem_univ _, χ.tsupport_subset hz.2⟩)

  obtain ⟨δF, CF, hδF, hCF, hsourceFields⟩ :=
    exists_reverseTimeSource_cutoff_mul_spatialDifferenceQuotient_fields_of_smoothOnNeighborhood
      r₀ r₁ η η.tsupport_subset ζ hζunit F hFSmooth
  obtain ⟨δA, CA, hδA, hCA, hfields⟩ :=
    exists_reverseTimeCoefficient_cutoff_mul_spatialFields_of_smoothOnNeighborhood
      r₀ r₁ χ χ.tsupport_subset ζ hζunit a b c haSmooth hbSmooth hcSmooth
  dsimp only at hfields
  rcases hfields with ⟨hmatrixFields, hdriftFields, hscalarFields⟩
  exact h10CommutatorFromFields r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth hbSmooth hcSmooth
    F hFSmooth ζ hζunit η χ δχ δF CF δA CA hδχ hδF hδA hCF hCA (show ∀ (k : Fin d) (h : ℝ), |h| ≤ δχ →
      Set.MapsTo (fun y  => y + h • PDE.basisVec k)
        (tsupport χ.toFun) Ω by
        intro k h hh y hy

        exact (hcollar k h hh (show (0, y) ∈ K from ⟨mem_singleton _, hy⟩)).2)
    hsourceFields hmatrixFields hdriftFields hscalarFields

/-- Fixed supplied-collar commutator identity from the raw majorants. -/
theorem reverseTimeSource_sub_reverseTimeSpatialForm_energyTest_eq_commutator_of_majorants

    (η : PDE.QuantitativeSmoothCutoff inner Ω Kη)
    (χ : PDE.QuantitativeSmoothCutoff (tsupport η.toFun) Ω Kχ)
    (ζ : ReverseTimeScalarTest (r₁ - r₀)) (hζunit : ∀ τ : ℝ, ‖ζ τ‖ ≤ 1)
    (δ M : ℝ) (hM : 0 ≤ M)
    (hcarrier : spatialCoordinateShiftCarrier (tsupport χ.toFun) δ ⊆ Ω)
    (a : CoefficientField d) (b : PDE.TimeVectorField d)
    (c F : PDE.TimeScalarField d)
    (haSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => a z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hbSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => b z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hcSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => c z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hFSmooth : IsSmoothOnNeighborhood (fun z : TimeVelocity d => F z.1 z.2)
      (scalarParabolicClosedCylinder r₀ r₁ Ω))
    (hA : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialMatrixFDerivFrobeniusNorm
        (fun w  => reverseTimeCoefficient r₁ a w.1 w.2) z ≤ M)
    (hB : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      PDE.vecEuclideanNorm (reverseTimeDivergenceDrift r₁ a b z.1 z.2) ≤ M)
    (hBD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialVectorFDerivFrobeniusNorm
        (fun w  => reverseTimeDivergenceDrift r₁ a b w.1 w.2) z ≤ M)
    (hq : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      |-(reverseTimeScalarCoefficient r₁ c z.1 z.2)| ≤ M)
    (hqD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w  => -(reverseTimeScalarCoefficient r₁ c w.1 w.2)) z ≤ M)
    (hfD : ∀ z ∈ Set.Icc 0 (r₁ - r₀) ×ˢ
      spatialCoordinateShiftCarrier (tsupport χ.toFun) δ,
      spatialScalarFDerivEuclideanNorm
        (fun w  => -(reverseTimeScalarCoefficient r₁ F w.1 w.2)) z ≤ M)
    (k : Fin d) (h : ℝ) (hh : |h| ≤ δ) (τ : ℝ)
    (hτ : τ ∈ Set.Icc 0 (r₁ - r₀)) (u : H10HilbertGraph hΩ) :
    let hχshift : Set.MapsTo
        (fun y  => y + h • PDE.basisVec k) (tsupport χ.toFun) Ω :=
      mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh
    let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := by
      intro y hy
      apply subset_tsupport
      change χ y ≠ 0
      rw [χ.eq_one_on_inner y hy]
      exact one_ne_zero
    let hηshift : Set.MapsTo
        (fun y  => y + h • PDE.basisVec k)
        (tsupport η.toFun) Ω :=
      hχshift.mono_left hηχ
    let A : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let B : H10HilbertGraph hΩ →L[ℝ] H10HilbertGraph hΩ :=
      localizedSpatialDifferenceQuotientEnergyTestH10CLM
        hΩ η k h η.tsupport_subset hηshift
    let V : PDE.ScalarField d :=
      fun y => valueCLM hΩ (A u) y
    let G : Fin d → PDE.ScalarField d :=
      fun i y =>
        PDE.hilbertVectorLpCoord Ω (2 ) i
          (gradientCLM hΩ (A u)) y
    let W : Fin d → PDE.ScalarField d :=
      fun i y =>
        cutoffGradientSpatialDifferenceQuotientL2
          hΩ.measurableSet η i k h (valueCLM hΩ u) y
    let E : Fin d → PDE.ScalarField d :=
      fun i y => G i y - W i y
    let H : Fin d → PDE.ScalarField d :=
      fun i y => G i y + W i y
    let U : Fin d → PDE.ScalarField d :=
      fun j y =>
        η y *
          PDE.hilbertVectorLpCoord Ω (2 ) j
            (gradientCLM hΩ u) y
    let U₀ : PDE.ScalarField d :=
      fun y => η y * valueCLM hΩ u y
    let source : HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun z => F (r₁ - z.1) z.2
    let α : Fin d → Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun i j z => reverseTimeCoefficient r₁ a z.1 z.2 i j
    let drift : Fin d → HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun j z => reverseTimeDivergenceDrift r₁ a b z.1 z.2 j
    let γ : HypoellipticAleksandrov.Parabolic.ScalarField d :=
      fun z => reverseTimeScalarCoefficient r₁ c z.1 z.2
    let sourceD : PDE.ScalarField d :=
      fun y =>
        ζ τ * η y *
          spatialDifferenceQuotient k h source (τ, y)
    let aT : Fin d → Fin d → PDE.ScalarField d :=
      fun i j y =>
        ζ τ * χ y * spatialTranslate k h (α i j) (τ, y)
    let aD : Fin d → Fin d → PDE.ScalarField d :=
      fun i j y =>
        ζ τ * χ y *
          spatialDifferenceQuotient k h (α i j) (τ, y)
    let driftT : Fin d → PDE.ScalarField d :=
      fun j y =>
        ζ τ * χ y * spatialTranslate k h (drift j) (τ, y)
    let driftD : Fin d → PDE.ScalarField d :=
      fun j y =>
        ζ τ * χ y *
          spatialDifferenceQuotient k h (drift j) (τ, y)
    let γT : PDE.ScalarField d :=
      fun y => ζ τ * χ y * spatialTranslate k h γ (τ, y)
    let γD : PDE.ScalarField d :=
      fun y =>
        ζ τ * χ y *
          spatialDifferenceQuotient k h γ (τ, y)
    ζ τ *
        (reverseTimeNegativeSourceRaw
            r₀ r₁ h₀₁ hΩ hΩbounded F hFSmooth τ (B u) -
          reverseTimeSpatialForm hΩ r₁ τ a b c u (B u)) =
      -(∫ y in Ω, sourceD y * V y) -
        (∑ i : Fin d, ∑ j : Fin d, ∫ y in Ω,
          (aT i j y * E j y + aD i j y * U j y) *
            H i y) -
        (∑ j : Fin d, ∫ y in Ω,
          (driftT j y * E j y + driftD j y * U j y) *
            V y) +
        ∫ y in Ω,
          (γT y * V y + γD y * U₀ y) * V y := by
  let hηχ : tsupport η.toFun ⊆ tsupport χ.toFun := fun y hy =>
    subset_tsupport _ (show χ y ≠ 0 from by rw [χ.eq_one_on_inner y hy]; exact one_ne_zero)
  let hηshift  :=
    (mapsTo_add_smul_basisVec_of_spatialCoordinateShiftCarrier_subset hcarrier k hh).mono_left hηχ
  change h10CommutatorFixedStepOutputLocal r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u
  rcases reverseTimeSpatialRawAmplitude_bounds_of_majorants r₀ r₁ χ δ M
    hcarrier a b c F haSmooth hbSmooth hcSmooth hFSmooth hA hB hBD hq hqD hfD with
    ⟨_, hsourceDQχ, hADQ, hBT, hBDQ, hcT, hcDQ⟩
  have hsourceJoint := continuousCompactBoundedField_reverseTimeSource_of_fixedStepRawAmplitude
      r₀ r₁ η ζ hζunit F hFSmooth k h hηshift M hM
      (fun τ' y hτ' hy => hsourceDQχ k h τ' y hh hτ' (hηχ hy))
  obtain ⟨CA, hCA, hmatrixFields, hdriftFields, hscalarFields⟩ :=
    exists_fixedStep_reverseTimeCoefficientFields_of_majorants
      r₀ r₁ χ ζ hζunit δ M hM hcarrier a b c haSmooth hbSmooth hcSmooth k h hh
      (fun i j τ' y hτ' hy => hADQ i j k h τ' y hh hτ' hy)
      (fun j τ' y hτ' hy => hBT j k h τ' y hh hτ' hy)
      (fun j τ' y hτ' hy => hBDQ j k h τ' y hh hτ' hy)
      (fun τ' y hτ' hy => hcT k h τ' y hh hτ' hy)
      (fun τ' y hτ' hy => hcDQ k h τ' y hh hτ' hy)
  exact h10CommutatorAtFixedStepFromFields r₀ r₁ h₀₁ hΩ hΩbounded a b c haSmooth
    hbSmooth hcSmooth F hFSmooth ζ η χ k h τ hτ hηshift u M CA hCA hsourceJoint
    hmatrixFields hdriftFields hscalarFields
end HypoellipticAleksandrov.Parabolic.Dirichlet
