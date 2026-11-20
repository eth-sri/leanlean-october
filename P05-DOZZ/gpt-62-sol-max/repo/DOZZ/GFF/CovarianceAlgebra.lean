/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.Potential
public import DOZZ.GFF.ComplexBridge
public import GaussianFields

/-!
# DOZZ.GFF.CovarianceAlgebra

The deterministic test-function transport and covariance identities for the pinned logarithmic
kernel.
-/

@[expose] public section

open Filter MeasureTheory
open ProbabilityTheory
open scoped Distributions ENNReal ProbabilityTheory Topology

namespace DOZZ

/-- A DOZZ test function viewed as a compactly supported function on `Vec 2`. -/
noncomputable def testFnVec (f : TestFn) : GaussianFields.Vec 2 → ℝ :=
  fun x => f (complexLinearEquivVecTwo.symm x)

section
variable (f : TestFn)

theorem continuous_testFnVec : Continuous (testFnVec f) := f.continuous.comp complexLinearEquivVecTwo.symm.continuous

theorem hasCompactSupport_testFnVec : HasCompactSupport (testFnVec f) := f.hasCompactSupport.comp_homeomorph complexLinearEquivVecTwo.symm.toHomeomorph

theorem integrable_testFnVec :
    Integrable (testFnVec f) (volume : Measure (GaussianFields.Vec 2)) :=
  (continuous_testFnVec f).integrable_of_hasCompactSupport (hasCompactSupport_testFnVec f)

end

/-- The total mass of the Lebesgue density defined by a DOZZ test function. -/
noncomputable def testMass (f : TestFn) : ℝ := ∫ z : ℂ, f z

/-- The coordinate transport preserves the integral of every DOZZ test function. -/
theorem integral_testFnVec (f : TestFn) :
    ∫ x : GaussianFields.Vec 2, testFnVec f x = testMass f := by
  have hmp := volume_preserving_complexToVecTwo
  have hchange := hmp.integral_comp' (f := complexToVecTwo) (g := testFnVec f)
  calc
    ∫ x : GaussianFields.Vec 2, testFnVec f x =
        ∫ z : ℂ, testFnVec f (complexToVecTwo z) := hchange.symm
    _ = testMass f := by
      rw [testMass]
      congr 1
      funext z
      simp [testFnVec, complexLinearEquivVecTwo, complexToVecTwo]

/-- The standard cutoff has strictly positive Lebesgue mass. -/
theorem abkStandardCutoff_mass_pos :
    0 < ∫ x : GaussianFields.Vec 2, GaussianFields.abkStandardCutoff 2 x := by
  let ζ := GaussianFields.abkStandardCutoff 2
  have hzero : GaussianFields.euclideanNorm (0 : GaussianFields.Vec 2) ≤ 1 / 2 := by
    simp [GaussianFields.euclideanNorm, GaussianFields.euclideanNormSq,
      GaussianFields.euclideanDot]
  have hζ0  := ζ.eq_one_of_norm_le_half 0 hzero
  exact integral_pos_of_integrable_nonneg_nonzero ζ.continuous
    (ζ.continuous.integrable_of_hasCompactSupport ζ.hasCompactSupport)
    ζ.nonneg (by rw [hζ0]; norm_num)

/-- A continuous compactly supported probability density obtained by normalizing the standard
ABK cutoff. -/
noncomputable def abkUnitMassBump : GaussianFields.Vec 2 → ℝ := fun x =>
  (∫ y : GaussianFields.Vec 2, GaussianFields.abkStandardCutoff 2 y)⁻¹ *
    GaussianFields.abkStandardCutoff 2 x

theorem continuous_abkUnitMassBump : Continuous abkUnitMassBump := continuous_const.mul (GaussianFields.abkStandardCutoff 2).continuous

theorem hasCompactSupport_abkUnitMassBump : HasCompactSupport abkUnitMassBump := by
  have hfun : abkUnitMassBump =
      (fun _ : GaussianFields.Vec 2 =>
        (∫ y : GaussianFields.Vec 2, GaussianFields.abkStandardCutoff 2 y)⁻¹) •
          (GaussianFields.abkStandardCutoff 2) := by
    rfl
  rw [hfun]
  exact (GaussianFields.abkStandardCutoff 2).hasCompactSupport.smul_left
    (f := fun _ : GaussianFields.Vec 2 =>
      (∫ y : GaussianFields.Vec 2, GaussianFields.abkStandardCutoff 2 y)⁻¹)

theorem integral_abkUnitMassBump :
    ∫ x : GaussianFields.Vec 2, abkUnitMassBump x = 1 := by
  change (∫ x : GaussianFields.Vec 2,
    (∫ y : GaussianFields.Vec 2, GaussianFields.abkStandardCutoff 2 y)⁻¹ *
      GaussianFields.abkStandardCutoff 2 x) = 1
  rw [integral_const_mul]
  exact inv_mul_cancel₀ (ne_of_gt abkStandardCutoff_mass_pos)

/-- Translate the fixed probability bump to a chosen point. -/
noncomputable def abkUnitMassBumpAt (a : GaussianFields.Vec 2) :
    GaussianFields.Vec 2 → ℝ := fun x => abkUnitMassBump (x - a)

section
variable (a : GaussianFields.Vec 2)

theorem continuous_abkUnitMassBumpAt :
    Continuous (abkUnitMassBumpAt a) := continuous_abkUnitMassBump.comp (continuous_id.sub continuous_const)

theorem hasCompactSupport_abkUnitMassBumpAt :
    HasCompactSupport (abkUnitMassBumpAt a) := by
  change HasCompactSupport (fun x : GaussianFields.Vec 2 => abkUnitMassBump (x - a))
  exact hasCompactSupport_abkUnitMassBump.comp_homeomorph (Homeomorph.subRight a)

theorem integrable_abkUnitMassBumpAt :
    Integrable (abkUnitMassBumpAt a) (volume : Measure (GaussianFields.Vec 2)) :=
  (continuous_abkUnitMassBumpAt a).integrable_of_hasCompactSupport
    (hasCompactSupport_abkUnitMassBumpAt a)

theorem memLp_two_abkUnitMassBumpAt :
    MemLp (abkUnitMassBumpAt a) 2 (volume : Measure (GaussianFields.Vec 2)) :=
  (continuous_abkUnitMassBumpAt a).memLp_of_hasCompactSupport
    (hasCompactSupport_abkUnitMassBumpAt a)

theorem integral_abkUnitMassBumpAt :
    ∫ x : GaussianFields.Vec 2, abkUnitMassBumpAt a x = 1 := by
  calc
    ∫ x : GaussianFields.Vec 2, abkUnitMassBumpAt a x =
        ∫ x : GaussianFields.Vec 2, abkUnitMassBump x := integral_sub_right_eq_self abkUnitMassBump a
    _ = 1 := integral_abkUnitMassBump

end

theorem abkUnitMassBump_support_subset_unitBall :
    Function.support abkUnitMassBump ⊆
      {x : GaussianFields.Vec 2 | GaussianFields.euclideanNorm x ≤ 1} := by
  intro x hx
  have hcut : GaussianFields.abkStandardCutoff 2 x ≠ 0 := by
    intro hzero
    apply hx
    simp [abkUnitMassBump, hzero]
  exact (GaussianFields.abkStandardCutoff 2).support_subset_unitBall hcut

theorem abkUnitMassBumpAt_eq_zero_of_norm_le
    {R : ℝ} (x a : GaussianFields.Vec 2)
    (hx : GaussianFields.euclideanNorm x ≤ R)
    (ha : R + 1 < GaussianFields.euclideanNorm a) :
    abkUnitMassBumpAt a x = 0 := by
  by_contra hne
  have hmem : x - a ∈ Function.support abkUnitMassBump := by
    assumption
  have hshift : GaussianFields.euclideanNorm (x - a) ≤ 1 :=
    abkUnitMassBump_support_subset_unitBall hmem
  have hreverse := GaussianFields.abs_euclideanNorm_sub_euclideanNorm_le a x
  have hdist : GaussianFields.euclideanNorm (a - x) =
      GaussianFields.euclideanNorm (x - a) := GaussianFields.euclideanNorm_sub_comm a x
  have ha_le := (abs_le.mp hreverse).2
  have : GaussianFields.euclideanNorm a ≤ R + 1 := by linarith
  linarith

/-- The logarithmic ABK pairing integrand is integrable for compact mean-zero tests. The proof
passes to the logarithmic kernel from the uniformly dominated centered Riesz slopes. -/
theorem integrable_abkLogCovarianceKernel_integrand
    (ψ φ : GaussianFields.MeanZeroTestFunction 2) :
    Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2)
      ((volume : Measure (GaussianFields.Vec 2)).prod
        (volume : Measure (GaussianFields.Vec 2))) := by
  let μ  :=
    (volume : Measure (GaussianFields.Vec 2)).prod (volume : Measure (GaussianFields.Vec 2))
  let α : ℕ → ℝ := fun n => ((n : ℝ) + 2)⁻¹
  let slope : ℕ → GaussianFields.Vec 2 × GaussianFields.Vec 2 → ℝ := fun n p =>
    ψ p.1 * φ p.2 *
      GaussianFields.abkCenteredRieszSlopeKernel (α n) p.1 p.2
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hαzero : Tendsto α atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_inv_atTop_zero.comp <;> assumption
  have hα : Tendsto α atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hαzero, Filter.Eventually.of_forall ?_⟩
    intro n
    exact Set.mem_Ioi.mpr (inv_pos.mpr (by positivity))
  have hαpos (n : ℕ) : 0 < α n := inv_pos.mpr (by positivity)
  have hαle (n : ℕ) : α n ≤ 1 / 2 := by
    have hden_le : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      linarith
    dsimp [α]
    calc
      ((n : ℝ) + 2)⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ (by positivity) (by norm_num)).2 hden_le
      _ = 1 / 2 := by norm_num
  have hconv : ∀ᵐ p : GaussianFields.Vec 2 × GaussianFields.Vec 2 ∂μ,
      Tendsto (fun n => slope n p) atTop
        (𝓝 (ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2)) := by
    filter_upwards [GaussianFields.ae_tendsto_abkCenteredRieszSlopeKernel_integrand
      (by norm_num : 0 < 2) ψ φ] with p hp
    apply hp.comp <;> assumption
  have hterms : ∀ n : ℕ, Integrable (slope n) μ := by
    intro n
    apply GaussianFields.integrable_abkCenteredRieszSlopeKernel_integrand_of_pos_le_half <;> solve_by_elim
  rcases GaussianFields.exists_integrable_bound_abkCenteredRieszSlopeKernel_integrand
      (by norm_num : 0 < 2) ψ φ with ⟨bound, hbound_int, hbound⟩
  have hbound_seq : ∀ᶠ n : ℕ in atTop,
      ∀ᵐ p ∂μ, ‖slope n p‖ ≤ bound p := by
    exact Eventually.of_forall fun n => hbound _ (hαpos n) (hαle n)
  have hlintegral_bound : ∀ᶠ n : ℕ in atTop,
      (∫⁻ p, ‖slope n p‖ₑ ∂μ) ≤ ∫⁻ p, ‖bound p‖ₑ ∂μ := by
    filter_upwards [hbound_seq] with n hn
    apply lintegral_mono_ae
    filter_upwards [hn] with p hp
    have hnonneg  := le_trans (norm_nonneg _) hp
    simpa only [Real.enorm_eq_ofReal hnonneg, ofReal_norm] using
      ENNReal.ofReal_le_ofReal hp
  have hlimsup := limsup_le_of_le (a := ∫⁻ p, ‖bound p‖ₑ ∂μ) (h := hlintegral_bound)
  have hliminf_finite :
      liminf (fun n : ℕ => ∫⁻ p, ‖slope n p‖ₑ ∂μ) atTop < (⊤ : ℝ≥0∞) := by
    have hlim :
        liminf (fun n : ℕ => ∫⁻ p, ‖slope n p‖ₑ ∂μ) atTop ≤
          limsup (fun n : ℕ => ∫⁻ p, ‖slope n p‖ₑ ∂μ) atTop := liminf_le_limsup
    exact lt_of_le_of_lt (hlim.trans hlimsup)
      ((hasFiniteIntegral_iff_enorm).1 hbound_int.hasFiniteIntegral)
  have hlimnorm : ∀ᵐ p ∂μ,
      liminf (fun n : ℕ => ‖slope n p‖ₑ) atTop =
        ‖ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2‖ₑ := by
    filter_upwards [hconv] with p hp
    exact hp.enorm.liminf_eq
  have hfatou :
      (∫⁻ p, ‖ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2‖ₑ ∂μ) ≤
        liminf (fun n : ℕ => ∫⁻ p, ‖slope n p‖ₑ ∂μ) atTop := by
    calc
      _ = ∫⁻ p, liminf (fun n : ℕ => ‖slope n p‖ₑ) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hlimnorm] with p hp
        exact hp.symm
      _ ≤ _ := lintegral_liminf_le' (fun n => (hterms n).aemeasurable.enorm)
  have htarget_meas := aestronglyMeasurable_of_tendsto_ae _ (fun n => (hterms n).aestronglyMeasurable) hconv
  have htarget_finite := lt_of_le_of_lt hfatou hliminf_finite
  exact ⟨htarget_meas, (hasFiniteIntegral_iff_enorm).2 htarget_finite⟩

/-- A compactly supported function on `Vec 2` is supported in some Euclidean ball. -/
theorem exists_ball_of_hasCompactSupport {u : GaussianFields.Vec 2 → ℝ}
    (hu : HasCompactSupport u) :
    ∃ R : ℝ, 0 ≤ R ∧
      Function.support u ⊆ {x : GaussianFields.Vec 2 | GaussianFields.euclideanNorm x ≤ R} := by
  rcases hu.exists_pos_le_norm with ⟨r, hr, hvanish⟩
  refine ⟨2 * r, by positivity, ?_⟩
  intro x hx
  have hnorm : ‖x‖ ≤ r := by
    by_contra hnot
    exact hx (hvanish x (le_of_not_ge hnot))
  calc
    GaussianFields.euclideanNorm x ≤ (2 : ℝ) * ‖x‖ := by
      simpa using GaussianFields.euclideanNorm_le_card_mul_norm x
    _ ≤ 2 * r := mul_le_mul_of_nonneg_left hnorm (by norm_num)

/-- Mean-zero centering of a continuous compactly supported function by a translated unit-mass
bump. -/
noncomputable def centeredCompactFunctionAt (u : GaussianFields.Vec 2 → ℝ)
    (hu : Continuous u) (huc : HasCompactSupport u) (a : GaussianFields.Vec 2) :
    GaussianFields.MeanZeroTestFunction 2 := by
  let m  := ∫ x : GaussianFields.Vec 2, u x
  let η := abkUnitMassBumpAt a
  have huI : Integrable u (volume : Measure (GaussianFields.Vec 2)) :=
    hu.integrable_of_hasCompactSupport huc
  have hηc : HasCompactSupport (fun x : GaussianFields.Vec 2 => m * η x) := by
    change HasCompactSupport ((fun _ : GaussianFields.Vec 2 => m) • η)
    exact (hasCompactSupport_abkUnitMassBumpAt a).smul_left
      (f := fun _ : GaussianFields.Vec 2 => m)
  refine
    { toFun := fun x => u x - m * η x
      continuous := hu.sub ((continuous_abkUnitMassBumpAt a).const_mul m)
      hasCompactSupport := huc.sub hηc
      integrable := huI.sub ((integrable_abkUnitMassBumpAt a).const_mul m)
      memLp_two :=
        (hu.memLp_of_hasCompactSupport huc).sub
          ((memLp_two_abkUnitMassBumpAt a).const_mul m)
      integral_eq_zero := ?_ }
  dsimp [m, η]
  rw [integral_sub huI ((integrable_abkUnitMassBumpAt a).const_mul _), integral_const_mul,
    integral_abkUnitMassBumpAt]
  simp

/-- On a region disjoint from the translated centering bump, centered data agrees with the
original compactly supported function. -/
theorem centeredCompactFunctionAt_eq_of_bump_zero
    (u : GaussianFields.Vec 2 → ℝ) (hu : Continuous u) (huc : HasCompactSupport u)
    (a x : GaussianFields.Vec 2) (hη : abkUnitMassBumpAt a x = 0) :
    centeredCompactFunctionAt u hu huc a x = u x := by
  simp [centeredCompactFunctionAt, hη]

/-- The logarithmic kernel is integrable against any two continuous compactly supported
densities. Centering each one outside its support reduces this to the ABK mean-zero theorem. -/
theorem integrable_compactLogKernelPair (u v : GaussianFields.Vec 2 → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v) :
    Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        u p.1 * v p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2)
      ((volume : Measure (GaussianFields.Vec 2)).prod
        (volume : Measure (GaussianFields.Vec 2))) := by
  rcases exists_ball_of_hasCompactSupport huc with ⟨Ru, hRu, huball⟩
  rcases exists_ball_of_hasCompactSupport hvc with ⟨Rv, hRv, hvball⟩
  let R := max Ru Rv
  have hR : 0 ≤ R := le_max_of_le_left hRu
  have hRuR : Ru ≤ R := le_max_left _ _
  have hRvR : Rv ≤ R := le_max_right _ _
  let a  := GaussianFields.abkRadialPoint 2 (R + 2)
  have ha_norm : GaussianFields.euclideanNorm a = R + 2 := by
    rw [GaussianFields.euclideanNorm_abkRadialPoint (by norm_num : 0 < 2)]
    exact abs_of_nonneg (by linarith)
  have ha : R + 1 < GaussianFields.euclideanNorm a := by
    rw [ha_norm]
    linarith
  let ψ := centeredCompactFunctionAt u hu huc a
  let φ := centeredCompactFunctionAt v hv hvc a
  have hψ := integrable_abkLogCovarianceKernel_integrand ψ φ
  let S : Set (GaussianFields.Vec 2 × GaussianFields.Vec 2) :=
    {p | u p.1 ≠ 0 ∧ v p.2 ≠ 0}
  have huS  :=
    (MeasurableSet.singleton (0 : ℝ)).compl.preimage hu.measurable
  have hvS  :=
    (MeasurableSet.singleton (0 : ℝ)).compl.preimage hv.measurable
  have hS : MeasurableSet S := by
    change MeasurableSet
      ({x : GaussianFields.Vec 2 | u x ≠ 0} ×ˢ {x : GaussianFields.Vec 2 | v x ≠ 0})
    exact huS.prod hvS
  have hψeq {x : GaussianFields.Vec 2} (hx : u x ≠ 0) : ψ x = u x := by
    have hxmem : x ∈ Function.support u := by assumption
    have hxR  := (huball hxmem).trans hRuR
    dsimp [ψ]
    exact centeredCompactFunctionAt_eq_of_bump_zero u hu huc a x
      (abkUnitMassBumpAt_eq_zero_of_norm_le x a hxR ha)
  have hφeq {y : GaussianFields.Vec 2} (hy : v y ≠ 0) : φ y = v y := by
    have hymem : y ∈ Function.support v := by assumption
    have hyR  := (hvball hymem).trans hRvR
    dsimp [φ]
    exact centeredCompactFunctionAt_eq_of_bump_zero v hv hvc a y
      (abkUnitMassBumpAt_eq_zero_of_norm_le y a hyR ha)
  have heq :
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        u p.1 * v p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2) =
      S.indicator (fun p => ψ p.1 * φ p.2 * GaussianFields.abkLogCovarianceKernel p.1 p.2) := by
    funext p
    by_cases hux : u p.1 ≠ 0
    · by_cases hvx : v p.2 ≠ 0
      · simp [S, hux, hvx, hψeq hux, hφeq hvx]
      · have hv0 : v p.2 = 0 := by simpa using hvx
        simp [S, hux, hv0]
    · have hu0 : u p.1 = 0 := by simpa using hux
      simp [S, hu0]
  rw [heq]
  exact hψ.indicator hS

/-- The smooth coordinate bridge agrees pointwise with the measurable coordinate equivalence. -/
theorem testFnVec_complexToVecTwo (f : TestFn) (z : ℂ) :
    testFnVec f (complexToVecTwo z) = f z := by
  change f (complexLinearEquivVecTwo.symm (complexToVecTwo z)) = f z
  rw [← complexLinearEquivVecTwo_apply]
  simp

/-- Product coordinate equivalence from `ℂ × ℂ` to `Vec 2 × Vec 2`. -/
noncomputable def complexPairToVecTwo :
    ℂ × ℂ ≃ᵐ GaussianFields.Vec 2 × GaussianFields.Vec 2 :=
  complexToVecTwo.prodCongr complexToVecTwo

/-- The product coordinate equivalence preserves product Lebesgue measure. -/
theorem volume_preserving_complexPairToVecTwo :
    MeasurePreserving complexPairToVecTwo
      ((volume : Measure ℂ).prod (volume : Measure ℂ))
      ((volume : Measure (GaussianFields.Vec 2)).prod
        (volume : Measure (GaussianFields.Vec 2))) := by
  change MeasurePreserving (Prod.map complexToVecTwo complexToVecTwo) _ _
  exact MeasurePreserving.prod volume_preserving_complexToVecTwo
    volume_preserving_complexToVecTwo

/-- The pinned kernel expressed in `Vec 2` coordinates. -/
noncomputable def gffKernelVec (x y : GaussianFields.Vec 2) : ℝ :=
  gffKernel (complexToVecTwo.symm x) (complexToVecTwo.symm y)

/-- The transported pinned kernel is the ABK logarithmic kernel plus the two pinning potentials. -/
theorem gffKernelVec_eq (x y : GaussianFields.Vec 2) :
    gffKernelVec x y =
      GaussianFields.abkLogCovarianceKernel x y +
        Real.log (max 1 (GaussianFields.euclideanNorm x)) +
        Real.log (max 1 (GaussianFields.euclideanNorm y)) := by
  have hdiff : complexToVecTwo (complexToVecTwo.symm x - complexToVecTwo.symm y) = x - y := by
    rw [complexToVecTwo_sub]
    simp
  have hnormxy :
      GaussianFields.euclideanNorm (x - y) =
        ‖complexToVecTwo.symm x - complexToVecTwo.symm y‖ := by
    calc
      GaussianFields.euclideanNorm (x - y) =
          GaussianFields.euclideanNorm
            (complexToVecTwo (complexToVecTwo.symm x - complexToVecTwo.symm y)) := by
              rw [hdiff]
      _ = ‖complexToVecTwo.symm x - complexToVecTwo.symm y‖ :=
        euclideanNorm_complexToVecTwo _
  have hnormx : GaussianFields.euclideanNorm x = ‖complexToVecTwo.symm x‖ := by
    calc
      GaussianFields.euclideanNorm x =
          GaussianFields.euclideanNorm (complexToVecTwo (complexToVecTwo.symm x)) := by simp
      _ = ‖complexToVecTwo.symm x‖ := euclideanNorm_complexToVecTwo _
  have hnormy : GaussianFields.euclideanNorm y = ‖complexToVecTwo.symm y‖ := by
    calc
      GaussianFields.euclideanNorm y =
          GaussianFields.euclideanNorm (complexToVecTwo (complexToVecTwo.symm y)) := by simp
      _ = ‖complexToVecTwo.symm y‖ := euclideanNorm_complexToVecTwo _
  simp [gffKernelVec, gffKernel, GaussianFields.abkLogCovarianceKernel, normPlus,
    hnormxy, hnormx, hnormy]

/-- The logarithmic pinning potential in `Vec 2` coordinates. -/
noncomputable def logNormPlusVec (x : GaussianFields.Vec 2) : ℝ :=
  Real.log (max 1 (GaussianFields.euclideanNorm x))

/-- The `Vec 2` potential is continuous because its logarithm has argument at least one. -/
theorem continuous_logNormPlusVec : Continuous logNormPlusVec := by
  apply (continuous_const.max GaussianFields.continuous_euclideanNorm).log
  intro x
  positivity

/-- Integrability of a test density times the pinning potential. -/
theorem integrable_testFnVec_mul_logNormPlus (f : TestFn) :
    Integrable (fun x : GaussianFields.Vec 2 => testFnVec f x * logNormPlusVec x)
      (volume : Measure (GaussianFields.Vec 2)) := by
  apply (continuous_testFnVec f).mul continuous_logNormPlusVec |>.integrable_of_hasCompactSupport
  exact (hasCompactSupport_testFnVec f).mul_right

/-- The finite planar logarithmic pairing of two DOZZ test densities. -/
noncomputable def testFnLogPairing (f g : TestFn) : ℝ :=
  ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
    testFnVec f p.1 * testFnVec g p.2 *
      GaussianFields.abkLogCovarianceKernel p.1 p.2
    ∂((volume : Measure (GaussianFields.Vec 2)).prod
      (volume : Measure (GaussianFields.Vec 2)))

/-- The first logarithmic pinning moment of a test density. -/
noncomputable def testFnPotential (f : TestFn) : ℝ :=
  ∫ x : GaussianFields.Vec 2, testFnVec f x * logNormPlusVec x

section
variable (f g : TestFn)

/-- Integrability of the full pinned covariance kernel against compact test densities. -/
theorem integrable_gffKernelVec_pair :
    Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        testFnVec f p.1 * gffKernelVec p.1 p.2 * testFnVec g p.2)
      ((volume : Measure (GaussianFields.Vec 2)).prod
        (volume : Measure (GaussianFields.Vec 2))) := by
  let μ  :=
    (volume : Measure (GaussianFields.Vec 2)).prod
      (volume : Measure (GaussianFields.Vec 2))
  have hlog := integrable_compactLogKernelPair _ _ (continuous_testFnVec f) (continuous_testFnVec g)
    (hasCompactSupport_testFnVec f) (hasCompactSupport_testFnVec g)
  have hpotx := (integrable_testFnVec_mul_logNormPlus f).mul_prod
    (integrable_testFnVec g)
  have hpoty := (integrable_testFnVec f).mul_prod
    (integrable_testFnVec_mul_logNormPlus g)
  have hsum : Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        testFnVec f p.1 * testFnVec g p.2 *
            GaussianFields.abkLogCovarianceKernel p.1 p.2 +
          (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 +
          testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2)) μ := by
    have hpotx' : Integrable
        (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
          (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2) μ := by
      simpa [μ] using hpotx
    have hpoty' : Integrable
        (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
          testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2)) μ := by
      simpa [μ] using hpoty
    exact (hlog.add hpotx').add hpoty'
  apply hsum.congr
  filter_upwards with p
  rw [gffKernelVec_eq]
  dsimp [logNormPlusVec]
  ring

/-- The `Vec 2` integral of the pinned kernel expands into its logarithmic ABK term and the two
positive potential terms, with all three product integrands integrable. -/
theorem integral_gffKernelVec_pair :
    (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
      testFnVec f p.1 * gffKernelVec p.1 p.2 * testFnVec g p.2
        ∂((volume : Measure (GaussianFields.Vec 2)).prod
          (volume : Measure (GaussianFields.Vec 2)))) =
      testFnLogPairing f g + testFnPotential f * testMass g +
        testMass f * testFnPotential g := by
  let μ  :=
    (volume : Measure (GaussianFields.Vec 2)).prod
      (volume : Measure (GaussianFields.Vec 2))
  have hlog := integrable_compactLogKernelPair _ _ (continuous_testFnVec f) (continuous_testFnVec g)
    (hasCompactSupport_testFnVec f) (hasCompactSupport_testFnVec g)
  have hpotx := (integrable_testFnVec_mul_logNormPlus f).mul_prod
    (integrable_testFnVec g)
  have hpoty := (integrable_testFnVec f).mul_prod
    (integrable_testFnVec_mul_logNormPlus g)
  have hpotx' : Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2) μ := by
    simpa [μ] using hpotx
  have hpoty' : Integrable
      (fun p : GaussianFields.Vec 2 × GaussianFields.Vec 2 =>
        testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2)) μ := by
    simpa [μ] using hpoty
  have hsplit :
      (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
        testFnVec f p.1 * gffKernelVec p.1 p.2 * testFnVec g p.2 ∂μ) =
        (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          testFnVec f p.1 * testFnVec g p.2 *
              GaussianFields.abkLogCovarianceKernel p.1 p.2 +
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 +
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ) := by
    apply integral_congr_ae
    filter_upwards with p
    rw [gffKernelVec_eq]
    dsimp [logNormPlusVec]
    ring
  have hsplit_integrals :
      (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          testFnVec f p.1 * testFnVec g p.2 *
            GaussianFields.abkLogCovarianceKernel p.1 p.2 ∂μ) +
          (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 ∂μ) +
          ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ =
        ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          testFnVec f p.1 * testFnVec g p.2 *
              GaussianFields.abkLogCovarianceKernel p.1 p.2 +
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 +
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := by
    calc
      _ = ((∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
              testFnVec f p.1 * testFnVec g p.2 *
                GaussianFields.abkLogCovarianceKernel p.1 p.2 ∂μ) +
            ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
              (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 ∂μ) +
          ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := by ring
      _ = (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            testFnVec f p.1 * testFnVec g p.2 *
              GaussianFields.abkLogCovarianceKernel p.1 p.2 +
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 ∂μ) +
          ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := by
          congr 1
          exact (integral_add hlog hpotx').symm
      _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            (testFnVec f p.1 * testFnVec g p.2 *
                GaussianFields.abkLogCovarianceKernel p.1 p.2 +
              (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2) +
                testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := (integral_add (hlog.add hpotx') hpoty').symm
      _ = _ := by
          rfl
  have hpotx_int :
      (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
        (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 ∂μ) =
          testFnPotential f * testMass g := by
    change (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
      (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2
        ∂((volume : Measure (GaussianFields.Vec 2)).prod
          (volume : Measure (GaussianFields.Vec 2)))) = _
    calc
      _ = (∫ x : GaussianFields.Vec 2,
            testFnVec f x * logNormPlusVec x) *
          ∫ y : GaussianFields.Vec 2, testFnVec g y :=
        integral_prod_mul (fun x : GaussianFields.Vec 2 =>
          testFnVec f x * logNormPlusVec x) (testFnVec g)
      _ = testFnPotential f * testMass g := by
        rw [testFnPotential, integral_testFnVec]
  have hpoty_int :
      (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
        testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ) =
          testMass f * testFnPotential g := by
    change (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
      testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2)
        ∂((volume : Measure (GaussianFields.Vec 2)).prod
          (volume : Measure (GaussianFields.Vec 2)))) = _
    calc
      _ = (∫ x : GaussianFields.Vec 2, testFnVec f x) *
          ∫ y : GaussianFields.Vec 2, testFnVec g y * logNormPlusVec y :=
        integral_prod_mul (testFnVec f)
          (fun y : GaussianFields.Vec 2 => testFnVec g y * logNormPlusVec y)
      _ = testMass f * testFnPotential g := by
        rw [integral_testFnVec, testFnPotential]
  calc
    _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          testFnVec f p.1 * testFnVec g p.2 *
              GaussianFields.abkLogCovarianceKernel p.1 p.2 +
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 +
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := hsplit
    _ = (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
          testFnVec f p.1 * testFnVec g p.2 *
            GaussianFields.abkLogCovarianceKernel p.1 p.2 ∂μ) +
          (∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            (testFnVec f p.1 * logNormPlusVec p.1) * testFnVec g p.2 ∂μ) +
          ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2,
            testFnVec f p.1 * (testFnVec g p.2 * logNormPlusVec p.2) ∂μ := hsplit_integrals.symm
    _ = testFnLogPairing f g + testFnPotential f * testMass g +
          testMass f * testFnPotential g := by
        rw [testFnLogPairing, hpotx_int, hpoty_int]

/-- The DOZZ covariance is the explicit log-energy expansion of the equator projection
`f dx - m(f) ν`. The two positive potential terms come from the cross energies, and the circle
self-energy term vanishes by the unit-circle identities proved in `Potential`. -/
theorem gffCov_eq_equatorLogEnergy :
    gffCov f g = testFnLogPairing f g + testFnPotential f * testMass g +
      testMass f * testFnPotential g := by
  let μc  := (volume : Measure ℂ).prod (volume : Measure ℂ)
  let μv  :=
    (volume : Measure (GaussianFields.Vec 2)).prod
      (volume : Measure (GaussianFields.Vec 2))
  let Fv : GaussianFields.Vec 2 × GaussianFields.Vec 2 → ℝ := fun p =>
    testFnVec f p.1 * gffKernelVec p.1 p.2 * testFnVec g p.2
  let Fc : ℂ × ℂ → ℝ := fun p => f p.1 * gffKernel p.1 p.2 * g p.2
  have hFv : Integrable Fv μv := by
    simpa [Fv, μv] using integrable_gffKernelVec_pair f g
  have hcomp : Fc = Fv ∘ complexPairToVecTwo := by
    funext p
    change f p.1 * gffKernel p.1 p.2 * g p.2 =
      Fv (complexToVecTwo p.1, complexToVecTwo p.2)
    simp [Fv, gffKernelVec, testFnVec_complexToVecTwo]
  have hFc : Integrable Fc μc := by
    have hcompInt : Integrable (Fv ∘ complexPairToVecTwo) μc := by
      simpa [μc, μv] using
        volume_preserving_complexPairToVecTwo.integrable_comp_of_integrable hFv
    exact hcompInt.congr (by
      filter_upwards with p
      exact (congrFun hcomp p).symm)
  have hprod : gffCov f g = ∫ p : ℂ × ℂ, Fc p ∂μc := by
    unfold gffCov
    exact (integral_prod _ hFc).symm
  have hchange := volume_preserving_complexPairToVecTwo.integral_comp'
    (f := complexPairToVecTwo) (g := Fv)
  calc
    gffCov f g = ∫ p : ℂ × ℂ, Fc p ∂μc := hprod
    _ = ∫ p : ℂ × ℂ, Fv (complexPairToVecTwo p) ∂μc := by
      apply integral_congr_ae
      filter_upwards with p
      exact congrFun hcomp p
    _ = ∫ p : GaussianFields.Vec 2 × GaussianFields.Vec 2, Fv p ∂μv :=
      hchange
    _ = testFnLogPairing f g + testFnPotential f * testMass g +
          testMass f * testFnPotential g := by
      simpa [Fv, μv] using integral_gffKernelVec_pair f g

end

/-- The ABK logarithmic covariance pairing is nonnegative on its diagonal, as it is the
covariance of the canonical L² Gaussian field. -/
theorem abkLogCovariancePairing_self_nonneg
    (ψ : GaussianFields.MeanZeroTestFunction 2) :
    0 ≤ GaussianFields.abkLogCovariancePairing ψ ψ := by
  let P := GaussianFields.scaleSpaceWhiteNoiseMeasure 2
  let X := GaussianFields.abkLogCorrelatedFieldL2Canonical
    (by norm_num : 0 < 2) (GaussianFields.abkStandardCutoff 2) ψ
  have hXa  := (Lp.aestronglyMeasurable X).aemeasurable
  have hcov : 0 ≤ cov[X, X; P] := by
    rw [covariance_self hXa]
    exact variance_nonneg X P
  have hformula :=
    GaussianFields.covariance_abkLogCorrelatedFieldL2Canonical_eq_logCovariancePairing
      (by norm_num : 0 < 2) (GaussianFields.abkStandardCutoff 2) ψ ψ
  change 0 ≤ cov[
    GaussianFields.abkLogCorrelatedFieldL2Canonical
      (by norm_num : 0 < 2) (GaussianFields.abkStandardCutoff 2) ψ,
    GaussianFields.abkLogCorrelatedFieldL2Canonical
      (by norm_num : 0 < 2) (GaussianFields.abkStandardCutoff 2) ψ;
    GaussianFields.scaleSpaceWhiteNoiseMeasure 2] at hcov
  have hconst : 0 < GaussianFields.abkLGFCovarianceConstant 2 := by
    rw [abkLGFCovarianceConstant_two_eq_one_div_two_pi]
    positivity
  rw [hformula] at hcov
  exact (mul_nonneg_iff_of_pos_left hconst).mp hcov

end DOZZ

end
