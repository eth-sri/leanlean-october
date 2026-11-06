module

public import HypoellipticAleksandrov.Parabolic.SourceDensityPositive
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Measure.InkSpotsSelection
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed from HypoellipticAleksandrov.Measure.InkSpotsSelection


/-!
# Source-aware parabolic level growth

This module turns a source-aware density-to-point relation into the supplied
upper-bound level-growth inequality on a literal physical parabolic box.
-/

 public section

open MeasureTheory Set

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

variable {d : ℕ}

private theorem parabolicOperator_const_sub  (B : CoefficientField d)
    (c : ℝ) (u : HypoellipticAleksandrov.Parabolic.ScalarField d) (z : TimeVelocity d) :
    parabolicOperator B (fun y ↦ c - u y) z = -parabolicOperator B u z := by
  calc
    parabolicOperator B (fun y ↦ c - u y) z =
        parabolicOperator B (fun y ↦ -u y + c) z := by
      congr 1
      funext y
      ring
    _ = parabolicOperator B (fun y ↦ -u y) z :=
      parabolicOperator_add_const B _ c z
    _ = -parabolicOperator B u z := parabolicOperator_neg B u z




private theorem terminalCenter_mem_parabolicClosedBox  {R t₀ : ℝ}
    {v₀ : PDE.Vec d} (hR : 0 < R) :
    (t₀ + R ^ 2, v₀) ∈ parabolicClosedBox 1 R t₀ v₀ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · nlinarith [sq_nonneg R]
  · apply le_of_eq
    ring
  · intro i
    simp only [sub_self, abs_zero]
    exact hR.le

private theorem center_mem_velocityClosedCube  {R : ℝ}
    {v₀ : PDE.Vec d} (hR : 0 < R) :
    v₀ ∈ velocityClosedCube v₀ (R / 2) := by
  intro i
  simp only [sub_self, abs_zero]
  linarith

private theorem contDiffOn_const_sub_div  {U : HypoellipticAleksandrov.Parabolic.Region d}
    {M D : ℝ} {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun z ↦ (M - u z) / D) U :=
  (contDiffOn_const.sub hu).div_const D

private theorem volume_toReal_mono_of_subset  {s t : HypoellipticAleksandrov.Parabolic.Region d}
    (ht : (HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) t ≠ ⊤) (hst : s ⊆ t) :
    ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) s).toReal ≤
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d) t).toReal :=
  ENNReal.toReal_mono ht (measure_mono hst)

variable {F : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem memLp_of_continuousOn_compact_carrier
      {U Q K : HypoellipticAleksandrov.Parabolic.Region d}
    (hF : ContinuousOn F U) (hKU : K ⊆ U) (hKcompact : IsCompact K)
    (hQK : Q ⊆ K) :
    MemLp F (parabolicExponent d) (volume.restrict Q) := by
  have hFK  := hF.mono hKU
  have hKmeas  := hKcompact.measurableSet
  letI : IsFiniteMeasure (volume.restrict K) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact hKcompact.measure_lt_top⟩
  obtain ⟨A, hA⟩ := hKcompact.exists_bound_of_continuousOn hFK

  exact (show MemLp F (parabolicExponent d) (volume.restrict K) by
      refine MemLp.of_bound (hFK.aestronglyMeasurable hKmeas) A ?_
      filter_upwards [ae_restrict_mem hKmeas] with z hz
      exact hA z hz).mono_measure (Measure.restrict_mono_set volume hQK)

private theorem parabolicLpNormOn_abs_div
      {Q : HypoellipticAleksandrov.Parabolic.Region d} {D : ℝ}
    (hD : 0 < D) (hFmem : MemLp F (parabolicExponent d) (volume.restrict Q)) :
    parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
      D⁻¹ * parabolicLpNormOn d F Q := by



  have hinv : 0 ≤ D⁻¹ := inv_nonneg.mpr hD.le
  calc
    parabolicLpNormOn d (fun z ↦ |F z| / D) Q =
        parabolicLpNormOn d (D⁻¹ • fun z ↦ |F z|) Q := by
      congr 2
      funext z
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
      ring
    _ = D⁻¹ * parabolicLpNormOn d (fun z ↦ |F z|) Q := by
      unfold parabolicLpNormOn parabolicELpNormOn
      rw [eLpNorm_const_smul, ENNReal.toReal_mul]
      simp only [Real.enorm_of_nonneg hinv, ENNReal.toReal_ofReal hinv]
    _ = D⁻¹ * parabolicLpNormOn d F Q := by
      congr 1
      unfold parabolicLpNormOn parabolicELpNormOn
      apply congrArg ENNReal.toReal
      apply eLpNorm_congr_enorm_ae (show MemLp (fun z ↦ |F z|) (parabolicExponent d) (volume.restrict Q) by
          exact hFmem.norm).aestronglyMeasurable hFmem.aestronglyMeasurable
      filter_upwards [] with z
      exact Real.enorm_abs (F z)

private theorem source_supersolution_const_sub_div
     {B : CoefficientField d} {M D : ℝ} {F u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    {Q : HypoellipticAleksandrov.Parabolic.Region d} (hD : 0 < D)
    (heq : ∀ z ∈ Q, parabolicOperator B u z = F z) :
    IsParabolicSupersolutionOn B (fun z ↦ -(|F z| / D))
      (fun z ↦ (M - u z) / D) Q := by
  let sharedTerm_3614efacfc := ((fun y ↦ (M - u y) / D))
  intro z hz
  have hoperator : parabolicOperator B sharedTerm_3614efacfc z =
      D⁻¹ * (-parabolicOperator B u z) := by
    calc
      parabolicOperator B sharedTerm_3614efacfc z =
          parabolicOperator B (D⁻¹ • fun y ↦ M - u y) z := by
        congr 1
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
        ring
      _ = D⁻¹ * parabolicOperator B (fun y ↦ M - u y) z :=
        parabolicOperator_const_smul B D⁻¹ _ z
      _ = D⁻¹ * (-parabolicOperator B u z) := by
        rw [parabolicOperator_const_sub]
  rw [hoperator, heq z hz]

  calc
    -(|F z| / D) ≤ -(F z / D) := neg_le_neg ((div_le_div_iff_of_pos_right hD).mpr (le_abs_self (F z)))
    _ = D⁻¹ * (-F z) := by field_simp [hD.ne']

/-- A supplied `SourceDensityToPoint` relation yields raw-equation source-aware level growth
on a physical box. -/
theorem source_level_growth_of_low_set_density
    {d : Nat} {lam Lam beta g C : Real}
    (hdtp : SourceDensityToPoint d lam Lam beta g C)
    {R nu t0 M : Real} {v0 : PDE.Vec d}
    (hR : 0 < R) (hnu : 0 < nu) (hg : g < 1)
    (U : HypoellipticAleksandrov.Parabolic.Region d) (B : CoefficientField d)
    (F u : HypoellipticAleksandrov.Parabolic.ScalarField d) (hU : IsOpen U)
    (hclosed : parabolicClosedBox 1 R t0 v0 ⊆ U)
    (hB : IsContinuousCoefficientOn B U) (hu : ContDiffOn Real 2 u U)
    (hF : ContinuousOn F U)
    (hlower : HasLowerEllipticityOn lam B (parabolicBox 1 R t0 v0))
    (hupper : HasUpperEllipticityOn Lam B (parabolicBox 1 R t0 v0))
    (heq : ∀ z ∈ parabolicBox 1 R t0 v0,
      parabolicOperator B u z = F z)
    (hM : ∀ z ∈ parabolicClosedBox 1 R t0 v0, u z ≤ M)
    (htop : nu ≤ u (t0 + R ^ 2, v0))
    (hdensity : beta * ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
      (parabolicBox 1 R t0 v0)).toReal ≤
      ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d)
        (parabolicBox 1 R t0 v0 ∩ {z | u z ≤ nu / 2})).toReal) :
    nu * ((2 - g) / (2 * (1 - g))) ≤
      M + (C / (1 - g)) * R ^ ((d : Real) / ((d : Real) + 1)) *
        parabolicLpNormOn d F (parabolicBox 1 R t0 v0) := by
  let sharedTerm_5fb5133c1f := (R ^ ((d : Real) / ((d : Real) + 1)))


  let Q := parabolicBox 1 R t0 v0

  let D := M - nu / 2
  let w  := fun z ↦ (M - u z) / D
  let Fabs  := fun z ↦ |F z| / D

  have hnuM : nu ≤ M := htop.trans (hM _ (terminalCenter_mem_parabolicClosedBox hR))
  have hD : 0 < D := by
    dsimp [D]
    linarith
  have hQsubset : Q ⊆ (parabolicClosedBox 1 R t0 v0) := _root_.HypoellipticAleksandrov.Parabolic.parabolicBox_subset_closed
  have hFmem  :=
    memLp_of_continuousOn_compact_carrier hF hclosed
      (isCompact_parabolicClosedBox 1 R t0 v0) hQsubset










  have hvolfin : (((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))) (Q ∩ {z | 1 ≤ w z}) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_parabolicClosedBox 1 R t0 v0).measure_ne_top
      (measure_mono (fun _ hz ↦ hQsubset hz.1))


  have hpoint : g ≤ w (((t0 + R ^ 2, v0))) +
      C * sharedTerm_5fb5133c1f * parabolicLpNormOn d Fabs Q := by
    simpa only [one_mul] using hdtp.scaled hR one_pos U B Fabs w hU hclosed hB
      (by
          dsimp only [w]
          exact contDiffOn_const_sub_div hu) (by
          dsimp only [Fabs]
          exact hF.abs.div_const D) (by
          intro z hz
          dsimp [w]
          exact div_nonneg (sub_nonneg.mpr (hM z (hQsubset hz))) hD.le) (by
          intro z _hz
          dsimp [Fabs]
          exact div_nonneg (abs_nonneg (F z)) hD.le) hlower hupper (by
          dsimp only [Fabs, w]
          exact source_supersolution_const_sub_div hD (heq)) (hdensity.trans (volume_toReal_mono_of_subset hvolfin (by
              intro z hz
              refine ⟨hz.1, ?_⟩
              change 1 ≤ (M - u z) / D
              apply (le_div_iff₀ hD).mpr
              dsimp [D]
              have huz : u z ≤ nu / 2 := hz.2
              linarith)))
      v0 (center_mem_velocityClosedCube hR)
  have hnorm : parabolicLpNormOn d Fabs Q = D⁻¹ * parabolicLpNormOn d F Q := by
    dsimp only [Fabs]
    exact parabolicLpNormOn_abs_div hD hFmem
  rw [hnorm] at hpoint


  have hmul : g * D ≤ M - nu + C * sharedTerm_5fb5133c1f *
      parabolicLpNormOn d F Q := by
    calc
      g * D ≤ ((M - nu) / D + C * sharedTerm_5fb5133c1f *
          (D⁻¹ * parabolicLpNormOn d F Q)) * D :=
        mul_le_mul_of_nonneg_right (hpoint.trans (add_le_add_left (by
            dsimp only [w]
            apply (div_le_div_iff_of_pos_right hD).mpr
            linarith) _)) hD.le
      _ = M - nu + C * sharedTerm_5fb5133c1f *
          parabolicLpNormOn d F Q := by
        field_simp [hD.ne']


  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by
      nlinarith)).mpr
  calc
    nu * (2 - g) ≤ 2 * M * (1 - g) +
        2 * C * sharedTerm_5fb5133c1f * parabolicLpNormOn d F Q := by
      dsimp [D] at hmul
      nlinarith
    _ = (M + (C / (1 - g)) * sharedTerm_5fb5133c1f *
        parabolicLpNormOn d F Q) * (2 * (1 - g)) := by
      field_simp [(ne_of_gt (sub_pos.mpr hg))]

end

end HypoellipticAleksandrov.Parabolic
