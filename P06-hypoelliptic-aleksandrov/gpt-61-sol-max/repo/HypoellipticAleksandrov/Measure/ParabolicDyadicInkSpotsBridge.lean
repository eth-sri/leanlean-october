module

public import HypoellipticAleksandrov.Measure.ParabolicDyadicAddress
public import HypoellipticAleksandrov.Measure.ParabolicDensity
public import HypoellipticAleksandrov.Measure.InkSpotsGeometry

/-!
# Dyadic source boxes for parabolic ink spots

This module identifies each open parabolic dyadic cell with a concrete
ink-spots source box.  It also records the ambient/subtype measure bridges
needed to pass the dyadic density theorem to the source family.
-/

@[expose] public section

open Filter MeasureTheory Set


namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- The source box whose open interior is an addressed parabolic dyadic cell.
Its radius is the positive real expression `2⁻¹ ^ n`, its base time is the
lower endpoint of the time cell, and its centre is the coordinate midpoint. -/
def parabolicDyadicSourceBox {d n : Nat}
    (index : ParabolicDyadicIndex d n) : InkSpotsBox d where
  radius := ((2 : ℝ) ^ n)⁻¹
  baseTime := (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n
  center := fun coordinate =>
    -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹

variable {d n : Nat}

variable (index : ParabolicDyadicIndex d n)

private theorem parabolicDyadicSourceBox_radius_sq
     :
    (parabolicDyadicSourceBox index).radius ^ 2 = ((4 : ℝ) ^ n)⁻¹ := by
  change ((2 : ℝ) ^ n)⁻¹ ^ 2 = ((4 : ℝ) ^ n)⁻¹
  rw [inv_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

private theorem parabolicDyadicSourceBox_time_upper
     :
    (parabolicDyadicSourceBox index).baseTime +
        (parabolicDyadicSourceBox index).radius ^ 2 =
      (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n := by
  rw [parabolicDyadicSourceBox_radius_sq]
  change (parabolicDyadicTimeCode n index : ℝ) / (4 : ℝ) ^ n +
      ((4 : ℝ) ^ n)⁻¹ = _
  field_simp

variable (coordinate : Fin d)

private theorem parabolicDyadicSourceBox_center_sub_radius
      :
    (parabolicDyadicSourceBox index).center coordinate -
        (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
        (2 : ℝ) ^ n := by
  change -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹ - ((2 : ℝ) ^ n)⁻¹ = _
  ring

private theorem parabolicDyadicSourceBox_center_add_radius
      :
    (parabolicDyadicSourceBox index).center coordinate +
        (parabolicDyadicSourceBox index).radius =
      -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
        (2 : ℝ) ^ n := by
  change -1 + 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
      (2 : ℝ) ^ n + ((2 : ℝ) ^ n)⁻¹ + ((2 : ℝ) ^ n)⁻¹ = _
  field_simp
  ring

/-- The source open box is exactly the addressed open dyadic cell. -/
theorem inkSpotsSourceBox_parabolicDyadicSourceBox
     :
    inkSpotsSourceBox (parabolicDyadicSourceBox index) = parabolicDyadicOpenCell index := by
  ext z
  rcases z with ⟨time, velocity⟩
  rw [mem_inkSpotsSourceBox_iff, mem_parabolicDyadicOpenCell_iff,
    mem_velocityCube_iff]
  rw [parabolicDyadicSourceBox_time_upper]
  constructor
  · rintro ⟨htlower, htupper, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    have hcoordinate := hvelocity coordinate
    rw [abs_lt] at hcoordinate


    constructor
    · nlinarith [hcoordinate.1, (parabolicDyadicSourceBox_center_sub_radius index coordinate)]
    · nlinarith [hcoordinate.2, (parabolicDyadicSourceBox_center_add_radius index coordinate)]
  · rintro ⟨htlower, htupper, hvelocity⟩
    refine ⟨htlower, htupper, fun coordinate => ?_⟩
    rw [abs_lt]
    have hcoordinate := hvelocity coordinate


    constructor
    · nlinarith [hcoordinate.1, (parabolicDyadicSourceBox_center_sub_radius index coordinate)]
    · nlinarith [hcoordinate.2, (parabolicDyadicSourceBox_center_add_radius index coordinate)]

/-- Every dyadic source box has positive radius. -/
theorem parabolicDyadicSourceBox_radius_pos
     :
    0 < (parabolicDyadicSourceBox index).radius := by
  change 0 < ((2 : ℝ) ^ n)⁻¹
  positivity

private theorem parabolicDyadicOpenCell_subset_unit
     :
    parabolicDyadicOpenCell index ⊆ inkSpotsUnitBox d := by
  rintro ⟨time, velocity⟩ hcell
  rw [mem_parabolicDyadicOpenCell_iff] at hcell
  rw [inkSpotsUnitBox, mem_parabolicBox_iff]
  have hfour : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _


  refine ⟨?_, ?_, ?_⟩
  · have : 0 ≤ (parabolicDyadicTimeCode n index : ℝ) := by positivity
    nlinarith [div_nonneg this hfour.le]
  · have hupper :
        (parabolicDyadicTimeCode n index + 1 : ℝ) / (4 : ℝ) ^ n ≤ 1 := by
      have hcodeNat  :=
        Nat.succ_le_iff.mpr (parabolicDyadicTimeCode_lt_pow index)

      exact (div_le_one hfour).mpr (by exact_mod_cast hcodeNat)
    nlinarith
  · intro coordinate

    simp only [Pi.zero_apply, sub_zero]
    have hlower : -1 < velocity coordinate := by
      have : -1 ≤ -1 + 2 *
          (parabolicDyadicVelocityCode n index coordinate : ℝ) / (2 : ℝ) ^ n := by
        have : 0 ≤ 2 * (parabolicDyadicVelocityCode n index coordinate : ℝ) /
            (2 : ℝ) ^ n := by positivity
        linarith
      exact lt_of_le_of_lt this (hcell.2.2 coordinate).1
    have hupper : velocity coordinate < 1 := by


      exact lt_of_lt_of_le (hcell.2.2 coordinate).2 (by
          have hfrac  := (div_le_one (show 0 < (2 : ℝ) ^ n from pow_pos (by norm_num) _)).mpr (show (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) ≤
          (2 : ℝ) ^ n by

              exact_mod_cast (Nat.succ_le_iff.mpr (parabolicDyadicVelocityCode_lt_pow index coordinate)))
          calc
            -1 + 2 * (parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
                (2 : ℝ) ^ n =
                -1 + 2 * ((parabolicDyadicVelocityCode n index coordinate + 1 : ℝ) /
                  (2 : ℝ) ^ n) := by ring
            _ ≤ 1 := by linarith)
    exact abs_lt.mpr (by constructor <;> linarith)

/-- The source box of an addressed cell lies in the open unit source box. -/
theorem inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit
     :
    inkSpotsSourceBox (parabolicDyadicSourceBox index) ⊆ inkSpotsUnitBox d := by
  rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
  exact parabolicDyadicOpenCell_subset_unit index

/-- The first enlargement of a child source box contains the entire open
parent cell.  The time computation uses the four child digits and the
velocity computation uses the two digits in each coordinate. -/
theorem parabolicDyadicOpenCell_parent_subset_inkSpotsQ1
    (index : ParabolicDyadicIndex d (n + 1)) :
    parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆
      inkSpotsQ1 (parabolicDyadicSourceBox index) := by
  let sharedTerm_ca64e06b1a := (3 * (parabolicDyadicSourceBox index).radius)
  rintro ⟨time, velocity⟩ hz
  rw [mem_parabolicDyadicOpenCell_iff] at hz
  rw [mem_inkSpotsQ1_iff]
  have htimeCode : parabolicDyadicTimeCode (n + 1) index =
      4 * parabolicDyadicTimeCode n (parabolicDyadicParent index) +
        (index (Fin.last n)).1.val := by
    rfl
  have htimeBase : (parabolicDyadicSourceBox index).baseTime =
      (parabolicDyadicTimeCode n (parabolicDyadicParent index) : ℝ) / (4 : ℝ) ^ n +
        (index (Fin.last n)).1.val * (((4 : ℝ) ^ n)⁻¹ / 4) := by
    change (parabolicDyadicTimeCode (n + 1) index : ℝ) / (4 : ℝ) ^ (n + 1) = _
    rw [htimeCode]
    push_cast
    rw [pow_succ]
    field_simp
  have hradiusSq : (parabolicDyadicSourceBox index).radius ^ 2 =
      ((4 : ℝ) ^ n)⁻¹ / 4 := by
    rw [parabolicDyadicSourceBox_radius_sq]
    rw [pow_succ]
    field_simp

  have htimeDigitUpper  := Nat.le_pred_of_lt (index (Fin.last n)).1.isLt
  have hfour : 0 < (4 : ℝ) ^ n := pow_pos (by norm_num) _
  have hinv  := inv_pos.mpr hfour
  have hzUnit  :=
    parabolicDyadicOpenCell_subset_unit _
      (mem_parabolicDyadicOpenCell_iff.mpr hz)
  refine ⟨?_, ?_, ?_, hzUnit⟩
  ·
    exact lt_of_le_of_lt (show (parabolicDyadicSourceBox index).baseTime -
            3 * (parabolicDyadicSourceBox index).radius ^ 2 ≤
          (parabolicDyadicTimeCode n (parabolicDyadicParent index) : ℝ) /
            (4 : ℝ) ^ n by
        rw [htimeBase, hradiusSq]
        simp only [div_eq_mul_inv]
        have hdigit : ((index (Fin.last n)).1.val : ℝ) ≤ 3 := by
          exact_mod_cast htimeDigitUpper
        have hmul := mul_le_mul_of_nonneg_right hdigit hinv.le
        nlinarith) hz.1
  ·
    exact lt_of_lt_of_le hz.2.1 (show (parabolicDyadicTimeCode n (parabolicDyadicParent index) + 1 : ℝ) /
            (4 : ℝ) ^ n ≤
          (parabolicDyadicSourceBox index).baseTime -
              3 * (parabolicDyadicSourceBox index).radius ^ 2 +
            (7 / 9 : ℝ) * (sharedTerm_ca64e06b1a) ^ 2 by
        rw [htimeBase]
        simp only [div_eq_mul_inv]
        have hdigit : 0 ≤ ((index (Fin.last n)).1.val : ℝ) := by positivity
        have hmul  :=
          mul_nonneg hdigit hinv.le
        have hradiusSq' := hradiusSq
        simp only [div_eq_mul_inv] at hradiusSq'
        nlinarith [hradiusSq'])
  · rw [mem_velocityCube_iff]
    intro coordinate
    have hvelocityCode : parabolicDyadicVelocityCode (n + 1) index coordinate =
        2 * parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate +
          ((index (Fin.last n)).2 coordinate).val := by
      rfl
    have hcenterLower : (parabolicDyadicSourceBox index).center coordinate -
        sharedTerm_ca64e06b1a =
      -1 + 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
          (2 : ℝ) ^ n +
        (((index (Fin.last n)).2 coordinate).val - 1) / (2 : ℝ) ^ n := by
      change -1 + 2 * (parabolicDyadicVelocityCode (n + 1) index coordinate : ℝ) /
          (2 : ℝ) ^ (n + 1) + ((2 : ℝ) ^ (n + 1))⁻¹ -
          3 * ((2 : ℝ) ^ (n + 1))⁻¹ = _
      rw [hvelocityCode]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    have hcenterUpper : (parabolicDyadicSourceBox index).center coordinate +
        sharedTerm_ca64e06b1a =
      -1 + 2 * (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
          (2 : ℝ) ^ n +
        (((index (Fin.last n)).2 coordinate).val + 2) / (2 : ℝ) ^ n := by
      change -1 + 2 * (parabolicDyadicVelocityCode (n + 1) index coordinate : ℝ) /
          (2 : ℝ) ^ (n + 1) + ((2 : ℝ) ^ (n + 1))⁻¹ +
          3 * ((2 : ℝ) ^ (n + 1))⁻¹ = _
      rw [hvelocityCode]
      push_cast
      rw [pow_succ]
      field_simp
      ring
    rw [abs_lt]

    have hvelocityDigitUpper  := Nat.le_pred_of_lt ((index (Fin.last n)).2 coordinate).isLt
    have hdenom : 0 < (2 : ℝ) ^ n := pow_pos (by norm_num) _

    have hparent := hz.2.2 coordinate
    have hlower :
        (parabolicDyadicSourceBox index).center coordinate -
            sharedTerm_ca64e06b1a ≤
          -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
              (2 : ℝ) ^ n := by
      rw [hcenterLower]

      have hdelta := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (show (((index (Fin.last n)).2 coordinate).val : ℝ) ≤ 1 by
          exact_mod_cast hvelocityDigitUpper)) hdenom.le
      linarith
    have hupper :
        -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1 : ℝ) /
              (2 : ℝ) ^ n ≤
          (parabolicDyadicSourceBox index).center coordinate +
            sharedTerm_ca64e06b1a := by

      have hfrac : 2 / (2 : ℝ) ^ n ≤
          ((((index (Fin.last n)).2 coordinate).val : ℝ) + 2) / (2 : ℝ) ^ n :=
        (div_le_div_iff_of_pos_right hdenom).mpr (by linarith)
      calc
        -1 + 2 *
            (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate + 1 : ℝ) /
              (2 : ℝ) ^ n =
            -1 + 2 *
                (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
                  (2 : ℝ) ^ n + 2 / (2 : ℝ) ^ n := by ring
        _ ≤ -1 + 2 *
                (parabolicDyadicVelocityCode n (parabolicDyadicParent index) coordinate : ℝ) /
                  (2 : ℝ) ^ n +
              ((((index (Fin.last n)).2 coordinate).val : ℝ) + 2) / (2 : ℝ) ^ n := by
            linarith
        _ = (parabolicDyadicSourceBox index).center coordinate +
              sharedTerm_ca64e06b1a := hcenterUpper.symm
    constructor
    · nlinarith [hparent.1, hlower]
    · nlinarith [hparent.2, hupper]

/-- Subtype reference measure of an ambient measurable preimage is ambient
volume intersected with the reference cell. -/
theorem parabolicDyadicReferenceMeasure_preimage_eq_volume_inter_reference
    (d : Nat) (s : HypoellipticAleksandrov.Parabolic.Region d) (_hs : MeasurableSet s) :
    parabolicDyadicReferenceMeasure d (Subtype.val ⁻¹' s) =
      volume (s ∩ parabolicDyadicReferenceCell d) := by
  rw [parabolicDyadicReferenceMeasure, comap_subtype_coe_apply
    (measurableSet_parabolicDyadicReferenceCell d)]
  change volume (Subtype.val '' (Subtype.val ⁻¹' s)) = _
  rw [Subtype.image_preimage_coe, inter_comm]

/-- On a set inside the reference cell, subtype reference measure is ambient volume. -/
theorem parabolicDyadicReferenceMeasure_preimage_eq_volume {d : Nat}
    (s : HypoellipticAleksandrov.Parabolic.Region d) (hs : MeasurableSet s)
    (hsub : s ⊆ parabolicDyadicReferenceCell d) :
    parabolicDyadicReferenceMeasure d (Subtype.val ⁻¹' s) = volume s := by
  rw [parabolicDyadicReferenceMeasure_preimage_eq_volume_inter_reference d s hs,
    inter_eq_left.mpr hsub]

variable (d : Nat)

private def parabolicDyadicAllBoundary  : HypoellipticAleksandrov.Parabolic.Region d :=
  ⋃ address : ParabolicDyadicAddress d,
    parabolicDyadicHalfOpenCell address.2 \ parabolicDyadicOpenCell address.2

private theorem volume_parabolicDyadicAllBoundary_eq_zero  :
    volume (parabolicDyadicAllBoundary d) = 0 := by
  apply measure_iUnion_null
  intro address
  apply ae_le_set.mp
  exact (parabolicDyadicOpenCell_ae_eq_halfOpenCell address.2).symm.le

private theorem ae_not_mem_parabolicDyadicAllBoundary  :
    ∀ᵐ z, z ∉ parabolicDyadicAllBoundary d := by
  rw [ae_iff]
  simpa only [Set.setOf_mem_eq, not_not] using
    volume_parabolicDyadicAllBoundary_eq_zero d

variable {d n : Nat} (Gamma : HypoellipticAleksandrov.Parabolic.Region d)

/-- A strict dyadic density on a restricted half-open cell gives a strict
ink-spots density for its actual open source box. -/
theorem inkSpotsStrictDense_of_restrictedCell_density_gt  (hGamma : MeasurableSet Gamma) (xi : Real)
    (index : ParabolicDyadicIndex d n)
    (h : xi * (parabolicDyadicReferenceMeasure d).real
        (parabolicDyadicRestrictedCell index) <
      (parabolicDyadicReferenceMeasure d).real
        (parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma)) :
    inkSpotsStrictDense Gamma xi (parabolicDyadicSourceBox index) := by
  have hrestrictedInter :
      parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma =
        Subtype.val ⁻¹' (parabolicDyadicHalfOpenCell index ∩ Gamma) := by
    ext z
    rfl

  have hcellAE  :=
    parabolicDyadicOpenCell_ae_eq_halfOpenCell index
  have hinterAE : (parabolicDyadicOpenCell index ∩ Gamma ) =ᵐ[volume]
      (parabolicDyadicHalfOpenCell index ∩ Gamma ) :=
    ae_eq_set_inter hcellAE (EventuallyEq.rfl)
  have hvolume  := measure_congr hcellAE

  refine ⟨parabolicDyadicSourceBox_radius_pos index,
    inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit index, ?_⟩
  rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
  calc
    xi * (volume (parabolicDyadicOpenCell index)).toReal =
        xi * (volume (parabolicDyadicHalfOpenCell index)).toReal := by rw [hvolume]
    _ < (volume (parabolicDyadicHalfOpenCell index ∩ Gamma)).toReal := (show _ by
        simpa only [Measure.real, hrestrictedInter,
          parabolicDyadicReferenceMeasure_restrictedCell,
          parabolicDyadicReferenceMeasure_preimage_eq_volume
            _ ((measurableSet_parabolicDyadicHalfOpenCell index).inter hGamma)
            (inter_subset_left.trans (parabolicDyadicHalfOpenCell_subset_reference index))] using h)
    _ = (volume (parabolicDyadicOpenCell index ∩ Gamma)).toReal := by rw [(measure_congr hinterAE)]

/-- A strict ambient density on a child open dyadic cell puts its parent open
cell in the actual first ink-spots enlargement union. -/
theorem parabolicDyadicOpenCell_parent_subset_inkSpotsD1_of_density_gt
     (xi : Real)
    (index : ParabolicDyadicIndex d (n + 1))
    (h : xi * (volume (parabolicDyadicOpenCell index)).toReal <
      (volume (Gamma ∩ parabolicDyadicOpenCell index)).toReal) :
    parabolicDyadicOpenCell (parabolicDyadicParent index) ⊆ inkSpotsD1 Gamma xi := by

  intro z hz
  refine Set.mem_iUnion.mpr ⟨parabolicDyadicSourceBox index, ?_⟩
  refine Set.mem_iUnion.mpr ⟨(by
      refine ⟨parabolicDyadicSourceBox_radius_pos index,
        inkSpotsSourceBox_parabolicDyadicSourceBox_subset_unit index, ?_⟩
      rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
      simpa only [inter_comm] using h), ?_⟩
  exact parabolicDyadicOpenCell_parent_subset_inkSpotsQ1 index hz

variable (d : Nat)

private theorem inkSpotsUnitBox_subset_parabolicDyadicReferenceCell  :
    inkSpotsUnitBox d ⊆ parabolicDyadicReferenceCell d := by
  rintro ⟨time, velocity⟩ hz
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hz
  simp only [zero_add, one_mul, one_pow] at hz
  rw [parabolicDyadicReferenceCell]
  refine ⟨⟨hz.1, hz.2.1.le⟩, fun coordinate _ => ?_⟩
  have hcoordinate := hz.2.2 coordinate
  rw [abs_lt, Pi.zero_apply, sub_zero] at hcoordinate
  exact ⟨hcoordinate.1, hcoordinate.2.le⟩

/-- Almost every point of a measurable set in the unit source box belongs to
the first ink-spots enlargement union. -/
theorem ae_le_inkSpotsD1_of_parabolicDyadicDensity
     (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi : Real)
    (hGamma : MeasurableSet Gamma) (hGammaUnit : Gamma ⊆ inkSpotsUnitBox d)
    (hxi : xi ∈ Set.Ioo (0 : Real) 1) :
    Gamma ≤ᵐ[volume] inkSpotsD1 Gamma xi := by



  have hsubtype := ae_exists_parabolicDyadicRestrictedCell_density_gt
    d (Subtype.val ⁻¹' Gamma) (hGamma.preimage continuous_subtype_val.measurable) xi hxi


  filter_upwards [((ae_restrict_iff' (measurableSet_parabolicDyadicReferenceCell d)).mp (show ∀ᵐ z ∂volume.restrict (parabolicDyadicReferenceCell d),
      z ∈ Gamma → ∃ n, ∃ index : ParabolicDyadicIndex d n,
        z ∈ parabolicDyadicHalfOpenCell index ∧
          xi * (parabolicDyadicReferenceMeasure d).real
              (parabolicDyadicRestrictedCell index) <
            (parabolicDyadicReferenceMeasure d).real
              (parabolicDyadicRestrictedCell index ∩ Subtype.val ⁻¹' Gamma) by
      rw [ae_restrict_iff_subtype (measurableSet_parabolicDyadicReferenceCell d)]
      exact hsubtype)), ae_not_mem_parabolicDyadicAllBoundary d] with z hz hzBoundary
  intro hzGamma
  obtain ⟨n, index, hzHalf, hdensity⟩ := hz ((hGammaUnit.trans (inkSpotsUnitBox_subset_parabolicDyadicReferenceCell d)) hzGamma) hzGamma

  have hstrict := inkSpotsStrictDense_of_restrictedCell_density_gt
    Gamma hGamma xi index hdensity

  have hzQ1 := inkSpotsSourceBox_subset_Q1_of_strictDense hstrict (by
      rw [inkSpotsSourceBox_parabolicDyadicSourceBox]
      exact (by
          by_contra hzOpen
          apply hzBoundary
          refine Set.mem_iUnion.mpr ⟨⟨n, index⟩, ?_⟩
          exact ⟨hzHalf, hzOpen⟩))
  exact Set.mem_iUnion.mpr ⟨_,
    Set.mem_iUnion.mpr ⟨hstrict, hzQ1⟩⟩

end

end HypoellipticAleksandrov.Parabolic
