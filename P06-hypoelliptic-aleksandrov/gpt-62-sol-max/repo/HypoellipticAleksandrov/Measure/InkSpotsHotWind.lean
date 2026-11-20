module

public import HypoellipticAleksandrov.Measure.InkSpotsWind
public import HypoellipticAleksandrov.Measure.ClippedCoordinateUnion
public import HypoellipticAleksandrov.Measure.VaryingCenterIntervalUnion

/-!
# Hot-wind scaffold for source ink spots

This module proves Lemma 2.4 of Krylov--Safonov, Section 2, by a
time contraction followed by one varying-centre/Fubini contraction for each
velocity coordinate.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
  (hq : inkSpotsStrictDense Gamma xi q)
include Gamma xi hq

private theorem strictDense_center_mem_unit_velocityCube :
    q.center ∈ velocityCube (0 : PDE.Vec d) 1 := by
  have hr : 0 < q.radius := hq.1
  let t : ℝ := q.baseTime + q.radius ^ 2 / 2
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    rw [mem_inkSpotsSourceBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [t]
      nlinarith [sq_pos_of_pos hr]
    · dsimp [t]
      nlinarith [sq_pos_of_pos hr]
    · intro i
      simp only [sub_self, abs_zero]
      exact hr
  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  exact htUnit.2.2

private theorem strictDense_center_coord_bounds (j : Fin d) :
    -1 < q.center j ∧ q.center j < 1 := by
  simpa only [Pi.zero_apply, sub_zero] using
    abs_lt.mp (strictDense_center_mem_unit_velocityCube hq j)

end

section
variable {d : ℕ}

/-- The source terminal contraction restricted to its time coordinate. -/
private def inkSpotsTimeContraction (eta zeta : ℝ) (q : InkSpotsBox d) :
    ℝ → ℝ :=
  fun t => inkSpotsTerminalTime eta q - zeta ^ 2 *
    (inkSpotsTerminalTime eta q - t)

/-- The first, time-only stage of the terminal contraction. -/
private def inkSpotsQ2TimeContracted (eta zeta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

private theorem inkSpotsTimeContraction_forwardInterval {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q =
      Ioo (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))
        (inkSpotsTerminalTime eta q) := by
  unfold inkSpotsTimeContraction windForwardInterval
  let T := inkSpotsTerminalTime eta q
  have hsq : 0 < zeta ^ 2 := sq_pos_of_pos hzeta
  convert image_affine_Ioo hsq ((1 - zeta ^ 2) * T)
    (q.baseTime + q.radius ^ 2) T using 1 <;> ext <;> dsimp [T] <;> ring_nf

private def inkSpotsD2TimeContractedUnion (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) : Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2TimeContracted eta zeta q

private theorem contractedTime_subset_forward {eta zeta : ℝ} {q : InkSpotsBox d}
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q ⊆ windForwardInterval eta q := by
  rintro t ⟨x, hx, rfl⟩
  have hx' : q.baseTime + q.radius ^ 2 < x ∧ x < inkSpotsTerminalTime eta q := hx
  have hζ : zeta ^ 2 ≤ 1 := by nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
  change _ < inkSpotsTimeContraction eta zeta q x ∧ _ < _
  unfold inkSpotsTimeContraction
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hζ) (sub_nonneg.mpr hx'.2.le),
    mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr hx'.2)]

end

section
variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (v : PDE.Vec d)
include d Gamma xi eta zeta v

private def hotTimeSectionFamily : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q}

private theorem timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily :
    timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v =
      ⋃₀ (hotTimeSectionFamily Gamma xi eta zeta v) := by
  ext t
  constructor
  · intro ht
    rw [timeSection, inkSpotsD2TimeContractedUnion] at ht
    rcases mem_iUnion.1 ht with ⟨q, ht⟩
    rcases mem_iUnion.1 ht with ⟨hq, ht⟩
    refine mem_sUnion.2 ⟨inkSpotsTimeContraction eta zeta q ''
      windForwardInterval eta q, ?_, ht.1⟩
    exact ⟨q, hq, ht.2.1, ht.2.2, rfl⟩
  · intro ht
    rcases mem_sUnion.1 ht with ⟨I, hI, ht⟩
    rcases hI with ⟨q, hq, hvCenter, hvUnit, rfl⟩
    rw [timeSection, inkSpotsD2TimeContractedUnion]
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, ⟨ht, hvCenter, hvUnit⟩⟩⟩

end

section
variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi eta zeta : ℝ} {q : InkSpotsBox d}
  (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (hq : inkSpotsStrictDense Gamma xi q)
include Gamma xi heta hzeta0 hzeta1 hq

private theorem hotTimeInterval_eligible :
    IsOpenSubinterval (windAmbientTime eta)
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) := by
  have hf := windForwardInterval_eligible heta hq
  refine ⟨hf.1.image _, ?_, ?_, (contractedTime_subset_forward hzeta0 hzeta1).trans hf.2.2.2⟩ <;>
    rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  · exact isOpen_Ioo
  · exact ordConnected_Ioo

private theorem hotTimeExpansion_contractedInterval :
    rightEndpointExpansion 0 (zeta ^ 2)⁻¹
        (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) =
      windForwardInterval eta q := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  have hs : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q :=
    nonempty_Ioo.mp (windForwardInterval_eligible heta hq).1
  have hgap := mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr hs)
  have hi : inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)) < inkSpotsTerminalTime eta q := by linarith
  unfold rightEndpointExpansion windForwardInterval
  rw [csInf_Ioo hi, csSup_Ioo hi, show inkSpotsTerminalTime eta q - (zeta ^ 2)⁻¹ *
      (inkSpotsTerminalTime eta q - (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))) = q.baseTime + q.radius ^ 2 by
      field_simp [hzeta0.ne']; ring]
  rw [max_eq_right (add_nonneg (strictDense_baseTime_nonneg hq) (sq_nonneg _))]

end

section
variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (heta : 0 < eta)
  (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d)
include heta hzeta0 hzeta1

private theorem timeSection_inkSpotsD2_subset_expanded_hotTimeSections :
    timeSection (inkSpotsD2 Gamma xi eta) v ⊆
      ⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
        hotTimeSectionFamily Gamma xi eta zeta v) := by
  intro t ht
  rw [timeSection, inkSpotsD2] at ht
  rcases mem_iUnion.1 ht with ⟨q, ht⟩
  rcases mem_iUnion.1 ht with ⟨hq, ht⟩
  rw [mem_inkSpotsQ2_iff] at ht
  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 (zeta ^ 2)⁻¹
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q), ?_,
      ?_⟩
  exact ⟨inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q,
    ⟨q, hq, ht.2.2.1, ht.2.2.2, rfl⟩, rfl⟩
  rw [hotTimeExpansion_contractedInterval heta hzeta0 hzeta1 hq]
  exact ⟨ht.1, ht.2.1⟩

private theorem sUnion_hotTimeSectionFamily_bounded :
    Bornology.IsBounded (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (hotTimeInterval_eligible heta hzeta0 hzeta1 hq).2.2.2

private theorem volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted :
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
  have hsq0 := sq_pos_of_pos hzeta0
  have hsq1 : zeta ^ 2 < 1 := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
  calc
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
        volume (⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
          hotTimeSectionFamily Gamma xi eta zeta v)) :=
      measure_mono (timeSection_inkSpotsD2_subset_expanded_hotTimeSections
        Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ ≤ ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) :=
      volume_sUnion_rightEndpointExpansion ((one_lt_inv₀ hsq0).2 hsq1) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact hotTimeInterval_eligible heta hzeta0 hzeta1 hq)
        (sUnion_hotTimeSectionFamily_bounded Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
      rw [timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily]

end

private theorem isOpen_inkSpotsQ2TimeContracted {d : ℕ} {eta zeta : ℝ}
    (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2TimeContracted eta zeta q) := by
  rw [inkSpotsQ2TimeContracted, inkSpotsTimeContraction_forwardInterval hzeta0]
  exact isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

section
variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ)

private theorem isOpen_inkSpotsD2TimeContractedUnion (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [inkSpotsD2TimeContractedUnion]
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2TimeContracted q hzeta0

private theorem volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    volume (inkSpotsD2 Gamma xi eta) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta),
    volume_eq_lintegral_timeSection _
      (isOpen_inkSpotsD2TimeContractedUnion Gamma xi eta zeta hzeta0).measurableSet]
  calc
    (∫⁻ v, volume (timeSection (inkSpotsD2 Gamma xi eta) v)) ≤
        ∫⁻ v, ENNReal.ofReal ((zeta ^ 2)⁻¹) *
          volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) :=
      lintegral_mono fun v =>
        volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
          Gamma xi eta zeta heta hzeta0 hzeta1 v
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        ∫⁻ v, volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end

/-! The remaining contractions are deliberately staged by prefix.  Keeping
the family of boxes under the union at every stage is essential: different
boxes meeting the same section have different velocity centres. -/

section
variable {d : Nat}

private def inkSpotsVelocityPrefixContraction
    (q : InkSpotsBox d) (zeta : Real) (k : Nat) (v : PDE.Vec d) : PDE.Vec d :=
  fun j => if j.1 < k then q.center j + zeta * (v j - q.center j) else v j

private def inkSpotsQ2PrefixContracted
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  {z | ∃ y ∈ inkSpotsQ2 eta q,
    z.1 = inkSpotsTimeContraction eta zeta q y.1 ∧
      z.2 = inkSpotsVelocityPrefixContraction q zeta k y.2}

private def inkSpotsD2PrefixContractedUnion
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2PrefixContracted eta zeta k q

private theorem inkSpotsQ2PrefixContracted_zero_eq_timeContracted
    (eta zeta : Real) (q : InkSpotsBox d) :
    inkSpotsQ2PrefixContracted eta zeta 0 q = inkSpotsQ2TimeContracted eta zeta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    rcases y with ⟨t, v⟩
    rw [mem_inkSpotsQ2_iff] at hy
    have hzv : z.2 = v := by
      funext j
      simpa only [inkSpotsVelocityPrefixContraction, Nat.not_lt_zero, if_false]
        using congrFun hv j
    refine ⟨⟨t, ⟨hy.1, hy.2.1⟩, ht.symm⟩, ?_, ?_⟩
    · rw [hzv]
      exact hy.2.2.1
    · rw [hzv]
      exact hy.2.2.2
  · rintro ⟨htime, hcenter, hunit⟩
    rcases htime with ⟨t, ht, htime⟩
    refine ⟨(t, z.2), ?_, htime.symm, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨ht.1, ht.2, hcenter, hunit⟩
    · funext j
      simp only [inkSpotsVelocityPrefixContraction, Nat.not_lt_zero, if_false]

private theorem inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0 =
      inkSpotsD2TimeContractedUnion Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD2TimeContractedUnion,
    inkSpotsQ2PrefixContracted_zero_eq_timeContracted]

private theorem inkSpotsQ2PrefixContracted_eq_Q3
    (eta zeta : Real) (q : InkSpotsBox d) :
    inkSpotsQ2PrefixContracted eta zeta d q = inkSpotsQ3 eta zeta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    rw [mem_inkSpotsQ3_iff]
    refine ⟨y, hy, ?_⟩
    apply Prod.ext
    · exact ht.symm
    · funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]
  · rw [mem_inkSpotsQ3_iff]
    rintro ⟨y, hy, hcontraction⟩
    refine ⟨y, hy, ?_, ?_⟩
    · simpa only [inkSpotsContraction, inkSpotsTimeContraction] using
        congrArg Prod.fst hcontraction.symm
    · have hv := congrArg Prod.snd hcontraction.symm
      funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]

private theorem inkSpotsD2PrefixContractedUnion_eq_D3
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta d = inkSpotsD3 Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD3,
    inkSpotsQ2PrefixContracted_eq_Q3]

end

section
variable (c zeta : Real) (hzeta : zeta ≠ 0)
include c zeta hzeta

private def inkSpotsAffineHomeomorph :
    Real ≃ₜ Real :=
  (Homeomorph.addLeft (-c)).trans
    ((Homeomorph.smulOfNeZero zeta hzeta).trans (Homeomorph.addLeft c))

private theorem inkSpotsAffineHomeomorph_apply
    (x : Real) :
    inkSpotsAffineHomeomorph c zeta hzeta x = c + zeta * (x - c) := by
  simp [inkSpotsAffineHomeomorph, Homeomorph.addLeft, Homeomorph.smulOfNeZero]
  ring

end

section
variable {d : Nat}

private def inkSpotsVelocitySectionPoint (j : Fin d) (x : Real)
    (w : Fin d → Real) : TimeVelocity d :=
  (timeVelocityCoordinateEquiv d).symm
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
      (Fin.succ j)).symm (x, w))

private theorem mem_timeVelocityCoordinateSection_succ_iff (j : Fin d)
    (S : Set (TimeVelocity d)) (w : Fin d → Real) (x : Real) :
    x ∈ timeVelocityCoordinateSection d (Fin.succ j) S w ↔
      inkSpotsVelocitySectionPoint j x w ∈ S := by
  let e := timeVelocityCoordinateEquiv d
  let ei := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
    (Fin.succ j)
  change ei.symm (x, w) ∈ e '' S ↔ _
  constructor
  · rintro ⟨z, hz, heq⟩
    have hz_eq : z = e.symm (ei.symm (x, w)) := by
      apply e.injective
      simpa using heq
    change e.symm (ei.symm (x, w)) ∈ S
    rw [← hz_eq]
    exact hz
  · intro hz
    refine ⟨e.symm (ei.symm (x, w)), hz, ?_⟩
    exact e.apply_symm_apply _

end

section
variable {d : Nat} (j : Fin d) (x : Real) (w : Fin d → Real)

private theorem timeVelocityCoordinateEquiv_sectionPoint :
    timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
        (Fin.succ j)).symm (x, w) := by
  simp [inkSpotsVelocitySectionPoint]

private theorem sectionPoint_velocity_eq : (inkSpotsVelocitySectionPoint j x w).2 j = x := by
  simp [inkSpotsVelocitySectionPoint, timeVelocityCoordinateEquiv, Fin.tail]

end

private theorem sectionPoint_velocity_eq_of_ne {d : Nat} (j l : Fin d) (x y : Real)
    (w : Fin d → Real) (h : l ≠ j) :
    (inkSpotsVelocitySectionPoint j x w).2 l =
      (inkSpotsVelocitySectionPoint j y w).2 l := by
  change (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w))
      (Fin.succ l) =
    (timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j y w))
      (Fin.succ l)
  rw [timeVelocityCoordinateEquiv_sectionPoint,
    timeVelocityCoordinateEquiv_sectionPoint]
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk]
  obtain ⟨u, hu⟩ := Fin.exists_succAbove_eq
    (show Fin.succ l ≠ Fin.succ j by simpa)
  rw [← hu, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove]

private theorem sectionPoint_time_eq {d : Nat} (j : Fin d) (x y : Real)
    (w : Fin d → Real) :
    (inkSpotsVelocitySectionPoint j x w).1 =
      (inkSpotsVelocitySectionPoint j y w).1 := by
  solve_by_elim

private def inkSpotsHotCoordinateInterval {d : Nat} (q : InkSpotsBox d)
    (j : Fin d) : Set Real :=
  Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1

private theorem inkSpotsHotCoordinateInterval_eligible {d : Nat}
    {Gamma : Set (TimeVelocity d)} {xi : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (j : Fin d) :
    IsOpenSubinterval (Ioo (-1 : Real) 1) (inkSpotsHotCoordinateInterval q j) := by
  have hc := strictDense_center_coord_bounds hq j
  have hr : 0 < q.radius := hq.1
  refine ⟨⟨q.center j, ⟨?_, hc⟩⟩, isOpen_Ioo.inter isOpen_Ioo,
    ordConnected_Ioo.inter ordConnected_Ioo, inter_subset_right⟩
  constructor <;> nlinarith

section
variable {d : ℕ} (q : InkSpotsBox d)
include q

private def prefixVelocityInterval (zeta : ℝ) (k : ℕ) (l : Fin d) :
    Set ℝ := if l.1 < k then centeredCoordinateContraction (q.center l) zeta ''
      inkSpotsHotCoordinateInterval q l else inkSpotsHotCoordinateInterval q l

private theorem mem_hotCoordinateInterval_iff (l : Fin d) (x : ℝ) :
    x ∈ inkSpotsHotCoordinateInterval q l ↔ |x - q.center l| < 3 * q.radius ∧ |x| < 1 := by
  simp only [inkSpotsHotCoordinateInterval, mem_inter_iff, mem_Ioo, abs_lt]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact ⟨⟨by linarith, by linarith⟩, h₃⟩

private theorem prefixVelocityInterval_image (zeta : ℝ)
    (k : ℕ) (l : Fin d) :
    prefixVelocityInterval q zeta k l =
      (fun x => if l.1 < k then centeredCoordinateContraction (q.center l) zeta x else x) ''
        inkSpotsHotCoordinateInterval q l := by
  by_cases hl : l.1 < k <;> simp [prefixVelocityInterval, hl]

end

section
variable {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) (k : ℕ)
include eta zeta q k

private theorem mem_prefixContracted_iff
    (z : TimeVelocity d) : z ∈ inkSpotsQ2PrefixContracted eta zeta k q ↔
      z.1 ∈ inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q ∧
        ∀ l, z.2 l ∈ prefixVelocityInterval q zeta k l := by
  simp only [prefixVelocityInterval_image]
  constructor
  · rintro ⟨⟨t, v⟩, hy, ht, hv⟩
    rw [mem_inkSpotsQ2_iff] at hy
    refine ⟨⟨t, ⟨hy.1, hy.2.1⟩, ht.symm⟩, fun l => ⟨v l, ?_, ?_⟩⟩
    · exact (mem_hotCoordinateInterval_iff q l _).2
        ⟨hy.2.2.1 l, by simpa only [Pi.zero_apply, sub_zero] using hy.2.2.2 l⟩
    · exact (congrFun hv l).symm
  · rintro ⟨⟨t, ht, htz⟩, hv⟩
    choose v hv hz using hv
    refine ⟨(t, v), mem_inkSpotsQ2_iff.mpr ⟨ht.1, ht.2, ?_, ?_⟩, htz.symm, ?_⟩
    · exact fun l => ((mem_hotCoordinateInterval_iff q l _).1 (hv l)).1
    · intro l
      simpa only [Pi.zero_apply, sub_zero] using ((mem_hotCoordinateInterval_iff q l _).1 (hv l)).2
    · exact funext fun l => (hz l).symm

private theorem isOpen_inkSpotsQ2PrefixContracted (hzeta : 0 < zeta) :
    IsOpen (inkSpotsQ2PrefixContracted eta zeta k q) := by
  have he : inkSpotsQ2PrefixContracted eta zeta k q =
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) ×ˢ
        Set.pi univ (prefixVelocityInterval q zeta k) := by
    ext z
    simp only [mem_prefixContracted_iff, mem_prod, mem_pi, mem_univ, true_implies]
  rw [he, inkSpotsTimeContraction_forwardInterval hzeta]
  refine isOpen_Ioo.prod (isOpen_set_pi finite_univ fun l _ => ?_)
  have ho : IsOpen (inkSpotsHotCoordinateInterval q l) := isOpen_Ioo.inter isOpen_Ioo
  unfold prefixVelocityInterval
  split
  · change IsOpen ((fun a : ℝ => q.center l + zeta * (a - q.center l)) '' _)
    simpa only [inkSpotsAffineHomeomorph_apply] using
      (inkSpotsAffineHomeomorph (q.center l) zeta hzeta.ne').isOpenMap _ ho
  · exact ho

section
variable (j : Fin d) (w : Fin d → ℝ)
include j w

private def hotSectionFiber : Prop :=
  let b := inkSpotsVelocitySectionPoint j 0 w
  b.1 ∈ inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q ∧
    ∀ l ≠ j, b.2 l ∈ prefixVelocityInterval q zeta k l

private theorem mem_prefixVelocitySection (x : ℝ) :
    x ∈ timeVelocityCoordinateSection d (Fin.succ j) (inkSpotsQ2PrefixContracted eta zeta k q) w ↔
      x ∈ prefixVelocityInterval q zeta k j ∧ hotSectionFiber eta zeta q k j w := by
  rw [mem_timeVelocityCoordinateSection_succ_iff, mem_prefixContracted_iff,
    sectionPoint_time_eq j x 0 w]
  constructor
  · rintro ⟨ht, hv⟩
    exact ⟨by simpa only [sectionPoint_velocity_eq] using hv j, ht, fun l hl => by
      simpa only [sectionPoint_velocity_eq_of_ne _ _ x 0 w hl] using hv l⟩
  · rintro ⟨hx, ht, hv⟩
    refine ⟨ht, fun l => ?_⟩
    by_cases hl : l = j
    · subst l
      simpa only [sectionPoint_velocity_eq] using hx
    · rw [sectionPoint_velocity_eq_of_ne _ _ x 0 w hl]
      exact hv l hl

end

end

private theorem section_prefix_eq_hotInterval_of_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
    (hnonempty : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta j.1 q) w =
      inkSpotsHotCoordinateInterval q j := by
  obtain ⟨x, hx⟩ := hnonempty
  have h := ((mem_prefixVelocitySection eta zeta q j.1 j w x).1 hx).2
  ext y
  simp only [mem_prefixVelocitySection, prefixVelocityInterval, lt_self_iff_false, if_false, h, and_true]

private theorem section_prefix_succ_eq_contraction_image {d : ℕ}
    (eta zeta : ℝ) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → ℝ) :
    timeVelocityCoordinateSection d (Fin.succ j) (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w =
      centeredCoordinateContraction (q.center j) zeta ''
        timeVelocityCoordinateSection d (Fin.succ j) (inkSpotsQ2PrefixContracted eta zeta j.1 q) w := by
  have hsame (l : Fin d) (hl : l ≠ j) :
      prefixVelocityInterval q zeta (j.1 + 1) l = prefixVelocityInterval q zeta j.1 l := by
    simp only [prefixVelocityInterval, show l.1 < j.1 + 1 ↔ l.1 < j.1 by omega]
  have hfiber : hotSectionFiber eta zeta q (j.1 + 1) j w ↔ hotSectionFiber eta zeta q j.1 j w := by
    constructor <;> rintro ⟨ht, hv⟩ <;> refine ⟨ht, fun l hl => ?_⟩
    · simpa only [hsame l hl] using hv l hl
    · simpa only [hsame l hl] using hv l hl
  ext x
  simp only [mem_prefixVelocitySection, prefixVelocityInterval, Nat.lt_succ_self, if_true,
    hfiber, lt_self_iff_false, if_false, mem_image]
  exact ⟨fun ⟨⟨y, hy, hxy⟩, h⟩ => ⟨y, ⟨hy, h⟩, hxy⟩,
    fun ⟨y, ⟨hy, h⟩, hxy⟩ => ⟨⟨y, hy, hxy⟩, h⟩⟩

section
variable {d : Nat} (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
  (w : Fin d → Real)
include d Gamma xi eta zeta j w

private def hotVelocitySectionBoxes : Set (InkSpotsBox d) :=
  {q ∈ inkSpotsDenseBoxes Gamma xi | (timeVelocityCoordinateSection d (Fin.succ j)
    (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty}

private def hotVelocitySectionFamily : Set (Set ℝ) :=
  (fun q => centeredCoordinateContraction (q.center j) zeta '' inkSpotsHotCoordinateInterval q j) ''
    hotVelocitySectionBoxes Gamma xi eta zeta j w

private theorem section_prefix_union_eq_iUnion (k : ℕ)
    (h : ∀ q, (timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta k q) w).Nonempty →
      (timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) w =
    ⋃ q ∈ hotVelocitySectionBoxes Gamma xi eta zeta j w,
      timeVelocityCoordinateSection d (Fin.succ j) (inkSpotsQ2PrefixContracted eta zeta k q) w := by
  ext x
  simp only [mem_iUnion, mem_timeVelocityCoordinateSection_succ_iff,
    inkSpotsD2PrefixContractedUnion, hotVelocitySectionBoxes, mem_setOf_eq]
  constructor
  · rintro ⟨q, hq, hx⟩
    exact ⟨q, ⟨hq, h q ⟨x, (mem_timeVelocityCoordinateSection_succ_iff ..).mpr hx⟩⟩, hx⟩
  · rintro ⟨q, ⟨hq, _⟩, hx⟩
    exact ⟨q, hq, hx⟩

private theorem section_prefix_succ_union_eq_sUnion_hotVelocityFamily :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (j.1 + 1)) w =
      ⋃₀ hotVelocitySectionFamily Gamma xi eta zeta j w := by
  have hn (q : InkSpotsBox d) (h : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w).Nonempty) := by
    rw [section_prefix_succ_eq_contraction_image] at h
    exact h.of_image
  rw [section_prefix_union_eq_iUnion Gamma xi eta zeta j w (j.1 + 1) hn,
    hotVelocitySectionFamily, sUnion_image]
  refine iUnion_congr fun q => iUnion_congr fun hq => ?_
  rw [section_prefix_succ_eq_contraction_image, section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hq.2]

section
variable (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
include hzeta0 hzeta1

private theorem section_prefix_union_eq_sUnion_expanded_hotVelocityFamily :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta j.1) w =
      ⋃₀ (boundaryShiftedMidpointExpansion zeta⁻¹ ''
        hotVelocitySectionFamily Gamma xi eta zeta j w) := by
  rw [section_prefix_union_eq_iUnion Gamma xi eta zeta j w j.1 (fun _ h => h),
    hotVelocitySectionFamily, ← image_comp, sUnion_image]
  refine iUnion_congr fun q => iUnion_congr fun hq => ?_
  rw [section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hq.2]
  exact (boundaryShiftedMidpointExpansion_image_centeredInterval_inter
    (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
      (strictDense_center_coord_bounds hq.1 j) (mul_pos (by norm_num) hq.1.1)).symm

private theorem hotVelocitySectionFamily_eligible :
    ∀ I ∈ hotVelocitySectionFamily Gamma xi eta zeta j w,
      IsOpenSubinterval (Ioo (-1 : Real) 1) I := by
  rintro I ⟨q, ⟨hq, _⟩, rfl⟩
  have hc := strictDense_center_coord_bounds hq j
  have hr : 0 < q.radius := hq.1
  exact (isClippedCoordinateInterval_centeredCoordinateContraction_image
    (q.center j) zeta hzeta0 hzeta1
      ⟨inkSpotsHotCoordinateInterval_eligible hq j,
        ⟨⟨by nlinarith, by nlinarith⟩, hc⟩⟩).1

end

end

private theorem isOpen_inkSpotsD2PrefixContractedUnion {d : ℕ}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) (k : ℕ) (hzeta : 0 < zeta) :
    IsOpen (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) :=
  isOpen_iUnion fun q => isOpen_iUnion fun _ => isOpen_inkSpotsQ2PrefixContracted eta zeta q k hzeta

section
variable {d : Nat} (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (hzeta0 : 0 < zeta)
  (hzeta1 : zeta < 1)
include hzeta0 hzeta1

private theorem volume_prefix_spatial_step {k : Nat} (hk : k < d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) ≤
      ENNReal.ofReal zeta⁻¹ *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
  let j : Fin d := ⟨k, hk⟩
  apply volume_timeVelocity_le_of_forall_volume_coordinateSection_le
    (Fin.succ j) _ _
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k hzeta0).measurableSet
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)
      hzeta0).measurableSet zeta⁻¹
  intro w
  have hleft := section_prefix_union_eq_sUnion_expanded_hotVelocityFamily
    Gamma xi eta zeta j w hzeta0 hzeta1
  have hright := section_prefix_succ_union_eq_sUnion_hotVelocityFamily
    Gamma xi eta zeta j w
  have hvary := volume_sUnion_boundaryShiftedMidpointExpansion zeta⁻¹
    ((one_lt_inv₀ hzeta0).2 hzeta1)
    (hotVelocitySectionFamily Gamma xi eta zeta j w)
    (hotVelocitySectionFamily_eligible Gamma xi eta zeta j w hzeta0 hzeta1)
  change volume (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta j.1) w) ≤
    ENNReal.ofReal zeta⁻¹ * volume (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (j.1 + 1)) w)
  rw [hleft, hright]
  exact hvary

private theorem volume_prefix_spatial_contraction (k : Nat) (hk : k ≤ d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
      (ENNReal.ofReal zeta⁻¹) ^ k *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt := Nat.lt_of_succ_le hk
      calc
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
            (ENNReal.ofReal zeta⁻¹) ^ k *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) :=
          ih (Nat.le_of_succ_le hk)
        _ ≤ (ENNReal.ofReal zeta⁻¹) ^ k *
              (ENNReal.ofReal zeta⁻¹ *
                volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1))) :=
          mul_le_mul_right (volume_prefix_spatial_step Gamma xi eta zeta
            hzeta0 hzeta1 hklt) _
        _ = (ENNReal.ofReal zeta⁻¹) ^ (k + 1) *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
          rw [pow_succ]
          ac_rfl

end

private theorem inkSpotsQ2PrefixContracted_subset_Q2 {d : Nat}
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (hzeta0 : 0 < zeta)
    (hzeta1 : zeta < 1) (k : Nat) :
    inkSpotsQ2PrefixContracted eta zeta k q ⊆ inkSpotsQ2 eta q := by
  intro z hz
  obtain ⟨ht, hv⟩ := (mem_prefixContracted_iff eta zeta q k z).mp hz
  have ht' := contractedTime_subset_forward hzeta0 hzeta1 ht
  have hvel (l : Fin d) : z.2 l ∈ inkSpotsHotCoordinateInterval q l := by
    specialize hv l
    unfold prefixVelocityInterval at hv
    split at hv
    · obtain ⟨x, hx, he⟩ := hv
      rw [← he]
      have hc : q.center l ∈ inkSpotsHotCoordinateInterval q l :=
        (mem_hotCoordinateInterval_iff q l _).2
          ⟨by simpa using (show 0 < 3 * q.radius from mul_pos (by norm_num) hq.1),
            abs_lt.mpr (strictDense_center_coord_bounds hq l)⟩
      exact ((convex_Ioo ..).inter (convex_Ioo ..) :
        Convex ℝ (inkSpotsHotCoordinateInterval q l)).add_smul_sub_mem hc hx
          ⟨hzeta0.le, hzeta1.le⟩
    · exact hv
  refine mem_inkSpotsQ2_iff.mpr ⟨ht'.1, ht'.2, fun l => ((mem_hotCoordinateInterval_iff q l _).mp (hvel l)).1, fun l => ?_⟩
  simpa only [Pi.zero_apply, sub_zero] using ((mem_hotCoordinateInterval_iff q l _).mp (hvel l)).2

private theorem inkSpotsD3_subset_D2 {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD3 Gamma xi eta zeta ⊆ inkSpotsD2 Gamma xi eta := by
  rw [← inkSpotsD2PrefixContractedUnion_eq_D3]
  intro z hz
  rw [inkSpotsD2PrefixContractedUnion] at hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  rw [inkSpotsD2]
  exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
    inkSpotsQ2PrefixContracted_subset_Q2 hq hzeta0 hzeta1 d hz⟩⟩

private theorem hotWind_scalar_identity (zeta : Real) (hzeta : zeta ≠ 0) (d : Nat) :
    ((zeta ^ 2)⁻¹) * (zeta⁻¹) ^ d = zeta ^ (-((d : Int) + 2)) := by
  have htime : (zeta ^ 2)⁻¹ = zeta ^ (-2 : Int) :=
    (zpow_neg zeta (2 : Int)).symm
  have hspace : (zeta⁻¹) ^ d = zeta ^ (-(d : Int)) := by
    rw [inv_pow, ← zpow_natCast]
    exact (zpow_neg zeta (d : Int)).symm
  rw [htime, hspace, ← zpow_add₀ hzeta]
  congr 1
  omega

/-- Krylov--Safonov, Lemma 2.4 (hot wind): the forward source union is controlled by
its terminal contraction in time and every velocity coordinate. -/
theorem volume_inkSpotsD2_toReal_le_zeta_zpow_mul_D3
    {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ)
    (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    (volume (inkSpotsD2 Gamma xi eta)).toReal ≤
      zeta ^ (-((d : ℤ) + 2)) *
        (volume (inkSpotsD3 Gamma xi eta zeta)).toReal := by
  have htime := volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
    Gamma xi eta zeta heta hzeta0 hzeta1
  have hspace := volume_prefix_spatial_contraction
    Gamma xi eta zeta hzeta0 hzeta1 d le_rfl
  rw [inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted,
    inkSpotsD2PrefixContractedUnion_eq_D3] at hspace
  have hmeasure : volume (inkSpotsD2 Gamma xi eta) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        ((ENNReal.ofReal zeta⁻¹) ^ d *
          volume (inkSpotsD3 Gamma xi eta zeta)) := by
    calc
      volume (inkSpotsD2 Gamma xi eta) ≤
          ENNReal.ofReal ((zeta ^ 2)⁻¹) *
            volume (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := htime
      _ ≤ ENNReal.ofReal ((zeta ^ 2)⁻¹) *
          ((ENNReal.ofReal zeta⁻¹) ^ d *
            volume (inkSpotsD3 Gamma xi eta zeta)) :=
        mul_le_mul_right hspace _
  have hD3finite : volume (inkSpotsD3 Gamma xi eta zeta) ≠ ∞ :=
    ne_top_of_le_ne_top (volume_inkSpotsD2_ne_top Gamma xi eta heta)
      (measure_mono (inkSpotsD3_subset_D2 Gamma xi eta zeta hzeta0 hzeta1))
  have hfinite : ENNReal.ofReal ((zeta ^ 2)⁻¹) *
      ((ENNReal.ofReal zeta⁻¹) ^ d *
        volume (inkSpotsD3 Gamma xi eta zeta)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hD3finite)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (zeta ^ 2)⁻¹),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ zeta⁻¹), ← mul_assoc,
    hotWind_scalar_identity zeta hzeta0.ne' d] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic
