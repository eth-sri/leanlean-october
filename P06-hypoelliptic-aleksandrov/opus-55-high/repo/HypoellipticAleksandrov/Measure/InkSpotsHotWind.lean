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

variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}




private theorem strictDense_center_mem_unit_velocityCube 
    (hq : inkSpotsStrictDense Gamma xi q) :
    q.center ∈ velocityCube (0 : PDE.Vec d) 1 := by
  have hr  := hq.1
  let t  := q.baseTime + q.radius ^ 2 / 2
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    aesop
  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 htSource
  rw [inkSpotsUnitBox] at htUnit
  simp_all

private theorem strictDense_center_coord_bounds 
    (hq : inkSpotsStrictDense Gamma xi q) (j : Fin d) :
    -1 < q.center j ∧ q.center j < 1 := by
  simpa using
    abs_lt.mp (strictDense_center_mem_unit_velocityCube hq j)









variable {a b kappa : ℝ} {I : Set ℝ}





variable {d : ℕ}



/-- The source terminal contraction restricted to its time coordinate. -/
private def inkSpotsTimeContraction {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    ℝ → ℝ :=
  fun t => inkSpotsTerminalTime eta q - zeta ^ 2 *
    (inkSpotsTerminalTime eta q - t)

/-- The first, time-only stage of the terminal contraction. -/
private def inkSpotsQ2TimeContracted {d : ℕ} (eta zeta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

private theorem inkSpotsTimeContraction_forwardInterval {d : ℕ} {eta zeta : ℝ}
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

private def inkSpotsD2TimeContractedUnion {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) : Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2TimeContracted eta zeta q

private theorem inkSpotsQ2TimeContracted_subset_Q2 {d : ℕ} {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsQ2TimeContracted eta zeta q ⊆ inkSpotsQ2 eta q := by
  intro z hz
  rcases z with ⟨t, v⟩
  rcases hz.1 with ⟨s, hs, rfl⟩
  rw [mem_inkSpotsQ2_iff]
  refine ⟨?_, ?_, hz.2.1, hz.2.2⟩
  · change q.baseTime + q.radius ^ 2 <
      inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - s)
    have hsq1 : zeta ^ 2 < 1 := by
      nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
    have hT : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q :=
      hs.1.trans hs.2
    have hdecomp :
        inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - s) - (q.baseTime + q.radius ^ 2) =
          (1 - zeta ^ 2) *
              (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)) +
            zeta ^ 2 * (s - (q.baseTime + q.radius ^ 2)) := by
      ring
    apply sub_pos.mp
    rw [hdecomp]
    exact add_pos
      (mul_pos (sub_pos.mpr hsq1) (sub_pos.mpr hT))
      (mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr hs.1))
  · change inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - s) < inkSpotsTerminalTime eta q
    have hsq0 : 0 < zeta ^ 2 := sq_pos_of_pos hzeta0
    apply sub_pos.mp
    nlinarith [mul_pos hsq0 (sub_pos.mpr hs.2)]

private def hotTimeSectionFamily {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta zeta : ℝ) (v : PDE.Vec d) : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q}

variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ)

private theorem timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily
     (v : PDE.Vec d) :
    timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v =
      ⋃₀ (hotTimeSectionFamily Gamma xi eta zeta v) := by
  ext t
  constructor
  · intro ht
    rcases mem_iUnion.1 ht with ⟨q, ht⟩
    rcases mem_iUnion.1 ht with ⟨hq, ht⟩
    refine mem_sUnion.2 ⟨inkSpotsTimeContraction eta zeta q ''
      windForwardInterval eta q, ?_, ht.1⟩
    exact ⟨q, hq, ht.2.1, ht.2.2, rfl⟩
  · intro ht
    rcases mem_sUnion.1 ht with ⟨I, hI, ht⟩
    rcases hI with ⟨q, hq, hvCenter, hvUnit, rfl⟩
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, ⟨ht, hvCenter, hvUnit⟩⟩⟩

private theorem hotTimeInterval_eligible  {Gamma : Set (TimeVelocity d)}
    {xi eta zeta : ℝ} {q : InkSpotsBox d} (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta)
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  constructor
  · apply nonempty_Ioo.mpr
    have hsource : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
      rw [inkSpotsTerminalTime_eq]
      have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
      simp_all
    simp_all
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have himage : t ∈ inkSpotsTimeContraction eta zeta q ''
        windForwardInterval eta q := by
      rw [inkSpotsTimeContraction_forwardInterval hzeta0]
      exact ht
    rcases himage with ⟨s, hs, rfl⟩
    have htime : (inkSpotsTimeContraction eta zeta q s, q.center) ∈
        inkSpotsQ2TimeContracted eta zeta q := by
      refine ⟨⟨s, hs, rfl⟩, ?_, ?_⟩
      · intro i
        simp only [sub_self, abs_zero]
        exact mul_pos (by norm_num) hq.1
      · exact strictDense_center_mem_unit_velocityCube hq
    have hq2 := inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1 htime
    rw [mem_inkSpotsQ2_iff] at hq2
    exact (windForwardInterval_eligible heta hq).2.2.2 ⟨hq2.1, hq2.2.1⟩

private theorem hotTimeExpansion_contractedInterval 
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (zeta ^ 2)⁻¹
        (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) =
      windForwardInterval eta q := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  unfold rightEndpointExpansion windForwardInterval
  have hsource : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
    rw [inkSpotsTerminalTime_eq]
    have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    simp_all
  have hcontracted :
      inkSpotsTerminalTime eta q - zeta ^ 2 *
          (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)) <
        inkSpotsTerminalTime eta q := by
    simp_all
  rw [csInf_Ioo hcontracted, csSup_Ioo hcontracted]
  congr 1
  rw [max_eq_right]
  · field_simp
    ring
  · have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    have hidentity : inkSpotsTerminalTime eta q - (zeta ^ 2)⁻¹ *
        (inkSpotsTerminalTime eta q -
          (inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))) =
        q.baseTime + q.radius ^ 2 := by
      field_simp
      ring
    rw [hidentity]
    positivity

private theorem timeSection_inkSpotsD2_subset_expanded_hotTimeSections  (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    timeSection (inkSpotsD2 Gamma xi eta) v ⊆
      ⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
        hotTimeSectionFamily Gamma xi eta zeta v) := by
  intro t ht
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

private theorem sUnion_hotTimeSectionFamily_bounded  (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    Bornology.IsBounded (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (hotTimeInterval_eligible heta hzeta0 hzeta1 hq).2.2.2

private theorem volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
     (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d) :
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
  have hsq0 : 0 < zeta ^ 2 := sq_pos_of_pos hzeta0
  have hsq1 : zeta ^ 2 < 1 := by
    nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)]
  calc
    volume _ ≤
        volume _ :=
      measure_mono (timeSection_inkSpotsD2_subset_expanded_hotTimeSections
        Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ ≤ ENNReal.ofReal _ *
        volume _ :=
      volume_sUnion_rightEndpointExpansion ((one_lt_inv₀ hsq0).2 hsq1) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact hotTimeInterval_eligible heta hzeta0 hzeta1 hq)
        (sUnion_hotTimeSectionFamily_bounded Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ = ENNReal.ofReal _ *
        volume _ := by
      rw [timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily]

private theorem isOpen_inkSpotsQ2TimeContracted  {eta zeta : ℝ}
    (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2TimeContracted eta zeta q) := by
  rw [inkSpotsQ2TimeContracted, inkSpotsTimeContraction_forwardInterval hzeta0]
  exact isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

private theorem isOpen_inkSpotsD2TimeContractedUnion  (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2TimeContracted q hzeta0

private theorem volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted  (heta : 0 < eta)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    volume (inkSpotsD2 Gamma xi eta) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta),
    volume_eq_lintegral_timeSection _
      (isOpen_inkSpotsD2TimeContractedUnion Gamma xi eta zeta hzeta0).measurableSet]
  calc
    (∫⁻ v, volume _) ≤
        ∫⁻ v, ENNReal.ofReal _ *
          volume _ :=
      lintegral_mono fun v =>
        volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
          Gamma xi eta zeta heta hzeta0 hzeta1 v
    _ = ENNReal.ofReal _ *
        ∫⁻ v, volume _ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! The remaining contractions are deliberately staged by prefix.  Keeping
the family of boxes under the union at every stage is essential: different
boxes meeting the same section have different velocity centres. -/

private def inkSpotsVelocityPrefixContraction {d : Nat}
    (q : InkSpotsBox d) (zeta : Real) (k : Nat) (v : PDE.Vec d) : PDE.Vec d :=
  fun j => if j.1 < k then q.center j + zeta * (v j - q.center j) else v j

private def inkSpotsQ2PrefixContracted {d : Nat}
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  {z | ∃ y ∈ inkSpotsQ2 eta q,
    z.1 = inkSpotsTimeContraction eta zeta q y.1 ∧
      z.2 = inkSpotsVelocityPrefixContraction q zeta k y.2}

private def inkSpotsD2PrefixContractedUnion {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2PrefixContracted eta zeta k q

variable {d : Nat} (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)

private theorem inkSpotsQ2PrefixContracted_zero_eq_timeContracted 
    (eta zeta : Real) (q : InkSpotsBox d) :
    inkSpotsQ2PrefixContracted eta zeta 0 q = inkSpotsQ2TimeContracted eta zeta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    rcases y with ⟨t, v⟩
    rw [mem_inkSpotsQ2_iff] at hy
    have hzv : z.2 = v := by
      aesop
    refine ⟨⟨t, ⟨hy.1, hy.2.1⟩, ht.symm⟩, ?_, ?_⟩
    · grind
    grind
  · rintro ⟨htime, hcenter, hunit⟩
    rcases htime with ⟨t, ht, htime⟩
    refine ⟨(t, z.2), ?_, htime.symm, ?_⟩
    · aesop
    aesop

private theorem inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted  :
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
    refine ⟨y, hy, ?_⟩
    apply Prod.ext
    · aesop
    · funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]
  · rintro ⟨y, hy, hcontraction⟩
    refine ⟨y, hy, ?_, ?_⟩
    · aesop
    · have hv := congrArg Prod.snd hcontraction.symm
      funext j
      have hj : j.1 < d := j.isLt
      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos hj]

private theorem inkSpotsD2PrefixContractedUnion_eq_D3  :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta d = inkSpotsD3 Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD3,
    inkSpotsQ2PrefixContracted_eq_Q3]

private def inkSpotsAffineHomeomorph (c zeta : Real) (hzeta : zeta ≠ 0) :
    Real ≃ₜ Real :=
  (Homeomorph.addLeft (-c)).trans
    ((Homeomorph.smulOfNeZero zeta hzeta).trans (Homeomorph.addLeft c))

private theorem inkSpotsAffineHomeomorph_apply (c zeta : Real) (hzeta : zeta ≠ 0)
    (x : Real) :
    inkSpotsAffineHomeomorph c zeta hzeta x = c + zeta * (x - c) := by
  simp [inkSpotsAffineHomeomorph, Homeomorph.smulOfNeZero]
  ring

private def inkSpotsPrefixHomeomorph {d : Nat} (eta zeta : Real) (k : Nat)
    (q : InkSpotsBox d) (hzeta : zeta ≠ 0) : TimeVelocity d ≃ₜ TimeVelocity d :=
  (inkSpotsAffineHomeomorph (inkSpotsTerminalTime eta q) (zeta ^ 2)
    (pow_ne_zero _ hzeta)).prodCongr
    (Homeomorph.piCongrRight fun j =>
      if _ : j.1 < k then inkSpotsAffineHomeomorph (q.center j) zeta hzeta
      else Homeomorph.refl Real)

variable {d : Nat} (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) (hzeta : zeta ≠ 0)

private theorem inkSpotsPrefixHomeomorph_apply  (y : TimeVelocity d) :
    inkSpotsPrefixHomeomorph eta zeta k q hzeta y =
      (inkSpotsTimeContraction eta zeta q y.1,
        inkSpotsVelocityPrefixContraction q zeta k y.2) := by
  apply Prod.ext
  · rw [show inkSpotsTimeContraction eta zeta q y.1 =
      inkSpotsTerminalTime eta q + zeta ^ 2 *
        (y.1 - inkSpotsTerminalTime eta q) by
      unfold inkSpotsTimeContraction
      ring]
    exact inkSpotsAffineHomeomorph_apply _ _ _ _
  · funext j
    change (Homeomorph.piCongrRight fun l =>
      if _ : l.1 < k then inkSpotsAffineHomeomorph (q.center l) zeta hzeta
      else Homeomorph.refl Real) y.2 j =
        inkSpotsVelocityPrefixContraction q zeta k y.2 j
    rw [Homeomorph.piCongrRight_apply]
    by_cases hj : j.1 < k
    · rw [dif_pos hj, inkSpotsAffineHomeomorph_apply]
      simp only [inkSpotsVelocityPrefixContraction, if_pos hj]
    · rw [dif_neg hj]
      simp only [inkSpotsVelocityPrefixContraction, if_neg hj]
      rfl

private theorem inkSpotsQ2PrefixContracted_eq_homeomorph_image  :
    inkSpotsQ2PrefixContracted eta zeta k q =
      inkSpotsPrefixHomeomorph eta zeta k q hzeta '' inkSpotsQ2 eta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    refine ⟨y, hy, ?_⟩
    rw [inkSpotsPrefixHomeomorph_apply]
    grind
  · rintro ⟨y, hy, hzy⟩
    refine ⟨y, hy, ?_, ?_⟩
    have hcomponents := congrArg Prod.fst hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    exact hcomponents.symm
    have hcomponents := congrArg Prod.snd hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    simp_all

private theorem isOpen_inkSpotsQ2PrefixContracted  {eta zeta : Real}
    (k : Nat) (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2PrefixContracted eta zeta k q) := by
  rw [inkSpotsQ2PrefixContracted_eq_homeomorph_image eta zeta k q hzeta0.ne']
  exact (inkSpotsPrefixHomeomorph eta zeta k q hzeta0.ne').isOpenMap _
    (isOpen_inkSpotsQ2 eta q)

private theorem isOpen_inkSpotsD2PrefixContractedUnion 
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat)
    (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2PrefixContracted k q hzeta0

private def inkSpotsVelocitySectionPoint {d : Nat} (j : Fin d) (x : Real)
    (w : Fin d → Real) : TimeVelocity d :=
  (timeVelocityCoordinateEquiv d).symm
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
      (Fin.succ j)).symm (x, w))

variable {d : Nat} (j : Fin d) (x : Real) (w : Fin d → Real)

private theorem mem_timeVelocityCoordinateSection_succ_iff 
    (S : Set (TimeVelocity d)) (w : Fin d → Real) (x : Real) :
    x ∈ timeVelocityCoordinateSection d (Fin.succ j) S w ↔
      inkSpotsVelocitySectionPoint j x w ∈ S := by
  let e := timeVelocityCoordinateEquiv d
  let ei := MeasurableEquiv.piFinSuccAbove (fun _ : Fin _ => Real)
    (Fin.succ j)
  change ei.symm _ ∈ e '' S ↔ _
  constructor
  · rintro ⟨z, hz, heq⟩
    have hz_eq : z = e.symm (ei.symm (x, w)) := by
      apply e.injective
      simp_all
    aesop
  · intro hz
    refine ⟨e.symm (ei.symm (x, w)), hz, ?_⟩
    simp

private theorem timeVelocityCoordinateEquiv_sectionPoint  :
    timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
        (Fin.succ j)).symm (x, w) := by
  simp [inkSpotsVelocitySectionPoint]

private theorem sectionPoint_velocity_eq  : (inkSpotsVelocitySectionPoint j x w).2 j = x := by
  simp [inkSpotsVelocitySectionPoint, timeVelocityCoordinateEquiv, Fin.tail]

private theorem sectionPoint_velocity_eq_of_ne  (j l : Fin d) (x y : Real)
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

private def inkSpotsPrefixCoordinateSectionFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    I = timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta k q) w ∧ I.Nonempty}

private theorem timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) w =
      ⋃₀ inkSpotsPrefixCoordinateSectionFamily Gamma xi eta zeta k j w := by
  ext x
  rw [mem_timeVelocityCoordinateSection_succ_iff]
  constructor
  · intro hx
    rcases mem_iUnion.1 hx with ⟨q, hx⟩
    rcases mem_iUnion.1 hx with ⟨hq, hx⟩
    refine mem_sUnion.2 ⟨timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta k q) w, ?_, ?_⟩
    · refine ⟨q, hq, rfl, ⟨x, ?_⟩⟩
      rw [mem_timeVelocityCoordinateSection_succ_iff]
      exact hx
    · rw [mem_timeVelocityCoordinateSection_succ_iff]
      exact hx
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, hI, hxI⟩
    rcases hI with ⟨q, hq, rfl, _⟩
    rw [mem_timeVelocityCoordinateSection_succ_iff] at hxI
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, hxI⟩⟩

private def inkSpotsHotCoordinateInterval {d : Nat} (q : InkSpotsBox d)
    (j : Fin d) : Set Real :=
  Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1

variable {d : Nat} (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)

private theorem inkSpotsHotCoordinateInterval_eligible 
    {Gamma : Set (TimeVelocity d)} {xi : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (j : Fin d) :
    IsOpenSubinterval (Ioo (-1 : Real) 1) (inkSpotsHotCoordinateInterval q j) := by
  have hc := strictDense_center_coord_bounds hq j
  have hr  := hq.1
  refine ⟨⟨q.center j, ⟨?_, hc⟩⟩, isOpen_Ioo.inter isOpen_Ioo,
    ordConnected_Ioo.inter ordConnected_Ioo, inter_subset_right⟩
  simp_all

private theorem section_prefix_eq_hotInterval_of_nonempty 
    (hnonempty : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta j.1 q) w =
      inkSpotsHotCoordinateInterval q j := by
  obtain ⟨x₀, hx₀⟩ := hnonempty
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx₀
  rcases hx₀ with ⟨y₀, hy₀, ht₀, hv₀⟩
  have hy₀' := hy₀
  rw [mem_inkSpotsQ2_iff] at hy₀'
  ext x
  constructor
  · rw [mem_timeVelocityCoordinateSection_succ_iff]
    rintro ⟨y, hy, _, hv⟩
    rw [mem_inkSpotsQ2_iff] at hy
    have hcoord := congrFun hv j
    simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction] at hcoord
    rw [inkSpotsHotCoordinateInterval]
    have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)
    have hu : -1 < y.2 j ∧ y.2 j < 1 := by
      simpa only [Pi.zero_apply, sub_zero] using
        abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j)
    grind
  · intro hx
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then x else y₀.2 l
    have hvcenter : v ∈ velocityCube q.center (3 * q.radius) := by
      intro l
      by_cases hlj : l = j
      · subst l
        simp only [v, if_pos]
        exact abs_lt.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
      aesop
    have hvunit : v ∈ velocityCube 0 1 := by
      intro l
      by_cases hlj : l = j
      · subst l
        simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hx.2
      aesop
    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · simp_all
    · aesop
    · funext l
      by_cases hlj : l = j
      · subst l
        simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
          lt_self_iff_false, if_false, v, if_pos]
      · calc
          (inkSpotsVelocitySectionPoint j x w).2 l =
              (inkSpotsVelocitySectionPoint j x₀ w).2 l :=
                sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 y₀.2 l := congrFun hv₀ l
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 v l := by
            simp only [inkSpotsVelocityPrefixContraction, v, if_neg hlj]

private theorem section_prefix_succ_eq_contraction_image_of_nonempty 
    (hnonempty : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w =
      centeredCoordinateContraction (q.center j) zeta ''
        inkSpotsHotCoordinateInterval q j := by
  obtain ⟨x₀, hx₀⟩ := hnonempty
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx₀
  rcases hx₀ with ⟨y₀, hy₀, ht₀, hv₀⟩
  have hy₀' := hy₀
  rw [mem_inkSpotsQ2_iff] at hy₀'
  ext x
  constructor
  · rw [mem_timeVelocityCoordinateSection_succ_iff]
    rintro ⟨y, hy, _, hv⟩
    rw [mem_inkSpotsQ2_iff] at hy
    refine ⟨y.2 j, ?_, ?_⟩
    · have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)
      have hu : -1 < y.2 j ∧ y.2 j < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j)
      exact ⟨⟨by linarith, by linarith⟩, hu⟩
    · have hcoord := congrFun hv j
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction] at hcoord
      aesop
  · rintro ⟨u, hu, rfl⟩
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then u else y₀.2 l
    have hvcenter : v ∈ velocityCube q.center (3 * q.radius) := by
      intro l
      by_cases hlj : l = j
      · subst l
        simp only [v, if_pos]
        exact abs_lt.mpr ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
      aesop
    have hvunit : v ∈ velocityCube 0 1 := by
      intro l
      by_cases hlj : l = j
      · subst l
        simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hu.2
      aesop
    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · simp_all
    · aesop
    · funext l
      by_cases hlj : l = j
      · subst l
        simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
          Nat.lt_succ_self, v, if_pos, centeredCoordinateContraction]
      · calc
          (inkSpotsVelocitySectionPoint j
              _ w).2 l =
              (inkSpotsVelocitySectionPoint j x₀ w).2 l :=
                sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 y₀.2 l := congrFun hv₀ l
          _ = inkSpotsVelocityPrefixContraction q zeta _ v l := by
            by_cases hl : l.1 < j.1
            · have hls : l.1 < j.1 + 1 := hl.trans (Nat.lt_succ_self _)
              simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos hls,
                v, if_neg hlj]
            · have hls : ¬ l.1 < j.1 + 1 := by omega
              simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg hls,
                v, if_neg hlj]

private theorem section_prefix_nonempty_of_succ_nonempty 
    (h : (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta (j.1 + 1) q) w).Nonempty) :
    (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty := by
  obtain ⟨x, hx⟩ := h
  rw [mem_timeVelocityCoordinateSection_succ_iff] at hx
  rcases hx with ⟨y, hy, ht, hv⟩
  refine ⟨y.2 j, ?_⟩
  rw [mem_timeVelocityCoordinateSection_succ_iff]
  refine ⟨y, hy, ?_, ?_⟩
  · aesop
  · funext l
    by_cases hlj : l = j
    · subst l
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
        lt_self_iff_false, if_false]
    · calc
        (inkSpotsVelocitySectionPoint j _ w).2 l =
            (inkSpotsVelocitySectionPoint j x w).2 l :=
              sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
        _ = inkSpotsVelocityPrefixContraction q zeta _ y.2 l := congrFun hv l
        _ = inkSpotsVelocityPrefixContraction q zeta j.1 y.2 l := by
          by_cases hl : l.1 < j.1
          · have hls : l.1 < j.1 + 1 := hl.trans (Nat.lt_succ_self _)
            simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos hls]
          · have hls : ¬ l.1 < j.1 + 1 := by omega
            simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg hls]

private def hotVelocitySectionFamily {d : Nat}
    (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty ∧
    I = centeredCoordinateContraction (q.center j) zeta ''
      inkSpotsHotCoordinateInterval q j}

variable {d : Nat} (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real) (j : Fin d) (w : Fin d → Real)

private theorem section_prefix_succ_union_eq_sUnion_hotVelocityFamily  :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (j.1 + 1)) w =
      ⋃₀ hotVelocitySectionFamily Gamma xi eta zeta j w := by
  rw [timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family]
  ext x
  constructor
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, rfl, hne⟩, hxI⟩
    have hpre := section_prefix_nonempty_of_succ_nonempty eta zeta q j w hne
    rw [section_prefix_succ_eq_contraction_image_of_nonempty eta zeta q j w hpre] at hxI
    exact mem_sUnion.2 ⟨_, ⟨q, hq, hpre, rfl⟩, hxI⟩
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, hpre, rfl⟩, hxI⟩
    rw [← section_prefix_succ_eq_contraction_image_of_nonempty eta zeta q j w hpre]
      at hxI
    exact mem_sUnion.2 ⟨_, ⟨q, hq, rfl, ⟨x, hxI⟩⟩, hxI⟩

private theorem section_prefix_union_eq_sUnion_expanded_hotVelocityFamily  (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta j.1) w =
      ⋃₀ (boundaryShiftedMidpointExpansion zeta⁻¹ ''
        hotVelocitySectionFamily Gamma xi eta zeta j w) := by
  rw [timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family]
  ext x
  constructor
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨I, ⟨q, hq, rfl, hpre⟩, hxI⟩
    rw [section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hpre] at hxI
    let K := centeredCoordinateContraction (q.center j) zeta ''
      inkSpotsHotCoordinateInterval q j
    have hrecover : boundaryShiftedMidpointExpansion zeta⁻¹ K =
        inkSpotsHotCoordinateInterval q j := boundaryShiftedMidpointExpansion_image_centeredInterval_inter
        _ _ zeta hzeta0 hzeta1
          (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)
    exact mem_sUnion.2 ⟨boundaryShiftedMidpointExpansion _ K,
      ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, by simp_all⟩
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨E, ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, hxE⟩
    change x ∈ boundaryShiftedMidpointExpansion zeta⁻¹
      ((fun u : Real => q.center j + zeta * (u - q.center j)) ''
        (Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1))
      at hxE
    rw [boundaryShiftedMidpointExpansion_image_centeredInterval_inter
      (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
        (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)] at hxE
    have hxJ : x ∈ inkSpotsHotCoordinateInterval q j := hxE
    rw [← section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hpre] at hxJ
    exact mem_sUnion.2 ⟨_, ⟨q, hq, rfl, hpre⟩, hxJ⟩

private theorem hotVelocitySectionFamily_eligible  (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    ∀ I ∈ hotVelocitySectionFamily Gamma xi eta zeta j w,
      IsOpenSubinterval (Ioo (-1 : Real) 1) I := by
  rintro I ⟨q, hq, _, rfl⟩
  have hc := strictDense_center_coord_bounds hq j
  have hr  := hq.1
  exact (isClippedCoordinateInterval_centeredCoordinateContraction_image
    _ zeta hzeta0 hzeta1
      ⟨inkSpotsHotCoordinateInterval_eligible hq j,
        ⟨⟨by nlinarith, by nlinarith⟩, hc⟩⟩).1

private theorem volume_prefix_spatial_step 
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) {k : Nat} (hk : k < d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) ≤
      ENNReal.ofReal zeta⁻¹ *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
  let j : Fin d := ⟨k, hk⟩
  apply volume_timeVelocity_le_of_forall_volume_coordinateSection_le
    (Fin.succ j) _ _
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k hzeta0).measurableSet
    (isOpen_inkSpotsD2PrefixContractedUnion Gamma xi eta zeta _
      hzeta0).measurableSet _
  intro w
  have hleft := section_prefix_union_eq_sUnion_expanded_hotVelocityFamily
    Gamma xi eta zeta j w hzeta0 hzeta1
  have hright := section_prefix_succ_union_eq_sUnion_hotVelocityFamily
    Gamma xi eta zeta j w
  have hvary := volume_sUnion_boundaryShiftedMidpointExpansion zeta⁻¹
    ((one_lt_inv₀ hzeta0).2 hzeta1)
    _
    (hotVelocitySectionFamily_eligible Gamma xi eta zeta j w hzeta0 hzeta1)
  grind

private theorem volume_prefix_spatial_contraction 
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (k : Nat) (hk : k ≤ d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
      (ENNReal.ofReal zeta⁻¹) ^ k *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hklt : k < d := Nat.lt_of_succ_le hk
      calc
        volume _ ≤
            (ENNReal.ofReal _) ^ k *
              volume _ :=
          ih (Nat.le_of_succ_le hk)
        _ ≤ (ENNReal.ofReal _) ^ k *
              (ENNReal.ofReal _ *
                volume _) :=
          mul_le_mul_right (volume_prefix_spatial_step Gamma xi eta zeta
            hzeta0 hzeta1 hklt) _
        _ = (ENNReal.ofReal _) ^ (k + 1) *
              volume _ := by
          ring

private theorem inkSpotsQ2PrefixContracted_subset_Q2 
    {Gamma : Set (TimeVelocity d)} {xi eta zeta : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (hzeta0 : 0 < zeta)
    (hzeta1 : zeta < 1) (k : Nat) :
    inkSpotsQ2PrefixContracted eta zeta k q ⊆ inkSpotsQ2 eta q := by
  rintro z ⟨y, hy, ht, hv⟩
  have hy' := hy
  rw [mem_inkSpotsQ2_iff] at hy'
  have htime : (z.1, y.2) ∈ inkSpotsQ2 eta q :=
    inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1
      ⟨⟨y.1, ⟨hy'.1, hy'.2.1⟩, ht.symm⟩, hy'.2.2.1, hy'.2.2.2⟩
  rw [mem_inkSpotsQ2_iff] at htime ⊢
  refine ⟨htime.1, htime.2.1, ?_, ?_⟩
  · intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hyc := mem_velocityCube_iff.mp hy'.2.2.1 l
      rw [show q.center l + zeta * (y.2 l - q.center l) - q.center l =
        zeta * (y.2 l - q.center l) by ring, abs_mul, abs_of_pos hzeta0]
      nlinarith [abs_nonneg (y.2 l - q.center l)]
    · rw [if_neg hl]
      simp_all
  · intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hc := strictDense_center_coord_bounds hq l
      have hyv : -1 < y.2 l ∧ y.2 l < 1 := by
        simpa using
          abs_lt.mp (mem_velocityCube_iff.mp hy'.2.2.2 l)
      rw [Pi.zero_apply, abs_lt]
      constructor <;> nlinarith
    · rw [if_neg hl]
      simp_all

private theorem inkSpotsD3_subset_D2 
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD3 Gamma xi eta zeta ⊆ inkSpotsD2 Gamma xi eta := by
  rw [← inkSpotsD2PrefixContractedUnion_eq_D3]
  intro z hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
    inkSpotsQ2PrefixContracted_subset_Q2 hq hzeta0 hzeta1 d hz⟩⟩



private theorem hotWind_scalar_identity (zeta : Real) (hzeta : zeta ≠ 0) (d : Nat) :
    ((zeta ^ 2)⁻¹) * (zeta⁻¹) ^ d = zeta ^ (-((d : Int) + 2)) := by
  have htime : (zeta ^ 2)⁻¹ = zeta ^ (-2 : Int) :=
    (zpow_neg zeta (2)).symm
  have hspace : (zeta⁻¹) ^ d = zeta ^ (-(d : Int)) := by
    simp
  rw [htime, hspace, ← zpow_add₀ hzeta]
  simp

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
      volume _ ≤
          ENNReal.ofReal _ *
            volume _ := htime
      _ ≤ ENNReal.ofReal _ *
          ((ENNReal.ofReal _) ^ d *
            volume _) :=
        mul_le_mul_right hspace _
  have hD3finite : volume _ ≠ ∞ :=
    ne_top_of_le_ne_top (volume_inkSpotsD2_ne_top Gamma xi eta heta)
      (measure_mono (inkSpotsD3_subset_D2 Gamma xi eta zeta hzeta0 hzeta1))
  have hfinite : ENNReal.ofReal ((zeta ^ 2)⁻¹) *
      ((ENNReal.ofReal zeta⁻¹) ^ d *
        volume _) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hD3finite)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ← mul_assoc,
    hotWind_scalar_identity zeta hzeta0.ne'] at hreal
  omega

end HypoellipticAleksandrov.Parabolic
