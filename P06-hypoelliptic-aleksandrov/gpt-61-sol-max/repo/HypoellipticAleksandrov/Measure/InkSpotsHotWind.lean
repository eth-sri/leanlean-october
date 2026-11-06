module

public import HypoellipticAleksandrov.Measure.InkSpotsWind
public import HypoellipticAleksandrov.Measure.ClippedCoordinateUnion
public import HypoellipticAleksandrov.Measure.VaryingCenterIntervalUnion
import Aesop
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Linarith
import all HypoellipticAleksandrov.Measure.InkSpotsWind

open private HypoellipticAleksandrov.Parabolic.isOpen_ordConnected_eq_Ioo_csInf_csSup from HypoellipticAleksandrov.Measure.InkSpotsWind
open private HypoellipticAleksandrov.Parabolic.strictDense_timeInterval_subset_unit from HypoellipticAleksandrov.Measure.InkSpotsWind
open private HypoellipticAleksandrov.Parabolic.volume_inkSpotsD2_ne_top from HypoellipticAleksandrov.Measure.InkSpotsWind
open private HypoellipticAleksandrov.Parabolic.strictDense_baseTime_add_sq_le_one from HypoellipticAleksandrov.Measure.InkSpotsWind
open private HypoellipticAleksandrov.Parabolic.strictDense_baseTime_nonneg from HypoellipticAleksandrov.Measure.InkSpotsWind
open private HypoellipticAleksandrov.Parabolic.isBounded_velocityCube from HypoellipticAleksandrov.Measure.InkSpotsWind
section
open private HypoellipticAleksandrov.Parabolic.isOpenSubinterval_rightEndpointExpansion from HypoellipticAleksandrov.Measure.InkSpotsWind
private alias _sharedProof_223_0 := HypoellipticAleksandrov.Parabolic.isOpenSubinterval_rightEndpointExpansion
end
section
open private HypoellipticAleksandrov.Parabolic.rightEndpointExpansion_measure_le from HypoellipticAleksandrov.Measure.InkSpotsWind
private alias _sharedProof_225_0 := HypoellipticAleksandrov.Parabolic.rightEndpointExpansion_measure_le
end
section
open private HypoellipticAleksandrov.Parabolic.windForwardInterval_eligible from HypoellipticAleksandrov.Measure.InkSpotsWind
private alias _sharedProof_21_0 := HypoellipticAleksandrov.Parabolic.windForwardInterval_eligible
end
section
open private HypoellipticAleksandrov.Parabolic.inkSpotsQ2_subset_windAmbient from HypoellipticAleksandrov.Measure.InkSpotsWind
private alias _sharedProof_40_0 := HypoellipticAleksandrov.Parabolic.inkSpotsQ2_subset_windAmbient
end
section
open private HypoellipticAleksandrov.Parabolic.volume_sUnion_rightEndpointExpansion from HypoellipticAleksandrov.Measure.InkSpotsWind
private alias _sharedProof_10_0 := HypoellipticAleksandrov.Parabolic.volume_sUnion_rightEndpointExpansion
end


/-!
# Hot-wind scaffold for source ink spots

This module proves Lemma 2.4 of Krylov--Safonov, Section 2, by a
time contraction followed by one varying-centre/Fubini contraction for each
velocity coordinate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ} {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi : ℝ} {q : InkSpotsBox d} (hq : inkSpotsStrictDense Gamma xi q)

include hq









private theorem strictDense_center_mem_unit_velocityCube  :
    q.center ∈ velocityCube (0 : PDE.Vec d) 1 := by
  have hr  := hq.1
  let t : ℝ := q.baseTime + q.radius ^ 2 / 2

  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 (by
      rw [mem_inkSpotsSourceBox_iff]
      refine ⟨?_, ?_, ?_⟩
      · dsimp [t]
        nlinarith [sq_pos_of_pos hr]
      · dsimp [t]
        nlinarith [sq_pos_of_pos hr]
      · intro i
        simp only [sub_self, abs_zero]
        exact hr)
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  exact htUnit.2.2

private theorem strictDense_center_coord_bounds  (j : Fin d) :
    -1 < q.center j ∧ q.center j < 1 := by
  simpa only [Pi.zero_apply, sub_zero] using
    abs_lt.mp (strictDense_center_mem_unit_velocityCube hq j)
end


private def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

variable (d : ℕ)





variable {d : ℕ}




/-- The time section of a forward source stack. -/
private def windForwardInterval  (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)




/-- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
private def rightEndpointExpansion (a kappa : ℝ) (I : Set ℝ) : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)



variable {a b kappa : ℝ}

variable {I : Set ℝ}







private theorem volume_sUnion_rightEndpointExpansion
    (hkappa : 1 < kappa) (B : Set (Set ℝ))
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := (_sharedProof_10_0 hkappa B hB hbounded)


variable {d : ℕ}

private def timeSection  (S : HypoellipticAleksandrov.Parabolic.Region d) (v : PDE.Vec d) : Set ℝ :=
  {t | (t, v) ∈ S}

private theorem windForwardInterval_eligible
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta) (windForwardInterval eta q) := (_sharedProof_21_0 heta hq)


private theorem volume_eq_lintegral_timeSection  (S : HypoellipticAleksandrov.Parabolic.Region d)
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

variable (eta zeta : ℝ) (q : InkSpotsBox d)

/-- The source terminal contraction restricted to its time coordinate. -/
private def inkSpotsTimeContraction   :
    ℝ → ℝ :=
  fun t => inkSpotsTerminalTime eta q - zeta ^ 2 *
    (inkSpotsTerminalTime eta q - t)

/-- The first, time-only stage of the terminal contraction. -/
private def inkSpotsQ2TimeContracted   :
    HypoellipticAleksandrov.Parabolic.Region d :=
  (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

private theorem inkSpotsTimeContraction_forwardInterval  {eta zeta : ℝ}
    {q : InkSpotsBox d} (hzeta : 0 < zeta) :
    inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q =
      Ioo (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2)))
        (inkSpotsTerminalTime eta q) := by
  unfold inkSpotsTimeContraction windForwardInterval
  let T := inkSpotsTerminalTime eta q

  convert image_affine_Ioo (sq_pos_of_pos hzeta) ((1 - zeta ^ 2) * T)
    (q.baseTime + q.radius ^ 2) T using 1 <;> ext <;> dsimp [T] <;> ring_nf

private def inkSpotsD2TimeContractedUnion  (Gamma : HypoellipticAleksandrov.Parabolic.Region d)
    (xi eta zeta : ℝ) : HypoellipticAleksandrov.Parabolic.Region d :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2TimeContracted eta zeta q

private theorem inkSpotsQ2TimeContracted_subset_Q2  {eta zeta : ℝ}
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
    rw [windForwardInterval, mem_Ioo] at hs
    nlinarith
  · change inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - s) < inkSpotsTerminalTime eta q

    rw [windForwardInterval, mem_Ioo] at hs
    apply sub_pos.mp
    nlinarith [mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr hs.2)]

variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : ℝ) (v : PDE.Vec d)

private def hotTimeSectionFamily   : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q}

private theorem timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily
      :
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

section
variable {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta zeta : ℝ} {q : InkSpotsBox d} (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (hq : inkSpotsStrictDense Gamma xi q)

include heta hzeta0 hzeta1 hq
private theorem hotTimeInterval_eligible   :
    IsOpenSubinterval (windAmbientTime eta)
      (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) := by
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  constructor
  · apply nonempty_Ioo.mpr



    nlinarith [mul_pos (sq_pos_of_pos hzeta0) (sub_pos.mpr (show q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q by
        rw [inkSpotsTerminalTime_eq]
        have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
        field_simp
        nlinarith))]
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

    have hq2 := inkSpotsQ2TimeContracted_subset_Q2 hzeta0 hzeta1 (show (inkSpotsTimeContraction eta zeta q s, q.center) ∈
        inkSpotsQ2TimeContracted eta zeta q by
        refine ⟨⟨s, hs, rfl⟩, ?_, ?_⟩
        · intro i
          simp only [sub_self, abs_zero]
          exact mul_pos (by norm_num) hq.1
        · exact strictDense_center_mem_unit_velocityCube hq)
    rw [mem_inkSpotsQ2_iff] at hq2
    rw [windAmbientTime, mem_Ioo]
    exact (windForwardInterval_eligible heta hq).2.2.2 ⟨hq2.1, hq2.2.1⟩

private theorem hotTimeExpansion_contractedInterval
     :
    rightEndpointExpansion 0 (zeta ^ 2)⁻¹
        (inkSpotsTimeContraction eta zeta q '' windForwardInterval eta q) =
      windForwardInterval eta q := by
  let sharedTerm_f1ee201576 := (inkSpotsTerminalTime eta q - (q.baseTime + q.radius ^ 2))
  rw [inkSpotsTimeContraction_forwardInterval hzeta0]
  unfold rightEndpointExpansion windForwardInterval

  have hcontracted :
      inkSpotsTerminalTime eta q - zeta ^ 2 *
          (sharedTerm_f1ee201576) <
        inkSpotsTerminalTime eta q := by
    have hgap : 0 < sharedTerm_f1ee201576 := sub_pos.mpr (by
        rw [inkSpotsTerminalTime_eq]
        have hr : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
        field_simp [ne_of_gt heta]
        nlinarith)
    nlinarith [mul_pos (sq_pos_of_pos hzeta0) hgap]
  rw [csInf_Ioo hcontracted, csSup_Ioo hcontracted]
  congr 1
  rw [max_eq_right]
  · field_simp
    ring
  ·

    have hidentity : inkSpotsTerminalTime eta q - (zeta ^ 2)⁻¹ *
        (inkSpotsTerminalTime eta q -
          (inkSpotsTerminalTime eta q - zeta ^ 2 *
            (sharedTerm_f1ee201576))) =
        q.baseTime + q.radius ^ 2 := by
      field_simp [ne_of_gt (sq_pos_of_pos hzeta0)]
      ring
    rw [hidentity]
    exact add_nonneg (_root_.HypoellipticAleksandrov.Parabolic.strictDense_baseTime_nonneg hq) (sq_nonneg _)
end


section
variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : ℝ) (heta : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (v : PDE.Vec d)

include heta hzeta0 hzeta1
private theorem timeSection_inkSpotsD2_subset_expanded_hotTimeSections
     :
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
  exact ⟨_,
    ⟨q, hq, ht.2.2.1, ht.2.2.2, rfl⟩, rfl⟩
  rw [hotTimeExpansion_contractedInterval heta hzeta0 hzeta1 hq]
  exact ⟨ht.1, ht.2.1⟩

private theorem sUnion_hotTimeSectionFamily_bounded
     :
    Bornology.IsBounded (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (hotTimeInterval_eligible heta hzeta0 hzeta1 hq).2.2.2

private theorem volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
      :
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
      ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by


  calc
    volume (timeSection (inkSpotsD2 Gamma xi eta) v) ≤
        volume (⋃₀ (rightEndpointExpansion 0 (zeta ^ 2)⁻¹ ''
          hotTimeSectionFamily Gamma xi eta zeta v)) :=
      measure_mono (timeSection_inkSpotsD2_subset_expanded_hotTimeSections
        Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ ≤ ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (⋃₀ hotTimeSectionFamily Gamma xi eta zeta v) :=
      volume_sUnion_rightEndpointExpansion ((one_lt_inv₀ (sq_pos_of_pos hzeta0)).2 (by
          nlinarith [mul_pos hzeta0 (sub_pos.mpr hzeta1)])) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact hotTimeInterval_eligible heta hzeta0 hzeta1 hq)
        (sUnion_hotTimeSectionFamily_bounded Gamma xi eta zeta heta hzeta0 hzeta1 v)
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) := by
      rw [timeSection_inkSpotsD2TimeContractedUnion_eq_sUnion_hotTimeSectionFamily]
end


private theorem isOpen_inkSpotsQ2TimeContracted  {eta zeta : ℝ}
    (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2TimeContracted eta zeta q) := by
  rw [inkSpotsQ2TimeContracted, inkSpotsTimeContraction_forwardInterval hzeta0]
  exact isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : ℝ)

private theorem isOpen_inkSpotsD2TimeContractedUnion
     (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) := by
  rw [inkSpotsD2TimeContractedUnion]
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro _
  exact isOpen_inkSpotsQ2TimeContracted q hzeta0

private theorem volume_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted
     (heta : 0 < eta)
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
      lintegral_mono (volume_timeSection_inkSpotsD2_le_zeta_sq_inv_mul_timeContracted Gamma xi eta zeta heta hzeta0 hzeta1)
    _ = ENNReal.ofReal ((zeta ^ 2)⁻¹) *
        ∫⁻ v, volume (timeSection (inkSpotsD2TimeContractedUnion Gamma xi eta zeta) v) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! The remaining contractions are deliberately staged by prefix.  Keeping
the family of boxes under the union at every stage is essential: different
boxes meeting the same section have different velocity centres. -/

variable {d : Nat}

private def inkSpotsVelocityPrefixContraction
    (q : InkSpotsBox d) (zeta : Real) (k : Nat) (v : PDE.Vec d) : PDE.Vec d :=
  fun j => if j.1 < k then q.center j + zeta * (v j - q.center j) else v j

private def inkSpotsQ2PrefixContracted
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) : HypoellipticAleksandrov.Parabolic.Region d :=
  {z | ∃ y ∈ inkSpotsQ2 eta q,
    z.1 = inkSpotsTimeContraction eta zeta q y.1 ∧
      z.2 = inkSpotsVelocityPrefixContraction q zeta k y.2}

private def inkSpotsD2PrefixContractedUnion
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (k : Nat) :
    HypoellipticAleksandrov.Parabolic.Region d :=
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
      exact congrFun hv j
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
    · rfl

private theorem inkSpotsD2PrefixContractedUnion_zero_eq_timeContracted
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) :
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

      rw [hv]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos j.isLt]
  · rw [mem_inkSpotsQ3_iff]
    rintro ⟨y, hy, hcontraction⟩
    refine ⟨y, hy, ?_, ?_⟩
    · bound
    ·
      funext j

      rw [(congrArg Prod.snd hcontraction.symm)]
      dsimp [inkSpotsContraction]
      rw [inkSpotsVelocityPrefixContraction, if_pos j.isLt]

private theorem inkSpotsD2PrefixContractedUnion_eq_D3
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) :
    inkSpotsD2PrefixContractedUnion Gamma xi eta zeta d = inkSpotsD3 Gamma xi eta zeta := by
  simp only [inkSpotsD2PrefixContractedUnion, inkSpotsD3,
    inkSpotsQ2PrefixContracted_eq_Q3]

variable (c zeta : Real) (hzeta : zeta ≠ 0)

private def inkSpotsAffineHomeomorph  :
    Real ≃ₜ Real :=
  (Homeomorph.addLeft (-c)).trans
    ((Homeomorph.smulOfNeZero zeta hzeta).trans (Homeomorph.addLeft c))

private theorem inkSpotsAffineHomeomorph_apply
    (x : Real) :
    inkSpotsAffineHomeomorph c zeta hzeta x = c + zeta * (x - c) := by
  simp [inkSpotsAffineHomeomorph, Homeomorph.addLeft, Homeomorph.smulOfNeZero]
  ring

private def inkSpotsPrefixHomeomorph {d : Nat} (eta zeta : Real) (k : Nat)
    (q : InkSpotsBox d) (hzeta : zeta ≠ 0) : TimeVelocity d ≃ₜ TimeVelocity d :=
  (inkSpotsAffineHomeomorph (inkSpotsTerminalTime eta q) (zeta ^ 2)
    (pow_ne_zero _ hzeta)).prodCongr
    (Homeomorph.piCongrRight fun j =>
      if _ : j.1 < k then inkSpotsAffineHomeomorph (q.center j) zeta hzeta
      else Homeomorph.refl Real)

private theorem inkSpotsPrefixHomeomorph_apply {d : Nat} (eta zeta : Real) (k : Nat)
    (q : InkSpotsBox d) (hzeta : zeta ≠ 0) (y : TimeVelocity d) :
    inkSpotsPrefixHomeomorph eta zeta k q hzeta y =
      (inkSpotsTimeContraction eta zeta q y.1,
        inkSpotsVelocityPrefixContraction q zeta k y.2) := by
  apply Prod.ext
  · change inkSpotsAffineHomeomorph (inkSpotsTerminalTime eta q) (zeta ^ 2)
      (pow_ne_zero _ hzeta) y.1 = _
    rw [show inkSpotsTimeContraction eta zeta q y.1 =
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
      simp only [Homeomorph.refl_apply, inkSpotsVelocityPrefixContraction, if_neg hj]
      rfl

private theorem inkSpotsQ2PrefixContracted_eq_homeomorph_image {d : Nat}
    (eta zeta : Real) (k : Nat) (q : InkSpotsBox d) (hzeta : zeta ≠ 0) :
    inkSpotsQ2PrefixContracted eta zeta k q =
      inkSpotsPrefixHomeomorph eta zeta k q hzeta '' inkSpotsQ2 eta q := by
  ext z
  constructor
  · rintro ⟨y, hy, ht, hv⟩
    refine ⟨y, hy, ?_⟩
    rw [inkSpotsPrefixHomeomorph_apply]
    exact Prod.ext ht.symm hv.symm
  · rintro ⟨y, hy, hzy⟩
    refine ⟨y, hy, ?_, ?_⟩
    have hcomponents := congrArg Prod.fst hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    exact hcomponents.symm
    have hcomponents := congrArg Prod.snd hzy
    rw [inkSpotsPrefixHomeomorph_apply] at hcomponents
    exact hcomponents.symm

private theorem isOpen_inkSpotsQ2PrefixContracted {d : Nat} {eta zeta : Real}
    (k : Nat) (q : InkSpotsBox d) (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsQ2PrefixContracted eta zeta k q) := by
  rw [inkSpotsQ2PrefixContracted_eq_homeomorph_image eta zeta k q hzeta0.ne']
  exact (inkSpotsPrefixHomeomorph eta zeta k q hzeta0.ne').isOpenMap _
    (isOpen_inkSpotsQ2 eta q)

private theorem isOpen_inkSpotsD2PrefixContractedUnion {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (k : Nat)
    (hzeta0 : 0 < zeta) :
    IsOpen (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  rw [inkSpotsD2PrefixContractedUnion]
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

private theorem mem_timeVelocityCoordinateSection_succ_iff {d : Nat} (j : Fin d)
    (S : HypoellipticAleksandrov.Parabolic.Region d) (w : Fin d → Real) (x : Real) :
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

private theorem timeVelocityCoordinateEquiv_sectionPoint {d : Nat} (j : Fin d)
    (x : Real) (w : Fin d → Real) :
    timeVelocityCoordinateEquiv d (inkSpotsVelocitySectionPoint j x w) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Real)
        (Fin.succ j)).symm (x, w) := by
  simp [inkSpotsVelocitySectionPoint]

private theorem sectionPoint_velocity_eq {d : Nat} (j : Fin d) (x : Real)
    (w : Fin d → Real) : (inkSpotsVelocitySectionPoint j x w).2 j = x := by
  simp [inkSpotsVelocitySectionPoint, timeVelocityCoordinateEquiv, Fin.tail]

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
      (inkSpotsVelocitySectionPoint j y w).1 := rfl

private def inkSpotsPrefixCoordinateSectionFamily {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    I = timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta k q) w ∧ I.Nonempty}

private theorem timeVelocityCoordinateSection_prefixUnion_eq_sUnion_family {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (k : Nat) (j : Fin d)
    (w : Fin d → Real) :
    timeVelocityCoordinateSection d (Fin.succ j)
        (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) w =
      ⋃₀ inkSpotsPrefixCoordinateSectionFamily Gamma xi eta zeta k j w := by
  ext x
  rw [mem_timeVelocityCoordinateSection_succ_iff]
  constructor
  · intro hx
    rw [inkSpotsD2PrefixContractedUnion] at hx
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
    rw [inkSpotsD2PrefixContractedUnion]
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq, hxI⟩⟩

private def inkSpotsHotCoordinateInterval {d : Nat} (q : InkSpotsBox d)
    (j : Fin d) : Set Real :=
  Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1

private theorem inkSpotsHotCoordinateInterval_eligible {d : Nat}
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi : Real} {q : InkSpotsBox d}
    (hq : q ∈ inkSpotsDenseBoxes Gamma xi) (j : Fin d) :
    IsOpenSubinterval (Ioo (-1 : Real) 1) (inkSpotsHotCoordinateInterval q j) := by

  have hr  := hq.1
  refine ⟨⟨q.center j, ⟨?_, (strictDense_center_coord_bounds hq j)⟩⟩, isOpen_Ioo.inter isOpen_Ioo,
    ordConnected_Ioo.inter ordConnected_Ioo, inter_subset_right⟩
  constructor <;> nlinarith

private theorem section_prefix_eq_hotInterval_of_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
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
    simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
      lt_self_iff_false, if_false] at hcoord
    rw [inkSpotsHotCoordinateInterval, hcoord]
    have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)

    exact ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, (show -1 < y.2 j ∧ y.2 j < 1 by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j))⟩
  · intro hx
    rw [inkSpotsHotCoordinateInterval] at hx
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then x else y₀.2 l


    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨hy₀'.1, hy₀'.2.1, (by
          rw [mem_velocityCube_iff]
          intro l
          by_cases hlj : l = j
          · subst l
            simp only [v, if_pos]
            exact abs_lt.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
          · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.1 l), (by
          rw [mem_velocityCube_iff]
          intro l
          by_cases hlj : l = j
          · subst l
            simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hx.2
          · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.2 l)⟩
    · assumption
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

private theorem section_prefix_succ_eq_contraction_image_of_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
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
    · rw [inkSpotsHotCoordinateInterval]
      have hc := abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.1 j)
      have hu : -1 < y.2 j ∧ y.2 j < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy.2.2.2 j)
      exact ⟨⟨by linarith [hc.1], by linarith [hc.2]⟩, hu⟩
    · have hcoord := congrFun hv j
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
        Nat.lt_succ_self, if_true] at hcoord
      exact hcoord.symm
  · rintro ⟨u, hu, rfl⟩
    rw [inkSpotsHotCoordinateInterval] at hu
    rw [mem_timeVelocityCoordinateSection_succ_iff]
    let v : PDE.Vec d := fun l => if l = j then u else y₀.2 l


    refine ⟨(y₀.1, v), ?_, ?_, ?_⟩
    · rw [mem_inkSpotsQ2_iff]
      exact ⟨hy₀'.1, hy₀'.2.1, (show v ∈ velocityCube q.center (3 * q.radius) by
          rw [mem_velocityCube_iff]
          intro l
          by_cases hlj : l = j
          · subst l
            simp only [v, if_pos]
            exact abs_lt.mpr ⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩
          · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.1 l), (show v ∈ velocityCube 0 1 by
          rw [mem_velocityCube_iff]
          intro l
          by_cases hlj : l = j
          · subst l
            simpa only [v, if_pos, Pi.zero_apply, sub_zero] using abs_lt.mpr hu.2
          · simpa only [v, if_neg hlj] using mem_velocityCube_iff.mp hy₀'.2.2.2 l)⟩
    · assumption
    · funext l
      by_cases hlj : l = j
      · subst l
        simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
          Nat.lt_succ_self, v, if_pos, centeredCoordinateContraction]
      · calc
          (inkSpotsVelocitySectionPoint j
              (centeredCoordinateContraction (q.center j) zeta u) w).2 l =
              (inkSpotsVelocitySectionPoint j x₀ w).2 l :=
                sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
          _ = inkSpotsVelocityPrefixContraction q zeta j.1 y₀.2 l := congrFun hv₀ l
          _ = inkSpotsVelocityPrefixContraction q zeta (j.1 + 1) v l := by
            by_cases hl : l.1 < j.1
            ·
              simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos (hl.trans (Nat.lt_succ_self _)),
                v, if_neg hlj]
            ·
              simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg (show ¬ l.1 < j.1 + 1 by omega),
                v, if_neg hlj]

private theorem section_prefix_nonempty_of_succ_nonempty {d : Nat}
    (eta zeta : Real) (q : InkSpotsBox d) (j : Fin d) (w : Fin d → Real)
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
  · exact (sectionPoint_time_eq j (y.2 j) x w).trans ht
  · funext l
    by_cases hlj : l = j
    · subst l
      simp only [sectionPoint_velocity_eq, inkSpotsVelocityPrefixContraction,
        lt_self_iff_false, if_false]
    · calc
        (inkSpotsVelocitySectionPoint j (y.2 j) w).2 l =
            (inkSpotsVelocitySectionPoint j x w).2 l :=
              sectionPoint_velocity_eq_of_ne _ _ _ _ _ hlj
        _ = inkSpotsVelocityPrefixContraction q zeta (j.1 + 1) y.2 l := congrFun hv l
        _ = inkSpotsVelocityPrefixContraction q zeta j.1 y.2 l := by
          by_cases hl : l.1 < j.1
          ·
            simp only [inkSpotsVelocityPrefixContraction, if_pos hl, if_pos (hl.trans (Nat.lt_succ_self _))]
          ·
            simp only [inkSpotsVelocityPrefixContraction, if_neg hl, if_neg (show ¬ l.1 < j.1 + 1 by omega)]

private def hotVelocitySectionFamily {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) : Set (Set Real) :=
  {I | ∃ q ∈ inkSpotsDenseBoxes Gamma xi,
    (timeVelocityCoordinateSection d (Fin.succ j)
      (inkSpotsQ2PrefixContracted eta zeta j.1 q) w).Nonempty ∧
    I = centeredCoordinateContraction (q.center j) zeta ''
      inkSpotsHotCoordinateInterval q j}

private theorem section_prefix_succ_union_eq_sUnion_hotVelocityFamily {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) :
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

private theorem section_prefix_union_eq_sUnion_expanded_hotVelocityFamily {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
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
        (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
          (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)
    exact mem_sUnion.2 ⟨boundaryShiftedMidpointExpansion zeta⁻¹ K,
      ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, by rw [hrecover]; exact hxI⟩
  · rintro hx
    rcases mem_sUnion.1 hx with ⟨E, ⟨K, ⟨q, hq, hpre, rfl⟩, rfl⟩, hxE⟩
    change x ∈ boundaryShiftedMidpointExpansion zeta⁻¹
      ((fun u  => q.center j + zeta * (u - q.center j)) ''
        (Ioo (q.center j - 3 * q.radius) (q.center j + 3 * q.radius) ∩ Ioo (-1) 1))
      at hxE
    rw [boundaryShiftedMidpointExpansion_image_centeredInterval_inter
      (q.center j) (3 * q.radius) zeta hzeta0 hzeta1
        (strictDense_center_coord_bounds hq j) (mul_pos (by norm_num) hq.1)] at hxE
    have hxJ : x ∈ inkSpotsHotCoordinateInterval q j := hxE
    rw [← section_prefix_eq_hotInterval_of_nonempty eta zeta q j w hpre] at hxJ
    exact mem_sUnion.2 ⟨_, ⟨q, hq, rfl, hpre⟩, hxJ⟩

private theorem hotVelocitySectionFamily_eligible {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real) (j : Fin d)
    (w : Fin d → Real) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    ∀ I ∈ hotVelocitySectionFamily Gamma xi eta zeta j w,
      IsOpenSubinterval (Ioo (-1 : Real) 1) I := by
  rintro I ⟨q, hq, _, rfl⟩

  have hr  := hq.1
  exact (isClippedCoordinateInterval_centeredCoordinateContraction_image
    (q.center j) zeta hzeta0 hzeta1
      ⟨inkSpotsHotCoordinateInterval_eligible hq j,
        ⟨⟨by nlinarith, by nlinarith⟩, (strictDense_center_coord_bounds hq j)⟩⟩).1

private theorem volume_prefix_spatial_step {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) {k : Nat} (hk : k < d) :
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
    _
    (hotVelocitySectionFamily_eligible Gamma xi eta zeta j w hzeta0 hzeta1)
  aesop

private theorem volume_prefix_spatial_contraction {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (k : Nat) (hk : k ≤ d) :
    volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
      (ENNReal.ofReal zeta⁻¹) ^ k *
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) := by
  induction k with
  | zero => simp
  | succ k ih =>

      calc
        volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta 0) ≤
            (ENNReal.ofReal zeta⁻¹) ^ k *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta k) :=
          ih (Nat.le_of_succ_le hk)
        _ ≤ (ENNReal.ofReal zeta⁻¹) ^ k *
              (ENNReal.ofReal zeta⁻¹ *
                volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1))) :=
          mul_le_mul_right (volume_prefix_spatial_step Gamma xi eta zeta
            hzeta0 hzeta1 (Nat.lt_of_succ_le hk)) _
        _ = (ENNReal.ofReal zeta⁻¹) ^ (k + 1) *
              volume (inkSpotsD2PrefixContractedUnion Gamma xi eta zeta (k + 1)) := by
          rw [pow_succ]
          ac_rfl

private theorem inkSpotsQ2PrefixContracted_subset_Q2 {d : Nat}
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta zeta : Real} {q : InkSpotsBox d}
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
  · rw [mem_velocityCube_iff]
    intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hyc := mem_velocityCube_iff.mp hy'.2.2.1 l
      rw [show q.center l + zeta * (y.2 l - q.center l) - q.center l =
        zeta * (y.2 l - q.center l) by ring, abs_mul, abs_of_pos hzeta0]
      nlinarith [abs_nonneg (y.2 l - q.center l)]
    · rw [if_neg hl]
      exact mem_velocityCube_iff.mp hy'.2.2.1 l
  · rw [mem_velocityCube_iff]
    intro l
    rw [hv, inkSpotsVelocityPrefixContraction]
    by_cases hl : l.1 < k
    · rw [if_pos hl]
      have hc := strictDense_center_coord_bounds hq l
      have hyv : -1 < y.2 l ∧ y.2 l < 1 := by
        simpa only [Pi.zero_apply, sub_zero] using
          abs_lt.mp (mem_velocityCube_iff.mp hy'.2.2.2 l)
      rw [Pi.zero_apply, sub_zero, abs_lt]
      constructor <;> nlinarith
    · rw [if_neg hl]
      exact mem_velocityCube_iff.mp hy'.2.2.2 l

private theorem inkSpotsD3_subset_D2 {d : Nat}
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : Real)
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

private alias isBounded_velocityCube := _root_.HypoellipticAleksandrov.Parabolic.isBounded_velocityCube





private theorem hotWind_scalar_identity (zeta : Real) (hzeta : zeta ≠ 0) (d : Nat) :
    ((zeta ^ 2)⁻¹) * (zeta⁻¹) ^ d = zeta ^ (-((d : Int) + 2)) := by
  have htime : (zeta ^ 2)⁻¹ = zeta ^ (-2 : Int) :=
    (zpow_neg zeta (2 )).symm
  have hspace : (zeta⁻¹) ^ d = zeta ^ (-(d : Int)) := by
    rw [inv_pow, ← zpow_natCast]
    exact (zpow_neg zeta (d : Int)).symm
  rw [htime, hspace, ← zpow_add₀ hzeta]
  congr 1
  omega

/-- Krylov--Safonov, Lemma 2.4 (hot wind): the forward source union is controlled by
its terminal contraction in time and every velocity coordinate. -/
theorem volume_inkSpotsD2_toReal_le_zeta_zpow_mul_D3
    {d : ℕ} (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta zeta : ℝ)
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

  have hD3finite : volume (inkSpotsD3 Gamma xi eta zeta) ≠ ∞ :=
    ne_top_of_le_ne_top (_root_.HypoellipticAleksandrov.Parabolic.volume_inkSpotsD2_ne_top Gamma xi eta heta)
      (measure_mono (inkSpotsD3_subset_D2 Gamma xi eta zeta hzeta0 hzeta1))
  have hfinite : ((ENNReal.ofReal ((zeta ^ 2)⁻¹) * ((ENNReal.ofReal zeta⁻¹) ^ d * volume (inkSpotsD3 Gamma xi eta zeta)))) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hD3finite)
  have hreal := ENNReal.toReal_mono hfinite ((Trans.trans htime (mul_le_mul_right hspace (ENNReal.ofReal (zeta ^ 2)⁻¹))))
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (zeta ^ 2)⁻¹),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ zeta⁻¹), ← mul_assoc,
    hotWind_scalar_identity zeta hzeta0.ne' d] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic
