module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import HypoellipticAleksandrov.Measure.IntervalUnion
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Prod
import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Wind estimate for source ink spots

This module proves the measure-theoretic wind estimate of Krylov--Safonov, Lemma 2.3 in
Section 2 of Krylov--Safonov. It applies the interval-union lemma on concrete
time sections and then integrates those section inequalities.
-/

@[expose] public section

noncomputable section

open Function MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

private theorem strictDense_timeInterval_subset_unit {d Gamma xi} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    Ioo q.baseTime (q.baseTime + q.radius ^ 2) ⊆ Ioo 0 1 := by
  have hr := hq.1
  intro t ht
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    rw [mem_inkSpotsSourceBox_iff]
    refine ⟨ht.1, ht.2, ?_⟩
    · intro i
      simp only [sub_self, abs_zero]
      exact hr
  have htUnit := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  constructor
  · exact htUnit.1
  · convert htUnit.2.1 using 1
    norm_num

private theorem strictDense_baseTime_nonneg {d Gamma xi} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    0 ≤ q.baseTime := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.1

private theorem strictDense_baseTime_add_sq_le_one {d Gamma xi} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    q.baseTime + q.radius ^ 2 ≤ 1 := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.2

private def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

private def windAmbientVelocity (d : ℕ) : Set (PDE.Vec d) :=
  velocityCube (0 : PDE.Vec d) 1

private def windAmbient (d : ℕ) (eta : ℝ) : Set (TimeVelocity d) :=
  windAmbientTime eta ×ˢ windAmbientVelocity d

private theorem inkSpotsQ2_subset_windAmbient {d eta Gamma xi q}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ2 eta q ⊆ windAmbient d eta := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsQ2_iff] at hz
  refine ⟨?_, hz.2.2.2⟩
  constructor
  · have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    nlinarith [sq_pos_of_pos hq.1]
  · have htop : q.baseTime + q.radius ^ 2 ≤ 1 :=
      strictDense_baseTime_add_sq_le_one hq
    have hbase := strictDense_baseTime_nonneg hq
    have hsquare : q.radius ^ 2 ≤ 1 := by nlinarith [hbase]
    rw [inkSpotsTerminalTime_eq] at hz
    have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
      rw [div_le_div_iff_of_pos_right heta]
      nlinarith
    exact hz.2.1.trans_le (by linarith)

private def windForwardInterval {d } (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)

/- The uncut right-end expansion of a forward stack.  The first source
enlargement is later clipped by the reference unit box. -/
private def windExpandedInterval {d } (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime - 3 * q.radius ^ 2) (inkSpotsTerminalTime eta q)

private theorem isOpen_ordConnected_eq_Ioo_csInf_csSup (I : Set ℝ)
    (hIopen : IsOpen I) (hIord : I.OrdConnected) (hInonempty : I.Nonempty)
    (hIbelow : BddBelow I) (hIabove : BddAbove I) :
    I = Ioo (sInf I) (sSup I) := by
  apply Subset.antisymm
  · intro x hx
    have hinf := csInf_le hIbelow hx
    have hsup := le_csSup hIabove hx
    constructor
    · by_contra hnot
      have hxeq := le_antisymm (le_of_not_gt hnot) hinf
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hleft := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x - eps / 2) - x| = eps / 2 := by
          rw [show (x - eps / 2) - x = -(eps / 2) by ring, abs_neg,
            abs_of_pos (by linarith)]
        rw [habs]
        linarith)
      have hle := csInf_le hIbelow hleft
      rw [← hxeq] at hle
      linarith
    · by_contra hnot
      have hxeq := le_antisymm (le_of_not_gt hnot) hsup
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hright := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x + eps / 2) - x| = eps / 2 := by
          rw [show (x + eps / 2) - x = eps / 2 by ring,
            abs_of_pos (by linarith)]
        rw [habs]
        linarith)
      have hle := le_csSup hIabove hright
      rw [hxeq] at hle
      linarith
  · exact IsConnected.Ioo_csInf_csSup_subset
      ⟨hInonempty, hIord.isPreconnected⟩ hIbelow hIabove

/- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
private def rightEndpointExpansion (a kappa : ℝ) (I : Set ℝ) : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)

private theorem volume_sUnion_rightEndpointExpansion {a b kappa }
    (hkappa : 1 < kappa) (B )
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo a b)
    isOpen_Ioo ordConnected_Ioo B (rightEndpointExpansion a kappa) hB hbounded
  · intro I hI
    have hIbelow : BddBelow I :=
      ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩
    have hIabove : BddAbove I :=
      ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
    have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
      hI.1 hIbelow hIabove
    have hlt : sInf I < sSup I := by
      rw [hIeq] at hI
      exact nonempty_Ioo.mp hI.1
    have hupper : sSup I ≤ b := by
      rcases hI.1 with ⟨x, hx⟩
      apply (csSup_le_iff hIabove ⟨x, hx⟩).2
      intro y hy
      exact (hI.2.2.2 hy).2.le
    have haUpper : a < sSup I := by
      rcases hI.1 with ⟨x, hx⟩
      exact (hI.2.2.2 hx).1.trans_le (le_csSup hIabove hx)
    unfold rightEndpointExpansion
    constructor
    · refine nonempty_Ioo.mpr (max_lt ?_ ?_)
      · exact haUpper
      · have hproduct : 0 < kappa * (sSup I - sInf I) :=
          mul_pos (zero_lt_one.trans hkappa) (sub_pos.mpr hlt)
        linarith
    constructor
    · exact isOpen_Ioo
    constructor
    · exact ordConnected_Ioo
    · exact Ioo_subset_Ioo (le_max_left _ _) hupper
  · intro I hI _
    have hkappa := hkappa.le
    have hIbelow : BddBelow I :=
      ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩
    have hIabove : BddAbove I :=
      ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
    have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
      hI.1 hIbelow hIabove
    have hlt : sInf I < sSup I := by
      rw [hIeq] at hI
      exact nonempty_Ioo.mp hI.1
    rw [hIeq, rightEndpointExpansion, csInf_Ioo hlt, csSup_Ioo hlt,
      Real.volume_Ioo, Real.volume_Ioo]
    rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa)]
    apply ENNReal.ofReal_le_ofReal
    have hleft : sSup I - kappa * (sSup I - sInf I) ≤
        max a (sSup I - kappa * (sSup I - sInf I)) := le_max_right _ _
    nlinarith
  · intro I₁ I₂ hI₁ hI₂ hsub
    have hI₂below : BddBelow I₂ :=
      ⟨a, fun x hx => (hI₂.2.2.2 hx).1.le⟩
    have hI₁above : BddAbove I₁ :=
      ⟨b, fun x hx => (hI₁.2.2.2 hx).2.le⟩
    have hI₂above : BddAbove I₂ :=
      ⟨b, fun x hx => (hI₂.2.2.2 hx).2.le⟩
    have hI₁nonempty := hI₁.1
    have hkappa := hkappa.le
    have hinf : sInf I₂ ≤ sInf I₁ := by
      apply le_csInf hI₁nonempty
      intro x hx
      exact csInf_le hI₂below (hsub hx)
    have hsup : sSup I₁ ≤ sSup I₂ := by
      apply (csSup_le_iff hI₁above hI₁nonempty).2
      intro x hx
      exact le_csSup hI₂above (hsub hx)
    unfold rightEndpointExpansion
    apply Ioo_subset_Ioo
    · apply max_le_max_left
      nlinarith
    · exact hsup

private def timeSection {d } (S : Set (TimeVelocity d)) (v : PDE.Vec d) : Set ℝ :=
  {t | (t, v) ∈ S}

private def windSectionFamily {d } (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) (v : PDE.Vec d) : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = windForwardInterval eta q}

private theorem windForwardInterval_eligible {d Gamma xi eta} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta) (windForwardInterval eta q) := by
  constructor
  · apply nonempty_Ioo.mpr
    rw [inkSpotsTerminalTime_eq]
    have hsquare := sq_pos_of_pos hq.1
    field_simp
    nlinarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have hbase := strictDense_baseTime_nonneg hq
    have htop :=
      strictDense_baseTime_add_sq_le_one hq
    have hsquare : q.radius ^ 2 ≤ 1 := by nlinarith
    rw [windForwardInterval, mem_Ioo] at ht
    rw [windAmbientTime, mem_Ioo]
    constructor
    · nlinarith [sq_pos_of_pos hq.1]
    · rw [inkSpotsTerminalTime_eq] at ht
      have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
        rw [div_le_div_iff_of_pos_right heta]
        nlinarith
      exact ht.2.trans_le (by linarith)

private theorem timeSection_inkSpotsD1_subset_expanded_windSections {d Gamma xi eta} (heta : 0 < eta)
    (heta1 : eta < 1) (v : PDE.Vec d) :
    timeSection (inkSpotsD1 Gamma xi) v ⊆
      ⋃₀ (rightEndpointExpansion 0 (1 + eta) ''
        windSectionFamily Gamma xi eta v) := by
  intro t ht
  rw [timeSection, inkSpotsD1] at ht
  rcases mem_iUnion.1 ht with ⟨q, ht⟩
  rcases mem_iUnion.1 ht with ⟨hq, ht⟩
  have htQ1 := ht
  rw [mem_inkSpotsQ1_iff] at ht
  have hExpanded : t ∈ windExpandedInterval eta q := by
    rw [mem_inkSpotsQ1_iff] at htQ1
    rw [windExpandedInterval, mem_Ioo]
    constructor
    · exact htQ1.1
    · rw [inkSpotsTerminalTime_eq]
      norm_num at htQ1
      have hr := hq.1
      have hdiv : 4 * q.radius ^ 2 ≤ 4 * q.radius ^ 2 / eta := by
        rw [le_div_iff₀ heta]
        nlinarith [sq_pos_of_pos hr]
      linarith
  have hUnitTime : 0 < t := by
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at ht
    exact ht.2.2.2.1
  have hUnitVelocity : v ∈ velocityCube (0 : PDE.Vec d) 1 := by
    have hUnit := ht.2.2.2
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hUnit
    exact hUnit.2.2
  have hExpanded' : t ∈ rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q) := by
    have _h_inl_22 : rightEndpointExpansion 0 (1 + eta) (windForwardInterval eta q) =
      Ioo (max 0 (q.baseTime - 3 * q.radius ^ 2))
        (inkSpotsTerminalTime eta q) := by
      unfold rightEndpointExpansion windForwardInterval
      have hnonempty : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
        rw [inkSpotsTerminalTime_eq]
        have hsquare := sq_pos_of_pos hq.1
        field_simp
        nlinarith
      rw [csInf_Ioo hnonempty, csSup_Ioo hnonempty]
      congr 2
      rw [inkSpotsTerminalTime_eq]
      field_simp
      ring
    rw [_h_inl_22]
    rw [windExpandedInterval, mem_Ioo] at hExpanded
    constructor
    · exact max_lt hUnitTime hExpanded.1
    · exact hExpanded.2
  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q), ?_, hExpanded'⟩
  exact ⟨windForwardInterval eta q,
    ⟨q, hq, ht.2.2.1, hUnitVelocity, rfl⟩, rfl⟩

private theorem sUnion_windSectionFamily_bounded {d }
    (Gamma : Set (TimeVelocity d)) (xi eta : ℝ) (heta : 0 < eta)
    (v : PDE.Vec d) :
    Bornology.IsBounded (⋃₀ windSectionFamily Gamma xi eta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (windForwardInterval_eligible heta hq).2.2.2

private theorem volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2 {d }
    (Gamma : Set (TimeVelocity d)) (xi eta : ℝ) (heta : 0 < eta)
    (heta1 : eta < 1) (v : PDE.Vec d) :
    volume (timeSection (inkSpotsD1 Gamma xi) v) ≤
      ENNReal.ofReal (1 + eta) *
        volume (timeSection (inkSpotsD2 Gamma xi eta) v) := by
  calc
    volume (timeSection (inkSpotsD1 Gamma xi) v) ≤
        volume (⋃₀ (rightEndpointExpansion 0 (1 + eta) ''
          windSectionFamily Gamma xi eta v)) :=
      measure_mono (timeSection_inkSpotsD1_subset_expanded_windSections heta heta1 v)
    _ ≤ ENNReal.ofReal (1 + eta) *
        volume (⋃₀ windSectionFamily Gamma xi eta v) :=
      volume_sUnion_rightEndpointExpansion (by linarith) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact windForwardInterval_eligible heta hq)
        (sUnion_windSectionFamily_bounded Gamma xi eta heta v)
    _ = ENNReal.ofReal (1 + eta) *
        volume (timeSection (inkSpotsD2 Gamma xi eta) v) := by
      have _h_inl_25 (Gamma : Set (TimeVelocity d)) (xi : ℝ) (eta : ℝ) (v) : timeSection (inkSpotsD2 Gamma xi eta) v = ⋃₀ (windSectionFamily Gamma xi eta v) := by
        ext t
        constructor
        · intro ht
          rw [timeSection, inkSpotsD2] at ht
          rcases mem_iUnion.1 ht with ⟨q, ht⟩
          rcases mem_iUnion.1 ht with ⟨hq, ht⟩
          rw [mem_inkSpotsQ2_iff] at ht
          refine mem_sUnion.2 ⟨windForwardInterval eta q, ?_, ⟨ht.1, ht.2.1⟩⟩
          exact ⟨q, hq, ht.2.2.1, ht.2.2.2, rfl⟩
        · intro ht
          rcases mem_sUnion.1 ht with ⟨I, hI, ht⟩
          rcases hI with ⟨q, hq, hvCenter, hvUnit, rfl⟩
          rw [timeSection, inkSpotsD2]
          exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
            (mem_inkSpotsQ2_iff).2 ⟨ht.1, ht.2, hvCenter, hvUnit⟩⟩⟩
      rw [_h_inl_25]

private theorem volume_eq_lintegral_timeSection {d } (S : Set (TimeVelocity d))
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

theorem volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2
    {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta : ℝ)
    (heta : 0 < eta) (heta1 : eta < 1) :
    (volume (inkSpotsD1 Gamma xi)).toReal ≤
      (1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal := by
  have hmeasure : volume (inkSpotsD1 Gamma xi) ≤
      ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) := by
    have _h_xinl_0 : MeasurableSet (inkSpotsD1 Gamma xi) := by
        exact (
      (isOpen_inkSpotsD1 Gamma xi).measurableSet

      /- The source \(D^2\) is open. -/
      )
    rw [volume_eq_lintegral_timeSection _ _h_xinl_0,
      volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta)]
    calc
      (∫⁻ v, volume (timeSection (inkSpotsD1 Gamma xi) v)) ≤
          ∫⁻ v, ENNReal.ofReal (1 + eta) *
            volume (timeSection (inkSpotsD2 Gamma xi eta) v) :=
        lintegral_mono fun v =>
          volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2 Gamma xi eta heta heta1 v
      _ = ENNReal.ofReal (1 + eta) *
          ∫⁻ v, volume (timeSection (inkSpotsD2 Gamma xi eta) v) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have _h_inl_30 : volume (inkSpotsD2 Gamma xi eta) ≠ ∞ := by
    apply ne_of_lt
    have _h_inl_17 : inkSpotsD2 Gamma xi eta ⊆ windAmbient d eta := by
        intro z hz
        rw [inkSpotsD2] at hz
        rcases mem_iUnion.1 hz with ⟨q, hz⟩
        rcases mem_iUnion.1 hz with ⟨hq, hz⟩
        exact inkSpotsQ2_subset_windAmbient heta hq hz


    apply lt_of_le_of_lt (measure_mono _h_inl_17)
    apply Bornology.IsBounded.measure_lt_top
    have _h_inl_31 : Bornology.IsBounded (velocityCube (0 : PDE.Vec d) 1) := by
      let v₀ := (0 : PDE.Vec d)
      apply (isCompact_velocityClosedCube v₀ 1).isBounded.subset
      intro v hv i
      exact le_of_lt (hv i)
    exact (Metric.isBounded_Ioo 0 (1 + 4 / eta)).prod
      _h_inl_31
  have hfinite : ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      _h_inl_30
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic
