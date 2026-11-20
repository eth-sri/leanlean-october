module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import HypoellipticAleksandrov.Measure.IntervalUnion
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Prod

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

section
variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q)
include hq

private theorem strictDense_timeInterval_subset_unit :
    Ioo q.baseTime (q.baseTime + q.radius ^ 2) ⊆ Ioo 0 1 := by
  intro t ht
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    rw [mem_inkSpotsSourceBox_iff]
    refine ⟨ht.1, ht.2, ?_⟩
    · intro i
      simp only [sub_self, abs_zero]
      exact (hq.1)
  have htUnit := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  grind

private theorem strictDense_baseTime_nonneg :
    0 ≤ q.baseTime := by
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp (strictDense_timeInterval_subset_unit hq) |>.1

private theorem strictDense_baseTime_add_sq_le_one :
    q.baseTime + q.radius ^ 2 ≤ 1 := by
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp (strictDense_timeInterval_subset_unit hq) |>.2

end

private def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

private def windAmbientVelocity (d : ℕ) : Set (PDE.Vec d) :=
  velocityCube (0 : PDE.Vec d) 1

private def windAmbient (d : ℕ) (eta : ℝ) : Set (TimeVelocity d) :=
  windAmbientTime eta ×ˢ windAmbientVelocity d

section
variable {d : ℕ} (a kappa : ℝ) {Gamma : Set (TimeVelocity d)} (I : Set ℝ) {xi eta : ℝ}

private theorem inkSpotsQ2_subset_windAmbient {eta : ℝ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ2 eta q ⊆ windAmbient d eta := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsQ2_iff] at hz
  refine ⟨?_, hz.2.2.2⟩
  constructor
  · nlinarith [strictDense_baseTime_nonneg hq]
  · have htop :=
      strictDense_baseTime_add_sq_le_one hq
    have hbase := strictDense_baseTime_nonneg hq
    rw [inkSpotsTerminalTime_eq] at hz
    have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
      rw [div_le_div_iff_of_pos_right heta]
      nlinarith
    linarith

private theorem inkSpotsD2_subset_windAmbient (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) (heta : 0 < eta) :
    inkSpotsD2 Gamma xi eta ⊆ windAmbient d eta := by
  intro z hz
  rw [inkSpotsD2] at hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  exact inkSpotsQ2_subset_windAmbient heta hq hz

/-- The time section of a forward source stack. -/
private def windForwardInterval (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)

/-- The uncut right-end expansion of a forward stack.  The first source
enlargement is later clipped by the reference unit box. -/
private def windExpandedInterval (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime - 3 * q.radius ^ 2) (inkSpotsTerminalTime eta q)

private theorem inkSpotsQ1_time_mem_windExpandedInterval {q : InkSpotsBox d} {t : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hq : inkSpotsStrictDense Gamma xi q)
    {v : PDE.Vec d} (ht : (t, v) ∈ inkSpotsQ1 q) :
    t ∈ windExpandedInterval eta q := by
  rw [mem_inkSpotsQ1_iff] at ht
  rw [windExpandedInterval, mem_Ioo]
  constructor
  · exact ht.1
  · rw [inkSpotsTerminalTime_eq]
    norm_num at ht
    have hr := hq.1
    have hdiv : 4 * q.radius ^ 2 ≤ 4 * q.radius ^ 2 / eta := by
      bound
    linarith

private theorem isOpen_ordConnected_eq_Ioo_csInf_csSup
    (hIopen : IsOpen I) (hIord : I.OrdConnected) (hInonempty : I.Nonempty)
    (hIbelow : BddBelow I) (hIabove : BddAbove I) :
    I = Ioo (sInf I) (sSup I) := by
  apply Subset.antisymm
  · intro x hx
    constructor
    · by_contra hnot
      have hxeq := le_antisymm (le_of_not_gt hnot) (csInf_le hIbelow hx)
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hleft := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x - eps / 2) - x| = eps / 2 := by
          grind
        linarith)
      have hle := csInf_le hIbelow hleft
      linarith
    · by_contra hnot
      have hxeq := le_antisymm (le_of_not_gt hnot) (le_csSup hIabove hx)
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hright := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        have habs : |(x + eps / 2) - x| = eps / 2 := by
          grind
        linarith)
      have hle := le_csSup hIabove hright
      linarith
  · exact IsConnected.Ioo_csInf_csSup_subset
      ⟨hInonempty, hIord.isPreconnected⟩ hIbelow hIabove

include a kappa I in
/-- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
private def rightEndpointExpansion : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)

private theorem rightEndpointExpansion_forwardInterval (q : InkSpotsBox d)
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (1 + eta) (windForwardInterval eta q) =
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

end

private theorem rightEndpointExpansion_mono_of_subset {a kappa : ℝ}
    {I₁ I₂ : Set ℝ} (hI₁nonempty : I₁.Nonempty) (hI₂below : BddBelow I₂)
    (hI₁above : BddAbove I₁) (hI₂above : BddAbove I₂)
    (hkappa : 1 ≤ kappa) (hsub : I₁ ⊆ I₂) :
    rightEndpointExpansion a kappa I₁ ⊆ rightEndpointExpansion a kappa I₂ := by
  have hinf : sInf I₂ ≤ sInf I₁ := by
    apply le_csInf hI₁nonempty
    intro x hx
    apply_rules [csInf_le]
  have hsup : sSup I₁ ≤ sSup I₂ := by
    gcongr
  unfold rightEndpointExpansion
  apply Ioo_subset_Ioo
  · apply max_le_max_left
    nlinarith
  · exact hsup

section
variable {a b kappa : ℝ} {d : ℕ} {I : Set ℝ} (Gamma : Set (TimeVelocity d))
    (S : Set (TimeVelocity d)) (hkappa : 1 < kappa) (xi eta : ℝ) (v : PDE.Vec d)

private theorem rightEndpointExpansion_measure_le
    (hkappa : 1 ≤ kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    volume (rightEndpointExpansion a kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩ ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
  have hlt : sInf I < sSup I := by
    rw [hIeq] at hI
    exact nonempty_Ioo.mp hI.1
  rw [hIeq, rightEndpointExpansion, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa)]
  apply ENNReal.ofReal_le_ofReal
  grind

include hkappa in
private theorem isOpenSubinterval_rightEndpointExpansion (hI : IsOpenSubinterval (Ioo a b) I) :
    IsOpenSubinterval (Ioo a b) (rightEndpointExpansion a kappa I) := by
  have hIabove : BddAbove I :=
    ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 ⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩ hIabove
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
    nlinarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  grind

include hkappa in
private theorem volume_sUnion_rightEndpointExpansion (B : Set (Set ℝ))
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo a b)
    isOpen_Ioo ordConnected_Ioo B (rightEndpointExpansion a kappa) hB hbounded
  · intro I hI
    exact isOpenSubinterval_rightEndpointExpansion hkappa hI
  · intro I hI _
    exact rightEndpointExpansion_measure_le hkappa.le hI
  · intro I₁ I₂ hI₁ hI₂ hsub
    exact rightEndpointExpansion_mono_of_subset hI₁.1 ⟨a, fun x hx => (hI₂.2.2.2 hx).1.le⟩ ⟨b, fun x hx => (hI₁.2.2.2 hx).2.le⟩ ⟨b, fun x hx => (hI₂.2.2.2 hx).2.le⟩
      hkappa.le hsub

include S v in
private def timeSection : Set ℝ :=
  {t | (t, v) ∈ S}

include Gamma xi eta v in
private def windSectionFamily : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = windForwardInterval eta q}

private theorem timeSection_inkSpotsD2_eq_sUnion_windSectionFamily :
    timeSection (inkSpotsD2 Gamma xi eta) v =
      ⋃₀ (windSectionFamily Gamma xi eta v) := by
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
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
      (mem_inkSpotsQ2_iff).2 ⟨ht.1, ht.2, hvCenter, hvUnit⟩⟩⟩

end

section
variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} {q : InkSpotsBox d} (heta : 0 < eta)
include heta

private theorem windForwardInterval_eligible (hq : inkSpotsStrictDense Gamma xi q) :
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
    rw [windForwardInterval, mem_Ioo] at ht
    rw [windAmbientTime, mem_Ioo]
    constructor
    · nlinarith [sq_pos_of_pos hq.1]
    · rw [inkSpotsTerminalTime_eq] at ht
      have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
        rw [div_le_div_iff_of_pos_right heta]
        nlinarith
      linarith

private theorem timeSection_inkSpotsD1_subset_expanded_windSections
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
  have hExpanded :=
    inkSpotsQ1_time_mem_windExpandedInterval heta heta1 hq htQ1
  have hUnitTime : 0 < t := by
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at ht
    grind
  have hUnitVelocity : v ∈ velocityCube 0 1 := by
    have hUnit := ht.2.2.2
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hUnit
    exact hUnit.2.2
  have hExpanded' : t ∈ rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q) := by
    rw [rightEndpointExpansion_forwardInterval q heta hq]
    rw [windExpandedInterval, mem_Ioo] at hExpanded
    grind
  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q), ?_, hExpanded'⟩
  exact ⟨windForwardInterval eta q,
    ⟨q, hq, ht.2.2.1, hUnitVelocity, rfl⟩, rfl⟩

end

variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta : ℝ) (heta : 0 < eta) (heta1 : eta < 1)
    (v : PDE.Vec d)

include heta in
private theorem sUnion_windSectionFamily_bounded :
    Bornology.IsBounded (⋃₀ windSectionFamily Gamma xi eta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (windForwardInterval_eligible heta hq).2.2.2

include heta heta1 in
private theorem volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2 :
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
      rw [timeSection_inkSpotsD2_eq_sUnion_windSectionFamily]

private theorem volume_eq_lintegral_timeSection (S : Set (TimeVelocity d))
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

include heta heta1 in
private theorem volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2 :
    volume (inkSpotsD1 Gamma xi) ≤
      ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD1 Gamma xi),
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

private theorem isBounded_velocityCube (v₀ : PDE.Vec d) (r : ℝ) :
    Bornology.IsBounded (velocityCube v₀ r) := by
  apply (isCompact_velocityClosedCube v₀ r).isBounded.subset
  solve_by_elim [le_of_lt]

include heta in
private theorem volume_inkSpotsD2_ne_top :
    volume (inkSpotsD2 Gamma xi eta) ≠ ∞ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (inkSpotsD2_subset_windAmbient Gamma xi eta heta))
  apply Bornology.IsBounded.measure_lt_top
  exact (Metric.isBounded_Ioo 0 (1 + 4 / eta)).prod
    (isBounded_velocityCube 0 1)

include heta heta1 in
/-- Krylov--Safonov, Lemma 2.3 (wind): the clipped first enlargements are controlled
by the forward stacks. -/
theorem volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2 :
    (volume (inkSpotsD1 Gamma xi)).toReal ≤
      (1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal := by
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (volume_inkSpotsD2_ne_top Gamma xi eta heta)) (volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2 Gamma xi eta heta heta1)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic
