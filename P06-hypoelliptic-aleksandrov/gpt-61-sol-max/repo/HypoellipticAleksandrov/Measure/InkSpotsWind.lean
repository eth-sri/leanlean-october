module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import HypoellipticAleksandrov.Measure.IntervalUnion
public import Mathlib.MeasureTheory.Integral.Marginal
public import Mathlib.MeasureTheory.Measure.Prod
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.IntervalDelayFinite
import Lean.Elab.Tactic.SolveByElim
import Mathlib.Tactic.Linarith



/-!
# Wind estimate for source ink spots

This module proves the measure-theoretic wind estimate of Krylov--Safonov, Lemma 2.3 in
Section 2 of Krylov--Safonov. It applies the interval-union lemma on concrete
time sections and then integrates those section inequalities.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HypoellipticAleksandrov.Parabolic

section
variable {d : ℕ} {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi : ℝ} {q : InkSpotsBox d} (hq : inkSpotsStrictDense Gamma xi q)

include hq
private theorem strictDense_timeInterval_subset_unit  :
    Ioo q.baseTime (q.baseTime + q.radius ^ 2) ⊆ Ioo 0 1 := by

  intro t ht

  have htUnit  := hq.2.1 (show (t, q.center) ∈ inkSpotsSourceBox q by
      rw [mem_inkSpotsSourceBox_iff]
      refine ⟨ht.1, ht.2, ?_⟩
      · intro i
        simp only [sub_self, abs_zero]
        exact hq.1)
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  constructor
  · exact htUnit.1
  · convert htUnit.2.1 using 1
    norm_num

private theorem strictDense_baseTime_nonneg  :
    0 ≤ q.baseTime := (Ioo_subset_Ioo_iff (by
      nlinarith [sq_pos_of_pos hq.1])).mp (strictDense_timeInterval_subset_unit hq) |>.1

private theorem strictDense_baseTime_add_sq_le_one  :
    q.baseTime + q.radius ^ 2 ≤ 1 := (Ioo_subset_Ioo_iff (by
      nlinarith [sq_pos_of_pos hq.1])).mp (strictDense_timeInterval_subset_unit hq) |>.2
end


private def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

variable (d : ℕ)

private def windAmbientVelocity  : PDE.VelocityRegion d :=
  velocityCube (0 ) 1

private def windAmbient  (eta : ℝ) : HypoellipticAleksandrov.Parabolic.Region d :=
  windAmbientTime eta ×ˢ windAmbientVelocity d

variable {d : ℕ}

private theorem inkSpotsQ2_subset_windAmbient  {eta : ℝ}
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ2 eta q ⊆ windAmbient d eta := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsQ2_iff] at hz
  refine ⟨?_, hz.2.2.2⟩
  constructor
  · have hbase  := strictDense_baseTime_nonneg hq
    nlinarith [sq_pos_of_pos hq.1]
  · have htop  :=
      strictDense_baseTime_add_sq_le_one hq
    have hbase  := strictDense_baseTime_nonneg hq

    rw [inkSpotsTerminalTime_eq] at hz
    have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
      rw [div_le_div_iff_of_pos_right heta]
      nlinarith
    exact hz.2.1.trans_le (by linarith)

private theorem inkSpotsD2_subset_windAmbient  (Gamma : HypoellipticAleksandrov.Parabolic.Region d)
    (xi eta : ℝ) (heta : 0 < eta) :
    inkSpotsD2 Gamma xi eta ⊆ windAmbient d eta := by
  intro z hz
  rw [inkSpotsD2] at hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  exact inkSpotsQ2_subset_windAmbient heta hq hz

variable (eta : ℝ) (q : InkSpotsBox d)

/-- The time section of a forward source stack. -/
private def windForwardInterval   : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)

/-- The uncut right-end expansion of a forward stack.  The first source
enlargement is later clipped by the reference unit box. -/
private def windExpandedInterval   : Set ℝ :=
  Ioo (q.baseTime - 3 * q.radius ^ 2) (inkSpotsTerminalTime eta q)

private theorem inkSpotsQ1_time_mem_windExpandedInterval
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta : ℝ} {q : InkSpotsBox d} {t : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hq : inkSpotsStrictDense Gamma xi q)
    {v : PDE.Vec d} (ht : (t, v) ∈ inkSpotsQ1 q) :
    t ∈ windExpandedInterval eta q := by
  rw [mem_inkSpotsQ1_iff] at ht
  rw [windExpandedInterval, mem_Ioo]
  constructor
  · exact ht.1
  · rw [inkSpotsTerminalTime_eq]
    norm_num at ht

    have hdiv : 4 * q.radius ^ 2 ≤ 4 * q.radius ^ 2 / eta := by
      rw [le_div_iff₀ heta]
      nlinarith [sq_pos_of_pos hq.1]
    linarith

private theorem isOpen_ordConnected_eq_Ioo_csInf_csSup (I : Set ℝ)
    (hIopen : IsOpen I) (hIord : I.OrdConnected) (hInonempty : I.Nonempty)
    (hIbelow : BddBelow I) (hIabove : BddAbove I) :
    I = Ioo (sInf I) (sSup I) := (KineticAleksandrov.Holder.Covering.open_ordConnected_eq_Ioo hIopen hInonempty hIbelow hIabove hIord)

/-- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
private def rightEndpointExpansion (a kappa : ℝ) (I : Set ℝ) : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)

private theorem rightEndpointExpansion_forwardInterval {d : ℕ}
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta : ℝ} (q : InkSpotsBox d)
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (1 + eta) (windForwardInterval eta q) =
      Ioo (max 0 (q.baseTime - 3 * q.radius ^ 2))
        (inkSpotsTerminalTime eta q) := by
  unfold rightEndpointExpansion windForwardInterval
  have hnonempty : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
    rw [inkSpotsTerminalTime_eq]
    have hsquare  := sq_pos_of_pos hq.1
    field_simp
    nlinarith
  rw [csInf_Ioo hnonempty, csSup_Ioo hnonempty]
  congr 2
  rw [inkSpotsTerminalTime_eq]
  field_simp
  ring

private theorem rightEndpointExpansion_mono_of_subset {a kappa : ℝ}
    {I₁ I₂ : Set ℝ} (hI₁nonempty : I₁.Nonempty) (hI₂below : BddBelow I₂)
    (hI₁above : BddAbove I₁) (hI₂above : BddAbove I₂)
    (hkappa : 1 ≤ kappa) (hsub : I₁ ⊆ I₂) :
    rightEndpointExpansion a kappa I₁ ⊆ rightEndpointExpansion a kappa I₂ := by
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

variable {a b kappa : ℝ}

variable {I : Set ℝ}

private theorem rightEndpointExpansion_measure_le
    (hkappa : 1 ≤ kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    volume (rightEndpointExpansion a kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
  let sharedTerm_c34a4b628e := ((sSup I - kappa * (sSup I - sInf I)))


  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 (⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩) (⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩)
  have hlt : sInf I < sSup I := by
    rw [hIeq] at hI
    exact nonempty_Ioo.mp hI.1
  rw [hIeq, rightEndpointExpansion, csInf_Ioo hlt, csSup_Ioo hlt,
    Real.volume_Ioo, Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (le_trans zero_le_one hkappa)]
  apply ENNReal.ofReal_le_ofReal
  have hleft : sharedTerm_c34a4b628e ≤
      max a sharedTerm_c34a4b628e := le_max_right _ _
  nlinarith

private theorem isOpenSubinterval_rightEndpointExpansion
     (hkappa : 1 < kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    IsOpenSubinterval (Ioo a b) (rightEndpointExpansion a kappa I) := by

  have hIabove : BddAbove I :=
    ⟨b, fun x hx => (hI.2.2.2 hx).2.le⟩
  have hIeq := isOpen_ordConnected_eq_Ioo_csInf_csSup I hI.2.1 hI.2.2.1
    hI.1 (⟨a, fun x hx => (hI.2.2.2 hx).1.le⟩) hIabove
  have hlt : sInf I < sSup I := by
    rw [hIeq] at hI
    exact nonempty_Ioo.mp hI.1


  unfold rightEndpointExpansion
  constructor
  · refine nonempty_Ioo.mpr (max_lt ?_ ?_)
    · exact (by
        rcases hI.1 with ⟨x, hx⟩
        exact (hI.2.2.2 hx).1.trans_le (le_csSup hIabove hx))
    · nlinarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · exact Ioo_subset_Ioo (le_max_left _ _) (by
      rcases hI.1 with ⟨x, hx⟩
      apply (csSup_le_iff hIabove ⟨x, hx⟩).2
      intro y hy
      exact (hI.2.2.2 hy).2.le)

private theorem volume_sUnion_rightEndpointExpansion
    (hkappa : 1 < kappa) (B : Set (Set ℝ))
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo a b)
    isOpen_Ioo ordConnected_Ioo B (rightEndpointExpansion a kappa) hB hbounded
  · simp_all [isOpenSubinterval_rightEndpointExpansion]
  · intro I hI _
    exact rightEndpointExpansion_measure_le hkappa.le hI
  · intro I₁ I₂ hI₁ hI₂ hsub



    exact rightEndpointExpansion_mono_of_subset hI₁.1 (⟨a, fun x hx => (hI₂.2.2.2 hx).1.le⟩) (⟨b, fun x hx => (hI₁.2.2.2 hx).2.le⟩) (⟨b, fun x hx => (hI₂.2.2.2 hx).2.le⟩)
      hkappa.le hsub

variable {d : ℕ}

private def timeSection  (S : HypoellipticAleksandrov.Parabolic.Region d) (v : PDE.Vec d) : Set ℝ :=
  {t | (t, v) ∈ S}

variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta : ℝ) (v : PDE.Vec d)

private def windSectionFamily   : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = windForwardInterval eta q}

private theorem timeSection_inkSpotsD2_eq_sUnion_windSectionFamily
     :
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
    rw [timeSection, inkSpotsD2]
    exact mem_iUnion.2 ⟨q, mem_iUnion.2 ⟨hq,
      (mem_inkSpotsQ2_iff).2 ⟨ht.1, ht.2, hvCenter, hvUnit⟩⟩⟩

variable {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta : ℝ}

private theorem windForwardInterval_eligible
     {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta) (windForwardInterval eta q) := by
  constructor
  · apply nonempty_Ioo.mpr
    rw [inkSpotsTerminalTime_eq]
    have hsquare  := sq_pos_of_pos hq.1
    field_simp
    nlinarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have hbase  := strictDense_baseTime_nonneg hq
    have htop  :=
      strictDense_baseTime_add_sq_le_one hq

    rw [windForwardInterval, mem_Ioo] at ht
    rw [windAmbientTime, mem_Ioo]
    constructor
    · nlinarith [sq_pos_of_pos hq.1]
    · rw [inkSpotsTerminalTime_eq] at ht
      have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
        rw [div_le_div_iff_of_pos_right heta]
        nlinarith
      exact ht.2.trans_le (by linarith)

private theorem timeSection_inkSpotsD1_subset_expanded_windSections
     (heta : 0 < eta)
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
  have hExpanded  :=
    inkSpotsQ1_time_mem_windExpandedInterval heta heta1 hq htQ1
  have hUnitTime : 0 < t := by
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at ht
    exact ht.2.2.2.1


  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q), ?_, (show _ by
          rw [rightEndpointExpansion_forwardInterval q heta hq]
          rw [windExpandedInterval, mem_Ioo] at hExpanded
          constructor
          · exact max_lt hUnitTime hExpanded.1
          · exact hExpanded.2)⟩
  exact ⟨_,
    ⟨q, hq, ht.2.2.1, (show _ by
        have hUnit := ht.2.2.2
        rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hUnit
        exact hUnit.2.2), rfl⟩, rfl⟩

section
variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta : ℝ) (heta : 0 < eta)

include heta
private theorem sUnion_windSectionFamily_bounded

    (v : PDE.Vec d) :
    Bornology.IsBounded (⋃₀ windSectionFamily Gamma xi eta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (windForwardInterval_eligible heta hq).2.2.2

private theorem volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2

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
      rw [timeSection_inkSpotsD2_eq_sUnion_windSectionFamily]
end


private theorem volume_eq_lintegral_timeSection  (S : HypoellipticAleksandrov.Parabolic.Region d)
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

private theorem volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2
    (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta : ℝ) (heta : 0 < eta)
    (heta1 : eta < 1) :
    volume (inkSpotsD1 Gamma xi) ≤
      ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD1 Gamma xi),
    volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta)]
  calc
    (∫⁻ v, volume (timeSection (inkSpotsD1 Gamma xi) v)) ≤
        ∫⁻ v, ENNReal.ofReal (1 + eta) *
          volume (timeSection (inkSpotsD2 Gamma xi eta) v) :=
      lintegral_mono (volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2 Gamma xi eta heta heta1)
    _ = ENNReal.ofReal (1 + eta) *
        ∫⁻ v, volume (timeSection (inkSpotsD2 Gamma xi eta) v) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem isBounded_velocityCube  (v₀ : PDE.Vec d) (r : ℝ) :
    Bornology.IsBounded (velocityCube v₀ r) := by
  apply (isCompact_velocityClosedCube v₀ r).isBounded.subset
  intro v hv i
  exact le_of_lt (hv i)

variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d) (xi eta : ℝ) (heta : 0 < eta)

include heta
private theorem volume_inkSpotsD2_ne_top   :
    volume (inkSpotsD2 Gamma xi eta) ≠ ∞ := (ne_of_lt
  (lt_of_le_of_lt (measure_mono (inkSpotsD2_subset_windAmbient Gamma xi eta heta))
    (Bornology.IsBounded.measure_lt_top
      (Bornology.IsBounded.prod (Metric.isBounded_Ioo 0 (1 + 4 / eta)) (isBounded_velocityCube 0 1)))))

/-- Krylov--Safonov, Lemma 2.3 (wind): the clipped first enlargements are controlled
by the forward stacks. -/
theorem volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2
      (heta1 : eta < 1) :
    (volume (inkSpotsD1 Gamma xi)).toReal ≤
      (1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal := by
  have hmeasure := volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2
    Gamma xi eta heta heta1
  have hfinite : ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (volume_inkSpotsD2_ne_top Gamma xi eta heta)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hreal
  exact hreal

end HypoellipticAleksandrov.Parabolic
