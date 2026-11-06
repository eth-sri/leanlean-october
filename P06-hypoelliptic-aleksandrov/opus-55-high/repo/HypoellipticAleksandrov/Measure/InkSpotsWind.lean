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

variable {d : ℕ} {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}

theorem strictDense_timeInterval_subset_unit 
    (hq : inkSpotsStrictDense Gamma xi q) :
    Ioo q.baseTime (q.baseTime + q.radius ^ 2) ⊆ Ioo 0 1 := by
  have hr  := hq.1
  intro t ht
  have htSource : (t, q.center) ∈ inkSpotsSourceBox q := by
    simp_all
  have htUnit : (t, q.center) ∈ inkSpotsUnitBox d := hq.2.1 htSource
  rw [inkSpotsUnitBox, mem_parabolicBox_iff] at htUnit
  simp_all

theorem strictDense_baseTime_nonneg 
    (hq : inkSpotsStrictDense Gamma xi q) :
    0 ≤ q.baseTime := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.1

theorem strictDense_baseTime_add_sq_le_one 
    (hq : inkSpotsStrictDense Gamma xi q) :
    q.baseTime + q.radius ^ 2 ≤ 1 := by
  have htime := strictDense_timeInterval_subset_unit hq
  have hnonempty : q.baseTime < q.baseTime + q.radius ^ 2 := by
    nlinarith [sq_pos_of_pos hq.1]
  exact (Ioo_subset_Ioo_iff hnonempty).mp htime |>.2

def windAmbientTime (eta : ℝ) : Set ℝ :=
  Ioo 0 (1 + 4 / eta)

def windAmbientVelocity (d : ℕ) : Set (PDE.Vec d) :=
  velocityCube (0 : PDE.Vec d) 1

def windAmbient (d : ℕ) (eta : ℝ) : Set (TimeVelocity d) :=
  windAmbientTime eta ×ˢ windAmbientVelocity d

variable {d : ℕ}

theorem inkSpotsQ2_subset_windAmbient  {eta : ℝ}
    {Gamma : Set (TimeVelocity d)} {xi : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ2 eta q ⊆ windAmbient d eta := by
  intro z hz
  rw [mem_inkSpotsQ2_iff] at hz
  refine ⟨?_, hz.2.2.2⟩
  constructor
  · have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    nlinarith [sq_pos_of_pos hq.1]
  · have htop : q.baseTime + q.radius ^ 2 ≤ 1 :=
      strictDense_baseTime_add_sq_le_one hq
    have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    rw [inkSpotsTerminalTime_eq] at hz
    have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
      rw [div_le_div_iff_of_pos_right heta]
      nlinarith
    linarith

private theorem inkSpotsD2_subset_windAmbient  (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) (heta : 0 < eta) :
    inkSpotsD2 Gamma xi eta ⊆ windAmbient d eta := by
  intro z hz
  rcases mem_iUnion.1 hz with ⟨q, hz⟩
  rcases mem_iUnion.1 hz with ⟨hq, hz⟩
  exact inkSpotsQ2_subset_windAmbient heta hq hz

/-- The time section of a forward source stack. -/
def windForwardInterval {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime + q.radius ^ 2) (inkSpotsTerminalTime eta q)

/-- The uncut right-end expansion of a forward stack.  The first source
enlargement is later clipped by the reference unit box. -/
private def windExpandedInterval {d : ℕ} (eta : ℝ) (q : InkSpotsBox d) : Set ℝ :=
  Ioo (q.baseTime - 3 * q.radius ^ 2) (inkSpotsTerminalTime eta q)

private theorem inkSpotsQ1_time_mem_windExpandedInterval {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} {q : InkSpotsBox d} {t : ℝ}
    (heta : 0 < eta) (heta1 : eta < 1) (hq : inkSpotsStrictDense Gamma xi q)
    {v : PDE.Vec d} (ht : (t, v) ∈ inkSpotsQ1 q) :
    t ∈ windExpandedInterval eta q := by
  rw [mem_inkSpotsQ1_iff] at ht
  constructor
  · grind
  · rw [inkSpotsTerminalTime_eq]
    have hr : 0 < q.radius := hq.1
    have hdiv : 4 * q.radius ^ 2 ≤ 4 * q.radius ^ 2 / eta := by
      rw [le_div_iff₀ heta]
      nlinarith [sq_pos_of_pos hr]
    linarith

theorem isOpen_ordConnected_eq_Ioo_csInf_csSup (I : Set ℝ)
    (hIopen : IsOpen I) (hIord : I.OrdConnected) (hInonempty : I.Nonempty)
    (hIbelow : BddBelow I) (hIabove : BddAbove I) :
    I = Ioo (sInf I) (sSup I) := by
  apply Subset.antisymm
  · intro x hx
    have hinf : sInf I ≤ x := csInf_le hIbelow hx
    have hsup : x ≤ sSup I := le_csSup hIabove hx
    constructor
    · by_contra hnot
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hleft : x - eps / 2 ∈ I := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        grind)
      have hle : sInf I ≤ x - eps / 2 := csInf_le hIbelow hleft
      linarith
    · by_contra hnot
      rcases Metric.mem_nhds_iff.1 (hIopen.mem_nhds hx) with ⟨eps, heps, hball⟩
      have hright : x + eps / 2 ∈ I := hball (by
        rw [Metric.mem_ball, Real.dist_eq]
        grind)
      have hle : x + eps / 2 ≤ sSup I := le_csSup hIabove hright
      linarith
  · exact IsConnected.Ioo_csInf_csSup_subset
      ⟨hInonempty, hIord.isPreconnected⟩ hIbelow hIabove

/-- Right-end interval expansion, clipped only at the left endpoint of the
ambient interval.  This is the concrete map used for the time sections. -/
def rightEndpointExpansion (a kappa : ℝ) (I : Set ℝ) : Set ℝ :=
  Ioo (max a (sSup I - kappa * (sSup I - sInf I))) (sSup I)

private theorem rightEndpointExpansion_forwardInterval {d : ℕ}
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} (q : InkSpotsBox d)
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    rightEndpointExpansion 0 (1 + eta) (windForwardInterval eta q) =
      Ioo (max 0 (q.baseTime - 3 * q.radius ^ 2))
        (inkSpotsTerminalTime eta q) := by
  unfold rightEndpointExpansion windForwardInterval
  have hnonempty : q.baseTime + q.radius ^ 2 < inkSpotsTerminalTime eta q := by
    rw [inkSpotsTerminalTime_eq]
    have hsquare : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    simp_all
  rw [csInf_Ioo hnonempty, csSup_Ioo hnonempty]
  congr 2
  rw [inkSpotsTerminalTime_eq]
  grind

theorem rightEndpointExpansion_mono_of_subset {a kappa : ℝ}
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
  apply Ioo_subset_Ioo
  · apply max_le_max_left
    nlinarith
  omega

variable {a b kappa : ℝ} {I : Set ℝ}

theorem rightEndpointExpansion_measure_le 
    (hkappa : 1 ≤ kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    volume (rightEndpointExpansion a kappa I) ≤
      ENNReal.ofReal kappa * volume I := by
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
  grind

theorem isOpenSubinterval_rightEndpointExpansion  (hkappa : 1 < kappa) (hI : IsOpenSubinterval (Ioo a b) I) :
    IsOpenSubinterval (Ioo a b) (rightEndpointExpansion a kappa I) := by
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
  constructor
  · refine nonempty_Ioo.mpr (max_lt ?_ ?_)
    · omega
    · have hproduct : 0 < kappa * (sSup I - sInf I) :=
        mul_pos (zero_lt_one.trans hkappa) (sub_pos.mpr hlt)
      linarith
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · exact Ioo_subset_Ioo (le_max_left _ _) hupper

theorem volume_sUnion_rightEndpointExpansion 
    (hkappa : 1 < kappa) (B : Set (Set ℝ))
    (hB : ∀ I ∈ B, IsOpenSubinterval (Ioo a b) I)
    (hbounded : Bornology.IsBounded (⋃₀ B)) :
    volume (⋃₀ (rightEndpointExpansion a kappa '' B)) ≤
      ENNReal.ofReal kappa * volume (⋃₀ B) := by
  apply volume_sUnion_monotone_interval_enlargement_of_le kappa hkappa (Ioo a b)
    isOpen_Ioo ordConnected_Ioo B _ hB hbounded
  · intro I hI
    exact isOpenSubinterval_rightEndpointExpansion hkappa hI
  · intro I hI _
    exact rightEndpointExpansion_measure_le hkappa.le hI
  · intro I₁ I₂ hI₁ hI₂ hsub
    have hI₂below : BddBelow I₂ :=
      ⟨a, fun x hx => (hI₂.2.2.2 hx).1.le⟩
    have hI₁above : BddAbove I₁ :=
      ⟨b, fun x hx => (hI₁.2.2.2 hx).2.le⟩
    have hI₂above : BddAbove I₂ :=
      ⟨b, fun x hx => (hI₂.2.2.2 hx).2.le⟩
    exact rightEndpointExpansion_mono_of_subset hI₁.1 hI₂below hI₁above hI₂above
      hkappa.le hsub

def timeSection {d : ℕ} (S : Set (TimeVelocity d)) (v : PDE.Vec d) : Set ℝ :=
  {t | (t, v) ∈ S}

private def windSectionFamily {d : ℕ} (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) (v : PDE.Vec d) : Set (Set ℝ) :=
  {I | ∃ q, inkSpotsStrictDense Gamma xi q ∧
    v ∈ velocityCube q.center (3 * q.radius) ∧ v ∈ velocityCube 0 1 ∧
    I = windForwardInterval eta q}

variable {d : ℕ} (Gamma : Set (TimeVelocity d)) (xi eta : ℝ)

private theorem timeSection_inkSpotsD2_eq_sUnion_windSectionFamily  (v : PDE.Vec d) :
    timeSection (inkSpotsD2 Gamma xi eta) v =
      ⋃₀ (windSectionFamily Gamma xi eta v) := by
  ext t
  constructor
  · intro ht
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

theorem windForwardInterval_eligible 
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} {q : InkSpotsBox d}
    (heta : 0 < eta) (hq : inkSpotsStrictDense Gamma xi q) :
    IsOpenSubinterval (windAmbientTime eta) (windForwardInterval eta q) := by
  constructor
  · apply nonempty_Ioo.mpr
    rw [inkSpotsTerminalTime_eq]
    have hsquare : 0 < q.radius ^ 2 := sq_pos_of_pos hq.1
    simp_all
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  · intro t ht
    have hbase : 0 ≤ q.baseTime := strictDense_baseTime_nonneg hq
    have htop : q.baseTime + q.radius ^ 2 ≤ 1 :=
      strictDense_baseTime_add_sq_le_one hq
    rw [windForwardInterval, mem_Ioo] at ht
    constructor
    · nlinarith [sq_pos_of_pos hq.1]
    · rw [inkSpotsTerminalTime_eq] at ht
      have hdiv : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
        rw [div_le_div_iff_of_pos_right heta]
        nlinarith
      linarith

private theorem timeSection_inkSpotsD1_subset_expanded_windSections 
    {Gamma : Set (TimeVelocity d)} {xi eta : ℝ} (heta : 0 < eta)
    (heta1 : eta < 1) (v : PDE.Vec d) :
    timeSection (inkSpotsD1 Gamma xi) v ⊆
      ⋃₀ (rightEndpointExpansion 0 (1 + eta) ''
        windSectionFamily Gamma xi eta v) := by
  intro t ht
  rcases mem_iUnion.1 ht with ⟨q, ht⟩
  rcases mem_iUnion.1 ht with ⟨hq, ht⟩
  have htQ1 := ht
  rw [mem_inkSpotsQ1_iff] at ht
  have hExpanded  :=
    inkSpotsQ1_time_mem_windExpandedInterval heta heta1 hq htQ1
  have hUnitTime : 0 < t := by
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at ht
    simp_all
  have hUnitVelocity : v ∈ velocityCube (0) 1 := by
    have hUnit := ht.2.2.2
    rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hUnit
    simp_all
  have hExpanded' : t ∈ rightEndpointExpansion 0 (1 + eta)
      (windForwardInterval eta q) := by
    rw [rightEndpointExpansion_forwardInterval q heta hq]
    constructor
    · simp_all
    · exact hExpanded.2
  refine mem_sUnion.2 ⟨rightEndpointExpansion 0 _
      _, ?_, hExpanded'⟩
  exact ⟨windForwardInterval eta q,
    ⟨q, hq, ht.2.2.1, hUnitVelocity, rfl⟩, rfl⟩

private theorem sUnion_windSectionFamily_bounded  (heta : 0 < eta)
    (v : PDE.Vec d) :
    Bornology.IsBounded (⋃₀ windSectionFamily Gamma xi eta v) := by
  apply (Metric.isBounded_Ioo 0 (1 + 4 / eta)).subset
  refine sUnion_subset fun I hI => ?_
  rcases hI with ⟨q, hq, _, _, rfl⟩
  exact (windForwardInterval_eligible heta hq).2.2.2

private theorem volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2  (heta : 0 < eta)
    (heta1 : eta < 1) (v : PDE.Vec d) :
    volume (timeSection (inkSpotsD1 Gamma xi) v) ≤
      ENNReal.ofReal (1 + eta) *
        volume (timeSection (inkSpotsD2 Gamma xi eta) v) := by
  calc
    volume _ ≤
        volume _ :=
      measure_mono (timeSection_inkSpotsD1_subset_expanded_windSections heta heta1 v)
    _ ≤ ENNReal.ofReal _ *
        volume _ :=
      volume_sUnion_rightEndpointExpansion (by linarith) _
        (fun I hI => by
          rcases hI with ⟨q, hq, _, _, rfl⟩
          exact windForwardInterval_eligible heta hq)
        (sUnion_windSectionFamily_bounded Gamma xi eta heta v)
    _ = ENNReal.ofReal _ *
        volume _ := by
      rw [timeSection_inkSpotsD2_eq_sUnion_windSectionFamily]

theorem volume_eq_lintegral_timeSection  (S : Set (TimeVelocity d))
    (hS : MeasurableSet S) :
    volume S = ∫⁻ v, volume (timeSection S v) := by
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hS]
  rfl

private theorem volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2  (heta : 0 < eta)
    (heta1 : eta < 1) :
    volume (inkSpotsD1 Gamma xi) ≤
      ENNReal.ofReal (1 + eta) * volume (inkSpotsD2 Gamma xi eta) := by
  rw [volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD1 Gamma xi),
    volume_eq_lintegral_timeSection _ (measurableSet_inkSpotsD2 Gamma xi eta)]
  calc
    (∫⁻ v, volume _) ≤
        ∫⁻ v, ENNReal.ofReal _ *
          volume _ :=
      lintegral_mono fun v =>
        volume_timeSection_inkSpotsD1_le_one_add_eta_mul_D2 Gamma xi eta heta heta1 v
    _ = ENNReal.ofReal _ *
        ∫⁻ v, volume _ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem isBounded_velocityCube  (v₀ : PDE.Vec d) (r : ℝ) :
    Bornology.IsBounded (velocityCube v₀ r) := by
  apply (isCompact_velocityClosedCube v₀ r).isBounded.subset
  intro v hv i
  exact le_of_lt (hv i)

theorem volume_inkSpotsD2_ne_top  (heta : 0 < eta) :
    volume (inkSpotsD2 Gamma xi eta) ≠ ∞ := by
  apply ne_of_lt
  apply lt_of_le_of_lt (measure_mono (inkSpotsD2_subset_windAmbient Gamma xi eta heta))
  apply Bornology.IsBounded.measure_lt_top
  exact (Metric.isBounded_Ioo 0 _).prod
    (isBounded_velocityCube _ 1)

/-- Krylov--Safonov, Lemma 2.3 (wind): the clipped first enlargements are controlled
by the forward stacks. -/
theorem volume_inkSpotsD1_toReal_le_one_add_eta_mul_D2
    
    (heta : 0 < eta) (heta1 : eta < 1) :
    (volume (inkSpotsD1 Gamma xi)).toReal ≤
      (1 + eta) * (volume (inkSpotsD2 Gamma xi eta)).toReal := by
  have hmeasure := volume_inkSpotsD1_le_one_add_eta_mul_inkSpotsD2
    Gamma xi eta heta heta1
  have hfinite : ENNReal.ofReal (1 + eta) * volume _ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (volume_inkSpotsD2_ne_top Gamma xi eta heta)
  have hreal := ENNReal.toReal_mono hfinite hmeasure
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at hreal
  omega

end HypoellipticAleksandrov.Parabolic
