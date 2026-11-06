module

public import HypoellipticAleksandrov.Parabolic.ScalingMeasure

/-!
# Source geometry for parabolic ink spots

This module fixes the box geometry in Section 2 of Krylov--Safonov used by
the crawling-of-ink-spots argument.  It contains only the source boxes,
their three enlargements, their ambient unions, and their elementary
topological and measure properties.  It does not contain the density
saturation lemma or either wind estimate.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/- Parameters of a source box \(Q_{1,R}(t_0,v_0)\).  Positivity is deliberately
kept out of the data and belongs to the strict-dense predicate. -/
structure InkSpotsBox (d : ℕ) where
  radius : ℝ
  baseTime : ℝ
  center : PDE.Vec d

/- The source reference box \(Q_1=Q_{1,1}(0,0)\). -/
def inkSpotsUnitBox (d : ℕ) : Set (TimeVelocity d) :=
  parabolicBox 1 1 0 0

/- The source box \(Q=Q_{1,R}(t_0,v_0)\). -/
def inkSpotsSourceBox {d } (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  parabolicBox 1 q.radius q.baseTime q.center

/- The first source enlargement \(Q^1\), including its required clipping by
the reference box. -/
def inkSpotsQ1 {d } (q : InkSpotsBox d) : Set (TimeVelocity d) :=
  parabolicBox (7 / 9 : ℝ) (3 * q.radius)
    (q.baseTime - 3 * q.radius ^ 2) q.center ∩ inkSpotsUnitBox d

/- The forward source enlargement \(Q^2\).  Its time interval is not clipped
by the reference box. -/
def inkSpotsQ2 {d } (eta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  Ioo (q.baseTime + q.radius ^ 2)
      (q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta) ×ˢ
    (velocityCube q.center (3 * q.radius) ∩ velocityCube 0 1)

/- The terminal time at the right edge of \(Q^2\). -/
def inkSpotsTerminalTime {d } (eta : ℝ) (q : InkSpotsBox d) : ℝ :=
  q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta

/- The source terminal contraction \(S_\zeta\). -/
def inkSpotsContraction {d } (eta zeta : ℝ) (q : InkSpotsBox d) :
    TimeVelocity d → TimeVelocity d :=
  fun z ↦
    (inkSpotsTerminalTime eta q - zeta ^ 2 *
        (inkSpotsTerminalTime eta q - z.1),
      q.center + zeta • (z.2 - q.center))

/- The source set \(Q^3=S_\zeta(Q^2)\). -/
def inkSpotsQ3 {d } (eta zeta : ℝ) (q : InkSpotsBox d) :
    Set (TimeVelocity d) :=
  inkSpotsContraction eta zeta q '' inkSpotsQ2 eta q

/- The strict source density condition.  Radius positivity is visible here,
not hidden in the box parameter structure. -/
def inkSpotsStrictDense {d } (Gamma : Set (TimeVelocity d)) (xi : ℝ)
    (q : InkSpotsBox d) : Prop :=
  0 < q.radius ∧
    inkSpotsSourceBox q ⊆ inkSpotsUnitBox d ∧
    xi * (volume (inkSpotsSourceBox q)).toReal <
      (volume (inkSpotsSourceBox q ∩ Gamma)).toReal

/- The actual source family of strict dense boxes. -/
def inkSpotsDenseBoxes {d } (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    Set (InkSpotsBox d) :=
  {q | inkSpotsStrictDense Gamma xi q}

/- The source union \(D^1=\bigcup_{Q\in\mathcal B}Q^1\). -/
def inkSpotsD1 {d } (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ1 q

/- The source union \(D^2=\bigcup_{Q\in\mathcal B}Q^2\). -/
def inkSpotsD2 {d } (Gamma : Set (TimeVelocity d)) (xi eta : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ2 eta q

/- The source union \(D^3=\bigcup_{Q\in\mathcal B}Q^3\). -/
def inkSpotsD3 {d } (Gamma : Set (TimeVelocity d)) (xi eta zeta : ℝ) :
    Set (TimeVelocity d) :=
  ⋃ q ∈ inkSpotsDenseBoxes Gamma xi, inkSpotsQ3 eta zeta q

@[simp] theorem mem_inkSpotsSourceBox_iff {d } {q : InkSpotsBox d}
    {t } {v } :
    (t, v) ∈ inkSpotsSourceBox q ↔
      q.baseTime < t ∧ t < q.baseTime + q.radius ^ 2 ∧
        v ∈ velocityCube q.center q.radius :=
  by
    simpa only [inkSpotsSourceBox, one_mul] using
      (mem_parabolicBox_iff (vartheta := (1 : ℝ)) (r := q.radius)
        (t₀ := q.baseTime) (t := t) (v₀ := q.center) (v := v))

@[simp] theorem mem_inkSpotsQ1_iff {d } {q : InkSpotsBox d}
    {t v} :
    (t, v) ∈ inkSpotsQ1 q ↔
      q.baseTime - 3 * q.radius ^ 2 < t ∧
        t < q.baseTime - 3 * q.radius ^ 2 +
          (7 / 9 : ℝ) * (3 * q.radius) ^ 2 ∧
        v ∈ velocityCube q.center (3 * q.radius) ∧
        (t, v) ∈ inkSpotsUnitBox d :=
  by
    rw [inkSpotsQ1, mem_inter_iff, mem_parabolicBox_iff]
    constructor
    · rintro ⟨⟨htLower, htUpper, hv⟩, hz⟩
      exact ⟨htLower, htUpper, hv, hz⟩
    · rintro ⟨htLower, htUpper, hv, hz⟩
      exact ⟨⟨htLower, htUpper, hv⟩, hz⟩

@[simp] theorem mem_inkSpotsQ2_iff {d eta} {q : InkSpotsBox d}
    {t } {v } :
    (t, v) ∈ inkSpotsQ2 eta q ↔
      q.baseTime + q.radius ^ 2 < t ∧
        t < inkSpotsTerminalTime eta q ∧
        v ∈ velocityCube q.center (3 * q.radius) ∧
        v ∈ velocityCube 0 1 :=
  by
    constructor
    · rintro ⟨⟨htLower, htUpper⟩, hvCenter, hvUnit⟩
      exact ⟨htLower, htUpper, hvCenter, hvUnit⟩
    · rintro ⟨htLower, htUpper, hvCenter, hvUnit⟩
      exact ⟨⟨htLower, htUpper⟩, hvCenter, hvUnit⟩

@[simp] theorem mem_inkSpotsQ3_iff {d eta zeta q} {z : TimeVelocity d} :
    z ∈ inkSpotsQ3 eta zeta q ↔
      ∃ y ∈ inkSpotsQ2 eta q, inkSpotsContraction eta zeta q y = z :=
  Iff.rfl

@[simp] theorem inkSpotsTerminalTime_eq {d } (eta : ℝ) (q : InkSpotsBox d) :
    inkSpotsTerminalTime eta q =
      q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta :=
  rfl

/- The source box is contained in its clipped first enlargement whenever it
is a genuine positive-radius subbox of the reference box. -/
theorem inkSpotsSourceBox_subset_Q1 {d } {q : InkSpotsBox d}
    (hr : 0 < q.radius) (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    inkSpotsSourceBox q ⊆ inkSpotsQ1 q := by
  intro z hz
  refine ⟨?_, hq hz⟩
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsSourceBox_iff] at hz
  rw [mem_parabolicBox_iff]
  constructor
  · nlinarith [sq_pos_of_pos hr]
  constructor
  · norm_num
    nlinarith [sq_pos_of_pos hr]
  · intro i
    have hi := hz.2.2 i
    calc
      |v i - q.center i| < q.radius := hi
      _ < 3 * q.radius := by linarith

/- Every strict dense source box is contained in its first source
enlargement. -/
theorem inkSpotsSourceBox_subset_Q1_of_strictDense {d Gamma xi} {q : InkSpotsBox d}
    (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsSourceBox q ⊆ inkSpotsQ1 q :=
  inkSpotsSourceBox_subset_Q1 hq.1 hq.2.1

/- The first source enlargement is open. -/
theorem isOpen_inkSpotsQ1 {d } (q : InkSpotsBox d) :
    IsOpen (inkSpotsQ1 q) :=
  (isOpen_parabolicBox _ _ _ _).inter (isOpen_parabolicBox _ _ _ _)

/- The forward source enlargement is open. -/
theorem isOpen_inkSpotsQ2 {d } (eta : ℝ) (q : InkSpotsBox d) :
    IsOpen (inkSpotsQ2 eta q) :=
  isOpen_Ioo.prod ((isOpen_velocityCube _ _).inter (isOpen_velocityCube _ _))

/- The source \(D^1\) is open. -/
theorem isOpen_inkSpotsD1 {d } (Gamma : Set (TimeVelocity d)) (xi : ℝ) :
    IsOpen (inkSpotsD1 Gamma xi) := by
  unfold inkSpotsD1
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  exact isOpen_inkSpotsQ1 q

/- The source \(D^1\) is measurable. -/
theorem isOpen_inkSpotsD2 {d } (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) :
    IsOpen (inkSpotsD2 Gamma xi eta) := by
  unfold inkSpotsD2
  apply isOpen_iUnion
  intro q
  apply isOpen_iUnion
  intro hq
  exact isOpen_inkSpotsQ2 eta q

/- The source \(D^2\) is measurable. -/
theorem measurableSet_inkSpotsD2 {d } (Gamma : Set (TimeVelocity d))
    (xi eta : ℝ) :
    MeasurableSet (inkSpotsD2 Gamma xi eta) :=
  (isOpen_inkSpotsD2 Gamma xi eta).measurableSet

end

end HypoellipticAleksandrov.Parabolic
