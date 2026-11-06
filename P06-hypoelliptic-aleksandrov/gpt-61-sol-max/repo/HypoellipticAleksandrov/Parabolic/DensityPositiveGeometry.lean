module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
public import Mathlib.Tactic
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity



/-!
# Cap-to-stack geometry for positive parabolic density

This module isolates the source-specific, purely geometric part of the two
propagation steps in Krylov--Safonov Lemma 3.3.  It deliberately contains no
coefficient, solution, density-to-point, or forward-propagation assertion.
-/

@[expose] public section




namespace HypoellipticAleksandrov.Parabolic

noncomputable section

/-- Strict containment of a genuine source box in the reference source box
extends to the corresponding closed coordinate boxes. -/
theorem inkSpots_closedSourceBox_subset_closedUnitBox
    (d : Nat) (q : InkSpotsBox d)
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    parabolicClosedBox 1 q.radius q.baseTime q.center ⊆
      parabolicClosedBox 1 1 0 0 := by
  have hsource : closure (inkSpotsSourceBox q) =
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    simpa only [inkSpotsSourceBox] using
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1 ))
        (r := q.radius) (t0 := q.baseTime) (v0 := q.center)
        (by norm_num) hR)
  have hunit : closure (inkSpotsUnitBox d) =
      parabolicClosedBox 1 1 0 0 := by
    simpa only [inkSpotsUnitBox] using
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1 ))
        (r := (1 )) (t0 := 0) (v0 := (0 ))
        (by norm_num) (by norm_num))
  rw [← hsource, ← hunit]
  exact closure_mono hq

variable {d : ℕ}

/-- Elementary endpoint and coordinate consequences of source containment. -/
private theorem inkSpots_source_bounds  {q : InkSpotsBox d}
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    0 ≤ q.baseTime ∧ q.baseTime + q.radius ^ 2 ≤ 1 ∧ q.radius ≤ 1 ∧
      ∀ i, |q.center i| + q.radius ≤ 1 := by
  have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq

  have hcenterUnit := hclosed (show (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨?_, ?_, fun i => ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · norm_num
      · simp [hR.le])
  rw [mem_parabolicClosedBox_iff] at hcenterUnit


  have hplusUnit := hclosed (show (q.baseTime, q.center + q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨le_rfl, ?_, ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        rw [add_sub_cancel_left]
        simp [abs_of_nonneg hR.le])
  have hminusUnit := hclosed (show (q.baseTime, q.center - q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨le_rfl, ?_, ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · intro i
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        rw [sub_sub_cancel_left]
        simp [abs_of_nonneg hR.le])
  rw [mem_parabolicClosedBox_iff] at hplusUnit hminusUnit
  refine ⟨hplusUnit.1, by norm_num at hcenterUnit ⊢; exact hcenterUnit.2.1, ?_, ?_⟩
  · nlinarith [sq_nonneg (q.radius - 1)]
  · intro i
    have hp := hplusUnit.2.2 i
    have hm := hminusUnit.2.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, Pi.zero_apply, sub_zero] at hp hm
    have hp'  :=
      (le_abs_self _).trans hp
    have hm'  :=
      (neg_le_abs _).trans hm
    have habs : |q.center i| ≤ 1 - q.radius := by
      rw [abs_le]
      constructor <;> linarith
    linarith

/-- A point of the terminal contraction has the source's strict time and
coordinate bounds. -/
private theorem inkSpotsQ3_bounds  {eta zeta : ℝ} {q : InkSpotsBox d}
    {z : TimeVelocity d} (heta : 0 < eta) (hzeta : 0 < zeta) (hzeta1 : zeta < 1)
    (hR : 0 < q.radius)
    (hz : z ∈ inkSpotsQ3 eta zeta q) :
    4 * (1 - zeta ^ 2) * q.radius ^ 2 / eta <
        z.1 - (q.baseTime + q.radius ^ 2) ∧
      z.1 - (q.baseTime + q.radius ^ 2) < 4 * q.radius ^ 2 / eta ∧
      ∀ i, |z.2 i - q.center i| < 3 * zeta * q.radius := by
  let sharedTerm_df0c8206b3 := (q.baseTime + q.radius ^ 2 + 4 * q.radius ^ 2 / eta)
  let sharedTerm_42137fb4c0 := ((1 - zeta ^ 2) * (4 * q.radius ^ 2 / eta))
  rcases hz with ⟨y, hy, hyz⟩
  rcases hy with ⟨⟨hyleft, hyright⟩, hycenter, hyunit⟩
  subst z
  constructor
  · dsimp [inkSpotsContraction, inkSpotsTerminalTime]
    have hsquare  := sq_pos_of_pos hzeta


    have htime :
        sharedTerm_df0c8206b3 -
            zeta ^ 2 * (sharedTerm_df0c8206b3 - y.1) -
            (q.baseTime + q.radius ^ 2) =
          sharedTerm_42137fb4c0 +
            zeta ^ 2 * (y.1 - (q.baseTime + q.radius ^ 2)) := by ring
    rw [htime]
    have htail : 0 < zeta ^ 2 * (y.1 - (q.baseTime + q.radius ^ 2)) :=
      mul_pos hsquare (by linarith)
    have hfactor : sharedTerm_42137fb4c0 =
        4 * (1 - zeta ^ 2) * q.radius ^ 2 / eta := by ring
    rw [hfactor]
    nlinarith
  constructor
  · dsimp [inkSpotsContraction, inkSpotsTerminalTime]
    have hsquare  := sq_pos_of_pos hzeta


    have htime :
        sharedTerm_df0c8206b3 -
            zeta ^ 2 * (sharedTerm_df0c8206b3 - y.1) -
            (q.baseTime + q.radius ^ 2) =
          sharedTerm_42137fb4c0 +
            zeta ^ 2 * (y.1 - (q.baseTime + q.radius ^ 2)) := by ring
    rw [htime]
    have htail : zeta ^ 2 * (y.1 - (q.baseTime + q.radius ^ 2)) <
        zeta ^ 2 * (4 * q.radius ^ 2 / eta) :=
      mul_lt_mul_of_pos_left (by linarith) hsquare
    nlinarith
  · intro i
    have hi := hycenter i
    dsimp [inkSpotsContraction]
    rw [add_sub_cancel_left]
    change |zeta * (y.2 i - q.center i)| < 3 * zeta * q.radius
    rw [abs_mul, abs_of_pos hzeta]
    nlinarith

/-- The clipped terminal stack has strict coordinate room inside the unit
box, measured at every contraction factor no larger than `1 - zeta`. -/
private theorem inkSpotsQ3_unit_margin  {eta zeta kappa : ℝ}
    {q : InkSpotsBox d} {z : TimeVelocity d}
    (hzeta : 0 < zeta) (hzeta1 : zeta < 1) (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d)
    (hkappa : kappa ≤ 1 - zeta)
    (hz : z ∈ inkSpotsQ3 eta zeta q ∩ inkSpotsUnitBox d) :
    ∀ i, |z.2 i| < 1 - kappa * q.radius := by
  rcases hz with ⟨hzq3, hzunit⟩
  rcases hzq3 with ⟨y, hy, hyz⟩
  rcases hy with ⟨⟨hyleft, hyright⟩, hycenter, hyunit⟩
  subst z
  obtain ⟨hbase0, hbase1, hRle, hcenter⟩ := inkSpots_source_bounds hR hq
  intro i


  have hrewrite : q.center i + zeta * (y.2 i - q.center i) =
      (1 - zeta) * q.center i + zeta * y.2 i := by ring
  change |q.center i + zeta * (y.2 i - q.center i)| <
    1 - kappa * q.radius
  rw [hrewrite]
  have hcenterTerm  :=
    mul_le_mul_of_nonneg_left (show |q.center i| ≤ 1 - q.radius by
        linarith [hcenter i]) (sub_nonneg.mpr hzeta1.le)
  have hyTerm  :=
    mul_lt_mul_of_pos_left (show |y.2 i| < 1 by
        simpa only [Pi.zero_apply, sub_zero] using hyunit i) hzeta
  calc
    |(1 - zeta) * q.center i + zeta * y.2 i| ≤
        |(1 - zeta) * q.center i| + |zeta * y.2 i| := abs_add_le _ _
    _ = (1 - zeta) * |q.center i| + zeta * |y.2 i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_pos hzeta]
    _ < (1 - zeta) * (1 - q.radius) + zeta * 1 := by
      linarith
    _ ≤ 1 - kappa * q.radius := by
      nlinarith

/-- The positive coordinatewise slack used to enlarge the two relevant
velocity points to a closed propagation rectangle. -/
private def inkSpotsCorridorSlack  (kappa : ℝ) (q : InkSpotsBox d)
    (z : TimeVelocity d) (i : Fin d) : ℝ :=
  min (kappa * q.radius / 2)
    (min (1 - |q.center i| - kappa * q.radius)
      (1 - |z.2 i| - kappa * q.radius) / 2)

/-- Numerical consequences of the source's first propagation parameter. -/
private theorem inkSpots_kappa_properties {eta zeta kappa : ℝ}
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hzeta1 : zeta < 1)
    (hkappa : kappa = min (eta / 4) (1 - zeta)) :
    0 < kappa ∧ kappa ≤ eta / 4 ∧ kappa ≤ 1 - zeta ∧ kappa < 1 / 4 := by
  grind

/-- A point of the clipped terminal stack admits a target-dependent physical
corridor suitable for the first propagation use in Lemma 3.3. -/
theorem exists_inkSpotsQ3_forward_corridor
    (d : Nat) (eta zeta kappa : Real) (q : InkSpotsBox d)
    (z : TimeVelocity d)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hkappa : kappa = min (eta / 4) (1 - zeta))
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d)
    (hz : z ∈ inkSpotsQ3 eta zeta q ∩ inkSpotsUnitBox d) :
    ∃ lower upper : PDE.Vec d,
      kappa * q.radius ^ 2 < z.1 - (q.baseTime + q.radius ^ 2) ∧
      z.1 - (q.baseTime + q.radius ^ 2) ≤ kappa⁻¹ * q.radius ^ 2 ∧
      (∀ i, 2 * kappa * q.radius < upper i - lower i ∧
        upper i - lower i ≤ kappa⁻¹ * q.radius) ∧
      (∀ i, lower i + kappa * q.radius ≤ 0 ∧
        0 < upper i - kappa * q.radius) ∧
      (∀ i, lower i + kappa * q.radius < z.2 i - q.center i ∧
        z.2 i - q.center i < upper i - kappa * q.radius) ∧
      parabolicAffine (q.baseTime + q.radius ^ 2) q.center 1 ''
          parabolicClosedRectangle
            (z.1 - (q.baseTime + q.radius ^ 2)) lower upper ⊆
        parabolicClosedBox 1 1 0 0 := by
  let sharedTerm_74145ac82f := ((3 * zeta + 3 * kappa) * q.radius)
  let sharedTerm_d2f2a398b1 := (4 * (1 - zeta ^ 2))
  let sharedTerm_be26e5f10f := (z.1 - (q.baseTime + q.radius ^ 2))
  obtain ⟨hkappa0, hkappaEta, hkappaZeta, hkappaQuarter⟩ :=
    inkSpots_kappa_properties heta0 heta1 hzeta1 hkappa
  obtain ⟨htlower, htupper, hzcenter⟩ :=
    inkSpotsQ3_bounds heta0 hzeta0 hzeta1 hR hz.1
  obtain ⟨hbase0, hbase1, hRle, hcenter⟩ := inkSpots_source_bounds hR hq
  have hztime : z.1 < 1 := by
    simpa only [one_pow, one_mul, zero_add] using (mem_parabolicBox_iff.mp hz.2).2.1
  have hzmargin  :=
    inkSpotsQ3_unit_margin hzeta0 hzeta1 hR hq hkappaZeta hz
  let slack  := inkSpotsCorridorSlack kappa q z
  let lower  := fun i =>
    min 0 (z.2 i - q.center i) - kappa * q.radius - slack i
  let upper  := fun i =>
    max 0 (z.2 i - q.center i) + kappa * q.radius + slack i
  have hslack : ∀ i, 0 < slack i ∧ slack i ≤ kappa * q.radius / 2 ∧
      slack i ≤ (1 - |q.center i| - kappa * q.radius) / 2 ∧
      slack i ≤ (1 - |z.2 i| - kappa * q.radius) / 2 := by
    intro i
    dsimp [slack, inkSpotsCorridorSlack]
    have hcenterMargin : 0 < 1 - |q.center i| - kappa * q.radius := by
      nlinarith [hcenter i]
    have hzMargin : 0 < 1 - |z.2 i| - kappa * q.radius := by
      nlinarith [hzmargin i]



    refine ⟨lt_min (show _ by positivity) (by
        exact div_pos (lt_min hcenterMargin hzMargin) (by norm_num)), min_le_left _ _,
      le_trans (min_le_right _ _)
        ((div_le_div_iff_of_pos_right (by norm_num)).mpr (min_le_left _ _)),
      le_trans (min_le_right _ _)
        ((div_le_div_iff_of_pos_right (by norm_num)).mpr (min_le_right _ _))⟩


  refine ⟨lower, upper, (by
      let sharedTerm_dd7f2f4d1d := ((1 - zeta) * (4 * (1 + zeta) / eta))

      calc
        kappa * q.radius ^ 2 <
            (sharedTerm_d2f2a398b1 / eta) * q.radius ^ 2 :=
          mul_lt_mul_of_pos_right (by
              have hrewrite : sharedTerm_d2f2a398b1 / eta =
                  sharedTerm_dd7f2f4d1d := by ring
              rw [hrewrite]
              calc
                kappa ≤ 1 - zeta := hkappaZeta
                _ < sharedTerm_dd7f2f4d1d := by
                  have : 1 < 4 * (1 + zeta) / eta := by
                    apply (lt_div_iff₀ heta0).mpr
                    nlinarith
                  simpa using mul_lt_mul_of_pos_left this (sub_pos.mpr hzeta1)) (sq_pos_of_pos hR)
        _ = sharedTerm_d2f2a398b1 * q.radius ^ 2 / eta := by ring
        _ < sharedTerm_be26e5f10f := htlower), (by

      have : 4 * q.radius ^ 2 / eta ≤ kappa⁻¹ * q.radius ^ 2 := by
        calc
          4 * q.radius ^ 2 / eta = (4 / eta) * q.radius ^ 2 := by ring
          _ ≤ kappa⁻¹ * q.radius ^ 2 :=
            mul_le_mul_of_nonneg_right (by
                rw [le_inv_comm₀ (by positivity) hkappa0]
                have hinv : (4 / eta)⁻¹ = eta / 4 := by
                  field_simp
                simpa only [hinv] using hkappaEta) (sq_nonneg q.radius)
      exact htupper.le.trans this), ?_, ?_, ?_, ?_⟩
  · intro i
    have hs := hslack i
    dsimp [lower, upper]
    constructor
    · rw [sub_sub, sub_add_eq_sub_sub]
      have hminmax : min 0 (z.2 i - q.center i) ≤ max 0 (z.2 i - q.center i) :=
        min_le_max
      linarith only [hminmax, hs.1]
    · have hdiff  := hzcenter i
      have hsmall : kappa * (3 * zeta + 3 * kappa) < 1 := by
        calc
          kappa * (3 * zeta + 3 * kappa) ≤
              (eta / 4) * (3 * zeta + 3 * kappa) := by gcongr
          _ < 1 := by nlinarith [hkappaQuarter]
      have hbound : 3 * zeta + 3 * kappa ≤ kappa⁻¹ := by
        rw [← one_div]
        apply (le_div_iff₀ hkappa0).mpr
        nlinarith [hsmall]
      rcases le_total 0 (z.2 i - q.center i) with hcase | hcase
      · rw [max_eq_right hcase, min_eq_left hcase]
        rw [abs_of_nonneg hcase] at hdiff
        exact (calc
          z.2 i - q.center i + kappa * q.radius + slack i -
              (0 - kappa * q.radius - slack i) =
              (z.2 i - q.center i) + 2 * kappa * q.radius + 2 * slack i := by ring
          _ < sharedTerm_74145ac82f := by
            have : 2 * slack i ≤ kappa * q.radius := by nlinarith [hs.2.1]

            calc
              z.2 i - q.center i + 2 * kappa * q.radius + 2 * slack i ≤
                  (z.2 i - q.center i) + 3 * kappa * q.radius :=
                by simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left (show 2 * kappa * q.radius + 2 * slack i ≤
                3 * kappa * q.radius by linarith only [this]) (z.2 i - q.center i)
              _ < 3 * zeta * q.radius + 3 * kappa * q.radius :=
                by gcongr <;> first | positivity | assumption | norm_num
              _ = sharedTerm_74145ac82f := by ring
          _ ≤ kappa⁻¹ * q.radius :=
            mul_le_mul_of_nonneg_right hbound hR.le).le
      · rw [max_eq_left hcase, min_eq_right hcase]
        have hcase'  := hcase
        rw [abs_of_nonpos hcase'] at hdiff
        exact (calc
          0 + kappa * q.radius + slack i -
              (z.2 i - q.center i - kappa * q.radius - slack i) =
              -(z.2 i - q.center i) + 2 * kappa * q.radius + 2 * slack i := by ring
          _ < sharedTerm_74145ac82f := by
            have : 2 * slack i ≤ kappa * q.radius := by nlinarith [hs.2.1]

            calc
              -(z.2 i - q.center i) + 2 * kappa * q.radius + 2 * slack i ≤
                  -(z.2 i - q.center i) + 3 * kappa * q.radius :=
                by simpa [add_assoc, add_left_comm, add_comm] using
                  add_le_add_left (show _ by linarith only [this]) (-(z.2 i - q.center i))
              _ < 3 * zeta * q.radius + 3 * kappa * q.radius :=
                by gcongr <;> first | positivity | assumption | norm_num
              _ = sharedTerm_74145ac82f := by ring
          _ ≤ kappa⁻¹ * q.radius :=
            mul_le_mul_of_nonneg_right hbound hR.le).le
  · intro i
    have hs := hslack i
    dsimp [lower, upper]
    constructor
    · have hmin : min 0 (z.2 i - q.center i) ≤ 0 := min_le_left _ _
      linarith only [hmin, hs.1]
    · have hmax : 0 ≤ max 0 (z.2 i - q.center i) := le_max_left _ _
      linarith only [hmax, hs.1]
  · intro i
    have hs := hslack i
    dsimp [lower, upper]
    constructor
    · have hmin : min 0 (z.2 i - q.center i) ≤ z.2 i - q.center i :=
        min_le_right _ _
      linarith only [hmin, hs.1]
    · have hmax : z.2 i - q.center i ≤ max 0 (z.2 i - q.center i) :=
        le_max_right _ _
      linarith only [hmax, hs.1]
  · rintro y ⟨x, hx, hxy⟩
    subst y
    rcases hx with ⟨⟨ht0, htz⟩, hv⟩
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine]
      nlinarith [sq_nonneg q.radius]
    · dsimp [parabolicAffine]
      nlinarith
    · intro i
      have hs := hslack i
      have hvi := hv i
      dsimp [parabolicAffine, lower, upper] at hvi ⊢
      have hkappaOne : kappa ≤ 1 := hkappaQuarter.le.trans (by norm_num)
      have hkR : kappa * q.radius ≤ q.radius :=
        by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hkappaOne hR.le
      have hcenterRoom : kappa * q.radius + slack i ≤ 1 - |q.center i| := by
        linarith only [hcenter i, hkR, hs.2.2.1]
      have hzRoom : kappa * q.radius + slack i < 1 - |z.2 i| := by
        linarith only [hzmargin i, hs.2.2.2]
      have hleft : -1 ≤ q.center i +
          (min 0 (z.2 i - q.center i) - kappa * q.radius - slack i) := by
        rcases le_total 0 (z.2 i - q.center i) with hcase | hcase
        · rw [min_eq_left hcase]
          have hcneg : -|q.center i| ≤ q.center i := neg_abs_le _
          linarith only [hcneg, hcenterRoom]
        · rw [min_eq_right hcase]
          have hzneg : -|z.2 i| ≤ z.2 i := neg_abs_le _
          linarith only [hzneg, hzRoom]
      have hright : q.center i +
          (max 0 (z.2 i - q.center i) + kappa * q.radius + slack i) ≤ 1 := by
        rcases le_total 0 (z.2 i - q.center i) with hcase | hcase
        · rw [max_eq_right hcase]
          have hzle : z.2 i ≤ |z.2 i| := le_abs_self _
          linarith only [hzle, hzRoom]
        · rw [max_eq_left hcase]
          have hcle : q.center i ≤ |q.center i| := le_abs_self _
          linarith only [hcle, hcenterRoom]
      rw [abs_le]
      exact ⟨by linarith [hleft, hvi.1], by linarith [hright, hvi.2]⟩

/-- The selected-box scaling factor is positive, below one, and its square is
strictly larger than one half.  The latter is the uniform numerical input for
the fixed-width second propagation rectangle. -/
private theorem selected_alpha_bounds {d : ℕ} {a alpha : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : ℝ) + 2)))) :
    0 < alpha ∧ alpha < 1 ∧ (1 / 2 : ℝ) < alpha ^ 2 := by
  let sharedTerm_3119e36090 := (2 / ((d : ℝ) + 2))
  have hbase : 1 < 1 + a := by linarith
  have hbasePos  := lt_trans zero_lt_one hbase
  have hden : 0 < (d : ℝ) + 2 := by positivity





  have halphaSq : alpha ^ 2 =
      (1 + a) ^ (-(sharedTerm_3119e36090) ) := by
    rw [halpha, ← Real.rpow_natCast, ← Real.rpow_mul hbasePos.le]
    congr 1
    ring


  exact ⟨(by
      rw [halpha]
      exact Real.rpow_pos_of_pos hbasePos _), (by
      rw [halpha]
      exact Real.rpow_lt_one_of_one_lt_of_neg hbase (neg_lt_zero.mpr (one_div_pos.mpr hden))), (show (1 / 2 : ℝ) < (1 + a) ^ (-1 : ℝ) by
          rw [Real.rpow_neg_one]
          rw [← one_div]
          apply (lt_div_iff₀ hbasePos).mpr
          nlinarith).trans_le (by
      rw [halphaSq]
      exact Real.rpow_le_rpow_of_exponent_le hbase.le (neg_le_neg (show sharedTerm_3119e36090 ≤ 1 by
          apply (div_le_iff₀ hden).mpr

          nlinarith)))⟩

/-- A selected crossing of the second ink-spots enlargement supplies the
fixed physical corridor for propagation to the terminal half-cube. -/
theorem selected_inkSpots_forward_corridor
    (d : Nat) (a eta c alpha R0 kappa : Real) (q : InkSpotsBox d)
    (v w : PDE.Vec d)
    (ha0 : 0 < a) (ha1 : a < 1)
    (heta0 : 0 < eta) (heta1 : eta < 1) (hc : 0 < c)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : Real) + 2))))
    (hR0 : R0 ^ 2 = eta * c / 4) (hR0pos : 0 < R0)
    (hkappa : kappa = (1 - alpha ^ 2) * R0 ^ 2)
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d)
    (hv : v ∈ velocityClosedCube (0 : PDE.Vec d) (1 / 2))
    (hcross : (1 + c, w) ∈ inkSpotsQ2 eta q) :
    kappa * q.radius ^ 2 < 1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2) ∧
      1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2) ≤
        kappa⁻¹ * q.radius ^ 2 ∧
      (∀ _i : Fin d, 2 * kappa * q.radius < (1 : Real) - (-1) ∧
        (1 : Real) - (-1) ≤ kappa⁻¹ * q.radius) ∧
      (∀ i, (-1 : Real) + kappa * q.radius ≤ q.center i ∧
        q.center i < (1 : Real) - kappa * q.radius) ∧
      (∀ i, (-1 : Real) + kappa * q.radius < v i ∧
        v i < (1 : Real) - kappa * q.radius) ∧
      parabolicClosedRectangle (d := d)
          (1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2))
          (fun _ => (-1 : Real)) (fun _ => (1 )) ⊆
        (parabolicAffine (d := d) (q.baseTime + alpha ^ 2 * q.radius ^ 2)
          (0 ) 1) ⁻¹' parabolicClosedBox  1 1 0 0 := by
  let sharedTerm_2555de4b20 := ((q.baseTime + alpha ^ 2 * q.radius ^ 2))
  obtain ⟨halpha0, halpha1, halphaHalf⟩ :=
    selected_alpha_bounds ha0 ha1 halpha
  have hetaLeOne  := heta1.le
  have hcNonneg  := hc.le
  obtain ⟨hbase0, hbase1, hRle, hcenter⟩ := inkSpots_source_bounds hR hq
  rcases (mem_inkSpotsQ2_iff.mp hcross) with
    ⟨hcrossLower, hcrossUpper, hcrossCenter, hcrossUnit⟩

  have hR0sqLt : R0 ^ 2 < q.radius ^ 2 := by
    rw [hR0]

    have hcEtaNonneg  :=
      mul_nonneg hcNonneg heta0.le

    nlinarith only [((lt_div_iff₀ heta0).mp (show c < 4 * q.radius ^ 2 / eta by
        change 1 + c < q.baseTime + q.radius ^ 2 +
          4 * q.radius ^ 2 / eta at hcrossUpper
        linarith)), hcEtaNonneg, (mul_le_mul_of_nonneg_left hetaLeOne hcNonneg)]

  have hR0sqLtOne  := hR0sqLt.trans_le (show q.radius ^ 2 ≤ 1 by

      nlinarith)


  have hfactor0 : 0 < 1 - alpha ^ 2 := by
    nlinarith [sq_pos_of_pos halpha0]

  have hkappa0 : 0 < kappa := by
    rw [hkappa]
    exact mul_pos hfactor0 (sq_pos_of_pos hR0pos)
  have hkappaLtR0sq : kappa < R0 ^ 2 := by
    rw [hkappa]

    nlinarith [mul_pos (sq_pos_of_pos hR0pos) (sub_pos.mpr (show 1 - alpha ^ 2 < 1 by linarith))]
  have hkappaLtHalfR0sq : kappa < (1 / 2 : ℝ) * R0 ^ 2 := by
    rw [hkappa]
    exact mul_lt_mul_of_pos_right (show 1 - alpha ^ 2 < 1 / 2 by
        linarith) (sq_pos_of_pos hR0pos)
  have hkappaLtOne  :=
    hkappaLtR0sq.trans hR0sqLtOne

  have htwoKappaLtR : 2 * kappa < q.radius := by


    exact (show 2 * kappa < R0 ^ 2 by
        nlinarith [hkappaLtHalfR0sq]).trans ((show R0 ^ 2 < R0 by
            nlinarith [mul_pos hR0pos (sub_pos.mpr (by
                apply (sq_lt_sq₀ hR0pos.le zero_le_one).mp
                simpa using hR0sqLtOne))]).trans (show R0 < q.radius by
        apply (sq_lt_sq₀ hR0pos.le hR.le).mp
        exact hR0sqLt))

  have hkappaLtRsq  :=
    hkappaLtR0sq.trans hR0sqLt


  have htimeUpper : 1 - (sharedTerm_2555de4b20) ≤
      kappa⁻¹ * q.radius ^ 2 := (show 1 - (sharedTerm_2555de4b20) ≤ 1 by
          have hnonneg  :=
            mul_nonneg (sq_nonneg alpha) (sq_nonneg q.radius)
          linarith).trans (by
          calc
            (1 : ℝ) ≤ q.radius ^ 2 / kappa :=
              (le_div_iff₀ hkappa0).mpr (by
                simpa only [one_mul] using hkappaLtRsq.le)
            _ = kappa⁻¹ * q.radius ^ 2 := by ring)
  refine ⟨(by
      have hmain  :=
        mul_lt_mul_of_pos_right (show kappa < 1 - alpha ^ 2 by
            rw [hkappa]
            have  := hR0sqLtOne
            nlinarith [mul_pos hfactor0 (sub_pos.mpr this)]) (sq_pos_of_pos hR)
      have hrewrite : 1 - (sharedTerm_2555de4b20) =
          (1 - (q.baseTime + q.radius ^ 2)) +
            (1 - alpha ^ 2) * q.radius ^ 2 := by ring
      rw [hrewrite]
      linarith), htimeUpper, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · have hkapRlt : kappa * q.radius < 1 := by
        calc
          kappa * q.radius < 1 * q.radius :=
            mul_lt_mul_of_pos_right hkappaLtOne hR
          _ ≤ 1 := by simpa using hRle
      norm_num
      linarith
    · norm_num
      calc
        (2 : ℝ) ≤ q.radius / kappa :=
          (le_div_iff₀ hkappa0).mpr htwoKappaLtR.le
        _ = kappa⁻¹ * q.radius := by ring
  · intro i
    have hci := hcenter i
    constructor
    · have hkapRle : kappa * q.radius ≤ q.radius := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hkappaLtOne.le hR.le
      have hcneg : -|q.center i| ≤ q.center i := neg_abs_le _
      linarith only [hci, hkapRle, hcneg]
    · have hkapRlt : kappa * q.radius < q.radius :=
        by simpa only [one_mul] using
          mul_lt_mul_of_pos_right hkappaLtOne hR
      have hcle : q.center i ≤ |q.center i| := le_abs_self _
      linarith only [hci, hkapRlt, hcle]
  · intro i
    have hvi := hv i
    simp only [Pi.zero_apply, sub_zero] at hvi
    have hvneg : -|v i| ≤ v i := neg_abs_le _
    have hvle : v i ≤ |v i| := le_abs_self _
    have hkappaHalf : kappa < (1 / 2 : ℝ) := by
      linarith only [htwoKappaLtR, hRle]
    have hkapRHalf : kappa * q.radius < (1 / 2 : ℝ) := by
      calc
        kappa * q.radius ≤ kappa * 1 :=
          mul_le_mul_of_nonneg_left hRle hkappa0.le
        _ < 1 / 2 := by simpa only [mul_one] using hkappaHalf
    constructor <;> linarith only [hvi, hvneg, hvle, hkapRHalf]
  · rintro ⟨t, x⟩ hx
    rw [mem_parabolicClosedRectangle_iff] at hx
    change parabolicAffine sharedTerm_2555de4b20 0 1
        (t, x) ∈ parabolicClosedBox 1 1 0 0
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · have hseedNonneg : 0 ≤ sharedTerm_2555de4b20 :=
        add_nonneg hbase0 (mul_nonneg (sq_nonneg alpha) (sq_nonneg q.radius))
      dsimp [parabolicAffine]
      linarith only [hseedNonneg, hx.1]
    · dsimp [parabolicAffine]
      linarith only [hx.2.1]
    · intro i
      have hxi := hx.2.2 i
      dsimp [parabolicAffine]
      simp only [one_mul, zero_add, sub_zero]
      rw [abs_le]
      exact hxi

end

end HypoellipticAleksandrov.Parabolic
