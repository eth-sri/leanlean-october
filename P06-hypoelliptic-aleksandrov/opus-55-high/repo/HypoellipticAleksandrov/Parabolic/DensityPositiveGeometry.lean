module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import HypoellipticAleksandrov.Parabolic.ForwardPropagationGeometry
public import Mathlib.Tactic

/-!
# Cap-to-stack geometry for positive parabolic density

This module isolates the source-specific, purely geometric part of the two
propagation steps in Krylov--Safonov Lemma 3.3.  It deliberately contains no
coefficient, solution, density-to-point, or forward-propagation assertion.
-/

@[expose] public section

open Set
open scoped Topology

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
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1))
        (r := q.radius) (t0 := q.baseTime) (v0 := q.center)
        (by norm_num) hR)
  have hunit : closure (inkSpotsUnitBox d) =
      parabolicClosedBox 1 1 0 0 := by
    simpa only [inkSpotsUnitBox] using
      (closure_parabolicBox_of_pos (d := d) (vartheta := (1))
        (r := (1)) (t0 := 0) (v0 := (0))
        (by norm_num) (by norm_num))
  rw [← hsource, ← hunit]
  exact closure_mono hq

variable {d : ℕ} {eta zeta kappa : ℝ} {q : InkSpotsBox d}

/-- Elementary endpoint and coordinate consequences of source containment. -/
private theorem inkSpots_source_bounds 
    (hR : 0 < q.radius)
    (hq : inkSpotsSourceBox q ⊆ inkSpotsUnitBox d) :
    0 ≤ q.baseTime ∧ q.baseTime + q.radius ^ 2 ≤ 1 ∧ q.radius ≤ 1 ∧
      ∀ i, |q.center i| + q.radius ≤ 1 := by
  have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hR hq
  have hcenter : (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, fun i => ?_⟩
    · nlinarith [sq_nonneg q.radius]
    · norm_num
    grind
  have hcenterUnit := hclosed hcenter
  rw [mem_parabolicClosedBox_iff] at hcenterUnit
  have hplus : (q.baseTime, q.center + q.radius • (1)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    rw [mem_parabolicClosedBox_iff]
    refine ⟨le_rfl, ?_, ?_⟩
    · simp_all
    · intro i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
      grind
  have hminus : (q.baseTime, q.center - q.radius • (1)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center := by
    aesop
  have hplusUnit := hclosed hplus
  have hminusUnit := hclosed hminus
  rw [mem_parabolicClosedBox_iff] at hplusUnit hminusUnit
  refine ⟨hplusUnit.1, by simp_all, ?_, ?_⟩
  · nlinarith [sq_nonneg (q.radius - 1)]
  · intro i
    have hp := hplusUnit.2.2 i
    have hm := hminusUnit.2.2 i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
      smul_eq_mul, Pi.zero_apply] at hp hm
    grind

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
  rcases hz with ⟨y, hy, hyz⟩
  rcases hy with ⟨⟨hyleft, hyright⟩, hycenter, hyunit⟩
  subst z
  constructor
  · dsimp [inkSpotsContraction]
    have hsquare : 0 < zeta ^ 2 := sq_pos_of_pos hzeta
    have htail : 0 < zeta ^ 2 * (y.1 - (q.baseTime + q.radius ^ 2)) :=
      mul_pos hsquare (by linarith)
    grind
  constructor
  · dsimp [inkSpotsContraction]
    have hsquare : 0 < zeta ^ 2 := sq_pos_of_pos hzeta
    nlinarith
  · intro i
    have hi := hycenter i
    dsimp [inkSpotsContraction]
    rw [add_sub_cancel_left, abs_mul, abs_of_pos hzeta]
    nlinarith

/-- The clipped terminal stack has strict coordinate room inside the unit
box, measured at every contraction factor no larger than `1 - zeta`. -/
private theorem inkSpotsQ3_unit_margin  {z : TimeVelocity d}
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
  have hyabs  := by
    simpa using hyunit i
  have hcabs : |q.center i| ≤ 1 - q.radius := by
    linarith [hcenter i]
  have hrewrite : q.center i + zeta * (y.2 i - q.center i) =
      (1 - zeta) * q.center i + zeta * y.2 i := by ring
  change |q.center i + zeta * (y.2 i - q.center i)| <
    1 - kappa * q.radius
  rw [hrewrite]
  have hcenterTerm : (1 - zeta) * |q.center i| ≤
      (1 - zeta) * (1 - q.radius) :=
    mul_le_mul_of_nonneg_left hcabs (sub_nonneg.mpr hzeta1.le)
  have hyTerm : zeta * |y.2 i| < zeta * 1 :=
    mul_lt_mul_of_pos_left hyabs hzeta
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
private theorem inkSpots_kappa_properties 
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
  obtain ⟨hkappa0, hkappaEta, hkappaZeta, hkappaQuarter⟩ :=
    inkSpots_kappa_properties heta0 heta1 hzeta1 hkappa
  obtain ⟨htlower, htupper, hzcenter⟩ :=
    inkSpotsQ3_bounds heta0 hzeta0 hzeta1 hR hz.1
  obtain ⟨hbase0, hbase1, hRle, hcenter⟩ := inkSpots_source_bounds hR hq
  have hztime : z.1 < 1 := by
    simpa using
      (mem_parabolicBox_iff.mp hz.2).2.1
  have hzmargin  :=
    inkSpotsQ3_unit_margin hzeta0 hzeta1 hR hq hkappaZeta hz
  let slack : PDE.Vec d := inkSpotsCorridorSlack kappa q z
  let lower : PDE.Vec d := fun i =>
    min 0 (z.2 i - q.center i) - kappa * q.radius - slack i
  let upper : PDE.Vec d := fun i =>
    max 0 (z.2 i - q.center i) + kappa * q.radius + slack i
  have hslack : ∀ i, 0 < slack i ∧ slack i ≤ kappa * q.radius / 2 ∧
      slack i ≤ (1 - |q.center i| - kappa * q.radius) / 2 ∧
      slack i ≤ (1 - |z.2 i| - kappa * q.radius) / 2 := by
    intro i
    dsimp [slack, inkSpotsCorridorSlack]
    have hcenterMargin : 0 < 1 - |q.center i| - kappa * q.radius := by
      nlinarith [hcenter i]
    have hhalfKappa : 0 < kappa * q.radius / 2 := by positivity
    grind
  have htimeLower : kappa * q.radius ^ 2 <
      z.1 - (q.baseTime + q.radius ^ 2) := by
    have hgap : kappa < 4 * (1 - zeta ^ 2) / eta := by
      have hrewrite : 4 * (1 - zeta ^ 2) / eta =
          (1 - zeta) * (4 * (1 + zeta) / eta) := by ring
      rw [hrewrite]
      calc
        kappa ≤ 1 - zeta := hkappaZeta
        _ < (1 - zeta) * (4 * (1 + zeta) / eta) := by
          have : 1 < 4 * (1 + zeta) / eta := by
            apply (lt_div_iff₀ heta0).mpr
            nlinarith
          simp_all
    calc
      kappa * q.radius ^ 2 <
          (4 * (1 - zeta ^ 2) / eta) * q.radius ^ 2 :=
        mul_lt_mul_of_pos_right hgap (sq_pos_of_pos hR)
      _ = 4 * (1 - zeta ^ 2) * q.radius ^ 2 / eta := by ring
      _ < z.1 - (q.baseTime + q.radius ^ 2) := htlower
  have htimeUpper : z.1 - (q.baseTime + q.radius ^ 2) ≤
      kappa⁻¹ * q.radius ^ 2 := by
    have hkappaInv : 4 / eta ≤ kappa⁻¹ := by
      rw [le_inv_comm₀ (by positivity) hkappa0]
      simp_all
    have  := by
      calc
        4 * q.radius ^ 2 / eta = (4 / eta) * q.radius ^ 2 := by ring
        _ ≤ kappa⁻¹ * q.radius ^ 2 :=
          mul_le_mul_of_nonneg_right hkappaInv (sq_nonneg q.radius)
    linarith
  refine ⟨lower, upper, htimeLower, htimeUpper, ?_, ?_, ?_, ?_⟩
  · intro i
    have hs := hslack i
    dsimp [lower, upper]
    constructor
    · grind
    · have hdiff : |z.2 i - q.center i| < 3 * zeta * q.radius := hzcenter i
      have hsmall : kappa * (3 * zeta + 3 * kappa) < 1 := by
        calc
          kappa * (3 * zeta + 3 * kappa) ≤
              (eta / 4) * (3 * zeta + 3 * kappa) := by gcongr
          _ < 1 := by nlinarith [hkappaQuarter]
      have hbound : 3 * zeta + 3 * kappa ≤ kappa⁻¹ := by
        rw [← one_div]
        apply (le_div_iff₀ hkappa0).mpr
        linarith
      rcases le_total 0 (z.2 i - q.center i) with hcase | hcase
      · rw [max_eq_right hcase, min_eq_left hcase]
        rw [abs_of_nonneg hcase] at hdiff
        exact (calc
          z.2 i - q.center i + kappa * q.radius + slack i -
              (0 - kappa * q.radius - slack i) =
              (z.2 i - q.center i) + 2 * kappa * q.radius + 2 * slack i := by ring
          _ < (3 * zeta + 3 * kappa) * q.radius := by
            linarith
          _ ≤ kappa⁻¹ * q.radius :=
            mul_le_mul_of_nonneg_right hbound hR.le).le
      · rw [max_eq_left hcase, min_eq_right hcase]
        have hcase' : z.2 i - q.center i ≤ 0 := hcase
        rw [abs_of_nonpos hcase'] at hdiff
        exact (calc
          0 + kappa * q.radius + slack i -
              (z.2 i - q.center i - kappa * q.radius - slack i) =
              -(z.2 i - q.center i) + 2 * kappa * q.radius + 2 * slack i := by ring
          _ < (3 * zeta + 3 * kappa) * q.radius := by
            linarith
          _ ≤ kappa⁻¹ * q.radius :=
            mul_le_mul_of_nonneg_right hbound hR.le).le
  · grind
  · grind
  · rintro y ⟨x, hx, hxy⟩
    subst y
    rcases hx with ⟨⟨ht0, htz⟩, hv⟩
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine]
      positivity
    · dsimp [parabolicAffine]
      nlinarith
    · intro i
      have hvi := hv i
      dsimp [parabolicAffine] at hvi ⊢
      grind

/-- The selected-box scaling factor is positive, below one, and its square is
strictly larger than one half.  The latter is the uniform numerical input for
the fixed-width second propagation rectangle. -/
private theorem selected_alpha_bounds  {a alpha : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : ℝ) + 2)))) :
    0 < alpha ∧ alpha < 1 ∧ (1 / 2 : ℝ) < alpha ^ 2 := by
  have hbase : 1 < 1 + a := by linarith
  have hbasePos : 0 < 1 + a := lt_trans zero_lt_one hbase
  have hden : 0 < (d : ℝ) + 2 := by positivity
  have hexpNeg : -(1 / ((d : ℝ) + 2)) < 0 := by
    simp_all
  have halphaPos : 0 < alpha := by
    rw [halpha]
    positivity
  have halphaLtOne : alpha < 1 := by
    rw [halpha]
    exact Real.rpow_lt_one_of_one_lt_of_neg hbase hexpNeg
  have hfrac : 2 / ((d : ℝ) + 2) ≤ 1 := by
    apply (div_le_iff₀ hden).mpr
    simp
  have halphaSq : alpha ^ 2 =
      (1 + a) ^ (-(2 / ((d : ℝ) + 2)) ) := by
    rw [halpha, ← Real.rpow_natCast, ← Real.rpow_mul hbasePos.le]
    ring
  have hpow : (1 + a) ^ (-1 : ℝ) ≤ alpha ^ 2 := by
    simp_all
  have hinv : (1 / 2) < (1 + a) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg_one, ← one_div]
    apply (lt_div_iff₀ hbasePos).mpr
    nlinarith
  grind

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
          (fun _ => (-1 : Real)) (fun _ => (1 : Real)) ⊆
        (parabolicAffine (d := d) (q.baseTime + alpha ^ 2 * q.radius ^ 2)
          (0 : PDE.Vec d) 1) ⁻¹' parabolicClosedBox (d := d) 1 1 0 0 := by
  obtain ⟨halpha0, halpha1, halphaHalf⟩ :=
    selected_alpha_bounds ha0 ha1 halpha
  obtain ⟨hbase0, hbase1, hRle, hcenter⟩ := inkSpots_source_bounds hR hq
  rcases (mem_inkSpotsQ2_iff.mp hcross) with
    ⟨hcrossLower, hcrossUpper, hcrossCenter, hcrossUnit⟩
  have hspan : c < 4 * q.radius ^ 2 / eta := by
    change 1 + c < q.baseTime + q.radius ^ 2 +
      4 * q.radius ^ 2 / eta at hcrossUpper
    linarith
  have hR0sqLt : R0 ^ 2 < q.radius ^ 2 := by
    have hmul  :=
      (lt_div_iff₀ heta0).mp hspan
    linarith
  have hRsqLe : q.radius ^ 2 ≤ 1 := by
    linarith
  have hR0sqLtOne : R0 ^ 2 < 1 := hR0sqLt.trans_le hRsqLe
  have hR0ltOne : R0 < 1 := by
    apply (sq_lt_sq₀ hR0pos.le zero_le_one).mp
    simp_all
  have hR0ltR : R0 < q.radius := by
    apply (sq_lt_sq₀ hR0pos.le hR.le).mp
    omega
  have hfactor0 : 0 < 1 - alpha ^ 2 := by
    nlinarith [sq_pos_of_pos halpha0]
  have hfactorLtHalf : 1 - alpha ^ 2 < 1 / 2 := by
    linarith
  have hkappa0 : 0 < kappa := by
    simp_all
  have hkappaLtR0sq : kappa < R0 ^ 2 := by
    simp_all
  have hkappaLtHalfR0sq : kappa < (1 / 2) * R0 ^ 2 := by
    simp_all
  have hkappaLtOne : kappa < 1 :=
    hkappaLtR0sq.trans hR0sqLtOne
  have hkappaLtFactor : kappa < 1 - alpha ^ 2 := by
    simp_all
  have htwoKappaLtR : 2 * kappa < q.radius := by
    have hR0sqLtR0 : R0 ^ 2 < R0 := by
      nlinarith [mul_pos hR0pos (sub_pos.mpr hR0ltOne)]
    linarith
  have htimeLower : kappa * q.radius ^ 2 <
      1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2) := by
    have hmain  :=
      mul_lt_mul_of_pos_right hkappaLtFactor (sq_pos_of_pos hR)
    linarith
  have htimeUpperOne  := by
    calc
      (1) ≤ q.radius ^ 2 / kappa :=
        (le_div_iff₀ hkappa0).mpr (by
          linarith)
      _ = kappa⁻¹ * q.radius ^ 2 := by ring
  have htimeLeOne : 1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2) ≤ 1 := by
    have hnonneg  :=
      mul_nonneg (sq_nonneg alpha) (sq_nonneg q.radius)
    linarith
  have htimeUpper : 1 - (q.baseTime + alpha ^ 2 * q.radius ^ 2) ≤
      kappa⁻¹ * q.radius ^ 2 := htimeLeOne.trans htimeUpperOne
  refine ⟨htimeLower, htimeUpper, ?_, ?_, ?_, ?_⟩
  · intro i
    constructor
    · have hkapRlt : kappa * q.radius < 1 := by
        calc
          kappa * q.radius < 1 * q.radius :=
            mul_lt_mul_of_pos_right hkappaLtOne hR
          _ ≤ 1 := by simp_all
      linarith
    · norm_num
      calc
        (2) ≤ q.radius / kappa :=
          (le_div_iff₀ hkappa0).mpr htwoKappaLtR.le
        _ = kappa⁻¹ * q.radius := by ring
  · intro i
    constructor
    · have hkapRle : kappa * q.radius ≤ q.radius := by
        simpa using
          mul_le_mul_of_nonneg_right hkappaLtOne.le hR.le
      grind
    · have hkapRlt : kappa * q.radius < q.radius :=
        by simp_all
      grind
  · intro i
    have hvi := hv i
    simp only [Pi.zero_apply] at hvi
    have hkappaHalf : kappa < (1 / 2 : ℝ) := by
      linarith
    have hkapRHalf : kappa * q.radius < (1 / 2 : ℝ) := by
      calc
        kappa * q.radius ≤ kappa * 1 :=
          mul_le_mul_of_nonneg_left hRle hkappa0.le
        _ < 1 / 2 := by simp_all
    grind
  · rintro ⟨t, x⟩ hx
    rw [mem_parabolicClosedRectangle_iff] at hx
    change parabolicAffine (q.baseTime + alpha ^ 2 * q.radius ^ 2) 0 1
        (t, x) ∈ parabolicClosedBox 1 1 0 0
    rw [mem_parabolicClosedBox_iff]
    refine ⟨?_, ?_, ?_⟩
    · dsimp [parabolicAffine]
      linarith
    · dsimp [parabolicAffine]
      linarith
    · intro i
      have hxi := hx.2.2 i
      dsimp [parabolicAffine]
      grind

end

end HypoellipticAleksandrov.Parabolic
