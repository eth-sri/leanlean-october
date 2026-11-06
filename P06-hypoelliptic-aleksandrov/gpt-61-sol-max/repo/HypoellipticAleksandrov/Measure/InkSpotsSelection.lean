module

public import HypoellipticAleksandrov.Measure.InkSpotsGeometry
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic
import Batteries.Tactic.Alias
import HypoellipticAleksandrov.Parabolic.DensityPositiveGeometry
import Mathlib.Tactic.Linarith



/-!
# Selection geometry for parabolic ink spots

This module proves the purely geometric selected-box step in the
Krylov--Safonov crawling-of-ink-spots argument.  In particular, it contains
the exact shrinking density transfer and extracts a genuine forward-box
crossing from the strict large-outside alternative.  It has no PDE, crossing,
measurability, or countability hypothesis.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace HypoellipticAleksandrov.Parabolic

noncomputable section




variable {d : Nat}

private theorem strictDense_source_bounds  {Gamma : HypoellipticAleksandrov.Parabolic.Region d}
    {xi : Real} {q : InkSpotsBox d} (hq : inkSpotsStrictDense Gamma xi q) :
    0 ≤ q.baseTime ∧ q.baseTime + q.radius ^ 2 ≤ 1 ∧
      ∀ i, |q.center i| + q.radius ≤ 1 := by
  have hclosed := _root_.HypoellipticAleksandrov.Parabolic.inkSpots_closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1

  have hterminalUnit := hclosed (show (q.baseTime + q.radius ^ 2, q.center) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨?_, ?_, fun i => ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · norm_num
      · simp [hq.1.le])
  rw [mem_parabolicClosedBox_iff] at hterminalUnit


  have hplusUnit := hclosed (show (q.baseTime, q.center + q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨le_rfl, ?_, ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · intro i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        rw [add_sub_cancel_left]
        simp [abs_of_nonneg hq.1.le])
  have hminusUnit := hclosed (show (q.baseTime, q.center - q.radius • (1 : PDE.Vec d)) ∈
      parabolicClosedBox 1 q.radius q.baseTime q.center by
      rw [mem_parabolicClosedBox_iff]
      refine ⟨le_rfl, ?_, ?_⟩
      · nlinarith [sq_nonneg q.radius]
      · intro i
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        rw [sub_sub_cancel_left]
        simp [abs_of_nonneg hq.1.le])
  rw [mem_parabolicClosedBox_iff] at hplusUnit hminusUnit
  refine ⟨hplusUnit.1, by norm_num at hterminalUnit ⊢; exact hterminalUnit.2.1, ?_⟩
  intro i
  have hp := hplusUnit.2.2 i
  have hm := hminusUnit.2.2 i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply,
    smul_eq_mul, Pi.zero_apply, sub_zero] at hp hm
  have hp' : q.center i + q.radius * 1 ≤ 1 := (le_abs_self _).trans hp
  have hm' : -(q.center i - q.radius * 1) ≤ 1 := (neg_le_abs _).trans hm
  have habs : |q.center i| ≤ 1 - q.radius := by
    rw [abs_le]
    constructor <;> linarith
  linarith

private theorem parabolicBox_subset_closed  {vartheta r t0 : Real}
    {v0 : PDE.Vec d} :
    parabolicBox vartheta r t0 v0 ⊆ parabolicClosedBox vartheta r t0 v0 := by
  intro z hz
  rw [mem_parabolicBox_iff] at hz
  rw [mem_parabolicClosedBox_iff]
  exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩

private theorem sourceBox_measure_ne_top  (q : InkSpotsBox d) :
    volume (inkSpotsSourceBox q) ≠ ∞ := (measure_ne_top_of_subset parabolicBox_subset_closed
  (IsCompact.measure_ne_top (isCompact_parabolicClosedBox 1 q.radius q.baseTime q.center)))

private theorem inkSpotsQ3_subset_positive_unit
    {Gamma : HypoellipticAleksandrov.Parabolic.Region d} {xi eta zeta : Real} {q : InkSpotsBox d}
    (heta : 0 < eta) (hzeta : 0 < zeta) (hzeta1 : zeta < 1)
    (hq : inkSpotsStrictDense Gamma xi q) :
    inkSpotsQ3 eta zeta q ⊆ Ioi 0 ×ˢ velocityCube (0 : PDE.Vec d) 1 := by
  rintro z hz
  rcases (mem_inkSpotsQ3_iff.mp hz) with ⟨y, hy, hyz⟩
  rcases (mem_inkSpotsQ2_iff.mp hy) with ⟨hyleft, hyright, hycenter, hyunit⟩
  obtain ⟨hbase, hterminal, hcenter⟩ := strictDense_source_bounds hq
  subst z
  constructor
  · dsimp [inkSpotsContraction]
    have hstart : 0 < q.baseTime + q.radius ^ 2 := by
      nlinarith [sq_pos_of_pos hq.1]




    have hrewrite :
        inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - y.1) =
          (1 - zeta ^ 2) * inkSpotsTerminalTime eta q + zeta ^ 2 * y.1 := by
      ring
    change 0 < inkSpotsTerminalTime eta q - zeta ^ 2 *
      (inkSpotsTerminalTime eta q - y.1)
    rw [hrewrite]
    exact add_pos (mul_pos (sub_pos.mpr (by nlinarith)) (show 0 < inkSpotsTerminalTime eta q by
        rw [inkSpotsTerminalTime_eq]
        have hspan : 0 < 4 * q.radius ^ 2 / eta :=
          div_pos (mul_pos (by norm_num) (sq_pos_of_pos hq.1)) heta
        linarith)) (mul_pos (sq_pos_of_pos hzeta) (hstart.trans hyleft))
  · intro i


    have hrewrite : q.center i + zeta * (y.2 i - q.center i) =
        (1 - zeta) * q.center i + zeta * y.2 i := by ring
    change |q.center i + zeta * (y.2 i - q.center i) - 0| < 1
    simp only [sub_zero]
    rw [hrewrite]
    calc
      |(1 - zeta) * q.center i + zeta * y.2 i| ≤
          |(1 - zeta) * q.center i| + |zeta * y.2 i| := abs_add_le _ _
      _ = (1 - zeta) * |q.center i| + zeta * |y.2 i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_pos hzeta]
      _ < (1 - zeta) * 1 + zeta * 1 := by
        have hleft : (1 - zeta) * |q.center i| < (1 - zeta) * 1 :=
          mul_lt_mul_of_pos_left (by
              nlinarith [hcenter i, hq.1]) (sub_pos.mpr hzeta1)
        have hright : zeta * |y.2 i| < zeta * 1 :=
          mul_lt_mul_of_pos_left (by
              simpa only [Pi.zero_apply, sub_zero] using hyunit i) hzeta
        linarith
      _ = 1 := by ring

variable (d : Nat)

private theorem inkSpotsD3_subset_positive_unit  (Gamma : HypoellipticAleksandrov.Parabolic.Region d)
    (xi eta zeta : Real) (heta : 0 < eta) (hzeta : 0 < zeta) (hzeta1 : zeta < 1) :
    inkSpotsD3 Gamma xi eta zeta ⊆ Ioi 0 ×ˢ velocityCube (0 : PDE.Vec d) 1 := by
  intro z hz
  rw [inkSpotsD3] at hz
  rcases Set.mem_iUnion.mp hz with ⟨q, hz⟩
  rcases Set.mem_iUnion.mp hz with ⟨hq, hzq⟩
  exact inkSpotsQ3_subset_positive_unit heta hzeta hzeta1 hq hzq

private theorem volume_closed_unit_slab_toReal  (c : Real) (hc : 0 ≤ c) :
    (volume (Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1)).toReal =
      c * (volume (inkSpotsUnitBox d)).toReal := by
  have hunit : (volume (inkSpotsUnitBox d)).toReal = (2 : Real) ^ d := by
    simpa only [inkSpotsUnitBox, one_mul, zero_add, one_pow, mul_one] using
      (volume_parabolicBox_toReal (d := d) (vartheta := (1 ))
        (r := (1 )) (t₀ := 0) (v₀ := (0 ))
        (by norm_num) (by norm_num))
  calc
    (volume (Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1)).toReal =
        (volume (Icc 1 (1 + c))).toReal *
          (volume (velocityCube (0 : PDE.Vec d) 1)).toReal := by
      rw [Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, ENNReal.toReal_mul]
    _ = c * (2 : Real) ^ d := by
      rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
        volume_velocityCube_toReal (by norm_num : (0 : Real) ≤ 1)]
      ring
    _ = c * (volume (inkSpotsUnitBox d)).toReal := by rw [hunit]

/-- The source box obtained by retaining its base and centre and shrinking its
radius by `alpha`. -/
def inkSpotsShrunkSourceBox {d : Nat} (alpha : Real) (q : InkSpotsBox d) :
    InkSpotsBox d :=
  { radius := alpha * q.radius
    baseTime := q.baseTime
    center := q.center }

variable (d : Nat)

variable (alpha : Real) (q : InkSpotsBox d)

/-- A non-expanding positive radius factor gives nested source boxes. -/
theorem inkSpotsSourceBox_shrunk_subset

    (halpha0 : 0 < alpha) (halpha1 : alpha ≤ 1) :
    inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q) ⊆
      inkSpotsSourceBox q := by
  intro z hz
  rcases z with ⟨t, v⟩
  rw [mem_inkSpotsSourceBox_iff] at hz ⊢
  change q.baseTime < t ∧
    t < q.baseTime + (alpha * q.radius) ^ 2 ∧
      v ∈ velocityCube q.center (alpha * q.radius) at hz
  refine ⟨hz.1, ?_, ?_⟩
  · have hfactor : alpha ^ 2 ≤ 1 := by
      have hnonneg : 0 ≤ (1 - alpha) * (1 + alpha) :=
        mul_nonneg (sub_nonneg.mpr halpha1) (by linarith)
      nlinarith
    nlinarith
  · intro i
    have hi := hz.2.2 i
    have hprod : 0 < alpha * q.radius :=
      lt_of_le_of_lt (abs_nonneg (v i - q.center i)) hi
    nlinarith

/-- The volume of a shrunk source box has the exact parabolic scaling factor. -/
theorem volume_inkSpotsSourceBox_shrunk_toReal

    (halpha : 0 ≤ alpha) (hR : 0 ≤ q.radius) :
    (volume (inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q))).toReal =
      alpha ^ (d + 2) * (volume (inkSpotsSourceBox q)).toReal := by
  change (volume (parabolicBox 1 (alpha * q.radius) q.baseTime q.center)).toReal =
    alpha ^ (d + 2) *
      (volume (parabolicBox 1 q.radius q.baseTime q.center)).toReal
  rw [volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
      (vartheta := (1 )) (r := alpha * q.radius) (t₀ := q.baseTime)
      (v₀ := q.center) (by norm_num) (mul_nonneg halpha hR),
    volume_parabolicBox_toReal_eq_parabolicScaling (d := d)
      (vartheta := (1 )) (r := q.radius) (t₀ := q.baseTime) (v₀ := q.center)
      (by norm_num) hR]
  rw [mul_pow]
  ring

/-- The selected shrinking factor has the reciprocal parabolic volume power. -/
theorem selected_inkSpots_alpha_pow
     (a alpha : Real) (ha : 0 < a)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : Real) + 2)))) :
    alpha ^ (d + 2) = (1 + a)⁻¹ := by

  have hden : (d : Real) + 2 ≠ 0 := by positivity
  calc
    alpha ^ (d + 2) = (1 + a) ^
        (-(1 / ((d : Real) + 2)) * (d + 2 : Real)) := by
      rw [halpha, ← Real.rpow_natCast, ← Real.rpow_mul (show 0 < 1 + a by linarith).le]
      congr 1
      norm_num [Nat.cast_add]
    _ = (1 + a) ^ (-1 : Real) := by
      congr 1
      field_simp [hden]
    _ = (1 + a)⁻¹ := Real.rpow_neg_one _

variable (Gamma : HypoellipticAleksandrov.Parabolic.Region d)

/-- Strict density `a` on a source box transfers to strict density `a^2` on
the selected shrunk source box. -/
theorem inkSpotsStrictDense_shrunkSourceBox
      (a alpha : Real)
    (q : InkSpotsBox d)
    (ha0 : 0 < a) (ha1 : a < 1)
    (halpha : alpha = (1 + a) ^ (-(1 / ((d : Real) + 2))))
    (hq : inkSpotsStrictDense Gamma a q) :
    inkSpotsStrictDense Gamma (a ^ 2) (inkSpotsShrunkSourceBox alpha q) := by
  have halpha0 : 0 < alpha := by
    rw [halpha]
    exact Real.rpow_pos_of_pos (by linarith) _
  have halpha1 : alpha < 1 := by
    rw [halpha]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · linarith
    · have hden : 0 < (d : Real) + 2 := by positivity
      exact neg_lt_zero.mpr (one_div_pos.mpr hden)
  let Q  := inkSpotsSourceBox q
  let Q'  := inkSpotsSourceBox (inkSpotsShrunkSourceBox alpha q)
  have hsub : Q' ⊆ Q := inkSpotsSourceBox_shrunk_subset d alpha q halpha0 halpha1.le
  have hQfinite : volume Q ≠ ∞ := sourceBox_measure_ne_top q

  have hQGammafinite : volume (Q ∩ Gamma) ≠ ∞ :=
    measure_ne_top_of_subset inter_subset_left hQfinite
  have hQdiffFinite : volume (Q \ Q') ≠ ∞ :=
    measure_ne_top_of_subset diff_subset hQfinite
  have hQ'measurable : MeasurableSet Q' := measurableSet_parabolicBox 1 _ q.baseTime q.center
  have hratio : (volume Q').toReal = alpha ^ (d + 2) * (volume Q).toReal := volume_inkSpotsSourceBox_shrunk_toReal d alpha q halpha0.le hq.1.le
  have hpow  :=
    selected_inkSpots_alpha_pow d a alpha ha0 halpha
  have hnum : a + alpha ^ (d + 2) - 1 = a ^ 2 * alpha ^ (d + 2) := by
    rw [hpow]
    have hden : 1 + a ≠ 0 := by linarith
    field_simp [hden]
    ring
  have hinter  := inter_eq_right.mpr hsub
  have hGammaInter : (Q ∩ Gamma) ∩ Q' = Q' ∩ Gamma := by
    ext z
    constructor
    · rintro ⟨⟨hzQ, hzGamma⟩, hzQ'⟩
      exact ⟨hzQ', hzGamma⟩
    · rintro ⟨hzQ', hzGamma⟩
      exact ⟨⟨hsub hzQ', hzGamma⟩, hzQ'⟩
  have hresidual : (Q ∩ Gamma) \ Q' ⊆ Q \ Q' := by
    rintro z ⟨hz, hzQ'⟩
    exact ⟨hz.1, hzQ'⟩
  have hQdecomp : (volume Q').toReal + (volume (Q \ Q')).toReal =
      (volume Q).toReal := by
    simpa only [Measure.real, hinter] using
      (measureReal_inter_add_diff   hQ'measurable hQfinite)
  have hGammaDecomp : (volume (Q' ∩ Gamma)).toReal +
      (volume ((Q ∩ Gamma) \ Q')).toReal = (volume (Q ∩ Gamma)).toReal := by
    simpa only [Measure.real, hGammaInter] using
      (measureReal_inter_add_diff
        hQ'measurable hQGammafinite)
  have hresidualLe  :=
    ENNReal.toReal_mono hQdiffFinite (measure_mono hresidual)
  have hstrict : a * (volume Q).toReal < (volume (Q ∩ Gamma)).toReal := hq.2.2
  have hQnonneg : 0 ≤ (volume Q).toReal := ENNReal.toReal_nonneg

  have hunit : Q' ⊆ inkSpotsUnitBox d := fun z hz => hq.2.1 (hsub hz)
  refine ⟨mul_pos halpha0 hq.1, hunit, ?_⟩
  exact (show a ^ 2 * (volume Q').toReal < (volume (Q' ∩ Gamma)).toReal by
      rw [hratio]
      nlinarith)

/-- A strict large-outside volume alternative contains a strict dense source
box whose forward enlargement contains a point at the time `1 + c`. -/
theorem exists_inkSpotsQ2_crossing_of_volume_outside
      (a eta zeta c : Real)
    (hc : 0 < c)
    (heta0 : 0 < eta) (heta1 : eta < 1)
    (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (houtside : c * (volume (inkSpotsUnitBox d)).toReal <
      (volume (inkSpotsD3 Gamma a eta zeta \ inkSpotsUnitBox d)).toReal) :
    ∃ q : InkSpotsBox d, ∃ w : PDE.Vec d,
      inkSpotsStrictDense Gamma a q ∧ (1 + c, w) ∈ inkSpotsQ2 eta q := by
  let sharedTerm_145105e645 := ((Icc 1 (1 + c) ×ˢ velocityCube (0 : PDE.Vec d) 1))



  have hexists : ∃ z ∈ inkSpotsD3 Gamma a eta zeta, 1 + c < z.1 := by
    by_contra hnone
    push_neg at hnone

    have hmeasure := ENNReal.toReal_mono (show volume sharedTerm_145105e645 ≠ ∞ by
        apply measure_ne_top_of_subset
          (show sharedTerm_145105e645 ⊆
              parabolicClosedBox c 1 1 (0 ) by
            intro z hz
            rw [mem_parabolicClosedBox_iff]
            exact ⟨hz.1.1, by simpa using hz.1.2, fun i => (hz.2 i).le⟩)
        exact (isCompact_parabolicClosedBox c 1 1 (0 : PDE.Vec d)).measure_ne_top) (measure_mono (show inkSpotsD3 Gamma a eta zeta \ inkSpotsUnitBox d ⊆
        sharedTerm_145105e645 by
            rintro z ⟨hzD3, hznotunit⟩
            have hzambient := (inkSpotsD3_subset_positive_unit d Gamma a eta zeta heta0 hzeta0 hzeta1) hzD3
            refine ⟨?_, hzambient.2⟩
            constructor
            · by_contra hlt

              apply hznotunit
              rw [inkSpotsUnitBox, mem_parabolicBox_iff]
              exact ⟨hzambient.1, by simpa using (lt_of_not_ge hlt), hzambient.2⟩
            · exact hnone z hzD3))
    rw [volume_closed_unit_slab_toReal d c hc.le] at hmeasure
    exact (not_lt_of_ge hmeasure) houtside
  rcases hexists with ⟨z, hzD3, hzlarge⟩
  rw [inkSpotsD3] at hzD3
  rcases Set.mem_iUnion.mp hzD3 with ⟨q, hzD3⟩
  rcases Set.mem_iUnion.mp hzD3 with ⟨hq, hzQ3⟩
  rcases (mem_inkSpotsQ3_iff.mp hzQ3) with ⟨y, hyQ2, hyz⟩
  rcases (mem_inkSpotsQ2_iff.mp hyQ2) with ⟨hyleft, hyright, hycenter, hyunit⟩
  obtain ⟨hbase, hsourceTerminal, hcenter⟩ := strictDense_source_bounds hq
  refine ⟨q, y.2, hq, ?_⟩
  rw [mem_inkSpotsQ2_iff]
  refine ⟨?_, ?_, hycenter, hyunit⟩
  · linarith
  · have hgap : 0 < inkSpotsTerminalTime eta q - y.1 := sub_pos.mpr hyright


    exact hzlarge.trans (by
        rw [← hyz]
        exact (by
            dsimp [inkSpotsContraction]
            rw [inkSpotsTerminalTime_eq] at hgap

            nlinarith [mul_pos (sq_pos_of_pos hzeta0) hgap]))

end

end HypoellipticAleksandrov.Parabolic
