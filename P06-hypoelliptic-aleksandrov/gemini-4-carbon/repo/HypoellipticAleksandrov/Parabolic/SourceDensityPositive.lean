module

public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import HypoellipticAleksandrov.Parabolic.SourceDensityNearOne
public import HypoellipticAleksandrov.Parabolic.SourceDensityPositivePropagation
public import HypoellipticAleksandrov.Measure.InkSpots
public import HypoellipticAleksandrov.Measure.InkSpotsSelection

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.Parabolic
open MeasureTheory Set
open scoped ENNReal Topology


/-- The explicit slack in the positive-density descent. -/
def positiveDensityEta (a : ℝ) : ℝ :=
  min (1 / 2) ((a ^ (-(1 / 2 : ℝ)) - 1) / 2)

/-- The terminal contraction parameter in Lemma 3.3. -/
def positiveDensityZeta (d : ℕ) (a : ℝ) : ℝ :=
  a ^ (1 / (2 * ((d : ℝ) + 2)))

/-- The normalized aggregate coefficient controlling one density step. -/
def positiveDensityDescentRatio (a eta : ℝ) : ℝ :=
  (1 + eta) * Real.sqrt a

/-- A canonical point strictly between an admissible ratio and one. -/
def positiveDensityQ (L : ℝ) : ℝ :=
  (1 + L) / 2

/-- The finite density sequence for the explicit descent. -/
def positiveDensityBeta (q a : ℝ) (n : ℕ) : ℝ :=
  q ^ n * a ^ 2



/-- The chosen slack is positive whenever the initial density lies in `(0, 1)`. -/
theorem positiveDensityEta_pos {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) : 0 < positiveDensityEta a := by
  rw [positiveDensityEta]
  apply lt_min
  · norm_num
  · have hpow : 1 < a ^ (-(1 / 2 : ℝ)) :=
      Real.one_lt_rpow_of_pos_of_lt_one_of_neg ha0 ha1 (by norm_num)
    linarith

/-- The chosen slack is strictly less than one. -/
theorem positiveDensityEta_lt_one {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) : positiveDensityEta a < 1 := by
  have heta0 := positiveDensityEta_pos ha0 ha1
  have hetaHalf : positiveDensityEta a ≤ 1 / 2 := by
    rw [positiveDensityEta]
    exact min_le_left _ _
  calc
    positiveDensityEta a < positiveDensityEta a + positiveDensityEta a := by
      linarith
    _ ≤ 1 := by linarith








/-- The canonical eta choice gives a positive normalized descent ratio. -/
theorem positiveDensityCanonicalRatio_pos {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    0 < positiveDensityDescentRatio a (positiveDensityEta a)  := by
  let heta0 := positiveDensityEta_pos ha0 ha1
  rw [positiveDensityDescentRatio]
  positivity

/-- The canonical eta choice gives a strictly subunit descent ratio. -/
theorem positiveDensityCanonicalRatio_lt_one {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) :
    positiveDensityDescentRatio a (positiveDensityEta a) < 1  := by
  have one_add_positiveDensityEta_mul_sqrt_lt_one :
      (1 + positiveDensityEta a) * Real.sqrt a < 1 := by
    have rpow_neg_half_eq_sqrt_inv :
        a ^ (-(1 / 2 : ℝ)) = (Real.sqrt a)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ha0.le]
    have hs0 := Real.sqrt_pos.2 ha0
    have hs1 : Real.sqrt a < 1 := by
      nlinarith [Real.sq_sqrt ha0.le]
    have heta : positiveDensityEta a ≤ (Real.sqrt a)⁻¹ / 2 - 1 / 2 := by
      rw [positiveDensityEta, rpow_neg_half_eq_sqrt_inv]
      calc
        min (1 / 2 : ℝ) (((Real.sqrt a)⁻¹ - 1) / 2) ≤
            ((Real.sqrt a)⁻¹ - 1) / 2 := min_le_right _ _
        _ = (Real.sqrt a)⁻¹ / 2 - 1 / 2 := by ring
    calc
      (1 + positiveDensityEta a) * Real.sqrt a ≤
          (1 + ((Real.sqrt a)⁻¹ / 2 - 1 / 2)) * Real.sqrt a :=
        mul_le_mul_of_nonneg_right (by linarith) hs0.le
      _ = (1 + Real.sqrt a) / 2 := by
        field_simp [hs0.ne']
        ring
      _ < 1 := by linarith
  rw [positiveDensityDescentRatio]
  exact one_add_positiveDensityEta_mul_sqrt_lt_one

/-- The midpoint ratio lies strictly between a positive subunit ratio and one. -/
theorem positiveDensityQ_bounds {L : ℝ}
    (hL0 : 0 < L) (hL1 : L < 1) :
    0 < L ∧ L < positiveDensityQ L ∧ positiveDensityQ L < 1 := by
  rw [positiveDensityQ]
  constructor
  · exact hL0
  constructor <;> linarith



/-- Division by a positive admissible ratio moves a density term below its successor. -/
theorem positiveDensityBeta_step_div {L q a : ℝ} (n : ℕ)
    (hL0 : 0 < L) (hLq : L < q) (hq0 : 0 < q) (ha0 : 0 < a) :
    positiveDensityBeta q a n < positiveDensityBeta q a (n + 1) / L  := by
  have positiveDensityBeta_step_mul :
      L * positiveDensityBeta q a n < positiveDensityBeta q a (n + 1) := by
    have hterm : 0 < q ^ n * a ^ 2 := by positivity
    rw [positiveDensityBeta, pow_succ]
    calc
      L * (q ^ n * a ^ 2) < q * (q ^ n * a ^ 2) :=
        mul_lt_mul_of_pos_right hLq hterm
      _ = q ^ n * q * a ^ 2 := by ring
  rw [lt_div_iff₀ hL0]
  rw [mul_comm]
  exact positiveDensityBeta_step_mul








private theorem inkSpotsD3_finite
    (d : Nat) (Gamma : Set (TimeVelocity d)) (xi eta zeta : Real)
    (heta0 : 0 < eta) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) :
    volume (inkSpotsD3 Gamma xi eta zeta) ≠ ∞  := by
  have inkSpots_radius_le_one_of_strictDense {Gamma : Set (TimeVelocity d)} {xi : Real} {q : InkSpotsBox d} (hq : inkSpotsStrictDense Gamma xi q) :
      q.radius ≤ 1 := by
    have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1
    have htop : (q.baseTime + q.radius ^ 2, q.center) ∈
        parabolicClosedBox 1 q.radius q.baseTime q.center := by
      rw [mem_parabolicClosedBox_iff]
      exact ⟨by linarith [sq_nonneg q.radius], by norm_num, fun i => by simp [hq.1.le]⟩
    have hbottom : (q.baseTime, q.center) ∈
        parabolicClosedBox 1 q.radius q.baseTime q.center := by
      rw [mem_parabolicClosedBox_iff]
      exact ⟨le_rfl, by nlinarith [sq_nonneg q.radius], fun i => by simp [hq.1.le]⟩
    have htop' := hclosed htop
    have hbottom' := hclosed hbottom
    rw [mem_parabolicClosedBox_iff] at htop' hbottom'
    norm_num at htop' hbottom'
    nlinarith [sq_nonneg (q.radius - 1)]
  apply measure_ne_top_of_subset
    (show inkSpotsD3 Gamma xi eta zeta ⊆
        parabolicClosedBox (1 + 4 / eta) 1 0 0 by
      intro z hz
      rw [inkSpotsD3] at hz
      rcases Set.mem_iUnion.mp hz with ⟨q, hz⟩
      rcases Set.mem_iUnion.mp hz with ⟨hq, hzq⟩
      rcases mem_inkSpotsQ3_iff.mp hzq with ⟨y, hy, rfl⟩
      rcases mem_inkSpotsQ2_iff.mp hy with ⟨hyleft, hyright, hycenter, hyunit⟩
      rw [mem_parabolicClosedBox_iff]
      constructor
      · dsimp [inkSpotsContraction]
        have hbase : 0 ≤ q.baseTime := by
          have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1
          have hbottom : (q.baseTime, q.center) ∈
              parabolicClosedBox 1 q.radius q.baseTime q.center := by
            rw [mem_parabolicClosedBox_iff]
            exact ⟨le_rfl, by nlinarith [sq_nonneg q.radius], fun i => by simp [hq.1.le]⟩
          have := hclosed hbottom
          rw [mem_parabolicClosedBox_iff] at this
          exact this.1
        have hTpos : 0 < inkSpotsTerminalTime eta q := by
          rw [inkSpotsTerminalTime_eq]
          exact add_pos (add_pos_of_nonneg_of_pos hbase (sq_pos_of_pos hq.1))
            (div_pos (mul_pos (by norm_num) (sq_pos_of_pos hq.1)) heta0)
        have hzetaSq : zeta ^ 2 < 1 := by nlinarith
        have hrewrite : inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - y.1) =
            (1 - zeta ^ 2) * inkSpotsTerminalTime eta q + zeta ^ 2 * y.1 := by ring
        change 0 ≤ inkSpotsTerminalTime eta q - zeta ^ 2 *
          (inkSpotsTerminalTime eta q - y.1)
        rw [hrewrite]
        exact (add_pos (mul_pos (sub_pos.mpr hzetaSq) hTpos)
          (mul_pos (sq_pos_of_pos hzeta0) ((add_pos_of_nonneg_of_pos hbase (sq_pos_of_pos hq.1)).trans hyleft))).le
      constructor
      · dsimp [inkSpotsContraction]
        have hterminal : q.baseTime + q.radius ^ 2 ≤ 1 := by
          have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1
          have htop : (q.baseTime + q.radius ^ 2, q.center) ∈
              parabolicClosedBox 1 q.radius q.baseTime q.center := by
            rw [mem_parabolicClosedBox_iff]
            exact ⟨by linarith [sq_nonneg q.radius], by norm_num,
              fun i => by simp [hq.1.le]⟩
          have := hclosed htop
          rw [mem_parabolicClosedBox_iff] at this
          norm_num at this
          exact this.2.1
        have hR2' :=
          (sq_le_sq₀ hq.1.le (by norm_num : (0 : ℝ) ≤ 1)).2 (inkSpots_radius_le_one_of_strictDense hq)
        have hR2 : q.radius ^ 2 ≤ 1 := by simpa using hR2'
        have hspan : 4 * q.radius ^ 2 / eta ≤ 4 / eta := by
          apply (div_le_div_iff_of_pos_right heta0).mpr
          nlinarith
        have hT : inkSpotsTerminalTime eta q ≤ 1 + 4 / eta := by
          rw [inkSpotsTerminalTime_eq]
          linarith
        have hleT : inkSpotsTerminalTime eta q - zeta ^ 2 *
            (inkSpotsTerminalTime eta q - y.1) ≤ inkSpotsTerminalTime eta q := by
          exact sub_le_self _ (mul_nonneg (sq_nonneg zeta) (sub_nonneg.mpr hyright.le))
        simpa using hleT.trans hT
      · intro i
        dsimp [inkSpotsContraction]
        have hyabs : |y.2 i| < 1 := by simpa using hyunit i
        have hcenter : |q.center i| + q.radius ≤ 1 := by
          have hclosed := inkSpots_closedSourceBox_subset_closedUnitBox d q hq.1 hq.2.1
          have hp : (q.baseTime, q.center + q.radius • 1) ∈
              parabolicClosedBox 1 q.radius q.baseTime q.center := by
            rw [mem_parabolicClosedBox_iff]
            refine ⟨le_rfl, by nlinarith [sq_nonneg q.radius], ?_⟩
            intro j
            simp [abs_of_nonneg hq.1.le]
          have hm : (q.baseTime, q.center - q.radius • 1) ∈
              parabolicClosedBox 1 q.radius q.baseTime q.center := by
            rw [mem_parabolicClosedBox_iff]
            refine ⟨le_rfl, by nlinarith [sq_nonneg q.radius], ?_⟩
            intro j
            simp [abs_of_nonneg hq.1.le]
          have hp' := hclosed hp
          have hm' := hclosed hm
          rw [mem_parabolicClosedBox_iff] at hp' hm'
          have hplus : q.center i + q.radius ≤ 1 := by
            have := (le_abs_self _).trans (hp'.2.2 i)
            simpa using this
          have hminus : -(q.center i - q.radius) ≤ 1 := by
            simpa using (neg_le_abs _).trans (hm'.2.2 i)
          have habs : |q.center i| ≤ 1 - q.radius := by
            rw [abs_le]
            constructor <;> linarith
          linarith
        have hcabs : |q.center i| < 1 := by linarith [hq.1]
        have hzeta1' := sub_pos.mpr hzeta1
        have hrewrite : q.center i + zeta * (y.2 i - q.center i) =
            (1 - zeta) * q.center i + zeta * y.2 i := by ring
        rw [sub_zero, hrewrite]
        exact (calc
          |(1 - zeta) * q.center i + zeta * y.2 i| ≤
              |(1 - zeta) * q.center i| + |zeta * y.2 i| := abs_add_le _ _
          _ = (1 - zeta) * |q.center i| + zeta * |y.2 i| := by
            rw [abs_mul, abs_mul, abs_of_pos hzeta1', abs_of_pos hzeta0]
          _ < (1 - zeta) * 1 + zeta * 1 := by gcongr
          _ = 1 := by ring).le)
  exact (isCompact_parabolicClosedBox (1 + 4 / eta) 1 0 0).measure_ne_top

private theorem IsParabolicSupersolutionOn.const_smul_source
    {d : Nat} {B : CoefficientField d} {F u : TimeVelocity d → Real}
    {V : Set (TimeVelocity d)} {c : Real}
    (hc : 0 ≤ c)
    (h : IsParabolicSupersolutionOn B (fun z ↦ -F z) u V) :
    IsParabolicSupersolutionOn B (fun z ↦ -(c • F) z) (c • u) V := by
  intro z hz
  rw [parabolicOperator_const_smul]
  change c * parabolicOperator B u z ≥ -(c * F z)
  rw [← mul_neg]
  exact mul_le_mul_of_nonneg_left (h z hz) hc




/-- Krylov--Safonov's finite source-aware descent upgrades the near-one
density relation to every positive density threshold. -/
theorem exists_sourceDensityToPoint_positive
    (d : Nat) (hd : 0 < d) (lam : Real) (hlam : 0 < lam)
    (Lam : Real) (hlamLam : lam ≤ Lam) (beta : Real)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    ∃ g C : Real, 0 < g ∧ g < 1 ∧ 0 ≤ C ∧
      SourceDensityToPoint d lam Lam beta g C       := by
  have source_density_descent_step (a eta zeta L beta₂ beta₁ g₂ C₂ C₀ : Real) (ha0 : 0 < a) (ha1 : a < 1) (heta0 : 0 < eta) (heta1 : eta < 1) (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1) (hL0 : 0 < L) (hfactor : a * (1 + eta) * zeta ^ (-((d : Int) + 2)) = L) (hstep : beta₂ < beta₁ / L) (hC₂ : 0 ≤ C₂) (hC₀ : 0 ≤ C₀) (hseed : SourceDensityToPoint d lam Lam (a ^ 2) (1 / 2) C₀) (hprev : SourceDensityToPoint d lam Lam beta₂ g₂ C₂) (hg₂0 : 0 < g₂) (hg₂1 : g₂ < 1) :
      ∃ g C : Real, 0 < g ∧ g < 1 ∧ 0 ≤ C ∧
      SourceDensityToPoint d lam Lam beta₁ g C := by
    have nonneg_at_terminal_half_cube {d : Nat} {U : Set (TimeVelocity d)} {u : TimeVelocity d → Real} (hU : IsOpen U) (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U) (hu : ContDiffOn Real 2 u U) (hnonneg : IsNonnegativeOn u (parabolicBox 1 1 0 0)) (v : PDE.Vec d) (hv : v ∈ velocityClosedCube 0 (1 / 2)) :
        0 ≤ u (1, v) := by
      have htargetClosed : (1, v) ∈ closure (parabolicBox 1 1 0 0) := by
        rw [closure_parabolicBox_of_pos (by norm_num) (by norm_num)]
        rw [mem_parabolicClosedBox_iff]
        exact ⟨by norm_num, by norm_num, fun i => (hv i).trans (by norm_num)⟩
      have htargetU : (1, v) ∈ U := by
        apply hclosed
        rw [← closure_parabolicBox_of_pos (by norm_num) (by norm_num)]
        exact htargetClosed
      have hmaps : MapsTo u (parabolicBox 1 1 0 0) (Ici 0) := by
        intro y hy
        exact hnonneg y hy
      have himage :=
        ((contDiffAt_of_contDiffOn_of_isOpen hU hu htargetU).continuousAt).continuousWithinAt.mem_closure htargetClosed hmaps
      simpa using himage
    have parabolicLpNormOn_const_smul_of_nonneg {d : Nat} (c : Real) (hc : 0 ≤ c) (F : TimeVelocity d → Real) (S : Set (TimeVelocity d)) :
        parabolicLpNormOn d (c • F) S = c * parabolicLpNormOn d F S := by
      unfold parabolicLpNormOn parabolicELpNormOn
      rw [eLpNorm_const_smul, ENNReal.toReal_mul]
      simp only [Real.enorm_of_nonneg hc, ENNReal.toReal_ofReal hc]
    have unit_high_measurable {U : Set (TimeVelocity d)} {u : TimeVelocity d → Real} (hclosed : parabolicClosedBox 1 1 0 0 ⊆ U) (hu : ContDiffOn Real 2 u U) :
        MeasurableSet (inkSpotsUnitBox d ∩ {z | 1 ≤ u z}) := by
      have hboxU : inkSpotsUnitBox d ⊆ U := by
        intro z hz
        apply hclosed
        rw [inkSpotsUnitBox, mem_parabolicBox_iff] at hz
        rw [mem_parabolicClosedBox_iff]
        exact ⟨hz.1.le, hz.2.1.le, fun i => (hz.2.2 i).le⟩
      have hlow : MeasurableSet (inkSpotsUnitBox d ∩ {z | u z < 1}) := by
        simpa only [inkSpotsUnitBox] using
          measurableSet_parabolicBox_inter_lt_one_of_contDiffOn d U u hboxU hu
      have hbox : MeasurableSet (inkSpotsUnitBox d) := by
        simpa only [inkSpotsUnitBox] using
          (measurableSet_parabolicBox 1 1 0 0)
      have hdiff : inkSpotsUnitBox d \ (inkSpotsUnitBox d ∩ {z | u z < 1}) =
          inkSpotsUnitBox d ∩ {z | 1 ≤ u z} := by
        ext z
        simp only [mem_diff, mem_inter_iff, mem_setOf_eq]
        constructor
        · rintro ⟨hz, hnot⟩
          exact ⟨hz, le_of_not_gt fun hlt => hnot ⟨hz, hlt⟩⟩
        · rintro ⟨hz, hlevel⟩
          exact ⟨hz, fun hlow => (not_lt_of_ge hlevel) hlow.2⟩
      rw [← hdiff]
      exact hbox.diff hlow
    let c : Real := beta₁ / L - beta₂
    have hc : 0 < c := by dsimp [c]; linarith
    obtain ⟨h₃, C₃, hh₃, hC₃, hcap₃⟩ :=
      exists_inkSpotsQ3_source_density_cap d hd lam hlam Lam hlamLam a eta zeta C₀
        ha0 ha1 heta0 heta1 hzeta0 hzeta1 hC₀ hseed
    obtain ⟨hs, Cs, hhs, hCs, hcaps⟩ :=
      exists_selected_inkSpots_source_density_cap d hd lam hlam Lam hlamLam a eta c C₀
        ha0 ha1 heta0 heta1 hc hC₀ hseed
    let g : Real := min (1 / 2) (min (h₃ * g₂ / 2) hs)
    let C : Real := max C₀ (max C₂ (max C₃ Cs))
    have hg0 : 0 < g := by
      dsimp [g]
      exact lt_min (by norm_num) (lt_min (div_pos (mul_pos hh₃ hg₂0) (by norm_num)) hhs)
    have hg1 : g < 1 := by
      calc
        g ≤ 1 / 2 := min_le_left _ _
        _ < 1 := by norm_num
    have hC : 0 ≤ C := by
      dsimp [C]
      exact hC₂.trans
        ((le_max_left C₂ (max C₃ Cs)).trans (le_max_right C₀ (max C₂ (max C₃ Cs))))
    refine ⟨g, C, hg0, hg1, hC, ?_⟩
    intro U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper hdensity v hv
    let Gamma := inkSpotsUnitBox d ∩ {z | 1 ≤ u z}
    have hGamma := unit_high_measurable hclosed hu
    have hGammaUnit : Gamma ⊆ inkSpotsUnitBox d := fun _ hz => hz.1
    have hQmeas : MeasurableSet (inkSpotsUnitBox d) := by
      simpa only [inkSpotsUnitBox] using
        (measurableSet_parabolicBox 1 1 0 0)
    have hQfinite : volume (inkSpotsUnitBox d) ≠ ∞ := by
      simpa only [inkSpotsUnitBox] using volume_parabolicBox_one_ne_top d
    have hQnonneg : 0 ≤ (volume (inkSpotsUnitBox d)).toReal := ENNReal.toReal_nonneg
    change beta₁ * (volume (inkSpotsUnitBox d)).toReal ≤ (volume Gamma).toReal at hdensity
    by_cases hlarge : a * (volume (inkSpotsUnitBox d)).toReal ≤ (volume Gamma).toReal
    · have ha2 : a ^ 2 ≤ a := by nlinarith [mul_nonneg ha0.le (sub_nonneg.mpr ha1.le)]
      have hseedDensity :=
        le_trans (mul_le_mul_of_nonneg_right ha2 hQnonneg) hlarge
      have hseed' := hseed.mono_error (by
        change C₀ ≤ max C₀ (max C₂ (max C₃ Cs))
        exact le_max_left _ _)
      exact (min_le_left _ _).trans (hseed'.apply U B F u hU hclosed hB hu hF hnonneg
        hFnonneg hlower hupper hsuper
        (by simpa only [Gamma, inkSpotsUnitBox] using hseedDensity) v hv)
    have hsubcritical := lt_of_not_ge hlarge
    have haggregate := volume_Gamma_le_inkSpotsD3 d Gamma a eta zeta hGamma hGammaUnit
      ⟨ha0, ha1⟩ ⟨heta0, heta1⟩ ⟨hzeta0, hzeta1⟩ hsubcritical
    rw [hfactor] at haggregate
    let D := inkSpotsD3 Gamma a eta zeta
    have hDfinite : volume D ≠ ∞ := by
      dsimp [D]
      exact inkSpotsD3_finite d Gamma a eta zeta heta0 hzeta0 hzeta1
    have hLbeta : L * beta₂ < beta₁ := by
      rw [lt_div_iff₀ hL0] at hstep
      simpa [mul_comm] using hstep
    have hscaled : L * (beta₂ * (volume (inkSpotsUnitBox d)).toReal) ≤
        L * (volume D).toReal := by
      calc
        L * (beta₂ * (volume (inkSpotsUnitBox d)).toReal) =
            (L * beta₂) * (volume (inkSpotsUnitBox d)).toReal := by ring
        _ ≤ beta₁ * (volume (inkSpotsUnitBox d)).toReal :=
          mul_le_mul_of_nonneg_right hLbeta.le hQnonneg
        _ ≤ (volume Gamma).toReal := hdensity
        _ ≤ L * (volume D).toReal := by simpa using haggregate
    have hDstrong : (beta₁ / L) * (volume (inkSpotsUnitBox d)).toReal ≤
        (volume D).toReal := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hL0).mpr
      calc
        beta₁ * (volume (inkSpotsUnitBox d)).toReal ≤ (volume Gamma).toReal := hdensity
        _ ≤ L * (volume D).toReal := by simpa only [D] using haggregate
        _ = (volume D).toReal * L := by ring
    by_cases hsmall : (volume (D \ inkSpotsUnitBox d)).toReal ≤
        c * (volume (inkSpotsUnitBox d)).toReal
    · have hdecomp : (volume (D ∩ inkSpotsUnitBox d)).toReal +
          (volume (D \ inkSpotsUnitBox d)).toReal = (volume D).toReal := by
        simpa only [Measure.real] using
          (measureReal_inter_add_diff (μ := volume) hQmeas hDfinite)
      have hcapDensity : beta₂ * (volume (inkSpotsUnitBox d)).toReal ≤
          (volume (D ∩ inkSpotsUnitBox d)).toReal := by
        have hcEq : c + beta₂ = beta₁ / L := by dsimp [c]; ring
        nlinarith [hDstrong]
      have hDcap : ∀ z ∈ D ∩ inkSpotsUnitBox d,
          h₃ ≤ u z + C₃ * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
        intro z hz
        dsimp [D] at hz
        rw [inkSpotsD3] at hz
        rcases Set.mem_iUnion.mp hz.1 with ⟨q, hzq⟩
        rcases Set.mem_iUnion.mp hzq with ⟨hq, hzq⟩
        exact hcap₃ U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper q hq z
          ⟨hzq, hz.2⟩
      by_cases herror : h₃ / 2 ≤ C₃ * parabolicLpNormOn d F (parabolicBox 1 1 0 0)
      · have huv := nonneg_at_terminal_half_cube hU hclosed hu hnonneg v hv
        have hC₃C : C₃ ≤ C := by
          change C₃ ≤ max C₀ (max C₂ (max C₃ Cs))
          exact (le_max_left C₃ Cs).trans
            ((le_max_right C₂ (max C₃ Cs)).trans (le_max_right C₀ (max C₂ (max C₃ Cs))))
        have htarget : g ≤ u (1, v) + C * parabolicLpNormOn d F
            (parabolicBox 1 1 0 0) := by
          have hnorm : 0 ≤ parabolicLpNormOn d F (parabolicBox 1 1 0 0) := ENNReal.toReal_nonneg
          calc
            g ≤ h₃ * g₂ / 2 := min_le_right _ _ |>.trans (min_le_left _ _)
            _ ≤ h₃ / 2 := by
              have : h₃ * g₂ < h₃ := by
                nlinarith [mul_pos hh₃ (sub_pos.mpr hg₂1)]
              linarith
            _ ≤ C₃ * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := herror
            _ ≤ C * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by gcongr
            _ ≤ u (1, v) + C * parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by linarith
        exact htarget
      · have hsmallError : C₃ * parabolicLpNormOn d F (parabolicBox 1 1 0 0) < h₃ / 2 :=
          lt_of_not_ge herror
        let k : Real := 2 / h₃
        have hk0 : 0 < k := div_pos (by norm_num) hh₃
        have hsubset : D ∩ inkSpotsUnitBox d ⊆
            inkSpotsUnitBox d ∩ {z | 1 ≤ k • u z} := by
          rintro z ⟨hzD, hzQ⟩
          refine ⟨hzQ, ?_⟩
          change 1 ≤ k * u z
          have hzcap := hDcap z ⟨hzD, hzQ⟩
          have hpoint : h₃ ≤ 2 * u z := by nlinarith [hzcap, hsmallError]
          calc
            1 = h₃ / h₃ := by field_simp [hh₃.ne']
            _ ≤ (2 * u z) / h₃ := (div_le_div_iff_of_pos_right hh₃).mpr hpoint
            _ = (2 / h₃) * u z := by field_simp [hh₃.ne']
        have hnormalfinite : volume (inkSpotsUnitBox d ∩ {z | 1 ≤ k • u z}) ≠ ∞ :=
          measure_ne_top_of_subset inter_subset_left hQfinite
        have hnormalizedDensity :=
          hcapDensity.trans (ENNReal.toReal_mono hnormalfinite (measure_mono hsubset))
        have hprev' := hprev.apply U B (k • F) (k • u) hU hclosed hB
          (by simpa only [Pi.smul_def] using hu.const_smul k)
          (by simpa only [Pi.smul_def] using hF.const_smul k)
          (by
            intro z hz
            change 0 ≤ k * u z
            exact mul_nonneg hk0.le (hnonneg z hz))
          (by
            intro z hz
            change 0 ≤ k * F z
            exact mul_nonneg hk0.le (hFnonneg z hz))
          hlower hupper (hsuper.const_smul_source hk0.le)
          (by simpa [inkSpotsUnitBox] using hnormalizedDensity) v hv
        rw [parabolicLpNormOn_const_smul_of_nonneg k hk0.le F
          (parabolicBox 1 1 0 0)] at hprev'
        change g₂ ≤ k * u (1, v) + C₂ * (k *
          parabolicLpNormOn d F (parabolicBox 1 1 0 0)) at hprev'
        have hC₂C : C₂ ≤ C := by
          change C₂ ≤ max C₀ (max C₂ (max C₃ Cs))
          exact (le_max_left C₂ (max C₃ Cs)).trans (le_max_right C₀ (max C₂ (max C₃ Cs)))
        have hmain : h₃ * g₂ / 2 ≤ u (1, v) + C₂ *
            parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by
          have hfactor : (h₃ / 2) * k = 1 := by
            dsimp [k]
            field_simp [hh₃.ne']
          calc
            h₃ * g₂ / 2 = (h₃ / 2) * g₂ := by ring
            _ ≤ (h₃ / 2) * (k * u (1, v) + C₂ * (k *
                parabolicLpNormOn d F (parabolicBox 1 1 0 0))) :=
              mul_le_mul_of_nonneg_left hprev' (by positivity)
            _ = ((h₃ / 2) * k) * u (1, v) + C₂ * ((h₃ / 2) * k) *
                parabolicLpNormOn d F (parabolicBox 1 1 0 0) := by ring
            _ = u (1, v) + C₂ * parabolicLpNormOn d F
                (parabolicBox 1 1 0 0) := by rw [hfactor]; ring
        have herrorC : u (1, v) + C₂ * parabolicLpNormOn d F
            (parabolicBox 1 1 0 0) ≤ u (1, v) + C * parabolicLpNormOn d F
            (parabolicBox 1 1 0 0) := by
          have hnorm : 0 ≤ parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
            ENNReal.toReal_nonneg
          simpa [add_comm] using
            (add_le_add_left (mul_le_mul_of_nonneg_right hC₂C hnorm) (u (1, v)))
        exact (min_le_right _ _ |>.trans (min_le_left _ _)).trans (hmain.trans herrorC)
    have houtside := lt_of_not_ge hsmall
    obtain ⟨q, w, hq, hcross⟩ :=
      exists_inkSpotsQ2_crossing_of_volume_outside d Gamma a eta zeta c hc heta0 heta1
        hzeta0 hzeta1 (by simpa only [D] using houtside)
    have hterminal := hcaps U B F u hU hclosed hB hu hF hnonneg hFnonneg hlower hupper hsuper
      q w hq hcross v hv
    have hCsC : Cs ≤ C := by
      change Cs ≤ max C₀ (max C₂ (max C₃ Cs))
      exact (le_max_right C₃ Cs).trans
        ((le_max_right C₂ (max C₃ Cs)).trans (le_max_right C₀ (max C₂ (max C₃ Cs))))
    apply (min_le_right _ _ |>.trans (min_le_right _ _)).trans
    apply hterminal.trans
    have hnorm : 0 ≤ parabolicLpNormOn d F (parabolicBox 1 1 0 0) :=
      ENNReal.toReal_nonneg
    simpa [add_comm] using
      (add_le_add_left (mul_le_mul_of_nonneg_right hCsC hnorm) (u (1, v)))
  have source_near_one_square_seed :
      ∃ a C₀ : Real, 0 < a ∧ a < 1 ∧ 0 ≤ C₀ ∧
      SourceDensityToPoint d lam Lam (a ^ 2) (1 / 2) C₀ := by
    obtain ⟨b, hb0, hb1, C₀, hC₀, hseed⟩ :=
      exists_sourceDensityToPoint_near_one d hd lam hlam Lam hlamLam (1 / 2)
        (by norm_num) (by norm_num)
    refine ⟨Real.sqrt b, C₀, Real.sqrt_pos.2 hb0, ?_, hC₀.le, ?_⟩
    · exact (Real.sqrt_lt' (by norm_num : (0 : Real) < 1)).mpr (by simpa using hb1)
    · rw [Real.sq_sqrt hb0.le]
      exact hseed
  have exists_positiveDensityBeta_lt {q : ℝ} {a : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (ha0 : 0 < a) :
      ∃ N : ℕ, positiveDensityBeta q a N < beta := by
    have positiveDensityBeta_succ_lt (n : ℕ) :
        positiveDensityBeta q a (n + 1) < positiveDensityBeta q a n := by
      have hterm : 0 < q ^ n * a ^ 2 := by positivity
      rw [positiveDensityBeta, pow_succ]
      calc
        q ^ n * q * a ^ 2 = q * (q ^ n * a ^ 2) := by ring
        _ < 1 * (q ^ n * a ^ 2) := mul_lt_mul_of_pos_right hq1 hterm
        _ = q ^ n * a ^ 2 := by ring
    have ha2 := sq_pos_of_pos ha0
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hbeta0 ha2) hq1
    refine ⟨N + 1, (positiveDensityBeta_succ_lt N).trans ?_⟩
    rw [positiveDensityBeta]
    exact (lt_div_iff₀ ha2).mp hN
  have positiveDensityAggregateFactor_eq {a : ℝ} {eta : ℝ} (ha0 : 0 < a) :
      a * (1 + eta) * positiveDensityZeta d a ^ (-((d : ℤ) + 2)) =
      positiveDensityDescentRatio a eta := by
    have positiveDensityZeta_zpow_neg_dim_add_two :
        positiveDensityZeta d a ^ (-((d : ℤ) + 2)) = (Real.sqrt a)⁻¹ := by
      have positiveDensityZeta_pow_dim_add_two :
          positiveDensityZeta d a ^ (d + 2) = Real.sqrt a := by
        have zeta_exponent_mul_dim_add_two (d : ℕ) :
            (1 / (2 * ((d : ℝ) + 2))) * ((d + 2 : ℕ) : ℝ) = 1 / 2 := by
          have hdim : 0 < (d : ℝ) + 2 := by positivity
          rw [Nat.cast_add, Nat.cast_ofNat]
          field_simp
        rw [positiveDensityZeta]
        calc
          (a ^ (1 / (2 * ((d : ℝ) + 2)))) ^ (d + 2) =
              a ^ ((1 / (2 * ((d : ℝ) + 2))) * ((d + 2 : ℕ) : ℝ)) :=
            (Real.rpow_mul_natCast ha0.le _ _).symm
          _ = a ^ (1 / 2 : ℝ) := by rw [zeta_exponent_mul_dim_add_two]
          _ = Real.sqrt a := (Real.sqrt_eq_rpow a).symm
      have hindex : -((d : ℤ) + 2) = -((d + 2 : ℕ) : ℤ) := by
        norm_num [Nat.cast_add]
      rw [hindex, zpow_neg, zpow_natCast, positiveDensityZeta_pow_dim_add_two]
    rw [positiveDensityZeta_zpow_neg_dim_add_two, positiveDensityDescentRatio]
    have hs0 := Real.sqrt_pos.2 ha0
    calc
      a * (1 + eta) * (Real.sqrt a)⁻¹ =
          Real.sqrt a ^ 2 * (1 + eta) * (Real.sqrt a)⁻¹ := by
        rw [Real.sq_sqrt ha0.le]
      _ = (1 + eta) * Real.sqrt a := by field_simp [hs0.ne']
  have positiveDensityZeta_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
      positiveDensityZeta d a < 1 := by
    rw [positiveDensityZeta]
    apply Real.rpow_lt_one ha0.le ha1
    positivity
  have positiveDensityZeta_pos {a : ℝ} (ha0 : 0 < a) :
      0 < positiveDensityZeta d a := by
    rw [positiveDensityZeta]
    exact Real.rpow_pos_of_pos ha0 _
  obtain ⟨a, C₀, ha0, ha1, hC₀, hseed⟩ :=
    source_near_one_square_seed
  let eta : Real := positiveDensityEta a
  let zeta : Real := positiveDensityZeta d a
  let L : Real := positiveDensityDescentRatio a eta
  let q : Real := positiveDensityQ L
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact positiveDensityEta_pos ha0 ha1
  have heta1 : eta < 1 := by
    dsimp [eta]
    exact positiveDensityEta_lt_one ha0 ha1
  have hzeta0 : 0 < zeta := by
    dsimp [zeta]
    exact positiveDensityZeta_pos ha0
  have hzeta1 : zeta < 1 := by
    dsimp [zeta]
    exact positiveDensityZeta_lt_one ha0 ha1
  have hL0 : 0 < L := by
    dsimp [L, eta]
    exact positiveDensityCanonicalRatio_pos ha0 ha1
  have hL1 : L < 1 := by
    dsimp [L, eta]
    exact positiveDensityCanonicalRatio_lt_one ha0 ha1
  obtain ⟨-, hLq, hq1⟩ := positiveDensityQ_bounds hL0 hL1
  have hq0 : 0 < q := hL0.trans hLq
  have hfactor : a * (1 + eta) * zeta ^ (-((d : Int) + 2)) = L := by
    dsimp [L, eta, zeta]
    exact positiveDensityAggregateFactor_eq ha0
  have hdescent : ∀ n : Nat, ∃ g C : Real, 0 < g ∧ g < 1 ∧ 0 ≤ C ∧
      SourceDensityToPoint d lam Lam (positiveDensityBeta q a n) g C := by
    intro n
    induction n with
    | zero =>
        refine ⟨1 / 2, C₀, by norm_num, by norm_num, hC₀, ?_⟩
        simpa [positiveDensityBeta] using hseed
    | succ n ih =>
        obtain ⟨g₂, C₂, hg₂0, hg₂1, hC₂, hprev⟩ := ih
        apply source_density_descent_step a eta zeta L
          (positiveDensityBeta q a n) (positiveDensityBeta q a (n + 1)) g₂ C₂ C₀
          ha0 ha1 heta0 heta1 hzeta0 hzeta1 hL0 hfactor
          (positiveDensityBeta_step_div n hL0 hLq hq0 ha0) hC₂ hC₀ hseed hprev hg₂0 hg₂1
  obtain ⟨N, hN⟩ := exists_positiveDensityBeta_lt hq0 hq1 ha0
  obtain ⟨g, C, hg0, hg1, hC, hNrel⟩ := hdescent N
  let g' : Real := min g (1 - beta)
  have hg'0 : 0 < g' := by
    dsimp [g']
    exact lt_min hg0 (sub_pos.mpr hbeta1)
  have hg'1 : g' < 1 := by
    dsimp [g']
    exact (min_le_right _ _).trans_lt (sub_lt_self 1 hbeta0)
  exact ⟨g', C, hg'0, hg'1, hC,
    (SourceDensityToPoint.mono_density hN.le hNrel).mono_value (min_le_left _ _)⟩

end HypoellipticAleksandrov.Parabolic

