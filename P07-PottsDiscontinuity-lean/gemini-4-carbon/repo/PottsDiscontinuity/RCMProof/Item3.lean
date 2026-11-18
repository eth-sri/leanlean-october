module

public import Mathlib
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Duality.Decay
public import PottsDiscontinuity.Duality.DiagonalComparison
public import PottsDiscontinuity.Duality.Discontinuity
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.SixVertex.Sec33Dominance
public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.SixVertex.Sec33RealAnalysis
public import PottsDiscontinuity.Torus.Corollary313Final
public import PottsDiscontinuity.TorusCrossing.Final
public import PottsDiscontinuity.TorusExploration.Contract
public import PottsDiscontinuity.TorusLoops.Lemma314Corrected
public import PottsDiscontinuity.TorusLoops.LoopDensityLogBounds
public import PottsDiscontinuity.TorusRC.CorrelationRate
public import PottsDiscontinuity.TorusRC.Eq315
public import PottsDiscontinuity.TorusRC.MeasureFacts
public import PottsDiscontinuity.TorusTopology.BarrierEvent
public import PottsDiscontinuity.TorusTopology.UnitWindingContract

/-! # Theorem 1.2 assembly: lower bound, Route B nonpercolation, eigenvalue dominance, and final assembly -/

@[expose] public section

open Finset MeasureTheory Filter Topology Real

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity Torus SixVertex

/-! ### 1. Exact-One-Winding Witness and Lower Bound on `ξ⁻¹` -/

private theorem exactOneProbability_pos_of_large_eight_width
    {N M : ℕ} (q : Set.Ici (1 : ℝ)) (hN : Even N) (hM : Even M)
    (hNdiv : 8 ∣ N) (hNlarge : 8 ≤ N) (hMpos : 0 < M) (hMlarge : N / 2 < M) :
    0 < TorusRC.torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1} := by
  have hNpos : 0 < N := by omega
  let W : RCConfig N M := fun e => decide (e.1.val ≠ 1)
  have hnoLeft : ¬ TorusRC.torusRCLeftStripCrossing hNpos hMpos W 1 := by
    rintro ⟨u, v, hu, hv, ⟨w⟩⟩
    cases w with
    | nil => omega
    | cons hadj _ =>
      rename_i z _
      have hzx : z.val.1 = 1 := by
        have h1 : |z.val.1| = 1 := by simpa [hu] using hadj.1.1
        rw [abs_of_nonneg hadj.2.2.2.1] at h1; omega
      have hfirst : (TorusRC.liftedEdgeIndex hNpos hMpos u z).1 = (⟨1, by omega⟩ : Fin N) := by
        apply Fin.ext
        change (TorusRC.periodicCoordinate hNpos (max u.val.1 z.val.1)).val = 1
        rw [hu, hzx, max_eq_right (by norm_num : (0 : ℤ) ≤ 1)]
        exact congrArg Fin.val (TorusTopology.periodicCoordinate_nat hNpos (⟨1, by omega⟩ : Fin N))
      have hopen : W (TorusRC.liftedEdgeIndex hNpos hMpos u z) = true := hadj.2.1
      simp only [W, hfirst, ne_self_iff_false, decide_false, Bool.false_eq_true] at hopen
  have hseam : TorusRC.torusRCSeamAllButOneOpen hMpos W :=
    ⟨⟨1, by omega⟩, rfl, fun i hi => decide_eq_true (fun h => hi (Fin.ext h))⟩
  have hB : W ∈ TorusRC.torusRCBarrier hNpos hMpos 1 := ⟨hnoLeft, hseam⟩
  have hC : W ∈ TorusRC.torusCPrime hNpos hMpos hNdiv hM 1 := by
    obtain ⟨kN, hkN⟩ := hNdiv
    have hcolLt : 3 * (N / 4) + 1 < N := by omega
    have hx : TorusRC.sourceRightColumn N = (3 * (N / 4) : ℕ) := rfl
    have hxEven : Even (TorusRC.sourceRightColumn N) := TorusRC.sourceRightColumn_even ⟨kN, hkN⟩
    have hstripLo : (N / 2 : ℤ) ≤ TorusRC.sourceRightColumn N := by
      rw [hx]; exact_mod_cast (show N / 2 ≤ 3 * (N / 4) by omega)
    have hstripHi : TorusRC.sourceRightColumn N + 1 ≤ (N : ℤ) := by
      rw [hx]; exact_mod_cast (show 3 * (N / 4) + 1 ≤ N by omega)
    have hcolOpen (j : Fin M) : W (⟨3 * (N / 4) + 1, hcolLt⟩, j) = true :=
      decide_eq_true (show 3 * (N / 4) + 1 ≠ 1 by omega)
    have hcolIdx : TorusRC.periodicCoordinate hNpos (TorusRC.sourceRightColumn N + 1) = ⟨3 * (N / 4) + 1, hcolLt⟩ := by
      simpa [TorusRC.sourceRightColumn] using TorusTopology.periodicCoordinate_nat hNpos (⟨3 * (N / 4) + 1, hcolLt⟩ : Fin N)
    change W ∈ TorusRC.liftedCPrime hNpos hMpos (N / 2 : ℤ) (N : ℤ) (TorusRC.sourceRightColumn N) hxEven hM 1 (N / 4)
    simp only [TorusRC.liftedCPrime, Set.mem_ofPred_eq]
    refine ⟨fun j hj => ?_, ?_⟩
    · let t : ℤ := 2 * (j : ℤ)
      let u : CorrLength.RotatedVertex := TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 j
      let v : CorrLength.RotatedVertex := TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (j + 1)
      let z : CorrLength.RotatedVertex := ⟨(TorusRC.sourceRightColumn N + 1, t + 1), by
        rcases hxEven with ⟨x, hxe⟩; exact ⟨x + j + 1, by dsimp [t]; omega⟩⟩
      have huy : u.val.2 = t := by change 2 * (1 : ℤ) * (j : ℤ) = t; simp [t]
      have hvy : v.val.2 = t + 2 := by change 2 * (1 : ℤ) * ((j + 1 : ℕ) : ℤ) = t + 2; simp [t]; ring
      have hidx1 : TorusRC.liftedEdgeIndex hNpos hMpos u z =
          (⟨3 * (N / 4) + 1, hcolLt⟩, TorusRC.periodicCoordinate hMpos (t + 1)) :=
        Prod.ext (Fin.ext (by
          change (TorusRC.periodicCoordinate hNpos (max (TorusRC.sourceRightColumn N) (TorusRC.sourceRightColumn N + 1))).val = _
          rw [max_eq_right (by omega)]; exact congrArg Fin.val hcolIdx))
          (by change TorusRC.periodicCoordinate hMpos (max u.val.2 (t + 1)) = _; rw [huy, max_eq_right (by omega)])
      have hidx2 : TorusRC.liftedEdgeIndex hNpos hMpos z v =
          (⟨3 * (N / 4) + 1, hcolLt⟩, TorusRC.periodicCoordinate hMpos (t + 2)) :=
        Prod.ext (Fin.ext (by
          change (TorusRC.periodicCoordinate hNpos (max (TorusRC.sourceRightColumn N + 1) (TorusRC.sourceRightColumn N))).val = _
          rw [max_eq_left (by omega)]; exact congrArg Fin.val hcolIdx))
          (by change TorusRC.periodicCoordinate hMpos (max (t + 1) v.val.2) = _; rw [hvy, max_eq_right (by omega)])
      have hAdj1 : (TorusRC.liftedStripGraph hNpos hMpos W (N / 2 : ℤ) (N : ℤ)).Adj u z :=
        ⟨by change |TorusRC.sourceRightColumn N - (TorusRC.sourceRightColumn N + 1)| = 1 ∧ |u.val.2 - (t + 1)| = 1; rw [huy]; norm_num,
         by rw [hidx1]; exact hcolOpen _,
         ⟨hstripLo, by change (TorusRC.sourceRightColumn N : ℤ) ≤ N; linarith [hstripHi]⟩,
         ⟨hstripLo.trans (by linarith), hstripHi⟩⟩
      have hAdj2 : (TorusRC.liftedStripGraph hNpos hMpos W (N / 2 : ℤ) (N : ℤ)).Adj z v :=
        ⟨by change |(TorusRC.sourceRightColumn N + 1) - TorusRC.sourceRightColumn N| = 1 ∧ |(t + 1) - v.val.2| = 1; rw [hvy]; norm_num,
         by rw [hidx2]; exact hcolOpen _,
         ⟨hstripLo.trans (by linarith), hstripHi⟩,
         ⟨hstripLo, by change (TorusRC.sourceRightColumn N : ℤ) ≤ N; linarith [hstripHi]⟩⟩
      refine ⟨SimpleGraph.Walk.cons hAdj1 (SimpleGraph.Walk.cons hAdj2 .nil), fun w hw => ?_⟩
      have hR : 2 ≤ (N / 4 : ℤ) := by exact_mod_cast (show 2 ≤ N / 4 by omega)
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · simp [TorusRC.inLiftedBox]; positivity
      · change |(TorusRC.sourceRightColumn N + 1) - TorusRC.sourceRightColumn N| ≤ (N / 4 : ℤ) ∧ |(t + 1) - u.val.2| ≤ (N / 4 : ℤ)
        rw [huy]; constructor <;> norm_num <;> omega
      · change |TorusRC.sourceRightColumn N - TorusRC.sourceRightColumn N| ≤ (N / 4 : ℤ) ∧ |v.val.2 - u.val.2| ≤ (N / 4 : ℤ)
        rw [huy, hvy]; constructor <;> norm_num <;> omega
    · rw [show M / (2 * 1) = M / 2 by omega,
        show TorusRC.liftedChainSite (TorusRC.sourceRightColumn N) hxEven 1 (M / 2) =
          TorusRC.liftedColumnSite (TorusRC.sourceRightColumn N) M hxEven (by exact_mod_cast hM) from
          Subtype.ext (Prod.ext rfl (by rcases hM with ⟨m, hm⟩; change 2 * (1 : ℤ) * ((M / 2 : ℕ) : ℤ) = (M : ℤ); norm_num; omega))]
      exact ⟨SimpleGraph.Walk.nil, by simp [TorusRC.inLiftedBox]; positivity⟩
  exact (TorusRC.torusRCProbability_pos_iff hN hM q _).2
    ⟨W, TorusTopology.hBCU_proved hN hM hNpos hMpos hNdiv 1 (by omega) hMlarge W hB hC⟩

private lemma correctedWeight_eq_mul_densityWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (A : RCConfig N M) :
    Torus.torusCorrectedRCWeight hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ q A =
      Torus.torusRCWeight hN hM q A * TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
  unfold Torus.torusCorrectedRCWeight TorusLoops.windingLoopDensityWeight TorusLoops.windingLoopDensityBase
  ring

private lemma densityWeight_le_one {N M : ℕ}
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (A : RCConfig N M) :
    TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A ≤ 1 := by
  have hsqrt : 2 < Real.sqrt q.val := by nlinarith [Real.sq_sqrt (by linarith [q.property] : 0 ≤ q.val), Real.sqrt_nonneg q.val]
  have hbase : TorusLoops.windingLoopDensityUpperBase q = 1 := by
    unfold TorusLoops.windingLoopDensityUpperBase TorusLoops.windingLoopDensityBase
    exact max_eq_left ((div_le_one (by positivity)).mpr hsqrt.le)
  exact (TorusLoops.windingLoopDensityWeight_le_global hN hM hNp hMp q A).trans (by rw [hbase, one_pow])

private theorem xi_inverse_ge_critical_rate (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv)) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  have hsec_bound {N M : ℕ} (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
      TorusRC.torusRCProbability hN hM q {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} ≤
        q.val ^ 2 * (SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 /
          SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M) := by
    classical
    have hqpos : 0 < q.val := by linarith [q.property]
    let P : RCConfig N M → Prop := fun A => rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1
    let C := Torus.torusNormalization q N M
    let Z0 := SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M
    let Z1 := SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1
    have hC : 0 < C := Torus.torusNormalization_pos q N M
    have hZ0 : 0 < Z0 := SixVertex.Z6V_pos (by positivity) hNp hMp
    have htot := Torus.corollary_313_i_final hN hM q hq ⟨0, hNp⟩ ⟨0, hMp⟩
    have hone : (∑ A ∈ Finset.univ.filter P, Torus.torusCorrectedRCWeight hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ q A) ≤ 4 * C * Z1 := by
      rw [Finset.sum_subtype (p := P) (Finset.univ.filter P) (fun _ => by simp)]
      exact Torus.corollary_313_ii_final hN hM q hq ⟨0, hNp⟩ ⟨0, hMp⟩
    have hden : C * Z0 ≤ TorusRC.torusRCPartition hN hM q := by
      rw [show TorusRC.torusRCPartition hN hM q = ∑ A, Torus.torusRCWeight hN hM q A from rfl, ← htot]
      exact Finset.sum_le_sum fun A _ => by
        rw [correctedWeight_eq_mul_densityWeight]
        exact mul_le_of_le_one_right (TorusRC.torusRCWeight_pos hN hM q A).le (densityWeight_le_one hN hM hNp hMp q hq A)
    have hnum : (∑ A ∈ Finset.univ.filter P, Torus.torusRCWeight hN hM q A) ≤ q.val ^ 2 * C * Z1 := by
      have h1 : (∑ A ∈ Finset.univ.filter P, Torus.torusRCWeight hN hM q A) ≤
          (q.val ^ 2 / 4) * ∑ A ∈ Finset.univ.filter P, Torus.torusCorrectedRCWeight hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ q A := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun A hA => ?_
        have hcount := TorusTopology.windingLoopCount_eq_two_of_U_eq_one hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A (Finset.mem_filter.mp hA).2
        have hpow : q.val⁻¹ ≤ (q.val ^ Torus.rcNetIndicator hN hM A)⁻¹ := by
          unfold Torus.rcNetIndicator; split_ifs
          · simp
          · norm_num; exact inv_le_one_of_one_le₀ q.property
        have hfge : 4 / q.val ^ 2 ≤ TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
          unfold TorusLoops.windingLoopDensityWeight TorusLoops.windingLoopDensityBase
          rw [hcount, div_pow, Real.sq_sqrt hqpos.le, div_eq_mul_inv]
          refine (show 4 / q.val ^ 2 = (2 ^ 2 / q.val) * q.val⁻¹ by field_simp; ring).trans_le ?_
          exact mul_le_mul_of_nonneg_left hpow (by positivity)
        have hc1 : 1 ≤ (q.val ^ 2 / 4) * TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
          have := mul_le_mul_of_nonneg_left hfge (show 0 ≤ q.val ^ 2 / 4 by positivity)
          rwa [show q.val ^ 2 / 4 * (4 / q.val ^ 2) = 1 by field_simp] at this
        rw [correctedWeight_eq_mul_densityWeight]
        nlinarith [(TorusRC.torusRCWeight_pos hN hM q A).le]
      exact h1.trans ((mul_le_mul_of_nonneg_left hone (by positivity)).trans_eq (by ring))
    have hprob : TorusRC.torusRCProbability hN hM q {A | P A} =
        (∑ A ∈ Finset.univ.filter P, Torus.torusRCWeight hN hM q A) / TorusRC.torusRCPartition hN hM q := by
      rw [TorusRC.torusRCProbability_eq_sum]; simp only [Set.indicator_apply, TorusRC.torusRCMass]
      rw [Finset.sum_div, ← Finset.sum_filter]; rfl
    have hZ1 : 0 ≤ Z1 := (SixVertex.Z6Vr_pos (by positivity) hNp hMp (by obtain ⟨k, hk⟩ := hN; omega)).le
    rw [hprob]
    exact ((div_le_div_of_nonneg_right hnum (TorusRC.torusRCPartition_pos hN hM q).le).trans
      (div_le_div_of_nonneg_left (by positivity) (mul_pos hC hZ0) hden)).trans_eq
      (by dsimp [Z0, Z1] at hZ0 ⊢; field_simp [hC.ne', hZ0.ne'])
  have hliminf {N : ℕ} (hN : Even N) (hNlarge : 8 ≤ N) (hNdiv : 8 ∣ N) {δ : ℝ} (hδ : 0 < δ) :
      Filter.liminf (TorusRC.torusRCUOneRateE hN q) atTop ≤
        ((Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 1) -
          Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0) + δ : ℝ) : EReal) := by
    have hNpos : 0 < N := by omega
    have hMseq : Tendsto TorusRC.positiveEvenPeriod atTop atTop :=
      tendsto_atTop.2 fun K => by filter_upwards [eventually_ge_atTop K] with m hm; dsimp [TorusRC.positiveEvenPeriod]; omega
    let c := Real.sqrt (2 + Real.sqrt q.val)
    have hc : 0 < c := by positivity
    let gap := Real.log (SixVertex.Lambda c N 1) - Real.log (SixVertex.Lambda c N 0)
    have hsecBdd : IsBoundedUnder (· ≤ ·) atTop
        (fun M : ℕ => (1 / (M : ℝ)) * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) := by
      refine isBoundedUnder_of_eventually_le (a := 0) ?_
      filter_upwards [eventually_gt_atTop 0] with M hM
      have hZle : SixVertex.Z6Vr c N M 1 ≤ SixVertex.Z6V c N M := by
        rw [SixVertex.Z6Vr_eq_trace_block hNpos hM c (by omega), ← SixVertex.Z6Vn_eq_trace_block hNpos hM c]
        exact SixVertex.Z6Vn_le_Z6V hc.le hM (by omega)
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos
        (div_pos (SixVertex.Z6Vr_pos hc hNpos hM (by omega)) (SixVertex.Z6V_pos hc hNpos hM)).le
        ((div_le_one (SixVertex.Z6V_pos hc hNpos hM)).2 hZle))
    have hsecEv := hMseq.eventually (eventually_lt_of_limsup_lt
      (lt_of_le_of_lt (SixVertex.limsup_log_Z6V_ratio_le_center hc hNpos (by omega)) (show gap < gap + δ / 2 by linarith)) hsecBdd)
    have hconstEv := ((tendsto_natCast_atTop_atTop.comp hMseq).const_div_atTop (Real.log (q.val ^ 2))).eventually
      (Iio_mem_nhds (show (0 : ℝ) < δ / 2 by linarith))
    have hrateEv : ∀ᶠ m : ℕ in atTop, TorusRC.torusRCUOneRateE hN q m ≤ (gap + δ : EReal) := by
      filter_upwards [hMseq.eventually (eventually_gt_atTop (N / 2)), hsecEv, hconstEv] with m hmL hsec hcm
      let M := TorusRC.positiveEvenPeriod m
      have hMp := TorusRC.positiveEvenPeriod_pos m; have hM := TorusRC.positiveEvenPeriod_even m
      have hprob := hsec_bound hN hM hNpos hMp
      have hpos := exactOneProbability_pos_of_large_eight_width q hN hM hNdiv hNlarge hMp hmL
      have hratPos : 0 < SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M :=
        div_pos (SixVertex.Z6Vr_pos hc hNpos hMp (by omega)) (SixVertex.Z6V_pos hc hNpos hMp)
      have hlog := Real.log_le_log hpos hprob
      rw [Real.log_mul (by positivity) hratPos.ne'] at hlog
      have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
      rw [add_div] at hdiv; rw [one_div_mul_eq_div] at hsec
      apply EReal.coe_le_coe_iff.mpr
      dsimp [M, Function.comp_def] at hdiv hsec hcm; exact hdiv.trans (by linarith)
    exact liminf_le_of_frequently_le' hrateEv.frequently
  obtain ⟨B, S, hS, hroot⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let c := Real.sqrt (2 + Real.sqrt q.val)
  have hc : 0 < c := by positivity
  let idx (j : ℕ) := 2 * (j + 1) + B % 2
  let kSeq (j : ℕ) := (idx j + B) / 2 - 1
  have hidxAtTop : Tendsto idx atTop atTop :=
    tendsto_atTop.2 fun K => by filter_upwards [eventually_ge_atTop K] with j hj; dsimp [idx]; omega
  have hkSeqAtTop : Tendsto kSeq atTop atTop :=
    tendsto_atTop.2 fun K => by filter_upwards [eventually_ge_atTop K] with j hj; dsimp [kSeq, idx]; omega
  have hw8 (j : ℕ) : TorusRC.eightfoldPeriod (kSeq j) = 4 * (idx j + B) := by dsimp [TorusRC.eightfoldPeriod, kSeq, idx]; omega
  have hgap : Tendsto (fun j => Real.log (SixVertex.Lambda c (4 * (idx j + B)) 1) -
      Real.log (SixVertex.Lambda c (4 * (idx j + B)) 0)) atTop (𝓝 (-R)) := by
    have hroot' : Tendsto (fun j => SixVertex.Lambda c (4 * (idx j + B)) 1 / SixVertex.Lambda c (4 * (idx j + B)) 0)
        atTop (𝓝 (Real.exp (-R))) := by simpa [Function.comp_def, R, c] using hroot.comp hidxAtTop
    have hlog := (Real.continuousAt_log (Real.exp_pos (-R)).ne').tendsto.comp hroot'
    rw [Real.log_exp] at hlog
    refine hlog.congr fun j => ?_
    exact Real.log_div (SixVertex.Lambda_pos hc (show 1 ≤ 4 * (idx j + B) / 2 by dsimp [idx]; omega)).ne'
      (SixVertex.Lambda_pos hc (Nat.zero_le _)).ne'
  let outer8 (k : ℕ) := liminf (TorusRC.torusRCUOneRateE (TorusRC.eightfoldPeriod_even k) q) atTop
  obtain ⟨_, _, hrot, hdiag⟩ := CorrLength.rotated_correlation_rate_exists_for_limit (FK.criticalParameters q) μ hμ
  have hxiCan : ξinv = TorusRC.inverseCorrelationLength q :=
    (tendsto_nhds_unique hRate hdiag).trans (tendsto_nhds_unique hrot (TorusRC.tendsto_inverseCorrelationLength q))
  have hW21 : (-(ξinv : ℝ) : EReal) ≤ liminf outer8 atTop := by
    rw [hxiCan]; exact TorusRC.eq315 q (TorusCrossing.h319_proved q)
  refine ⟨S, hS, ?_⟩
  by_contra hnot
  let ε := (R - ξinv) / 2
  have hε : 0 < ε := by dsimp [ε, R] at *; linarith
  have hfreq : ∃ᶠ n : ℕ in atTop, outer8 n ≤ ((-R + ε : ℝ) : EReal) := by
    rw [frequently_atTop']; intro K
    obtain ⟨J₁, hJ₁⟩ := eventually_atTop.1 (hgap.eventually (Iio_mem_nhds (show -R < -R + ε / 2 by linarith)))
    obtain ⟨J₂, hJ₂⟩ := eventually_atTop.1 (hkSeqAtTop.eventually (eventually_gt_atTop K))
    let j := max J₁ J₂
    refine ⟨kSeq j, hJ₂ j (le_max_right _ _), ?_⟩
    have hf := hliminf (TorusRC.eightfoldPeriod_even (kSeq j)) (by dsimp [TorusRC.eightfoldPeriod]; omega)
      (TorusRC.eightfoldPeriod_dvd (kSeq j)) (show 0 < ε / 2 by linarith)
    refine hf.trans (EReal.coe_le_coe_iff.mpr ?_)
    have hj1 := hJ₁ j (le_max_left _ _)
    rw [hw8 j]; linarith
  have hle := EReal.coe_le_coe_iff.mp (hW21.trans (liminf_le_of_frequently_le' hfreq))
  dsimp [ε] at hle; linarith

/-! ### 2. Route B Nonpercolation, Lemma 3.14 Cutoff, and Upper Bound on `ξ⁻¹` -/

private theorem routeB_nonpercolation_and_square_boundary_decay
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv)) :
    0 < ξinv ∧
    Tendsto (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique (TorusLoops.rectangleFKParameters q)))
      (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ)) atTop (𝓝 0) := by
  have := hμ.1
  obtain ⟨S, hS, hxi⟩ := xi_inverse_ge_critical_rate q hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := (arcosh_pos_of_gt4 q.val hq).1
  obtain ⟨S₀, _, hS₀, _, hpositive, _⟩ := identity44 lam hlam
  have hxiPos : 0 < ξinv := lt_of_lt_of_le (tendsto_nhds_unique hS hS₀ ▸ hpositive) (by simpa [lam] using hxi)
  have hRateDual : Tendsto (fun n : ℕ => -(1 / (n : ℝ)) * Real.log (Duality.twoPoint μ (diagonalSite n))) atTop (𝓝 ξinv) :=
    hRate.congr fun n => by
      have hev : CorrLength.connectionEvent (0, 0) (diagonalSite n) = Duality.connectionEvent 0 (diagonalSite n) :=
        Set.ext fun ω => CorrLength.connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω
      rw [hev]; simp only [Duality.twoPoint, div_eq_mul_inv]; ring
  obtain ⟨C, c, _, hc, hdecay⟩ := Duality.free_exponential_decay_of_pos_diagonal_rate
    (FK.criticalParameters q) μ hμ ξinv hxiPos hRateDual
  have hclusterBound (x : ℤ × ℤ) : μ (Duality.connectionEvent (0, 0) x) ≤
      ENNReal.ofReal (C * Real.exp (-c * (|(x.1 : ℝ)| + |(x.2 : ℝ)|))) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    exact ENNReal.ofReal_le_ofReal (hdecay x)
  have hno : μ (Duality.infiniteClusterAt (0, 0)) = 0 :=
    Duality.infiniteClusterAt_zero_of_exponential_decay μ C c hc hclusterBound
  let θ : FK.Parameters := TorusLoops.rectangleFKParameters q
  let ν : ProbabilityMeasure FK.LatticeConfiguration := Classical.choose (FK.freeBoxLimit_existsUnique θ)
  have hweak := (Classical.choose_spec (FK.freeBoxLimit_existsUnique θ)).1
    (fun _ => (0, 0)) (fun n => n) FK.origin_latticeBox_nested FK.origin_latticeBox_exhaustive
  have hμν : μ = ν.toMeasure :=
    rc_limit_unique θ.toP θ.toQ 0 μ ν.toMeasure hμ (FK.isRCInfiniteVolumeLimit_of_freeBox_tendsto θ ν hweak)
  have hnoν : ν.toMeasure (RCInfinite.infiniteAt (0, 0)) = 0 := by
    rw [← hμν]; simpa [Duality.infiniteClusterAt, Duality.cluster, RCInfinite.infiniteAt, RCInfinite.cluster] using hno
  have hzeroReal : Tendsto (fun n => (ν.toMeasure (Zhang.boundaryConnectionEvent n)).toReal) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp
      ((Zhang.tendsto_boundaryConnection_zero_iff ν.toMeasure).2 hnoν)
  refine ⟨hxiPos, hzeroReal.congr fun n => ?_⟩
  exact (ProbabilityMeasure.measureReal_eq_coe_coeFn ν (Zhang.boundaryConnectionEvent n))

private theorem lemma314_eventual_bound
    (q : Set.Ici (1 : ℝ))
    (hzero : Tendsto (fun n => (((Classical.choose (FK.freeBoxLimit_existsUnique (TorusLoops.rectangleFKParameters q)))
      (Zhang.boundaryConnectionEvent n) : NNReal) : ℝ)) atTop (𝓝 0))
    {bound : ℝ} (hbound : 0 < bound) :
    ∃ Ncut : ℕ, ∀ (N : ℕ) (hN : Even N) (hNp : 0 < N), Ncut ≤ N →
      ∀ᶠ m : ℕ in atTop,
        |Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hN (TorusRC.positiveEvenPeriod_even m)
          hNp (TorusRC.positiveEvenPeriod_pos m) q) / (TorusRC.positiveEvenPeriod m : ℝ)| ≤ bound := by
  obtain ⟨Nlim, hlim⟩ := TorusLoops.lemma_3_14_corrected_limsup q hzero (bound / 2) (by linarith)
  have hdecay := TorusLoops.tendsto_rectangleFreeOneArmProbability_of_boundaryConnection_zero q hzero
  obtain ⟨Narm, harm⟩ := eventually_atTop.1 ((hdecay.eventually
    (Iio_mem_nhds (TorusLoops.windingLoopTailArmThreshold_pos q 1))).mono fun _ h => h.le)
  refine ⟨max Nlim.val Narm, fun N hN hNp hlarge => ?_⟩
  have hlimN := hlim N hN ((le_max_left _ _).trans hlarge)
  have harmN := harm N ((le_max_right _ _).trans hlarge)
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (fun n => |TorusLoops.windingLoopDensityLogRate hN hNp q n|) := by
    let C₀ := TorusLoops.windingLoopDensityLogOffset q
    let C₁ := TorusLoops.windingLoopDensityLogSlope q
    have hC₀ := TorusLoops.windingLoopDensityLogOffset_nonneg q
    have hC₁ := TorusLoops.windingLoopDensityLogSlope_nonneg q
    refine isBoundedUnder_of_eventually_le (a := C₁ / 2 + (C₀ + C₁) / 2) ?_
    filter_upwards [eventually_ge_atTop (9 * N)] with n hn
    have hrate := TorusLoops.abs_windingLoopDensityLogRate_le hN hNp q 1 n (by norm_num)
      (by omega) (by omega) harmN
    have h1 : |TorusLoops.windingLoopDensityLogRate hN hNp q n| ≤ C₁ / 2 + (C₀ + C₁) / (2 * ((n + 1 : ℕ) : ℝ)) := by
      simpa [C₀, C₁] using hrate
    have hden : 2 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
      linarith
    exact h1.trans (add_le_add le_rfl (div_le_div_of_nonneg_left (add_nonneg hC₀ hC₁) (by norm_num) hden))
  filter_upwards [eventually_lt_of_limsup_lt (lt_of_le_of_lt hlimN (by linarith : bound / 2 < bound)) hbdd] with m hm
  simpa [TorusLoops.windingLoopDensityLogRate, TorusRC.positiveEvenPeriod] using hm.le

private theorem upperTail_factorization_and_pos
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) {N M : ℕ}
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) {r : ℕ} (hr : r ≤ N / 2) :
    0 < TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q ∧
    0 < TorusRC.torusRCProbability hN hM q (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r) ∧
    SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
        (TorusRC.torusRCProbability hN hM q (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r) /
          TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q) := by
  classical
  let c := Real.sqrt (2 + Real.sqrt q.val)
  let C := Torus.torusNormalization q N M
  let E := TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r
  let expLoop := TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q
  let probTail := TorusRC.torusRCProbability hN hM q E
  have hC : 0 < C := Torus.torusNormalization_pos q N M
  have hP : 0 < TorusRC.torusRCPartition hN hM q := TorusRC.torusRCPartition_pos hN hM q
  have htot := Torus.corollary_313_i_final hN hM q hq ⟨0, hNp⟩ ⟨0, hMp⟩
  have hexp_eq : expLoop = (∑ A : RCConfig N M, Torus.torusCorrectedRCWeight hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ q A) /
      TorusRC.torusRCPartition hN hM q := by
    unfold expLoop TorusLoops.phi_T_windingLoopDensityExpectation TorusRC.torusRCMass
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun A _ => by rw [correctedWeight_eq_mul_densityWeight]; ring
  have hEpos : 0 < expLoop := by
    rw [hexp_eq, htot]
    exact div_pos (mul_pos hC (SixVertex.Z6V_pos (by positivity) hNp hMp)) hP
  have hsec : C * SixVertex.Z6Vr c N M r ≤
      ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E),
        Torus.torusCorrectedRCWeight hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ q A := by
    rw [Finset.sum_subtype (p := fun A => r ≤ rcVerticalWinding hN hM ⟨0, hMp⟩ A)
      (Finset.univ.filter (fun A : RCConfig N M => A ∈ E))
      (fun _ => by simp [E, TorusRC.torusRCVerticalTail])]
    exact Torus.corollary_313_iii_final hN hM q hq ⟨0, hNp⟩ ⟨0, hMp⟩ r
  have hprob : TorusRC.torusRCPartition hN hM q * probTail =
      ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), Torus.torusRCWeight hN hM q A := by
    dsimp [probTail]; rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply, TorusRC.torusRCMass]
    rw [← Finset.sum_filter, ← Finset.sum_div]; exact mul_div_cancel₀ _ hP.ne'
  have htail : C * SixVertex.Z6Vr c N M r ≤ TorusRC.torusRCPartition hN hM q * probTail :=
    hsec.trans <| (Finset.sum_le_sum fun A _ => by
      rw [correctedWeight_eq_mul_densityWeight]
      exact mul_le_of_le_one_right (TorusRC.torusRCWeight_pos hN hM q A).le
        (densityWeight_le_one hN hM hNp hMp q hq A)).trans hprob.symm.le
  have hexp_mul : expLoop * TorusRC.torusRCPartition hN hM q = C * SixVertex.Z6V c N M := by
    rw [hexp_eq, htot, div_mul_cancel₀ _ hP.ne']
  have hfact : SixVertex.Z6Vr c N M r ≤ SixVertex.Z6V c N M * (probTail / expLoop) := by
    refine (mul_le_mul_iff_of_pos_left hC).mp ?_
    have hmul := mul_le_mul_of_nonneg_left htail hEpos.le
    rw [← mul_assoc _ _ probTail, hexp_mul] at hmul
    exact ((le_div_iff₀' hEpos).mpr hmul).trans_eq (by ring)
  have hPpos : 0 < probTail := by
    by_contra hnot
    have hZ := SixVertex.Z6V_pos (by positivity : 0 < c) hNp hMp
    have hZr := SixVertex.Z6Vr_pos (by positivity : 0 < c) hNp hMp hr
    linarith [mul_nonpos_of_nonneg_of_nonpos hZ.le (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hEpos.le)]
  exact ⟨hEpos, hPpos, hfact⟩

private theorem upperTailRateEventually
    (q : Set.Ici (1 : ℝ)) (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv))
    {r : ℕ} (hr1 : 1 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m < -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  have hnp (n m : ℕ) : TorusRC.positiveEvenVerticalTailRateE q r n m ≤ 0 :=
    EReal.coe_le_coe_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (TorusRC.torusRCVerticalTail_log_nonpos _ _ q _ r) (Nat.cast_nonneg _))
  let u (n : ℕ) : EReal := limsup (fun m => TorusRC.positiveEvenVerticalTailRateE q r n m) atTop
  have huBdd : IsBoundedUnder (· ≤ ·) atTop u :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => by
      simpa using limsup_le_limsup (v := fun _ : ℕ => (0 : EReal)) (Eventually.of_forall (hnp n)))
  have hlt : limsup u atTop < ((-((r - 1 : ℕ) : ℝ) * ξinv + δ : ℝ) : EReal) :=
    lt_of_le_of_lt (TorusExploration.contract_eq316 q μ hμ ξinv hRate r hr1) (EReal.coe_lt_coe_iff.mpr (by linarith))
  filter_upwards [eventually_lt_of_limsup_lt hlt huBdd] with n hn
  filter_upwards [eventually_lt_of_limsup_lt hn (isBoundedUnder_of_eventually_le (Eventually.of_forall (hnp n)))] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

private theorem rc_xi_inverse_le_critical_rate (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (μ : Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv)) :
    ∃ S : ℝ,
      Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨hxiPos, hzeroSq⟩ := routeB_nonpercolation_and_square_boundary_decay q hq μ hμ ξinv hRate
  let c := Real.sqrt (2 + Real.sqrt q.val)
  have hc : 0 < c := by positivity
  have hpow_period (x : ℝ) (m : ℕ) : x ^ TorusRC.positiveEvenPeriod m = x ^ 2 * (x ^ 2) ^ m := by
    rw [show TorusRC.positiveEvenPeriod m = 2 + 2 * m by simp [TorusRC.positiveEvenPeriod]; omega, pow_add, ← pow_mul]
  -- 1. First sector strict gap for `N ∈ 4ℕ`
  have hfirst : ∃ Nfirst : ℕ, ∀ N : ℕ, 4 ∣ N → Nfirst ≤ N → SixVertex.Lambda c N 1 < SixVertex.Lambda c N 0 := by
    let lam := Real.arcosh (Real.sqrt q.val / 2)
    obtain ⟨B, S₁, hS₁, hratio⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
    obtain ⟨S₀, _, hS₀, _, hpos, _⟩ := identity44 lam (arcosh_pos_of_gt4 q.val hq).1
    have hexp : Real.exp (-(↑(1 : ℕ) : ℝ) * (lam + 2 * S₁)) < 1 := by
      rw [Real.exp_lt_one_iff, tendsto_nhds_unique hS₁ hS₀]; norm_num; linarith
    obtain ⟨i₀, hi₀⟩ := eventually_atTop.1 (hratio.eventually (Iio_mem_nhds hexp))
    refine ⟨4 * (i₀ + B), fun N ⟨k, hk⟩ hlarge => ?_⟩
    have hNrepr : N = 4 * (k - B + B) := by omega
    have hlt : SixVertex.Lambda c N 1 / SixVertex.Lambda c N 0 < 1 := by simpa [c, hNrepr] using hi₀ (k - B) (by omega)
    exact (div_lt_one (SixVertex.Lambda_pos hc (by omega))).1 hlt
  obtain ⟨Nfirst, hfirstEvent⟩ := hfirst
  -- 2. Eigenvalue dominance `LambdaMax c N = Lambda c N 0` for large `N ∈ 4ℕ`
  obtain ⟨nTail2, hnTail2⟩ := eventually_atTop.1 (upperTailRateEventually q μ hμ ξinv hRate (r := 2) (by norm_num) (show 0 < ξinv / 4 by positivity))
  obtain ⟨NloopDom, hloopDom⟩ := lemma314_eventual_bound q hzeroSq (show 0 < ξinv / 32 by positivity)
  let Ndom := max 4 (max (4 * (max nTail2 NloopDom + 1)) Nfirst)
  have hdom : ∀ N : ℕ, 4 ∣ N → Ndom ≤ N → SixVertex.LambdaMax c N = SixVertex.Lambda c N 0 := fun N ⟨k, hk⟩ hlarge => by
    let n := 2 * k - 1
    have hperiod : TorusRC.positiveEvenPeriod n = N := by dsimp [n, TorusRC.positiveEvenPeriod]; dsimp [Ndom] at hlarge; omega
    let hNn := TorusRC.positiveEvenPeriod_even n; let hNpn := TorusRC.positiveEvenPeriod_pos n
    have hLoop := hloopDom (TorusRC.positiveEvenPeriod n) hNn hNpn (by rw [hperiod]; dsimp [Ndom] at hlarge; omega)
    have hTail : ∀ᶠ m : ℕ in atTop, TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4 := by
      filter_upwards [hnTail2 n (by dsimp [n, Ndom] at hlarge ⊢; omega)] with m hm; norm_num at hm; linarith
    have hbulk (r : ℕ) (hr2 : 2 ≤ r) (hr : r ≤ N / 2) :
        SixVertex.Lambda c N r ≤ Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax c N := by
      have hr' : r ≤ TorusRC.positiveEvenPeriod n / 2 := by simpa [hperiod] using hr
      let Lr := SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) r
      let Lmax := SixVertex.LambdaMax c (TorusRC.positiveEvenPeriod n)
      let D := Lmax ^ 2; let K := (2 ^ TorusRC.positiveEvenPeriod n : ℝ) * D
      let X (m : ℕ) := Lr ^ TorusRC.positiveEvenPeriod m
      let Y (m : ℕ) := TorusRC.torusRCProbability hNn (TorusRC.positiveEvenPeriod_even m) q
          (TorusRC.torusRCVerticalTail hNn (TorusRC.positiveEvenPeriod_even m) ⟨0, TorusRC.positiveEvenPeriod_pos m⟩ 2) /
        TorusLoops.phi_T_windingLoopDensityExpectation hNn (TorusRC.positiveEvenPeriod_even m) hNpn (TorusRC.positiveEvenPeriod_pos m) q
      let Z (m : ℕ) := (2 ^ TorusRC.positiveEvenPeriod n : ℝ) * Lmax ^ TorusRC.positiveEvenPeriod m
      have hLr : 0 < Lr := SixVertex.Lambda_pos hc hr'
      have hLmax : 0 < Lmax := SixVertex.LambdaMax_pos hc
      have hD : 0 < D := by positivity
      have hK : 0 < K := by positivity
      have hYp (m : ℕ) : 0 < Y m := by
        obtain ⟨hE, hP, _⟩ := upperTail_factorization_and_pos q hq hNn (TorusRC.positiveEvenPeriod_even m) hNpn (TorusRC.positiveEvenPeriod_pos m) (r := 2) (by omega)
        exact div_pos hP hE
      have hupper : ∀ᶠ m : ℕ in atTop, X m ≤ Y m * Z m := Eventually.of_forall fun m => by
        let M := TorusRC.positiveEvenPeriod m
        let hMm := TorusRC.positiveEvenPeriod_even m; let hMpm := TorusRC.positiveEvenPeriod_pos m
        obtain ⟨hE, _, hfact⟩ := upperTail_factorization_and_pos q hq hNn hMm hNpn hMpm hr'
        have hmono := div_le_div_of_nonneg_right (TorusRC.torusRCProbability_mono hNn hMm q
          (show TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ r ⊆ TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ 2 from
            fun _ hA => le_trans hr2 hA)) hE.le
        calc X m ≤ SixVertex.Z6Vr c (TorusRC.positiveEvenPeriod n) M r := SixVertex.Lambda_pow_le_Z6Vr_even hc hNpn hMpm hr' hMm
          _ ≤ SixVertex.Z6V c (TorusRC.positiveEvenPeriod n) M * _ := hfact
          _ ≤ SixVertex.Z6V c (TorusRC.positiveEvenPeriod n) M * Y m := mul_le_mul_of_nonneg_left hmono (SixVertex.Z6V_pos hc hNpn hMpm).le
          _ ≤ ((2 ^ TorusRC.positiveEvenPeriod n : ℝ) * Lmax ^ M) * Y m :=
              mul_le_mul_of_nonneg_right (SixVertex.Z6V_le_two_pow_mul_LambdaMax_pow hc hNpn hMpm) (hYp m).le
          _ = Y m * Z m := mul_comm _ _
      have hYrate : ∀ ε > 0, ∀ᶠ m : ℕ in atTop, (1 / (m : ℝ)) * Real.log (Y m) ≤ -ξinv + ε := fun ε hε => by
        filter_upwards [eventually_ge_atTop 1, hTail, hLoop] with m hm htail hmLoop
        let M := TorusRC.positiveEvenPeriod m
        let hMm := TorusRC.positiveEvenPeriod_even m; let hMpm := TorusRC.positiveEvenPeriod_pos m
        obtain ⟨hE, hp, _⟩ := upperTail_factorization_and_pos q hq hNn hMm hNpn hMpm (r := 2) (by omega)
        have hMcast : (M : ℝ) = 2 * ((m : ℝ) + 1) := by dsimp [M, TorusRC.positiveEvenPeriod]; push_cast; ring
        have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
        have hrLo : 2 ≤ (M : ℝ) / m := by rw [hMcast, le_div_iff₀ (by positivity)]; linarith
        have hrHi : (M : ℝ) / m ≤ 4 := by rw [hMcast, div_le_iff₀ (by positivity)]; linarith
        have htR : Real.log (TorusRC.torusRCProbability hNn hMm q (TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ 2)) / (M : ℝ) < -3 * ξinv / 4 := htail
        have hlU : -Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hNn hMm hNpn hMpm q) / (M : ℝ) ≤ ξinv / 32 := by
          simpa [neg_div] using neg_le_neg (abs_le.mp hmLoop).1
        have hMne : (M : ℝ) ≠ 0 := by exact_mod_cast hMpm.ne'
        rw [show (1 / (m : ℝ)) * Real.log (Y m) = ((M : ℝ) / m) *
            (Real.log (TorusRC.torusRCProbability hNn hMm q (TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ 2)) / M +
              (-Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hNn hMm hNpn hMpm q) / M)) by
          dsimp [Y, hMm, hMpm]; rw [Real.log_div hp.ne' hE.ne']; field_simp [hMne]; ring]
        nlinarith [mul_le_mul_of_nonpos_right hrLo (by linarith : Real.log _ / (M : ℝ) ≤ 0),
          mul_le_mul_of_nonneg_left hlU (show (0 : ℝ) ≤ (M : ℝ) / m by positivity)]
      have hZrate : ∀ ε > 0, ∀ᶠ m : ℕ in atTop, (1 / (m : ℝ)) * Real.log (Z m) ≤ Real.log D + ε := fun ε hε => by
        have hconv : Tendsto (fun m : ℕ => Real.log D + (1 / (m : ℝ)) * Real.log K) atTop (𝓝 (Real.log D)) := by
          simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log K))
        have hEq : (fun m : ℕ => (1 / (m : ℝ)) * Real.log (Z m)) =ᶠ[atTop] fun m : ℕ => Real.log D + (1 / (m : ℝ)) * Real.log K := by
          filter_upwards [eventually_gt_atTop 0] with m hm
          have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
          have hZ : Z m = K * D ^ m := by
            change (2 ^ TorusRC.positiveEvenPeriod n : ℝ) * Lmax ^ TorusRC.positiveEvenPeriod m =
              ((2 ^ TorusRC.positiveEvenPeriod n : ℝ) * Lmax ^ 2) * (Lmax ^ 2) ^ m
            rw [hpow_period Lmax m]; ring
          rw [hZ, Real.log_mul hK.ne' (pow_ne_zero _ hD.ne'), Real.log_pow]; field_simp; ring
        filter_upwards [(hconv.congr' hEq.symm).eventually (Iio_mem_nhds (show Real.log D < Real.log D + ε by linarith))] with m hm using hm.le
      have hgrowth := SixVertex.log_growth_le_of_eventually_factorized
        (C := Lr ^ 2) (Λ := Lr ^ 2) (Λmax := D) (a := -ξinv) (b := 0) (by positivity) (by positivity)
        X Y Z (Eventually.of_forall hYp) (Eventually.of_forall fun _ => by dsimp [Z]; positivity)
        (Eventually.of_forall fun m => by dsimp [X]; rw [hpow_period])
        hupper hYrate (by simpa using hZrate)
      rw [Real.log_pow, Real.log_pow] at hgrowth
      have hgap : Real.log (SixVertex.Lambda c N r) ≤ Real.log (SixVertex.LambdaMax c N) - ξinv / 2 := by
        dsimp [Lr, Lmax, D] at hgrowth; rw [hperiod] at hgrowth; nlinarith
      have hexp := Real.exp_le_exp.mpr hgap
      rwa [Real.exp_log (SixVertex.Lambda_pos hc hr), Real.exp_sub,
        Real.exp_log (SixVertex.LambdaMax_pos hc), div_eq_mul_inv, ← Real.exp_neg, mul_comm] at hexp
    exact SixVertex.LambdaMax_eq_Lambda0_of_dominance hc ⟨2 * k, by omega⟩
      (by dsimp [Ndom] at hlarge; omega) (by positivity) hbulk (hfirstEvent N ⟨k, hk⟩ (by dsimp [Ndom] at hlarge; omega))
  -- 3. Fixed-`r` upper bound and `r → ∞` squeeze
  have hfixed_r (r : ℕ) (hr2 : 2 ≤ r) :
      ∃ S : ℝ, Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
        ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) * (Real.arcosh (Real.sqrt q.val / 2) + 2 * S) := by
    obtain ⟨B, Sbethe, hSbethe, hratio⟩ := apply_17_at_critical_c q.val hq r (by omega)
    let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * Sbethe
    have hlogLim : Tendsto (fun i : ℕ => Real.log (SixVertex.Lambda c (4 * (i + B)) r / SixVertex.Lambda c (4 * (i + B)) 0))
        atTop (𝓝 (-(r : ℝ) * R)) := by
      convert (Real.continuousAt_log (Real.exp_pos (-(r : ℝ) * R)).ne').tendsto.comp hratio using 1 <;>
        ext i <;> simp [c, R, Real.log_exp]
    have hforδ (δ : ℝ) (hδ : 0 < δ) : -(r : ℝ) * R ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
      obtain ⟨nTail, hnTail⟩ := eventually_atTop.1
        (upperTailRateEventually q μ hμ ξinv hRate (r := r) (by omega) (show 0 < δ / 2 by linarith))
      obtain ⟨Ncut, hLoopCut⟩ := lemma314_eventual_bound q hzeroSq (show 0 < δ / 2 by linarith)
      refine le_of_tendsto hlogLim ?_
      filter_upwards [eventually_ge_atTop (max r (max 1 (max nTail (max Ncut Ndom))))] with i hi
      let N := 4 * (i + B); let n := 2 * (i + B) - 1
      have hperiod : TorusRC.positiveEvenPeriod n = N := by dsimp [n, N, TorusRC.positiveEvenPeriod]; omega
      let hNn := TorusRC.positiveEvenPeriod_even n; let hNpn := TorusRC.positiveEvenPeriod_pos n
      have hrN : r ≤ TorusRC.positiveEvenPeriod n / 2 := by rw [hperiod]; dsimp [N]; omega
      have hcenter : SixVertex.LambdaMax c (TorusRC.positiveEvenPeriod n) = SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) 0 := by
        rw [hperiod]; exact hdom N ⟨i + B, rfl⟩ (by dsimp [N]; omega)
      have hLoop := hLoopCut (TorusRC.positiveEvenPeriod n) hNn hNpn (by rw [hperiod]; dsimp [N]; omega)
      have hTail := hnTail n (by dsimp [n]; omega)
      let f (m : ℕ) := (1 / (TorusRC.positiveEvenPeriod m : ℝ)) *
        Real.log (SixVertex.Z6Vr c (TorusRC.positiveEvenPeriod n) (TorusRC.positiveEvenPeriod m) r /
          SixVertex.Z6V c (TorusRC.positiveEvenPeriod n) (TorusRC.positiveEvenPeriod m))
      have hMseq : Tendsto TorusRC.positiveEvenPeriod atTop atTop :=
        tendsto_atTop.2 fun K => by filter_upwards [eventually_ge_atTop K] with m hm; dsimp [TorusRC.positiveEvenPeriod]; omega
      have hlim_f : Tendsto f atTop (𝓝 (Real.log (SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) r /
          SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) 0))) := by
        simpa [Function.comp_def, f] using (SixVertex.tendsto_log_Z6V_ratio_eq_Lambda_ratio hc hNpn hrN hcenter).comp hMseq
      have hsec_le : Real.log (SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) r /
          SixVertex.Lambda c (TorusRC.positiveEvenPeriod n) 0) ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
        refine le_of_tendsto hlim_f ?_
        filter_upwards [hTail, hLoop] with m htail hloop
        let M := TorusRC.positiveEvenPeriod m
        let hMm := TorusRC.positiveEvenPeriod_even m; let hMpm := TorusRC.positiveEvenPeriod_pos m
        have hZV := SixVertex.Z6V_pos hc hNpn hMpm
        obtain ⟨hE, hP, hsec⟩ := upperTail_factorization_and_pos q hq hNn hMm hNpn hMpm hrN
        have hlog : Real.log (SixVertex.Z6Vr c (TorusRC.positiveEvenPeriod n) M r / SixVertex.Z6V c (TorusRC.positiveEvenPeriod n) M) ≤
            Real.log (TorusRC.torusRCProbability hNn hMm q (TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ r)) -
              Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hNn hMm hNpn hMpm q) := by
          rw [← Real.log_div hP.ne' hE.ne']
          exact Real.log_le_log (div_pos (SixVertex.Z6Vr_pos hc hNpn hMpm hrN) hZV) ((div_le_iff₀ hZV).2 (by simpa [mul_comm] using hsec))
        have hdiv : f m ≤ Real.log (TorusRC.torusRCProbability hNn hMm q (TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ r)) / M -
            Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hNn hMm hNpn hMpm q) / M := by
          dsimp [f]; rw [one_div_mul_eq_div, ← sub_div]; exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
        have hl : -(Real.log (TorusLoops.phi_T_windingLoopDensityExpectation hNn hMm hNpn hMpm q) / M) ≤ δ / 2 := by
          linarith [(abs_le.mp hloop).1]
        have ht : Real.log (TorusRC.torusRCProbability hNn hMm q (TorusRC.torusRCVerticalTail hNn hMm ⟨0, hMpm⟩ r)) / M <
            -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2 := htail
        linarith
      simpa [N, hperiod] using hsec_le
    refine ⟨Sbethe, hSbethe, ?_⟩
    by_contra hnot
    linarith [hforδ _ (show 0 < (-(r : ℝ) * R - (-((r - 1 : ℕ) : ℝ) * ξinv)) / 2 by dsimp [R] at hnot ⊢; linarith)]
  obtain ⟨_, S, hS, _⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  refine ⟨S, hS, ?_⟩
  by_contra hnot
  have h0R : Tendsto (fun n : ℕ => (1 / (n : ℝ)) * R) atTop (𝓝 0) := by
    simpa using tendsto_one_div_atTop_nhds_zero_nat.mul_const R
  obtain ⟨n, hnsmall, hnpos⟩ := ((h0R.eventually
    (Iio_mem_nhds (show (0 : ℝ) < (ξinv - R) / 2 by dsimp [R]; linarith))).and (eventually_gt_atTop 0)).exists
  obtain ⟨S', hS', hsec⟩ := hfixed_r (n + 1) (by omega)
  rw [tendsto_nhds_unique hS' hS, Nat.add_sub_cancel] at hsec
  push_cast at hsec
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hdiv : ξinv ≤ R + (1 / (n : ℝ)) * R := by
    have hmulR : ξinv * (n : ℝ) ≤ ((n : ℝ) + 1) * R := by
      have : (n : ℝ) * ξinv ≤ ((n : ℝ) + 1) * R := by simpa [R] using hsec
      linarith
    have := (le_div_iff₀ hnR).2 hmulR
    rwa [show ((n : ℝ) + 1) * R / n = R + (1 / (n : ℝ)) * R by field_simp] at this
  linarith

/-! ### 3. Item 3 and Theorem 1.2 Final Assembly -/

/-- Item 3 of Theorem 1.2, uniformly for every free critical box limit. -/
theorem rcItem3ForEveryFreeLimit_proved (q : ℝ) (hq : 4 < q)
    (μ : Measure (squareLattice.edgeSet → Bool))
    (hμ : IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ 0 μ)
    (lam : ℝ) (hlam : 0 < lam) (hcosh : Real.cosh lam = Real.sqrt q / 2) :
    ∃ S : ℝ,
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
      Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
        Real.log (μ.real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)})) atTop (𝓝 (lam + 2 * S)) := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩
  have hμFK : IsRCInfiniteVolumeLimit (FK.criticalParameters qI).toP (FK.criticalParameters qI).toQ 0 μ := by
    simpa [qI, FK.criticalParameters, FK.Parameters.toP, FK.Parameters.toQ, FK.edgeParameter] using hμ
  obtain ⟨aInf, _, _, hdiag⟩ := CorrLength.rotated_correlation_rate_exists_for_limit (FK.criticalParameters qI) μ hμFK
  let ξinv : ℝ := aInf / 2
  have hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv) := by simpa [ξinv] using hdiag
  obtain ⟨Slo, hSlo, hLower⟩ := xi_inverse_ge_critical_rate qI hq μ hμFK ξinv hRate
  obtain ⟨Shi, hShi, hUpper⟩ := rc_xi_inverse_le_critical_rate qI hq μ hμFK ξinv hRate
  have hxi : ξinv = Real.arcosh (Real.sqrt q / 2) + 2 * Slo :=
    le_antisymm (tendsto_nhds_unique hSlo hShi ▸ hUpper) hLower
  obtain ⟨hlam0, hcosh0⟩ := arcosh_pos_of_gt4 q hq
  have hlamEq : lam = Real.arcosh (Real.sqrt q / 2) :=
    Real.cosh_injOn (Set.mem_Ici.mpr hlam.le) (Set.mem_Ici.mpr hlam0.le) (hcosh.trans hcosh0.symm)
  have hsum : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / (k : ℝ) * Real.tanh ((k : ℝ) * lam))
      atTop (𝓝 Slo) := by
    change Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / (k : ℝ) *
      Real.tanh ((k : ℝ) * Real.arcosh (Real.sqrt q / 2))) atTop (𝓝 Slo) at hSlo
    simpa [hlamEq] using hSlo
  refine ⟨Slo, hsum, ?_⟩
  rw [show lam + 2 * Slo = ξinv by rw [hxi, hlamEq]]
  refine hRate.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hevent : CorrLength.connectionEvent (0, 0) (diagonalSite n) =
      {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)} :=
    Set.ext fun ω => CorrLength.connectionEvent_iff_rcInfiniteReachable (0, 0) (diagonalSite n) ω
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hevent]; field_simp [hnreal]

/-- The exact frozen Theorem 1.2 conclusion. -/
theorem rc_theorem_1_2_assembled (q : ℝ) (hq : 4 < q) :
    ∃ φ : Fin 2 → Measure (squareLattice.edgeSet → Bool),
      (∀ i, IsRCInfiniteVolumeLimit
        (rcCriticalParameter ⟨q, Set.mem_Ici.2 (by linarith)⟩)
        ⟨q, Set.mem_Ioi.2 (by linarith)⟩ i (φ i)) ∧
      φ 1 ≠ φ 0 ∧
      (φ 1).real {ω | ∃ x, {y | (rcInfiniteOpenGraph ω).Reachable x y}.Infinite} = 1 ∧
      (∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
        ∃ S : ℝ,
          Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
          Tendsto (fun n : ℕ => -(1 / (n : ℝ)) *
              Real.log ((φ 0).real {ω | (rcInfiniteOpenGraph ω).Reachable (0, 0) (diagonalSite n)})) atTop (𝓝 (lam + 2 * S))) := by
  let qI : Set.Ici (1 : ℝ) := ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩
  let qO : Set.Ioi (0 : ℝ) := ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩
  obtain ⟨μ₀, hμ₀⟩ := FK.exists_isRCInfiniteVolumeLimit (rcCriticalParameter qI) qO (by linarith) 0
  obtain ⟨μ₁, hμ₁⟩ := FK.exists_isRCInfiniteVolumeLimit (rcCriticalParameter qI) qO (by linarith) 1
  let φ : Fin 2 → Measure (squareLattice.edgeSet → Bool) := fun i => if i = 0 then μ₀ else μ₁
  have hφ : ∀ i, IsRCInfiniteVolumeLimit
      (rcCriticalParameter ⟨q, le_trans (by norm_num : (1 : ℝ) ≤ 4) hq.le⟩)
      ⟨q, lt_trans (by norm_num : (0 : ℝ) < 4) hq⟩ i (φ i) := fun i => by fin_cases i <;> simpa [φ, qI, qO] using (by assumption)
  obtain ⟨hLam, hcosh⟩ := arcosh_pos_of_gt4 q hq
  let lam := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨S, hS, hRate⟩ := rcItem3ForEveryFreeLimit_proved q hq (φ 0) (hφ 0) lam hLam hcosh
  obtain ⟨S₀, _, hS₀, _, hpos, _⟩ := identity44 lam hLam
  have hL : 0 < lam + 2 * S := tendsto_nhds_unique hS (by simpa [lam] using hS₀) ▸ hpos
  have hitems := Duality.rcm_items_one_two_of_pos_diagonal_rate q hq φ hφ (lam + 2 * S) hL hRate
  exact ⟨φ, hφ, hitems.1, hitems.2, rcItem3ForEveryFreeLimit_proved q hq (φ 0) (hφ 0)⟩

end PottsDiscontinuity.RCMProof
