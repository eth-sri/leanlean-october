module

public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.RCMProof.ExactOneWitness
public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.TorusTopology.UnitWindingContract

/-!
# The lower bound on the inverse correlation length

The first lemma converts the exact-one-winding probability into a six-vertex
sector ratio. The fixed factor `q^2` absorbs the net indicator without a
separate no-net assertion.
-/

@[expose] public section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus

section
variable {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
include hq

lemma loopBase_le_one : 2 / Real.sqrt q.val ≤ 1 := by
  have h := Real.sq_sqrt (by linarith : 0 ≤ q.val)
  rw [div_le_one (by positivity)]
  nlinarith [Real.sqrt_nonneg q.val]

lemma torusLoopWeightFactor_le_one :
    torusLoopWeightFactor hN hM q hNp hMp A ≤ 1 := by
  have hq0 : 0 < q.val := by linarith
  exact (div_le_one (by positivity)).mpr ((pow_le_one₀ (by positivity) (loopBase_le_one q hq)).trans
    (one_le_pow₀ q.property))

lemma loopWeightFactor_ge {k : ℕ}
    (hk : TorusLoops.windingLoopCount hN hM ⟨0,hNp⟩ ⟨0,hMp⟩ A ≤ k) :
    (2 / Real.sqrt q.val)^k / q.val ≤ torusLoopWeightFactor hN hM q hNp hMp A := by
  have hq0 : 0 < q.val := by linarith
  have hpow := pow_le_pow_of_le_one (by positivity) (loopBase_le_one q hq) hk
  unfold torusLoopWeightFactor
  apply div_le_div₀ (by positivity) hpow (by positivity)
  simpa using pow_le_pow_right₀ q.property (show rcNetIndicator hN hM A ≤ 1 by grind [rcNetIndicator])

end

variable (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii) (hW21 : contract_eq315) {c : ℝ}
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici 1) (hh319 : TorusRC.h319 q)
    (hq : 4 < q.val) (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ) (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
      n) Filter.atTop (nhds ξinv))

include hq in
private theorem lowerLoopFactor_ge_qsq_inv (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (hU : rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1) :
    4 / q.val ^ 2 ≤ torusLoopWeightFactor hN hM q hNp hMp A := by
  have h := loopWeightFactor_ge hN hM q hq hNp hMp A
    (TorusTopology.windingLoopCount_eq_two_of_U_eq_one hN hM _ A hU).le
  rw [div_pow, Real.sq_sqrt (by linarith)] at h
  convert h using 1 <;> ring

include hW12i hW12ii hq in
theorem exactOneProbability_le_qsq_mul_sector_ratio (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} ≤
      q.val ^ 2 * (SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 /
        SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M) := by
  classical
  let E :=
    {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1}
  let w := Torus.torusRCWeight hN hM q
  let f := torusLoopWeightFactor hN hM q hNp hMp
  let C := Torus.torusNormalization q N M
  let Z0 := SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M
  let Z1 := SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1
  have hC : 0 < C := Torus.torusNormalization_pos q N M
  have hZ0 : 0 < Z0 := by
    apply SixVertex.Z6V_pos <;> positivity
  have hZ1 : 0 < Z1 := by
    apply SixVertex.Z6Vr_pos
    · positivity
    · exact hNp
    · exact hMp
    · grind
  have htotalContract := hW12i q hq N M hN hM hNp hMp
  change _ = C * Z0 at htotalContract
  have honeContract := hW12ii q hq N M hN hM hNp hMp
  have hpart : TorusRC.torusRCPartition hN hM q = ∑ A, w A := rfl
  have hden : C * Z0 ≤ TorusRC.torusRCPartition hN hM q := by
    rw [hpart, ← htotalContract]
    apply Finset.sum_le_sum
    intro A hA
    have hf := torusLoopWeightFactor_le_one hN hM q hq hNp hMp A
    have hw := (TorusRC.torusRCWeight_pos hN hM q A).le
    exact mul_le_of_le_one_right hw hf
  have hnum :
      (∑ A ∈ Finset.univ.filter (· ∈ E), w A) ≤
        (q.val ^ 2 / 4) *
          (∑ A ∈ Finset.univ.filter (· ∈ E), w A * f A) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro A hA
    have hf := lowerLoopFactor_ge_qsq_inv hN hM q hq hNp hMp A (by grind)
    have hcoef : 0 < q.val ^ 2 / 4 := by positivity
    have hcoef' : 1 ≤ (q.val ^ 2 / 4) * torusLoopWeightFactor hN hM q hNp hMp A := by
      calc
        1 = (q.val ^ 2 / 4) * (4 / q.val ^ 2) := by
          field_simp
        _ ≤ (q.val ^ 2 / 4) * torusLoopWeightFactor hN hM q hNp hMp A :=
          mul_le_mul_of_nonneg_left hf hcoef.le
    calc
      w A = w A * 1 := by ring
      _ ≤ w A * ((q.val ^ 2 / 4) * torusLoopWeightFactor hN hM q hNp hMp A) :=
        mul_le_mul_of_nonneg_left hcoef' (TorusRC.torusRCWeight_pos hN hM q A).le
      _ = (q.val ^ 2 / 4) * (w A * torusLoopWeightFactor hN hM q hNp hMp A) := by ring
  have hnum' :
      (∑ A ∈ Finset.univ.filter (· ∈ E), w A) ≤
        q.val ^ 2 * C * Z1 := by
    calc
      _ ≤ (q.val ^ 2 / 4) *
          (∑ A ∈ Finset.univ.filter (· ∈ E), w A * f A) := hnum
      _ ≤ (q.val ^ 2 / 4) * (4 * C * Z1) := mul_le_mul_of_nonneg_left honeContract (by positivity)
      _ = _ := by ring
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter (· ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  have hquot₁ :
      (∑ A ∈ Finset.univ.filter (· ∈ E), w A) /
          TorusRC.torusRCPartition hN hM q ≤
        (q.val ^ 2 * C * Z1) / TorusRC.torusRCPartition hN hM q := div_le_div_of_nonneg_right hnum' (le_of_lt (TorusRC.torusRCPartition_pos hN hM q))
  have hquot₂ :
      (q.val ^ 2 * C * Z1) / TorusRC.torusRCPartition hN hM q ≤
        (q.val ^ 2 * C * Z1) / (C * Z0) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · positivity
    · exact hden
  have hquot :
      (q.val ^ 2 * C * Z1) / (C * Z0) = q.val ^ 2 * (Z1 / Z0) := by
    grind
  grind

private theorem Z6Vr_le_Z6V_of_pos
    (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) : SixVertex.Z6Vr c N M r ≤ SixVertex.Z6V c N M := by
  have hEq : SixVertex.Z6Vr c N M r =
      SixVertex.Z6Vn c N M (N / 2 - r) := by
    rw [SixVertex.Z6Vr_eq_trace_block hN hM c hr,
      SixVertex.Z6Vn_eq_trace_block hN hM c]
  grind [SixVertex.Z6Vn_le_Z6V]

include hW12i hW12ii in
private theorem lowerExactOneRate_liminf_le_lambda_gap
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) {N : ℕ} (hN : Even N)
    (hNlarge : 8 ≤ N) (hNdiv : 8 ∣ N)
    {δ : ℝ} (hδ : 0 < δ) :
    Filter.liminf (TorusRC.torusRCUOneRateE hN q) Filter.atTop ≤
      (Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 1) -
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 0) + δ : ℝ) := by
  have hNpos : 0 < N := by omega
  have hMseq : Filter.Tendsto TorusRC.positiveEvenPeriod Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with m hm
    grind [TorusRC.positiveEvenPeriod]
  let c := Real.sqrt (2 + Real.sqrt q.val)
  let gap := Real.log (SixVertex.Lambda c N 1) -
    Real.log (SixVertex.Lambda c N 0)
  have hc : 0 < c := by positivity
  have hsectorLimsup : Filter.limsup (fun M : ℕ => (1 / M) *
      Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) Filter.atTop ≤ gap := by
    apply SixVertex.limsup_log_Z6V_ratio_le_center hc hNpos
    omega
  have hsectorBound : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun M : ℕ => (1 / M) *
        Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) := by
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM
    have hMpos := hM
    have hZnum : 0 < SixVertex.Z6Vr c N M 1 := by
      apply SixVertex.Z6Vr_pos hc hNpos hMpos
      omega
    have hZden := SixVertex.Z6V_pos hc hNpos hMpos
    have hlog :=
      Real.log_nonpos (div_pos hZnum hZden).le (by
        apply (div_le_one hZden).2
        exact Z6Vr_le_Z6V_of_pos hc hNpos hMpos (by omega))
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog
  have hsectorEventually (η : ℝ) (hη : 0 < η) :
      ∀ᶠ M : ℕ in Filter.atTop,
        (1 / M) *
          Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) < gap + η := by
    have hlt : Filter.limsup (fun M : ℕ => (1 / M) *
        Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) Filter.atTop <
        gap + η := lt_of_le_of_lt hsectorLimsup (by linarith)
    exact Filter.eventually_lt_of_limsup_lt hlt hsectorBound
  let logValueAt := Real.log (q.val ^ 2)
  have hconst :=
    (tendsto_natCast_atTop_atTop.comp hMseq).const_div_atTop (logValueAt)
  have hconstEventual : ∀ᶠ m : ℕ in Filter.atTop,
      logValueAt / (TorusRC.positiveEvenPeriod m) < δ / 2 :=
    hconst.eventually (Iio_mem_nhds (by linarith))
  have hrateEventual : ∀ᶠ m : ℕ in Filter.atTop,
      TorusRC.torusRCUOneRateE hN q m ≤ (gap + δ) := by
    filter_upwards [(hMseq.eventually (Filter.eventually_gt_atTop (N / 2))), (hMseq.eventually (hsectorEventually (δ / 2) (by linarith))), hconstEventual] with m hmLarge hsector hconstm
    let M := TorusRC.positiveEvenPeriod m
    have hMpos : 0 < M := TorusRC.positiveEvenPeriod_pos m
    have hM : Even M := TorusRC.positiveEvenPeriod_even m
    have hZnum : 0 < SixVertex.Z6Vr c N M 1 := by
      apply SixVertex.Z6Vr_pos hc hNpos hMpos
      omega
    have hratio :=
      div_pos hZnum (SixVertex.Z6V_pos hc hNpos hMpos)
    have hq2 : 0 < q.val ^ 2 := by positivity
    have hlog := Real.log_le_log (exactOneProbability_pos_of_large_eight_width q hN hM hNdiv hNlarge hMpos (by assumption)) (exactOneProbability_le_qsq_mul_sector_ratio hW12i hW12ii q hq N M hN hM hNpos hMpos)
    rw [Real.log_mul hq2.ne' hratio.ne'] at hlog
    let logValue' := Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)
    have hrealRate : Real.log (TorusRC.torusRCProbability hN hM q
        {A | rcVerticalWinding hN hM ⟨0, TorusRC.positiveEvenPeriod_pos m⟩ A = 1}) /
          M ≤
        (1 / M) * logValue' +
          logValueAt / M := by
      calc
        _ ≤ (logValueAt +
            logValue') / M :=
          div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
        _ = _ := by ring
    have hstrict : (1 / M) *
          logValue' +
          logValueAt / M < gap + δ := by linarith
    apply EReal.coe_le_coe_iff.mpr
    exact hrealRate.trans hstrict.le
  exact Filter.liminf_le_of_frequently_le' hrateEventual.frequently

include hμ hRate in
private theorem freeLimitRate_eq_torusRC_inverseCorrelationLength :
    ξinv = TorusRC.inverseCorrelationLength q := by
  obtain ⟨aInf, _, hrot, hdiag⟩ :=
    CorrLength.rotated_correlation_rate_exists_for_limit μ hμ
  have hxi := tendsto_nhds_unique hRate hdiag
  have hrot' : Filter.Tendsto (fun n : ℕ =>
      -Real.log ((CorrLength.rotatedDiagonalConnectionProbability
        (TorusRC.torusRCBridgeParameters q) n : NNReal) : ℝ) /
        ((2 * n : ℕ) : ℝ)) Filter.atTop (nhds (aInf / 2)) := by
    assumption
  exact hxi.trans (tendsto_nhds_unique hrot' (TorusRC.tendsto_inverseCorrelationLength q))

include hW12i hW12ii hW21 hh319 hq hμ hRate in
/-- The exact-one-winding lower bound (3.24), using the provider contracts for
Corollary 3.13(i)–(ii) and equation (3.15) (`contract_cor313_i`, `contract_cor313_ii`,
`contract_eq315`). The quantity `R` is kept in its source form `λ + 2S`. -/
theorem xi_inverse_ge_critical_rate :
    ∃ S,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨B, S, hS, hroot⟩ := apply_17_at_critical_c (q := q.val) hq (r := 1) (by omega)
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let c := Real.sqrt (2 + Real.sqrt q.val)
  let idx := fun j => 2 * (j + 1) + B % 2
  let nSeq := fun j => 2 * (idx j + B) - 1
  have hperiod (j : ℕ) : TorusRC.positiveEvenPeriod (nSeq j) =
      4 * (idx j + B) := by
    have hpos : 1 ≤ 2 * (idx j + B) := by grind
    simp [nSeq, TorusRC.positiveEvenPeriod, Nat.sub_add_cancel hpos]
    omega
  have hidxAtTop : Filter.Tendsto idx Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    grind
  have hrootSeq : Filter.Tendsto
      (fun j : ℕ => SixVertex.Lambda c (4 * (idx j + B)) 1 /
        SixVertex.Lambda c (4 * (idx j + B)) 0)
      Filter.atTop (nhds (Real.exp (-R))) := by
    convert hroot.comp hidxAtTop using 1
    · rfl
    · simp [R]
  have hc : 0 < c := by positivity
  let ratioSeq := fun j =>
    SixVertex.Lambda c (4 * (idx j + B)) 1 /
      SixVertex.Lambda c (4 * (idx j + B)) 0
  have hlogRatio : Filter.Tendsto (fun j => Real.log (ratioSeq j))
      Filter.atTop (nhds (-R)) := by
    have h := (Real.continuousAt_log (Real.exp_pos (-R)).ne').tendsto.comp hrootSeq
    convert h using 1
    · rfl
    · simp
  let gapSeq := fun j =>
    Real.log (SixVertex.Lambda c (4 * (idx j + B)) 1) -
      Real.log (SixVertex.Lambda c (4 * (idx j + B)) 0)
  have hgapEq (j : ℕ) : gapSeq j = Real.log (ratioSeq j) := by
    rw [Real.log_div (SixVertex.Lambda_pos hc (by
      grind)).ne' (SixVertex.Lambda_pos hc (by omega)).ne']
  have hgap : Filter.Tendsto gapSeq Filter.atTop (nhds (-R)) := by
    grind
  have hgapEventually (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in Filter.atTop, gapSeq j < -R + ε := hgap.eventually (Iio_mem_nhds (by linarith))
  let outerRate8 := fun k =>
    Filter.liminf (TorusRC.torusRCUOneRateE
      (TorusRC.eightfoldPeriod_even k) q) Filter.atTop
  let kSeq := fun j => (idx j + B) / 2 - 1
  have hkSeqAtTop : Filter.Tendsto kSeq Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    grind
  have hwidth8 (j : ℕ) : TorusRC.eightfoldPeriod (kSeq j) =
      TorusRC.positiveEvenPeriod (nSeq j) := by
    dsimp [TorusRC.eightfoldPeriod, kSeq]
    grind
  have houterBound (ε : ℝ) (hε : 0 < ε) :
      Filter.liminf outerRate8 Filter.atTop ≤ (-R + ε : ℝ) := by
    have hnear := hgapEventually (ε / 2) (by linarith)
    have hinnerEventually : ∀ᶠ j : ℕ in Filter.atTop,
        outerRate8 (kSeq j) ≤ (-R + ε : ℝ) := by
      filter_upwards [hnear] with j hj
      have hfixed := lowerExactOneRate_liminf_le_lambda_gap
        hW12i hW12ii q hq (N := (TorusRC.eightfoldPeriod (kSeq j)))
        (TorusRC.eightfoldPeriod_even (kSeq j)) (by
          simp [TorusRC.eightfoldPeriod]) (TorusRC.eightfoldPeriod_dvd (kSeq j)) (δ := (ε / 2)) (by linarith)
      have hvalue :
          Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
              (TorusRC.eightfoldPeriod (kSeq j)) 1) -
            Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
              (TorusRC.eightfoldPeriod (kSeq j)) 0) + ε / 2 =
          gapSeq j + ε / 2 := by
        grind
      have hfixed' : outerRate8 (kSeq j) ≤
          ((gapSeq j + ε / 2 : ℝ) : EReal) := by
        grind
      have hupper : gapSeq j + ε / 2 ≤ -R + ε := by linarith
      have hupperE := EReal.coe_le_coe_iff.mpr hupper
      exact hfixed'.trans hupperE
    exact Filter.liminf_le_of_frequently_le' (by
      rw [Filter.frequently_atTop']
      intro K
      obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hinnerEventually
      have hKevent := hkSeqAtTop.eventually (Filter.eventually_gt_atTop K)
      obtain ⟨Jk, hJk⟩ := Filter.eventually_atTop.1 hKevent
      let j := max J Jk
      have hJle : J ≤ j := by exact Nat.le_max_left _ _
      have hJkle : Jk ≤ j := by exact Nat.le_max_right _ _
      grind)
  have hxiCanonical := freeLimitRate_eq_torusRC_inverseCorrelationLength
    q μ hμ ξinv hRate
  have hW21' := hW21 q hh319
  change ((-TorusRC.inverseCorrelationLength q : ℝ) : EReal) ≤
    Filter.liminf outerRate8 Filter.atTop at hW21'
  have hW21'' : (-ξinv : EReal) ≤ Filter.liminf outerRate8 Filter.atTop := by
    simp_all
  have hxi : ξinv ≥ R := by
    by_contra hnot
    have hε : 0 < (R - ξinv) / 2 := by linarith
    have houter := houterBound ((R - ξinv) / 2) hε
    have hbetween :=
      hW21''.trans houter
    have hreal :=
      EReal.coe_le_coe_iff.mp hbetween
    linarith
  grind

end PottsDiscontinuity.RCMProof
