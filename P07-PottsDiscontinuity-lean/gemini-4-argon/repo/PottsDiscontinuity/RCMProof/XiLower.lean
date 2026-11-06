module

public import PottsDiscontinuity.RCMProof.BetheAssembly
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.RCMProof.ExactOneWitness
public import PottsDiscontinuity.SixVertex.Sec33Ratios
public import PottsDiscontinuity.TorusTopology.UnitWindingContract

@[expose] public section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open Torus

noncomputable def lowerLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) : ℝ :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

theorem lowerLoopFactor_le_one {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : lowerLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hqpos : 0 < q.val := by linarith
  have hsqrt : 2 < Real.sqrt q.val := by
    nlinarith [Real.sq_sqrt hqpos.le, Real.sqrt_nonneg q.val]
  have hfactor₁ := Real.rpow_le_one (x := 2 / Real.sqrt q.val) (by positivity)
    (by rw [div_le_one (by positivity)]; linarith)
    (Nat.cast_nonneg (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A))
  have hfactor₂ := Real.rpow_le_one_of_one_le_of_nonpos
    q.property (neg_nonpos.mpr (Nat.cast_nonneg (Torus.rcNetIndicator hN hM A)))
  unfold lowerLoopFactor
  calc _ ≤ 1 * Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) :=
      mul_le_mul_of_nonneg_right hfactor₁ (Real.rpow_nonneg hqpos.le _)
    _ = Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) := one_mul _
    _ ≤ 1 := hfactor₂

private theorem lowerLoopFactor_ge_qsq_inv {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (hU : rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1) :
    4 / q.val ^ 2 ≤ lowerLoopFactor hN hM q hNp hMp A := by
  have hqpos : 0 < q.val := by linarith
  have hcount := TorusTopology.windingLoopCount_eq_two_of_U_eq_one hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A hU
  have hnet : (Torus.rcNetIndicator hN hM A : ℝ) ≤ 1 := by
    exact_mod_cast (show Torus.rcNetIndicator hN hM A ≤ 1 by unfold Torus.rcNetIndicator; split_ifs <;> omega)
  have hpow : 1 / q.val ≤ Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) := by
    simpa [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le q.property
      (by linarith : (-1 : ℝ) ≤ -(Torus.rcNetIndicator hN hM A : ℝ))
  have hsq : Real.rpow (2 / Real.sqrt q.val) ((2 : ℕ) : ℝ) = 4 / q.val := by
    calc Real.rpow (2 / Real.sqrt q.val) ((2 : ℕ) : ℝ)
      _ = (2 / Real.sqrt q.val) ^ (2 : ℕ) := Real.rpow_natCast _ _
      _ = 4 / q.val := by rw [div_pow, Real.sq_sqrt hqpos.le]; norm_num
  unfold lowerLoopFactor
  rw [hcount, hsq]
  calc 4 / q.val ^ 2 = (4 / q.val) * (1 / q.val) := by ring
    _ ≤ (4 / q.val) * Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)

theorem exactOneProbability_le_qsq_mul_sector_ratio
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} ≤
      q.val ^ 2 * (SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 /
        SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M) := by
  classical
  let E : Set (RCConfig N M) := {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1}
  let w : RCConfig N M → ℝ := Torus.torusRCWeight hN hM q
  let f : RCConfig N M → ℝ := lowerLoopFactor hN hM q hNp hMp
  let C : ℝ := Torus.torusNormalization q N M
  let Z0 : ℝ := SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M
  let Z1 : ℝ := SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1
  have hC : 0 < C := Torus.torusNormalization_pos q N M
  have hZ0 : 0 < Z0 := SixVertex.Z6V_pos (by positivity) hNp hMp
  have htotalContract : (∑ A : RCConfig N M, w A * f A) = C * Z0 :=
    hW12i q hq N M hN hM hNp hMp
  have honeContract : (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A) ≤
      4 * C * Z1 := hW12ii q hq N M hN hM hNp hMp
  have hden : C * Z0 ≤ TorusRC.torusRCPartition hN hM q := by
    rw [show TorusRC.torusRCPartition hN hM q = ∑ A : RCConfig N M, w A from rfl, ← htotalContract]
    exact Finset.sum_le_sum fun A _ =>
      mul_le_of_le_one_right (TorusRC.torusRCWeight_pos hN hM q A).le
        (lowerLoopFactor_le_one hN hM q hq hNp hMp A)
  have hnum : (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) ≤
      q.val ^ 2 * C * Z1 := by
    calc (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A)
      _ ≤ (q.val ^ 2 / 4) *
          (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A * f A) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun A hA => ?_
        have hf := lowerLoopFactor_ge_qsq_inv hN hM q hq hNp hMp A (by simpa [E] using hA)
        have hw : 0 ≤ w A := (TorusRC.torusRCWeight_pos hN hM q A).le
        have hqpos : 0 < q.val ^ 2 := by positivity
        have h1 : 1 ≤ (q.val ^ 2 / 4) * f A := by
          calc (1 : ℝ) = (q.val ^ 2 / 4) * (4 / q.val ^ 2) := by field_simp
            _ ≤ (q.val ^ 2 / 4) * f A := mul_le_mul_of_nonneg_left hf (by positivity)
        nlinarith
      _ ≤ (q.val ^ 2 / 4) * (4 * C * Z1) :=
        mul_le_mul_of_nonneg_left honeContract (by positivity)
      _ = q.val ^ 2 * C * Z1 := by ring
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  change TorusRC.torusRCProbability hN hM q E ≤ q.val ^ 2 * (Z1 / Z0)
  rw [hprobEq]
  have hZ1 : 0 < Z1 := SixVertex.Z6Vr_pos (by positivity) hNp hMp (by rcases hN with ⟨k, hk⟩; omega)
  calc (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q
    _ ≤ (q.val ^ 2 * C * Z1) / TorusRC.torusRCPartition hN hM q :=
      div_le_div_of_nonneg_right hnum (TorusRC.torusRCPartition_pos hN hM q).le
    _ ≤ (q.val ^ 2 * C * Z1) / (C * Z0) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hC hZ0) hden
    _ = q.val ^ 2 * (Z1 / Z0) := by field_simp [hC.ne', hZ0.ne']

private theorem lowerExactOneRate_liminf_le_lambda_gap
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N : ℕ) (hN : Even N)
    (hNlarge : 8 ≤ N) (hNdiv : 8 ∣ N)
    (δ : ℝ) (hδ : 0 < δ) :
    Filter.liminf (TorusRC.torusRCUOneRateE hN q) Filter.atTop ≤
      ((Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 1) -
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0) + δ : ℝ) : EReal) := by
  have hNpos : 0 < N := by omega
  have hMseq : Filter.Tendsto TorusRC.positiveEvenPeriod Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun K => by
      filter_upwards [Filter.eventually_ge_atTop K] with m hm
      simp [TorusRC.positiveEvenPeriod]; omega
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let gap : ℝ := Real.log (SixVertex.Lambda c N 1) - Real.log (SixVertex.Lambda c N 0)
  have hc : 0 < c := by positivity
  have hsectorLimsup : Filter.limsup (fun M : ℕ => (1 / (M : ℝ)) *
      Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) Filter.atTop ≤ gap :=
    SixVertex.limsup_log_Z6V_ratio_le_center hc hNpos (by omega)
  have hsectorBound : Filter.IsBoundedUnder (· ≤ ·) Filter.atTop
      (fun M : ℕ => (1 / (M : ℝ)) * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) := by
    apply Filter.isBoundedUnder_of_eventually_le
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM
    have hZnum : 0 < SixVertex.Z6Vr c N M 1 := SixVertex.Z6Vr_pos hc hNpos hM (by omega)
    have hZden : 0 < SixVertex.Z6V c N M := SixVertex.Z6V_pos hc hNpos hM
    have hle : SixVertex.Z6Vr c N M 1 ≤ SixVertex.Z6V c N M := by
      rw [SixVertex.Z6Vr_eq_trace_block hNpos hM c (by omega),
        ← SixVertex.Z6Vn_eq_trace_block hNpos hM c]
      exact SixVertex.Z6Vn_le_Z6V hc.le hM (by omega)
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
      (Real.log_nonpos (div_pos hZnum hZden).le ((div_le_one hZden).2 hle))
  have hsectorEventualOnM := hMseq.eventually
    (Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hsectorLimsup (by linarith : gap < gap + δ / 2))
      hsectorBound)
  have hconstEventual : ∀ᶠ m : ℕ in Filter.atTop,
      Real.log (q.val ^ 2) / (TorusRC.positiveEvenPeriod m : ℝ) < δ / 2 :=
    ((tendsto_natCast_atTop_atTop.comp hMseq).const_div_atTop
      (Real.log (q.val ^ 2))).eventually (Iio_mem_nhds (by linarith))
  have hrateEventual : ∀ᶠ m : ℕ in Filter.atTop,
      TorusRC.torusRCUOneRateE hN q m ≤ (gap + δ : EReal) := by
    filter_upwards [hMseq.eventually (Filter.eventually_gt_atTop (N / 2)),
      hsectorEventualOnM, hconstEventual] with m hmLarge hsector hconstm
    let M := TorusRC.positiveEvenPeriod m
    have hMpos : 0 < M := TorusRC.positiveEvenPeriod_pos m
    have hM : Even M := TorusRC.positiveEvenPeriod_even m
    have hprob := exactOneProbability_le_qsq_mul_sector_ratio hW12i hW12ii q hq N M hN hM hNpos hMpos
    have hprobPos := exactOneProbability_pos_of_large_eight_width q hN hM hNdiv hNlarge hMpos hmLarge
    have hratio : 0 < SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M :=
      div_pos (SixVertex.Z6Vr_pos hc hNpos hMpos (by omega)) (SixVertex.Z6V_pos hc hNpos hMpos)
    have hlog := Real.log_le_log hprobPos hprob
    rw [Real.log_mul (by positivity) hratio.ne'] at hlog
    apply EReal.coe_le_coe_iff.mpr
    change Real.log (TorusRC.torusRCProbability hN hM q
        {A | rcVerticalWinding hN hM ⟨0, hMpos⟩ A = 1}) / (M : ℝ) ≤ gap + δ
    have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
    rw [add_div] at hdiv
    have hsector' : 1 / (M : ℝ) * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) <
        gap + δ / 2 := hsector
    linarith [show Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) / (M : ℝ) =
      1 / (M : ℝ) * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) by ring]
  exact Filter.liminf_le_of_frequently_le' hrateEventual.frequently

private theorem freeLimitRate_eq_torusRC_inverseCorrelationLength
    (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ξinv = TorusRC.inverseCorrelationLength q := by
  obtain ⟨aInf, _, hrot, hdiag⟩ :=
    CorrLength.rotated_correlation_rate_exists_for_limit (FK.criticalParameters q) μ hμ
  have hrot' : Filter.Tendsto (fun n : ℕ =>
      -Real.log ((CorrLength.rotatedDiagonalConnectionProbability
        (TorusRC.torusRCBridgeParameters q) n : NNReal) : ℝ) /
        ((2 * n : ℕ) : ℝ)) Filter.atTop (nhds (aInf / 2)) := by
    simpa [TorusRC.torusRCBridgeParameters, TorusRC.torusRCFKParameters,
      FK.criticalParameters] using hrot
  exact (tendsto_nhds_unique hRate hdiag).trans
    (tendsto_nhds_unique hrot' (TorusRC.tendsto_inverseCorrelationLength q))

theorem xi_inverse_ge_critical_rate
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW21 : contract_eq315)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Filter.Tendsto (fun n : ℕ =>
      -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) /
        (n : ℝ)) Filter.atTop (nhds ξinv)) :
    ∃ S : ℝ,
      Filter.Tendsto (altTanhPartial (Real.arcosh (Real.sqrt q.val / 2)))
        Filter.atTop (nhds S) ∧
      ξinv ≥ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨B, S, hS, hroot⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  let R : ℝ := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let idx : ℕ → ℕ := fun j => 2 * (j + 1) + B % 2
  have hidxEven (j : ℕ) : Even (idx j + B) := ⟨j + 1 + B / 2 + B % 2, by dsimp [idx]; omega⟩
  have hwidthLarge (j : ℕ) : 8 ≤ 4 * (idx j + B) := by dsimp [idx]; omega
  have hidxAtTop : Filter.Tendsto idx Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun K => by
      filter_upwards [Filter.eventually_ge_atTop K] with j hj; dsimp [idx]; omega
  have hrootSeq : Filter.Tendsto
      (fun j : ℕ => SixVertex.Lambda c (4 * (idx j + B)) 1 /
        SixVertex.Lambda c (4 * (idx j + B)) 0)
      Filter.atTop (nhds (Real.exp (-R))) := by
    simpa [Function.comp_def, R] using hroot.comp hidxAtTop
  have hc : 0 < c := by positivity
  let gapSeq : ℕ → ℝ := fun j =>
    Real.log (SixVertex.Lambda c (4 * (idx j + B)) 1) -
      Real.log (SixVertex.Lambda c (4 * (idx j + B)) 0)
  have hgap : Filter.Tendsto gapSeq Filter.atTop (nhds (-R)) := by
    have h := (Real.continuousAt_log (Real.exp_pos (-R)).ne').tendsto.comp hrootSeq
    rw [Real.log_exp] at h
    refine h.congr fun j => ?_
    dsimp [Function.comp_def, gapSeq]
    exact Real.log_div
      (SixVertex.Lambda_pos (N := 4 * (idx j + B)) (r := 1) hc (by have := hwidthLarge j; omega)).ne'
      (SixVertex.Lambda_pos (N := 4 * (idx j + B)) (r := 0) hc (by omega)).ne'
  let outerRate8 : ℕ → EReal := fun k =>
    Filter.liminf (TorusRC.torusRCUOneRateE
      (TorusRC.eightfoldPeriod_even k) q) Filter.atTop
  let kSeq : ℕ → ℕ := fun j => (idx j + B) / 2 - 1
  have hkSeqAtTop : Filter.Tendsto kSeq Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop.2 fun K => by
      filter_upwards [Filter.eventually_ge_atTop K] with j hj
      dsimp [kSeq, idx]; omega
  have hwidth8 (j : ℕ) : TorusRC.eightfoldPeriod (kSeq j) = 4 * (idx j + B) := by
    dsimp [TorusRC.eightfoldPeriod, kSeq]
    obtain ⟨k, hk⟩ := hidxEven j
    have := hwidthLarge j
    omega
  have houterBound (ε : ℝ) (hε : 0 < ε) :
      Filter.liminf outerRate8 Filter.atTop ≤ ((-R + ε : ℝ) : EReal) := by
    have hinnerEventually : ∀ᶠ j : ℕ in Filter.atTop,
        outerRate8 (kSeq j) ≤ ((-R + ε : ℝ) : EReal) := by
      filter_upwards [hgap.eventually (Iio_mem_nhds (by linarith : -R < -R + ε / 2))] with j hj
      have hfixed := lowerExactOneRate_liminf_le_lambda_gap
        hW12i hW12ii q hq (TorusRC.eightfoldPeriod (kSeq j))
        (TorusRC.eightfoldPeriod_even (kSeq j))
        (by dsimp [TorusRC.eightfoldPeriod]; omega)
        (TorusRC.eightfoldPeriod_dvd (kSeq j)) (ε / 2) (by linarith)
      dsimp [outerRate8]
      refine hfixed.trans (EReal.coe_le_coe_iff.mpr ?_)
      rw [hwidth8 j]
      dsimp [gapSeq, c] at hj
      linarith
    refine Filter.liminf_le_of_frequently_le' (Filter.frequently_atTop'.2 fun K => ?_)
    obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hinnerEventually
    obtain ⟨Jk, hJk⟩ := Filter.eventually_atTop.1
      (hkSeqAtTop.eventually (Filter.eventually_gt_atTop K))
    exact ⟨kSeq (max J Jk), hJk _ (le_max_right _ _), hJ _ (le_max_left _ _)⟩
  have hW21' : (-(ξinv : ℝ) : EReal) ≤ Filter.liminf outerRate8 Filter.atTop := by
    rw [freeLimitRate_eq_torusRC_inverseCorrelationLength q μ hμ ξinv hRate]
    exact hW21 q hh319
  refine ⟨S, hS, ?_⟩
  by_contra hnot
  have hbetween := hW21'.trans (houterBound ((R - ξinv) / 2) (by dsimp [R] at *; linarith))
  have hreal : -ξinv ≤ -R + (R - ξinv) / 2 := EReal.coe_le_coe_iff.mp hbetween
  dsimp [R] at *; linarith

end PottsDiscontinuity.RCMProof
