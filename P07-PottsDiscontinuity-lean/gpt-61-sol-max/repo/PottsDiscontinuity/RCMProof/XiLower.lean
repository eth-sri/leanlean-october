module
public import Mathlib

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


open Torus

noncomputable def lowerLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)  :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

section

variable {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M)
include hq

private theorem lowerLoopFactor_le_one  : lowerLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hqpos : 0 < q.val := by linarith
  have hsqrt : 2 < Real.sqrt q.val := by
    have hs := Real.sq_sqrt (le_of_lt hqpos)
    have hn := Real.sqrt_nonneg q.val
    nlinarith
  have hbase : 0 ≤ 2 / Real.sqrt q.val ∧ 2 / Real.sqrt q.val ≤ 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      linarith
  have hnet : 0 ≤ (Torus.rcNetIndicator hN hM A : ℝ) := by positivity
  
  
  
  
  calc
    _ ≤ 1 * Real.rpow q.val (- Torus.rcNetIndicator hN hM A ) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_one hbase.1 hbase.2
                                    (by positivity)) (Real.rpow_nonneg (le_of_lt hqpos) _)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos
                                              q.property (neg_nonpos.mpr hnet)) (by norm_num)
    _ = 1 := by ring

private theorem lowerLoopFactor_ge_qsq_inv  (hU : rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1) :
    4 / q.val ^ 2 ≤ lowerLoopFactor hN hM q hNp hMp A := by
  
  
  
  
  
  have hnetcast : (Torus.rcNetIndicator hN hM A : ℝ) ≤ 1 := by exact_mod_cast  by
                                                                                 grind [Torus.rcNetIndicator] 
  
  
  have hsq : Real.rpow (2 / Real.sqrt q.val)  2  = 4 / q.val := by
    
    simp_all <;> grind
  unfold lowerLoopFactor
  rw [ TorusTopology.windingLoopCount_eq_two_of_U_eq_one
         hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A hU ]
  
  rw [(by
         simpa using hsq : Real.rpow (2 / Real.sqrt q.val) ((2 : ℕ) ) = 4 / q.val)]
  
  calc
    4 / q.val ^ 2 =  4 / q.val  * (1 / q.val) := by
      field_simp
    _ ≤  4 / q.val  * Real.rpow q.val
          (- Torus.rcNetIndicator hN hM A ) :=  mul_le_mul_of_nonneg_left (by
                                                                                 simpa [Real.rpow_neg_one] using (by
                                                                                                                    apply Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) q.property)
                                                                                                                    linarith : Real.rpow q.val (-1 ) ≤
      Real.rpow q.val (-(Torus.rcNetIndicator hN hM A )))) (by positivity) 
    _ =  4 / q.val  * Real.rpow q.val
          (- Torus.rcNetIndicator hN hM A ) := rfl

end

theorem exactOneProbability_le_qsq_mul_sector_ratio
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    TorusRC.torusRCProbability hN hM q
      {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1} ≤
      q.val ^ 2 * (SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1 /
        SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M) := by
  
  let E  :=
    {A | rcVerticalWinding hN hM ⟨0, hMp⟩ A = 1}
  let w  := Torus.torusRCWeight hN hM q
  let f  := lowerLoopFactor hN hM q hNp hMp
  let C  := Torus.torusNormalization q N M
  let Z0  := SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M
  let Z1  := SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M 1
  have hC : 0 < C := torusNormalization_pos q N M
  have hZ0 : 0 < Z0 := by
    
    apply SixVertex.Z6V_pos
    · positivity
    · exact hNp
    · exact hMp
  have hZ1 : 0 < Z1 := by
    
    apply SixVertex.Z6Vr_pos
    · positivity
    all_goals grind
  have htotalContract := hW12i q hq N M hN hM hNp hMp
  change  ∑ A : RCConfig N M, w A * f A  = C * Z0 at htotalContract
  
  
  have hpart : TorusRC.torusRCPartition hN hM q = ∑ A : RCConfig N M, w A := rfl
  have hden : C * Z0 ≤ TorusRC.torusRCPartition hN hM q := by
    rw [hpart, ← htotalContract]
    apply Finset.sum_le_sum
    intro A hA
    
    
    
    exact mul_le_of_le_one_right  (TorusRC.torusRCWeight_pos hN hM q A).le  (lowerLoopFactor_le_one hN hM q hq hNp hMp A)
  
  
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter  fun A  => A ∈ E , w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  
  rw [hprobEq]
  
  have hquot₂ :
       q.val ^ 2 * C * Z1  / TorusRC.torusRCPartition hN hM q ≤
         q.val ^ 2 * C * Z1  / (C * Z0) := by
    bound
  have hquot :
       q.val ^ 2 * C * Z1  / (C * Z0) = q.val ^ 2 * (Z1 / Z0) := by
    field_simp [hC.ne', hZ0.ne']
  simpa [E, Z0, Z1, hquot] using (div_le_div_of_nonneg_right (by
                                                                calc
                                                                  _ ≤  q.val ^ 2 / 4  *
                                                                       ∑ A ∈ Finset.univ.filter  fun A : RCConfig N M => A ∈ E , w A * f A  :=  by
                                                                                                                                                  rw [Finset.mul_sum]
                                                                                                                                                  apply Finset.sum_le_sum
                                                                                                                                                  intro A hA
                                                                                                                                                  
                                                                                                                                                  have hf := lowerLoopFactor_ge_qsq_inv hN hM q hq hNp hMp A (by
                                                                                                                                                                                                                simpa [E] using hA)
                                                                                                                                                  
                                                                                                                                                  dsimp [w, f]
                                                                                                                                                  have hcoef : 0 < q.val ^ 2 / 4 := by positivity
                                                                                                                                                  
                                                                                                                                                  calc
                                                                                                                                                    w A = w A * 1 := by ring
                                                                                                                                                    _ ≤ w A * ( q.val ^ 2 / 4  * lowerLoopFactor hN hM q hNp hMp A) :=
                                                                                                                                                      mul_le_mul_of_nonneg_left (by
                                                                                                                                                                                   calc
                                                                                                                                                                                     1 = (q.val ^ 2 / 4) * (4 / q.val ^ 2) := by
                                                                                                                                                                                       field_simp
                                                                                                                                                                                     _ ≤ (q.val ^ 2 / 4) * lowerLoopFactor hN hM q hNp hMp A :=
                                                                                                                                                                                       mul_le_mul_of_nonneg_left hf hcoef.le) ((TorusRC.torusRCWeight_pos hN hM q A).le)
                                                                                                                                                    _ =  q.val ^ 2 / 4  * (w A * lowerLoopFactor hN hM q hNp hMp A) := by ring 
                                                                  _ ≤  q.val ^ 2 / 4  * (4 * C * Z1) := mul_le_mul_of_nonneg_left (hW12ii q hq N M hN hM hNp hMp) (by positivity)
                                                                  _ = q.val ^ 2 * C * Z1 := by ring) (le_of_lt (TorusRC.torusRCPartition_pos hN hM q))).trans hquot₂

private theorem Z6Vr_le_Z6V_of_pos {c : ℝ} {N M : ℕ}
    (hc : 0 < c) (hN : 0 < N) (hM : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) : SixVertex.Z6Vr c N M r ≤ SixVertex.Z6V c N M := by
  have hEq : SixVertex.Z6Vr c N M r =
      SixVertex.Z6Vn c N M (N / 2 - r) := by
    rw [SixVertex.Z6Vr_eq_trace_block hN hM c hr,
      SixVertex.Z6Vn_eq_trace_block hN hM c]
  rw [hEq]
  exact SixVertex.Z6Vn_le_Z6V hc.le hM (by omega)

private theorem lowerExactOneRate_liminf_le_lambda_gap
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N : ℕ) (hN : Even N)
    (hNlarge : 8 ≤ N) (hNdiv : 8 ∣ N)
    (δ : ℝ) (hδ : 0 < δ) :
    Filter.liminf (TorusRC.torusRCUOneRateE hN q) Filter.atTop ≤
      ((Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 1) -
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          N 0) + δ : ℝ) : EReal) := by
  have hNpos : 0 < N := by  omega
  have hMseq : Filter.Tendsto TorusRC.positiveEvenPeriod Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with m hm
    simp [TorusRC.positiveEvenPeriod]
    omega
  
  
  let c  := Real.sqrt (2 + Real.sqrt q.val)
  let gap  := Real.log (SixVertex.Lambda c N 1) -
    Real.log (SixVertex.Lambda c N 0)
  have hc : 0 < c := by  positivity
  
  
  have hsectorEventually (η : ℝ) (hη : 0 < η) :
      ∀ᶠ M : ℕ in Filter.atTop,
         1 /  M   *
          Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) < gap + η := by
    exact eventually_lt_add_pos_of_limsup_le (by
                                                apply Filter.isBoundedUnder_of_eventually_le
                                                filter_upwards [Filter.eventually_gt_atTop 0] with M hM
                                                have hMpos  := hM
                                                have hZnum : 0 < SixVertex.Z6Vr c N M 1 := by
                                                  apply SixVertex.Z6Vr_pos hc hNpos hMpos
                                                  omega
                                                have hZden  := SixVertex.Z6V_pos hc hNpos hMpos
                                                have hratio  :=
                                                  div_pos hZnum hZden
                                                have hratioLe : SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M ≤ 1 := by
                                                  apply (div_le_one hZden).2
                                                  exact Z6Vr_le_Z6V_of_pos hc hNpos hMpos (by omega)
                                                have hlog  :=
                                                  Real.log_nonpos hratio.le hratioLe
                                                exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hlog) (by
                                                             
                                                             apply SixVertex.limsup_log_Z6V_ratio_le_center hc hNpos
                                                             omega) hη
  
  have hconst  :=
    (tendsto_natCast_atTop_atTop.comp hMseq).const_div_atTop (Real.log (q.val ^ 2))
  have hconstEventual : ∀ᶠ m : ℕ in Filter.atTop,
      Real.log (q.val ^ 2) /  TorusRC.positiveEvenPeriod m  < δ / 2 :=
    hconst.eventually (Iio_mem_nhds (by linarith))
  have hrateEventual : ∀ᶠ m : ℕ in Filter.atTop,
      TorusRC.torusRCUOneRateE hN q m ≤  gap + δ  := by
    filter_upwards [ hMseq.eventually (Filter.eventually_gt_atTop (N / 2)) ,  hMseq.eventually (hsectorEventually (δ / 2) (by linarith)) , hconstEventual] with m hmLarge hsector hconstm
    let M := TorusRC.positiveEvenPeriod m
    have hMpos : 0 < M := TorusRC.positiveEvenPeriod_pos m
    have hM : Even M := TorusRC.positiveEvenPeriod_even m
    
    
    
    
    
    have hq2 : 0 < q.val ^ 2 := by positivity
    have hlog := Real.log_le_log (exactOneProbability_pos_of_large_eight_width
                                    q hN hM hNdiv hNlarge hMpos  hmLarge ) (exactOneProbability_le_qsq_mul_sector_ratio
                                             hW12i hW12ii q hq N M hN hM hNpos hMpos)
    rw [Real.log_mul hq2.ne' (div_pos (by
                                         apply SixVertex.Z6Vr_pos hc hNpos hMpos
                                         omega) (SixVertex.Z6V_pos hc hNpos hMpos)).ne'] at hlog
    have hrealRate : Real.log (TorusRC.torusRCProbability hN hM q
        {A | rcVerticalWinding hN hM ⟨0, TorusRC.positiveEvenPeriod_pos m⟩ A = 1}) /
           M  ≤
         1 /  M   * Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) +
          Real.log (q.val ^ 2) /  M  := by
      
      calc
        _ ≤ (Real.log (q.val ^ 2) +
            Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M)) /  M  :=
          div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
        _ = _ := by  ring
    have hstrict :  1 /  M   *
          Real.log (SixVertex.Z6Vr c N M 1 / SixVertex.Z6V c N M) +
          Real.log (q.val ^ 2) /  M  < gap + δ := by linarith
    apply EReal.coe_le_coe_iff.mpr
    
    
    exact hrealRate.trans hstrict.le
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
  
  
  
  
  exact (tendsto_nhds_unique hRate hdiag).trans (tendsto_nhds_unique (by
                                                                        assumption) (TorusRC.tendsto_inverseCorrelationLength q))

/-- The exact-one-winding lower bound (3.24), using the provider contracts for
Corollary 3.13(i)–(ii) and equation (3.15) (`contract_cor313_i`, `contract_cor313_ii`,
`contract_eq315`). The quantity `R` is kept in its source form `λ + 2S`. -/
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
  let R  := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  let c  := Real.sqrt (2 + Real.sqrt q.val)
  let idx  := fun j => 2 * (j + 1) + B % 2
  let nSeq  := fun j => 2 * (idx j + B) - 1
  have hidxEven (j : ℕ) : Even (idx j + B) := by
    grind
  have hperiod (j : ℕ) : TorusRC.positiveEvenPeriod (nSeq j) =
      4 * (idx j + B) := by
    grind [TorusRC.positiveEvenPeriod]
  have hwidthLarge (j : ℕ) : 8 ≤ 4 * (idx j + B) := by
    dsimp [idx]
    omega
  
  have hidxAtTop : Filter.Tendsto idx Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    dsimp [idx]
    omega
  
  
  have hc : 0 < c := by  positivity
  let ratioSeq  := fun j =>
    SixVertex.Lambda c (4 * (idx j + B)) 1 /
      SixVertex.Lambda c (4 * (idx j + B)) 0
  
  have hlogRatio : Filter.Tendsto (fun j => Real.log (ratioSeq j))
      Filter.atTop (nhds (-R)) := by
    have h := (Real.continuousAt_log (Real.exp_pos (-R)).ne').tendsto.comp (by
                                                                              convert hroot.comp hidxAtTop using 1
                                                                              
                                                                              all_goals grind)
    convert h using 1
    · rfl
    · simp [Real.log_exp]
  let gapSeq  := fun j =>
    Real.log (SixVertex.Lambda c (4 * (idx j + B)) 1) -
      Real.log (SixVertex.Lambda c (4 * (idx j + B)) 0)
  have hgapEq (j : ℕ) : gapSeq j = Real.log (ratioSeq j) := by
    
    rw [Real.log_div (SixVertex.Lambda_pos hc (by
      have := hwidthLarge j
      omega)).ne' (SixVertex.Lambda_pos hc (by omega)).ne']
  have hgap : Filter.Tendsto gapSeq Filter.atTop (nhds (-R)) := by
    convert hlogRatio using 1
    funext j
    exact hgapEq j
  have hgapEventually (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ j : ℕ in Filter.atTop, gapSeq j < -R + ε := hgap.eventually (Iio_mem_nhds (by linarith))
  let outerRate8  := fun k =>
    Filter.liminf (TorusRC.torusRCUOneRateE
      (TorusRC.eightfoldPeriod_even k) q) Filter.atTop
  let kSeq  := fun j => (idx j + B) / 2 - 1
  have hkSeqAtTop : Filter.Tendsto kSeq Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [Filter.eventually_ge_atTop K] with j hj
    have hbound : 2 * (j + 1) ≤ idx j + B := by
      dsimp [idx]
      omega
    
    
    exact hj.trans (by dsimp [kSeq]; omega)
  have hwidth8 (j : ℕ) : TorusRC.eightfoldPeriod (kSeq j) =
      TorusRC.positiveEvenPeriod (nSeq j) := by
    dsimp [TorusRC.eightfoldPeriod, kSeq]
    rw [hperiod]
    obtain ⟨k, hk⟩ := hidxEven j
    
    have hlarge : 8 ≤ 4 * (k + k) := by
      grind
    omega
  have houterBound (ε : ℝ) (hε : 0 < ε) :
      Filter.liminf outerRate8 Filter.atTop ≤   -R + ε   := by
    
    
    
    exact Filter.liminf_le_of_frequently_le' (by
                                                rw [Filter.frequently_atTop']
                                                intro K
                                                obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 (by
                                                                                               filter_upwards [(hgapEventually (ε / 2) (by linarith))] with j hj
                                                                                               have hfixed := lowerExactOneRate_liminf_le_lambda_gap
                                                                                                 hW12i hW12ii q hq (TorusRC.eightfoldPeriod (kSeq j))
                                                                                                 (TorusRC.eightfoldPeriod_even (kSeq j)) (by
                                                                                                   dsimp [TorusRC.eightfoldPeriod]
                                                                                                   omega) (TorusRC.eightfoldPeriod_dvd (kSeq j)) (ε / 2) (by linarith)
                                                                                               have hvalue :
                                                                                                   Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
                                                                                                       (TorusRC.eightfoldPeriod (kSeq j)) 1) -
                                                                                                     Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
                                                                                                       (TorusRC.eightfoldPeriod (kSeq j)) 0) + ε / 2 =
                                                                                                   gapSeq j + ε / 2 := by
                                                                                                 rw [hwidth8 j, hperiod]
                                                                                               have hfixed' : outerRate8 (kSeq j) ≤
                                                                                                   ((gapSeq j + ε / 2 : ℝ) : EReal) := by
                                                                                                 dsimp [outerRate8]
                                                                                                 rw [hvalue] at hfixed
                                                                                                 exact hfixed
                                                                                               have hupper : gapSeq j + ε / 2 ≤ -R + ε := by linarith
                                                                                               
                                                                                               exact hfixed'.trans (EReal.coe_le_coe_iff.mpr hupper))
                                                have hKevent := hkSeqAtTop.eventually (Filter.eventually_gt_atTop K)
                                                obtain ⟨Jk, hJk⟩ := Filter.eventually_atTop.1 hKevent
                                                let j := max J Jk
                                                
                                                
                                                refine ⟨kSeq j, hJk j (Nat.le_max_right J Jk), hJ j (Nat.le_max_left J Jk)⟩)
  
  have hW21' := hW21 q hh319
  change   -TorusRC.inverseCorrelationLength q   ≤
    Filter.liminf outerRate8 Filter.atTop at hW21'
  have hW21'' :  - ξinv   ≤ Filter.liminf outerRate8 Filter.atTop := by
    simpa [ freeLimitRate_eq_torusRC_inverseCorrelationLength
              q μ hμ ξinv hRate ] using hW21'
  
  exact ⟨S, hS, by simpa [R] using  by
                                      by_contra hnot
                                      
                                      
                                      have hbetween  :=
                                        hW21''.trans (houterBound ((R - ξinv) / 2) (by linarith))
                                      have hreal  :=
                                        EReal.coe_le_coe_iff.mp hbetween
                                      linarith ⟩

end PottsDiscontinuity.RCMProof
