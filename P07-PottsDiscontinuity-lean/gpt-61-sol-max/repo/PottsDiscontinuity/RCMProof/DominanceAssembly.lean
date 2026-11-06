module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.RCMProof.RouteB
public import PottsDiscontinuity.RCMProof.Lemma314Adapters
public import PottsDiscontinuity.SixVertex.Sec33Dominance
public import PottsDiscontinuity.SixVertex.Sec33RealAnalysis

@[expose] public section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof


open SixVertex Torus

noncomputable def upperLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M)  :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

section

variable {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))


private theorem upperLoopFactor_eq_densityWeight 
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    upperLoopFactor hN hM q hNp hMp A =
      TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
                                                                 unfold upperLoopFactor TorusLoops.windingLoopDensityWeight TorusLoops.windingLoopDensityBase
                                                                 aesop

private theorem upperLoopFactor_le_one  (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : upperLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hsqrt : 2 < Real.sqrt q.val := by
    have hs := Real.sq_sqrt (by linarith )
    nlinarith [Real.sqrt_nonneg q.val]
  have hbase : TorusLoops.windingLoopDensityUpperBase q = 1 := by
    unfold TorusLoops.windingLoopDensityUpperBase TorusLoops.windingLoopDensityBase
    rw [max_eq_left]
    rw [div_le_one (by positivity)]
    linarith
  rw [upperLoopFactor_eq_densityWeight hN hM q hNp hMp A]
  calc
    TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A ≤
        TorusLoops.windingLoopDensityUpperBase q ^ (N + M) :=
      TorusLoops.windingLoopDensityWeight_le_global hN hM hNp hMp q A
    _ = 1 := by rw [hbase]; simp

end

noncomputable def upperTailRateE
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ)  :=
  TorusRC.positiveEvenVerticalTailRateE q r n m

private theorem upperTailRateE_nonpos
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ) : upperTailRateE q r n m ≤ 0 := by
  apply EReal.coe_le_coe_iff.mpr
  
  exact div_nonpos_of_nonpos_of_nonneg
    (TorusRC.torusRCVerticalTail_log_nonpos _ _ q _ r) (Nat.cast_nonneg _)

private theorem upperTailRateE_inner_limsup_nonpos
    (q : Set.Ici (1 : ℝ)) (r n : ℕ) :
    Filter.limsup (fun m => upperTailRateE q r n m) atTop ≤ 0 := by
  
  simpa using  Filter.limsup_le_limsup
                 (f := atTop) (u :=  upperTailRateE q r n )
                 (v := fun _  => 0) (Filter.Eventually.of_forall (upperTailRateE_nonpos q r n)) 

section

variable (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ)) (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ) (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
include hW21 hμ hRate

private theorem upperTailRateEventually
    
    (hξ : 0 < ξinv) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4 := by
  let u  := fun n => Filter.limsup
     (upperTailRateE q 2 n)  atTop
  have huPoint (n : ℕ)  := upperTailRateE_inner_limsup_nonpos q 2 n
  
  
  
  have htarget :  -ξinv  < -3 * ξinv / 4 := by nlinarith
  
  have hn  :=
    Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt (by
                                                         simpa [u, upperTailRateE] using  hW21 q μ hμ ξinv hRate 2 (by norm_num) ) (EReal.coe_lt_coe_iff.mpr htarget)) (isBoundedUnder_of_eventually_le (Eventually.of_forall huPoint))
  filter_upwards [hn] with n hn
  
  have hm := Filter.eventually_lt_of_limsup_lt hn (isBoundedUnder_of_eventually_le (Eventually.of_forall (upperTailRateE_nonpos q 2 n)))
  filter_upwards [hm] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

private theorem upperTailRateEventually_general
    
    {r : ℕ} (hr1 : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  let u  := fun n => Filter.limsup
    (fun m => upperTailRateE q r n m) atTop
  have huPoint (n : ℕ)  := upperTailRateE_inner_limsup_nonpos q r n
  
  
  have hbase : - (r - 1 : ℕ)  * ξinv <
      - (r - 1 : ℕ)  * ξinv + δ := by linarith
  
  have houterStrict  :=
    lt_of_le_of_lt (by
                      simpa [u, upperTailRateE] using  hW21 q μ hμ ξinv hRate r hr1 ) (EReal.coe_lt_coe_iff.mpr hbase)
  have hn  :=
    Filter.eventually_lt_of_limsup_lt houterStrict (isBoundedUnder_of_eventually_le (Eventually.of_forall huPoint))
  filter_upwards [hn] with n hn
  
  have hm := Filter.eventually_lt_of_limsup_lt hn (isBoundedUnder_of_eventually_le (Eventually.of_forall (upperTailRateE_nonpos q r n)))
  filter_upwards [hm] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

end

noncomputable def upperTailProbability
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hMp : 0 < M) (r : ℕ)  :=
  TorusRC.torusRCProbability hN hM q
    (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r)

noncomputable def upperLoopExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M)  :=
  ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
    upperLoopFactor hN hM q hNp hMp A

private theorem upperLoopExpectation_eq_densityExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) :
    upperLoopExpectation hN hM q hNp hMp =
      TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
                                                                          simp_all [upperLoopExpectation, TorusLoops.phi_T_windingLoopDensityExpectation, upperLoopFactor_eq_densityWeight]

section

variable {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N)
include hN q hNp

private theorem upperLoopExpectation_rate_eq
     (m : ℕ) :
    TorusLoops.windingLoopDensityLogRate hN hNp q m =
      Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ) := by
  simp [TorusLoops.windingLoopDensityLogRate, TorusRC.positiveEvenPeriod,
    upperLoopExpectation_eq_densityExpectation]

private theorem upperLoopExpectation_abs_log_rate_eventually
    
    (lim : ℝ)
    (hlim : Filter.limsup
      (fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m)) atTop ≤ lim)
    (hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop
       fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m) )
    {bound : ℝ} (hbound : lim < bound) :
    ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ bound := by
  
  filter_upwards [ Filter.eventually_lt_of_limsup_lt
                     (lt_of_le_of_lt hlim hbound) hbounded ] with m hm
  simpa [upperLoopExpectation_rate_eq] using hm.le

end

private theorem upperTailFactorization
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
        (upperTailProbability hN hM q hMp r / upperLoopExpectation hN hM q hNp hMp) := by
  classical
  let c  := Real.sqrt (2 + Real.sqrt q.val)
  let E  :=
    TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r
  
  let f  := upperLoopFactor hN hM q hNp hMp
  let w  := Torus.torusRCWeight hN hM q
  let C  := Torus.torusNormalization q N M
  have hscale : 0 < C := torusNormalization_pos q N M
  have hZ : 0 < SixVertex.Z6V c N M := by
    apply SixVertex.Z6V_pos
    ·  positivity
    · exact hNp
    · exact hMp
  
  have htotalContract := hW12i q hq N M hN hM hNp hMp
  change  ∑ A : RCConfig N M, w A * f A  =
    C * SixVertex.Z6V c N M at htotalContract
  have hsectorContract := hW12iii q hq r N M hr1 hN hM hNp hMp
  change C * SixVertex.Z6Vr c N M r ≤
    ∑ A ∈ Finset.univ.filter  fun A  => A ∈ ({A | r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A}) , w A * f A
    at hsectorContract
  
  have hpartitionPos  :=
    TorusRC.torusRCPartition_pos hN hM q
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter  fun A  => A ∈ E , w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  
  have hsectorTail  := hsectorContract.trans (by
                                                calc
                                                  _ ≤ ∑ A ∈ Finset.univ.filter  fun A  => A ∈ E , w A * f A := by
                                                    apply Finset.sum_le_sum_of_subset_of_nonneg (by
                                                                                                   intro A hA
                                                                                                   simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
                                                                                                   exact hA)
                                                    intro A hA hnot
                                                    
                                                    
                                                    exact mul_nonneg  (TorusRC.torusRCWeight_pos hN hM q A).le  (by
                                                                           dsimp [f, upperLoopFactor]
                                                                           positivity)
                                                  _ ≤ ∑ A ∈ Finset.univ.filter  fun A  => A ∈ E , w A := sum_le_sum fun A hA =>
                                                                                                                         mul_le_of_le_one_right (LT.lt.le (TorusRC.torusRCWeight_pos hN hM q A)) (upperLoopFactor_le_one hN hM q hq hNp hMp A)
                                                  _ = TorusRC.torusRCPartition hN hM q *
                                                      TorusRC.torusRCProbability hN hM q E := by
                                                    rw [hprobEq]
                                                    field_simp)
  have hsumNormalized : upperLoopExpectation hN hM q hNp hMp =
      (∑ A : RCConfig N M, w A * f A) / TorusRC.torusRCPartition hN hM q := by
    
    calc
       ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
          upperLoopFactor hN hM q hNp hMp A  =
        ∑ A : RCConfig N M,  w A * f A  /
          TorusRC.torusRCPartition hN hM q := by
        grind [TorusRC.torusRCMass]
      _ = (∑ A : RCConfig N M, w A * f A) /
          TorusRC.torusRCPartition hN hM q := by rw [Finset.sum_div]
  
  have htotalPos : 0 < upperLoopExpectation hN hM q hNp hMp := by
    simp_all
  
  simpa [c, E, upperTailProbability, upperLoopExpectation] using  by
                                                                    have hP : TorusRC.torusRCPartition hN hM q =
                                                                        C * SixVertex.Z6V c N M / upperLoopExpectation hN hM q hNp hMp := by
                                                                      grind
                                                                    
                                                                    exact (mul_le_mul_iff_of_pos_left hscale).mp (by
                                                                                                                    calc
                                                                                                                      C * SixVertex.Z6Vr c N M r ≤
                                                                                                                           C * SixVertex.Z6V c N M /
                                                                                                                            upperLoopExpectation hN hM q hNp hMp  *
                                                                                                                              TorusRC.torusRCProbability hN hM q E := by
                                                                                                                        simpa [hP] using hsectorTail
                                                                                                                      _ = C * (SixVertex.Z6V c N M *
                                                                                                                          (TorusRC.torusRCProbability hN hM q E /
                                                                                                                            upperLoopExpectation hN hM q hNp hMp)) := by
                                                                                                                        field_simp [ne_of_gt htotalPos]) 

private theorem upperLoopExpectation_pos
    (hW12i : contract_cor313_i) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (N M : ℕ) (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) :
    0 < upperLoopExpectation hN hM q hNp hMp := by
  let f  := upperLoopFactor hN hM q hNp hMp
  let w  := Torus.torusRCWeight hN hM q
  
  
  
  
  have hcontract := hW12i q hq N M hN hM hNp hMp
  change  ∑ A : RCConfig N M, w A * f A  =
     Torus.torusNormalization q N M  * SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M at hcontract
  have hsum : upperLoopExpectation hN hM q hNp hMp =
      (∑ A : RCConfig N M, w A * f A) / TorusRC.torusRCPartition hN hM q := by
    
    calc
       ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
          upperLoopFactor hN hM q hNp hMp A  =
        ∑ A : RCConfig N M,  w A * f A  /
          TorusRC.torusRCPartition hN hM q := by
        grind [TorusRC.torusRCMass]
      _ = (∑ A : RCConfig N M, w A * f A) /
          TorusRC.torusRCPartition hN hM q := by rw [Finset.sum_div]
  rw [hsum, hcontract]
  exact div_pos (mul_pos (torusNormalization_pos q N M) (SixVertex.Z6V_pos (by positivity) hNp hMp)) (TorusRC.torusRCPartition_pos hN hM q)

private theorem upperTailProbability_pos
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    0 < upperTailProbability hN hM q hMp r := by
  
  have hZ : 0 < SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M := SixVertex.Z6V_pos (by positivity) hNp hMp
  have hZr : 0 < SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r := SixVertex.Z6Vr_pos (by positivity) hNp hMp hr
  
  
  by_contra hnot
  
  
  have hprodNonpos  :=
    mul_nonpos_of_nonneg_of_nonpos hZ.le (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp).le)
  linarith [ upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp
               (r := r) hr hr1 ]

private theorem pow_positiveEvenPeriod (x : ℝ) (m : ℕ) :
    x ^ TorusRC.positiveEvenPeriod m = x ^ 2 * (x ^ 2) ^ m := by
  rw [show TorusRC.positiveEvenPeriod m = 2 + 2 * m by
    simp [TorusRC.positiveEvenPeriod]; omega]
  rw [pow_add, ← pow_mul]

section

variable (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
include hW12i hW12iii hq

private theorem upperDominanceGap_fixedIndex
    
    (ξinv : ℝ) (hξ : 0 < ξinv) (n Nloop : ℕ)
    (hNloop : Nloop ≤ TorusRC.positiveEvenPeriod n)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4)
    (hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ ξinv / 32)
    {r : ℕ} (hr : r ≤ TorusRC.positiveEvenPeriod n / 2) (hr2 : 2 ≤ r) :
    Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) r) ≤
      Real.log (SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val))
        (TorusRC.positiveEvenPeriod n)) - ξinv / 2 := by
  
  let N := TorusRC.positiveEvenPeriod n
  let c  := Real.sqrt (2 + Real.sqrt q.val)
  let Lr  := SixVertex.Lambda c N r
  let Lmax  := SixVertex.LambdaMax c N
  let D  := Lmax ^ 2
  let K  :=  2 ^ N  * D
  let X  := fun m => Lr ^ TorusRC.positiveEvenPeriod m
  let Y  := fun m =>
    upperTailProbability (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos m) 2 /
    upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)
  let Z  := fun m =>
     2 ^ N  * Lmax ^ TorusRC.positiveEvenPeriod m
  have hN : Even N := TorusRC.positiveEvenPeriod_even n
  have hNp : 0 < N := TorusRC.positiveEvenPeriod_pos n
  have hNhalf : 2 ≤ N / 2 := by omega
  have hc : 0 < c := by  positivity
  have hLr : 0 < Lr := SixVertex.Lambda_pos (by positivity) hr
  have hLmax : 0 < Lmax := by
    
    exact SixVertex.LambdaMax_pos (by positivity)
  have hD : 0 < D := pow_pos hLmax 2
  have hK : 0 < K := by  positivity
  have hEpos (m : ℕ)  :=
    upperLoopExpectation_pos hW12i q hq N (TorusRC.positiveEvenPeriod m) hN
      (TorusRC.positiveEvenPeriod_even m) hNp (TorusRC.positiveEvenPeriod_pos m)
  
  have hZpos : ∀ᶠ m : ℕ in atTop, 0 < Z m := by
    aesop
  
  
  
  have hZfactor (m : ℕ) : Z m = K * D ^ m := by
    grind [TorusRC.positiveEvenPeriod, pow_positiveEvenPeriod]
  have hZrate : ∀ ε , 0 < ε → ∀ᶠ m : ℕ in atTop,
       1 /  m   * Real.log (Z m) ≤ Real.log D + ε := by
    intro ε hε
    have hconst : Tendsto (fun m : ℕ =>  1 /  m   * Real.log K)
        atTop (𝓝 0) := by
      
      simpa using  tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log K) 
    have hconv : Tendsto (fun m : ℕ => Real.log D +
         1 /  m   * Real.log K) atTop (𝓝 (Real.log D)) := by
      simpa using  tendsto_const_nhds.add hconst 
    have hEq : (fun m  =>  1 /  m   * Real.log (Z m)) =ᶠ[atTop]
         fun m  => Real.log D +  1 /  m   * Real.log K  := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      
      have hpow : D ^ m ≠ 0 := pow_ne_zero _ hD.ne'
      rw [hZfactor m, Real.log_mul hK.ne' hpow, Real.log_pow]
      field_simp
      ring
    have hconv' := hconv.congr' hEq.symm
    filter_upwards [hconv'.eventually (Iio_mem_nhds (by linarith :
      Real.log D < Real.log D + ε))] with m hm
    exact hm.le
  have hgrowth := SixVertex.log_growth_le_of_eventually_factorized
    (C := Lr ^ 2) (Λ := Lr ^ 2) (Λmax := D) (a := -ξinv) (b := 0)
    (by positivity) (by positivity) X Y Z (by
                                             filter_upwards with m
                                             have htailpos := upperTailProbability_pos hW12i hW12iii q hq N
                                               (TorusRC.positiveEvenPeriod m) hN (TorusRC.positiveEvenPeriod_even m)
                                               hNp (TorusRC.positiveEvenPeriod_pos m) (r := 2) (by omega) (by norm_num)
                                             aesop) hZpos (by
                                                         filter_upwards with m
                                                         change  Lr ^ 2  * (Lr ^ 2) ^ m ≤ Lr ^ TorusRC.positiveEvenPeriod m
                                                         rw [pow_positiveEvenPeriod]) (by
                                                                filter_upwards with m
                                                                let M := TorusRC.positiveEvenPeriod m
                                                                have hM : Even M := by grind
                                                                have hMp : 0 < M := TorusRC.positiveEvenPeriod_pos m
                                                                
                                                                
                                                                have htailMono : upperTailProbability hN hM q hMp r ≤
                                                                    upperTailProbability hN hM q hMp 2 := TorusRC.torusRCProbability_mono hN hM q fun ⦃A⦄ => le_trans hr2
                                                                
                                                                
                                                                
                                                                
                                                                calc
                                                                  X m ≤ SixVertex.Z6Vr
                                                                      (Real.sqrt (2 + Real.sqrt q.val)) N M r :=  SixVertex.Lambda_pow_le_Z6Vr_even hc hNp hMp hr hM 
                                                                  _ ≤ SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N
                                                                      M * (upperTailProbability hN hM q hMp r /
                                                                        upperLoopExpectation hN hM q hNp hMp) :=  upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp
                                                                                                                    (r := r) hr (by omega) 
                                                                  _ ≤ SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
                                                                      (upperTailProbability hN hM q hMp 2 /
                                                                        upperLoopExpectation hN hM q hNp hMp) :=
                                                                    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htailMono (hEpos m).le)
                                                                      (SixVertex.Z6V_pos hc hNp hMp).le
                                                                  _ ≤   2 ^ N  * SixVertex.LambdaMax
                                                                        (Real.sqrt (2 + Real.sqrt q.val)) N ^ M  *
                                                                      (upperTailProbability hN hM q hMp 2 /
                                                                        upperLoopExpectation hN hM q hNp hMp) :=
                                                                    mul_le_mul_of_nonneg_right (SixVertex.Z6V_le_two_pow_mul_LambdaMax_pow hc hNp hMp) (div_pos (upperTailProbability_pos hW12i hW12iii q hq N M hN hM hNp hMp
                                                                                                                                                                                       (r := 2) (by omega) (by norm_num)) (hEpos m)).le
                                                                  _ = Y m * Z m := by
                                                                    
                                                                    ring) (by
                                                                       intro ε hε
                                                                       rcases Filter.eventually_atTop.1 hTail with ⟨m₀, hm₀⟩
                                                                       filter_upwards [Filter.eventually_ge_atTop (max m₀ 1), hLoop] with m hm hmLoop
                                                                       
                                                                       have hmpos : 0 < m := by
                                                                                               omega
                                                                       have htail := hm₀ m (le_trans (Nat.le_max_left _ _) hm)
                                                                       let M := TorusRC.positiveEvenPeriod m
                                                                       let p := upperTailProbability hN (TorusRC.positiveEvenPeriod_even m) q
                                                                         (TorusRC.positiveEvenPeriod_pos m) 2
                                                                       let e := upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m) q hNp
                                                                         (TorusRC.positiveEvenPeriod_pos m)
                                                                       have hp : 0 < p := by
                                                                         grind [upperTailProbability_pos]
                                                                       
                                                                       have htailRate : Real.log p /  M  < -3 * ξinv / 4 := by
                                                                         assumption
                                                                       have hMcast :  M  = 2 * ((m : ℝ) + 1) := by
                                                                         dsimp [M, TorusRC.positiveEvenPeriod]
                                                                         push_cast
                                                                         ring
                                                                       
                                                                       have hmone : 1 ≤ (m : ℝ) := by simp_all
                                                                       have hratioLo : 2 ≤  M  / (m : ℝ) := by
                                                                         
                                                                         field_simp
                                                                         nlinarith [hmone]
                                                                       have hratioHi :  M  / (m : ℝ) ≤ 4 := by
                                                                         
                                                                         field_simp
                                                                         nlinarith
                                                                       
                                                                       have htailScaled :   M  /  m   * (Real.log p /  M ) <
                                                                           -3 * ξinv / 2 := by
                                                                         nlinarith
                                                                       
                                                                       have hloopBound' : |Real.log e / (M )| ≤ ξinv / 32 := hmLoop
                                                                       have hloopUpper : -Real.log e /  M  ≤ ξinv / 32 := by
                                                                         
                                                                         grind
                                                                       have hloopScaled :   M  /  m   * (-Real.log e /  M ) ≤
                                                                           ξinv / 8 := by
                                                                         nlinarith
                                                                       have hYlog : Real.log (Y m) = Real.log p - Real.log e := by
                                                                         
                                                                         rw [Real.log_div hp.ne' (hEpos m).ne']
                                                                       have hscaledEq :  1 /  m   * Real.log (Y m) =
                                                                             M  /  m   * (Real.log p /  M  - Real.log e /  M ) := by
                                                                         grind
                                                                       grind)
    (by simpa using hZrate)
  have hlogpow := hgrowth
  rw [Real.log_pow, Real.log_pow] at hlogpow
  dsimp [Lr, Lmax, c, N] at hlogpow ⊢
  nlinarith

private theorem sectorLogRate_le_of_eventual_tail
     (n : ℕ)
    (ξinv δ : ℝ) {r : ℕ} (hr : r ≤
      TorusRC.positiveEvenPeriod n / 2) (hr1 : 1 ≤ r)
    (hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (TorusRC.positiveEvenPeriod n) 0)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2)
    (hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos n)
        (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ δ / 2) :
    Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (TorusRC.positiveEvenPeriod n) 0) ≤
      -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  
  let N := TorusRC.positiveEvenPeriod n
  let c  := Real.sqrt (2 + Real.sqrt q.val)
  let p (m : ℕ) := upperTailProbability (TorusRC.positiveEvenPeriod_even n)
    (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos m) r
  let e (m : ℕ) := upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
    (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos n)
      (TorusRC.positiveEvenPeriod_pos m)
  let f (m : ℕ) :=  1 /  TorusRC.positiveEvenPeriod m   *
    Real.log (SixVertex.Z6Vr c N (TorusRC.positiveEvenPeriod m) r /
      SixVertex.Z6V c N (TorusRC.positiveEvenPeriod m))
  have hNpos : 0 < N := TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < c := by  positivity
  have hZV (m : ℕ)  :=
    SixVertex.Z6V_pos hc hNpos (TorusRC.positiveEvenPeriod_pos m)
  have hP (m : ℕ) : 0 < p m := by
    grind [TorusRC.positiveEvenPeriod, upperTailProbability_pos]
  have hE (m : ℕ) : 0 < e m := by
    grind [TorusRC.positiveEvenPeriod, upperLoopExpectation_pos]
  
  
  have hlimit : Tendsto f atTop
      (𝓝 (Real.log (SixVertex.Lambda c N r / SixVertex.Lambda c N 0))) := by
    simpa [Function.comp_def, f, N, c] using (SixVertex.tendsto_log_Z6V_ratio_eq_Lambda_ratio
                                                (c := c) (N := N) hc hNpos hr hcenter).comp (by
                                                                 apply Filter.tendsto_atTop.2
                                                                 intro K
                                                                 filter_upwards [Filter.eventually_ge_atTop K] with m hm
                                                                 dsimp [TorusRC.positiveEvenPeriod]
                                                                 omega)
  have hrateBound : ∀ᶠ m : ℕ in atTop,
      f m < - (r - 1 : ℕ)  * ξinv + δ := by
    filter_upwards [hTail, hLoop] with m htail hloop
    let M := TorusRC.positiveEvenPeriod m
    have hM : Even M := by grind
    have hMp : 0 < M := TorusRC.positiveEvenPeriod_pos m
    
    have htailRate : Real.log (p m) /  M  <
        - (r - 1 : ℕ)  * ξinv + δ / 2 := by
      assumption
    
    have hsector := upperTailFactorization hW12i hW12iii q hq N M
      (TorusRC.positiveEvenPeriod_even n) hM hNpos hMp hr  hr1 
    have hratio : SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M ≤
        p m / e m := by
      apply (div_le_iff₀ (hZV m)).2
      all_goals grind
    have hlog  := Real.log_le_log
          (div_pos (SixVertex.Z6Vr_pos hc hNpos hMp hr) (hZV m)) hratio
    have hlogDiv  :=
      Real.log_div (hP m).ne' (hE m).ne'
    
    have hlog' : Real.log (SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M) ≤
        Real.log (p m) - Real.log (e m) := by
      rw [← hlogDiv]
      exact hlog
    have hrateAux : f m ≤ Real.log (p m) /  M  -
        Real.log (e m) /  M  := by
      
      calc
        _ ≤  1 /  M   * (Real.log (p m) - Real.log (e m)) :=
          mul_le_mul_of_nonneg_left hlog' (by positivity)
        _ = Real.log (p m) /  M  - Real.log (e m) /  M  := by ring
    all_goals grind
  by_contra hnot
  
  
  have hfalse : ∀ᶠ m : ℕ in atTop, False := by
    filter_upwards [ hlimit.eventually (Ioi_mem_nhds (lt_of_not_ge hnot)) , hrateBound] with m hlargeM hrateM
    grind
  rcases hfalse.exists with ⟨m, hm⟩
  exact hm

end

/-- The fixed-sector estimate used to take `r → ∞` in the inverse correlation
length upper bound. -/
theorem rc_upper_bound_fixed_r
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (hDominance : ∃ Ndom : ℕ, ∀ N : ℕ, 4 ∣ N → Ndom ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    (r : ℕ) (hr2 : 2 ≤ r) :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) *
        (Real.arcosh (Real.sqrt q.val / 2) + 2 * S) := by
  
  
  
  obtain ⟨Sfree, hSfree, hxi, hno, _hboundary⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  obtain ⟨Ndom, hdom⟩ := hDominance
  obtain ⟨B, Sbethe, hSbethe, hratio⟩ :=
    apply_17_at_critical_c q.val hq r (by omega)
  
  let R  :=  Real.arcosh (Real.sqrt q.val / 2)  + 2 * Sbethe
  
  
  
  
  
  
  
  
  
  have hforδ : ∀ δ , 0 < δ →
      - r  * R ≤ - (r - 1 : ℕ)  * ξinv + δ := by
    intro δ hδ
    
    obtain ⟨nTail', hnTail'⟩ := Filter.eventually_atTop.1 (upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate
                                                             (r := r) (by omega) (δ := δ / 2) (by linarith))
    
    obtain ⟨NloopCut', hloopData'⟩ :=
      lemma314_limsup_and_one_arm_cutoff q (lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno) (δ / 4) (by linarith)
    let Nloop' := NloopCut'.val
    let i₁ := max r (max 1 (max nTail' (max Nloop' Ndom)))
    have hboundEvent' : ∀ᶠ i : ℕ in atTop,
        Real.log (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (4 * (i + B)) r /
          SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) 0) ≤
          - (r - 1 : ℕ)  * ξinv + δ := by
      filter_upwards [Filter.eventually_ge_atTop i₁] with i hi
      let N := 4 * (i + B)
      let n := 2 * (i + B) - 1
      
      
      
      
      
      have hperiod : TorusRC.positiveEvenPeriod n = N := by
        dsimp [n, N, TorusRC.positiveEvenPeriod]
        
        omega
      
      
      have hnTailIndex : nTail' ≤ n := by  omega
      
      have hcenter  :=
        hdom N  ⟨i + B, rfl⟩  (by dsimp [N]; omega)
      
      have hNloopPeriod : Nloop' ≤ TorusRC.positiveEvenPeriod n := by
        rw [hperiod]
        exact  by dsimp [N]; omega 
      
      have hfixed := sectorLogRate_le_of_eventual_tail hW12i hW12iii q hq n
        ξinv δ (r := r) (by   omega) (by omega)
        (by simpa [hperiod] using hcenter) (by
                                              have hevent := hnTail' n hnTailIndex
                                              filter_upwards [hevent] with m hm
                                              simpa [hperiod] using hm) (by
                                                    obtain ⟨hlim, harm⟩ := hloopData' (TorusRC.positiveEvenPeriod n)
                                                      (TorusRC.positiveEvenPeriod_even n) hNloopPeriod
                                                    have hbounded := windingLoopDensityLogRate_abs_bounded q
                                                      (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm
                                                    exact upperLoopExpectation_abs_log_rate_eventually
                                                      (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
                                                      (δ / 4) hlim hbounded (by linarith))
      simpa [N, hperiod] using hfixed
    have hlimitBound' : - r  * R ≤ - (r - 1 : ℕ)  * ξinv + δ := by
                                                                          exact Decidable.byContradiction fun hnot =>
                                                                                  Exists.casesOn
                                                                                    (Eventually.exists
                                                                                      (mp_mem hboundEvent'
                                                                                        (mp_mem (Tendsto.eventually (by
                                                                                                                       have hposLimit : 0 < Real.exp (-(r : ℝ) * R) := Real.exp_pos _
                                                                                                                       
                                                                                                                       convert ((Real.continuousAt_log hposLimit.ne').tendsto.comp hratio) using 1 <;> ext i <;> simp [R, Real.log_exp]) (Ioi_mem_nhds (lt_of_not_ge hnot)))
                                                                                          (univ_mem' fun i hlargei hboundi => not_lt_of_ge hboundi hlargei))))
                                                                                    fun i hi => hi
    exact hlimitBound'
  
  exact ⟨Sbethe, hSbethe,  by
                             by_contra hnot
                             
                             let δ := (-(r : ℝ) * R -  -((r - 1 : ℕ) : ℝ) * ξinv ) / 2
                             
                             have hbound := hforδ δ (by dsimp [δ]; linarith)
                             dsimp [δ] at hbound
                             linarith ⟩

private theorem firstSectorStrict_eventually
    (q : ℝ) (hq : 4 < q) :
    ∃ Nfirst : ℕ, ∀ N : ℕ, 4 ∣ N → Nfirst ≤ N →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 <
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 := by
  let lam := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨B, S, hS, hratio⟩ := apply_17_at_critical_c q hq 1 (by omega)
  
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam (by
                                         
                                         apply Real.arcosh_pos
                                         
                                         have hsqrt : 2 < Real.sqrt q := by
                                           have hs := Real.sq_sqrt (le_of_lt (by linarith))
                                           nlinarith [Real.sqrt_nonneg q]
                                         linarith)
  
  have hSS  := tendsto_nhds_unique hS  hS₀ 
  
  have hexp : Real.exp (-(lam + 2 * S)) < 1 := by
    apply (Real.exp_lt_one_iff).2
    linarith
  have hexp' : Real.exp (- 1  *
      (Real.arcosh (Real.sqrt q / 2) + 2 * S)) < 1 := by
    grind
  
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.1 (by
                                                   have hexpLimit : Real.exp (- ↑(1 : ℕ)  *
                                                       (Real.arcosh (Real.sqrt q / 2) + 2 * S)) < 1 := by
                                                     simpa using hexp'
                                                   exact hratio.eventually (Iio_mem_nhds hexpLimit))
  refine ⟨4 * (i₀ + B), ?_⟩
  intro N hdiv hlarge
  obtain ⟨k, hk⟩ := hdiv
  
  let i := k - B
  
  have hNrepr : N = 4 * (i + B) := by
    
    
    omega
  
  
  have hlt : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 /
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 < 1 := by
    simpa [hNrepr] using (hi₀ i (by  omega))
  
  exact ((div_lt_one (by
                          apply SixVertex.Lambda_pos
                          · positivity
                          · omega)).1 hlt)

section

variable (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii) (hW12iii : contract_cor313_iii) (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316) (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val) (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ) (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
include hW12i hW12ii hW12iii hW21eq315 hW21eq316 hh319 hq hμ hRate

/-- The repaired dominance gap: for all sufficiently large widths divisible by four,
the centered six-vertex block has the largest Perron root. -/
theorem rc_dominance_for_large_width
     :
    ∃ N₀ : ℕ, ∀ N : ℕ, 4 ∣ N → N₀ ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := by
  obtain ⟨S, hS, hxi, hno, _hboundary⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  
  obtain ⟨S₀, T, hS₀, hT, hpositive, hidentity⟩ :=
    PottsDiscontinuity.identity44 lam  (PottsDiscontinuity.arcosh_pos_of_gt4 q.val hq).1 
  
  
  have hRpositive : 0 < lam + 2 * S := by rw [ tendsto_nhds_unique hS  hS₀  ]; exact hpositive
  have hxiPos  := lt_of_lt_of_le hRpositive (by simpa [lam] using hxi)
  obtain ⟨Nfirst, hfirstEvent⟩ := firstSectorStrict_eventually q.val hq
  
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1 (upperTailRateEventually hW21eq316 q μ hμ ξinv hRate hxiPos)
  
  obtain ⟨NloopCut, hloopData⟩ :=
    lemma314_limsup_and_one_arm_cutoff q (lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno) (ξinv / 64) (by positivity)
  let Nloop := NloopCut.val
  
  
  refine ⟨(max 4 (max (4 * ( max nTail Nloop  + 1)) Nfirst)), ?_⟩
  intro N hdiv hlarge
  obtain ⟨k, hk⟩ := hdiv
  let n := 2 * k - 1
  
  have hperiod : TorusRC.positiveEvenPeriod n = N := by
    dsimp [n, TorusRC.positiveEvenPeriod]
    
    
    
    omega
  
  have hNloop : Nloop ≤ TorusRC.positiveEvenPeriod n := by
    
    
    omega
  
  
  
  have hTail  :=
    hnTail n (by
                omega)
  have hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m )| ≤ ξinv / 32 := by
    obtain ⟨hlim, harm⟩ := hloopData (TorusRC.positiveEvenPeriod n)
      (TorusRC.positiveEvenPeriod_even n) hNloop
    
    exact upperLoopExpectation_abs_log_rate_eventually
      (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
      (ξinv / 64) hlim (windingLoopDensityLogRate_abs_bounded q
                          (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm) (by linarith)
  have hbulk : ∀ r , 2 ≤ r → r ≤ N / 2 →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
        Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N := by
    intro r hr2 hr
    have hgap := upperDominanceGap_fixedIndex hW12i hW12iii q hq ξinv hxiPos n Nloop
      hNloop hTail hLoop (by simpa [hperiod] using hr) hr2
    have hLrPos : 0 < SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r := SixVertex.Lambda_pos (by positivity) hr
    have hLmaxPos : 0 < SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N :=
      SixVertex.LambdaMax_pos (by positivity)
    have hgapN : Real.log (SixVertex.Lambda
        (Real.sqrt (2 + Real.sqrt q.val)) N r) ≤
        Real.log (SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2 := by
      simpa [hperiod] using hgap
    have hexp := Real.exp_le_exp.mpr hgapN
    have hlogToRoot : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
        Real.exp (Real.log (SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2) := by
      rw [Real.exp_log hLrPos] at hexp
      exact hexp
    calc
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
          Real.exp (Real.log (SixVertex.LambdaMax
            (Real.sqrt (2 + Real.sqrt q.val)) N) - ξinv / 2) := hlogToRoot
      _ = Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N := by
        rw [Real.exp_sub, Real.exp_log hLmaxPos]
        rw [Real.exp_neg]
        ring
  have hmax := SixVertex.LambdaMax_eq_Lambda0_of_dominance
    (by positivity) (by
                       grind) (by  omega) (by positivity) hbulk (by
                                                      apply hfirstEvent N  ⟨k, hk⟩ 
                                                      
                                                      omega)
  simpa [hperiod] using hmax

/-- The upper estimate for the inverse correlation length follows from the
fixed-sector bounds after the repaired dominant-eigenvalue identification. -/
theorem rc_xi_inverse_le_critical_rate
     :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨Ndom, hdom⟩ := rc_dominance_for_large_width
    hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq μ hμ ξinv hRate
  obtain ⟨_, S, hS, _hratio⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  have hbound (r : ℕ) (hr : 2 ≤ r) :
       (r - 1 : ℕ)  * ξinv ≤  r  *
        (Real.arcosh (Real.sqrt q.val / 2) + 2 * S) := by
    obtain ⟨S', hS', hsector⟩ := rc_upper_bound_fixed_r
      hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq
      ⟨Ndom, hdom⟩ μ hμ ξinv hRate r hr
    
    simpa [ tendsto_nhds_unique hS' hS ] using hsector
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  have hR : ξinv ≤ R := by
    by_contra hnot
    
    have hsmall : ∀ᶠ n : ℕ in atTop,
         1 /  n   * R < (ξinv - R) / 2 := by
      have hzero := tendsto_one_div_atTop_nhds_zero_nat.mul_const R
      exact hzero.eventually (Iio_mem_nhds (by linarith))
    
    obtain ⟨n, hnsmall, hnpositive⟩ := (hsmall.and (Filter.eventually_gt_atTop 0)).exists
    
    have hsector := hbound (n + 1) (by omega)
    have hsector' :  n  * ξinv ≤ ( n  + 1) * R := by
      grind
    have hdiv : ξinv ≤  ( n  + 1) * R  /  n  :=
      (le_div_iff₀ (by exact_mod_cast hnpositive)).2 (by nlinarith [hsector'])
    have hdivEq :  ( n  + 1) * R  /  n  =
        R +  1 /  n   * R := by
      field_simp [ne_of_gt (by exact_mod_cast hnpositive)]
    
    linarith
  exact ⟨S, hS, hR⟩

end

end PottsDiscontinuity.RCMProof

