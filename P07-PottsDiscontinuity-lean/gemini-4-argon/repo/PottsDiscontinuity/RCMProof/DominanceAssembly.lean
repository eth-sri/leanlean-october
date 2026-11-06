module

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

open PottsDiscontinuity
open SixVertex Torus

noncomputable abbrev upperLoopFactor {N M : ℕ} (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : ℝ :=
  lowerLoopFactor hN hM q hNp hMp A

private theorem upperLoopFactor_eq_densityWeight {N M : ℕ}
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    upperLoopFactor hN hM q hNp hMp A =
      TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
  unfold upperLoopFactor lowerLoopFactor TorusLoops.windingLoopDensityWeight
    TorusLoops.windingLoopDensityBase
  let k := TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A
  let s := Torus.rcNetIndicator hN hM A
  calc Real.rpow (2 / Real.sqrt q.val) (k : ℝ) * Real.rpow q.val (-(s : ℝ))
    _ = (2 / Real.sqrt q.val) ^ k * (Real.rpow q.val (s : ℝ))⁻¹ :=
      congrArg₂ (· * ·) (Real.rpow_natCast _ k) (Real.rpow_neg (le_trans zero_le_one q.property) _)
    _ = (2 / Real.sqrt q.val) ^ k * (q.val ^ s)⁻¹ :=
      congrArg ((2 / Real.sqrt q.val) ^ k * ·) (congrArg Inv.inv (Real.rpow_natCast q.val s))
    _ = (2 / Real.sqrt q.val) ^ k / q.val ^ s := (div_eq_mul_inv _ _).symm

noncomputable def upperTailRateE
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ) : EReal :=
  TorusRC.positiveEvenVerticalTailRateE q r n m

private theorem upperTailRateE_nonpos
    (q : Set.Ici (1 : ℝ)) (r n m : ℕ) : upperTailRateE q r n m ≤ 0 := by
  apply EReal.coe_le_coe_iff.mpr
  dsimp [upperTailRateE, TorusRC.positiveEvenVerticalTailRateE,
    TorusRC.positiveEvenVerticalTailRate]
  exact div_nonpos_of_nonpos_of_nonneg
    (TorusRC.torusRCVerticalTail_log_nonpos _ _ q _ r) (Nat.cast_nonneg _)

private theorem upperTailRateEventually_general
    (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    {r : ℕ} (hr1 : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  let u : ℕ → EReal := fun n => Filter.limsup (fun m => upperTailRateE q r n m) atTop
  have huBounded : Filter.IsBoundedUnder (· ≤ ·) atTop u :=
    Filter.isBoundedUnder_of_eventually_le (Filter.Eventually.of_forall fun n => by
      simpa using Filter.limsup_le_limsup
        (Filter.Eventually.of_forall (upperTailRateE_nonpos q r n)))
  have houter' : Filter.limsup u atTop ≤ ((-((r - 1 : ℕ) : ℝ) * ξinv : ℝ) : EReal) := by
    simpa [u, upperTailRateE] using hW21 q μ hμ ξinv hRate r hr1
  have houterStrict : Filter.limsup u atTop <
      ((-((r - 1 : ℕ) : ℝ) * ξinv + δ : ℝ) : EReal) :=
    lt_of_le_of_lt houter' (EReal.coe_lt_coe_iff.mpr (by linarith))
  filter_upwards [Filter.eventually_lt_of_limsup_lt houterStrict huBounded] with n hn
  have hmBounded : Filter.IsBoundedUnder (· ≤ ·) atTop (fun m => upperTailRateE q r n m) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall (upperTailRateE_nonpos q r n))
  filter_upwards [Filter.eventually_lt_of_limsup_lt hn hmBounded] with m hm
  exact EReal.coe_lt_coe_iff.mp hm

private theorem upperTailRateEventually
    (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ))
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv))
    (hξ : 0 < ξinv) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -3 * ξinv / 4 := by
  filter_upwards [upperTailRateEventually_general hW21 q μ hμ ξinv hRate
    (r := 2) (by norm_num) (ξinv / 4) (by positivity)] with n hn
  filter_upwards [hn] with m hm
  norm_num at hm; linarith

noncomputable def upperTailProbability
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hMp : 0 < M) (r : ℕ) : ℝ :=
  TorusRC.torusRCProbability hN hM q
    (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r)

noncomputable def upperLoopExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) : ℝ :=
  ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
    upperLoopFactor hN hM q hNp hMp A

private theorem upperLoopExpectation_eq_densityExpectation
    {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (hNp : 0 < N) (hMp : 0 < M) :
    upperLoopExpectation hN hM q hNp hMp =
      TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q :=
  Finset.sum_congr rfl fun A _ => by rw [upperLoopFactor_eq_densityWeight]

private theorem upperLoopExpectation_rate_eq
    {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (m : ℕ) :
    TorusLoops.windingLoopDensityLogRate hN hNp q m =
      Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ) := by
  simp [TorusLoops.windingLoopDensityLogRate, TorusRC.positiveEvenPeriod,
    upperLoopExpectation_eq_densityExpectation]

private theorem upperLoopExpectation_abs_log_rate_eventually
    {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N)
    (lim : ℝ)
    (hlim : Filter.limsup
      (fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m)) atTop ≤ lim)
    (hbounded : Filter.IsBoundedUnder (· ≤ ·) atTop
      (fun m => abs (TorusLoops.windingLoopDensityLogRate hN hNp q m)))
    {bound : ℝ} (hbound : lim < bound) :
    ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ bound := by
  filter_upwards [Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hlim hbound) hbounded] with m hm
  simpa [upperLoopExpectation_rate_eq] using hm.le

private theorem upperLoopExpectation_eq_div
    (hW12i : contract_cor313_i) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (N M : ℕ) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M) :
    upperLoopExpectation hN hM q hNp hMp =
      Torus.torusNormalization q N M *
        SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M /
        TorusRC.torusRCPartition hN hM q := by
  have hcontract : (∑ A : RCConfig N M, Torus.torusRCWeight hN hM q A *
      upperLoopFactor hN hM q hNp hMp A) =
      Torus.torusNormalization q N M * SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M :=
    hW12i q hq N M hN hM hNp hMp
  unfold upperLoopExpectation TorusRC.torusRCMass
  simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, hcontract]

private theorem upperLoopExpectation_pos
    (hW12i : contract_cor313_i) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (N M : ℕ) (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) :
    0 < upperLoopExpectation hN hM q hNp hMp := by
  rw [upperLoopExpectation_eq_div hW12i q hq N M hN hM hNp hMp]
  exact div_pos (mul_pos (Torus.torusNormalization_pos q N M)
    (SixVertex.Z6V_pos (by positivity) hNp hMp)) (TorusRC.torusRCPartition_pos hN hM q)

private theorem upperTailFactorization
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (_hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
        (upperTailProbability hN hM q hMp r / upperLoopExpectation hN hM q hNp hMp) := by
  classical
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let E : Set (RCConfig N M) := TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r
  let Er : Set (RCConfig N M) := {A | r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A}
  let w : RCConfig N M → ℝ := Torus.torusRCWeight hN hM q
  let f : RCConfig N M → ℝ := upperLoopFactor hN hM q hNp hMp
  let C : ℝ := Torus.torusNormalization q N M
  have hscale : 0 < C := Torus.torusNormalization_pos q N M
  have hpartitionPos : 0 < TorusRC.torusRCPartition hN hM q := TorusRC.torusRCPartition_pos hN hM q
  have hsectorContract := hW12iii q hq r N M hr1 hN hM hNp hMp
  change C * SixVertex.Z6Vr c N M r ≤
    ∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ Er), w A * f A at hsectorContract
  have hsub : Finset.univ.filter (fun A : RCConfig N M => A ∈ Er) =
      Finset.univ.filter (fun A : RCConfig N M => A ∈ E) := by
    ext A; simp only [Finset.mem_filter]; rfl
  rw [hsub] at hsectorContract
  have hprobEq : TorusRC.torusRCProbability hN hM q E =
      (∑ A ∈ Finset.univ.filter (fun A : RCConfig N M => A ∈ E), w A) /
        TorusRC.torusRCPartition hN hM q := by
    rw [TorusRC.torusRCProbability_eq_sum]
    simp only [Set.indicator_apply]
    rw [← Finset.sum_filter]
    simp_rw [TorusRC.torusRCMass, w]
    rw [← Finset.sum_div]
  have hsectorTail : C * SixVertex.Z6Vr c N M r ≤
      TorusRC.torusRCPartition hN hM q * TorusRC.torusRCProbability hN hM q E := by
    refine hsectorContract.trans ?_
    rw [hprobEq, mul_div_cancel₀ _ hpartitionPos.ne']
    exact Finset.sum_le_sum fun A _ =>
      mul_le_of_le_one_right (TorusRC.torusRCWeight_pos hN hM q A).le
        (lowerLoopFactor_le_one hN hM q hq hNp hMp A)
  have htotalPos := upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp
  have htotalEq : upperLoopExpectation hN hM q hNp hMp =
      C * SixVertex.Z6V c N M / TorusRC.torusRCPartition hN hM q :=
    upperLoopExpectation_eq_div hW12i q hq N M hN hM hNp hMp
  have hP : TorusRC.torusRCPartition hN hM q =
      C * SixVertex.Z6V c N M / upperLoopExpectation hN hM q hNp hMp := by
    rw [htotalEq]; field_simp [hpartitionPos.ne', hscale.ne',
      (SixVertex.Z6V_pos (by positivity : 0 < c) hNp hMp).ne']
  rw [hP] at hsectorTail
  refine (mul_le_mul_iff_of_pos_left hscale).mp (hsectorTail.trans_eq ?_)
  dsimp [upperTailProbability, E, c]
  ring

private theorem upperTailProbability_pos
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ)
    (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    0 < upperTailProbability hN hM q hMp r := by
  have hE := upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp
  have hZ : 0 < SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M :=
    SixVertex.Z6V_pos (by positivity) hNp hMp
  have hZr : 0 < SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r :=
    SixVertex.Z6Vr_pos (by positivity) hNp hMp hr
  have hfactor := upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp hr hr1
  by_contra hnot
  have : SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
      (upperTailProbability hN hM q hMp r / upperLoopExpectation hN hM q hNp hMp) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hZ.le (div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) hE.le)
  linarith

private theorem pow_positiveEvenPeriod (x : ℝ) (m : ℕ) :
    x ^ TorusRC.positiveEvenPeriod m = x ^ 2 * (x ^ 2) ^ m := by
  rw [show TorusRC.positiveEvenPeriod m = 2 + 2 * m by
    simp [TorusRC.positiveEvenPeriod]; omega, pow_add, ← pow_mul]

private theorem upperDominanceGap_fixedIndex
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
    (ξinv : ℝ) (hξ : 0 < ξinv) (n : ℕ)
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
  classical
  let N := TorusRC.positiveEvenPeriod n
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let Lr : ℝ := SixVertex.Lambda c N r
  let Lmax : ℝ := SixVertex.LambdaMax c N
  let D : ℝ := Lmax ^ 2
  let K : ℝ := (2 ^ N : ℝ) * D
  let X : ℕ → ℝ := fun m => Lr ^ TorusRC.positiveEvenPeriod m
  let Y : ℕ → ℝ := fun m =>
    upperTailProbability (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q (TorusRC.positiveEvenPeriod_pos m) 2 /
    upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
      (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)
  let Z : ℕ → ℝ := fun m => (2 ^ N : ℝ) * Lmax ^ TorusRC.positiveEvenPeriod m
  have hN : Even N := TorusRC.positiveEvenPeriod_even n
  have hNp : 0 < N := TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < c := by positivity
  have hLr : 0 < Lr := SixVertex.Lambda_pos hc hr
  have hLmax : 0 < Lmax := SixVertex.LambdaMax_pos hc
  have hD : 0 < D := by positivity
  have hK : 0 < K := by positivity
  have hEpos (m : ℕ) := upperLoopExpectation_pos hW12i q hq N (TorusRC.positiveEvenPeriod m) hN
    (TorusRC.positiveEvenPeriod_even m) hNp (TorusRC.positiveEvenPeriod_pos m)
  have hYpos : ∀ᶠ m : ℕ in atTop, 0 < Y m :=
    Filter.Eventually.of_forall fun m =>
      div_pos (upperTailProbability_pos hW12i hW12iii q hq N
        (TorusRC.positiveEvenPeriod m) hN (TorusRC.positiveEvenPeriod_even m)
        hNp (TorusRC.positiveEvenPeriod_pos m) (r := 2) (by omega) (by norm_num)) (hEpos m)
  have hZpos : ∀ᶠ m : ℕ in atTop, 0 < Z m := Filter.Eventually.of_forall fun _ => by positivity
  have hlower : ∀ᶠ m : ℕ in atTop, (Lr ^ 2) * (Lr ^ 2) ^ m ≤ X m :=
    Filter.Eventually.of_forall fun m => (pow_positiveEvenPeriod Lr m).ge
  have hupper : ∀ᶠ m : ℕ in atTop, X m ≤ Y m * Z m := by
    filter_upwards [hYpos] with m hYm
    let M := TorusRC.positiveEvenPeriod m
    have hM : Even M := TorusRC.positiveEvenPeriod_even m
    have hMp : 0 < M := TorusRC.positiveEvenPeriod_pos m
    have htrace := SixVertex.Lambda_pow_le_Z6Vr_even hc hNp hMp hr hM
    have hsector := upperTailFactorization hW12i hW12iii q hq N M hN hM hNp hMp hr (by omega)
    have htailMono : upperTailProbability hN hM q hMp r ≤ upperTailProbability hN hM q hMp 2 :=
      TorusRC.torusRCProbability_mono hN hM q fun A hA => le_trans hr2 hA
    have hwhole := SixVertex.Z6V_le_two_pow_mul_LambdaMax_pow hc hNp hMp
    calc X m ≤ SixVertex.Z6Vr c N M r := htrace
      _ ≤ SixVertex.Z6V c N M * (upperTailProbability hN hM q hMp r /
            upperLoopExpectation hN hM q hNp hMp) := hsector
      _ ≤ SixVertex.Z6V c N M * Y m :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htailMono (hEpos m).le)
          (SixVertex.Z6V_pos hc hNp hMp).le
      _ ≤ Z m * Y m := mul_le_mul_of_nonneg_right hwhole hYm.le
      _ = Y m * Z m := mul_comm _ _
  have hYrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (1 / (m : ℝ)) * Real.log (Y m) ≤ -ξinv + ε := by
    intro ε hε
    filter_upwards [Filter.eventually_ge_atTop 1, hTail, hLoop] with m hm htail hmLoop
    let M := TorusRC.positiveEvenPeriod m
    let p := upperTailProbability hN (TorusRC.positiveEvenPeriod_even m) q
      (TorusRC.positiveEvenPeriod_pos m) 2
    let e := upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m) q hNp
      (TorusRC.positiveEvenPeriod_pos m)
    have hp : 0 < p := upperTailProbability_pos hW12i hW12iii q hq N M hN
      (TorusRC.positiveEvenPeriod_even m) hNp (TorusRC.positiveEvenPeriod_pos m)
      (r := 2) (by omega) (by norm_num)
    have he : 0 < e := hEpos m
    have htailRate : Real.log p / (M : ℝ) < -3 * ξinv / 4 := htail
    have hMcast : (M : ℝ) = 2 * ((m : ℝ) + 1) := by
      dsimp [M, TorusRC.positiveEvenPeriod]; push_cast; ring
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hmcast : (0 : ℝ) < m := by linarith
    have hratioLo : 2 ≤ (M : ℝ) / (m : ℝ) := by rw [hMcast]; field_simp; linarith
    have hratioHi : (M : ℝ) / (m : ℝ) ≤ 4 := by rw [hMcast]; field_simp; linarith
    have hloopUpper : -Real.log e / (M : ℝ) ≤ ξinv / 32 := by
      simpa [neg_div] using neg_le_neg (abs_le.mp hmLoop).1
    have hMpos : 0 < (M : ℝ) := by linarith
    have hscaledEq : (1 / (m : ℝ)) * Real.log (Y m) =
        ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ)) +
          ((M : ℝ) / (m : ℝ)) * (-Real.log e / (M : ℝ)) := by
      dsimp [Y, p, e]
      rw [Real.log_div hp.ne' he.ne']
      field_simp [hmcast.ne', hMpos.ne']; ring
    rw [hscaledEq]
    have h1 : ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ)) < -3 * ξinv / 2 := by
      calc ((M : ℝ) / (m : ℝ)) * (Real.log p / (M : ℝ))
        _ ≤ 2 * (Real.log p / (M : ℝ)) := mul_le_mul_of_nonpos_right hratioLo (by linarith)
        _ < -3 * ξinv / 2 := by linarith
    have h2 : ((M : ℝ) / (m : ℝ)) * (-Real.log e / (M : ℝ)) ≤ ξinv / 8 := by
      calc ((M : ℝ) / (m : ℝ)) * (-Real.log e / (M : ℝ))
        _ ≤ ((M : ℝ) / (m : ℝ)) * (ξinv / 32) := mul_le_mul_of_nonneg_left hloopUpper (by positivity)
        _ ≤ 4 * (ξinv / 32) := mul_le_mul_of_nonneg_right hratioHi (by positivity)
        _ = ξinv / 8 := by ring
    linarith
  have hZrate : ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (1 / (m : ℝ)) * Real.log (Z m) ≤ Real.log D + ε := by
    intro ε hε
    have hconv : Tendsto (fun m : ℕ => Real.log D + (1 / (m : ℝ)) * Real.log K)
        atTop (𝓝 (Real.log D)) := by
      simpa using (tendsto_const_nhds (x := Real.log D)).add
        (tendsto_one_div_atTop_nhds_zero_nat.mul_const (Real.log K))
    have hEq : (fun m : ℕ => (1 / (m : ℝ)) * Real.log (Z m)) =ᶠ[atTop]
        (fun m : ℕ => Real.log D + (1 / (m : ℝ)) * Real.log K) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hZfactor : Z m = K * D ^ m := by
        dsimp [Z, K, D]; rw [pow_positiveEvenPeriod Lmax m, mul_assoc]
      rw [hZfactor, Real.log_mul hK.ne' (pow_ne_zero _ hD.ne'), Real.log_pow]
      field_simp; ring
    filter_upwards [(hconv.congr' hEq.symm).eventually
      (Iio_mem_nhds (by linarith : Real.log D < Real.log D + ε))] with m hm
    exact hm.le
  have hgrowth := SixVertex.log_growth_le_of_eventually_factorized
    (C := Lr ^ 2) (Λ := Lr ^ 2) (Λmax := D) (a := -ξinv) (b := 0)
    (by positivity) (by positivity) X Y Z hYpos hZpos hlower hupper hYrate
    (by simpa using hZrate)
  rw [Real.log_pow, Real.log_pow] at hgrowth
  dsimp [Lr, Lmax, c, N, D] at hgrowth ⊢
  nlinarith

private theorem sectorLogRate_le_of_eventual_tail
    (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii)
    (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (n : ℕ)
    (ξinv δ : ℝ) {r : ℕ} (hr : r ≤ TorusRC.positiveEvenPeriod n / 2) (hr1 : 1 ≤ r)
    (hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val))
      (TorusRC.positiveEvenPeriod n) =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val))
          (TorusRC.positiveEvenPeriod n) 0)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m < -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2)
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
  classical
  let N := TorusRC.positiveEvenPeriod n
  let c : ℝ := Real.sqrt (2 + Real.sqrt q.val)
  let f (m : ℕ) := (1 / (TorusRC.positiveEvenPeriod m : ℝ)) *
    Real.log (SixVertex.Z6Vr c N (TorusRC.positiveEvenPeriod m) r /
      SixVertex.Z6V c N (TorusRC.positiveEvenPeriod m))
  have hNpos : 0 < N := TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < c := by positivity
  have hMseq : Tendsto TorusRC.positiveEvenPeriod atTop atTop :=
    Filter.tendsto_atTop.2 fun K => by
      filter_upwards [Filter.eventually_ge_atTop K] with m hm
      dsimp [TorusRC.positiveEvenPeriod]; omega
  have hlimit : Tendsto f atTop
      (𝓝 (Real.log (SixVertex.Lambda c N r / SixVertex.Lambda c N 0))) := by
    simpa [Function.comp_def, f, N, c] using
      (SixVertex.tendsto_log_Z6V_ratio_eq_Lambda_ratio hc hNpos hr hcenter).comp hMseq
  refine le_of_tendsto hlimit ?_
  filter_upwards [hTail, hLoop] with m htail hloop
  let M := TorusRC.positiveEvenPeriod m
  have hM : Even M := TorusRC.positiveEvenPeriod_even m
  have hMp : 0 < M := TorusRC.positiveEvenPeriod_pos m
  have hZV : 0 < SixVertex.Z6V c N M := SixVertex.Z6V_pos hc hNpos hMp
  have hP := upperTailProbability_pos hW12i hW12iii q hq N M
    (TorusRC.positiveEvenPeriod_even n) hM hNpos hMp hr hr1
  have hE := upperLoopExpectation_pos hW12i q hq N M
    (TorusRC.positiveEvenPeriod_even n) hM hNpos hMp
  have hsector := upperTailFactorization hW12i hW12iii q hq N M
    (TorusRC.positiveEvenPeriod_even n) hM hNpos hMp hr hr1
  have hratio : SixVertex.Z6Vr c N M r / SixVertex.Z6V c N M ≤
      upperTailProbability (TorusRC.positiveEvenPeriod_even n) hM q hMp r /
        upperLoopExpectation (TorusRC.positiveEvenPeriod_even n) hM q hNpos hMp :=
    (div_le_iff₀ hZV).2 (by simpa [mul_comm] using hsector)
  have hlog := Real.log_le_log (div_pos (SixVertex.Z6Vr_pos hc hNpos hMp hr) hZV) hratio
  rw [Real.log_div hP.ne' hE.ne'] at hlog
  have hloopUpper : -(Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
      hM q hNpos hMp) / (M : ℝ)) ≤ δ / 2 := by
    have := (abs_le.mp hloop).1; linarith
  have htailRate : Real.log (upperTailProbability (TorusRC.positiveEvenPeriod_even n)
      hM q hMp r) / (M : ℝ) < -((r - 1 : ℕ) : ℝ) * ξinv + δ / 2 := htail
  have hdiv : f m ≤ Real.log (upperTailProbability (TorusRC.positiveEvenPeriod_even n)
        hM q hMp r) / (M : ℝ) -
      Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        hM q hNpos hMp) / (M : ℝ) := by
    dsimp [f]
    rw [← sub_div, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hlog (Nat.cast_nonneg M)
  linarith

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
  classical
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  obtain ⟨_, _, _, hno⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  obtain ⟨Ndom, hdom⟩ := hDominance
  obtain ⟨B, Sbethe, hSbethe, hratio⟩ := apply_17_at_critical_c q.val hq r (by omega)
  let R : ℝ := lam + 2 * Sbethe
  have hlogLimit : Tendsto (fun i : ℕ => Real.log
      (SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) r /
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) (4 * (i + B)) 0))
      atTop (𝓝 (-(r : ℝ) * R)) := by
    have h := (Real.continuousAt_log (Real.exp_pos (-(r : ℝ) * R)).ne').tendsto.comp hratio
    convert h using 1 <;> ext i <;> simp [R, Real.log_exp]
  have hzeroSquare := lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno
  have hforδ : ∀ δ : ℝ, 0 < δ →
      -(r : ℝ) * R ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
    intro δ hδ
    have hTailEvent' := upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate
      (r := r) (by omega) (δ := δ / 2) (by linarith)
    obtain ⟨nTail', hnTail'⟩ := Filter.eventually_atTop.1 hTailEvent'
    obtain ⟨NloopCut', hloopData'⟩ :=
      lemma314_limsup_and_one_arm_cutoff q hzeroSquare (δ / 4) (by linarith)
    let Nloop' := NloopCut'.val
    let i₁ := max r (max 1 (max nTail' (max Nloop' Ndom)))
    refine le_of_tendsto hlogLimit ?_
    filter_upwards [Filter.eventually_ge_atTop i₁] with i hi
    let N := 4 * (i + B)
    let n := 2 * (i + B) - 1
    have hperiod : TorusRC.positiveEvenPeriod n = N := by
      dsimp [n, N, TorusRC.positiveEvenPeriod, i₁] at hi ⊢
      rw [Nat.sub_add_cancel (by omega)]; omega
    have hNdom : Ndom ≤ N := by dsimp [N, i₁] at hi ⊢; omega
    have hNloopPeriod : Nloop' ≤ TorusRC.positiveEvenPeriod n := by
      rw [hperiod]; dsimp [N, i₁] at hi ⊢; omega
    have hnTailIndex : nTail' ≤ n := by dsimp [n, i₁] at hi ⊢; omega
    have hcenter : SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 :=
      hdom N ⟨i + B, rfl⟩ hNdom
    have hLoop : ∀ᶠ m : ℕ in atTop,
        |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
          (TorusRC.positiveEvenPeriod_even m) q
          (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
            (TorusRC.positiveEvenPeriod m : ℝ)| ≤ δ / 2 := by
      obtain ⟨hlim, harm⟩ := hloopData' (TorusRC.positiveEvenPeriod n)
        (TorusRC.positiveEvenPeriod_even n) hNloopPeriod
      exact upperLoopExpectation_abs_log_rate_eventually
        (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
        (δ / 4) hlim (windingLoopDensityLogRate_abs_bounded q
          (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm)
        (by linarith)
    have hfixed := sectorLogRate_le_of_eventual_tail hW12i hW12iii q hq n
      ξinv δ (r := r) (by rw [hperiod]; dsimp [N, i₁] at hi ⊢; omega) (by omega)
      (by simpa [hperiod] using hcenter) (hnTail' n hnTailIndex) hLoop
    simpa [N, hperiod] using hfixed
  refine ⟨Sbethe, hSbethe, ?_⟩
  by_contra hnot
  have hbound := hforδ ((-(r : ℝ) * R - (-((r - 1 : ℕ) : ℝ) * ξinv)) / 2)
    (by dsimp [R] at *; linarith)
  dsimp [R] at *; linarith

private theorem firstSectorStrict_eventually
    (q : ℝ) (hq : 4 < q) :
    ∃ Nfirst : ℕ, ∀ N : ℕ, 4 ∣ N → Nfirst ≤ N →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 <
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 := by
  let lam := Real.arcosh (Real.sqrt q / 2)
  obtain ⟨B, S, hS, hratio⟩ := apply_17_at_critical_c q hq 1 (by omega)
  have hlam : 0 < lam := (PottsDiscontinuity.arcosh_pos_of_gt4 q hq).1
  obtain ⟨S₀, _, hS₀, _, hpositive, _⟩ := PottsDiscontinuity.identity44 lam hlam
  have hSS : S = S₀ := tendsto_nhds_unique hS hS₀
  have hexpLimit : Real.exp (-(↑(1 : ℕ) : ℝ) * (lam + 2 * S)) < 1 := by
    rw [Real.exp_lt_one_iff]; push_cast; linarith [hSS ▸ hpositive]
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.1 (hratio.eventually (Iio_mem_nhds hexpLimit))
  refine ⟨4 * (i₀ + B), fun N ⟨k, hk⟩ hlarge => ?_⟩
  have hNrepr : N = 4 * (k - B + B) := by omega
  have hlt : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 /
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 < 1 := by
    simpa [hNrepr] using hi₀ (k - B) (by omega)
  exact (div_lt_one (SixVertex.Lambda_pos (by positivity) (by omega))).1 hlt

theorem rc_dominance_for_large_width
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv)) :
    ∃ N₀ : ℕ, ∀ N : ℕ, 4 ∣ N → N₀ ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := by
  obtain ⟨S, hS, hxi, hno⟩ :=
    routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii
      hW21eq315 q hh319 hq μ hμ ξinv hRate
  let lam := Real.arcosh (Real.sqrt q.val / 2)
  have hlam : 0 < lam := (PottsDiscontinuity.arcosh_pos_of_gt4 q.val hq).1
  obtain ⟨S₀, _, hS₀, _, hpositive, _⟩ := PottsDiscontinuity.identity44 lam hlam
  have hSS : S = S₀ := tendsto_nhds_unique hS hS₀
  have hxiPos : 0 < ξinv := lt_of_lt_of_le (hSS ▸ hpositive) (by simpa [lam] using hxi)
  obtain ⟨Nfirst, hfirstEvent⟩ := firstSectorStrict_eventually q.val hq
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1
    (upperTailRateEventually hW21eq316 q μ hμ ξinv hRate hxiPos)
  have hzeroSquare := lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno
  obtain ⟨NloopCut, hloopData⟩ :=
    lemma314_limsup_and_one_arm_cutoff q hzeroSquare (ξinv / 64) (by positivity)
  let Nloop := NloopCut.val
  let n₀ := max nTail Nloop
  let N₀ := max 4 (max (4 * (n₀ + 1)) Nfirst)
  refine ⟨N₀, fun N ⟨k, hk⟩ hlarge => ?_⟩
  let n := 2 * k - 1
  have hNpos : 0 < N := by dsimp [N₀] at hlarge; omega
  have hperiod : TorusRC.positiveEvenPeriod n = N := by
    dsimp [n, TorusRC.positiveEvenPeriod, N₀] at hlarge ⊢
    rw [Nat.sub_add_cancel (by omega)]; omega
  have hNloop : Nloop ≤ TorusRC.positiveEvenPeriod n := by
    rw [hperiod]; dsimp [N₀, n₀] at hlarge; omega
  have hN : Even N := ⟨2 * k, by omega⟩
  have hfirst : SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 1 <
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 :=
    hfirstEvent N ⟨k, hk⟩ (by dsimp [N₀] at hlarge; omega)
  have hLoop : ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n)
        (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ)| ≤ ξinv / 32 := by
    obtain ⟨hlim, harm⟩ := hloopData (TorusRC.positiveEvenPeriod n)
      (TorusRC.positiveEvenPeriod_even n) hNloop
    exact upperLoopExpectation_abs_log_rate_eventually
      (TorusRC.positiveEvenPeriod_even n) q (TorusRC.positiveEvenPeriod_pos n)
      (ξinv / 64) hlim (windingLoopDensityLogRate_abs_bounded q
        (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm)
      (by linarith)
  have hbulk : ∀ r : ℕ, 2 ≤ r → r ≤ N / 2 →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r ≤
        Real.exp (-(ξinv / 2)) * SixVertex.LambdaMax
          (Real.sqrt (2 + Real.sqrt q.val)) N := by
    intro r hr2 hr
    have hgap := upperDominanceGap_fixedIndex hW12i hW12iii q hq ξinv hxiPos n
      (hnTail n (by dsimp [N₀, n₀, n] at hlarge ⊢; omega))
      hLoop (by simpa [hperiod] using hr) hr2
    have hLrPos : 0 < SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N r :=
      SixVertex.Lambda_pos (by positivity) hr
    have hLmaxPos : 0 < SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N :=
      SixVertex.LambdaMax_pos (by positivity)
    have hexp := Real.exp_le_exp.mpr (by simpa [hperiod] using hgap)
    rw [Real.exp_log hLrPos, Real.exp_sub, Real.exp_log hLmaxPos,
      div_eq_mul_inv, ← Real.exp_neg, mul_comm] at hexp
    exact hexp
  exact SixVertex.LambdaMax_eq_Lambda0_of_dominance
    (by positivity) hN hNpos (by positivity) hbulk hfirst

theorem rc_xi_inverse_le_critical_rate
    (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii)
    (hW12iii : contract_cor313_iii)
    (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316)
    (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val)
    (μ : MeasureTheory.Measure FK.LatticeConfiguration)
    (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP
      (FK.criticalParameters q).toQ 0 μ)
    (ξinv : ℝ)
    (hRate : Tendsto (fun n : ℕ => -Real.log
      (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ))
      atTop (𝓝 ξinv)) :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨Ndom, hdom⟩ := rc_dominance_for_large_width
    hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq μ hμ ξinv hRate
  obtain ⟨_, S, hS, _hratio⟩ := apply_17_at_critical_c q.val hq 1 (by omega)
  let R := Real.arcosh (Real.sqrt q.val / 2) + 2 * S
  have hbound (r : ℕ) (hr : 2 ≤ r) : ((r - 1 : ℕ) : ℝ) * ξinv ≤ (r : ℝ) * R := by
    obtain ⟨S', hS', hsector⟩ := rc_upper_bound_fixed_r
      hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq
      ⟨Ndom, hdom⟩ μ hμ ξinv hRate r hr
    dsimp [R]
    rwa [← tendsto_nhds_unique hS' hS]
  refine ⟨S, hS, ?_⟩
  by_contra hnot
  have hsmall : ∀ᶠ n : ℕ in atTop, (1 / (n : ℝ)) * R < (ξinv - R) / 2 :=
    (tendsto_one_div_atTop_nhds_zero_nat.mul_const R).eventually
      (Iio_mem_nhds (by dsimp [R] at *; linarith))
  obtain ⟨n, hnsmall, hnpositive⟩ := (hsmall.and (Filter.eventually_gt_atTop 0)).exists
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpositive
  have hsector := hbound (n + 1) (by omega)
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hsector
  have := mul_lt_mul_of_pos_left hnsmall hnR
  rw [← mul_assoc, mul_one_div_cancel hnR.ne', one_mul] at this
  nlinarith

end PottsDiscontinuity.RCMProof
