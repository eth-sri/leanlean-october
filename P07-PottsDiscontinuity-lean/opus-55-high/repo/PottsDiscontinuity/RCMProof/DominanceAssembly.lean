module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Infra.Lambda
public import PottsDiscontinuity.RCMProof.RouteB
public import PottsDiscontinuity.RCMProof.Lemma314Adapters
public import PottsDiscontinuity.SixVertex.Sec33Dominance
public import Mathlib

public noncomputable section

open Finset Filter Topology

namespace PottsDiscontinuity.RCMProof

open PottsDiscontinuity
open SixVertex Torus

section
variable {N M : ℕ} (hN : Even N) (hM : Even M)
def upperLoopFactor (q : Set.Ici (1 : ℝ)) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : ℝ :=
  Real.rpow (2 / Real.sqrt q.val)
      (TorusLoops.windingLoopCount hN hM ⟨0, hNp⟩ ⟨0, hMp⟩ A : ℝ) *
    Real.rpow q.val (-(Torus.rcNetIndicator hN hM A : ℝ))

section
variable (q : Set.Ici (1 : ℝ))
theorem upperLoopFactor_eq_densityWeight (hNp : 0 < N) (hMp : 0 < M) (A : RCConfig N M) :
    upperLoopFactor hN hM q hNp hMp A =
      TorusLoops.windingLoopDensityWeight hN hM hNp hMp q A := by
  unfold upperLoopFactor TorusLoops.windingLoopDensityWeight TorusLoops.windingLoopDensityBase
  aesop

theorem upperLoopFactor_le_one (hq : 4 < q.val) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) : upperLoopFactor hN hM q hNp hMp A ≤ 1 := by
  have hbase : TorusLoops.windingLoopDensityUpperBase q = 1 := by
    simp [TorusLoops.windingLoopDensityUpperBase, TorusLoops.windingLoopDensityBase]
    rw [div_le_one (by positivity), Real.le_sqrt] <;> linarith
  simpa [upperLoopFactor_eq_densityWeight, hbase] using TorusLoops.windingLoopDensityWeight_le_global hN hM hNp hMp q A
end
end

section
variable (hW21 : contract_eq316) (q : Set.Ici (1 : ℝ)) (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ) (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv))
include hW21 μ hμ hRate
theorem upperTailRateEventually_general
    {r : ℕ} (hr1 : 1 ≤ r) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q r n m <
        -((r - 1 : ℕ) : ℝ) * ξinv + δ := by
  have h0 (n m) : TorusRC.positiveEvenVerticalTailRateE q r n m ≤ 0 :=
    EReal.coe_le_coe_iff.mpr (div_nonpos_of_nonpos_of_nonneg (TorusRC.torusRCVerticalTail_log_nonpos _ _ q _ r) (Nat.cast_nonneg _))
  filter_upwards [Filter.eventually_lt_of_limsup_lt ((hW21 q μ hμ ξinv hRate r hr1).trans_lt (EReal.coe_lt_coe_iff.mpr (lt_add_of_pos_right _ hδ)))
    (Filter.isBoundedUnder_of_eventually_le (.of_forall fun n => Filter.limsup_le_of_le (h := .of_forall (h0 n))))] with n hn
  filter_upwards [Filter.eventually_lt_of_limsup_lt hn (Filter.isBoundedUnder_of_eventually_le (.of_forall (h0 n)))] with m hm
  exact EReal.coe_lt_coe_iff.mp hm
end

section
variable {N M : ℕ} (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
def upperTailProbability
    (hMp : 0 < M) (r : ℕ) : ℝ :=
  TorusRC.torusRCProbability hN hM q
    (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ r)

section
variable (hNp : 0 < N) (hMp : 0 < M)
def upperLoopExpectation
     : ℝ :=
  ∑ A : RCConfig N M, TorusRC.torusRCMass hN hM q A *
    upperLoopFactor hN hM q hNp hMp A

theorem upperLoopExpectation_eq_densityExpectation
     :
    upperLoopExpectation hN hM q hNp hMp =
      TorusLoops.phi_T_windingLoopDensityExpectation hN hM hNp hMp q := by
  unfold upperLoopExpectation TorusLoops.phi_T_windingLoopDensityExpectation
  simp [upperLoopFactor_eq_densityWeight]
end
end

section
variable {N : ℕ} (hN : Even N) (q : Set.Ici (1 : ℝ)) (hNp : 0 < N)
theorem upperLoopExpectation_rate_eq
    (m : ℕ) :
    TorusLoops.windingLoopDensityLogRate hN hNp q m =
      Real.log (upperLoopExpectation hN (TorusRC.positiveEvenPeriod_even m)
        q hNp (TorusRC.positiveEvenPeriod_pos m)) /
          (TorusRC.positiveEvenPeriod m : ℝ) := by
  simp [TorusLoops.windingLoopDensityLogRate, TorusRC.positiveEvenPeriod,
    upperLoopExpectation_eq_densityExpectation]

end

theorem upperLoop_eventually (q : Set.Ici (1 : ℝ)) (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ) (hno : μ (Duality.infiniteClusterAt (0, 0)) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n, N₀ ≤ TorusRC.positiveEvenPeriod n → ∀ᶠ m : ℕ in atTop,
      |Real.log (upperLoopExpectation (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_even m) q
        (TorusRC.positiveEvenPeriod_pos n) (TorusRC.positiveEvenPeriod_pos m)) / (TorusRC.positiveEvenPeriod m : ℝ)| ≤ ε := by
  obtain ⟨N₀, h⟩ := lemma314_limsup_and_one_arm_cutoff q (lemma314_square_boundary_decay_of_nonpercolation q μ hμ hno) (ε / 2) (by positivity)
  refine ⟨N₀.val, fun n hn => ?_⟩
  obtain ⟨hlim, harm⟩ := h _ (TorusRC.positiveEvenPeriod_even n) hn
  filter_upwards [Filter.eventually_lt_of_limsup_lt (hlim.trans_lt (half_lt_self hε)) (windingLoopDensityLogRate_abs_bounded q (TorusRC.positiveEvenPeriod_even n) (TorusRC.positiveEvenPeriod_pos n) harm)] with m hm
  grind [upperLoopExpectation_rate_eq]

section
variable (hW12i : contract_cor313_i) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val) (N M : ℕ) (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
include hW12i hq
theorem upperLoopExpectation_eq :
    upperLoopExpectation hN hM q hNp hMp = torusCorrespondenceScale q N M * SixVertex.Z6V (criticalSixVertexParameter q) N M / TorusRC.torusRCPartition hN hM q := by
  rw [← hW12i q hq N M hN hM hNp hMp, upperLoopExpectation, Finset.sum_div]
  exact Finset.sum_congr rfl fun A _ => div_mul_eq_mul_div _ _ _

theorem upperLoopExpectation_pos : 0 < upperLoopExpectation hN hM q hNp hMp := by
  rw [upperLoopExpectation_eq hW12i q hq N M hN hM hNp hMp]
  exact div_pos (mul_pos (Torus.torusNormalization_pos q N M) (SixVertex.Z6V_pos (Real.sqrt_pos.2 (by positivity)) hNp hMp)) (TorusRC.torusRCPartition_pos hN hM q)

theorem upperTailFactorization (hW12iii : contract_cor313_iii) {r : ℕ} (hr1 : 1 ≤ r) :
    SixVertex.Z6Vr (Real.sqrt (2 + Real.sqrt q.val)) N M r ≤
      SixVertex.Z6V (Real.sqrt (2 + Real.sqrt q.val)) N M *
        (upperTailProbability hN hM q hMp r / upperLoopExpectation hN hM q hNp hMp) := by
  show SixVertex.Z6Vr (criticalSixVertexParameter q) N M r ≤ SixVertex.Z6V (criticalSixVertexParameter q) N M * _
  have hC : 0 < torusCorrespondenceScale q N M := Torus.torusNormalization_pos q N M
  have hP := TorusRC.torusRCPartition_pos hN hM q
  have hZ : 0 < SixVertex.Z6V (criticalSixVertexParameter q) N M := SixVertex.Z6V_pos (Real.sqrt_pos.2 (by positivity)) hNp hMp
  have key := (hW12iii q hq r N M hr1 hN hM hNp hMp).trans (show _ ≤ TorusRC.torusRCPartition hN hM q * upperTailProbability hN hM q hMp r by
    rw [upperTailProbability, TorusRC.torusRCProbability_eq_sum, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun A _ => ?_
    by_cases h : r ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A
    · simp only [h, ite_true, Set.indicator_apply, TorusRC.torusRCVerticalTail, Set.mem_ofPred_eq, TorusRC.torusRCMass, mul_div_cancel₀ _ hP.ne']
      exact mul_le_of_le_one_right (TorusRC.torusRCWeight_pos hN hM q A).le (upperLoopFactor_le_one hN hM q hq hNp hMp A)
    · simp [h, TorusRC.torusRCVerticalTail])
  rw [upperLoopExpectation_eq hW12i q hq N M hN hM hNp hMp]
  field_simp
  nlinarith

include hNp in
theorem upperTailProbability_pos (hW12iii : contract_cor313_iii) {r : ℕ} (hr : r ≤ N / 2) (hr1 : 1 ≤ r) :
    0 < upperTailProbability hN hM q hMp r :=
  (div_pos_iff_of_pos_right (upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp)).1 (pos_of_mul_pos_right
    ((SixVertex.Z6Vr_pos (by positivity) hNp hMp hr).trans_le (upperTailFactorization hW12i q hq N M hN hM hNp hMp hW12iii hr1)) (SixVertex.Z6V_pos (by positivity) hNp hMp).le)
end

section
variable (hW12i : contract_cor313_i) (hW12iii : contract_cor313_iii) (q : Set.Ici (1 : ℝ)) (hq : 4 < q.val)
include hW12i hW12iii hq
theorem upperDominanceGap_fixedIndex
    (ξinv : ℝ) (hξ : 0 < ξinv) (n : ℕ)
    (hTail : ∀ᶠ m : ℕ in atTop,
      TorusRC.positiveEvenVerticalTailRate q 2 n m < -((2 - 1 : ℕ) : ℝ) * ξinv + ξinv / 4)
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
  set N := TorusRC.positiveEvenPeriod n
  set c := √(2 + √q.val)
  have hN := TorusRC.positiveEvenPeriod_even n
  have hNp := TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < c := by positivity
  have hLr := SixVertex.Lambda_pos hc hr
  have hLmax : 0 < SixVertex.LambdaMax c N := SixVertex.LambdaMax_pos hc
  suffices ∀ᶠ m in atTop, Real.log (SixVertex.Lambda c N r) - Real.log (SixVertex.LambdaMax c N) +
      23 * ξinv / 32 ≤ Real.log 2 * N / (TorusRC.positiveEvenPeriod m : ℝ) by
    linarith [ge_of_tendsto (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun m => (by simp [TorusRC.positiveEvenPeriod]; omega : m ≤ _)) tendsto_id))) this]
  filter_upwards [hTail, hLoop] with m ht hl
  set M := TorusRC.positiveEvenPeriod m
  have hM := TorusRC.positiveEvenPeriod_even m
  have hMp := TorusRC.positiveEvenPeriod_pos m
  have he := upperLoopExpectation_pos hW12i q hq N M hN hM hNp hMp
  have hp : 0 < TorusRC.torusRCProbability hN hM q (TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ 2) :=
    upperTailProbability_pos hW12i q hq N M hN hM hNp hMp hW12iii (by omega) one_le_two
  have key := Real.log_le_log (pow_pos hLr M) <| (SixVertex.Lambda_pow_le_Z6Vr_even hc hNp hMp hr hM).trans <|
    (upperTailFactorization hW12i q hq N M hN hM hNp hMp hW12iii (by omega)).trans <|
    mul_le_mul (SixVertex.Z6V_le_two_pow_mul_LambdaMax_pow hc hNp hMp) (div_le_div_of_nonneg_right
      (TorusRC.torusRCProbability_mono hN hM q (F := TorusRC.torusRCVerticalTail hN hM ⟨0, hMp⟩ 2)
        fun A (hA : r ≤ _) => (by omega : 2 ≤ Torus.rcVerticalWinding hN hM ⟨0, hMp⟩ A)) he.le)
      (div_nonneg (upperTailProbability_pos hW12i q hq N M hN hM hNp hMp hW12iii hr (by omega)).le he.le)
      (by positivity)
  rw [Real.log_mul (by positivity) (div_pos hp he).ne', Real.log_mul (by positivity) (by positivity), Real.log_div hp.ne' he.ne', Real.log_pow, Real.log_pow, Real.log_pow] at key
  have hM0 : (0 : ℝ) < M := by positivity
  rw [abs_le, le_div_iff₀ hM0, div_le_iff₀ hM0] at hl
  rw [TorusRC.positiveEvenVerticalTailRate, div_lt_iff₀ hM0] at ht
  norm_num at ht
  rw [le_div_iff₀ hM0]
  linarith

theorem sectorLogRate_le_of_eventual_tail
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
  set N := TorusRC.positiveEvenPeriod n
  have hNp := TorusRC.positiveEvenPeriod_pos n
  have hc : 0 < √(2 + √q.val) := by positivity
  refine le_of_tendsto ((SixVertex.tendsto_log_Z6V_ratio_eq_Lambda_ratio hc hNp hr hcenter).comp (tendsto_atTop_mono (g := TorusRC.positiveEvenPeriod) (fun m => by simp [TorusRC.positiveEvenPeriod]; omega) tendsto_id)) ?_
  filter_upwards [hTail, hLoop] with m ht hl
  rw [Function.comp_apply, one_div, inv_mul_le_iff₀ (Nat.cast_pos.2 (TorusRC.positiveEvenPeriod_pos m))]
  set M := TorusRC.positiveEvenPeriod m
  have hM := TorusRC.positiveEvenPeriod_even m
  have hMp := TorusRC.positiveEvenPeriod_pos m
  have he := upperLoopExpectation_pos hW12i q hq N M (TorusRC.positiveEvenPeriod_even n) hM hNp hMp
  have hp := upperTailProbability_pos hW12i q hq N M (TorusRC.positiveEvenPeriod_even n) hM hNp hMp hW12iii hr hr1
  have key := Real.log_le_log (div_pos (SixVertex.Z6Vr_pos hc hNp hMp hr) (SixVertex.Z6V_pos hc hNp hMp)) ((div_le_iff₀' (SixVertex.Z6V_pos hc hNp hMp)).2 (upperTailFactorization hW12i q hq N M (TorusRC.positiveEvenPeriod_even n) hM hNp hMp hW12iii hr1))
  rw [Real.log_div hp.ne' he.ne'] at key
  have hM0 : (0 : ℝ) < M := by positivity
  rw [abs_le, le_div_iff₀ hM0, div_le_iff₀ hM0] at hl
  rw [TorusRC.positiveEvenVerticalTailRate, div_lt_iff₀ hM0] at ht
  unfold upperTailProbability at key
  linarith [hl.1]
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
  obtain ⟨-, -, -, hno, -⟩ := routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii hW21eq315 q hh319 hq μ hμ ξinv hRate
  obtain ⟨Ndom, hdom⟩ := hDominance
  obtain ⟨B, Sbethe, hSbethe, hratio⟩ := apply_17_at_critical_c q.val hq r (by omega)
  refine ⟨Sbethe, hSbethe, ?_⟩
  have hlog := (Real.continuousAt_log (Real.exp_pos _).ne').tendsto.comp hratio
  rw [Real.log_exp] at hlog
  suffices ∀ δ, 0 < δ → -(r : ℝ) * (Real.arcosh (Real.sqrt q.val / 2) + 2 * Sbethe) ≤ -((r - 1 : ℕ) : ℝ) * ξinv + δ by
    linarith [le_of_forall_pos_le_add this]
  intro δ hδ
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1 (upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate (r := r) (by omega) (δ / 2) (by linarith))
  obtain ⟨Nloop, hloop⟩ := upperLoop_eventually q μ hμ hno (ε := δ / 2) (by linarith)
  refine le_of_tendsto hlog (Filter.eventually_atTop.2 ⟨max r (max 1 (max nTail (max Nloop Ndom))), fun i hi => ?_⟩)
  have hperiod : TorusRC.positiveEvenPeriod (2 * (i + B) - 1) = 4 * (i + B) := by simp [TorusRC.positiveEvenPeriod]; omega
  simpa [hperiod] using sectorLogRate_le_of_eventual_tail hW12i hW12iii q hq (2 * (i + B) - 1) ξinv δ (by omega) (by omega)
    (by rw [hperiod]; exact hdom _ (by omega) (by omega)) (hnTail _ (by omega)) (hloop _ (by omega))

theorem firstSectorStrict_eventually
    (q : ℝ) (hq : 4 < q) :
    ∃ Nfirst : ℕ, ∀ N : ℕ, 4 ∣ N → Nfirst ≤ N →
      SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 1 <
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q)) N 0 := by
  obtain ⟨B, S, hS, hratio⟩ := apply_17_at_critical_c q hq 1 le_rfl
  obtain ⟨S₀, T, hS₀, -, hpositive, -⟩ := PottsDiscontinuity.identity44 _ (PottsDiscontinuity.arcosh_pos_of_gt4 q hq).1
  have := tendsto_nhds_unique hS hS₀
  obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.1 (hratio.eventually (Iio_mem_nhds (by rw [Real.exp_lt_one_iff]; push_cast; linarith)))
  refine ⟨4 * (i₀ + B), fun N ⟨k, hk⟩ hlarge => ?_⟩
  have := hi₀ (k - B) (by omega)
  rwa [show 4 * (k - B + B) = N by omega, div_lt_one (SixVertex.Lambda_pos (by positivity) (by omega))] at this

section
variable (hW12i : contract_cor313_i) (hW12ii : contract_cor313_ii) (hW12iii : contract_cor313_iii) (hW21eq315 : contract_eq315) (hW21eq316 : contract_eq316) (q : Set.Ici (1 : ℝ)) (hh319 : TorusRC.h319 q) (hq : 4 < q.val) (μ : MeasureTheory.Measure FK.LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit (FK.criticalParameters q).toP (FK.criticalParameters q).toQ 0 μ) (ξinv : ℝ) (hRate : Tendsto (fun n : ℕ => -Real.log (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite n))) / (n : ℝ)) atTop (𝓝 ξinv))
include hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq μ hμ ξinv hRate
/-- The repaired dominance gap: for all sufficiently large widths divisible by four,
the centered six-vertex block has the largest Perron root. -/
theorem rc_dominance_for_large_width
     :
    ∃ N₀ : ℕ, ∀ N : ℕ, 4 ∣ N → N₀ ≤ N →
      SixVertex.LambdaMax (Real.sqrt (2 + Real.sqrt q.val)) N =
        SixVertex.Lambda (Real.sqrt (2 + Real.sqrt q.val)) N 0 := by
  obtain ⟨S, hS, hxi, hno, -⟩ := routeB_free_nonpercolation_and_boundary_decay hW12i hW12ii hW21eq315 q hh319 hq μ hμ ξinv hRate
  obtain ⟨S₀, T, hS₀, -, hpositive, -⟩ := PottsDiscontinuity.identity44 _ (PottsDiscontinuity.arcosh_pos_of_gt4 q.val hq).1
  have hxiPos : 0 < ξinv := by linarith [tendsto_nhds_unique hS hS₀]
  obtain ⟨Nfirst, hfirstEvent⟩ := firstSectorStrict_eventually q.val hq
  obtain ⟨nTail, hnTail⟩ := Filter.eventually_atTop.1 (upperTailRateEventually_general hW21eq316 q μ hμ ξinv hRate one_le_two (ξinv / 4) (by positivity))
  obtain ⟨Nloop, hloop⟩ := upperLoop_eventually q μ hμ hno (ε := ξinv / 32) (by positivity)
  refine ⟨max 4 (max (4 * (max nTail Nloop + 1)) Nfirst), fun N ⟨k, hk⟩ hlarge => ?_⟩
  have hperiod : TorusRC.positiveEvenPeriod (2 * k - 1) = N := by simp [TorusRC.positiveEvenPeriod]; omega
  refine SixVertex.LambdaMax_eq_Lambda0_of_dominance (by positivity) ⟨2 * k, by omega⟩ (by omega) (half_pos hxiPos) (fun r hr2 hr => ?_) (hfirstEvent N ⟨k, hk⟩ (by omega))
  have := Real.exp_le_exp.mpr (hperiod ▸ upperDominanceGap_fixedIndex hW12i hW12iii q hq ξinv hxiPos (2 * k - 1) (hnTail _ (by omega)) (hloop _ (by omega)) (by omega) hr2)
  rwa [Real.exp_log (SixVertex.Lambda_pos (by positivity) hr), sub_eq_add_neg, Real.exp_add, Real.exp_log (SixVertex.LambdaMax_pos (by positivity)), mul_comm] at this

/-- The upper estimate for the inverse correlation length follows from the
fixed-sector bounds after the repaired dominant-eigenvalue identification. -/
theorem rc_xi_inverse_le_critical_rate
     :
    ∃ S : ℝ, Tendsto (PottsDiscontinuity.altTanhPartial
        (Real.arcosh (Real.sqrt q.val / 2))) atTop (𝓝 S) ∧
      ξinv ≤ Real.arcosh (Real.sqrt q.val / 2) + 2 * S := by
  obtain ⟨Ndom, hdom⟩ := rc_dominance_for_large_width hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq μ hμ ξinv hRate
  obtain ⟨_, S, hS, -⟩ := apply_17_at_critical_c q.val hq 1 le_rfl
  refine ⟨S, hS, not_lt.1 fun h => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ((Real.arcosh (Real.sqrt q.val / 2) + 2 * S) / (ξinv - (Real.arcosh (Real.sqrt q.val / 2) + 2 * S)))
  rw [div_lt_iff₀ (by linarith)] at hn
  obtain ⟨S', hS', h'⟩ := rc_upper_bound_fixed_r hW12i hW12ii hW12iii hW21eq315 hW21eq316 q hh319 hq ⟨Ndom, hdom⟩ μ hμ ξinv hRate (n + 2) (by omega)
  rw [tendsto_nhds_unique hS' hS] at h'
  push_cast at h'
  nlinarith
end

end PottsDiscontinuity.RCMProof

