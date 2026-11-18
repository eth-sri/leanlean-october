module

public import Mathlib
public import PottsDiscontinuity.AnalyticTools.Identity
public import PottsDiscontinuity.Bethe.Theorem23
public import PottsDiscontinuity.BetheAnsatz.ZeroRootTheorem
public import PottsDiscontinuity.SixVertex.Cor34BethePF
public import PottsDiscontinuity.SixVertex.Cor34FinalEquations

/-! # Endpoint and existence forms of Corollary 3.4 -/

@[expose] public section

open Filter Topology Set Matrix
open PottsDiscontinuity.PerronFrobenius
open scoped BigOperators

namespace PottsDiscontinuity.SixVertex

/-- The real Bethe eigenvalue `Λ(p)` in the two source formulas, selected by root parity. -/
noncomputable def cor34BetheLambda (N n : ℕ) (c : ℝ) (p : Fin n → ℝ) : ℝ := by
  classical
  exact if he : Even n then
    2 * ∏ j : Fin n, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖
  else
    let q : ℕ := n / 2 + 1
    let l : Fin n := ⟨q - 1, by
      obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp he; omega⟩
    (2 + c ^ 2 * ((N : ℝ) - 1) + c ^ 2 *
      ∑ j ∈ Finset.univ.erase l,
        deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0) *
      ∏ j ∈ Finset.univ.erase l, ‖BetheAnsatz.M c (BetheAnsatz.z (p j))‖

private theorem cor34_eventually_blockWave_ne_zero {N n : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hN : 0 < N) (hn : 2 * n ≤ N) :
    ∀ᶠ ε in 𝓝[<] (0 : ℝ), cor34_normalizedBlockWave (N := N) ε (p ε) ≠ 0 := by
  filter_upwards [(cor34_eventually_normalizedCoordinate_ne_zero hp hp0 hN hn).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with ε hsrc (hε : ε < 0) hwave
  apply hsrc
  have hpos : cor34_sourceEvenPositions = fun k => BetheAnsatz.positions (cor34_evenCoordinateState hn) k + 1 := by
    funext k; rw [cor34_evenCoordinateState_positions hn]; simp [cor34_sourceEvenPositions]; omega
  have hcoord : cor34_normalizedCoordinate ε (p ε) cor34_sourceEvenPositions =
      Complex.exp (Complex.I * ((∑ j, p ε j : ℝ) : ℂ)) *
        cor34_normalizedBlockWave (N := N) ε (p ε) (cor34_evenCoordinateState hn) := by
    change _ = _ * cor34_normalizedCoordinate ε (p ε) (BetheAnsatz.positions (cor34_evenCoordinateState hn))
    rw [cor34_normalizedCoordinate_eq_scaled_coordinateWave ε (p ε) _ hε.ne,
      cor34_normalizedCoordinate_eq_scaled_coordinateWave ε (p ε) _ hε.ne,
      hpos, BetheAnsatz.coordinateWave_add_one]; ring
  rw [hcoord, congrFun hwave (cor34_evenCoordinateState hn)]; simp

private theorem cor34_restrict_and_scale_eigen {N n : ℕ} {ε : ℝ} (hε : ε < 0)
    {p : Fin n → ℝ} {μ : ℂ}
    (hfull : (transferMatrix N (Real.sqrt (2 - 2 / ε))).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.betheVector (1 / ε) p = μ • BetheAnsatz.betheVector (1 / ε) p) :
    (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) *ᵥ cor34_normalizedBlockWave ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n * μ) • cor34_normalizedBlockWave ε p := by
  classical
  let c := Real.sqrt (2 - 2 / ε)
  have hblk : (transferBlock N c n).map (algebraMap ℝ ℂ) *ᵥ BetheAnsatz.blockWave (1 / ε) p =
      μ • BetheAnsatz.blockWave (1 / ε) p := by
    ext x
    have hx := congrFun hfull x.1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hx
    rw [← Fintype.sum_subtype_add_sum_subtype (fun y : Finset (Fin N) => y.card = n),
      Finset.sum_eq_zero (fun (y : {y : Finset (Fin N) // y.card ≠ n}) _ => by
        rw [BetheAnsatz.betheVector_eq_zero (1 / ε) p y.2, mul_zero]), add_zero,
      Finset.sum_congr rfl (g := fun (y : State N n) =>
        ((transferBlock N c n).map (algebraMap ℝ ℂ)) x y * BetheAnsatz.blockWave (1 / ε) p y)
        (fun y _ => by simp [c, transferBlock, BetheAnsatz.betheVector])] at hx
    simpa [c, transferBlock, BetheAnsatz.betheVector, BetheAnsatz.extendByZero, BetheAnsatz.blockWave,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, State, x.2] using hx
  have hM : (cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ) =
      ((-ε / 2 : ℝ) : ℂ) ^ n • (transferBlock N c n).map (algebraMap ℝ ℂ) := by
    rw [cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε,
      ← inv_pow, show (-2 / ε : ℝ)⁻¹ = -ε / 2 by field_simp [hε.ne]]
    ext x y; simp [c, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  have hW : cor34_normalizedBlockWave (N := N) ε p =
      ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n • BetheAnsatz.blockWave (N := N) (1 / ε) p := by
    funext x; exact cor34_normalizedCoordinate_eq_scaled_coordinateWave ε p (BetheAnsatz.positions x) hε.ne
  rw [hM, hW]; ext i
  have hi := congrFun hblk i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
  change (∑ j, (algebraMap ℝ ℂ) (transferBlock N c n i j) * BetheAnsatz.blockWave (1 / ε) p j) =
    μ * BetheAnsatz.blockWave (1 / ε) p i at hi
  calc (∑ j, ((-ε / 2 : ℝ) : ℂ) ^ n * (algebraMap ℝ ℂ) (transferBlock N c n i j) *
          (((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n * BetheAnsatz.blockWave (1 / ε) p j))
      = ((-ε / 2 : ℝ) : ℂ) ^ n * ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n *
          ∑ j, (algebraMap ℝ ℂ) (transferBlock N c n i j) * BetheAnsatz.blockWave (1 / ε) p j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [hi]; ring

private theorem cor34_exists_cutoff {n : ℕ} {d₀ d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₀ : d₀ < d₁) (hpAnalytic : AnalyticOnNhd ℝ p (Iio d₁))
    (hp : ∀ d ≤ d₀, p d ∈ Bethe.S_n n) (S : Finset (Fin n))
    (hphys : ∀ d ≤ d₀, ∀ j, j ∈ S ∨ p d j ≠ 0) :
    ∃ d₂, d₀ < d₂ ∧ d₂ < d₁ ∧ ∀ d < d₂, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (j ∈ S ∨ p d j ≠ 0) := by
  have hpCont : ContinuousAt p d₀ := (hpAnalytic d₀ hd₀).continuousAt
  have hnear : ∀ᶠ d in 𝓝 d₀, ∀ j, p d j ∈ Ioo (-Real.pi) Real.pi ∧ (j ∈ S ∨ p d j ≠ 0) := by
    refine Filter.eventually_all.2 fun j => ?_
    have hc : ContinuousAt (fun d => p d j) d₀ := (continuous_apply j).continuousAt.comp hpCont
    refine (hc.eventually (isOpen_Ioo.mem_nhds ((hp d₀ le_rfl).1 j))).and ?_
    rcases hphys d₀ le_rfl j with hjS | hj0
    · exact Filter.Eventually.of_forall fun _ => Or.inl hjS
    · exact (hc.eventually_ne hj0).mono fun _ => Or.inr
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨min ((d₀ + d₁) / 2) (d₀ + δ / 2), lt_min (by linarith) (by linarith),
    lt_of_le_of_lt (min_le_left _ _) (by linarith), fun d hd j => ?_⟩
  by_cases hle : d ≤ d₀
  · exact ⟨(hp d hle).1 j, hphys d hle j⟩
  · exact hball (Metric.mem_ball.mpr (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      linarith [lt_of_lt_of_le hd (min_le_right _ _)])) j

private theorem cor34_analyticAt_ofReal {f : ℝ → ℝ} {d : ℝ} (hf : AnalyticAt ℝ f d) :
    AnalyticAt ℝ (fun t => (f t : ℂ)) d :=
  (Complex.ofRealCLM.analyticAt (f d)).comp hf

private theorem cor34_analyticAt_coord {n : ℕ} {p : ℝ → Fin n → ℝ} {d d₁ : ℝ}
    (hp : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁) (j : Fin n) :
    AnalyticAt ℝ (fun t => p t j) d := by
  convert ((ContinuousLinearMap.proj (R := ℝ) j).analyticAt (p d)).comp (hp d hd) using 1; rfl

private theorem cor34_analyticAt_z_and_M {n : ℕ} {d d₁ : ℝ} {p : ℝ → Fin n → ℝ}
    (hd₁ : d₁ < -1) (hp : AnalyticOnNhd ℝ p (Iio d₁)) (hd : d < d₁) {j : Fin n}
    (hrange : p d j ∈ Ioo (-Real.pi) Real.pi) (hne : p d j ≠ 0) :
    AnalyticAt ℝ (fun t => cor34_normalizedL (1 / t) (p t j)) d ∧
      AnalyticAt ℝ (fun t => cor34_normalizedM (1 / t) (p t j)) d := by
  have hd0 : d ≠ 0 := (lt_trans hd (lt_trans hd₁ (by norm_num))).ne
  have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d := analyticAt_const.div analyticAt_id hd0
  have hhalfC := cor34_analyticAt_ofReal (by fun_prop : AnalyticAt ℝ (fun t : ℝ => -(1 / t) / 2) d)
  have hcoefC := cor34_analyticAt_ofReal ((analyticAt_const (v := (1 : ℝ))).sub heps)
  have hpjC := cor34_analyticAt_ofReal (cor34_analyticAt_coord hp hd j)
  have hZ : AnalyticAt ℝ (fun t => BetheAnsatz.z (p t j)) d :=
    analyticAt_cexp.restrictScalars.comp ((analyticAt_const (v := Complex.I)).mul hpjC)
  have hden : AnalyticAt ℝ (fun t => 1 - BetheAnsatz.z (p t j)) d := analyticAt_const.sub hZ
  have hden0 : 1 - BetheAnsatz.z (p d j) ≠ 0 := sub_ne_zero.mpr (BetheAnsatz.z_ne_one hrange hne).symm
  refine ⟨?_, ?_⟩
  · convert hhalfC.add ((hcoefC.mul hZ).div hden hden0) using 1
    ext t; simp [cor34_normalizedL, div_eq_mul_inv]
  · convert hhalfC.sub (hcoefC.div hden hden0) using 1
    ext t; simp [cor34_normalizedM]

private theorem cor34_pfRoot_eq_re_at_d0 {N n : ℕ} {d₀ d₂ d₁ : ℝ}
    (hd₀ : d₀ < -1) (hd₀₂ : d₀ < d₂) (hd₂₁ : d₂ < d₁) (hd₁ : d₁ < -1) (hbound : 2 * n ≤ N)
    {μ_norm : ℝ → ℂ} (hAn : AnalyticOnNhd ℝ μ_norm (Iio d₂))
    {μ_phys : ℝ → ℂ}
    (hscale : ∀ d < d₁, ((-2 * d : ℝ) : ℂ) ^ n * μ_norm d = μ_phys d)
    (hev : ∀ᶠ ε in 𝓝[<] (0 : ℝ), μ_phys (1 / ε) = (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ)) :
    pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n) = (μ_phys d₀).re := by
  let f : ℝ → ℝ := fun d => pfRoot (transferBlock N (Real.sqrt (2 - 2 * d)) n)
  let g : ℝ → ℝ := fun d => (((-2 * d : ℝ) : ℂ) ^ n * μ_norm d).re
  have hf : AnalyticOnNhd ℝ f (Iio d₂) := fun d hd =>
    cor34_analyticAt_pfRoot_transferBlock (by omega : n ≤ N) (lt_trans (lt_trans hd hd₂₁) hd₁)
  have hg : AnalyticOnNhd ℝ g (Iio d₂) := fun d hd => by
    have hs := (cor34_analyticAt_ofReal (by fun_prop : AnalyticAt ℝ (fun t : ℝ => -2 * t) d)).pow n
    exact (Complex.reCLM.analyticAt _).comp (hs.mul (hAn d hd))
  have hinv : Tendsto (fun d : ℝ => 1 / d) atBot (𝓝[<] (0 : ℝ)) := by
    simpa only [one_div] using tendsto_inv_atBot_nhdsLT_zero
  obtain ⟨b, hb⟩ := Filter.eventually_atBot.mp (hinv.eventually hev)
  let dTail := min d₀ b
  have hEqV : EqOn f g (Iio dTail) := fun d hd => by
    have hd₀' : d < d₀ := lt_of_lt_of_le hd (min_le_left _ _)
    have hdneg : d < 0 := lt_trans hd₀' (lt_trans hd₀ (by norm_num))
    have hraw := hb d (lt_of_lt_of_le hd (min_le_right _ _)).le
    rw [show 1 / (1 / d) = d by field_simp [hdneg.ne], show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hraw
    rw [← hscale d (lt_trans hd₀' (lt_trans hd₀₂ hd₂₁))] at hraw
    simpa [f, g] using (congrArg Complex.re hraw).symm
  have hiden := AnalyticTools.analytic_eqOn_of_eqOn_open_preconnected hf hg
    isPreconnected_Iio isOpen_Iio nonempty_Iio
    (fun d hd => lt_trans (lt_of_lt_of_le hd (min_le_left _ _)) hd₀₂) hEqV hd₀₂
  rw [← hscale d₀ (lt_trans hd₀₂ hd₂₁)]; exact hiden

/-- Theorem 2.3 supplies a density-controlled Bethe state at `Δ₀`; Corollary 3.4 identifies its
real Bethe eigenvalue with the `r`-sector Perron root for every sufficiently large even `N`. -/
theorem cor34_final_exists_family_at_endpoint (r : ℕ) {d₀ : ℝ} (hd₀ : d₀ < -1) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → Even N →
      let n := N / 2 - r
      ∃ hn : 0 < n, ∃ hs : 2 * n ≤ N, ∃ p : Fin n → ℝ,
        ∃ hp : p ∈ Bethe.S_n n,
        Bethe.DiscreteBetheEquation d₀ N n p ∧
        Bethe.densityNorm d₀ hd₀
          (fun x => Bethe.rootStepDensity N n p hp hn hs x - Bethe.rho d₀ x)
          (Bethe.rootStepDensity_error_bddAbove hd₀ _ hp hn hs) ≤ K / N ∧
        cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p =
          Lambda (Real.sqrt (2 - 2 * d₀)) N r := by
  obtain ⟨K, hK, N₀, hN₀, d₁, hd₀₁, hd₁, hfamily⟩ := Bethe.theorem23 r hd₀
  refine ⟨K, hK, N₀, hN₀, fun N hlarge hEvenN => ?_⟩
  let n : ℕ := N / 2 - r
  obtain ⟨hn, hs, p, hp, hBE, hpAnalytic, ⟨P, hPanalytic, hP0, hformula⟩, hDensity⟩ := hfamily N hlarge hEvenN
  let p₀ := p d₀
  have hp₀ : p₀ ∈ Bethe.S_n n := hp d₀ le_rfl
  have hNpos : 0 < N := by omega
  have hNform : N = 2 * (n + r) := by obtain ⟨m, rfl⟩ := hEvenN; dsimp [n]; omega
  have hc₀ : 2 < Real.sqrt (2 - 2 * d₀) := by rw [Real.lt_sqrt (by norm_num)]; nlinarith [hd₀]
  have hPcont : ContinuousAt P 0 := hPanalytic.continuousAt
  have hInv_d0 : ∀ᶠ ε in 𝓝[<] (0 : ℝ), 1 / ε ≤ d₀ := by
    simpa only [one_div] using tendsto_inv_nhdsLT_zero.eventually (Iic_mem_atBot d₀)
  have hw_ne := cor34_eventually_blockWave_ne_zero (N := N) hPcont hP0 hNpos hs
  have hc_eps {ε : ℝ} (hε : ε < 0) (hΔ : 1 / ε ≤ d₀) :
      2 < Real.sqrt (2 - 2 / ε) ∧ BetheAnsatz.anisotropy (Real.sqrt (2 - 2 / ε)) = 1 / ε := by
    have hrec : 2 / ε < 0 := div_neg_of_pos_of_neg two_pos hε
    have hsq : (Real.sqrt (2 - 2 / ε)) ^ 2 = 2 - 2 / ε := Real.sq_sqrt (by linarith)
    refine ⟨by rw [Real.lt_sqrt (by norm_num)]; linarith [show 2 / ε = 2 * (1 / ε) by ring], ?_⟩
    unfold BetheAnsatz.anisotropy; rw [hsq]; ring
  have hscale_inv {d : ℝ} (hd : d < d₁) {a b : ℂ} (h : a = ((-(1 / d) / 2 : ℝ) : ℂ) ^ n * b) :
      ((-2 * d : ℝ) : ℂ) ^ n * a = b := by
    have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
    rw [h, ← mul_assoc, ← mul_pow, show ((-2 * d : ℝ) : ℂ) * ((-(1 / d) / 2 : ℝ) : ℂ) = 1 by
      exact_mod_cast (by field_simp [hdneg.ne] : (-2 * d) * (-(1 / d) / 2) = 1), one_pow, one_mul]
  refine ⟨hn, hs, p₀, hp₀, hBE d₀ le_rfl, by simpa [p₀] using hDensity d₀ le_rfl, ?_⟩
  change cor34BetheLambda N n (Real.sqrt (2 - 2 * d₀)) p₀ = pfRoot (transferBlock N (Real.sqrt (2 - 2 * d₀)) n)
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · obtain ⟨d₂, hd₀₂, hd₂₁, hcut⟩ := cor34_exists_cutoff hd₀₁ hpAnalytic hp ∅
      (fun d hle j => Or.inr (cor34_even_S_n_roots_nonzero (hp d hle) hnEven j))
    have hAn : AnalyticOnNhd ℝ (fun t => cor34_normalizedRegularEigenvalue (1 / t) (p t)) (Iio d₂) := fun d hd => by
      have hLM (j : Fin n) := cor34_analyticAt_z_and_M hd₁ hpAnalytic (lt_trans hd hd₂₁) (hcut d hd j).1
        ((hcut d hd j).2.resolve_left (Finset.notMem_empty j))
      exact (Finset.univ.analyticAt_fun_prod fun j _ => (hLM j).1).add
        (Finset.univ.analyticAt_fun_prod fun j _ => (hLM j).2)
    have hev : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) (P ε) =
          (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
      refine cor34_even_bethe_branch_eventually_physical_pfRoot hPcont hP0 hNpos hs hn hnEven hNform (Nat.zero_le r) ?_
      filter_upwards [hw_ne, hInv_d0, self_mem_nhdsWithin] with ε hw hΔ (hε : ε < 0)
      obtain ⟨hc, hAni⟩ := hc_eps hε hΔ
      have hrec : 1 / (1 / ε) = ε := by field_simp [hε.ne]
      have hS : P ε ∈ Bethe.S_n n := by rw [← hrec, ← hformula (1 / ε) hΔ]; exact hp (1 / ε) hΔ
      have hBEε : Bethe.DiscreteBetheEquation (1 / ε) N n (P ε) := by
        have h := hBE (1 / ε) hΔ; rwa [hformula (1 / ε) hΔ, hrec] at h
      have hBA : BetheAnsatz.BetheEquations N (BetheAnsatz.anisotropy (Real.sqrt (2 - 2 / ε))) (P ε) := by
        rw [hAni]; exact cor34_discreteBetheEquation_to_betheEquations _ hBEε
      rcases BetheAnsatz.betheAnsatz_all hc (P ε) (fun j => hS.1 j) (cor34_S_n_injective hS) hBA with
        ⟨_, hfull⟩ | ⟨l, hl, _⟩
      · rw [hAni] at hfull
        rw [cor34_normalizedRegularEigenvalue_scale hε (P ε)]
        exact ⟨hw, cor34_restrict_and_scale_eigen hε hfull⟩
      · exact (cor34_even_S_n_roots_nonzero hS hnEven l hl).elim
    have hpf := cor34_pfRoot_eq_re_at_d0 hd₀ hd₀₂ hd₂₁ hd₁ hs hAn
      (μ_phys := fun d => BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 * d)) (p d))
      (fun d hd => by
        have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
        have hsc := cor34_normalizedRegularEigenvalue_scale (one_div_neg.mpr hdneg) (p d)
        rw [show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hsc
        exact hscale_inv hd hsc)
      (by filter_upwards [hev, hInv_d0, self_mem_nhdsWithin] with ε he hΔ (hε : ε < 0)
          rw [hformula (1 / ε) hΔ, show 1 / (1 / ε) = ε by field_simp [hε.ne], show 2 * (1 / ε) = 2 / ε by ring]
          exact he)
    rw [hpf]
    have hrat := congrArg Complex.re (Bethe.ratio_eigenvalueRegular hc₀ hp₀)
    have hprod : (∏ j : Fin n, ((‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀)) (BetheAnsatz.z (p₀ j))‖ : ℝ) : ℂ)).re =
        ∏ j : Fin n, ‖BetheAnsatz.M (Real.sqrt (2 - 2 * d₀)) (BetheAnsatz.z (p₀ j))‖ := by norm_cast
    simp only [cor34BetheLambda, hnEven, ↓reduceDIte]
    simpa [hprod, p₀] using hrat.symm
  · let q : ℕ := n / 2 + 1
    have hnotEven : ¬ Even n := Nat.not_even_iff_odd.mpr hnOdd
    have hnq : n + 1 = 2 * q := by obtain ⟨k, hk⟩ := hnOdd; dsimp [q]; omega
    let l : Fin n := ⟨q - 1, by omega⟩
    obtain ⟨d₂, hd₀₂, hd₂₁, hcut⟩ := cor34_exists_cutoff hd₀₁ hpAnalytic hp {l} (fun d hle j => by
      by_cases hj : j = l
      · exact Or.inl (hj ▸ Finset.mem_singleton_self l)
      · exact Or.inr fun hz => hj ((cor34_S_n_injective (hp d hle))
          (hz.trans (cor34_odd_S_n_center_zero (hp d hle) hnq).symm)))
    have hAn : AnalyticOnNhd ℝ (fun t => cor34_normalizedZeroEigenvalue (N := N) (1 / t) (p t) l) (Iio d₂) := fun d hd => by
      have hd₁' := lt_trans hd hd₂₁
      have hd0 : d ≠ 0 := (lt_trans hd₁' (lt_trans hd₁ (by norm_num))).ne
      have heps : AnalyticAt ℝ (fun t : ℝ => 1 / t) d := analyticAt_const.div analyticAt_id hd0
      have hcorr (j : Fin n) : AnalyticAt ℝ (fun t => cor34_derivativeCorrection (1 / t) (p t j)) d := by
        have hpj := cor34_analyticAt_coord hpAnalytic hd₁' j
        have hcos : AnalyticAt ℝ (fun t => Real.cos (p t j)) d := Real.analyticAt_cos.comp hpj
        have hsin : AnalyticAt ℝ (fun t => Real.sin (p t j)) d := Real.analyticAt_sin.comp hpj
        have hnum : AnalyticAt ℝ (fun t : ℝ => 2 * (1 / t) * ((1 / t) * (1 + Real.cos (p t j)) - 2)) d :=
          ((analyticAt_const.mul heps).mul ((heps.mul (analyticAt_const.add hcos)).sub analyticAt_const))
        have hden : AnalyticAt ℝ (fun t : ℝ => ((1 / t) * (1 + Real.cos (p t j)) - 2) ^ 2 +
            (1 / t) ^ 2 * (Real.sin (p t j)) ^ 2) d :=
          (((heps.mul (analyticAt_const.add hcos)).sub analyticAt_const).pow 2).add ((heps.pow 2).mul (hsin.pow 2))
        have harg : (1 / d) * (1 + Real.cos (p d j)) - 2 < 0 := by
          have h1 : 1 / d < 0 := one_div_neg.mpr (lt_trans hd₁' (lt_trans hd₁ (by norm_num)))
          nlinarith [Real.neg_one_le_cos (p d j), mul_nonpos_of_nonpos_of_nonneg h1.le (by linarith [Real.neg_one_le_cos (p d j)] : 0 ≤ 1 + Real.cos (p d j))]
        have hden0 : ((1 / d) * (1 + Real.cos (p d j)) - 2) ^ 2 + (1 / d) ^ 2 * (Real.sin (p d j)) ^ 2 ≠ 0 :=
          (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero harg.ne) (by positivity)).ne'
        exact hnum.div hden hden0
      have hsumC := cor34_analyticAt_ofReal ((analyticAt_const (v := (N : ℝ) - 1)).add
        ((Finset.univ.erase l).analyticAt_fun_sum fun j _ => (analyticAt_const (v := (-1 : ℝ))).add (hcorr j)))
      have hpre := (cor34_analyticAt_ofReal heps.neg).add
        ((cor34_analyticAt_ofReal ((analyticAt_const (v := (1 : ℝ))).sub heps)).mul hsumC)
      have hprodM := (Finset.univ.erase l).analyticAt_fun_prod fun j hj => by
        have hjne : p d j ≠ 0 := ((hcut d hd j).2).resolve_left
          (Finset.mem_singleton.not.mpr (Finset.mem_erase.mp hj).1)
        exact (cor34_analyticAt_z_and_M hd₁ hpAnalytic hd₁' (hcut d hd j).1 hjne).2
      convert hpre.mul hprodM using 1
      ext t; simp only [cor34_normalizedZeroEigenvalue, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply]
      push_cast; ring
    have hev : ∀ᶠ ε in 𝓝[<] (0 : ℝ),
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) (P ε) l =
          (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
      refine cor34_odd_bethe_branch_eventually_physical_pfRoot hPcont hP0 hNpos hs hn hnq hNform (Nat.zero_le r) ?_
      filter_upwards [hw_ne, hInv_d0, self_mem_nhdsWithin] with ε hw hΔ (hε : ε < 0)
      obtain ⟨hc, hAni⟩ := hc_eps hε hΔ
      have hrec : 1 / (1 / ε) = ε := by field_simp [hε.ne]
      have hS : P ε ∈ Bethe.S_n n := by rw [← hrec, ← hformula (1 / ε) hΔ]; exact hp (1 / ε) hΔ
      have hBEε : Bethe.DiscreteBetheEquation (1 / ε) N n (P ε) := by
        have h := hBE (1 / ε) hΔ; rwa [hformula (1 / ε) hΔ, hrec] at h
      have hBA : BetheAnsatz.BetheEquations N (BetheAnsatz.anisotropy (Real.sqrt (2 - 2 / ε))) (P ε) := by
        rw [hAni]; exact cor34_discreteBetheEquation_to_betheEquations _ hBEε
      have hcen : P ε l = 0 := cor34_odd_S_n_center_zero hS hnq
      rcases BetheAnsatz.betheAnsatz_all hc (P ε) (fun j => hS.1 j) (cor34_S_n_injective hS) hBA with
        ⟨hnez, _⟩ | ⟨l', hl', hfull⟩
      · exact (hnez l hcen).elim
      · have hll : l' = l := (cor34_S_n_injective hS) (hl'.trans hcen.symm)
        subst hll; rw [hAni] at hfull
        rw [cor34_normalizedZeroEigenvalue_scale l (lt_of_le_of_lt hΔ hd₀) hε (P ε)]
        exact ⟨hw, cor34_restrict_and_scale_eigen hε hfull⟩
    have hpf := cor34_pfRoot_eq_re_at_d0 hd₀ hd₀₂ hd₂₁ hd₁ hs hAn
      (μ_phys := fun d => BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 * d)) (p d) l)
      (fun d hd => by
        have hdneg : d < 0 := lt_trans hd (lt_trans hd₁ (by norm_num))
        have hInv : 1 / (1 / d) < -1 := by rw [one_div_one_div]; exact lt_trans hd hd₁
        have hsc := cor34_normalizedZeroEigenvalue_scale (N := N) l hInv (one_div_neg.mpr hdneg) (p d)
        rw [show 2 / (1 / d) = 2 * d by field_simp [hdneg.ne]] at hsc
        exact hscale_inv hd hsc)
      (by filter_upwards [hev, hInv_d0, self_mem_nhdsWithin] with ε he hΔ (hε : ε < 0)
          rw [hformula (1 / ε) hΔ, show 1 / (1 / ε) = ε by field_simp [hε.ne], show 2 * (1 / ε) = 2 / ε by ring]
          exact he)
    rw [hpf]
    have hrat := congrArg Complex.re (Bethe.ratio_eigenvalueZero (N := N) (n := n) hc₀ hp₀ l
      (cor34_odd_S_n_center_zero hp₀ hnq))
    simp only [Complex.ofReal_re] at hrat
    rw [hrat]; simp [cor34BetheLambda, hnotEven, q, l, p₀]

end PottsDiscontinuity.SixVertex
