module

public import PottsDiscontinuity.SixVertex.Cor34BasePositivity
public import PottsDiscontinuity.SixVertex.Cor34Spectral
public import PottsDiscontinuity.SixVertex.Cor34FinalEigen

/-! A positive limiting Bethe wave identifies the Perron branch without computing the
spectrum (or proving simplicity) of the infinite-anisotropy transfer matrix. -/

@[expose] public section

open Filter Topology Matrix Finset Complex
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- A wave positive on the limiting matrix's support has nonzero overlap with a
positive Perron vector for all sufficiently small perturbations. -/
private theorem eventually_perronBranch {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {W : ℝ → ι → ℂ} {μ : ℝ → ℂ} {R : ℝ → ℝ}
    (hA : ContinuousAt A 0) (hsym : ∀ t, (A t).IsSymm)
    (hW : ∀ j, ContinuousAt (fun t => W t j) 0) (hR : ContinuousAt R 0)
    (hR0 : 0 < R 0) (hnonneg : ∀ i j, 0 ≤ A 0 i j)
    (hW0 : ∀ j, 0 ≤ (W 0 j).re)
    (hsupp : ∀ i j, A 0 i j ≠ 0 → 0 < (W 0 j).re)
    (hPF : ∀ᶠ t in 𝓝[<] 0, ∃ v : ι → ℝ, (∀ j, 0 < v j) ∧ A t *ᵥ v = R t • v)
    (hEig : ∀ᶠ t in 𝓝[<] 0, (A t).map (algebraMap ℝ ℂ) *ᵥ W t = μ t • W t) :
    ∀ᶠ t in 𝓝[<] 0, μ t = (R t : ℂ) := by
  let B (t : ℝ) (j : ι) := ∑ i, A t i j
  let q (t : ℝ) (j : ι) := (W t j).re
  let K := 1 + ∑ j, B 0 j / q 0 j
  have hnon (j : ι) : 0 ≤ B 0 j / q 0 j := div_nonneg (sum_nonneg fun i _ => hnonneg i j) (hW0 j)
  have hK : 0 < K := by have := sum_nonneg (s := univ) (fun j _ => hnon j); linarith
  have hbound (j : ι) : B 0 j ≤ K * q 0 j := by
    by_cases h : B 0 j = 0
    · rw [h]; exact mul_nonneg hK.le (hW0 j)
    have hj : 0 < q 0 j := by
      by_contra! hh
      exact h (sum_eq_zero fun i _ => by by_contra hn; exact (not_lt_of_ge hh) (hsupp i j hn))
    rw [← div_le_iff₀ hj]
    exact (single_le_sum (fun i _ => hnon i) (mem_univ j)).trans (by linarith)
  have hB (j : ι) : ContinuousAt (fun t => B t j) 0 := by
    apply tendsto_finsetSum _ fun i _ => ?_
    exact ((continuous_apply j).continuousAt.comp ((continuous_apply i).continuousAt.comp hA))
  have hvic : ∀ᶠ t in 𝓝 0, ∀ j, B t j < K * q t j + R t := eventually_all.mpr fun j =>
    (hB j).eventually_lt ((continuousAt_const.mul (continuous_re.continuousAt.comp (hW j))).add hR)
      (lt_add_of_le_of_pos (hbound j) hR0)
  filter_upwards [hvic.filter_mono nhdsWithin_le_nhds, hPF, hEig] with t ht ⟨v, hvpos, hv⟩ he
  have hvsum : ∑ j, B t j * v j = R t * ∑ j, v j := by
    have h := dotProduct_mulVec (fun _ : ι => (1 : ℝ)) (A t) v
    rw [hv] at h
    simpa [dotProduct, vecMul, Finset.mul_sum] using h.symm
  have hsum := sum_lt_sum_of_nonempty (univ_nonempty (α := ι)) fun j _ =>
    mul_lt_mul_of_pos_right (ht j) (hvpos j)
  simp only [add_mul, mul_assoc, sum_add_distrib, ← Finset.mul_sum, hvsum] at hsum
  have hdot : 0 < ∑ j, q t j * v j := by
    exact pos_of_mul_pos_right (by linarith only [hsum]) hK.le
  let vC : ι → ℂ := fun j => v j
  let AC := (A t).map (algebraMap ℝ ℂ)
  have hvC : AC *ᵥ vC = (R t : ℂ) • vC := by
    funext j
    change ((A t).map (algebraMap ℝ ℂ) *ᵥ ((algebraMap ℝ ℂ) ∘ v)) j = _
    rw [← RingHom.map_mulVec (algebraMap ℝ ℂ) _ v j, hv]
    simp [vC]
  have hAC : ACᵀ = AC := by
    ext i j
    exact congrArg (algebraMap ℝ ℂ) ((hsym t).apply i j)
  have hne : vC ⬝ᵥ W t ≠ 0 := by
    intro hz
    have hz' : ∑ j, q t j * v j = 0 := by
      simpa [vC, dotProduct, mul_comm] using congrArg Complex.re hz
    linarith only [hdot, hz']
  have h := dotProduct_transpose_mulVec (A := AC) vC (W t)
  rw [hAC, he, hvC, dotProduct_smul, dotProduct_smul, dotProduct_comm (W t) vC] at h
  exact mul_right_cancel₀ hne h

private theorem staggered_inf_positive {N n : ℕ} (hn : 0 < n) (hN : 2 * n ≤ N) :
    ∃ x y, 0 < infinityBlock N n x y := by
  classical
  let x := cor34_evenCoordinateState hN
  let y : State N n := ⟨x.1.map (finRotate N).symm.toEmbedding, by simpa using x.2⟩
  refine ⟨y, x, ?_⟩
  have hy (i : Fin N) : i ∈ y.1 ↔ nxt i ∈ x.1 := mem_map_equiv
  have hd : Disjoint y.1 x.1 := by
    refine disjoint_left.mpr fun i hi hj => ?_
    have hi' := (hy i).mp hi
    rcases mem_image.mp (show i ∈ univ.image _ from hj) with ⟨k, _, hk⟩
    rcases mem_image.mp (show nxt i ∈ univ.image _ from hi') with ⟨l, _, hl⟩
    have hix : i.val = 2 * k.val + 1 := congrArg Fin.val hk.symm
    have hnx : (nxt i).val = 2 * l.val + 1 := congrArg Fin.val hl.symm
    rw [nxt_val_mod] at hnx
    by_cases h : i.val + 1 = N
    · rw [h, Nat.mod_self] at hnx; omega
    · rw [Nat.mod_eq_of_lt (by omega)] at hnx
      omega
  have hprv (i : Fin N) : nxt (prv i) = i := (finRotate N).apply_symm_apply i
  have hf : Flux y.1 x.1 (fun i => decide (i ∈ y.1)) := by
    intro i
    have hh := hy (prv i)
    rw [hprv] at hh
    simp only [hh]
    ring
  have hi : Interlaced y.1 x.1 := by
    cases N with
    | zero => omega
    | succ k =>
      have h := validS_of_flux hf
      apply (interlaced_iff_validS _ _).mpr
      grind
  rw [(infinityBlock_eq_one_iff hn _ _).mpr ⟨hi, hd⟩]
  norm_num

/-- Near infinite anisotropy the Bethe scalar is the Perron root. -/
theorem cor34_eventually_perron {N n : ℕ} {P : ℝ → Fin n → ℝ}
    (hn : 0 < n) (hN : 2 * n ≤ N)
    (hP : ContinuousAt P 0) (hP0 : P 0 = Bethe.discreteBaseSolution N n)
    {μ : ℝ → ℂ}
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      (transferBlock N (Real.sqrt (2 - 2 / ε)) n).map (algebraMap ℝ ℂ) *ᵥ
        BetheAnsatz.blockWave (1 / ε) (P ε) = μ ε • BetheAnsatz.blockWave (1 / ε) (P ε)) :
    ∀ᶠ ε in 𝓝[<] 0, μ ε = (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  classical
  let A := cor34_normalizedTransferBlock N n
  let R := fun ε => pfRoot (A ε)
  let W (ε : ℝ) (x : State N n) := (((2 * I : ℂ) ^ cor34_pairCount n)⁻¹) *
    cor34_normalizedCoordinate ε (P ε) (BetheAnsatz.positions x)
  let s (ε : ℝ) : ℝ := ((-2 / ε) ^ n)⁻¹
  have hA0 : A 0 = infinityBlock N n := cor34_normalizedTransferBlock_zero N n
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  have hH (ε : ℝ) : (A ε).IsHermitian := cor34_normalizedTransferBlock_isHermitian ε
  have hA' (i j : State N n) : AnalyticAt ℝ (fun ε => A ε i j) 0 :=
    cor34_normalizedTransferBlock_entry_analyticAt i j 0
  have hA : ContinuousAt A 0 := continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j =>
    (hA' i j).continuousAt
  have hR : ContinuousAt R 0 := AnalyticTools.continuousAt_pfRoot_of_hermitian hA (hH 0) (.of_forall hH)
  have hR0 : 0 < R 0 := by
    dsimp [R]; rw [hA0]
    exact pfRoot_pos infinityBlock_isHermitian infinityBlock_nonneg (staggered_inf_positive hn hN)
  have hW (x : State N n) : ContinuousAt (fun ε => W ε x) 0 :=
    continuousAt_const.mul (cor34_normalizedCoordinate_tendsto hP _)
  have hpos (x : State N n) : 0 ≤ (W 0 x).re ∧ (NoConsecutiveUp x.1 → 0 < (W 0 x).re) := by
    dsimp [W]; rw [hP0]
    exact cor34_base_phase (by omega) x
  have hscale {ε : ℝ} (hε : ε < 0) :
      R ε = s ε * pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) := by
    rw [show R ε = pfRoot (A ε) by rfl, cor34_pfRoot_normalizedTransferBlock_eq (by omega) hε]
    simp [s, div_eq_mul_inv, mul_comm]
  have hPF : ∀ᶠ ε in 𝓝[<] 0, ∃ v : State N n → ℝ, (∀ j, 0 < v j) ∧ A ε *ᵥ v = R ε • v := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : ε < 0)
    obtain ⟨v, hvpos, hv⟩ := (transferBlock_perronFrobenius (Real.sqrt_pos.2
      (show 0 < 2 - 2 / ε by have := div_neg_of_pos_of_neg (by norm_num : 0 < (2 : ℝ)) hε; linarith)) (show n ≤ N by omega)).2.1
    refine ⟨v, hvpos, ?_⟩
    rw [show A ε = _ from cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε,
      smul_mulVec, hv, hscale hε, smul_smul]
  have hEig' : ∀ᶠ ε in 𝓝[<] 0,
      (A ε).map (algebraMap ℝ ℂ) *ᵥ W ε = ((s ε : ℂ) * μ ε) • W ε := by
    filter_upwards [hEig, self_mem_nhdsWithin] with ε he (hε : ε < 0)
    let a : ℂ := (((2 * I : ℂ) ^ cor34_pairCount n)⁻¹) * ((-ε / 2 : ℝ) : ℂ) ^ cor34_pairCount n
    have hw : W ε = a • BetheAnsatz.blockWave (N := N) (1 / ε) (P ε) := by
      funext x
      simp [W, a, BetheAnsatz.blockWave, cor34_normalizedCoordinate_eq_scaled_coordinateWave ε (P ε) _ hε.ne, mul_assoc]
    have hmat : (A ε).map (algebraMap ℝ ℂ) = (s ε : ℂ) •
        (transferBlock N (Real.sqrt (2 - 2 / ε)) n).map (algebraMap ℝ ℂ) := by
      rw [show A ε = _ from cor34_normalizedTransferBlock_eq_scaled_transferBlock ε hε]
      ext i j
      simp [s]
    rw [hw, hmat, mulVec_smul, smul_mulVec, he, smul_comm a (s ε : ℂ),
      smul_comm a (μ ε), smul_smul]
  have h := eventually_perronBranch hA (fun t => (isHermitian_iff_isSymm.mp (hH t)))
    hW hR hR0 (fun i j => hA0 ▸ infinityBlock_nonneg i j) (fun j => (hpos j).1)
    (fun i j h => (hpos j).2 ((infinityBlock_support hn i j (hA0 ▸ h)).2)) hPF hEig'
  filter_upwards [h, self_mem_nhdsWithin] with ε he (hε : ε < 0)
  rw [hscale hε, ofReal_mul] at he
  have hs : s ε ≠ 0 := inv_ne_zero (pow_ne_zero _ (div_ne_zero (by norm_num) hε.ne))
  exact mul_left_cancel₀ (ofReal_ne_zero.mpr hs) he

end PottsDiscontinuity.SixVertex
