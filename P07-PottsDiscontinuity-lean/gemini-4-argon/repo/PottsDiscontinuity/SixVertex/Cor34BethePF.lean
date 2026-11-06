module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BetheLimits
public import PottsDiscontinuity.SixVertex.Cor34Spectral

@[expose] public section

open Filter Topology
open Matrix Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

noncomputable def cor34_normalizedBlockWave {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : State N n → ℂ :=
  fun x => cor34_normalizedCoordinate ε p (BetheAnsatz.positions x)

private theorem cor34_det_eq_zero_of_mulVec_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    {M : Matrix ι ι K} {v : ι → K} (hv : v ≠ 0) (hMv : M *ᵥ v = 0) : M.det = 0 := by
  have hsmul : M.det • v = 0 := by
    rw [← Matrix.one_mulVec v, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul,
      ← Matrix.mulVec_mulVec, hMv, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact (mul_eq_zero.mp (congrFun hsmul i)).resolve_right hi

private theorem cor34_local_eigenvalue_uniqueness_left
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {μ : ℝ → ℂ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hsimple : (A 0).charpoly.rootMultiplicity (sSup (spectrum ℝ (A 0))) = 1)
    (hμ : Tendsto μ (𝓝 0) (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)))
    (hEig : ∀ᶠ t in 𝓝[<] 0, ∃ ψ : ι → ℂ, ψ ≠ 0 ∧
      (A t).map (algebraMap ℝ ℂ) *ᵥ ψ = μ t • ψ) :
    ∀ᶠ t in 𝓝[<] 0, μ t = ((sSup (spectrum ℝ (A t)) : ℝ) : ℂ) := by
  let ρ : ℝ := sSup (spectrum ℝ (A 0))
  have hroot0 : (A 0).charpoly.eval ρ = 0 :=
    (Matrix.mem_spectrum_iff_isRoot_charpoly.1
      (AnalyticTools.largestSpectrum_isGreatest (hHerm 0)).1).eq_zero
  obtain ⟨branch, _, _, W, _, hWopen, _, hWbase, _, _, hunique⟩ :=
    AnalyticTools.exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness
      (A := A) (t₀ := 0) (μ₀ := ρ) hA hroot0 hsimple
  have hpfCont : ContinuousAt (fun t => sSup (spectrum ℝ (A t))) 0 :=
    AnalyticTools.continuousAt_pfRoot_of_entrywise_analytic hA (hHerm 0)
      (Filter.Eventually.of_forall hHerm)
  have hμre : Tendsto (fun t => (μ t).re) (𝓝 0) (𝓝 ρ) := by
    simpa [ρ, Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hμ
  have hbranch_pf_left : ∀ᶠ t in 𝓝[<] 0, sSup (spectrum ℝ (A t)) = branch t := by
    have hpair : Tendsto (fun t => (t, sSup (spectrum ℝ (A t)))) (𝓝 0) (𝓝 (0, ρ)) := by
      simpa [ρ] using (continuousAt_id.prodMk hpfCont).tendsto
    refine (Filter.Eventually.mono (hpair.eventually (hWopen.mem_nhds hWbase)) fun t hW => ?_).filter_mono
      nhdsWithin_le_nhds
    exact hunique t _ hW (Matrix.mem_spectrum_iff_isRoot_charpoly.1
      (AnalyticTools.largestSpectrum_isGreatest (hHerm t)).1).eq_zero
  have hμ_real_eventually : ∀ᶠ t in 𝓝[<] 0, μ t = (μ t).re := by
    filter_upwards [hEig] with t ⟨ψ, hψne, hψ⟩
    let AC : Matrix ι ι ℂ := (A t).map (algebraMap ℝ ℂ)
    have hAC : AC.IsHermitian := Matrix.IsHermitian.ext fun i j => by
      simpa [AC] using congrArg (algebraMap ℝ ℂ) ((hHerm t).apply i j)
    let q : ℂ := star ψ ⬝ᵥ ψ
    have hself := hAC.star_dotProduct_mulVec_comm ψ ψ
    rw [hψ, dotProduct_smul, smul_eq_mul, star_mul', ← star_dotProduct] at hself
    have hq : q ≠ 0 := by
      have hsum : q = (∑ i, (Complex.normSq (ψ i) : ℝ) : ℂ) := by
        simp [q, dotProduct, Complex.normSq_eq_conj_mul_self]
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
      rw [hsum]
      exact_mod_cast (Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
        ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩).ne'
    have hstar : star (μ t) = μ t := mul_right_cancel₀ hq hself
    have him : -(μ t).im = (μ t).im := by simpa [Complex.star_def] using congrArg Complex.im hstar
    exact Complex.ext rfl (by simp; linarith)
  have hμ_root_eventually : ∀ᶠ t in 𝓝[<] 0, (A t).charpoly.eval (μ t).re = 0 := by
    filter_upwards [hμ_real_eventually, hEig] with t hreal ⟨ψ, hψne, hψ⟩
    let m := (μ t).re
    let AC : Matrix ι ι ℂ := (A t).map (algebraMap ℝ ℂ)
    have hscal : ∀ (z : ℂ) (v : ι → ℂ), Matrix.scalar ι z *ᵥ v = z • v := fun z v => by
      ext i; simp [Matrix.scalar, Matrix.diagonal, Matrix.mulVec, dotProduct]
    have hzero : (Matrix.scalar ι (m : ℂ) - AC) *ᵥ ψ = 0 := by
      rw [Matrix.sub_mulVec, hscal, hψ, hreal, sub_self]
    have hdetC := cor34_det_eq_zero_of_mulVec_eq_zero hψne hzero
    have hmap : (algebraMap ℝ ℂ).mapMatrix (Matrix.scalar ι m - A t) =
        Matrix.scalar ι (m : ℂ) - AC := by
      ext i j; by_cases hij : i = j <;> simp [AC, Matrix.scalar, hij]
    rw [Matrix.eval_charpoly]
    apply (algebraMap ℝ ℂ).injective
    rw [RingHom.map_det, hmap, hdetC, map_zero]
  have hmCurve_left : Tendsto (fun t => (t, (μ t).re)) (𝓝[<] 0) (𝓝 (0, ρ)) :=
    (continuousAt_id.tendsto.prodMk_nhds hμre).mono_left nhdsWithin_le_nhds
  filter_upwards [hμ_real_eventually, hmCurve_left.eventually (hWopen.mem_nhds hWbase),
    hμ_root_eventually, hbranch_pf_left] with t hreal hW hroot hpfb
  rw [hreal, hunique t (μ t).re hW hroot, hpfb]

theorem cor34_bethe_eigenbranch_eventually_pfRoot {N n : ℕ}
    (hn : 0 < n) (hbound : 2 * n ≤ N)
    {μ : ℝ → ℂ} {ψ : ℝ → State N n → ℂ}
    (hμ : Tendsto μ (𝓝 0) (𝓝 (pfRoot (infinityBlock N n) : ℂ)))
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      ψ ε ≠ 0 ∧
        Matrix.mulVec ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
          (ψ ε) = μ ε • ψ ε) :
    ∀ᶠ ε in 𝓝[<] 0,
      μ ε = (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := by
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  have hnear := cor34_local_eigenvalue_uniqueness_left
    (A := cor34_normalizedTransferBlock N n)
    (fun i j => cor34_normalizedTransferBlock_entry_analyticAt i j 0)
    cor34_normalizedTransferBlock_isHermitian
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using
      rootMultiplicity_infinityBlock_pfRoot hn hbound)
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using hμ)
    (hEig.mono fun t ht => ⟨ψ t, ht.1, ht.2⟩)
  simpa [pfRoot] using hnear

theorem cor34_final_normalizedRegularEigenvalue_scale {n : ℕ} {ε : ℝ}
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε :=
    Real.sq_sqrt (by linarith [div_neg_of_pos_of_neg two_pos hε])
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q]
    rw [show (c : ℂ) ^ 2 = ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast (show (-ε / 2) * (2 - 2 / ε) = 1 - ε by field_simp [hε.ne]; ring)
  have hL (j : Fin n) : cor34_normalizedL ε (p j) = q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedL BetheAnsatz.L; rw [← hcoeff]; ring
  have hM (j : Fin n) : cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M; rw [← hcoeff]; ring
  unfold cor34_normalizedRegularEigenvalue BetheAnsatz.eigenvalueRegular
  simp_rw [hL, hM, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem cor34_derivativeCorrection_eq_rational {ε y : ℝ} (hε : ε < 0) :
    cor34_derivativeCorrection ε y =
      2 * (1 + Real.cos y - 2 / ε) /
        ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
  have hd : 0 < 1 + Real.cos y - 2 / ε := by
    linarith [Real.neg_one_le_cos y, div_neg_of_pos_of_neg two_pos hε]
  have hden : (ε * (1 + Real.cos y) - 2) ^ 2 + ε ^ 2 * (Real.sin y) ^ 2 =
      ε ^ 2 * ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by field_simp [hε.ne]
  have hnum : 2 * ε * (ε * (1 + Real.cos y) - 2) =
      ε ^ 2 * (2 * (1 + Real.cos y - 2 / ε)) := by field_simp [hε.ne]
  unfold cor34_derivativeCorrection
  rw [hnum, hden]
  field_simp [hε.ne, (by positivity : 0 < (1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2).ne']

theorem cor34_final_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    {ε : ℝ} (hInv : 1 / ε < -1) (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  let c : ℝ := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε :=
    Real.sq_sqrt (by linarith [div_neg_of_pos_of_neg two_pos hε])
  have hcoeff : q * (c : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    dsimp [q]
    rw [show (c : ℂ) ^ 2 = ((2 - 2 / ε : ℝ) : ℂ) by exact_mod_cast hroot]
    exact_mod_cast (show (-ε / 2) * (2 - 2 / ε) = 1 - ε by field_simp [hε.ne]; ring)
  have hanisotropy : BetheAnsatz.anisotropy c = 1 / ε := by
    unfold BetheAnsatz.anisotropy; rw [hroot]; ring
  have hderivC (j : Fin n) :
      deriv (fun t : ℝ => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
        ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) := by
    have hdiff : DifferentiableAt ℝ
        (fun t : ℝ => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 := by
      simpa [hanisotropy] using (Bethe.analyticAt_theta_left hInv 0 (p j)).differentiableAt
    rw [hdiff.hasDerivAt.ofReal_comp.deriv, hanisotropy, cor34_deriv_theta_at_zero hInv,
      show 2 * (1 / ε) = 2 / ε by ring, cor34_derivativeCorrection_eq_rational hε]
  have hM (j : Fin n) : cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    unfold cor34_normalizedM BetheAnsatz.M; rw [← hcoeff]; ring
  have hpow : q * q ^ (n - 1) = q ^ n := by
    rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (Nat.zero_lt_of_lt l.isLt)]
  have htwo : q * (2 : ℂ) = ((-ε : ℝ) : ℂ) := by dsimp [q]; push_cast; ring
  have hsum :
      (∑ j ∈ Finset.univ.erase l,
          (deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 : ℂ)) =
        ∑ j ∈ Finset.univ.erase l,
          (((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ)) :=
    Finset.sum_congr rfl fun j _ => hderivC j
  have hprodM :
      (∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)) =
        q ^ (n - 1) * ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    rw [Finset.prod_congr rfl fun j _ => hM j, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  unfold cor34_normalizedZeroEigenvalue BetheAnsatz.eigenvalueZero
  rw [hsum, hprodM, ← hpow, ← hcoeff, ← htwo]
  push_cast
  ring

private theorem cor34_cancel_scale {N n : ℕ} {ε : ℝ} {Λ : ℂ}
    (hbound : 2 * n ≤ N) (hε : ε < 0)
    (h : (((-ε / 2 : ℝ) : ℂ) ^ n) * Λ = (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ)) :
    Λ = (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  rw [cor34_pfRoot_normalizedTransferBlock_eq (by omega) hε] at h
  let q : ℂ := ((-ε / 2 : ℝ) : ℂ)
  have hfactor : ((pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ) : ℂ) =
      q ^ n * (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
    dsimp [q]
    exact_mod_cast (by
      rw [div_eq_mul_inv, ← inv_pow, show (-2 / ε : ℝ)⁻¹ = -ε / 2 by field_simp [hε.ne]]
      ring : pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n =
        (-ε / 2 : ℝ) ^ n * pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n))
  rw [hfactor] at h
  have hqne : q ≠ 0 := by dsimp [q]; exact_mod_cast div_ne_zero (neg_ne_zero.mpr hε.ne) two_ne_zero
  exact mul_left_cancel₀ (pow_ne_zero n hqne) h

theorem cor34_even_bethe_branch_eventually_physical_pfRoot {N n r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedRegularEigenvalue ε (p ε) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) (p ε) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hnear := cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
    (cor34_normalizedRegularEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hn hN hr) hEig
  filter_upwards [hnear, self_mem_nhdsWithin] with ε hnear hε
  rw [cor34_final_normalizedRegularEigenvalue_scale hε (p ε)] at hnear
  exact cor34_cancel_scale hbound hε hnear

theorem cor34_odd_bethe_branch_eventually_physical_pfRoot {N n q r : ℕ}
    {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0)
    (hp0 : p 0 = Bethe.discreteBaseSolution N n)
    (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n)
    (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
              (⟨q - 1, by omega⟩ : Fin n) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) (p ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have hnear := cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
    (cor34_normalizedZeroEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hnq hN hr) hEig
  have hgt : ∀ᶠ ε : ℝ in 𝓝[<] (0 : ℝ), (-1 : ℝ) < ε :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
  filter_upwards [hnear, hgt, self_mem_nhdsWithin] with ε hnear hεlo hεhi
  have hInv : 1 / ε < -1 := by
    have hinv : 1 / ε < 0 := div_neg_of_pos_of_neg one_pos hεhi
    have hprod : (ε + 1) * (1 / ε) < 0 := mul_neg_of_pos_of_neg (by linarith) hinv
    rw [add_mul, mul_one_div_cancel (ne_of_lt hεhi), one_mul] at hprod
    linarith
  rw [cor34_final_normalizedZeroEigenvalue_scale (⟨q - 1, by omega⟩ : Fin n) hInv hεhi (p ε)] at hnear
  exact cor34_cancel_scale hbound hεhi hnear

end PottsDiscontinuity.SixVertex
