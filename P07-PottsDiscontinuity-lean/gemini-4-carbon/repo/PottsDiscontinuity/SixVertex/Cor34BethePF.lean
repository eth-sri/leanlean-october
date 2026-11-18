module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BetheLimits
public import PottsDiscontinuity.SixVertex.Cor34Spectral

/-! # Corollary 3.4: conditional identification with the Perron root

The eigenvector equation is an explicit premise corresponding to the Bethe ansatz theorem.
-/

@[expose] public section

open Filter Topology Matrix Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The continuously normalized Bethe coordinate wave on the `n`-particle state block. -/
noncomputable def cor34_normalizedBlockWave {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : State N n → ℂ :=
  fun x => cor34_normalizedCoordinate ε p (BetheAnsatz.positions x)

private theorem cor34_local_eigenvalue_uniqueness_left
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {μ : ℝ → ℂ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hsimple : (A 0).charpoly.rootMultiplicity (sSup (spectrum ℝ (A 0))) = 1)
    (hμ : Tendsto μ (𝓝 0) (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)))
    (hEig : ∀ᶠ t in 𝓝[<] 0, ∃ ψ : ι → ℂ, ψ ≠ 0 ∧ (A t).map (algebraMap ℝ ℂ) *ᵥ ψ = μ t • ψ) :
    ∀ᶠ t in 𝓝[<] 0, μ t = ((sSup (spectrum ℝ (A t)) : ℝ) : ℂ) := by
  let ρ : ℝ := sSup (spectrum ℝ (A 0))
  have hroot0 : (A 0).charpoly.eval ρ = 0 :=
    ((Matrix.mem_spectrum_iff_isRoot_charpoly).1 (AnalyticTools.largestSpectrum_isGreatest (hHerm 0)).1).eq_zero
  obtain ⟨branch, _, _, W, _, hWopen, _, hWbase, _, _, hunique⟩ :=
    AnalyticTools.exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness (t₀ := 0) hA hroot0 hsimple
  have hpfCont := AnalyticTools.continuousAt_pfRoot_of_entrywise_analytic hA (hHerm 0) (Filter.Eventually.of_forall hHerm)
  have hbranch_pf : ∀ᶠ t in 𝓝[<] 0, sSup (spectrum ℝ (A t)) = branch t := by
    refine (Filter.Tendsto.eventually (by simpa [ρ] using (continuousAt_id.prodMk hpfCont).tendsto)
      (hWopen.mem_nhds hWbase)).filter_mono nhdsWithin_le_nhds |>.mono fun t hW =>
      hunique t _ hW (((Matrix.mem_spectrum_iff_isRoot_charpoly).1 (AnalyticTools.largestSpectrum_isGreatest (hHerm t)).1).eq_zero)
  have hμ_real_root : ∀ᶠ t in 𝓝[<] 0, μ t = (μ t).re ∧ (A t).charpoly.eval (μ t).re = 0 := by
    filter_upwards [hEig] with t ⟨ψ, hψne, hψ⟩
    let AC := (A t).map (algebraMap ℝ ℂ)
    have hAC : AC.IsHermitian := Matrix.IsHermitian.ext fun i j => by
      simpa [AC, Complex.star_def] using congrArg (algebraMap ℝ ℂ) ((hHerm t).apply i j)
    let q : ℂ := star ψ ⬝ᵥ ψ
    have hqstar : star q = q := (star_dotProduct ψ ψ).symm
    have hself := hAC.star_dotProduct_mulVec_comm ψ ψ
    rw [hψ, dotProduct_smul, smul_eq_mul, star_mul'] at hself
    change star (μ t) * star q = μ t * q at hself
    rw [hqstar] at hself
    have hq : q ≠ 0 := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
      have hpos : 0 < ∑ j, Complex.normSq (ψ j) :=
        Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
      rw [show q = ((∑ j, Complex.normSq (ψ j) : ℝ) : ℂ) by simp [q, dotProduct, Complex.normSq_eq_conj_mul_self]]
      exact_mod_cast hpos.ne'
    have hstar : star (μ t) = μ t := mul_right_cancel₀ hq hself
    have him : (μ t).im = 0 := by have := congrArg Complex.im hstar; simp at this; linarith
    let m : ℝ := (μ t).re
    have hreal : μ t = (m : ℂ) := Complex.ext rfl him
    refine ⟨hreal, ?_⟩
    let M := Matrix.scalar ι (m : ℂ) - AC
    have hzero : M *ᵥ ψ = 0 := by
      change (Matrix.scalar ι (m : ℂ) - AC) *ᵥ ψ = 0
      rw [Matrix.sub_mulVec, show Matrix.scalar ι (m : ℂ) *ᵥ ψ = (m : ℂ) • ψ by
        ext i; simp [Matrix.scalar, Matrix.diagonal, Matrix.mulVec, dotProduct], hψ, hreal, sub_self]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
    have hsmul : M.det • ψ = 0 := by
      calc M.det • ψ = (M.adjugate * M) *ᵥ ψ := by rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
        _ = M.adjugate *ᵥ (M *ᵥ ψ) := by rw [Matrix.mulVec_mulVec]
        _ = 0 := by rw [hzero, Matrix.mulVec_zero]
    have hdetC : M.det = 0 := (mul_eq_zero.mp (congrFun hsmul i)).resolve_right hi
    rw [Matrix.eval_charpoly]
    refine (algebraMap ℝ ℂ).injective ?_
    rw [RingHom.map_det, show (algebraMap ℝ ℂ).mapMatrix (Matrix.scalar ι m - A t) = M by
      ext a b; by_cases hab : a = b <;> simp [AC, M, Matrix.scalar, hab], hdetC, map_zero]
  have hmCurve : Tendsto (fun t => (t, (μ t).re)) (𝓝[<] 0) (𝓝 (0, ρ)) := by
    have hre : Tendsto (fun t => (μ t).re) (𝓝 0) (𝓝 ρ) := by
      change Tendsto (Complex.re ∘ μ) (𝓝 0) (𝓝 ρ)
      simpa [ρ] using Complex.continuous_re.continuousAt.tendsto.comp hμ
    exact (continuousAt_id.tendsto.prodMk_nhds hre).mono_left nhdsWithin_le_nhds
  filter_upwards [hμ_real_root, hmCurve.eventually (hWopen.mem_nhds hWbase), hbranch_pf] with t ⟨hreal, hroot⟩ hW hpfb
  rw [hreal, hunique t _ hW hroot, hpfb]

private theorem cor34_physical_pfRoot_of_normalized {N n : ℕ}
    (hnpos : 0 < n) (hbound : 2 * n ≤ N) {μ_norm μ_phys : ℝ → ℂ} {ψ : ℝ → State N n → ℂ}
    (hμ : Tendsto μ_norm (𝓝 0) (𝓝 (pfRoot (infinityBlock N n) : ℂ)))
    (hscale : ∀ᶠ ε in 𝓝[<] 0, μ_norm ε = ((-ε / 2 : ℝ) : ℂ) ^ n * μ_phys ε)
    (hEig : ∀ᶠ ε in 𝓝[<] 0, ψ ε ≠ 0 ∧
      Matrix.mulVec ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ)) (ψ ε) = μ_norm ε • ψ ε) :
    ∀ᶠ ε in 𝓝[<] 0, μ_phys ε = (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) := by
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  have hnear := cor34_local_eigenvalue_uniqueness_left
    (fun i j => cor34_normalizedTransferBlock_entry_analyticAt i j 0)
    cor34_normalizedTransferBlock_isHermitian
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using rootMultiplicity_infinityBlock_pfRoot hnpos hbound)
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using hμ)
    (hEig.mono fun ε h => ⟨ψ ε, h.1, h.2⟩)
  filter_upwards [hnear, hscale, self_mem_nhdsWithin] with ε hnear hsc hε
  have hεlt : ε < 0 := hε
  rw [hsc, ← pfRoot, cor34_pfRoot_normalizedTransferBlock_eq (by omega) hεlt,
    show ((pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ) : ℂ) =
      ((-ε / 2 : ℝ) : ℂ) ^ n * (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) : ℂ) by
      rw [div_eq_mul_inv, ← inv_pow, show (-2 / ε)⁻¹ = -ε / 2 by field_simp [hεlt.ne'], mul_comm]; push_cast; rfl] at hnear
  exact mul_left_cancel₀ (pow_ne_zero n (by exact_mod_cast (div_ne_zero (neg_ne_zero.mpr hεlt.ne) two_ne_zero))) hnear

/-- The even conditional conclusion in physical eigenvalue units. -/
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
  refine cor34_physical_pfRoot_of_normalized hnpos hbound
    (cor34_normalizedRegularEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hn hN hr) ?_ hEig
  filter_upwards [self_mem_nhdsWithin] with ε (hε : ε < 0)
  exact cor34_normalizedRegularEigenvalue_scale hε (p ε)

/-- The odd conditional conclusion in physical eigenvalue units. -/
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
  refine cor34_physical_pfRoot_of_normalized hnpos hbound
    (cor34_normalizedZeroEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hnq hN hr) ?_ hEig
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0)), self_mem_nhdsWithin]
    with ε (hεlo : -1 < ε) (hεhi : ε < 0)
  have hbInv : 1 / ε < -1 := by
    have := mul_neg_of_pos_of_neg (by linarith : 0 < ε + 1) (div_neg_of_pos_of_neg one_pos hεhi)
    rw [add_mul, mul_one_div_cancel hεhi.ne, one_mul] at this; linarith
  exact cor34_normalizedZeroEigenvalue_scale ⟨q - 1, by omega⟩ hbInv hεhi (p ε)

end PottsDiscontinuity.SixVertex
