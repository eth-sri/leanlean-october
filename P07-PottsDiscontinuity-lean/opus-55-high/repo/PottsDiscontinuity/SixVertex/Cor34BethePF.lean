module

public import Mathlib
public import PottsDiscontinuity.SixVertex.Cor34BetheLimits
public import PottsDiscontinuity.SixVertex.Cor34Spectral

/-! # Corollary 3.4: conditional identification with the Perron root

The eigenvector equation is an explicit premise corresponding to the Bethe ansatz theorem.
-/

@[expose] public section

open Filter Topology
open Matrix Set
open PottsDiscontinuity.PerronFrobenius

namespace PottsDiscontinuity.SixVertex

/-- The continuously normalized Bethe coordinate wave on the `n`-particle state block. -/
noncomputable def cor34_normalizedBlockWave {N n : ℕ} (ε : ℝ)
    (p : Fin n → ℝ) : State N n → ℂ :=
  fun x => cor34_normalizedCoordinate ε p (BetheAnsatz.positions x)

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- One-sided form of the simple-top-root argument. The eigenvector equation is needed only
on the physical side `ε<0`, matching the finite-parameter Bethe identity. -/
theorem cor34_local_eigenvalue_uniqueness_left
    [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {μ : ℝ → ℂ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hsimple : (A 0).charpoly.rootMultiplicity (sSup (spectrum ℝ (A 0))) = 1)
    (hμ : Tendsto μ (𝓝 0) (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)))
    (hEig : ∀ᶠ t in 𝓝[<] 0, ∃ ψ : ι → ℂ, ψ ≠ 0 ∧
      (A t).map (algebraMap ℝ ℂ) *ᵥ ψ = μ t • ψ) :
    ∀ᶠ t in 𝓝[<] 0, μ t = ((sSup (spectrum ℝ (A t)) : ℝ) : ℂ) := by
  let ρ := sSup (spectrum ℝ (A 0))
  have hroot := fun t =>
    Matrix.mem_spectrum_iff_isRoot_charpoly.1 (AnalyticTools.largestSpectrum_isGreatest (hHerm t)).1
  obtain ⟨branch, -, -, W, V, hWopen, -, hWbase, -, -, hunique⟩ :=
    AnalyticTools.exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness
      (μ₀ := ρ) hA (hroot 0) hsimple
  have hbranch_pf : ∀ᶠ t in 𝓝 0, sSup (spectrum ℝ (A t)) = branch t := by
    filter_upwards [(continuousAt_id.prodMk (AnalyticTools.continuousAt_pfRoot_of_entrywise_analytic
      hA (hHerm 0) (.of_forall hHerm))).eventually (hWopen.mem_nhds hWbase)] with t hW
    exact hunique t _ hW (hroot t)
  have hμ_real_eventually : ∀ᶠ t in 𝓝[<] 0, μ t = (μ t).re := by
    filter_upwards [hEig] with t ht
    obtain ⟨ψ, hψne, hψ⟩ := ht
    have h := ((hHerm t).map (algebraMap ℝ ℂ) fun x => by simp).im_star_dotProduct_mulVec_self ψ
    rw [hψ, dotProduct_smul, smul_eq_mul] at h
    have hq : star ψ ⬝ᵥ ψ = ((∑ i, Complex.normSq (ψ i) : ℝ) : ℂ) := by
      simp [dotProduct, Complex.normSq_eq_conj_mul_self]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
    have := Finset.sum_pos' (fun j _ => Complex.normSq_nonneg (ψ j)) ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩
    simp [hq] at h
    apply Complex.ext <;> simp [h.resolve_right this.ne']
  have hμ_root_eventually : ∀ᶠ t in 𝓝[<] 0,
      (A t).charpoly.eval (μ t).re = 0 := by
    filter_upwards [hμ_real_eventually, hEig] with t hreal hEig_t
    obtain ⟨ψ, hψne, hψ⟩ := hEig_t
    rw [Matrix.eval_charpoly]
    apply (algebraMap ℝ ℂ).injective
    rw [RingHom.map_det, map_zero, ← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨ψ, hψne, ?_⟩
    simp only [Complex.coe_algebraMap] at hψ
    simp [RingHom.mapMatrix_apply, Matrix.map_sub, Matrix.sub_mulVec, hψ, sub_eq_zero]
    nth_rw 2 [hreal]; rfl
  have hbranch_mu : ∀ᶠ t in 𝓝[<] 0, (μ t).re = branch t := by
    filter_upwards [((continuousAt_id.tendsto.prodMk_nhds (Complex.continuous_re.continuousAt.tendsto.comp
      hμ)).mono_left nhdsWithin_le_nhds).eventually (hWopen.mem_nhds hWbase), hμ_root_eventually] with t hW hroot
    exact hunique t _ hW hroot
  filter_upwards [hμ_real_eventually, hbranch_mu, nhdsWithin_le_nhds hbranch_pf] with t hreal hμb hpfb
  grind
end

/-- A normalized Bethe eigenvalue branch converging to the infinity PF root is the PF root
near zero if its normalized wave is eventually a nonzero eigenvector of the normalized block. -/
theorem cor34_bethe_eigenbranch_eventually_pfRoot {N n : ℕ}
    (hn : 0 < n) (hbound : 2 * n ≤ N)
    {μ : ℝ → ℂ} {ψ : ℝ → State N n → ℂ}
    (hμ : Tendsto μ (𝓝 0) (𝓝 (pfRoot (infinityBlock N n) : ℂ)))
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      ψ ε ≠ 0 ∧
        Matrix.mulVec ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
          (ψ ε) =
          μ ε • ψ ε) :
    ∀ᶠ ε in 𝓝[<] 0,
      μ ε = (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := by
  have : Nonempty (State N n) := ⟨packed (by omega)⟩
  exact cor34_local_eigenvalue_uniqueness_left (fun i j => cor34_normalizedTransferBlock_entry_analyticAt i j 0)
    cor34_normalizedTransferBlock_isHermitian
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using rootMultiplicity_infinityBlock_pfRoot hn hbound)
    (by simpa [cor34_normalizedTransferBlock_zero, pfRoot] using hμ) (hEig.mono fun t ht => ⟨_, ht⟩)

theorem cor34_scale_LM {ε : ℝ} (hε : ε < 0) : ∀ y,
    cor34_normalizedL ε y = ((-ε / 2 : ℝ) : ℂ) * BetheAnsatz.L √(2 - 2 / ε) (BetheAnsatz.z y) ∧
    cor34_normalizedM ε y = ((-ε / 2 : ℝ) : ℂ) * BetheAnsatz.M √(2 - 2 / ε) (BetheAnsatz.z y) := by
  have hcoeff : ((-ε / 2 : ℝ) : ℂ) * ((√(2 - 2 / ε) : ℝ) : ℂ) ^ 2 = ((1 - ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by have := div_neg_of_pos_of_neg two_pos hε; linarith),
      ← Complex.ofReal_mul]
    have := hε.ne; congr 1; field_simp; ring
  intro y; constructor <;> grind [cor34_normalizedL, cor34_normalizedM, BetheAnsatz.L, BetheAnsatz.M]

theorem cor34_normalizedRegularEigenvalue_scale {n : ℕ} (ε : ℝ)
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  simp [cor34_normalizedRegularEigenvalue, BetheAnsatz.eigenvalueRegular, cor34_scale_LM hε,
    Finset.prod_mul_distrib, mul_add, div_pow]

theorem cor34_derivativeCorrection_eq_rational {ε y : ℝ} (hε : ε < 0) :
    cor34_derivativeCorrection ε y =
      2 * (1 + Real.cos y - 2 / ε) /
        ((1 + Real.cos y - 2 / ε) ^ 2 + (Real.sin y) ^ 2) := by
  grind [Real.cos, Real.sin, cor34_derivativeCorrection]

/-- The odd normalized zero-root eigenvalue is the physical expression multiplied by
`(-ε/2)^n` on the negative side where the phase derivative formula applies. -/
theorem cor34_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    (ε : ℝ) (hεlo : -1 < ε) (hεhi : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
      (((-ε / 2 : ℝ) : ℂ) ^ n) *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  rw [cor34_normalizedZeroEigenvalue, BetheAnsatz.eigenvalueZero]
  simp only [(cor34_scale_LM hεhi _).2, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  set c := Real.sqrt (2 - 2 / ε)
  have hbaseInv : 1 / ε < -1 := by
    have hmul : ε * (1 / ε) = 1 := by grind
    nlinarith
  have hanisotropy : BetheAnsatz.anisotropy c = 1 / ε := by
    grind [BetheAnsatz.anisotropy]
  have hderivC (j : Fin n) :
      deriv (fun t : ℝ => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
        ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) := by
    rw [hanisotropy, (Bethe.analyticAt_theta_left hbaseInv 0 (p j)).differentiableAt.hasDerivAt.ofReal_comp.deriv,
      cor34_deriv_theta_at_zero hbaseInv]
    grind [cor34_derivativeCorrection_eq_rational]
  have hroot : (c : ℂ) ^ 2 = ((2 - 2 / ε : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by have := div_neg_of_pos_of_neg two_pos hεhi; linarith)]
  simp only [hderivC, hroot]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by have := l.pos; omega⟩
  have : (ε : ℂ) ≠ 0 := by exact_mod_cast hεhi.ne
  push_cast
  field_simp
  ring

theorem cor34_unscale {N n : ℕ} (hn : n ≤ N) {ε : ℝ} (hε : ε < 0) {X Y : ℂ}
    (h : X = pfRoot (cor34_normalizedTransferBlock N n ε)) (hX : X = ((-ε / 2 : ℝ) : ℂ) ^ n * Y) :
    Y = pfRoot (transferBlock N √(2 - 2 / ε) n) := by
  have := hε.ne
  rw [cor34_pfRoot_normalizedTransferBlock_eq hn hε, hX, div_eq_mul_inv _ ((-2 / ε) ^ n), ← inv_pow,
    show (-2 / ε)⁻¹ = -ε / 2 by field_simp] at h
  push_cast at h
  exact mul_left_cancel₀ (pow_ne_zero n (by simpa)) (h.trans (mul_comm _ _))

end PottsDiscontinuity.SixVertex
