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
include ι

private theorem cor34_scalar_mulVec_eq_smul 
    {K : Type*} [Semiring K] (z : K) (v : ι → K) :
    Matrix.scalar ι z *ᵥ v = z • v := by
                                        simp_all

private theorem cor34_det_eq_zero_of_mulVec_eq_zero
     {K : Type*} [Field K]
    {M : Matrix ι ι K} {v : ι → K} (hv : v ≠ 0) (hMv : M *ᵥ v = 0) : M.det = 0 := by
  have hsmul : M.det • v = 0 := by
    calc
      M.det • v = (M.adjugate * M) *ᵥ v := by
        rw [Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = M.adjugate *ᵥ  M *ᵥ v  := by rw [Matrix.mulVec_mulVec]
      _ = 0 := by rw [hMv, Matrix.mulVec_zero]
  simp_all

/-- One-sided form of the simple-top-root argument. The eigenvector equation is needed only
on the physical side `ε<0`, matching the finite-parameter Bethe identity. -/
private theorem cor34_local_eigenvalue_uniqueness_left
     [Nonempty ι]
    {A : ℝ → Matrix ι ι ℝ} {μ : ℝ → ℂ}
    (hA : ∀ i j, AnalyticAt ℝ (fun t => A t i j) 0)
    (hHerm : ∀ t, (A t).IsHermitian)
    (hsimple : (A 0).charpoly.rootMultiplicity (sSup (spectrum ℝ (A 0))) = 1)
    (hμ : Tendsto μ (𝓝 0) (𝓝 ((sSup (spectrum ℝ (A 0)) : ℝ) : ℂ)))
    (hEig : ∀ᶠ t in 𝓝[<] 0, ∃ ψ : ι → ℂ, ψ ≠ 0 ∧
      (A t).map (algebraMap ℝ ℂ) *ᵥ ψ = μ t • ψ) :
    ∀ᶠ t in 𝓝[<] 0, μ t = ((sSup (spectrum ℝ (A t)) : ℝ) : ℂ) := by
  let ρ  := sSup (spectrum ℝ (A 0))
  
  have hbranch := AnalyticTools.exists_analytic_charpolyRootBranch_of_simple_with_local_uniqueness
    (A := A) (t₀ := 0) (μ₀ := ρ) hA (Polynomial.IsRoot.eq_zero
                                       (mem_spectrum_iff_isRoot_charpoly.mp (AnalyticTools.largestSpectrum_isGreatest (hHerm 0)).left)) hsimple
  obtain ⟨branch, hbranch0, hbranchAnalytic, W, V, hWopen, hVopen, hWbase, hVbase,
      hbranch, hunique⟩ := hbranch
  have hpfCont  :=
    AnalyticTools.continuousAt_pfRoot_of_entrywise_analytic hA (hHerm 0)
      (Filter.Eventually.of_forall hHerm)
  
  have hbranch_pf : ∀ᶠ t in 𝓝 0,
      sSup (spectrum ℝ (A t)) = branch t := by
                                              exact mp_mem (Eventually.of_forall hHerm)
                                                      (mp_mem
                                                        (Tendsto.eventually (ContinuousAt.tendsto (ContinuousAt.prodMk continuousAt_id hpfCont))
                                                          (IsOpen.mem_nhds hWopen hWbase))
                                                        (univ_mem' fun t hW hHt =>
                                                          hunique t (sSup (spectrum ℝ (A t))) hW
                                                            (Polynomial.IsRoot.eq_zero
                                                              (mem_spectrum_iff_isRoot_charpoly.mp (AnalyticTools.largestSpectrum_isGreatest hHt).left))))
  
  have hμ_real_eventually : ∀ᶠ t in 𝓝[<] 0, μ t = (μ t).re := by
    filter_upwards [hEig] with t ht
    obtain ⟨ψ, hψne, hψ⟩ := ht
    let AC  := (A t).map (algebraMap ℝ ℂ)
    have hAC : AC.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro i j
      simp only [AC]
      
      simpa using congrArg (algebraMap ℝ ℂ) ((hHerm t).apply i j)
    have hμreal : μ t = (μ t).re := by
      let q  := star ψ ⬝ᵥ ψ
      have hself := hAC.star_dotProduct_mulVec_comm ψ ψ
      rw [hψ] at hself
      have hqstar : star q = q := Eq.symm (star_dotProduct ψ ψ)
      
      have hq : q ≠ 0 := by
        have hsum :  star ψ ⬝ᵥ ψ  =
             ∑ i,  Complex.normSq (ψ i)  := by
          simp [dotProduct, Complex.normSq_eq_conj_mul_self]
        
        change star ψ ⬝ᵥ ψ ≠ 0
        rw [hsum]
        exact_mod_cast  ne_of_gt (by
                                    obtain ⟨i, hi⟩ := Function.ne_iff.mp hψne
                                    refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
                                    exact Complex.normSq_pos.mpr hi) 
      have hstar : star (μ t) = μ t := by
                                         aesop
      have him' : -(μ t).im = (μ t).im := congrArg Complex.im hstar
      have him : (μ t).im = 0 := by linarith
      apply Complex.ext
      · rfl
      · exact him
    exact hμreal
  have hμ_root_eventually : ∀ᶠ t in 𝓝[<] 0,
      (A t).charpoly.eval (μ t).re = 0 := by
    filter_upwards [hμ_real_eventually, hEig] with t hreal hEig_t
    obtain ⟨ψ, hψne, hψ⟩ := hEig_t
    let m := (μ t).re
    let AC  := (A t).map (algebraMap ℝ ℂ)
    
    have hdetC : (Matrix.scalar ι (m : ℂ) - AC).det = 0 :=
      cor34_det_eq_zero_of_mulVec_eq_zero hψne (by
                                                  rw [Matrix.sub_mulVec, cor34_scalar_mulVec_eq_smul, hψ, hreal, sub_self])
    have hmap : (algebraMap ℝ ℂ).mapMatrix (Matrix.scalar ι m - A t) =
        Matrix.scalar ι (m : ℂ) - AC := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [AC]
      · simp [AC, hij]
    have hdetR : (Matrix.scalar ι m - A t).det = 0 := by
      apply (algebraMap ℝ ℂ).injective
      rw [RingHom.map_det, hmap, hdetC]
      simp
    rw [Matrix.eval_charpoly]
    exact hdetR
  have hmCurve : Tendsto (fun t => (t, (μ t).re)) (𝓝 0) (𝓝 (0, ρ)) := by
    exact Tendsto.prodMk_nhds (fun ⦃U⦄ a => a) (Tendsto.comp (ContinuousAt.tendsto (Continuous.continuousAt Complex.continuous_re)) hμ)
  
  
  filter_upwards [hμ_real_eventually,  by
                                         filter_upwards [(hmCurve.mono_left
                                                            (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ)))).eventually (hWopen.mem_nhds hWbase),
                                           hμ_root_eventually] with t hW hroot
                                         exact hunique t (μ t).re hW hroot ,  hbranch_pf.filter_mono
                                                                                (nhdsWithin_le_nhds (s := Set.Iio (0 : ℝ))) ]
    with t hreal hμb hpfb
  rw [hreal, hμb, hpfb]

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
  
  
  
  
  
  
  
  simpa [pfRoot] using  cor34_local_eigenvalue_uniqueness_left
                             (fun i j => (fun i j => cor34_normalizedTransferBlock_entry_analyticAt i j 0) i j)  cor34_normalizedTransferBlock_isHermitian  (by
                                                          simpa [cor34_normalizedTransferBlock_zero, pfRoot] using
                                                            rootMultiplicity_infinityBlock_pfRoot hn hbound) (by
                                                                  simpa [cor34_normalizedTransferBlock_zero, pfRoot] using hμ) (by
                                                                      filter_upwards [hEig] with t ht
                                                                      all_goals grind) 

/-- The even normalized eigenvalue is the physical Bethe eigenvalue multiplied by
`(-ε/2)^n = (-2/ε)^(-n)`. -/
theorem cor34_normalizedRegularEigenvalue_scale {n : ℕ} (ε : ℝ)
    (hε : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedRegularEigenvalue ε p =
       ((-ε / 2 : ℝ) : ℂ) ^ n  *
        BetheAnsatz.eigenvalueRegular (Real.sqrt (2 - 2 / ε)) p := by
  let q : ℂ :=  (-ε / 2 : ℝ) 
  let c  := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    
    have hrec : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hε
    exact Real.sq_sqrt (by linarith)
  
  have hcoeff : q *  c  ^ 2 =  (1 - ε : ℝ)  := by
    dsimp [q]
    rw [show   Real.sqrt (2 - 2 / ε)   ^ 2 =
      ( 2 - 2 / ε  : ℂ) by exact_mod_cast hroot]
    exact_mod_cast  by
                      field_simp [ne_of_lt hε]
                      ring 
  have hL (j : Fin n) :
      cor34_normalizedL ε (p j) = q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    grind [cor34_normalizedL, BetheAnsatz.L]
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    grind [cor34_normalizedM, BetheAnsatz.M]
  have hprodL :
       ∏ j : Fin n, cor34_normalizedL ε (p j)  =
        q ^ n * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.L c (BetheAnsatz.z (p j)) := by
        simp_all
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.L c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp 
  have hprodM :
       ∏ j : Fin n, cor34_normalizedM ε (p j)  =
        q ^ n * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j : Fin n, q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        simp_all
      _ = (∏ j : Fin n, q) * ∏ j : Fin n, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp 
  unfold cor34_normalizedRegularEigenvalue BetheAnsatz.eigenvalueRegular
  rw [hprodL, hprodM]
  
  ring

private theorem cor34_derivativeCorrection_eq_rational {ε y : ℝ} (hε : ε < 0) :
    cor34_derivativeCorrection ε y =
      2 * (1 + Real.cos y - 2 / ε) /
        ((1 + Real.cos y - 2 / ε) ^ 2 +  Real.sin y  ^ 2) := by
  grind [cor34_derivativeCorrection]

/-- The odd normalized zero-root eigenvalue is the physical expression multiplied by
`(-ε/2)^n` on the negative side where the phase derivative formula applies. -/
theorem cor34_normalizedZeroEigenvalue_scale {N n : ℕ} (l : Fin n)
    (ε : ℝ) (hεlo : -1 < ε) (hεhi : ε < 0) (p : Fin n → ℝ) :
    cor34_normalizedZeroEigenvalue (N := N) ε p l =
       ((-ε / 2 : ℝ) : ℂ) ^ n  *
        BetheAnsatz.eigenvalueZero N (Real.sqrt (2 - 2 / ε)) p l := by
  let q : ℂ :=  (-ε / 2 : ℝ) 
  let c  := Real.sqrt (2 - 2 / ε)
  have hroot : c ^ 2 = 2 - 2 / ε := by
    
    have hdiv : 2 / ε < 0 := div_neg_of_pos_of_neg (by norm_num) hεhi
    exact Real.sq_sqrt (by linarith)
  
  have hcoeff : q *  c  ^ 2 =  (1 - ε : ℝ)  := by
    dsimp [q]
    rw [show   Real.sqrt (2 - 2 / ε)   ^ 2 =
      ( 2 - 2 / ε  : ℂ) by exact_mod_cast hroot]
    exact_mod_cast  by
                      field_simp [ne_of_lt hεhi]
                      ring 
  have hbaseInv : 1 / ε < -1 := by
    
    
    have hprod : (ε + 1) * (1 / ε) < 0 :=
      mul_neg_of_pos_of_neg (by linarith) (div_neg_of_pos_of_neg one_pos hεhi)
    grind
  have hanisotropy : BetheAnsatz.anisotropy c = 1 / ε := by
    grind [BetheAnsatz.anisotropy]
  have hderiv (j : Fin n) :
       deriv (fun t => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0  =
        -1 + cor34_derivativeCorrection ε (p j) := by
    rw [hanisotropy, cor34_deriv_theta_at_zero hbaseInv]
    rw [show 2 * (1 / ε) = 2 / ε by ring]
    rw [cor34_derivativeCorrection_eq_rational hεhi]
  have hderivC (j : Fin n) :
      deriv (fun t  => (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 =
         (-1 + cor34_derivativeCorrection ε (p j) : ℝ)  := by
    have hdiff : DifferentiableAt ℝ
        (fun t  => Bethe.theta (BetheAnsatz.anisotropy c) t (p j)) 0 := by
      simpa [hanisotropy] using
        (Bethe.analyticAt_theta_left hbaseInv 0 (p j)).differentiableAt
    have hcast := hdiff.hasDerivAt.ofReal_comp
    rw [hcast.deriv, hderiv j]
  
  have htwo : q *  2  =  -ε  := by
    dsimp [q]
    push_cast
    ring
  
  have hM (j : Fin n) :
      cor34_normalizedM ε (p j) = q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    grind [cor34_normalizedM, BetheAnsatz.M]
  have hprodM :
       ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j)  =
        q ^ (n - 1) * ∏ j ∈ Finset.univ.erase l,
          BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
    calc
      _ = ∏ j ∈ Finset.univ.erase l,
          q * BetheAnsatz.M c (BetheAnsatz.z (p j)) := by
        simp_all
      _ = (∏ j ∈ Finset.univ.erase l, q) *
          ∏ j ∈ Finset.univ.erase l, BetheAnsatz.M c (BetheAnsatz.z (p j)) :=
        Finset.prod_mul_distrib
      _ = _ := by simp_all
  have hnpos  := Nat.zero_lt_of_lt l.isLt
  have hpow : q * q ^ (n - 1) = q ^ n := by
    have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    grind
  
  
  have hmain :
      ( -ε  +  (1 - ε : ℝ)  *
          (  N  - 1  + ∑ j ∈ Finset.univ.erase l,
             ((-1 + cor34_derivativeCorrection ε (p j) : ℝ) : ℂ) )) *
        ∏ j ∈ Finset.univ.erase l, cor34_normalizedM ε (p j) =
      q ^ n *
        ((2 +  c  ^ 2 * ( N  - 1) +  c  ^ 2 *
            ∑ j ∈ Finset.univ.erase l,
               deriv (fun t  =>
                (Bethe.theta (BetheAnsatz.anisotropy c) t (p j) : ℂ)) 0 ) *
          ∏ j ∈ Finset.univ.erase l,
            BetheAnsatz.M c (BetheAnsatz.z (p j))) := by
    grind
  simpa [cor34_normalizedZeroEigenvalue, BetheAnsatz.eigenvalueZero, c, q] using hmain

section

variable {N n r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hn : Even n) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
include hp hp0 hNpos hbound hnpos hn hN hr

/-- Even-parity conditional Corollary 3.4 for a continuous family based at the discrete
solution. -/
theorem cor34_even_bethe_branch_eventually_pfRoot 
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedRegularEigenvalue ε (p ε) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedRegularEigenvalue ε (p ε) =
        (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
                                                                (cor34_normalizedRegularEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hn hN hr) hEig

/-- The even conditional conclusion in physical eigenvalue units. -/
theorem cor34_even_bethe_branch_eventually_physical_pfRoot 
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
  have hnear := cor34_even_bethe_branch_eventually_pfRoot
    hp hp0 hNpos hbound hnpos hn hN hr hEig
  filter_upwards [hnear, self_mem_nhdsWithin] with ε hnear hεmem
  have hε  := hεmem
  
  
  rw [ cor34_normalizedRegularEigenvalue_scale ε hε (p ε) ,  cor34_pfRoot_normalizedTransferBlock_eq
                 (N := N) (n := n) (by omega) hε ] at hnear
  let q : ℂ :=   -ε / 2  
  have hbaseInv :  (-2 / ε )⁻¹  =  -ε / 2  := by
    field_simp 
  have hfactorR :
       pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n  =
        (-ε / 2 ) ^ n *
          pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) := by
    rw [div_eq_mul_inv, ← inv_pow, hbaseInv]
    ring
  have hfactor :
       (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ)  =
        q ^ n *  pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n)  := by
    dsimp [q]
    exact_mod_cast hfactorR
  rw [hfactor] at hnear
  have hqne : q ≠ 0 := by
    aesop 
  apply mul_left_cancel₀ (pow_ne_zero n hqne)
  simpa [q] using hnear

end

section

variable {N n q r : ℕ} {p : ℝ → Fin n → ℝ} (hp : ContinuousAt p 0) (hp0 : p 0 = Bethe.discreteBaseSolution N n) (hNpos : 0 < N) (hbound : 2 * n ≤ N) (hnpos : 0 < n) (hnq : n + 1 = 2 * q) (hN : N = 2 * (n + r)) (hr : 0 ≤ r)
include hp hp0 hNpos hbound hnpos hnq hN hr

/-- Odd-parity conditional Corollary 3.4 for the centered zero-root branch. -/
theorem cor34_odd_bethe_branch_eventually_pfRoot 
    (hEig : ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedBlockWave (N := N) (n := n) ε (p ε) ≠ 0 ∧
        Matrix.mulVec
          ((cor34_normalizedTransferBlock N n ε).map (algebraMap ℝ ℂ))
            (cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) =
          cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
              (⟨q - 1, by omega⟩ : Fin n) •
            cor34_normalizedBlockWave (N := N) (n := n) ε (p ε)) :
    ∀ᶠ ε in 𝓝[<] 0,
      cor34_normalizedZeroEigenvalue (N := N) ε (p ε)
          (⟨q - 1, by omega⟩ : Fin n) =
        (pfRoot (cor34_normalizedTransferBlock N n ε) : ℂ) := cor34_bethe_eigenbranch_eventually_pfRoot hnpos hbound
                                                                (cor34_normalizedZeroEigenvalue_tendsto_pfRoot hp hp0 hNpos hbound hnpos hnq hN hr) hEig

/-- The odd conditional conclusion in physical eigenvalue units. -/
theorem cor34_odd_bethe_branch_eventually_physical_pfRoot 
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
  have hnear := cor34_odd_bethe_branch_eventually_pfRoot
    hp hp0 hNpos hbound hnpos hnq hN hr hEig
  
  filter_upwards [hnear,  by
                            have hbase : ∀ᶠ ε : ℝ in 𝓝 0, ε ∈ Set.Ioi (-1 ) :=
                              Ioi_mem_nhds (by norm_num)
                            exact hbase.filter_mono (nhdsWithin_le_nhds (s := Set.Iio  0 )) , self_mem_nhdsWithin] with ε hnear hεlo hεmem
  have hεhi  := hεmem
  let l : Fin n := ⟨q - 1, by omega⟩
  
  
  rw [ cor34_normalizedZeroEigenvalue_scale (N := N) l ε hεlo hεhi (p ε) ,  cor34_pfRoot_normalizedTransferBlock_eq
                 (N := N) (n := n) (by omega) hεhi ] at hnear
  let qscale : ℂ :=   -ε / 2  
  have hbaseInv :  (-2 / ε )⁻¹  =  -ε / 2  := by
    field_simp 
  have hfactorR :
       pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n  =
        (-ε / 2 ) ^ n *
          pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) := by
    rw [div_eq_mul_inv, ← inv_pow, hbaseInv]
    ring
  have hfactor :
       (pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n) / (-2 / ε) ^ n : ℝ)  =
        qscale ^ n *  pfRoot (transferBlock N (Real.sqrt (2 - 2 / ε)) n)  := by
    dsimp [qscale]
    exact_mod_cast hfactorR
  rw [hfactor] at hnear
  have hqne : qscale ≠ 0 := by
    aesop 
  apply mul_left_cancel₀ (pow_ne_zero n hqne)
  simpa [qscale, l] using hnear

end

end PottsDiscontinuity.SixVertex
