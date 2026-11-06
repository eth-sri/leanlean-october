module

public import RequestProject.L2Pairing

public import RequestProject.PlanarTypes

public import RequestProject.Spectrum

/-!
# Finiteness of the Neumann eigenvalues

For a nonempty open set `Ω`, every min–max value `μ_j(Ω)` is finite.  We exhibit a
`(j+1)`-dimensional space of smooth compactly supported bumps on which the Rayleigh
quotient is bounded.
-/

public section

open scoped ContDiff

open MeasureTheory



namespace PolyaNeumann

variable {Ω : PlanarSet}

lemma TestFunction.memLp_fderiv  (hφ : TestFunction Ω φ) v :
    MemLp (fun w => fderiv ℝ φ w v) 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (((hs.continuous_fderiv (by simp)).clm_apply continuous_const :).memLp_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) v)).restrict Ω

lemma TestFunction.memLp  (hφ : TestFunction Ω φ) :
    MemLp φ 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (hs.continuous.memLp_of_hasCompactSupport hc).restrict Ω



lemma IsWeakGradient.add   (hu : IsWeakGradient Ω u g)
    (hv : IsWeakGradient Ω v h) : IsWeakGradient Ω (u + v) (g + h) := by
  intro φ hφ i
  simpa only [← lpPair_apply (hφ.memLp_fderiv (coordDir i)),
    ← lpPair_apply hφ.memLp, map_add, Pi.add_apply, neg_add]
    using congrArg₂ (· + ·) (hu φ hφ i) (hv φ hφ i)

lemma IsWeakGradient.smul   (c : ℂ) (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (c • u) (c • g) := by
  intro φ hφ i
  simpa only [← lpPair_apply (hφ.memLp_fderiv (coordDir i)),
    ← lpPair_apply hφ.memLp, map_smul, Pi.smul_apply, smul_eq_mul, mul_neg]
    using congrArg (c * ·) (hu φ hφ i)

lemma isWeakGradient_zero : IsWeakGradient Ω 0 0 := by
  intro φ hφ i
  simp only [← lpPair_apply (hφ.memLp_fderiv (coordDir i)),
    ← lpPair_apply hφ.memLp, Pi.zero_apply, map_zero, neg_zero]

lemma IsWeakGradient.sum {ι : Type*} s (u : ι → L2 Ω) (g : ι → Coord → L2 Ω)
    (h : ∀ k ∈ s, IsWeakGradient Ω (u k) (g k)) :
    IsWeakGradient Ω (∑ k ∈ s, u k) (∑ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeakGradient_zero
  | insert a s ha ih =>
    simp_all [add]

/-- The classical gradient of a `C¹` function is its weak gradient. -/
lemma isWeakGradient_of_contDiff_one  (hf : ContDiff ℝ 1 f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨hs, hφc, hsupp⟩ := hφ
  have e1' : (fun w => ((hu.toLp f : L2 Ω) : PlaneMap) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => f w * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [hu.coeFn_toLp] with w hw; rw [hw]
  have e2' : (fun w => (((hg i).toLp _ : L2 Ω) : PlaneMap) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => fderiv ℝ f w (coordDir i) * φ w := by
    filter_upwards [(hg i).coeFn_toLp] with w hw; rw [hw]
  rw [integral_congr_ae e1', integral_congr_ae e2']
  have hout : ∀ w ∉ Ω, w ∉ tsupport φ := fun w hw h => hw (hsupp h)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) (hout w hw)]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun w hw => by
      simp [image_eq_zero_of_notMem_tsupport (hout w hw)])]
  have hfd : Continuous fun w => fderiv ℝ f w (coordDir i) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφd : Continuous fun w => fderiv ℝ φ w (coordDir i) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hfd.mul hs.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) _).mul_left))
    ((hf.continuous.mul hs.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => (hs.differentiable (by simp)) x)

/-- The classical gradient of a smooth compactly supported function is its weak gradient. -/
lemma isWeakGradient_of_smooth  (hf : RealSmooth f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) :=
  isWeakGradient_of_contDiff_one (hf.of_le (by simp)) hu hg

/-- If `u_0, …, u_j ∈ H¹(Ω)` are linearly independent in `L²(Ω)`, then `μ_j(Ω) < ∞`. -/
lemma neumannEigenvalue_lt_top_of_family j u
    (g : Fin (j + 1) → Coord → L2 Ω) (hli : LinearIndependent ℂ u)
    (hg : ∀ k, IsWeakGradient Ω (u k) (g k)) : neumannEigenvalue Ω j < ⊤ := by
  set T := Fintype.linearCombination ℂ u
  set Gr := Fintype.linearCombination ℂ g
  have hinj  := hli.fintypeLinearCombination_injective
  set e := LinearEquiv.ofInjective T hinj
  let L  := Gr ∘ₗ e.symm.toLinearMap
  let Lc := LinearMap.toContinuousLinearMap L
  have hrank : Module.finrank ℂ (LinearMap.range T) = j + 1 := by
    rw [← e.finrank_eq]; simp
  have hbound : ∀ v ∈ LinearMap.range T, v ≠ 0 →
      rayleigh Ω v ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 := by
    intro v hv _
    obtain ⟨a, rfl⟩ := hv
    have hgrad : IsWeakGradient Ω (T a) (Gr a) := by
      exact IsWeakGradient.sum _ _ _ fun k _ => (hg k).smul (a k)
    have hL : Gr a = Lc ⟨T a, a, rfl⟩ := by
      change Gr a = Gr (e.symm ⟨T a, a, rfl⟩)
      congr 1
      measurability
    have hnorm : ∀ i, ‖Gr a i‖ ≤ ‖Lc‖ * ‖T a‖ := by
      intro i
      refine (norm_le_pi_norm _ i).trans ?_
      rw [hL]
      exact (Lc.le_opNorm _).trans_eq (by rfl)
    have henergy : neumannEnergy Ω (T a) ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := by
      refine (iInf₂_le (Gr a) hgrad).trans ?_
      rw [Fin.sum_univ_two]
      have h' : ∀ i, (‖Gr a i‖₊ : ENNReal) ^ 2 ≤ (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := by
        intro i
        rw [← mul_pow]
        gcongr
        solve_by_elim (maxDepth := 5) [PolyaNeumann.L2]
      calc (‖Gr a 0‖₊) ^ 2 + (‖Gr a 1‖₊) ^ 2
          ≤ (‖Lc‖₊) ^ 2 * (‖T a‖₊) ^ 2 +
            (‖Lc‖₊) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := add_le_add (h' 0) (h' 1)
        _ = _ := by ring
    exact ENNReal.div_le_of_le_mul henergy
  calc neumannEigenvalue Ω j
      ≤ ⨆ (v : L2 Ω) (_ : v ∈ LinearMap.range T) (_ : v ≠ 0), rayleigh Ω v :=
        iInf₂_le (LinearMap.range T) hrank
    _ ≤ 2 * (‖Lc‖₊) ^ 2 := iSup₂_le fun v hv => iSup_le (hbound v hv)
    _ < ⊤ := by
      finiteness

lemma coeFn_sum_smul {ι : Type*} s (a : ι → ℂ) (u : ι → L2 Ω) :
    ((∑ k ∈ s, a k • u k : L2 Ω) : PlaneMap) =ᵐ[volume.restrict Ω]
      fun w => ∑ k ∈ s, a k * (u k : PlaneMap) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    simpa using hw
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (a b • u b) (∑ k ∈ s, a k • u k), Lp.coeFn_smul (a b) (u b),
      ih] with w h1 h2 h3
    simp_all

/-- Lemma 3.3 (finiteness): on a nonempty open set every Neumann min–max value is finite. -/
theorem neumannEigenvalue_lt_top_of_isOpen (hΩ : IsOpen Ω) (hne : Ω.Nonempty) j :
    neumannEigenvalue Ω j < ⊤ := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  set n : ℕ := j + 1
  have hn : (0 : ℝ) < n := by positivity
  set δ : ℝ := r / n
  have hδ  := div_pos hr hn
  let c  := fun k => z + (((k : ℕ) : ℝ) * δ : ℝ)
  let b : ∀ k, ContDiffBump (c k) := fun k => ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let f  := fun k w => ((b k w : ℝ) : ℂ)
  have hf : ∀ k, RealSmooth (f k) := fun k =>
    Complex.ofRealCLM.contDiff.comp (b k).contDiff
  have hfc  := fun k =>
    (b k).hasCompactSupport.comp_left Complex.ofReal_zero
  have hu : ∀ k, MemLp (f k) 2 (volume.restrict Ω) := fun k =>
    ((hf k).continuous.memLp_of_hasCompactSupport (hfc k)).restrict Ω
  have hg : ∀ k i, MemLp (fun w => fderiv ℝ (f k) w (coordDir i)) 2 (volume.restrict Ω) :=
    fun k i => ((((hf k).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hfc k).fderiv_apply (𝕜 := ℝ) _)).restrict Ω
  -- values at the centres
  have hdist : ∀ k m : Fin n, dist (c m) (c k) = |((m : ℕ) : ℝ) - (k : ℕ)| * δ := by
    intro k m
    simp only [c, dist_eq_norm, add_sub_add_left_eq_sub, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    rw [← sub_mul, abs_mul, abs_of_pos hδ]
  have hval : ∀ k m : Fin n, f k (c m) = if k = m then 1 else 0 := by
    intro k m
    split_ifs with h
    · subst h
      simp only [f]
      rw [(b k).one_of_mem_closedBall (Metric.mem_closedBall_self (by
        change 0 ≤ δ / 4; positivity))]
      simp
    · simp only [f]
      rw [(b k).zero_of_le_dist]
      · simp
      · rw [hdist]
        change δ / 2 ≤ _
        have h1 : (1 : ℝ) ≤ |((m : ℕ) : ℝ) - (k : ℕ)| := by
          have hne : (m : ℕ) ≠ (k : ℕ) := fun h' => h (Fin.ext h'.symm)
          rcases Nat.lt_or_gt_of_ne hne with h' | h'
          · rw [abs_sub_comm, abs_of_pos (by
              simp_all)]
            have : ((m : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by exact_mod_cast h'
            linarith
          · rw [abs_of_pos (by
              simp_all)]
            have : ((k : ℕ) : ℝ) + 1 ≤ (m : ℕ) := by exact_mod_cast h'
            linarith
        nlinarith
  have hcmem : ∀ m : Fin n, c m ∈ Ω := by
    intro m
    apply hball
    rw [Metric.mem_ball]
    simp only [c, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have hm : ((m : ℕ) : ℝ) < n := by exact_mod_cast m.2
    calc ((m : ℕ) : ℝ) * δ < n * δ := by gcongr
      _ = r := by simp only [δ]; field_simp
  apply neumannEigenvalue_lt_top_of_family j (fun k => (hu k).toLp _)
    (fun k i => (hg k i).toLp _) _ (fun k => isWeakGradient_of_smooth (hf k) (hu k) (hg k))
  rw [Fintype.linearIndependent_iff]
  intro a ha m
  have hae := coeFn_sum_smul Finset.univ a (fun k => (hu k).toLp _)
  rw [ha] at hae
  have hall :=
    ae_all_iff.mpr fun k => (hu k).coeFn_toLp
  have hF : (fun w => ∑ k, a k * f k w) =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hae, hall, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w h1 h2 h3
    simp_all
  have hcont : Continuous fun w => ∑ k, a k * f k w :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (hf k).continuous
  have heq := Measure.eqOn_open_of_ae_eq hF hΩ hcont.continuousOn continuousOn_const
    (hcmem m)
  simp_all

end PolyaNeumann
