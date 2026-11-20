module

public import RequestProject.Spectrum

/-!
# Finiteness of the Neumann eigenvalues

For a nonempty open set `Ω`, every min–max value `μ_j(Ω)` is finite.  We exhibit a
`(j+1)`-dimensional space of smooth compactly supported bumps on which the Rayleigh
quotient is bounded.
-/

@[expose] public section

open MeasureTheory Set
open scoped ComplexConjugate

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ}

section

variable {φ : ℂ → ℂ} (hφ : TestFunction Ω φ)
include φ hφ

lemma TestFunction.memLp_fderiv  (v : ℂ) :
    MemLp (fun w => fderiv ℝ φ w v) 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (((hs.continuous_fderiv (by simp)).clm_apply continuous_const :).memLp_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) v)).restrict Ω

lemma TestFunction.memLp  :
    MemLp φ 2 (volume.restrict Ω) := by
  obtain ⟨hs, hc, -⟩ := hφ
  exact (hs.continuous.memLp_of_hasCompactSupport hc).restrict Ω

end

lemma TestFunction.add {D : Set ℂ} {φ ψ : ℂ → ℂ} (hφ : TestFunction D φ)
    (hψ : TestFunction D ψ) : TestFunction D (fun z => φ z + ψ z) :=
  ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)⟩

lemma TestFunction.const_mul {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) (c : ℂ) :
    TestFunction D (fun z => c * φ z) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.1.mul_left, (tsupport_mul_subset_right).trans hφ.2.2⟩

/-- Complex conjugates of test functions are test functions. -/
lemma TestFunction.conj {D : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction D φ) :
    TestFunction D (fun z => conj (φ z)) := by
  refine ⟨Complex.conjCLE.contDiff.comp hφ.1, hφ.2.1.comp_left (by simp), ?_⟩
  exact (tsupport_comp_subset (g := fun z : ℂ => conj z) (by simp) φ).trans hφ.2.2

lemma integral_norm_sq_lp {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℂ 2 μ) : ∫ x, ‖u x‖ ^ 2 ∂μ = ‖u‖ ^ 2 := by
  have h := congrArg RCLike.re (L2.inner_def (𝕜 := ℂ) u u)
  rw [inner_self_eq_norm_sq, ← integral_re (L2.integrable_inner u u)] at h
  simpa only [inner_self_eq_norm_sq, RCLike.ofReal_re] using h.symm

lemma norm_sq_toLp_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ :=
  (integral_norm_sq_lp _).symm.trans (integral_congr_ae (hf.coeFn_toLp.fun_comp (‖·‖ ^ 2)))

/-- Integration against a fixed L² test is a continuous linear functional. -/
def lpIntegralPair {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) : Lp ℂ 2 μ →L[ℂ] ℂ :=
  innerSL ℂ (hf.star.toLp (fun z => conj (f z)))

theorem lpIntegralPair_apply {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) (u : Lp ℂ 2 μ) : lpIntegralPair hf u = ∫ z, u z * f z ∂μ := by
  rw [lpIntegralPair, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (f := fun z => conj (f z)) hf.star] with x hx
  simp [RCLike.inner_apply, hx]

lemma norm_lpIntegralPair_apply_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : MemLp f 2 μ) (u : Lp ℂ 2 μ) : ‖lpIntegralPair hf u‖ ≤ ‖u‖ * (eLpNorm f 2 μ).toReal := by
  rw [lpIntegralPair, innerSL_apply_apply, mul_comm]
  simpa only [Lp.norm_toLp, show (fun z => conj (f z)) = star f from rfl, eLpNorm_star] using norm_inner_le_norm (𝕜 := ℂ) (hf.star.toLp (fun z => conj (f z))) u

/-- Cauchy–Schwarz for the bilinear integral, via the `L²` pairing. -/
lemma norm_integral_mul_le_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B : α → ℂ}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    ‖∫ x, A x * B x ∂μ‖ ≤ (eLpNorm A 2 μ).toReal * (eLpNorm B 2 μ).toReal := by
  have h := norm_lpIntegralPair_apply_le hB (hA.toLp A)
  rw [lpIntegralPair_apply, Lp.norm_toLp] at h
  convert h using 2
  exact integral_congr_ae (hA.coeFn_toLp.mono fun x hx => congrArg (· * B x) hx.symm)

lemma ae_eq_zero_on_of_integral_mul_test {μ : Measure ℂ} {W : Set ℂ} (hW : IsOpen W)
    {f : ℂ → ℂ} (hf : LocallyIntegrableOn f W μ)
    (h : ∀ φ, TestFunction W φ → ∫ x, f x * φ x ∂μ = 0) :
    ∀ᵐ x ∂μ, x ∈ W → f x = 0 := by
  apply hW.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
  intro ψ hs hc hw
  simpa only [Complex.real_smul, mul_comm] using
    h (fun x => (ψ x : ℂ)) ⟨Complex.ofRealCLM.contDiff.comp hs,
      hc.comp_left Complex.ofReal_zero, (tsupport_comp_subset Complex.ofReal_zero ψ).trans hw⟩

lemma eq_zero_of_pairing_test {W : Set ℂ} (hW : IsOpen W) (f : L2 W)
    (h : ∀ φ (hφ : TestFunction W φ), lpIntegralPair hφ.memLp f = 0) : f = 0 := by
  have hloc := (Lp.memLp f).locallyIntegrable one_le_two
  have hf := ae_eq_zero_on_of_integral_mul_test hW (hloc.locallyIntegrableOn W)
    (fun φ hφ => (lpIntegralPair_apply hφ.memLp f).symm.trans (h φ hφ))
  apply Lp.ext
  filter_upwards [hf, ae_restrict_mem hW.measurableSet, Lp.coeFn_zero ℂ 2 (volume.restrict W)]
    with x hx hxW h0
  exact (hx hxW).trans h0.symm

lemma inner_toLp_test {W : Set ℂ} {φ : ℂ → ℂ} (hφ : TestFunction W φ) (f : L2 W) :
    inner ℂ (hφ.memLp.toLp φ) f = lpIntegralPair hφ.conj.memLp f := by
  rw [lpIntegralPair_apply, L2.inner_def]
  exact integral_congr_ae (hφ.memLp.coeFn_toLp.mono fun x hx => by simp [RCLike.inner_apply, hx])

/-- The image of the compactly supported smooth tests in `L²(W)`. -/
private def l2TestSubmodule (W : Set ℂ) : Submodule ℂ (L2 W) where
  carrier := {f | ∃ (φ : ℂ → ℂ) (hφ : TestFunction W φ), hφ.memLp.toLp φ = f}
  zero_mem' := by
    have h : TestFunction W 0 := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
    exact ⟨0, h, MemLp.toLp_zero _⟩
  add_mem' := by
    rintro _ _ ⟨φ, hφ, rfl⟩ ⟨ψ, hψ, rfl⟩
    exact ⟨φ + ψ, hφ.add hψ, hφ.memLp.toLp_add hψ.memLp⟩
  smul_mem' := by
    rintro c _ ⟨φ, hφ, rfl⟩
    exact ⟨c • φ, hφ.const_mul c, hφ.memLp.toLp_const_smul c⟩

lemma dense_l2_tests {W : Set ℂ} (hW : IsOpen W) :
    Dense {f : L2 W | ∃ (φ : ℂ → ℂ) (hφ : TestFunction W φ), hφ.memLp.toLp φ = f} := by
  change Dense (l2TestSubmodule W : Set (L2 W))
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply eq_bot_iff.mpr
  intro f hf
  rw [Submodule.mem_bot]
  apply eq_zero_of_pairing_test hW f
  intro φ hφ
  have he := ((l2TestSubmodule W).mem_orthogonal f).mp hf _ ⟨_, hφ.conj, rfl⟩
  rw [inner_toLp_test hφ.conj, lpIntegralPair_apply] at he
  simpa only [lpIntegralPair_apply, starRingEnd_apply, star_star] using he

lemma isWeakGradient_iff_pair {u : L2 Ω} {g : Fin 2 → L2 Ω} :
    IsWeakGradient Ω u g ↔ ∀ φ (hφ : TestFunction Ω φ) i,
      lpIntegralPair (hφ.memLp_fderiv (coordDir i)) u = -lpIntegralPair hφ.memLp (g i) := by
  simp_rw [lpIntegralPair_apply]
  rfl

lemma IsWeakGradient.add {u v : L2 Ω} {g h : Fin 2 → L2 Ω} (hu : IsWeakGradient Ω u g)
    (hv : IsWeakGradient Ω v h) : IsWeakGradient Ω (u + v) (g + h) := by
  rw [isWeakGradient_iff_pair] at hu hv ⊢
  intro φ hφ i
  simp [hu φ hφ i, hv φ hφ i, neg_add, add_comm]

lemma IsWeakGradient.smul {u : L2 Ω} {g : Fin 2 → L2 Ω} (c : ℂ) (hu : IsWeakGradient Ω u g) :
    IsWeakGradient Ω (c • u) (c • g) := by
  rw [isWeakGradient_iff_pair] at hu ⊢
  intro φ hφ i
  simp [hu φ hφ i]

lemma isWeakGradient_zero : IsWeakGradient Ω 0 0 := by simp [isWeakGradient_iff_pair]

lemma IsWeakGradient.sum {ι : Type*} (s : Finset ι) (u : ι → L2 Ω) (g : ι → Fin 2 → L2 Ω)
    (h : ∀ k ∈ s, IsWeakGradient Ω (u k) (g k)) :
    IsWeakGradient Ω (∑ k ∈ s, u k) (∑ k ∈ s, g k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeakGradient_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- The classical gradient of a `C¹` function is its weak gradient. -/
lemma isWeakGradient_of_contDiff_one {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) := by
  intro φ hφ i
  obtain ⟨hs, hφc, hsupp⟩ := hφ
  have e1' : (fun w => ((hu.toLp f : L2 Ω) : ℂ → ℂ) w * fderiv ℝ φ w (coordDir i))
      =ᵐ[volume.restrict Ω] fun w => f w * fderiv ℝ φ w (coordDir i) := by
    filter_upwards [hu.coeFn_toLp] with x; simp_all
  have e2' : (fun w => (((hg i).toLp _ : L2 Ω) : ℂ → ℂ) w * φ w)
      =ᵐ[volume.restrict Ω] fun w => fderiv ℝ f w (coordDir i) * φ w := by
    filter_upwards [(hg i).coeFn_toLp] with x; simp_all
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
    ((hfd.mul hs.continuous).integrable_of_hasCompactSupport (hφc.mul_left))
    ((hf.continuous.mul hφd).integrable_of_hasCompactSupport
      ((hφc.fderiv_apply (𝕜 := ℝ) _).mul_left))
    ((hf.continuous.mul hs.continuous).integrable_of_hasCompactSupport hφc.mul_left)
    (fun x _ => (hf.differentiable (by simp)) x) (fun x _ => (hs.differentiable (by simp)) x)

/-- The classical gradient of a smooth compactly supported function is its weak gradient. -/
lemma isWeakGradient_of_smooth {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : MemLp f 2 (volume.restrict Ω))
    (hg : ∀ i, MemLp (fun w => fderiv ℝ f w (coordDir i)) 2 (volume.restrict Ω)) :
    IsWeakGradient Ω (hu.toLp f) (fun i => (hg i).toLp _) :=
  isWeakGradient_of_contDiff_one (hf.of_le (by simp)) hu hg

/-- If `u_0, …, u_j ∈ H¹(Ω)` are linearly independent in `L²(Ω)`, then `μ_j(Ω) < ∞`. -/
lemma neumannEigenvalue_lt_top_of_family (j : ℕ) (u : Fin (j + 1) → L2 Ω)
    (g : Fin (j + 1) → Fin 2 → L2 Ω) (hli : LinearIndependent ℂ u)
    (hg : ∀ k, IsWeakGradient Ω (u k) (g k)) : neumannEigenvalue Ω j < ⊤ := by
  set T := Fintype.linearCombination ℂ u
  set Gr := Fintype.linearCombination ℂ g
  have hinj := hli.fintypeLinearCombination_injective
  set e := LinearEquiv.ofInjective T hinj
  let L := Gr ∘ₗ e.symm.toLinearMap
  let Lc := LinearMap.toContinuousLinearMap L
  have hrank : Module.finrank ℂ (LinearMap.range T) = j + 1 := by
    rw [← e.finrank_eq]; simp
  have hbound : ∀ v ∈ LinearMap.range T, v ≠ 0 →
      rayleigh Ω v ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 := by
    intro v hv _
    obtain ⟨a, rfl⟩ := hv
    have hgrad : IsWeakGradient Ω (T a) (Gr a) := by
      simp only [Gr]
      exact IsWeakGradient.sum _ _ _ fun k _ => (hg k).smul (a k)
    have hL : Gr a = Lc ⟨T a, a, rfl⟩ := by
      change Gr a = Gr (e.symm ⟨T a, a, rfl⟩)
      congr 1
      apply e.injective
      rw [LinearEquiv.apply_symm_apply]
      rfl
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
        tauto
      calc (‖Gr a 0‖₊ : ENNReal) ^ 2 + (‖Gr a 1‖₊ : ENNReal) ^ 2
          ≤ (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 +
            (‖Lc‖₊ : ENNReal) ^ 2 * (‖T a‖₊ : ENNReal) ^ 2 := add_le_add (h' 0) (h' 1)
        _ = _ := by ring
    exact ENNReal.div_le_of_le_mul henergy
  calc neumannEigenvalue Ω j
      ≤ ⨆ (v : L2 Ω) (_ : v ∈ LinearMap.range T) (_ : v ≠ 0), rayleigh Ω v :=
        iInf₂_le (LinearMap.range T) hrank
    _ ≤ 2 * (‖Lc‖₊ : ENNReal) ^ 2 := iSup₂_le fun v hv => iSup_le fun hv0 => hbound v hv hv0
    _ < ⊤ := by tauto

lemma coeFn_sum_smul {ι : Type*} (s : Finset ι) (a : ι → ℂ) (u : ι → L2 Ω) :
    ((∑ k ∈ s, a k • u k : L2 Ω) : ℂ → ℂ) =ᵐ[volume.restrict Ω]
      fun w => ∑ k ∈ s, a k * (u k : ℂ → ℂ) w := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w hw
    assumption
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    filter_upwards [Lp.coeFn_add (a b • u b) (∑ k ∈ s, a k • u k), Lp.coeFn_smul (a b) (u b),
      ih] with w h1 h2 h3
    simp_all

/-- Lemma 3.3 (finiteness): on a nonempty open set every Neumann min–max value is finite. -/
theorem neumannEigenvalue_lt_top_of_isOpen (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (j : ℕ) :
    neumannEigenvalue Ω j < ⊤ := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ z hz
  set n : ℕ := j + 1
  have hn : (0 : ℝ) < n := by positivity
  set δ : ℝ := r / n
  have hδ := div_pos hr hn
  let c : Fin n → ℂ := fun k => z + (((k : ℕ) : ℝ) * δ : ℝ)
  let b : ∀ k, ContDiffBump (c k) := fun k => ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  let f := fun k w => ((b k w : ℝ) : ℂ)
  have hf : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k) := fun k =>
    Complex.ofRealCLM.contDiff.comp (b k).contDiff
  have hfc := fun k =>
    (b k).hasCompactSupport.comp_left Complex.ofReal_zero
  have hu : ∀ k, MemLp (f k) 2 (volume.restrict Ω) := fun k =>
    ((hf k).continuous.memLp_of_hasCompactSupport (hfc k)).restrict Ω
  have hg : ∀ k i, MemLp (fun w => fderiv ℝ (f k) w (coordDir i)) 2 (volume.restrict Ω) :=
    fun k i => ((((hf k).continuous_fderiv (by simp)).clm_apply continuous_const :
      Continuous fun w => fderiv ℝ (f k) w (coordDir i)).memLp_of_hasCompactSupport
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
      rw [(b k).one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))]
      simp
    · simp only [f]
      rw [(b k).zero_of_le_dist]
      rfl
      · rw [hdist]
        change δ / 2 ≤ _
        have h1 : (1 : ℝ) ≤ |((m : ℕ) : ℝ) - (k : ℕ)| := by
          have hne : (m : ℕ) ≠ (k : ℕ) := fun h' => h (Fin.ext h'.symm)
          rcases Nat.lt_or_gt_of_ne hne with h' | h'
          · rw [abs_sub_comm, abs_of_pos (by simp_all)]
            have : ((m : ℕ) : ℝ) + 1 ≤ (k : ℕ) := by norm_cast
            linarith
          · rw [abs_of_pos (by simp_all)]
            have : ((k : ℕ) : ℝ) + 1 ≤ (m : ℕ) := by norm_cast
            linarith
        nlinarith
  have hcmem : ∀ m : Fin n, c m ∈ Ω := by
    intro m
    apply hball
    rw [Metric.mem_ball]
    simp only [c, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have hm : ((m : ℕ) : ℝ) < n := by simp
    calc ((m : ℕ) : ℝ) * δ < n * δ := by gcongr
      _ = r := by grind
  apply neumannEigenvalue_lt_top_of_family j (fun k => (hu k).toLp _)
    (fun k i => (hg k i).toLp _) _ (fun k => isWeakGradient_of_smooth (hf k) (hu k) (hg k))
  rw [Fintype.linearIndependent_iff]
  intro a ha m
  have hae := coeFn_sum_smul Finset.univ a (fun k => (hu k).toLp _)
  rw [ha] at hae
  have hall :=
    ae_all_iff.mpr fun k => (hu k).coeFn_toLp
  have hF : (fun w => ∑ k, a k * f k w) =ᵐ[volume.restrict Ω] fun _ => 0 := by
    filter_upwards [hae, hall, Lp.coeFn_zero ℂ 2 (volume.restrict Ω)] with w h1 h2 h3
    simp_all
  have hcont : Continuous fun w => ∑ k, a k * f k w :=
    continuous_finset_sum _ fun k _ => continuous_const.mul (hf k).continuous
  have heq := Measure.eqOn_open_of_ae_eq hF hΩ hcont.continuousOn continuousOn_const
    (hcmem m)
  simp_all

end PolyaNeumann

end
