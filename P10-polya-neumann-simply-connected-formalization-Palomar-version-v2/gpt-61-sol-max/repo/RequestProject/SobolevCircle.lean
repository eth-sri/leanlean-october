module

public import RequestProject.PlanarTypes

public import RequestProject.HilbertSchmidt

/-!
# The Fourier model of the Sobolev scale on the circle

Section 6 of the paper works on the Fourier side of `L²(𝕋)`: a function is identified with its
sequence of Fourier coefficients in `ℓ²(ℤ)`, the Sobolev scale is given by the weights
`λₙ = 1 + |n|`, and the operators `Λ^{-s}`, `Π₊`, `|D|^{-1}`, `D^{-1}` are Fourier multipliers.
This file sets up these multipliers on `ℓ²(ℤ)`:

* `diagOp w`: the bounded multiplier by a bounded sequence `w`, with `‖diagOp w‖ ≤ C`;
* `isCompactOperator_diagOp`: a multiplier by a sequence tending to zero is compact; in
  particular `Λ^{-ε}` is compact for `ε > 0` (`isCompactOperator_sobolevSmoothing`), which is the
  compact embedding `H^{s+ε}(𝕋) ↪ H^s(𝕋)` in normalized form;
* `principal_normalized_sub_four_posProj_compact`: the normalized principal part of the periodic
  form, `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2} = 4 Π₊ + (compact)`, which is the Fourier
  computation in the proof of Lemma 6.7.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology
open scoped ENNReal

/-- `ℓ²(ℤ)`, the space of Fourier coefficients of `L²(𝕋)`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

lemma memℓp_two_iff_summable {f : FourierSeq} : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  simp

lemma summable_norm_sq_L2Z (f : L2Z) : Summable fun n => ‖f n‖ ^ 2 :=
  memℓp_two_iff_summable.mp (lp.memℓp f)

lemma norm_sq_L2Z (f : L2Z) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa using this

/-! ### Bounded multipliers -/

section Diag

variable (w : FourierSeq) (C ) (hw : ∀ n, ‖w n‖ ≤ C)
include hw

lemma memℓp_mul_of_bounded (f : L2Z) : Memℓp (fun n => w n * f n) 2 := by
  refine memℓp_two_iff_summable.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_norm_sq_L2Z f).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  gcongr
  exact hw n

/-- The multiplier `f ↦ (wₙ fₙ)ₙ` as a linear map. -/
def diagLin : L2Z →ₗ[ℂ] L2Z where
  toFun f := ⟨fun n => w n * f n, memℓp_mul_of_bounded w C hw f⟩
  map_add' f g := by
    ext n
    change w n * ((f + g : L2Z)) n = w n * f n + w n * g n
    simp [mul_add]
  map_smul' c f := by
    ext <;> simp_all <;> ring

lemma nonneg_of_bounded : 0 ≤ C := (norm_nonneg _).trans (hw 0)

lemma norm_diagLin_le f : ‖diagLin w C hw f‖ ≤ C * ‖f‖ := by
  have hC := nonneg_of_bounded w C hw
  have h1 : ‖diagLin w C hw f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [norm_sq_L2Z, mul_pow, norm_sq_L2Z, ← tsum_mul_left]
    refine (summable_norm_sq_L2Z _).tsum_le_tsum (fun n => ?_)
      ((summable_norm_sq_L2Z f).mul_left _)
    show ‖w n * f n‖ ^ 2 ≤ C ^ 2 * ‖f n‖ ^ 2
    rw [norm_mul, mul_pow]
    gcongr
    exact hw n
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1

/-- The bounded multiplier by a sequence `w` with `‖wₙ‖ ≤ C`. -/
def diagOp : L2Z →L[ℂ] L2Z :=
  (diagLin w C hw).mkContinuous C (norm_diagLin_le w C hw)

@[simp] lemma diagOp_apply f n : (diagOp w C hw f : FourierSeq) n = w n * f n := rfl

lemma norm_diagOp_le : ‖diagOp w C hw‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (nonneg_of_bounded w C hw) _

end Diag

/-- The standard Hilbert basis `(δₙ)` of `ℓ²(ℤ)`. -/
def stdBasisZ  := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ L2Z)

lemma stdBasisZ_apply n : stdBasisZ n = lp.single 2 n 1 := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

section
variable (w : FourierSeq) (C ) (hw : ∀ n, ‖w n‖ ≤ C)
include w C hw

lemma diagOp_stdBasisZ (n : ℤ) :
    diagOp w C hw (stdBasisZ n) = lp.single 2 n (w n) := by
  ext m
  rw [diagOp_apply, stdBasisZ_apply, lp.single_apply, lp.single_apply]
  grind

/-- A multiplier by a finitely supported sequence is compact. -/
lemma isCompactOperator_diagOp_of_finite
    (S : Finset ℤ) (hS : ∀ n ∉ S, w n = 0) : IsCompactOperator (diagOp w C hw) := by
  refine isCompactOperator_of_summable_norm_sq stdBasisZ _ ?_
  refine summable_of_ne_finset_zero (s := S) fun n hn => ?_
  rw [diagOp_stdBasisZ, hS n hn]
  simp

/-- **Compact multipliers.** A multiplier by a bounded sequence tending to zero at infinity is a
compact operator on `ℓ²(ℤ)`. -/
theorem isCompactOperator_diagOp
    (hw0 : Tendsto w cofinite (𝓝 0)) : IsCompactOperator (diagOp w C hw) := by
  classical
  have hcl : IsClosed {f : L2Z →L[ℂ] L2Z | IsCompactOperator f} :=
    isClosed_setOf_isCompactOperator
  show diagOp w C hw ∈ {f : L2Z →L[ℂ] L2Z | IsCompactOperator f}
  rw [← hcl.closure_eq]
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  have hev : ∀ᶠ n in cofinite, ‖w n‖ < ε / 2 := by
    have := hw0.norm
    simpa using this.eventually (gt_mem_nhds (by simpa using half_pos hε))
  rw [Filter.eventually_cofinite] at hev
  set S := hev.toFinset
  set w' : FourierSeq := fun n => if n ∈ S then w n else 0
  have hw' : ∀ n, ‖w' n‖ ≤ C := fun n => by
    by_cases h : n ∈ S
    · simp [w', h, hw n]
    · simp [w', h, nonneg_of_bounded w C hw]
  refine ⟨diagOp w' C hw', isCompactOperator_diagOp_of_finite w' C hw' S
    (fun n hn => by simp [w', hn]), ?_⟩
  rw [dist_eq_norm]
  have hd : ∀ n, ‖w n - w' n‖ ≤ ε / 2 := fun n => by
    by_cases h : n ∈ S
    · simp only [w', h, if_true, sub_self, norm_zero]
      positivity
    · have : ¬ (ε / 2 ≤ ‖w n‖) := by
        measurability
      simp only [w', h, if_false, sub_zero]
      exact (not_le.mp this).le
  have hle : ‖diagOp w C hw - diagOp w' C hw'‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    have heq : (diagOp w C hw - diagOp w' C hw') f =
        diagOp (((w - w'))) (ε / 2) hd f := by
      ext n
      simp [sub_mul]
    rw [heq]
    exact (diagOp _ _ hd).le_opNorm f |>.trans (by gcongr; exact norm_diagOp_le _ _ hd)
  linarith

end


/-! ### The Sobolev weights -/

/-- The Sobolev weight `λₙ = 1 + |n|`. -/
def sobWeight (n : ℤ)  := 1 + |(n : ℝ)|

lemma one_le_sobWeight n : 1 ≤ sobWeight n := by
  simp_all [sobWeight, PolyaNeumann.sobWeight]

lemma sobWeight_pos n : 0 < sobWeight n := lt_of_lt_of_le one_pos (one_le_sobWeight n)

lemma norm_sobWeight_rpow_neg_le {s : ℝ} (hs : 0 ≤ s) n :
    ‖((sobWeight n ^ (-s) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := sobWeight_pos n; positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_sobWeight n) (by linarith)

/-- The smoothing multiplier `Λ^{-s} = (1 + |D|)^{-s}` for `s ≥ 0`. -/
def sobolevSmoothing s hs  :=
  diagOp (fun n => ((sobWeight n ^ (-s) : ℝ) : ℂ)) 1 (norm_sobWeight_rpow_neg_le hs)

lemma tendsto_sobWeight_cofinite : Tendsto sobWeight cofinite atTop := by
  rw [Int.cofinite_eq]
  refine tendsto_sup.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun n : ℤ => (n : ℝ)) atBot atBot := tendsto_intCast_atBot_iff.mpr tendsto_id
    refine tendsto_atTop_add_const_left _ 1 ?_
    exact tendsto_abs_atBot_atTop.comp this
  · have : Tendsto (fun n : ℤ => (n : ℝ)) atTop atTop := tendsto_intCast_atTop_iff.mpr tendsto_id
    refine tendsto_atTop_add_const_left _ 1 ?_
    exact tendsto_abs_atTop_atTop.comp this

/-- **Compact embedding.** For `ε > 0`, `Λ^{-ε}` is compact on `ℓ²(ℤ)`; equivalently the
inclusion `H^{s+ε}(𝕋) ↪ H^s(𝕋)` is compact. -/
theorem isCompactOperator_sobolevSmoothing  (hε : 0 < ε) :
    IsCompactOperator (sobolevSmoothing ε hε.le) := by
  refine isCompactOperator_diagOp _ _ _ ?_
  have h  :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_sobWeight_cofinite
  have := (Complex.continuous_ofReal.tendsto 0).comp h
  simpa [Function.comp_def] using this

/-! ### The normalized principal part of the periodic form (Lemma 6.7) -/

/-- The Fourier projection `Π₊` onto the positive modes `n > 0`. -/
def posProj : L2Z →L[ℂ] L2Z :=
  diagOp (fun n => if 0 < n then 1 else 0) 1 (fun n => by split_ifs <;> simp)

/-- The multiplier of `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2}`: for `n ≠ 0` it is
`(1 + |n|) (2/|n| + 2/n)`, i.e. `4 (1 + n)/n` for `n > 0` and `0` for `n < 0`; the constant mode
is set to zero. -/
def principalSymbol n  :=
  if n = 0 then 0 else ((sobWeight n * (2 / |(n : ℝ)| + 2 / (n : ℝ)) : ℝ) : ℂ)

lemma principalSymbol_pos  (hn : 0 < n) : principalSymbol n = 4 + 4 / (n : ℂ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp  [principalSymbol, hn.ne', sobWeight, abs_of_pos hn']
  push_cast
  field_simp
  ring

lemma principalSymbol_neg  (hn : n < 0) : principalSymbol n = 0 := by
  have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
  simp only [principalSymbol, hn.ne, if_false, abs_of_neg hn']
  rw [div_neg, neg_add_cancel, mul_zero, Complex.ofReal_zero]

lemma norm_principalSymbol_le n : ‖principalSymbol n‖ ≤ 8 := by
  rcases lt_trichotomy n 0 with h | h | h
  · simp [principalSymbol_neg h]
  · simp [principalSymbol, h]
  · rw [principalSymbol_pos h]
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast h
    calc ‖4 + 4 / (n : ℂ)‖ ≤ ‖4‖ + ‖4 / (n : ℂ)‖ := norm_add_le _ _
      _ ≤ 4 + 4 := by
        gcongr
        · simp
        · rw [norm_div, Complex.norm_intCast]
          simp  
          rw [abs_of_pos (by linarith)]
          bound
      _ = 8 := by norm_num

/-- The normalized principal part `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2}` as a multiplier. -/
def principalNormalized  := diagOp principalSymbol 8 norm_principalSymbol_le

/-- **Lemma 6.7, principal part.** `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2} = 4 Π₊ + C` with `C`
compact: the difference is the multiplier `4/n` on the positive modes, which tends to zero. -/
theorem principal_normalized_sub_four_posProj_compact :
    IsCompactOperator (principalNormalized - (4 : ℂ) • posProj) := by
  have hb : ∀ n : ℤ, ‖principalSymbol n - 4 * (if 0 < n then 1 else 0)‖ ≤ 12 := fun n => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_principalSymbol_le n
    have h2 : ‖(4 : ℂ) * (if 0 < n then 1 else 0)‖ ≤ 4 := by split_ifs <;> simp
    linarith
  have heq : principalNormalized - (4 : ℂ) • posProj =
      diagOp (fun n => principalSymbol n - 4 * (if 0 < n then 1 else 0)) 12 hb := by
    ext f n
    simp only [ContinuousLinearMap.sub_apply, lp.coeFn_sub]
    simp [principalNormalized, posProj, sub_mul]
  rw [heq]
  refine isCompactOperator_diagOp _ _ _ ?_
  have hev : (fun n : ℤ => principalSymbol n - 4 * (if 0 < n then 1 else 0)) =
      fun n : ℤ => if 0 < n then 4 / (n : ℂ) else 0 := by
    funext n
    rcases lt_trichotomy n 0 with h | h | h
    · simp [principalSymbol_neg h, not_lt.mpr h.le]
    · simp [principalSymbol, h]
    · simp [principalSymbol_pos h, h]
  rw [hev]
  have h1 : Tendsto (fun n : ℤ => ‖(n : ℂ)‖) cofinite atTop := by
    have := tendsto_atTop_add_const_right _ (-1) tendsto_sobWeight_cofinite
    simp_all [sobWeight]
  have h2 := (tendsto_const_nhds (x := 4)).div_atTop h1
  refine squeeze_zero_norm (fun n => ?_) h2
  split_ifs with h
  · simp
  · simp only [norm_zero]
    positivity

end PolyaNeumann
