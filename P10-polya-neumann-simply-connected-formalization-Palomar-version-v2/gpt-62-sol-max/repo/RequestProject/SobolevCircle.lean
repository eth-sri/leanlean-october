module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
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

lemma int_tsum_eq_halves (a : ℤ → ℝ) (b : ℕ ⊕ ℕ → ℝ)
    (hb : Summable b) (hzero : a 0 = 0)
    (hpos : ∀ m : ℕ, a ((m + 1 : ℕ) : ℤ) = b (Sum.inl m))
    (hneg : ∀ m : ℕ, a (-((m + 1 : ℕ) : ℤ)) = b (Sum.inr m)) :
    Summable a ∧ (∑' n : ℤ, a n) = ∑' j : ℕ ⊕ ℕ, b j := by
  have hbl := hb.comp_injective Sum.inl_injective
  have hbr := hb.comp_injective Sum.inr_injective
  have hpos' :=
    hbl.congr (fun m => (hpos m).symm)
  have hpos0 : Summable (fun m : ℕ => a (m : ℤ)) :=
    (summable_nat_add_iff 1).mp hpos'
  have hneg' :=
    hbr.congr (fun m => (hneg m).symm)
  have hneg0 : Summable (fun m : ℕ => a (-(m + 1 : ℤ))) := by
    assumption
  refine ⟨Summable.of_nat_of_neg_add_one hpos0 hneg0, ?_⟩
  rw [tsum_of_nat_of_neg_add_one hpos0 hneg0, hpos0.tsum_eq_zero_add]
  simp only [Nat.cast_zero, hzero, zero_add]
  calc
    _ = (∑' m : ℕ, b (Sum.inl m)) + ∑' m : ℕ, b (Sum.inr m) := by simp_all
    _ = _ := (hbl.tsum_sum hbr).symm

open Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

/-- `ℓ²(ℤ)`, the space of Fourier coefficients of `L²(𝕋)`. -/
abbrev L2Z := lp (fun _ : ℤ => ℂ) 2

lemma memℓp_two_iff_summable {f : ℤ → ℂ} : Memℓp f 2 ↔ Summable fun n => ‖f n‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp

lemma summable_norm_sq_L2Z (f : L2Z) : Summable fun n => ‖f n‖ ^ 2 :=
  memℓp_two_iff_summable.mp (lp.memℓp f)

lemma norm_sq_L2Z (f : L2Z) : ‖f‖ ^ 2 = ∑' n, ‖f n‖ ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) f
  simpa using this

/-! ### Bounded multipliers -/

section Diag

variable (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
include hw

lemma memℓp_mul_of_bounded (f : L2Z) : Memℓp (fun n => w n * f n) 2 := by
  refine memℓp_two_iff_summable.mpr ?_
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_norm_sq_L2Z f).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  gcongr
  tauto

/-- The multiplier `f ↦ (wₙ fₙ)ₙ` as a linear map. -/
def diagLin : L2Z →ₗ[ℂ] L2Z where
  toFun f := ⟨fun n => w n * f n, memℓp_mul_of_bounded w C hw f⟩
  map_add' f g := by
    ext n
    change w n * ((f + g : L2Z) : ℤ → ℂ) n = w n * f n + w n * g n
    simp [mul_add]
  map_smul' c f := by
    ext n
    simp  [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    ring

lemma nonneg_of_bounded : 0 ≤ C := (norm_nonneg _).trans (hw 0)

lemma norm_diagLin_le (f : L2Z) : ‖diagLin w C hw f‖ ≤ C * ‖f‖ := by
  have hC := nonneg_of_bounded w C hw
  have h1 : ‖diagLin w C hw f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [norm_sq_L2Z, mul_pow, norm_sq_L2Z, ← tsum_mul_left]
    refine (summable_norm_sq_L2Z _).tsum_le_tsum (fun n => ?_)
      ((summable_norm_sq_L2Z f).mul_left _)
    show ‖w n * f n‖ ^ 2 ≤ C ^ 2 * ‖f n‖ ^ 2
    rw [norm_mul, mul_pow]
    gcongr
    tauto
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h1

/-- The bounded multiplier by a sequence `w` with `‖wₙ‖ ≤ C`. -/
def diagOp : L2Z →L[ℂ] L2Z :=
  (diagLin w C hw).mkContinuous C (norm_diagLin_le w C hw)

@[simp] lemma diagOp_apply (f : L2Z) (n : ℤ) : (diagOp w C hw f : ℤ → ℂ) n = w n * f n := rfl

lemma norm_diagOp_le : ‖diagOp w C hw‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (nonneg_of_bounded w C hw) _

end Diag

/-- The standard Hilbert basis `(δₙ)` of `ℓ²(ℤ)`. -/
def stdBasisZ : HilbertBasis ℤ ℂ L2Z := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ L2Z)

lemma stdBasisZ_apply (n : ℤ) : stdBasisZ n = lp.single 2 n 1 := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

lemma inner_stdBasisZ (n : ℤ) (b : L2Z) : ⟪stdBasisZ n, b⟫_ℂ = b n := by
  simp [stdBasisZ_apply, lp.inner_single_left]

section

variable (w : ℤ → ℂ) (C : ℝ) (hw : ∀ n, ‖w n‖ ≤ C)
include w C hw

lemma diagOp_stdBasisZ  (n : ℤ) :
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
    simpa using this.eventually (gt_mem_nhds (by simp_all))
  rw [Filter.eventually_cofinite] at hev
  set S := hev.toFinset
  set w' : ℤ → ℂ := fun n => if n ∈ S then w n else 0
  have hw' : ∀ n, ‖w' n‖ ≤ C := fun n => by
    by_cases h : n ∈ S
    · simp [w', h, hw n]
    · simp [w', h, nonneg_of_bounded w C hw]
  refine ⟨diagOp w' C hw', isCompactOperator_diagOp_of_finite w' C hw' S
    (fun n hn => by lia), ?_⟩
  rw [dist_eq_norm]
  have hd : ∀ n, ‖w n - w' n‖ ≤ ε / 2 := fun n => by
    by_cases h : n ∈ S
    · simp  [w', h, if_true, sub_self, norm_zero]
      positivity
    · have : ¬ (ε / 2 ≤ ‖w n‖) := by
        intro h'
        exact h (by simpa [S] using h')
      simp  [w', h, if_false, sub_zero]
      linarith
  have hle : ‖diagOp w C hw - diagOp w' C hw'‖ ≤ ε / 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    have heq : (diagOp w C hw - diagOp w' C hw') f =
        diagOp (fun n => w n - w' n) (ε / 2) hd f := by
      ext n
      simp [sub_mul]
    rw [heq]
    exact (diagOp _ _ hd).le_opNorm f |>.trans (by gcongr; exact norm_diagOp_le _ _ hd)
  linarith

end

/-! ### The Sobolev weights -/

section

variable (n : ℤ)
include n

/-- The Sobolev weight `λₙ = 1 + |n|`. -/
def sobWeight  : ℝ := 1 + |(n : ℝ)|

lemma one_le_sobWeight  : 1 ≤ sobWeight n := by simp [sobWeight]

lemma sobWeight_pos  : 0 < sobWeight n := lt_of_lt_of_le one_pos (one_le_sobWeight n)

end

lemma norm_sobWeight_rpow_neg_le {s : ℝ} (hs : 0 ≤ s) (n : ℤ) :
    ‖((sobWeight n ^ (-s) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have := sobWeight_pos n; positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_sobWeight n) (by linarith)

/-- The smoothing multiplier `Λ^{-s} = (1 + |D|)^{-s}` for `s ≥ 0`. -/
def sobolevSmoothing (s : ℝ) (hs : 0 ≤ s) : L2Z →L[ℂ] L2Z :=
  diagOp (fun n => ((sobWeight n ^ (-s) : ℝ) : ℂ)) 1 (norm_sobWeight_rpow_neg_le hs)

lemma sobolevSmoothing_injective (s : ℝ) (hs : 0 ≤ s) : Function.Injective (sobolevSmoothing s hs) := by
  intro b c h
  apply lp.ext
  funext n
  have hn := congrArg (fun v : L2Z => v n) h
  simp only [sobolevSmoothing, diagOp_apply] at hn
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (sobWeight_pos n) _).ne') hn

lemma sobWeight_neg_nat (k : ℕ) : sobWeight (-(k : ℤ)) = ((k + 1 : ℕ) : ℝ) := by
  simp [sobWeight, abs_of_nonneg] ; ring

lemma sobolevSmoothing_one_apply (b : L2Z) (n : ℤ) :
    sobolevSmoothing 1 zero_le_one b n = (sobWeight n : ℂ)⁻¹ * b n := by
  simp [sobolevSmoothing, diagOp_apply, Real.rpow_neg_one, Complex.ofReal_inv]

lemma inner_sobolevSmoothing_half (q t b : L2Z)
    (hq : ∀ n, q n = (Real.sqrt (sobWeight n) : ℂ) * t n) :
    ⟪q, sobolevSmoothing (1 / 2 : ℝ) (by norm_num) b⟫_ℂ = ⟪t, b⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun n => ?_
  simp only [RCLike.inner_apply', hq, sobolevSmoothing, diagOp_apply, map_mul, Complex.conj_ofReal]
  have h : (Real.sqrt (sobWeight n) : ℂ) * ((sobWeight n ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) = 1 := by
    rw [Real.rpow_neg (sobWeight_pos n).le, ← Real.sqrt_eq_rpow, Complex.ofReal_inv]
    exact mul_inv_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr (sobWeight_pos n)).ne')
  linear_combination (conj (t n) * b n) * h

lemma tendsto_sobWeight_cofinite : Tendsto sobWeight cofinite atTop := by
  rw [Int.cofinite_eq]
  exact tendsto_sup.mpr ⟨have this := tendsto_intCast_atBot_iff.mpr tendsto_id; tendsto_atTop_add_const_left atBot 1 (Tendsto.comp tendsto_abs_atBot_atTop this), have this := tendsto_intCast_atTop_iff.mpr tendsto_id; tendsto_atTop_add_const_left atTop 1 (Tendsto.comp tendsto_abs_atTop_atTop this)⟩

/-- **Compact embedding.** For `ε > 0`, `Λ^{-ε}` is compact on `ℓ²(ℤ)`; equivalently the
inclusion `H^{s+ε}(𝕋) ↪ H^s(𝕋)` is compact. -/
theorem isCompactOperator_sobolevSmoothing {ε : ℝ} (hε : 0 < ε) :
    IsCompactOperator (sobolevSmoothing ε hε.le) := by
  refine isCompactOperator_diagOp _ _ _ ?_
  have h :=
    (tendsto_rpow_neg_atTop hε).comp tendsto_sobWeight_cofinite
  have := (Complex.continuous_ofReal.tendsto 0).comp h
  assumption

/-! ### The normalized principal part of the periodic form (Lemma 6.7) -/

/-- The Fourier projection `Π₊` onto the positive modes `n > 0`. -/
def posProj : L2Z →L[ℂ] L2Z :=
  diagOp (fun n => if 0 < n then 1 else 0) 1 (fun n => by aesop)

/-- The multiplier of `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2}`: for `n ≠ 0` it is
`(1 + |n|) (2/|n| + 2/n)`, i.e. `4 (1 + n)/n` for `n > 0` and `0` for `n < 0`; the constant mode
is set to zero. -/
def principalSymbol (n : ℤ) : ℂ :=
  if n = 0 then 0 else ((sobWeight n * (2 / |(n : ℝ)| + 2 / (n : ℝ)) : ℝ) : ℂ)

lemma principalSymbol_pos {n : ℤ} (hn : 0 < n) : principalSymbol n = 4 + 4 / (n : ℂ) := by
  have hn' : (0 : ℝ) < n := by positivity
  have hc : (n : ℂ) ≠ 0 := by aesop
  simp only [principalSymbol, hn.ne', sobWeight, abs_of_pos hn']
  push_cast
  field_simp
  ring

lemma principalSymbol_neg {n : ℤ} (hn : n < 0) : principalSymbol n = 0 := by
  have hn' : (n : ℝ) < 0 := by norm_cast
  simp only [principalSymbol, hn.ne, if_false, abs_of_neg hn']
  rw [div_neg, neg_add_cancel, mul_zero, Complex.ofReal_zero]

lemma norm_principalSymbol_le (n : ℤ) : ‖principalSymbol n‖ ≤ 8 := by
  rcases lt_trichotomy n 0 with h | h | h
  · simp [principalSymbol_neg h]
  simp [principalSymbol, h]
  · rw [principalSymbol_pos h]
    have hn : (1 : ℝ) ≤ n := by norm_cast
    calc ‖(4 : ℂ) + 4 / (n : ℂ)‖ ≤ ‖(4 : ℂ)‖ + ‖4 / (n : ℂ)‖ := norm_add_le _ _
      _ ≤ 4 + 4 := by
        gcongr
        simp
        · rw [norm_div, Complex.norm_intCast]
          simp  
          rw [abs_of_pos (by linarith)]
          rw [div_le_iff₀ (by linarith)]
          nlinarith
      _ = 8 := by norm_num

/-- The normalized principal part `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2}` as a multiplier. -/
def principalNormalized : L2Z →L[ℂ] L2Z := diagOp principalSymbol 8 norm_principalSymbol_le

/-- **Lemma 6.7, principal part.** `Λ^{1/2} (2|D|^{-1} + 2D^{-1}) Λ^{1/2} = 4 Π₊ + C` with `C`
compact: the difference is the multiplier `4/n` on the positive modes, which tends to zero. -/
theorem principal_normalized_sub_four_posProj_compact :
    IsCompactOperator (principalNormalized - (4 : ℂ) • posProj) := by
  have hb : ∀ n : ℤ, ‖principalSymbol n - 4 * (if 0 < n then 1 else 0)‖ ≤ 12 := fun n => by
    refine (norm_sub_le _ _).trans ?_
    have h1 := norm_principalSymbol_le n
    have h2 : ‖(4 : ℂ) * (if 0 < n then 1 else 0)‖ ≤ 4 := by aesop
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
    refine this.congr fun n => ?_
    simp [sobWeight]
  have h2 := (tendsto_const_nhds (x := (4 : ℝ))).div_atTop h1
  refine squeeze_zero_norm (fun n => ?_) h2
  split_ifs with h
  simp
  · simp only [norm_zero]
    positivity

end PolyaNeumann
