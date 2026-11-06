module

public import RequestProject.SobolevMultiplier

/-!
# The boundary part of the transmutation estimates (Lemmas 5.2 and 5.3)

In conformal coordinates the paper's normalized antiholomorphic primitive `J` acts on boundary
traces by `(Jh ∘ γ)' = conj(γ') (h ∘ γ)`, normalized by `Jh(γ(0)) = 0`, and the boundary trace
of the transmutation is

  `𝒱_E h ∘ γ = ∑_{j ≥ 0} (-E/4)^j / j! · γ^j (J^j h ∘ γ)`.

On Fourier coefficients (with `a = ĉonj γ'`, `g = γ̂`) this is:

* `antiPrim a h`: the normalized primitive, coefficients `(a ⋆ h)ₙ / (i n)` for `n ≠ 0` and the
  zero mode fixed by `∑ₙ (Jh)ₙ = 0` (value `0` at `θ = 0`, `tsum_antiPrim`);
* `antiPrim_bound` (**Lemma 5.2**): `‖Jh‖²_{H^{s+1}} ≤ K ‖h‖²_{H^s}` with an explicit
  `K = 4 (Z + 1) (∑ λₖ^s |aₖ|)²`, and for the iterates `‖J^j h‖²_{H^{s+1}} ≤ K^j ‖h‖²_{H^s}`
  (`antiPrimIter_bound`);
* `vekuaBdry_sub_one_bound` (**Lemma 5.3, boundary part of `𝒱_E − I`**): the series
  `∑_{j ≥ 1} (-E/4)^j / j! · γ^j J^j h` converges absolutely in `H^{s+1}(𝕋)` and its norm is
  at most `(exp(|E| R √K / 4) − 1) ‖h‖_{H^s}` with `R = ∑ λₖ^{s+1} |gₖ|`; in particular
  `𝒱_E − I : H^s → H^{s+1}` is bounded with norm `O(|E|)`;
* `vekuaConormal_sub_bound` (**Lemma 5.3, `𝒥_E − |D|`**): the terms `j ≥ 1` of the conormal
  density, `-i j γ' γ^{j-1} J^j h + i conj(γ') γ^j J^{j-1} h`, form a series converging
  absolutely in `H^s(𝕋)` with norm `O(|E|) ‖h‖_{H^s}`.

The identification of the `j = 0` conormal term with `|D| h` (Lemma 5.1) and of these Fourier
coefficients with the conformal parametrization are not part of this file.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

/-! ### The normalized primitive -/

/-- The normalized primitive on the Fourier side: coefficients `(a ⋆ h)ₙ / (i n)` for `n ≠ 0`,
and the zero mode chosen so that the coefficients sum to `0` (value `0` at `θ = 0`). -/
def antiPrim (a h : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n = 0 then -∑' m, primSeq (seqConv a h) m else primSeq (seqConv a h) n

/-- The constant of Lemma 5.2: `K = 4 (Z + 1) (∑ₖ λₖ^s |aₖ|)²`. -/
def primConst (s : ℝ) (a : ℤ → ℂ) : ℝ := 4 * (evalConst + 1) * wl1Norm s a ^ 2

lemma evalConst_nonneg : 0 ≤ evalConst :=
  tsum_nonneg fun n => by have := sobWeight_pos n; positivity

lemma primConst_nonneg s a : 0 ≤ primConst s a := by
  have := evalConst_nonneg; unfold primConst; positivity

/-- **Lemma 5.2 (Fourier form).** For `s ≥ 0`, `∑ₖ λₖ^s |aₖ| < ∞` and `h ∈ H^s`, the normalized
primitive lies in `H^{s+1}`, `‖Jh‖²_{H^{s+1}} ≤ K ‖h‖²_{H^s}`, and its coefficients are absolutely
summable with sum `0` (normalization at the boundary origin). -/
theorem antiPrim_bound  (hs : 0 ≤ s)  (ha : IsWL1 s a)
    (hh : IsSobolevSeq s h) :
    IsSobolevSeq (s + 1) (antiPrim a h) ∧
      sobNormSq (s + 1) (antiPrim a h) ≤ primConst s a * sobNormSq s h := by
  set p := primSeq (seqConv a h) with hpdef
  obtain ⟨hp, hpS⟩ := sobNormSq_primSeq_seqConv_le hs ha hh
  obtain ⟨hps, hpZ⟩ := sq_tsum_norm_le hs hp
  set P := ∑' m, ‖p m‖ with hP
  have hpt : ∀ n, (sobWeight n ^ (s + 1) * ‖antiPrim a h n‖) ^ 2 ≤
      (sobWeight n ^ (s + 1) * ‖p n‖) ^ 2 + (if n = 0 then P ^ 2 else 0) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp [antiPrim, show sobWeight 0 = 1 by simp [sobWeight]]
      have h1 := norm_tsum_le_tsum_norm hps
      have h2 := sq_nonneg ‖p 0‖
      nlinarith [norm_nonneg (∑' m, p m)]
    · simp [antiPrim, hn, hpdef]
  have hind : Summable fun n : ℤ => if n = 0 then P ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => by
      simp at hn; simp [hn]
  have hsum :=
    Summable.of_nonneg_of_le (fun n => sq_nonneg _) hpt (hp.add hind)
  refine ⟨hsum, ?_⟩
  calc _
      ≤ _ :=
        Summable.tsum_le_tsum hpt hsum (hp.add hind)
    _ = sobNormSq (s + 1) p + P ^ 2 := by
        rw [Summable.tsum_add hp hind, tsum_ite_eq]; rfl
    _ ≤ (evalConst + 1) * sobNormSq (s + 1) p := by nlinarith
    _ ≤ (evalConst + 1) * (4 * wl1Norm s a ^ 2 * sobNormSq s h) :=
        mul_le_mul_of_nonneg_left hpS (by linarith [evalConst_nonneg])
    _ = _ := by unfold primConst; ring

/-- The iterates `J^j h`. -/
def antiPrimIter (a : ℤ → ℂ) (j : ℕ) (h : ℤ → ℂ) : ℤ → ℂ := (antiPrim a)^[j] h

/-- **Iterated primitive bound** (Lemma 5.2, last assertion): for `j ≥ 1`,
`‖J^j h‖²_{H^{s+1}} ≤ K^j ‖h‖²_{H^s}`; for all `j`, `‖J^j h‖²_{H^s} ≤ K^j ‖h‖²_{H^s}`. -/
theorem antiPrimIter_bound  (hs : 0 ≤ s)  (ha : IsWL1 s a)
    (hh : IsSobolevSeq s h) j :
    IsSobolevSeq s (antiPrimIter a j h) ∧
      sobNormSq s (antiPrimIter a j h) ≤ primConst s a ^ j * sobNormSq s h := by
  induction j with
  | zero => simp [antiPrimIter, hh]
  | succ j ih =>
    have e : antiPrimIter a (j + 1) h = antiPrim a (antiPrimIter a j h) :=
      Function.iterate_succ_apply' _ _ _
    obtain ⟨h1, h2⟩ := antiPrim_bound hs ha ih.1
    obtain ⟨h3, h4⟩ := sobNormSq_mono (by linarith : s ≤ s + 1) h1
    rw [e]
    refine ⟨h3, h4.trans (h2.trans ?_)⟩
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left ih.2 (primConst_nonneg s a)

/-! ### The boundary transmutation series -/

/-- The `j`-th term `γ^j (J^j h ∘ γ)` of the boundary transmutation series, on Fourier
coefficients (`g` the coefficients of `γ`, `a` those of `conj γ'`). -/
def vekuaBdryTerm (g a h : ℤ → ℂ) (j : ℕ) : ℤ → ℂ := seqConv (seqConvPow g j) (antiPrimIter a j h)

/-- Bound on the terms `j ≥ 1` in `H^{s+1}`:
`‖γ^j J^j h‖²_{H^{s+1}} ≤ R^{2j} K^j ‖h‖²_{H^s}`, `R = ∑ λₖ^{s+1} |gₖ|`. -/
theorem vekuaBdryTerm_bound  (hs : 0 ≤ s)  (hg : IsWL1 (s + 1) g)
    (ha : IsWL1 s a) (hh : IsSobolevSeq s h) j :
    IsSobolevSeq (s + 1) (vekuaBdryTerm g a h (j + 1)) ∧
      sobNormSq (s + 1) (vekuaBdryTerm g a h (j + 1)) ≤
        (wl1Norm (s + 1) g ^ 2 * primConst s a) ^ (j + 1) * sobNormSq s h := by
  have hs1 : 0 ≤ s + 1 := by linarith
  obtain ⟨hP1, hP2⟩ := wl1Norm_seqConvPow_le hs1 hg (j + 1)
  obtain ⟨hJ1, hJ2⟩ : IsSobolevSeq (s + 1) (antiPrimIter a (j + 1) h) ∧ sobNormSq (s + 1) (antiPrimIter a (j + 1) h) ≤ primConst s a ^ (j + 1) * sobNormSq s h := by
    have e : antiPrimIter a (j + 1) h = antiPrim a (antiPrimIter a j h) :=
      Function.iterate_succ_apply' _ _ _
    obtain ⟨ih1, ih2⟩ := antiPrimIter_bound hs ha hh j
    obtain ⟨h1, h2⟩ := antiPrim_bound hs ha ih1
    rw [e]
    refine ⟨h1, h2.trans ?_⟩
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left ih2 (primConst_nonneg s a)
  obtain ⟨-, h1, h2⟩ := sobNormSq_seqConv_le hs1 hP1 hJ1
  refine ⟨h1, h2.trans ?_⟩
  have hR0 : 0 ≤ wl1Norm (s + 1) (seqConvPow g (j + 1)) :=
    tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  have hJ0 := sobNormSq_nonneg (s + 1) (antiPrimIter a (j + 1) h)
  calc _
      ≤ (wl1Norm (s + 1) g ^ (j + 1)) ^ 2 *
          (primConst s a ^ (j + 1) * sobNormSq s h) := by
        gcongr
    _ = _ := by ring

/-- The element of `ℓ²(ℤ)` representing `f ∈ H^s` in normalized coordinates
(`(λₙ^s fₙ)ₙ`); its norm is the `H^s` norm. -/
def sobVec s f (hf : IsSobolevSeq s f) : L2Z :=
  ⟨fun n => ((sobWeight n ^ s : ℝ) : ℂ) * f n, by
    refine memℓp_two_iff_summable.mpr ?_
    refine hf.congr fun n => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by have := sobWeight_pos n; positivity)]⟩

lemma norm_sobVec s f hf :
    ‖sobVec s f hf‖ = Real.sqrt (sobNormSq s f) := by
  rw [← Real.sqrt_sq (norm_nonneg (sobVec s f hf)), norm_sq_L2Z]
  congr 1
  refine tsum_congr fun n => ?_
  change ‖(sobWeight n ^ s : ℝ) * f n‖ ^ 2 = _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have := sobWeight_pos n; positivity)]

/-- **Lemma 5.3, boundary part of `𝒱_E − I` (Fourier form).** Let `s ≥ 0`, let `g`
(coefficients of `γ`) satisfy `∑ λₖ^{s+1} |gₖ| = R < ∞`, `a` (coefficients of `conj γ'`)
satisfy `∑ λₖ^s |aₖ| < ∞`, and `h ∈ H^s`. Then for every `E ∈ ℂ` the series
`∑_{j ≥ 1} (-E/4)^j / j! · γ^j J^j h` converges absolutely in `H^{s+1}(𝕋)` (normalized
coordinates in `ℓ²(ℤ)`), and its norm is at most `(exp(|E| R √K / 4) − 1) ‖h‖_{H^s}`; this is
`O(|E|)` as `E → 0`. -/
theorem vekuaBdry_sub_one_bound  (hs : 0 ≤ s) {g a h : ℤ → ℂ} (hg : IsWL1 (s + 1) g)
    (ha : IsWL1 s a) (hh : IsSobolevSeq s h) (E : ℂ) :
    ∃ hT : ∀ j, IsSobolevSeq (s + 1) (vekuaBdryTerm g a h (j + 1)),
      Summable (fun j => ‖((-E / 4) ^ (j + 1) / (j + 1).factorial) •
        sobVec (s + 1) _ (hT j)‖) ∧
      ‖∑' j, ((-E / 4) ^ (j + 1) / (j + 1).factorial) • sobVec (s + 1) _ (hT j)‖ ≤
        (Real.exp (‖E‖ * wl1Norm (s + 1) g * Real.sqrt (primConst s a) / 4) - 1) *
          Real.sqrt (sobNormSq s h) := by
  have hT : ∀ j, IsSobolevSeq (s + 1) (vekuaBdryTerm g a h (j + 1)) :=
    fun j => (vekuaBdryTerm_bound hs hg ha hh j).1
  refine ⟨hT, ?_⟩
  set R := wl1Norm (s + 1) g with hR
  set K := primConst s a with hK
  set S := sobNormSq s h with hS
  have hR0 : 0 ≤ R := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  set x := ‖E‖ * R * Real.sqrt K / 4 with hx
  have hx0 : 0 ≤ x := by positivity
  have hterm : ∀ j : ℕ, ‖((-E / 4) ^ (j + 1) / (j + 1).factorial) •
      sobVec (s + 1) _ (hT j)‖ ≤ x ^ (j + 1) / (j + 1).factorial * Real.sqrt S := by
    intro j
    rw [norm_smul, norm_sobVec, norm_div, norm_pow, norm_div, norm_neg, Complex.norm_natCast]
    have hsq : Real.sqrt (sobNormSq (s + 1) (vekuaBdryTerm g a h (j + 1))) ≤
        (R * Real.sqrt K) ^ (j + 1) * Real.sqrt S := by
      have e : (R ^ 2 * K) ^ (j + 1) * S = ((R * Real.sqrt K) ^ (j + 1)) ^ 2 * S := by
        rw [← pow_mul, mul_comm (j + 1) 2, pow_mul, mul_pow R (Real.sqrt K) 2,
          Real.sq_sqrt (primConst_nonneg s a)]
      calc _ ≤ _ := Real.sqrt_le_sqrt ((vekuaBdryTerm_bound hs hg ha hh j).2)
        _ = _ := by
          rw [e, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [show ‖(4 : ℂ)‖ = 4 by norm_num]
    calc _
        ≤ (‖E‖ / 4) ^ (j + 1) / (j + 1).factorial *
          ((R * Real.sqrt K) ^ (j + 1) * Real.sqrt S) := by gcongr
      _ = _ := by rw [hx]; ring
  have hsumx : Summable fun j => x ^ (j + 1) / (j + 1).factorial * Real.sqrt S :=
    ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial x)).mul_right _
  have hsumN := Summable.of_nonneg_of_le (fun j => norm_nonneg _) hterm hsumx
  refine ⟨hsumN, ?_⟩
  calc _ ≤ _ :=
        norm_tsum_le_tsum_norm hsumN
    _ ≤ _ :=
        Summable.tsum_le_tsum hterm hsumN hsumx
    _ = _ := by rw [tsum_mul_right, show ∑' j : ℕ, x ^ (j + 1) / (j + 1).factorial = Real.exp x - 1 by
      rw [show Real.exp x = ∑' n : ℕ, x ^ n / n.factorial by
        rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div], (Real.summable_pow_div_factorial x).tsum_eq_zero_add]
      simp]

/-! ### The conormal series: `𝒥_E − |D|` -/

end PolyaNeumann
