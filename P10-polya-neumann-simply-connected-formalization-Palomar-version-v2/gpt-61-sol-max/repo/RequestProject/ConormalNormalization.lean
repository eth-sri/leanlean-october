module

public import RequestProject.PlanarTypes

public import RequestProject.BoundaryTransmutation

/-!
# The normalized conormal transmutation (Lemma 6.14, Fourier form)

Lemma 6.14 of the paper concerns `Ĵ_E = Λ^{-1/2} 𝒥_E Λ^{-1/2}`, where in conformal coordinates

  `𝒥_E h = |D| h + ∑_{j ≥ 1} (-E/4)^j / j! · (-i j γ' γ^{j-1} J^j h + i conj(γ') γ^j J^{j-1} h)`.

It asserts that `Ĵ_E` is the inclusion plus an operator gaining one derivative, and that it
depends continuously on `E` in operator norm. This file proves these two assertions in the
Fourier model of `BoundaryTransmutation.lean`. As there, the Fourier coefficients `b`, `a`, `g` of
`γ'`, `conj γ'`, `γ` are given sequences in the weighted `ℓ¹` space of order `s ≥ 0`.

* `SeqOpBound s t C Φ`: a map of coefficient sequences, linear on `H^s`, with
  `‖Φ h‖_{H^t} ≤ C ‖h‖_{H^s}`. Such maps form a calculus (composition, sums, scalars), and each
  gives a bounded operator on `ℓ²(ℤ)` in normalized coordinates (`SeqOpBound.toCLM`).
* `conormalRemOp`: the remainder `𝒥_E − |D|` on `H^s`, as a bounded operator on `ℓ²(ℤ)` in
  normalized coordinates. It is the operator-norm convergent series `∑_j (-E/4)^{j+1}/(j+1)! T_j`.
  On `sobVec s h` it gives the series of `vekuaConormal_sub_bound` (`conormalRemOp_sobVec`).
  It is continuous in `E ∈ ℂ` in operator norm (`continuous_conormalRemOp`).
* `normalizedConormal`: `Ĵ_E = Λ^{-1/2} |D| Λ^{-1/2} + Λ^{-1} ∘ (𝒥_E − |D|)` at `s = 1/2`. The
  principal part is the multiplier `|n|/(1+|n|)` (`normalizedConormal_principal_apply`).
* **Lemma 6.14** (`normalizedConormal_sub_one_eq`, `isCompactOperator_normalizedConormal_sub_one`,
  `continuous_normalizedConormal`): `Ĵ_E − I = Λ^{-1} ∘ ((𝒥_E − |D|) − I)` gains one derivative,
  hence is compact, and `E ↦ Ĵ_E` is norm-continuous.
* **Lemma 7.3 for `Ĵ_E`** (`normalizedConormal_fixed_complement`): if `Ĵ_{E₀}` is injective on a
  closed subspace `H₀`, a fixed `R = inclusion + finite rank` makes `Ĵ_E Π₀ + R Π₁` invertible
  near `E₀`, with continuous inverse.

The operators are defined on all of `ℓ²(ℤ)`; the paper's `Ĵ_E` is the restriction to the
nonpositive modes, and both properties pass to restrictions. The injectivity of `Ĵ_E` (from
Lemma 6.13, which needs elliptic regularity) is not proved here.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Filter Topology

/-! ### Sobolev sequences in normalized coordinates -/

section
variable {s : ℝ}
include s

lemma isSobolevSeq_add  (hf : IsSobolevSeq s f) (hf' : IsSobolevSeq s f') :
    IsSobolevSeq s (f + f') := by
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
    ((hf.mul_left 2).add (hf'.mul_left 2))
  have hw : 0 ≤ sobWeight n ^ s := by have := sobWeight_pos n; positivity
  have h1 : ‖(f + f') n‖ ≤ ‖f n‖ + ‖f' n‖ := norm_add_le _ _
  have h2 : sobWeight n ^ s * ‖(f + f') n‖ ≤
      sobWeight n ^ s * ‖f n‖ + sobWeight n ^ s * ‖f' n‖ := by
    nlinarith
  have h3 : 0 ≤ sobWeight n ^ s * ‖(f + f') n‖ := by positivity
  nlinarith [sq_nonneg (sobWeight n ^ s * ‖f n‖ - sobWeight n ^ s * ‖f' n‖)]

lemma isSobolevSeq_smul (c : ℂ)  (hf : IsSobolevSeq s f) :
    IsSobolevSeq s (c • f) := by
  refine (hf.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp  ; ring

@[simp] lemma sobVec_apply  hf n :
    (sobVec s f hf : FourierSeq) n = ((sobWeight n ^ s : ℝ) : ℂ) * f n := rfl

lemma sobVec_add  hf hf'
    hff :
    sobVec s (f + f') hff = sobVec s f hf + sobVec s f' hf' := by
  ext n
  simp [mul_add]

lemma sobVec_smul (c : ℂ) {f : FourierSeq} (hf : IsSobolevSeq s f)
    (hcf : IsSobolevSeq s (c • f)) :
    sobVec s (c • f) hcf = c • sobVec s f hf := by
  ext <;> simp_all <;> ring

end


lemma sobWeight_rpow_mul_neg (s : ℝ) n : sobWeight n ^ s * sobWeight n ^ (-s) = 1 := by
  rw [Real.rpow_neg (sobWeight_pos n).le,
    mul_inv_cancel₀ (by have := sobWeight_pos n; positivity)]

/-- The coefficient sequence `(λₙ^{-s} fₙ)ₙ ∈ H^s` represented by `f ∈ ℓ²(ℤ)` in normalized
coordinates; inverse to `sobVec s`. -/
def fromL2 (s : ℝ) (f : L2Z) n  := ((sobWeight n ^ (-s) : ℝ) : ℂ) * f n

section
variable (s : ℝ)
include s

lemma isSobolevSeq_fromL2 f : IsSobolevSeq s (fromL2 s f) := by
  refine (summable_norm_sq_L2Z f).congr fun n => ?_
  unfold fromL2
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by have := sobWeight_pos n; positivity), ← mul_assoc,
    sobWeight_rpow_mul_neg, one_mul]

lemma sobVec_fromL2 f : sobVec s (fromL2 s f) (isSobolevSeq_fromL2 s f) = f := by
  ext n
  rw [sobVec_apply, fromL2, ← mul_assoc, ← Complex.ofReal_mul, sobWeight_rpow_mul_neg]
  simp

lemma fromL2_sobVec h hh : fromL2 s (sobVec s h hh) = h := by
  funext n
  rw [fromL2, sobVec_apply, ← mul_assoc, ← Complex.ofReal_mul, mul_comm (sobWeight n ^ (-s)),
    sobWeight_rpow_mul_neg]
  simp

lemma fromL2_add f f' : fromL2 s (f + f') = fromL2 s f + fromL2 s f' := by
  funext n
  simp [fromL2, mul_add]

lemma fromL2_smul (c : ℂ) (f : L2Z) : fromL2 s (c • f) = c • fromL2 s f := by
  funext n
  simp  [fromL2]
  ring

end


/-! ### Bounded linear maps of coefficient sequences -/

/-- `Φ` maps `H^s` to `H^t`, linearly on `H^s`, with `‖Φ h‖_{H^t} ≤ C ‖h‖_{H^s}`. -/
structure SeqOpBound (s t C : ℝ) (Φ : (FourierSeq) → (FourierSeq)) : Prop where
  nonneg : 0 ≤ C
  maps : ∀ h, IsSobolevSeq s h → IsSobolevSeq t (Φ h)
  bound : ∀ h, IsSobolevSeq s h → Real.sqrt (sobNormSq t (Φ h)) ≤ C * Real.sqrt (sobNormSq s h)
  map_add : ∀ h h', IsSobolevSeq s h → IsSobolevSeq s h' → Φ (h + h') = Φ h + Φ h'
  map_smul : ∀ (c : ℂ) h, IsSobolevSeq s h → Φ (c • h) = c • Φ h

namespace SeqOpBound

variable {s t u C D : ℝ} {Φ Ψ : (FourierSeq) → (FourierSeq)}

section
variable (H : SeqOpBound s t C Φ)
include H

lemma mono_const (hCD : C ≤ D) : SeqOpBound s t D Φ :=
  ⟨H.nonneg.trans hCD, H.maps,
    fun h hh => (H.bound h hh).trans (mul_le_mul_of_nonneg_right hCD (Real.sqrt_nonneg _)),
    H.map_add, H.map_smul⟩

lemma comp (H' : SeqOpBound t u D Ψ) :
    SeqOpBound s u (D * C) (Ψ ∘ Φ) := by
  refine ⟨mul_nonneg H'.nonneg H.nonneg, fun h hh => H'.maps _ (H.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · calc _ ≤ D * Real.sqrt (sobNormSq t (Φ h)) := H'.bound _ (H.maps h hh)
      _ ≤ D * (C * Real.sqrt (sobNormSq s h)) :=
          mul_le_mul_of_nonneg_left (H.bound h hh) H'.nonneg
      _ = _ := by ring
  · simp  [H.map_add h h' hh hh', H'.map_add _ _ (H.maps h hh) (H.maps h' hh')]
  · simp  [H.map_smul c h hh, H'.map_smul c _ (H.maps h hh)]

lemma add (H' : SeqOpBound s t D Ψ) :
    SeqOpBound s t (C + D) (fun h => Φ h + Ψ h) := by
  refine ⟨add_nonneg H.nonneg H'.nonneg, fun h hh => isSobolevSeq_add (H.maps h hh) (H'.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · have e := sobVec_add (H.maps h hh) (H'.maps h hh) (isSobolevSeq_add (H.maps h hh) (H'.maps h hh))
    rw [← norm_sobVec _ _ (isSobolevSeq_add (H.maps h hh) (H'.maps h hh)), e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_sobVec, norm_sobVec, add_mul]
    exact add_le_add (H.bound h hh) (H'.bound h hh)
  · rw [H.map_add h h' hh hh', H'.map_add h h' hh hh']
    abel
  · rw [H.map_smul c h hh, H'.map_smul c h hh, smul_add]

end


lemma smul (c : ℂ) (H : SeqOpBound s t C Φ) :
    SeqOpBound s t (‖c‖ * C) (fun h => c • Φ h) := by
  refine ⟨mul_nonneg (norm_nonneg _) H.nonneg, fun h hh => isSobolevSeq_smul c (H.maps h hh),
    fun h hh => ?_, fun h h' hh hh' => ?_, fun d h hh => ?_⟩
  · rw [← norm_sobVec _ _ (isSobolevSeq_smul c (H.maps h hh)), sobVec_smul c (H.maps h hh),
      norm_smul, norm_sobVec, mul_assoc]
    exact mul_le_mul_of_nonneg_left (H.bound h hh) (norm_nonneg _)
  · rw [H.map_add h h' hh hh', smul_add]
  · rw [H.map_smul d h hh, smul_comm]

lemma id_mono (hst : s ≤ t) : SeqOpBound t s 1 id :=
  ⟨zero_le_one, fun _ hh => (sobNormSq_mono hst hh).1,
    fun _ hh => by rw [one_mul]; exact Real.sqrt_le_sqrt (sobNormSq_mono hst hh).2,
    fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- The bounded operator on `ℓ²(ℤ)` given by `Φ` in normalized coordinates:
`f ↦ sobVec t (Φ (fromL2 s f))`. -/
def toCLM (H : SeqOpBound s t C Φ) : L2Z →L[ℂ] L2Z :=
  LinearMap.mkContinuous
    { toFun := fun f => sobVec t (Φ (fromL2 s f)) (H.maps _ (isSobolevSeq_fromL2 s f))
      map_add' := fun f g => by
        have e : Φ (fromL2 s (f + g)) = Φ (fromL2 s f) + Φ (fromL2 s g) := by
          rw [fromL2_add, H.map_add _ _ (isSobolevSeq_fromL2 s f) (isSobolevSeq_fromL2 s g)]
        ext <;> simp_all <;> ring
      map_smul' := fun c f => by
        have e : Φ (fromL2 s (c • f)) = c • Φ (fromL2 s f) := by
          rw [fromL2_smul, H.map_smul _ _ (isSobolevSeq_fromL2 s f)]
        ext <;> simp_all <;> ring }
    C (fun f => by
      have e := norm_sobVec s (fromL2 s f) (isSobolevSeq_fromL2 s f)
      rw [sobVec_fromL2] at e
      change ‖sobVec t (Φ (fromL2 s f)) (H.maps _ (isSobolevSeq_fromL2 s f))‖ ≤ C * ‖f‖
      rw [norm_sobVec, e]
      exact H.bound _ (isSobolevSeq_fromL2 s f))

lemma norm_toCLM_le (H : SeqOpBound s t C Φ) : ‖H.toCLM‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ H.nonneg _

end SeqOpBound

/-! ### The building blocks: multipliers and the normalized primitive -/

theorem seqOpBound_seqConv  (hs : 0 ≤ s)  (hc : IsWL1 s c) :
    SeqOpBound s s (wl1Norm s c) (seqConv c) := by
  have h0 : 0 ≤ wl1Norm s c := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  refine ⟨h0, fun h hh => (sobNormSq_seqConv_le hs hc hh).2.1, fun h hh => ?_,
    fun h h' hh hh' => ?_, fun c' h hh => ?_⟩
  · calc _ ≤ Real.sqrt (wl1Norm s c ^ 2 * sobNormSq s h) :=
          Real.sqrt_le_sqrt (sobNormSq_seqConv_le hs hc hh).2.2
      _ = _ := by simp_all
  · funext n
    simp  [seqConv, mul_add]
    exact Summable.tsum_add ((sobNormSq_seqConv_le hs hc hh).1 n)
      ((sobNormSq_seqConv_le hs hc hh').1 n)
  · funext n
    simp  [seqConv]
    rw [← tsum_mul_left]
    exact tsum_congr fun k => by ring

lemma primSeq_add u v : primSeq (u + v) = primSeq u + primSeq v := by
  funext n; simp [primSeq, add_div]

lemma primSeq_smul (c : ℂ) u : primSeq (c • u) = c • primSeq u := by
  funext n; simp [primSeq, mul_div_assoc]

section
variable {s : ℝ} (hs : 0 ≤ s)
include s hs

lemma summable_primSeq_seqConv  (ha : IsWL1 s a)
    (hh : IsSobolevSeq s h) : Summable (primSeq (seqConv a h)) :=
  (sq_tsum_norm_le hs (sobNormSq_primSeq_seqConv_le hs ha hh).1).1.of_norm

theorem seqOpBound_antiPrim  (ha : IsWL1 s a) :
    SeqOpBound s (s + 1) (Real.sqrt (primConst s a)) (antiPrim a) := by
  refine ⟨Real.sqrt_nonneg _, fun h hh => (antiPrim_bound hs ha hh).1, fun h hh => ?_,
    fun h h' hh hh' => ?_, fun c h hh => ?_⟩
  · calc _ ≤ Real.sqrt (primConst s a * sobNormSq s h) :=
          Real.sqrt_le_sqrt (antiPrim_bound hs ha hh).2
      _ = _ := Real.sqrt_mul (primConst_nonneg s a) _
  · have hc := (seqOpBound_seqConv hs ha).map_add h h' hh hh'
    funext n
    by_cases hn : n = 0
    · simp  [antiPrim, hn, hc, primSeq_add]
      rw [Summable.tsum_add (summable_primSeq_seqConv hs ha hh)
        (summable_primSeq_seqConv hs ha hh'), neg_add]
    · simp [antiPrim, hn, hc, primSeq_add]
  · have hc := (seqOpBound_seqConv hs ha).map_smul c h hh
    funext n
    by_cases hn : n = 0
    · simp only [antiPrim, hn, if_true, Pi.smul_apply, hc, primSeq_smul, smul_eq_mul]
      rw [tsum_mul_left]; ring
    · simp [antiPrim, hn, hc, primSeq_smul]

theorem seqOpBound_antiPrimIter  (ha : IsWL1 s a) j :
    SeqOpBound s s (Real.sqrt (primConst s a) ^ j) (antiPrimIter a j) := by
  induction j with
  | zero => exact (SeqOpBound.id_mono le_rfl).mono_const (by simp)
  | succ j ih =>
    have e : antiPrimIter a (j + 1) = id ∘ (antiPrim a ∘ antiPrimIter a j) := by
      funext h; exact Function.iterate_succ_apply' _ _ _
    rw [e]
    exact ((ih.comp (seqOpBound_antiPrim hs ha)).comp
      (SeqOpBound.id_mono (by linarith))).mono_const (le_of_eq (by ring))

/-- Multiplication by `c · γ^j` on `H^s`, with bound `‖c‖_{ℓ¹_s} R^j`. -/
theorem seqOpBound_conv_pow  (hc : IsWL1 s c)
    (hg : IsWL1 s g) j :
    SeqOpBound s s (wl1Norm s c * wl1Norm s g ^ j)
      (fun h => seqConv c (seqConv (seqConvPow g j) h)) := by
  have hc0 : 0 ≤ wl1Norm s c := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  exact ((seqOpBound_seqConv hs (wl1Norm_seqConvPow_le hs hg j).1).comp
    (seqOpBound_seqConv hs hc)).mono_const
    (mul_le_mul_of_nonneg_left (wl1Norm_seqConvPow_le hs hg j).2 hc0)

end


/-! ### The conormal remainder `𝒥_E − |D|` -/

/-- The `(j+1)`-th term of the conormal series (before its coefficient), as a map of coefficient
sequences: `-i (j+1) γ' γ^j J^{j+1} h + i conj(γ') γ^{j+1} J^j h`. -/
def conormalTermMap b a g j h  :=
  (-Complex.I * (j + 1 : ℕ)) • seqConv b (seqConv (seqConvPow g j) (antiPrimIter a (j + 1) h)) +
    Complex.I • seqConv a (seqConv (seqConvPow g (j + 1)) (antiPrimIter a j h))

/-- The bound `(j+1) B R^j q^{j+1} + M R^{j+1} q^j` on the `(j+1)`-th conormal term. -/
def conormalTermConst s b a g (j : ℕ)  :=
  (j + 1) * (wl1Norm s b * wl1Norm s g ^ j * Real.sqrt (primConst s a) ^ (j + 1)) +
    wl1Norm s a * wl1Norm s g ^ (j + 1) * Real.sqrt (primConst s a) ^ j

section
variable {s } (hs : 0 ≤ s) {b a g } (hb : IsWL1 s b) (ha : IsWL1 s a) (hg : IsWL1 s g)

include s hs b a g hb ha hg in
theorem seqOpBound_conormalTerm (j : ℕ) :
    SeqOpBound s s (conormalTermConst s b a g j) (conormalTermMap b a g j) := by
  have H1 := ((seqOpBound_antiPrimIter hs ha (j + 1)).comp
    (seqOpBound_conv_pow hs hb hg j)).smul (-Complex.I * (j + 1 : ℕ))
  have H2 := ((seqOpBound_antiPrimIter hs ha j).comp
    (seqOpBound_conv_pow hs ha hg (j + 1))).smul Complex.I
  have hn : ‖-Complex.I * ((j + 1 : ℕ) : ℂ)‖ = j + 1 := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_natCast]; push_cast; ring
  refine (H1.add H2).mono_const (le_of_eq ?_)
  measurability

/-- The `(j+1)`-th conormal term as a bounded operator on `ℓ²(ℤ)` (normalized `H^s`
coordinates). -/
def conormalTermOp {s } hs {b a g } (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) j  :=
  (seqOpBound_conormalTerm hs hb ha hg j).toCLM

/-- The coefficient `(-E/4)^{j+1}/(j+1)!` of the `(j+1)`-th conormal term. -/
def conormalCoeff (E : ℂ) j  := (-E / 4) ^ (j + 1) / (j + 1).factorial

section
include s hs b a g hb ha hg

/-- Summable majorant of the operator-norm series on `‖E‖ ≤ r`. -/
lemma norm_conormalCoeff_smul_le {r : ℝ} {E : ℂ} (hE : ‖E‖ ≤ r) (j : ℕ) :
    ‖conormalCoeff E j • conormalTermOp hs hb ha hg j‖ ≤
      r / 4 * (wl1Norm s b * Real.sqrt (primConst s a) + wl1Norm s a * wl1Norm s g) *
        ((r * wl1Norm s g * Real.sqrt (primConst s a) / 4) ^ j / j.factorial) := by
  set B := wl1Norm s b
  set M := wl1Norm s a
  set R := wl1Norm s g
  set q := Real.sqrt (primConst s a) with hq
  
  have hM0 : 0 ≤ M := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  have hR0 : 0 ≤ R := tsum_nonneg fun k => by have := sobWeight_pos k; positivity
  
  have hr0  := (norm_nonneg E).trans hE
  set e := r / 4 with he
  
  have hT  :=
    (seqOpBound_conormalTerm hs hb ha hg j).norm_toCLM_le
  have hc : ‖conormalCoeff E j‖ ≤ e ^ (j + 1) / ((j + 1).factorial : ℝ) := by
    rw [conormalCoeff, norm_div, norm_pow, norm_div, norm_neg, Complex.norm_natCast,
      show ‖(4 : ℂ)‖ = 4 by norm_num]
    gcongr
    linarith
  have hf : ((j + 1).factorial : ℝ) = (j + 1) * j.factorial := by
    push_cast [Nat.factorial_succ]; ring
  
  rw [norm_smul]
  calc ‖conormalCoeff E j‖ * ‖conormalTermOp hs hb ha hg j‖
      ≤ e ^ (j + 1) / ((j + 1).factorial) *
          ((j + 1) * (B * R ^ j * q ^ (j + 1)) + M * R ^ (j + 1) * q ^ j) :=
        mul_le_mul hc hT (norm_nonneg _) (by positivity)
    _ = e ^ (j + 1) / j.factorial * (B * R ^ j * q ^ (j + 1)) +
          e ^ (j + 1) / ((j + 1) * j.factorial) * (M * R ^ (j + 1) * q ^ j) := by
        rw [hf]; field_simp
    _ ≤ e ^ (j + 1) / j.factorial * (B * R ^ j * q ^ (j + 1)) +
          e ^ (j + 1) / j.factorial * (M * R ^ (j + 1) * q ^ j) := by
        gcongr
        nlinarith
    _ = e * (B * q + M * R) * ((r * R * q / 4) ^ j / j.factorial) := by
        ring

lemma summable_conormalSeries (E : ℂ) :
    Summable fun j => conormalCoeff E j • conormalTermOp hs hb ha hg j :=
  Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial _).mul_left _)
    (norm_conormalCoeff_smul_le hs hb ha hg le_rfl)

end


/-- The conormal remainder `𝒥_E − |D|` on `H^s`, in normalized coordinates on `ℓ²(ℤ)`. -/
def conormalRemOp {s : ℝ} (hs : 0 ≤ s) {b a g : FourierSeq} (hb : IsWL1 s b)
    (ha : IsWL1 s a) (hg : IsWL1 s g) (E : ℂ) : L2Z →L[ℂ] L2Z :=
  ∑' j, conormalCoeff E j • conormalTermOp hs hb ha hg j

include s hs b a g hb ha hg in
/-- The conormal remainder depends continuously on `E` in operator norm. -/
theorem continuous_conormalRemOp :
    Continuous fun E => conormalRemOp hs hb ha hg E := by
  refine continuous_iff_continuousAt.mpr fun E₀ => ?_
  have hcont : ContinuousOn ((conormalRemOp hs hb ha hg))
      (Metric.ball 0 (‖E₀‖ + 1)) := by
    refine continuousOn_tsum (fun j => ?_) ((Real.summable_pow_div_factorial _).mul_left _)
      (fun j E hE => norm_conormalCoeff_smul_le hs hb ha hg
        (le_of_lt (mem_ball_zero_iff.mp hE)) j)
    unfold conormalCoeff
    fun_prop
  exact hcont.continuousAt (Metric.isOpen_ball.mem_nhds (by simp))

end


/-! ### The normalized conormal transmutation `Ĵ_E` -/

/-- The normalized principal part `Λ^{-1/2} |D| Λ^{-1/2} = I − Λ^{-1}`. -/
def normalizedConormalPrincipal : L2Z →L[ℂ] L2Z :=
  (1 : L2Z →L[ℂ] L2Z) - sobolevSmoothing 1 zero_le_one

/-- The principal part is the Fourier multiplier `|n| / (1 + |n|)`. -/
lemma normalizedConormal_principal_apply f n :
    (normalizedConormalPrincipal f : FourierSeq) n = ((|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) : ℂ) * f n := by
  
  have key : (|(n : ℝ)| / (1 + |(n : ℝ)|) : ℝ) = 1 - sobWeight n ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg_one, sobWeight]
    field_simp
    ring
  simp_all [normalizedConormalPrincipal, sobolevSmoothing] <;> ring

/-- **`Ĵ_E = Λ^{-1/2} 𝒥_E Λ^{-1/2}`** in Fourier form: principal part `Λ^{-1/2}|D|Λ^{-1/2}` plus
`Λ^{-1/2} (𝒥_E − |D|) Λ^{-1/2} = Λ^{-1} ∘ R_E`, where `R_E` is the conormal remainder on
`H^{1/2}` in normalized coordinates. -/
def normalizedConormal {b a g : FourierSeq} (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a)
    (hg : IsWL1 (1 / 2) g) (E : ℂ) : L2Z →L[ℂ] L2Z :=
  normalizedConormalPrincipal +
    (sobolevSmoothing 1 zero_le_one).comp (conormalRemOp (by norm_num) hb ha hg E)

section
variable {b a g } (hb : IsWL1 (1 / 2) b) (ha : IsWL1 (1 / 2) a) (hg : IsWL1 (1 / 2) g)
include b a g hb ha hg

/-- **Lemma 6.14 (gain of one derivative).** `Ĵ_E − I = Λ^{-1} ∘ (R_E − I)`. -/
theorem normalizedConormal_sub_one_eq (E : ℂ) :
    normalizedConormal hb ha hg E - (1 : L2Z →L[ℂ] L2Z) =
      (sobolevSmoothing 1 zero_le_one).comp
        (conormalRemOp (by norm_num) hb ha hg E - (1 : L2Z →L[ℂ] L2Z)) := by
  unfold normalizedConormal normalizedConormalPrincipal
  have h1 : (sobolevSmoothing 1 zero_le_one).comp (1 : L2Z →L[ℂ] L2Z) =
      sobolevSmoothing 1 zero_le_one := ContinuousLinearMap.ext fun _ => rfl
  ext <;> simp_all <;> ring

/-- **Lemma 6.14 (inclusion plus compact).** `Ĵ_E − I` is compact. -/
theorem isCompactOperator_normalizedConormal_sub_one (E : ℂ) :
    IsCompactOperator (normalizedConormal hb ha hg E - (1 : L2Z →L[ℂ] L2Z)) := by
  rw [normalizedConormal_sub_one_eq]
  exact (isCompactOperator_sobolevSmoothing one_pos).comp_clm _

/-- **Lemma 6.14 (continuity).** `E ↦ Ĵ_E` is continuous in operator norm. -/
theorem continuous_normalizedConormal :
    Continuous fun E => normalizedConormal hb ha hg E :=
  continuous_const.add (continuous_const.clm_comp (continuous_conormalRemOp _ hb ha hg))

end


end PolyaNeumann
