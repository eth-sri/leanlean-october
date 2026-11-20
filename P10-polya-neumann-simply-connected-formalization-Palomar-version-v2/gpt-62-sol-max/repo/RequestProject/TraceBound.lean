module

public import RequestProject.MonodromyCompact
public import RequestProject.PhaseCount

/-!
# Lemma 4.7: trace-norm bounds for `V_E - I` and `U_E - I`

The paper shows that `V_E - I` is trace class. We use the trace norm through the elementary
quantity `sup |∑ᵢ ⟨fᵢ, T eᵢ⟩|` over pairs of finite orthonormal families: `TraceBound T C`
says that this quantity is at most `C`. It is stable under sums, scalars, composition with
unitaries, interval integrals, increments with bounded derivative and norm limits, and it
bounds the multiplicity-weighted eigenvalue sums of `T`. Integrating the curvature formula
`∂_E V_E = -i V_E Q_E` as in the paper, we obtain that `∑_{z ≠ 1} mult(z) |z - 1|` converges
for the monodromy `U_E` of a closed Lipschitz curve.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Real Topology ComplexConjugate

noncomputable section

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `TraceBound T C`: for all finite orthonormal families `eᵢ`, `fᵢ`,
`|∑ᵢ ⟨fᵢ, T eᵢ⟩| ≤ C` (a bound on the trace norm of `T`). -/
def TraceBound (T : H →L[ℂ] H) (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (e f : ι → H), Orthonormal ℂ e → Orthonormal ℂ f →
    ‖∑ i, inner ℂ (f i) (T (e i))‖ ≤ C

section

variable {T : H →L[ℂ] H}
include T

lemma TraceBound.nonneg  {C : ℝ} (h : TraceBound T C) : 0 ≤ C := by
  have he : Orthonormal ℂ (fun _ : Empty => (0 : H)) := ⟨fun i => i.elim, fun i => i.elim⟩
  have := h Empty _ _ he he
  simpa using this

lemma TraceBound.mono  {C D : ℝ} (h : TraceBound T C) (hCD : C ≤ D) :
    TraceBound T D := fun ι _ e f he hf => (h ι e f he hf).trans hCD

end

lemma TraceBound.zero : TraceBound (0 : H →L[ℂ] H) 0 := by
  intro ι _ e f _ _; simp

lemma TraceBound.add {S T : H →L[ℂ] H} {C D : ℝ} (hS : TraceBound S C) (hT : TraceBound T D) :
    TraceBound (S + T) (C + D) := by
  intro ι _ e f he hf
  simp  [inner_add_right, Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add (hS ι e f he hf) (hT ι e f he hf))

section

variable {T : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C)
include T C hT

lemma TraceBound.smul  (c : ℂ) :
    TraceBound (c • T) (‖c‖ * C) := by
  intro ι _ e f he hf
  simp  [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hT ι e f he hf) (norm_nonneg _)

lemma TraceBound.neg  : TraceBound (-T) C := by
  simpa using hT.smul (-1)

end

lemma TraceBound.sub {S T : H →L[ℂ] H} {C D : ℝ} (hS : TraceBound S C) (hT : TraceBound T D) :
    TraceBound (S - T) (C + D) := by
  rw [sub_eq_add_neg]; exact hS.add hT.neg

lemma TraceBound.real_smul {T : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C) (c : ℝ) :
    TraceBound (c • T) (|c| * C) := by
  have := hT.smul (c : ℂ)
  rwa [Complex.coe_smul, Complex.norm_real, Real.norm_eq_abs] at this

section

variable {T V : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C)
include T V C hT

/-- Composition on the right with an isometry. -/
lemma TraceBound.comp_isometry 
    (hV : ∀ x y, inner ℂ (V x) (V y) = inner ℂ x y) : TraceBound (T * V) C := by
  classical
  intro ι _ e f he hf
  have he' : Orthonormal ℂ (fun i => V (e i)) := by
    rw [orthonormal_iff_ite] at he ⊢
    simp_all
  tauto

/-- Composition on the left with an operator whose adjoint is an isometry. -/
lemma TraceBound.isometry_comp 
    (V' : H → H) (hV' : ∀ x y, inner ℂ (V' x) (V' y) = inner ℂ x y)
    (hadj : ∀ x y, inner ℂ x (V y) = inner ℂ (V' x) y) : TraceBound (V * T) C := by
  classical
  intro ι _ e f he hf
  have hf' : Orthonormal ℂ (fun i => V' (f i)) := by
    rw [orthonormal_iff_ite] at hf ⊢
    simp_all
  have := hT ι e (fun i => V' (f i)) he hf'
  simpa [hadj] using this

end

/-- A rank-one operator `x ⟨y, ·⟩` has trace norm at most `‖x‖ ‖y‖`. -/
lemma TraceBound.rankOne (x y : H) :
    TraceBound ((ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ y)) (‖x‖ * ‖y‖) := by
  intro ι _ e f he hf
  simp  [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, inner_smul_right]
  refine (norm_sum_le _ _).trans ?_
  simp  
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖inner ℂ (f i) x‖) (fun i => ‖inner ℂ y (e i)‖)
  have hy : ∑ i, ‖inner ℂ y (e i)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    have := he.sum_inner_products_le y (s := Finset.univ)
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) this
    rw [← inner_conj_symm, RCLike.norm_conj]
  have hx : ∑ i, ‖inner ℂ (f i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := hf.sum_inner_products_le x
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)) (hCS.trans ?_)
  exact mul_le_mul (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hx⟩)
    (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hy⟩) (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The trace-norm bound also controls the sum of the absolute values of the diagonal terms. -/
lemma TraceBound.sum_norm_le {T : H →L[ℂ] H} {C : ℝ} (h : TraceBound T C)
    (ι : Type) [Fintype ι] (e f : ι → H) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    ∑ i, ‖inner ℂ (f i) (T (e i))‖ ≤ C := by
  classical
  set w : ι → ℂ := fun i => inner ℂ (f i) (T (e i)) with hw
  set c : ι → ℂ := fun i => if w i = 0 then 1 else w i / (‖w i‖ : ℂ)
  have hc : ∀ i, ‖c i‖ = 1 := by
    aesop
  have hcw : ∀ i, conj (c i) * w i = ‖w i‖ := by
    intro i; simp  [c]; split_ifs with h
    simp_all
    · rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]; push_cast
      grind
  have hf' : Orthonormal ℂ (fun i => c i • f i) := by
    rw [orthonormal_iff_ite] at hf ⊢
    intro i j
    rw [inner_smul_left, inner_smul_right, hf i j]
    split_ifs with hij
    simp_all [mul_one, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
  have := h ι e _ he hf'
  simp only [inner_smul_left] at this
  have h2 : ∀ x, (starRingEnd ℂ) (c x) * inner ℂ (f x) (T (e x)) = ‖w x‖ := hcw
  simp only [h2, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs] at this
  grind

/-- The functional `T ↦ ∑ᵢ ⟨fᵢ, T eᵢ⟩`. -/
def diagFunctional {ι : Type} [Fintype ι] (e f : ι → H) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  ∑ i, (innerSL ℂ (f i)).comp ((ContinuousLinearMap.apply ℂ H (e i)))

lemma diagFunctional_apply {ι : Type} [Fintype ι] (e f : ι → H) (T : H →L[ℂ] H) :
    diagFunctional e f T = ∑ i, inner ℂ (f i) (T (e i)) := by
  simp [diagFunctional]

/-- Trace-norm bounds pass to norm limits. -/
lemma TraceBound.of_tendsto {α : Type*} {T : α → H →L[ℂ] H} {T₀ : H →L[ℂ] H} {C : ℝ}
    {l : Filter α} [l.NeBot]
    (hT : Tendsto T l (𝓝 T₀)) (h : ∀ᶠ n in l, TraceBound (T n) C) : TraceBound T₀ C := by
  intro ι _ e f he hf
  exact le_of_tendsto (by simpa only [Function.comp_apply, diagFunctional_apply] using
    (((diagFunctional e f).continuous.tendsto T₀).comp hT).norm)
    (h.mono fun _ hn => hn ι e f he hf)

/-- Trace-norm bound for an increment with trace-norm bounded derivative. -/
lemma TraceBound.sub_of_hasDerivAt {g g' : ℝ → H →L[ℂ] H} {a b C : ℝ} (hab : a ≤ b)
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t) (h : ∀ t ∈ Icc a b, TraceBound (g' t) C) :
    TraceBound (g b - g a) (C * (b - a)) := by
  intro ι _ e f he hf
  set L := diagFunctional e f
  have hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun t => L (g t)) (L (g' t)) (Icc a b) t :=
    fun t ht => ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hg t ht)).hasDerivWithinAt
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' hd
    (fun t ht => by rw [diagFunctional_apply]; exact h t (Ico_subset_Icc_self ht) ι e f he hf)
    b ⟨hab, le_rfl⟩
  rw [← map_sub, diagFunctional_apply] at hb
  assumption

variable [CompleteSpace H]

/-- Trace-norm bound for an interval integral. -/
lemma TraceBound.intervalIntegral {g : ℝ → H →L[ℂ] H} {a b C : ℝ}
    (h : ∀ t ∈ uIoc a b, TraceBound (g t) C) (hC : 0 ≤ C) :
    TraceBound (∫ t in a..b, g t) (C * |b - a|) := by
  intro ι _ e f he hf
  by_cases hi : IntervalIntegrable g volume a b
  · have := (diagFunctional e f).intervalIntegral_comp_comm hi
    rw [diagFunctional_apply] at this
    rw [← this]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht => ?_)
    rw [diagFunctional_apply]; tauto
  · rw [intervalIntegral.integral_undef hi]; simp; positivity

section

variable {T V : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C) (hV : V ∈ unitary (H →L[ℂ] H))
include T V C hT hV

/-- Composition on either side with a unitary operator preserves trace-norm bounds. -/
lemma TraceBound.unitary_mul  : TraceBound (V * T) C := by
  refine hT.isometry_comp (⇑(star V)) (fun x y => ?_) (fun x y => ?_)
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint, (Unitary.mem_iff.mp hV).2,
      ContinuousLinearMap.one_apply]
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma TraceBound.mul_unitary  : TraceBound (T * V) C := by
  refine hT.comp_isometry (fun x y => ?_)
  rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
    (Unitary.mem_iff.mp hV).1, ContinuousLinearMap.one_apply]

end

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
include U hU

/-- Finite partial sums of `∑_{z ≠ 1} mult(z) |z - 1|` are bounded by a trace-norm bound. -/
lemma sum_eigenMult_mul_norm_le {C : ℝ} (hT : TraceBound (U - 1) C)
    (s : Finset {z : ℂ // z ≠ 1}) :
    ∑ z ∈ s, (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖ ≤ C := by
  classical
  obtain ⟨e, he, heig⟩ := exists_orthonormal_eigen_family hU s
  have key := hT.sum_norm_le _ e e he he
  have hterm : ∀ p : (Σ z : s, Fin (eigenMult U z)),
      ‖inner ℂ (e p) ((U - 1) (e p))‖ = ‖((p.1 : {z : ℂ // z ≠ 1}) : ℂ) - 1‖ := by
    intro p
    have hs : ∀ (c : ℂ) (v : H), c • v - v = (c - 1) • v := fun c v => by
      rw [sub_smul, one_smul]
    rw [ContinuousLinearMap.sub_apply, heig, ContinuousLinearMap.one_apply, hs,
      inner_smul_right, inner_self_eq_norm_sq_to_K, he.1 p]
    simp
  simp only [hterm] at key
  refine le_trans (le_of_eq ?_) key
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_coe_sort s]

/-- For a unitary perturbation of the identity, a trace-norm bound controls the
multiplicity-weighted sum of distances from `1`. -/
theorem summable_eigenMult_mul_norm {C : ℝ} (hT : TraceBound (U - 1) C) :
    Summable (fun z : {z : ℂ // z ≠ 1} => (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖) :=
  summable_of_sum_le (fun _ => by positivity) (sum_eigenMult_mul_norm_le hU hT)

end

end General

/-- `D_N = 2 P_0 - P_1` has trace norm at most `3`. -/
theorem traceBound_diagN : TraceBound diagN 3 := by
  have h0 := (TraceBound.rankOne (lp.single 2 0 (1 : ℂ) : Ell2)
    (lp.single 2 0 (1 : ℂ) : Ell2)).smul (2 : ℂ)
  have h1 := TraceBound.rankOne (lp.single 2 1 (1 : ℂ) : Ell2) (lp.single 2 1 (1 : ℂ) : Ell2)
  have h := h0.sub h1
  rw [diagN]
  convert h using 1
  norm_num

/-- Conjugating `D_N` by a unitary keeps the trace-norm bound `3`. -/
theorem traceBound_conj_diagN {W : Ell2 →L[ℂ] Ell2} (hW : W ∈ unitary (Ell2 →L[ℂ] Ell2)) :
    TraceBound (star W * diagN * W) 3 :=
  (traceBound_diagN.unitary_mul (Unitary.star_mem hW)).mul_unitary hW

/-- The curvature operator `Q_E` has trace norm at most `(1/4) · 3 R K · 2π`, where `R` bounds
`|γ(θ) - γ(0)|` on `[0, 2π]` and `K` is a Lipschitz constant of `γ`. -/
theorem traceBound_curvatureOp {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    TraceBound (curvatureOp γ W) (1 / 4 * ((R * K * 3) * (2 * π))) := by
  have hR0 := (norm_nonneg _).trans (hR 0 ⟨le_rfl, by positivity⟩)
  have hint : TraceBound (∫ θ in (0 : ℝ)..(2 * π), areaDensity γ θ • (star (W θ) * diagN * W θ))
      ((R * K * 3) * |2 * π - 0|) := by
    refine TraceBound.intervalIntegral (fun θ hθ => ?_) (by positivity)
    have hθ' : θ ∈ Icc 0 (2 * π) := by
      rw [uIoc_of_le (by positivity)] at hθ; grind
    refine ((traceBound_conj_diagN (transport_mem_unitary hK hW hθ')).real_smul _).mono ?_
    exact mul_le_mul_of_nonneg_right (abs_areaDensity_le hK hR hθ') (by norm_num)
  rw [sub_zero, abs_of_pos (by positivity)] at hint
  have := hint.real_smul (1 / 4)
  rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at this

lemma monodromy_mem_unitary' {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) :
    monodromy W ∈ unitary (Ell2 →L[ℂ] Ell2) :=
  Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩)

/-- The trace norm of `U_E - I` grows at most linearly in energy. -/
theorem exists_linear_traceBound_monodromyAt {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E, 0 ≤ E → TraceBound (monodromyAt γ E - 1) (C * E) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * π))
    (hK.continuous.sub (continuous_const (y := γ 0))).continuousOn
  choose Ws hWs using fun E => transport_exists_of_lipschitz γ hK E
  let C := 1 / 4 * ((R * K * 3) * (2 * π))
  have hC := (traceBound_curvatureOp hK hR (hWs 0)).nonneg
  have h0 : monodromy (Ws 0) = 1 := by
    rw [monodromy, transport_zero_energy (hWs 0), ← ContinuousLinearMap.star_eq_adjoint, star_one]
  have hlim : Tendsto (fun δ => monodromy (Ws δ)) (𝓝 0) (𝓝 1) := by
    rw [← h0]
    exact ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp
      (tendsto_transport_energy hK hWs 0 ⟨by positivity, le_rfl⟩)
  refine ⟨C, hC, fun E hE => ?_⟩
  rw [monodromyAt_eq hK (hWs E)]
  rcases eq_or_lt_of_le hE with rfl | hE
  · simpa [h0] using (TraceBound.zero (H := Ell2))
  refine TraceBound.of_tendsto (l := 𝓝[>] (0 : ℝ)) ((tendsto_const_nhds.sub hlim).mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [Ioo_mem_nhdsGT hE] with δ hδ
  apply TraceBound.mono _ (mul_le_mul_of_nonneg_left (sub_le_self _ hδ.1.le) hC)
  refine TraceBound.sub_of_hasDerivAt (g := fun t => monodromy (Ws t))
    (g' := fun t => Complex.I • (curvatureOp γ (Ws t) * monodromy (Ws t))) hδ.2.le
    (fun t ht => hasDerivAt_monodromy_energy hK hclosed hWs (hδ.1.trans_le ht.1)) (fun t _ => ?_)
  simpa only [Complex.norm_I, one_mul] using
    (((traceBound_curvatureOp hK hR (hWs t)).mul_unitary (monodromy_mem_unitary' hK (hWs t))).smul Complex.I)

/-- The distances from `1` of the monodromy eigenvalues are summable with multiplicity. -/
theorem summable_eigenMult_monodromy {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    Summable (fun z : {z : ℂ // z ≠ 1} => (eigenMult (monodromy W) z : ℝ) * ‖(z : ℂ) - 1‖) := by
  obtain ⟨C, -, hC⟩ := exists_linear_traceBound_monodromyAt hK hclosed
  exact summable_eigenMult_mul_norm (monodromy_mem_unitary' hK hW) (monodromyAt_eq hK hW ▸ hC E hE)

end PolyaNeumann

end
