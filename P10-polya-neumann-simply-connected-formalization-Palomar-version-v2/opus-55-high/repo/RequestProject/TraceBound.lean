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

variable {T : H →L[ℂ] H} {S T : H →L[ℂ] H} {T V : H →L[ℂ] H} {C : ℝ} {C D : ℝ}

lemma TraceBound.nonneg (h : TraceBound T C) : 0 ≤ C := by
  have he : Orthonormal ℂ (fun _ : Empty => (0 : H)) := ⟨fun i => i.elim, fun i => i.elim⟩
  have := h Empty _ _ he he
  simp_all

lemma TraceBound.mono (h : TraceBound T C) (hCD : C ≤ D) :
    TraceBound T D := fun ι _ e f he hf => (h ι e f he hf).trans hCD

lemma TraceBound.zero : TraceBound (0 : H →L[ℂ] H) 0 := by
  intro ι _ e f _ _; simp

lemma TraceBound.add (hS : TraceBound S C) (hT : TraceBound T D) :
    TraceBound (S + T) (C + D) := by
  intro ι _ e f he hf
  simp only [ContinuousLinearMap.add_apply, inner_add_right, Finset.sum_add_distrib]
  exact (norm_add_le _ _).trans (add_le_add (hS ι e f he hf) (hT ι e f he hf))

lemma TraceBound.smul (hT : TraceBound T C) (c : ℂ) :
    TraceBound (c • T) (‖c‖ * C) := by
  intro ι _ e f he hf
  simp only [ContinuousLinearMap.smul_apply, inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hT ι e f he hf) (norm_nonneg _)

lemma TraceBound.neg (hT : TraceBound T C) : TraceBound (-T) C := by
  simpa using hT.smul (-1)

lemma TraceBound.sub (hS : TraceBound S C) (hT : TraceBound T D) :
    TraceBound (S - T) (C + D) := by
  rw [sub_eq_add_neg]; exact hS.add hT.neg

lemma TraceBound.real_smul (hT : TraceBound T C) (c : ℝ) :
    TraceBound (c • T) (|c| * C) := by
  have := hT.smul c
  simp_all

/-- Composition on the right with an isometry. -/
lemma TraceBound.comp_isometry (hT : TraceBound T C)
    (hV : ∀ x y, inner ℂ (V x) (V y) = inner ℂ x y) : TraceBound (T * V) C := by
  classical
  intro ι _ e f he hf
  simpa using hT ι (fun i => V (e i)) f (by
    simp_all [orthonormal_iff_ite]) hf

/-- Composition on the left with an operator whose adjoint is an isometry. -/
lemma TraceBound.isometry_comp (hT : TraceBound T C)
    (V' : H → H) (hV' : ∀ x y, inner ℂ (V' x) (V' y) = inner ℂ x y)
    (hadj : ∀ x y, inner ℂ x (V y) = inner ℂ (V' x) y) : TraceBound (V * T) C := by
  classical
  intro ι _ e f he hf
  have := hT ι e (fun i => V' (f i)) he (by
    simp_all [orthonormal_iff_ite])
  simp_all

/-- A rank-one operator `x ⟨y, ·⟩` has trace norm at most `‖x‖ ‖y‖`. -/
lemma TraceBound.rankOne (x y : H) :
    TraceBound ((ContinuousLinearMap.toSpanSingleton ℂ x).comp (innerSL ℂ y)) (‖x‖ * ‖y‖) := by
  intro ι _ e f he hf
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, inner_smul_right]
  refine (norm_sum_le _ _).trans ?_
  simp 
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => mul_comm _ _)) ((Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => ‖inner ℂ (f i) x‖) (fun i => ‖inner ℂ y (e i)‖)).trans ?_)
  exact mul_le_mul (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, hf.sum_inner_products_le x⟩)
    (Real.sqrt_le_iff.mpr ⟨norm_nonneg _, by
    have := he.sum_inner_products_le y (s := Finset.univ)
    refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) this
    rw [← inner_conj_symm, RCLike.norm_conj]⟩) (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The trace-norm bound also controls the sum of the absolute values of the diagonal terms. -/
lemma TraceBound.sum_norm_le (h : TraceBound T C)
    (ι : Type) [Fintype ι] (e f : ι → H) (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    ∑ i, ‖inner ℂ (f i) (T (e i))‖ ≤ C := by
  classical
  set w : ι → ℂ := fun i => inner ℂ (f i) (T (e i)) with hw
  set c : ι → ℂ := fun i => if w i = 0 then 1 else w i / ‖w i‖
  have hc : ∀ i, ‖c i‖ = 1 := by
    intro i; simp only [c]; split_ifs with h
    all_goals simp_all
  have hcw : ∀ i, conj (c i) * w i = ‖w i‖ := by
    intro i; simp only [c]; split_ifs with h
    · simp_all
    · rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]; push_cast
      field_simp 
  have hf' : Orthonormal ℂ (fun i => c i • f i) := by
    rw [orthonormal_iff_ite] at hf ⊢
    simp_all [inner_smul_left, inner_smul_right, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have := h ι e _ he hf'
  simp only [inner_smul_left] at this
  have h2 : ∀ x, (starRingEnd ℂ) (c x) * inner ℂ (f x) (T (e x)) = ‖w x‖ := hcw
  simp only [h2, ← Complex.ofReal_sum, Complex.norm_real] at this
  exact (le_abs_self _).trans this

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
  exact le_of_tendsto (by
    have := ((diagFunctional e f).continuous.tendsto T₀).comp hT
    simp only [Function.comp_def, diagFunctional_apply] at this
    exact this.norm) (h.mono fun n hn => hn ι e f he hf)

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
  rwa [← map_sub, diagFunctional_apply] at hb

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
    rw [diagFunctional_apply]; exact h t ht ι e f he hf
  · rw [intervalIntegral.integral_undef hi]; simp; positivity

/-- Composition on either side with a unitary operator preserves trace-norm bounds. -/
lemma TraceBound.unitary_mul {T V : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C)
    (hV : V ∈ unitary (H →L[ℂ] H)) : TraceBound (V * T) C := by
  refine hT.isometry_comp (⇑(star V)) (fun x y => ?_) (fun x y => ?_)
  · rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
      ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
      ← ContinuousLinearMap.star_eq_adjoint, (Unitary.mem_iff.mp hV).2,
      ContinuousLinearMap.one_apply]
  simp [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

lemma TraceBound.mul_unitary {T V : H →L[ℂ] H} {C : ℝ} (hT : TraceBound T C)
    (hV : V ∈ unitary (H →L[ℂ] H)) : TraceBound (T * V) C := by
  refine hT.comp_isometry (fun x y => ?_)
  simp [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, (Unitary.mem_iff.mp hV).1]

/-- Eigenvectors of a unitary operator for distinct eigenvalues are orthogonal. -/
lemma inner_eq_zero_of_eigen_unitary {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    {z z' : ℂ} {v w : H} (hv : U v = z • v) (hw : U w = z' • w) (hzz : z ≠ z')
    (hz : ‖z‖ = 1) : inner ℂ v w = 0 := by
  have hpres : inner ℂ (U v) (U w) = inner ℂ v w := by
    simp [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def, (Unitary.mem_iff.mp hU).1]
  rw [hv, hw, inner_smul_left, inner_smul_right] at hpres
  have : (conj z * z' - 1) * inner ℂ v w = 0 := by grind
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) (by
    intro h
    have : z * (conj z * z') = z := by simp_all
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq] at this
    simp_all)
  assumption

/-- If `U` is unitary, `U - I` is compact and has a trace-norm bound, then the
multiplicity-weighted sum `∑_{z ≠ 1} mult(z) |z - 1|` converges. -/
theorem summable_eigenMult_mul_norm {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C) :
    Summable (fun z : {z : ℂ // z ≠ 1} => eigenMult U z * ‖(z : ℂ) - 1‖) := by
  classical
  refine summable_of_sum_le (fun z => by positivity) (c := C) (fun s => ?_)
  let ι := Σ z : s, Fin (eigenMult U z)
  let b : ∀ z : {z : ℂ // z ≠ 1}, OrthonormalBasis (Fin (eigenMult U z)) ℂ
      (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) := fun z =>
    haveI := (fun z => finiteDimensional_eigenspace hC z.2) z; stdOrthonormalBasis ℂ _
  let e : ι → H := fun p => b p.1.1 p.2
  have heig : ∀ p : ι, U (e p) = (p.1.1 : ℂ) • e p := fun p =>
    Module.End.mem_eigenspace_iff.mp (b p.1.1 p.2).2
  have he : Orthonormal ℂ e := by
    rw [orthonormal_iff_ite]
    rintro ⟨⟨z, hz⟩, k⟩ ⟨⟨z', hz'⟩, k'⟩
    by_cases hzz : z = z'
    · subst hzz
      have := (orthonormal_iff_ite.mp (b z).orthonormal) k k'
      rw [← Submodule.coe_inner]
      grind
    · rw [inner_eq_zero_of_eigen_unitary hU (heig _) (heig ⟨⟨z', hz'⟩, k'⟩)
        (fun h => hzz (Subtype.ext h)) (norm_eq_one_of_eigen hU (by
        have := (b z).orthonormal.ne_zero k
        simp_all [e]) (heig _))]
      grind
  have key := hT.sum_norm_le ι e e he he
  have hterm : ∀ p : ι, ‖inner ℂ (e p) ((U - 1) (e p))‖ = ‖(p.1.1 : ℂ) - 1‖ := by
    intro p
    have hs : ∀ (c : ℂ) (v : H), c • v - v = (c - 1) • v := fun c v => by
      rw [sub_smul, one_smul]
    simp [heig, hs, inner_smul_right, he.1 p]
  simp only [hterm] at key
  refine le_trans (le_of_eq ?_) key
  rw [Fintype.sum_sigma]
  simp [← Finset.sum_coe_sort s]

/-- **Lemma 9.1 (absolute summability, abstract form).** Let `U` be unitary. If only finitely
many eigenvalues of `U` lie in the open upper half-plane and the multiplicity-weighted sum
`∑_{z ≠ 1} mult(z) |z - 1|` converges, then the multiplicity-weighted phase sum
`∑_{z ≠ 1} mult(z) Arg₋ z` converges absolutely (on the lower semicircle
`|Arg₋ z| ≤ (π/2) |z - 1|`). -/
theorem summable_phaseTerm_of_upper_finite {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hfin : {z : ℂ | 0 < z.im ∧ ∃ v : H, v ≠ 0 ∧ U v = z • v}.Finite)
    (hs : Summable (fun z : {z : ℂ // z ≠ 1} => eigenMult U z * ‖(z : ℂ) - 1‖)) :
    Summable (phaseTerm U) := by
  classical
  set F := {z : ℂ | 0 < z.im ∧ ∃ v : H, v ≠ 0 ∧ U v = z • v}
  have hg2 : Summable (fun z : {z : ℂ // z ≠ 1} =>
      (if (z : ℂ) ∈ F then 2 * π * eigenMult U z else 0)) := by
    refine summable_of_finite_support ((hfin.preimage Subtype.val_injective.injOn).subset ?_)
    simp_all
  refine Summable.of_norm_bounded ((hs.mul_left (π / 2)).add hg2) (fun z => ?_)
  rw [phaseTerm, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
  have hpos : 0 ≤ (if (z : ℂ) ∈ F then 2 * π * eigenMult U z else 0) := by
    positivity
  by_cases hm : eigenMult U z = 0
  · simp_all
  have hm'  :=
    Nat.pos_of_ne_zero hm
  haveI := Module.finite_of_finrank_pos hm'
  obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm'
  have hv0' : v ≠ 0 := fun h => hv0 (by simp_all)
  have hveig  := Module.End.mem_eigenspace_iff.mp hv
  have hz1  := norm_eq_one_of_eigen hU hv0' hveig
  by_cases him : (z : ℂ).im ≤ 0
  · have := abs_argNeg_le_of_im_nonpos hz1 z.2 him
    have h1 : eigenMult U z * |argNeg z| ≤
        π / 2 * (eigenMult U z * ‖(z : ℂ) - 1‖) := by
      rw [mul_left_comm]
      simp_all
    linarith
  · rw [if_pos ⟨lt_of_not_ge him, v, hv0', hveig⟩]
    have hI := argNeg_mem_Ioo hz1 z.2
    have habs : |argNeg z| ≤ 2 * π := by
      grind
    have h1 : eigenMult U z * |argNeg z| ≤ 2 * π * eigenMult U z := by
      simp_all [mul_comm (2 * π)]
    have h2 : 0 ≤ π / 2 * (eigenMult U z * ‖(z : ℂ) - 1‖) := by positivity
    linarith

/-- If `e^{it}` is close to `1` with `0 < t < π`, then `cot(t/2)` is large. -/
lemma cot_gt_of_norm_exp_sub_one_lt {t A : ℝ} (ht0 : 0 < t) (htπ : t < π)
    (h : ‖Complex.exp (t * Complex.I) - 1‖ < 1 / (|A| + 1)) : A < Real.cot (t / 2) := by
  have hn : ‖Complex.exp (t * Complex.I) - 1‖ = 2 * Real.sin (t / 2) := by
    rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
      abs_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))]
  rw [hn] at h
  have hs : 0 < Real.sin (t / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hc : 0 < Real.cos (t / 2) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hs2 : Real.sin (t / 2) * (|A| + 1) < 1 / 2 := by
    rw [lt_div_iff₀ (by positivity)] at h; linarith
  have hs1 : Real.sin (t / 2) < 1 / 2 := by nlinarith [abs_nonneg A]
  have hsq := Real.sin_sq_add_cos_sq (t / 2)
  have hc2 : 1 / 2 < Real.cos (t / 2) := by nlinarith
  rw [Real.cot_eq_cos_div_sin, lt_div_iff₀ hs]
  nlinarith [le_abs_self A]

/-- **Lemma 9.1 (finitely many upper-semicircle eigenvalues, abstract form).** Let `U` be
unitary with `U - I` compact and `∑_{z ≠ 1} mult(z) |z - 1| < ∞`. Suppose the Cayley transform
of `U` is bounded above by `A` on eigenvectors: whenever `U v = e^{it} v` with `v ≠ 0` and
`0 < t < 2π`, `cot(t/2) ≤ A`. Then only finitely many eigenvalues of `U` lie in the open upper
half-plane: they stay away from `1`, and only finitely many eigenvalues do. -/
theorem upper_eigen_finite_of_cot_bound {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1))
    (hs : Summable (fun z : {z : ℂ // z ≠ 1} => eigenMult U z * ‖(z : ℂ) - 1‖))
    (A : ℝ) (hA : ∀ t : ℝ, 0 < t → t < 2 * π → ∀ v : H, v ≠ 0 →
      U v = Complex.exp (t * Complex.I) • v → Real.cot (t / 2) ≤ A) :
    {z : ℂ | 0 < z.im ∧ ∃ v : H, v ≠ 0 ∧ U v = z • v}.Finite := by
  set c : ℝ := 1 / (|A| + 1) with hcdef
  have hc : 0 < c := by positivity
  have hS : {z : {z : ℂ // z ≠ 1} | c ≤ eigenMult U z * ‖(z : ℂ) - 1‖}.Finite := by
    have := hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hc)
    simp_all
  refine (hS.image Subtype.val).subset ?_
  rintro z ⟨him, v, hv0, hv⟩
  have hz1 : z ≠ 1 := by rintro rfl; simp_all
  refine ⟨⟨z, hz1⟩, ?_, rfl⟩
  have hnorm  := norm_eq_one_of_eigen hU hv0 hv
  haveI := finiteDimensional_eigenspace hC hz1
  have hmult : 1 ≤ eigenMult U z := Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simp_all)⟩
  calc c ≤ ‖z - 1‖ := (by
    by_contra hlt
    push_neg at hlt
    set t := Complex.arg z with ht
    have ht0 : 0 < t := by
      rcases (Complex.arg_nonneg_iff.mpr him.le).lt_or_eq with h | h
      · assumption
      · have := Complex.arg_eq_zero_iff.mp h.symm
        linarith 
    have htπ : t < π := by
      rcases (Complex.arg_le_pi z).lt_or_eq with h | h
      · assumption
      · have := Complex.arg_eq_pi_iff.mp h
        linarith 
    have hz : z = Complex.exp (t * Complex.I) := by
      have := Complex.norm_mul_exp_arg_mul_I z
      simp_all
    rw [hz] at hlt hv
    have h1 := cot_gt_of_norm_exp_sub_one_lt ht0 htπ hlt
    grind)
    _ = 1 * ‖z - 1‖ := (one_mul _).symm
    _ ≤ eigenMult U z * ‖z - 1‖ :=
        mul_le_mul_of_nonneg_right (by simp_all) (norm_nonneg _)

end General

variable {γ : ℝ → ℂ} {K : NNReal}

/-- `D_N = 2 P_0 - P_1` has trace norm at most `3`. -/
theorem traceBound_diagN : TraceBound diagN 3 := by
  rw [diagN]
  convert ((TraceBound.rankOne (lp.single 2 0 1)
    (lp.single 2 0 1)).smul 2).sub (TraceBound.rankOne (lp.single 2 1 1) (lp.single 2 1 1)) using 1
  norm_num

/-- Conjugating `D_N` by a unitary keeps the trace-norm bound `3`. -/
theorem traceBound_conj_diagN {W : Ell2 →L[ℂ] Ell2} (hW : W ∈ unitary (Ell2 →L[ℂ] Ell2)) :
    TraceBound (star W * diagN * W) 3 :=
  (traceBound_diagN.unitary_mul (Unitary.star_mem hW)).mul_unitary hW

/-- The curvature operator `Q_E` has trace norm at most `(1/4) · 3 R K · 2π`, where `R` bounds
`|γ(θ) - γ(0)|` on `[0, 2π]` and `K` is a Lipschitz constant of `γ`. -/
theorem traceBound_curvatureOp (hK : LipschitzWith K γ) {R : ℝ}
    (hR : ∀ θ ∈ Icc 0 (2 * π), ‖γ θ - γ 0‖ ≤ R) {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    TraceBound (curvatureOp γ W) (1 / 4 * ((R * K * 3) * (2 * π))) := by
  have hR0  := (norm_nonneg _).trans (hR 0 ⟨le_rfl, by positivity⟩)
  have hint : TraceBound (∫ θ in 0..(2 * π), areaDensity γ θ • (star (W θ) * diagN * W θ))
      ((R * K * 3) * |2 * π - 0|) := by
    refine TraceBound.intervalIntegral (fun θ hθ => ?_) (by positivity)
    have hθ' : θ ∈ Icc 0 (2 * π) := by
      rw [uIoc_of_le (by positivity)] at hθ; grind
    refine ((traceBound_conj_diagN (transport_mem_unitary hK hW hθ')).real_smul _).mono ?_
    exact mul_le_mul_of_nonneg_right (abs_areaDensity_le hK hR hθ') (by norm_num)
  rw [sub_zero, abs_of_pos (by positivity)] at hint
  have := hint.real_smul (1 / 4)
  rwa [abs_of_pos (by norm_num)] at this

/-- **Lemma 4.7 (trace-norm bound for `V_E - I`).** For a closed Lipschitz curve and `E ≥ 0`,
the endpoint `V_E = W_E(L)` of the transport satisfies a trace-norm bound for `V_E - I`. -/
theorem exists_traceBound_transport_sub_one (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : ∃ C, TraceBound (W (2 * π) - 1) C := by
  have h2π : (2 * π) ∈ Icc 0 (2 * π) := ⟨by positivity, le_rfl⟩
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn 
     (hK.continuous.sub continuous_const).continuousOn
  set Cq : ℝ := 1 / 4 * ((R * K * 3) * (2 * π)) with hCq
  choose Ws hWs using transport_exists_of_lipschitz γ hK
  rw [transport_unique_of_lipschitz γ hK E hW (hWs E) h2π]
  rcases eq_or_lt_of_le hE with rfl | hEpos
  · rw [transport_zero_energy (hWs 0), sub_self]; exact ⟨0, TraceBound.zero⟩
  have hinc : ∀ δ ∈ Ioc 0 E, TraceBound (Ws E (2 * π) - Ws δ (2 * π)) (Cq * (E - δ)) := by
    intro δ hδ
    refine TraceBound.sub_of_hasDerivAt (g := fun E' => Ws E' (2 * π))
       hδ.2
      (fun t ht => hasDerivAt_transport_energy hK hclosed hWs (hδ.1.trans_le ht.1)) ?_
    intro t _
    have h := ((traceBound_curvatureOp hK hR (hWs t)).unitary_mul
      (transport_mem_unitary hK (hWs t) h2π)).smul Complex.I
    rw [Complex.norm_I, one_mul] at h
    exact h.neg
  -- let `δ → 0⁺`
  have hlim : Tendsto (fun δ => Ws E (2 * π) - Ws δ (2 * π)) (𝓝[>] 0)
      (𝓝 (Ws E (2 * π) - 1)) := by
    have h := tendsto_transport_energy hK hWs 0 h2π
    rw [transport_zero_energy (hWs 0)] at h
    exact (tendsto_const_nhds.sub h).mono_left nhdsWithin_le_nhds
  refine ⟨Cq * E, TraceBound.of_tendsto hlim ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hEpos] with δ hδ
  exact (hinc δ ⟨hδ.1, hδ.2.le⟩).mono (mul_le_mul_of_nonneg_left (by grind) (traceBound_curvatureOp hK hR (hWs 0)).nonneg)

/-- **Lemma 4.7 (trace-norm bound for `U_E - I`).** For a closed Lipschitz curve and `E ≥ 0`,
the monodromy `U_E = V_E^*` satisfies a trace-norm bound for `U_E - I`. -/
theorem exists_traceBound_monodromy_sub_one (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) : ∃ C, TraceBound (monodromy W - 1) C := by
  obtain ⟨C, hC⟩ := exists_traceBound_transport_sub_one hK hclosed hE hW
  have hU := transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩
  have heq : monodromy W - 1 = -(star (W (2 * π)) * (W (2 * π) - 1)) := by
    simp [monodromy, ← ContinuousLinearMap.star_eq_adjoint, mul_sub, (Unitary.mem_iff.mp hU).1]
  rw [heq]
  exact ⟨C, (hC.unitary_mul (Unitary.star_mem hU)).neg⟩

/-- **Lemma 9.1 (trace-class part).** For a closed Lipschitz curve and `E ≥ 0`, the
multiplicity-weighted sum `∑_{z ≠ 1} mult(z) |z - 1|` over the eigenvalues of the monodromy
`U_E` converges. -/
theorem summable_eigenMult_monodromy (hK : LipschitzWith K γ)
    (hclosed : γ (2 * π) = γ 0) {E : ℝ} (hE : 0 ≤ E) {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) :
    Summable (fun z : {z : ℂ // z ≠ 1} => eigenMult (monodromy W) z * ‖(z : ℂ) - 1‖) := by
  obtain ⟨C, hC⟩ := exists_traceBound_monodromy_sub_one hK hclosed hE hW
  exact summable_eigenMult_mul_norm (Unitary.star_mem (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩))
    (isCompactOperator_monodromy_sub_one hK hclosed hE hW) hC

end PolyaNeumann

end
