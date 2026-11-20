module

public import RequestProject.SmallKernel

/-!
# Lemma 8.6 (negative index at small energy): the reduction to a Schur complement

For a bounded operator `U` on `ℓ²` put

  `F(w) = -4 Im ⟨w, U w⟩`,   `B(x, w) = 2i ⟨x, (U - U^*) w⟩`,

so that `B` is a Hermitian form with `B(w, w) = F(w)`; on Herglotz data `F` is the Herglotz form
(`herglotzForm_eq_im`). If `F(x) < 0`, the Schur complement

  `C(w) = F(w) - |B(x, w)|² / F(x)`

is invariant under `w ↦ w + t x` (`imSchur_add_smul`), and `C ≥ 0` on a dense set forces
`F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}` (`nonneg_of_imSchur_nonneg`): this is the
index count `ind₋ 𝒜_E ≤ 1` of Lemma 8.6.

The analytic input (Lemmas 8.2–8.5, proved in `SmallEnergyCore.lean`) is `small_energy_schur_core`: for small `E > 0`,
`F(e₀) < 0`, and every finitely supported `w` can be shifted along `e₀` to a vector on which
`C ≥ 0`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

section

variable (U : Ell2 →L[ℂ] Ell2)
include U

/-- The form `F(w) = -4 Im ⟨w, U w⟩`. -/
def imForm  (w : Ell2) : ℝ := -4 * (⟪w, U w⟫_ℂ).im

/-- The Hermitian form `B(x, w) = 2i ⟨x, (U - U^*) w⟩`. -/
def imPair  (x w : Ell2) : ℂ :=
  2 * Complex.I * ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ

/-- The Schur complement `C(w) = F(w) - |B(x, w)|² / F(x)`. -/
def imSchur  (x w : Ell2) : ℝ :=
  imForm U w - ‖imPair U x w‖ ^ 2 / imForm U x

lemma imPair_self  (w : Ell2) : imPair U w w = imForm U w := by
  unfold imPair imForm
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, ContinuousLinearMap.adjoint_inner_right]
  have hz : ⟪U w, w⟫_ℂ = conj ⟪w, U w⟫_ℂ := (inner_conj_symm _ _).symm
  rw [hz]
  generalize ⟪w, U w⟫_ℂ = z
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  ring

lemma imPair_conj  (x w : Ell2) : imPair U w x = conj (imPair U x w) := by
  unfold imPair
  have h : ⟪w, (U - ContinuousLinearMap.adjoint U) x⟫_ℂ =
      -conj ⟪x, (U - ContinuousLinearMap.adjoint U) w⟫_ℂ := by
    rw [inner_conj_symm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      inner_sub_left, inner_sub_right, ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.adjoint_inner_right]
    ring
  rw [h, map_mul, map_mul, Complex.conj_I, map_ofNat]
  ring

lemma imPair_add_right  (x v w : Ell2) :
    imPair U x (v + w) = imPair U x v + imPair U x w := by
  unfold imPair; rw [map_add, inner_add_right]; ring

lemma imPair_smul_right  (x w : Ell2) (t : ℂ) :
    imPair U x (t • w) = t * imPair U x w := by
  unfold imPair; rw [map_smul, inner_smul_right]; ring

lemma imPair_add_left  (x v w : Ell2) :
    imPair U (v + w) x = imPair U v x + imPair U w x := by
  unfold imPair; rw [inner_add_left]; ring

lemma imPair_smul_left  (x w : Ell2) (t : ℂ) :
    imPair U (t • w) x = conj t * imPair U w x := by
  unfold imPair; rw [inner_smul_left]; ring

/-- The Schur complement is invariant under `w ↦ w + t x`. -/
lemma imSchur_add_smul  {x : Ell2} (hx : imForm U x ≠ 0) (w : Ell2)
    (t : ℂ) : imSchur U x (w + t • x) = imSchur U x w := by
  set a := imForm U x with ha
  set b := imPair U x w with hb
  have hxx : imPair U x x = a := imPair_self U x
  have hF : ((imForm U (w + t • x) : ℝ) : ℂ) =
      (imForm U w : ℂ) + conj t * b + t * conj b + t * conj t * a := by
    rw [← imPair_self, ← imPair_self, imPair_add_left, imPair_add_right, imPair_add_right,
      imPair_smul_left, imPair_smul_right, imPair_smul_left, imPair_smul_right, hxx,
      imPair_conj U x w]
    ring
  have hB : imPair U x (w + t • x) = b + t * a := by
    rw [imPair_add_right, imPair_smul_right, hxx]
  unfold imSchur
  rw [← ha, hB]
  have hFr : imForm U (w + t • x) =
      imForm U w + 2 * (conj t * b).re + Complex.normSq t * a := by
    have := congrArg Complex.re hF
    simp only [Complex.ofReal_re, Complex.add_re] at this
    rw [this]
    have e1 : (t * conj b).re = (conj t * b).re := by
      simp
    have e2 : (t * conj t * (a : ℂ)).re = Complex.normSq t * a := by
      rw [Complex.mul_conj]; simp
    linarith
  have hN : ‖b + t * a‖ ^ 2 = ‖b‖ ^ 2 + 2 * a * (conj t * b).re + Complex.normSq t * a ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add]
    simp only [Complex.normSq_ofReal, map_mul, Complex.conj_ofReal]
    have : (b * (conj t * (a : ℂ))).re = a * (conj t * b).re := by
      simp [Complex.mul_re]; ring
    linarith
  rw [hFr, hN]
  field_simp
  ring

/-- Continuity of `F` and of `B(x, ·)`. -/
lemma continuous_imForm  : Continuous (imForm U) := by
  unfold imForm
  fun_prop

lemma continuous_imPair  (x : Ell2) : Continuous (imPair U x) := by
  unfold imPair
  fun_prop

/-- **Index count.** If the Schur complement is nonnegative on a dense set, then `F ≥ 0` on the closed hyperplane `{B(x, ·) = 0}`. -/
theorem nonneg_of_imSchur_nonneg  {x : Ell2}
    {S : Set Ell2} (hS : Dense S) (hC : ∀ w ∈ S, 0 ≤ imSchur U x w) (w : Ell2)
    (hw : imPair U x w = 0) : 0 ≤ imForm U w := by
  have hcont : Continuous (imSchur U x) := by
    unfold imSchur
    exact (continuous_imForm U).sub (((continuous_imPair U x).norm.pow 2).div_const _)
  have hall : ∀ v, 0 ≤ imSchur U x v := by
    intro v
    have hclosed : IsClosed {v | 0 ≤ imSchur U x v} := isClosed_le continuous_const hcont
    exact hclosed.closure_subset_iff.mpr (fun v hv => hC v hv) (hS v)
  have := hall w
  unfold imSchur at this
  rwa [hw, norm_zero, zero_pow two_ne_zero, zero_div, sub_zero] at this

end

/-- Finitely supported vectors are dense in `ℓ²`. -/
lemma dense_finSupp : Dense {v : Ell2 | ∃ N : ℕ, ∀ n, N ≤ n → (v : ℕ → ℂ) n = 0} := by
  intro v
  have hs := lp.hasSum_single (p := 2) (by norm_num) v
  refine mem_closure_of_tendsto hs.tendsto_sum_nat ?_
  refine Eventually.of_forall fun N => ⟨N, fun n hn => ?_⟩
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
  simp_all

/-- `F(e₀) = 2 a_E`. -/
lemma imForm_monodromy_basisVec (W : ℝ → Ell2 →L[ℂ] Ell2) :
    imForm (monodromy W) (basisVec 0) = 2 * smallA W := by
  unfold imForm smallA monodromy
  rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_basisVec,
    Complex.conj_im]
  ring

/-- **Lemma 8.2 (sign of `a_E`).** For small `E > 0`, `F(e₀) = 2 a_E < 0`. -/
theorem small_energy_imForm_basisVec_neg {Ω : Set ℂ} (hb : Bornology.IsBounded Ω)
    (hL : IsLipschitzDomain Ω) {γ : ℝ → ℂ} (hγ : IsBoundaryParam Ω γ) :
    ∃ δ > 0, ∀ E, 0 < E → E < δ → ∀ W : ℝ → Ell2 →L[ℂ] Ell2, IsTransport γ E W →
      imForm (monodromy W) (basisVec 0) < 0 := by
  obtain ⟨δ, hδ, -, h⟩ := smallA_le_neg hb hL hγ
  refine ⟨δ, hδ, fun E hE hEδ W hW => ?_⟩
  rw [imForm_monodromy_basisVec]
  have hv := ENNReal.toReal_pos
    (hL.1.1.measure_pos volume hL.1.2.nonempty).ne' hb.measure_lt_top.ne
  linarith [h E hE hEδ W hW, mul_pos hv hE]

end PolyaNeumann

end
