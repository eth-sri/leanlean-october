module

public import RequestProject.CutPhase

/-!
# Small energies: the principal phase sum (abstract part of Lemmas 8.7–8.8)

* The trace-norm bound of Lemma 4.7 is linear in the energy:
  `‖U_E - I‖_{𝒮₁} ≤ C E` for a closed Lipschitz curve (`exists_linear_traceBound_monodromyAt`).
* For a unitary `U` with `U - I` compact and trace-norm bound `C`, the principal phases
  (the cut phase sum with the cut through `-1`) satisfy `∑ mult(z) |arg z| ≤ (π/2) C`
  (`cutPhaseSum_pi_bound`), and if `C < 2` then `-1` is not an eigenvalue
  (`not_eigen_neg_one_of_traceBound`).
-/

@[expose] public section

noncomputable section

open scoped Real
open MeasureTheory Filter Topology Set

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The principal argument is bounded by `(π/2) |z - 1|` on the unit circle. -/
lemma abs_arg_le_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    |Complex.arg z| ≤ π / 2 * ‖z - 1‖ := by
  set t := Complex.arg z with ht
  have hexp : z = Complex.exp (Complex.I * t) := by
    have := Complex.norm_mul_exp_arg_mul_I z
    simp_all [mul_comm]
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two]
  have hu0 : 0 ≤ |t| / 2 := by positivity
  have hu1 : |t| / 2 ≤ π / 2 := by
    have := abs_le.mpr ⟨by linarith, hhi⟩
    linarith
  have hs := Real.mul_le_sin hu0 hu1
  have hsin : |Real.sin (t / 2)| = Real.sin (|t| / 2) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h, abs_of_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, abs_of_nonpos]
      have := Real.sin_nonneg_of_nonneg_of_le_pi (x := -(t / 2)) (by linarith) (by linarith)
      rw [Real.sin_neg] at this; linarith
  rw [hsin]
  have hpi := Real.pi_pos
  have h2 : 2 / π * (|t| / 2) * π = |t| := by field_simp
  nlinarith

/-- With the cut through `-1`, the cut argument is the principal argument up to sign. -/
lemma abs_argCut_pi (z : ℂ) : |argCut π z| = |Complex.arg z| := by
  have hlo := Complex.neg_pi_lt_arg z
  have hhi := Complex.arg_le_pi z
  have hpi := Real.pi_pos
  unfold argCut argNeg
  grind

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) (hC : IsCompactOperator ⇑(U - 1)) {C : ℝ} (hT : TraceBound (U - 1) C)
include U hU hC C hT

/-- **Lemma 8.7 (summability of the principal phases, abstract form).** For a unitary `U` with
`U - I` compact and trace-norm bound `C`, the principal phases (cut through `-1`) are absolutely
summable, with `|∑ mult(z) arg z| ≤ (π/2) C`. -/
lemma cutPhaseSum_pi_bound  :
    Summable (cutPhaseTerm π U) ∧ |cutPhaseSum π U| ≤ π / 2 * C := by
  set g : {z : ℂ // z ≠ 1} → ℝ := fun z => (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖ with hg
  have hgnn : ∀ z, 0 ≤ g z := fun z => by positivity
  have hgs : Summable g := summable_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hT)
  have hgt : ∑' z, g z ≤ C := Real.tsum_le_of_sum_le hgnn (sum_eigenMult_mul_norm_le hU hT)
  have hb : ∀ z, ‖cutPhaseTerm π U z‖ ≤ π / 2 * g z := by
    intro z
    rw [cutPhaseTerm, norm_mul, Real.norm_natCast, Real.norm_eq_abs]
    by_cases hm : eigenMult U z = 0
    simp_all
    have hm' : 0 < Module.finrank ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Nat.pos_of_ne_zero hm
    haveI := Module.finite_of_finrank_pos hm'
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hm'
    have hv0' : v ≠ 0 := fun h => hv0 (by simp [h])
    have hz1 : ‖(z : ℂ)‖ = 1 :=
      norm_eq_one_of_eigen hU hv0' (Module.End.mem_eigenspace_iff.mp hv)
    rw [abs_argCut_pi]
    calc (eigenMult U z : ℝ) * |Complex.arg z|
        ≤ (eigenMult U z : ℝ) * (π / 2 * ‖(z : ℂ) - 1‖) :=
          mul_le_mul_of_nonneg_left (abs_arg_le_of_norm_eq_one hz1) (Nat.cast_nonneg _)
      _ = π / 2 * g z := by ring
  have hs : Summable (cutPhaseTerm π U) := Summable.of_norm_bounded (hgs.mul_left (π / 2)) hb
  refine ⟨hs, ?_⟩
  calc |cutPhaseSum π U| = ‖∑' z, cutPhaseTerm π U z‖ := by rfl
    _ ≤ ∑' z, ‖cutPhaseTerm π U z‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' z, π / 2 * g z := Summable.tsum_le_tsum hb hs.norm (hgs.mul_left _)
    _ = π / 2 * ∑' z, g z := tsum_mul_left
    _ ≤ π / 2 * C := mul_le_mul_of_nonneg_left hgt (by positivity)

/-- If `U` is unitary, `U - I` is compact and has trace-norm bound `C < 2`, then `-1` is not an
eigenvalue of `U`. -/
lemma not_eigen_neg_one_of_traceBound  (hC2 : C < 2)
    {v : H} (hv : v ≠ 0) : U v ≠ (-1 : ℂ) • v := by
  intro hUv
  have hne : (-1 : ℂ) ≠ 1 := by norm_num
  haveI := finiteDimensional_eigenspace hC hne
  have hpos : 0 < eigenMult U (-1) := Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hUv⟩, fun h => hv (by simp_all)⟩
  have h := sum_eigenMult_mul_norm_le hU hT {⟨-1, hne⟩}
  rw [Finset.sum_singleton] at h
  have h2 : ‖(-1 : ℂ) - 1‖ = 2 := by norm_num
  simp  at h
  rw [h2] at h
  have : (1 : ℝ) ≤ eigenMult U (-1) := by exact_mod_cast hpos
  linarith

end

end General

end PolyaNeumann

end
