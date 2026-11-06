module

public import RequestProject.Driven

/-!
# The correction at the boundary origin (Definition 6.2, Lemma 6.3 and the jump in Lemma 6.4)

Let `V` be a unitary operator on a complex Hilbert space `H` (in the paper, the transport endpoint
`V_E` on `ℓ²(ℕ₀)`) and `e₀ ∈ H`. Put

* `c = (V^* - I) e₀`, `s = (I + V^*) e₀`, `d = i s`,
* `Π^c = I - c ⟨c, ·⟩ / ‖c‖²`,
* `B = (d ⟨c, ·⟩ + c ⟨d, ·⟩) / ‖c‖² - ⟨c, d⟩ / ‖c‖⁴ · c ⟨c, ·⟩`.

Lemma 6.3 of the paper (Algebra of the correction) states that `Π^c` is the orthogonal
projection onto `c^⊥`, that `B` is self-adjoint of rank at most two with `B c = i s`, and that
`⟨c, d⟩ = -2 Im ⟨e₀, V e₀⟩` is real. These are proved here, together with the continuity of
`B` and `Π^c` in the data, and the endpoint jump of the correction used in Lemma 6.4:
`⟨c, B x⟩ = -i ⟨s, x⟩`.

The rank-one operator `x ↦ ⟨u, x⟩ v` is Mathlib's `rankOne ℂ v u`.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `c = (V^* - I) e₀`. -/
def cutC (V : H →L[ℂ] H) (e₀ : H) : H := adjoint V e₀ - e₀

/-- `s = (I + V^*) e₀`. -/
def cutS (V : H →L[ℂ] H) (e₀ : H) : H := e₀ + adjoint V e₀

/-- `Π^c = I - c ⟨c, ·⟩ / ‖c‖²`. -/
def cutProj (c : H) : H →L[ℂ] H := 1 - ((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ • rankOne ℂ c c

/-- `B = (d ⟨c, ·⟩ + c ⟨d, ·⟩) / ‖c‖² - ⟨c, d⟩ / ‖c‖⁴ · c ⟨c, ·⟩` (equation (6.1)). -/
def cutB (c d : H) : H →L[ℂ] H :=
  ((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ • (rankOne ℂ d c + rankOne ℂ c d) -
    (⟪c, d⟫_ℂ / ((‖c‖ ^ 4 : ℝ) : ℂ)) • rankOne ℂ c c

variable {c d : H} {V : H →L[ℂ] H}

omit [CompleteSpace H] in
lemma cutB_apply (c d x : H) :
    cutB c d x = ((‖c‖ ^ 2 : ℝ) : ℂ)⁻¹ • (⟪c, x⟫_ℂ • d + ⟪d, x⟫_ℂ • c) -
      (⟪c, d⟫_ℂ / (‖c‖ ^ 4 : ℝ) * ⟪c, x⟫_ℂ) • c := by
  simp [cutB, smul_smul]

omit [CompleteSpace H] in
/-- **Lemma 6.3.** `Π^c` is the orthogonal projection onto `c^⊥`. -/
theorem cutProj_eq_starProjection (c : H) : cutProj c = (ℂ ∙ c)ᗮ.starProjection := by
  ext x
  simp [cutProj, Submodule.starProjection_singleton, smul_smul, div_eq_inv_mul]

/-- **Lemma 6.3.** `B` is self-adjoint as soon as `⟨c, d⟩` is real. -/
theorem cutB_isSelfAdjoint (hcd : ⟪d, c⟫_ℂ = ⟪c, d⟫_ℂ) : IsSelfAdjoint (cutB c d) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe, cutB_apply, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, map_inv₀, map_mul,
    map_div₀, Complex.conj_ofReal, inner_conj_symm]
  grind

omit [CompleteSpace H] in
/-- **Lemma 6.3.** `B c = d` when `c ≠ 0` and `⟨c, d⟩` is real. -/
theorem cutB_apply_self (hc : c ≠ 0) (hcd : ⟪d, c⟫_ℂ = ⟪c, d⟫_ℂ) :
    cutB c d c = d := by
  rw [cutB_apply, smul_add, smul_smul, smul_smul]
  have h2 : (‖c‖ ^ 2)⁻¹ * ⟪c, d⟫_ℂ =
      ⟪c, d⟫_ℂ / ‖c‖ ^ 4 * ‖c‖ ^ 2 := by
    push_cast; field_simp
  simp_all

/-- **Lemma 6.3.** For unitary `V`, `⟨c, d⟩ = -2 Im ⟨e₀, V e₀⟩` with `d = i s`. -/
theorem inner_cutC_cutD {V : H →L[ℂ] H} (hV : V ∈ unitary (H →L[ℂ] H)) (e₀ : H) :
    ⟪cutC V e₀, Complex.I • cutS V e₀⟫_ℂ = (-2 * (⟪e₀, V e₀⟫_ℂ).im : ℝ) := by
  have hVV  := Unitary.mul_star_self_of_mem hV
  rw [ContinuousLinearMap.star_eq_adjoint] at hVV
  have h2 : ⟪e₀, adjoint V e₀⟫_ℂ = conj ⟪e₀, V e₀⟫_ℂ := by
    rw [adjoint_inner_right, inner_conj_symm]
  have h3 : ⟪adjoint V e₀, adjoint V e₀⟫_ℂ = ⟪e₀, e₀⟫_ℂ := by
    rw [adjoint_inner_left, ← ContinuousLinearMap.mul_apply, hVV, ContinuousLinearMap.one_apply]
  simp only [cutC, cutS, inner_sub_left, inner_smul_right, inner_add_right, adjoint_inner_left V e₀ e₀, h2, h3]
  generalize ⟪e₀, V e₀⟫_ℂ = w
  apply Complex.ext
  · simp; ring
  norm_num

/-- In particular `⟨d, c⟩ = ⟨c, d⟩`. -/
theorem inner_cutD_cutC (hV : V ∈ unitary (H →L[ℂ] H)) (e₀ : H) :
    ⟪Complex.I • cutS V e₀, cutC V e₀⟫_ℂ = ⟪cutC V e₀, Complex.I • cutS V e₀⟫_ℂ := by
  rw [← inner_conj_symm, inner_cutC_cutD hV, Complex.conj_ofReal]

/-- **Lemma 6.3** for the transport data: `B_E` is self-adjoint and `B_E c_E = i s_E`. -/
theorem cutB_transport (hV : V ∈ unitary (H →L[ℂ] H)) (e₀ : H)
    (hc : cutC V e₀ ≠ 0) :
    IsSelfAdjoint (cutB (cutC V e₀) (Complex.I • cutS V e₀)) ∧
      cutB (cutC V e₀) (Complex.I • cutS V e₀) (cutC V e₀) = Complex.I • cutS V e₀ :=
  ⟨cutB_isSelfAdjoint (inner_cutD_cutC hV e₀), cutB_apply_self hc (inner_cutD_cutC hV e₀)⟩

/-- **Lemma 6.4 (jump of the correction).** `⟨c_E, B_E x⟩ = -i ⟨s_E, x⟩`. -/
theorem inner_cutC_cutB {V : H →L[ℂ] H} (hV : V ∈ unitary (H →L[ℂ] H)) (e₀ : H)
    (hc : cutC V e₀ ≠ 0) (x : H) :
    ⟪cutC V e₀, cutB (cutC V e₀) (Complex.I • cutS V e₀) x⟫_ℂ =
      -Complex.I * ⟪cutS V e₀, x⟫_ℂ := by
  obtain ⟨hsa, hBc⟩ := cutB_transport hV e₀ hc
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric] at hsa
  have := hsa (cutC V e₀) x
  simp_all [inner_smul_left]

/-! ### Specialization to the boundary transport -/

/-- **Lemma 6.4 (observation jump).** For a transport `W` (so `W(0) = I`, `W(L) = V_E`),
`(O_E v)(L) - (O_E v)(0) = ⟨c_E, v⟩` with `c_E = (V_E^* - I) e₀`. -/
theorem observation_jump {γ : ℝ → ℂ} {E : ℝ} {W : ℝ → Ell2 →L[ℂ] Ell2}
    (hW : IsTransport γ E W) (v : Ell2) :
    observation W v (2 * Real.pi) - observation W v 0 =
      ⟪cutC (W (2 * Real.pi)) (basisVec 0), v⟫_ℂ := by
  have h0 : W 0 = 1 := by
    have := hW.2 0 ⟨le_rfl, by positivity⟩
    simp_all
  simp [observation, cutC, inner_sub_left, adjoint_inner_left, h0]

end PolyaNeumann
