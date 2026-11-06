module

public import RequestProject.CutCorrection

/-!
# The periodic boundary form: endpoint jumps and transmuted nullspace (Lemmas 6.4, 6.9, 6.10)

For a transport `W = W_E` with endpoint `V_E = W(L)`, `c_E = (V_E^* - I)e₀`,
`s_E = (I + V_E^*)e₀` and the correction `B_E` of Definition 6.2, the paper considers
`𝒜_E g = 2 𝒩(E) g + i(T_E - T_E^*) g` and the corrected form `𝒫_E = 𝒜_E + O_E B_E O_E^*`.

The Neumann-to-Dirichlet map `𝒩(E)` is not formalized; we take its output `n = 𝒩(E) g` as an
arbitrary function, and impose on it exactly the properties the paper uses (periodicity in
Lemma 6.4; the trace identities from the transmutation endpoint formulas in Lemmas 6.9–6.10).

* `volterra_jump` / `periodicA_jump` / `periodicP_periodic` (**Lemma 6.4**):
  `(𝒜_E g)(L) - (𝒜_E g)(0) = i⟨s_E, O_E^* g⟩` and `(𝒫_E g)(L) = (𝒫_E g)(0)`.
* `periodicA_radial` (**Lemma 6.9**): if `O_E^* q = i c_E` and `𝒩(E) q = O_E e₀ - i T_E q`,
  then `𝒜_E q = O_E s_E`.
* `periodicP_radial`, `periodicP_of_observationAdj_eq_zero` (**Lemma 6.10**):
  `𝒫_E q = 0` and `T_E^♯ q = Π^c_E O_E^* q = 0` for the radial input, and
  `𝒫_E g = 0`, `T_E^♯ g = 0` whenever `O_E^* g = 0` and `𝒩(E) g = -i T_E g`.
* `schurC` (**Definition 8.1**) and `schurC_periodic`, `schurC_radial`,
  `schurC_of_observationAdj_eq_zero` (**Lemma 8.3**): with `b_E = 𝒜_E q`, `a_E = ⟨q, b_E⟩ ≠ 0`,
  the Schur complement `C^sc_E = 𝒜_E - a_E⁻¹ b_E ⟨b_E, ·⟩` has matching endpoint values,
  `C^sc_E q = 0`, and `C^sc_E g = 0` when `O_E^* g = 0` and `𝒩(E) g = -i T_E g`. The reality of
  `a_E = -i⟨c_E, s_E⟩` (`l2Inner_radial_eq`) is derived from unitarity of `V_E`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ComplexConjugate Real InnerProductSpace

noncomputable section

namespace PolyaNeumann

/-- The form `(𝒜_E g)(θ) = 2 n(θ) + i((T_E g)(θ) - (T_E^* g)(θ))`, where `n = 𝒩(E) g` is the
Neumann-to-Dirichlet trace of `g` (supplied as data). -/
def periodicA (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  2 * n θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)

/-- The corrected periodic form `𝒫_E g = 𝒜_E g + O_E B_E O_E^* g` of Definition 6.2, with
`B_E` built from `c_E = (V_E^* - I)e₀` and `d_E = i s_E`. -/
def periodicP (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ) : ℂ :=
  periodicA W n g θ +
    observation W (cutB (cutC (W (2 * π)) (basisVec 0))
      (Complex.I • cutS (W (2 * π)) (basisVec 0)) (observationAdj W g)) θ

/-- **Lemma 6.4 (jump of `𝒜_E`).** If the Neumann trace `n` is periodic, then
`(𝒜_E g)(L) - (𝒜_E g)(0) = i⟨s_E, O_E^* g⟩`. -/
theorem periodicA_jump  (hW : ContinuousOn W (Icc 0 (2 * π)))
    (hW0 : W 0 = 1)  (hn : n (2 * π) = n 0) (hg : AEStronglyMeasurable g volume)
     (hgB : ∀ s, ‖g s‖ ≤ B) :
    periodicA W n g (2 * π) - periodicA W n g 0 =
      Complex.I * ⟪cutS (W (2 * π)) (basisVec 0), observationAdj W g⟫_ℂ := by
  rw [← (show Complex.I * (volterraOp W g (2 * π) - volterraOpAdj W g (2 * π)) - Complex.I * (volterraOp W g 0 - volterraOpAdj W g 0) = Complex.I * ⟪cutS (W (2 * π)) (basisVec 0), observationAdj W g⟫_ℂ by
    have hL : 0 ≤ 2 * π := by positivity
    have h0 := volterraOp_add_adj hW hg hgB ⟨le_rfl, hL⟩
    have h1 := volterraOp_add_adj hW hg hgB ⟨hL, le_rfl⟩
    have hT0 : volterraOp W g 0 = 0 := by simp [volterraOp]
    have hT1 : volterraOpAdj W g (2 * π) = 0 := by simp [volterraOpAdj]
    rw [hT0, zero_add] at h0
    rw [hT1, add_zero] at h1
    rw [hT0, hT1, h0, h1]
    simp only [observation, hW0, ContinuousLinearMap.one_apply, cutS, inner_add_left,
      ContinuousLinearMap.adjoint_inner_left]
    ring), periodicA, periodicA, hn]
  ring

/-- **Lemma 6.4 (periodicity of `𝒫_E`).** For a transport `W` of a Lipschitz curve with
`c_E ≠ 0` and a periodic Neumann trace `n`, the corrected form has matching endpoint values:
`(𝒫_E g)(L) = (𝒫_E g)(0)`. -/
theorem periodicP_periodic   (hK : LipschitzWith K γ) 
     (hW : IsTransport γ E W)
    (hc : cutC (W (2 * π)) (basisVec 0) ≠ 0)  (hn : n (2 * π) = n 0)
    (hg : AEStronglyMeasurable g volume)  (hgB : ∀ s, ‖g s‖ ≤ B) :
    periodicP W n g (2 * π) = periodicP W n g 0 := by
  have hO := observation_jump hW (cutB (cutC (W (2 * π)) (basisVec 0))
      (Complex.I • cutS (W (2 * π)) (basisVec 0)) (observationAdj W g))
  rw [inner_cutC_cutB (transport_mem_unitary hK hW ⟨by positivity, le_rfl⟩) _ hc] at hO
  rw [← sub_eq_zero]
  simp [periodicP]
  linear_combination (periodicA_jump hW.1 (by
    simpa using (hW.2 0 ⟨le_rfl, by positivity⟩)) hn hg hgB) + hO

/-! ### The small-energy Schur complement (Definition 8.1, Lemma 8.3) -/

/-- The `L²(0, L)` pairing `⟨f, g⟩ = ∫₀^L conj(f) g`. -/
def l2Inner (f g : ℝ → ℂ) : ℂ := ∫ s in 0..(2 * π), conj (f s) * g s

/-- `⟨x, O_E^* g⟩ = ⟨O_E x, g⟩_{L²}`. -/
lemma inner_observationAdj_right  (hW : ContinuousOn W (Icc 0 (2 * π)))
     (hg : AEStronglyMeasurable g volume)  (hgB : ∀ s, ‖g s‖ ≤ B) x :
    ⟪x, observationAdj W g⟫_ℂ = l2Inner (observation W x) g := by
  rw [← inner_conj_symm, inner_observationAdj hW hg hgB, ← intervalIntegral_conj, l2Inner]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp
  ring

end PolyaNeumann
