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

section

variable (W : ℝ → Ell2 →L[ℂ] Ell2) (n g : ℝ → ℂ) (θ : ℝ)
include W n g θ

/-- The form `(𝒜_E g)(θ) = 2 n(θ) + i((T_E g)(θ) - (T_E^* g)(θ))`, where `n = 𝒩(E) g` is the
Neumann-to-Dirichlet trace of `g` (supplied as data). -/
def periodicA  : ℂ :=
  2 * n θ + Complex.I * (volterraOp W g θ - volterraOpAdj W g θ)

/-- The corrected periodic form `𝒫_E g = 𝒜_E g + O_E B_E O_E^* g` of Definition 6.2, with
`B_E` built from `c_E = (V_E^* - I)e₀` and `d_E = i s_E`. -/
def periodicP  : ℂ :=
  periodicA W n g θ +
    observation W (cutB (cutC (W (2 * π)) (basisVec 0))
      (Complex.I • cutS (W (2 * π)) (basisVec 0)) (observationAdj W g)) θ

end



/-! ### The small-energy Schur complement (Definition 8.1, Lemma 8.3) -/

/-- The `L²(0, L)` pairing `⟨f, g⟩ = ∫₀^L conj(f) g`. -/
def l2Inner (f g : ℝ → ℂ) : ℂ := ∫ s in (0 : ℝ)..(2 * π), conj (f s) * g s

/-- `⟨x, O_E^* g⟩ = ⟨O_E x, g⟩_{L²}`. -/
lemma inner_observationAdj_right {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : ContinuousOn W (Icc 0 (2 * π)))
    {g : ℝ → ℂ} (hg : IntervalIntegrable g volume 0 (2 * π)) (x : Ell2) :
    ⟪x, observationAdj W g⟫_ℂ = l2Inner (observation W x) g := by
  rw [← inner_conj_symm, inner_observationAdj hW hg, ← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp  
  ring

end PolyaNeumann
