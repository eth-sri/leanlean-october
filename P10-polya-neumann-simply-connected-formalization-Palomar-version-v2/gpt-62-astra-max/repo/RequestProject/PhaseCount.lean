module

public import RequestProject.NormAttained
public import RequestProject.Phase
public import RequestProject.Transport
public import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import RequestProject.PlanarNotation

/-!
# The phase integer `M(E)` (Definition 5.19)

For a unitary operator `U` with `U - I` compact, the eigenvalues `z ≠ 1` of `U` have finite
multiplicity. The negative-branch phase sum is
`Φ₋ = ∑_{z ∈ σ_p(U) \ {1}} Arg₋ z`, with each eigenvalue counted with its multiplicity, and the
phase integer of a domain `Ω` with boundary parametrization `γ` at energy `E` is
`M(E) = (E|Ω|/2 - Φ₋(E)) / (2π)`, computed for the monodromy `U_E`.

We also show that a summable multiplicity-weighted phase sum can be written as the sum over a
family listing the nonunit eigenvalues with multiplicity.
-/

@[expose] public section

noncomputable section

open scoped Real
open MeasureTheory

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable (U : H →L[ℂ] H)
include U

/-- The (geometric) multiplicity of `z` as an eigenvalue of `U`: the dimension of the
eigenspace `ker(U - z)` (zero if `z` is not an eigenvalue). -/
def eigenMult (z : ℂ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)

/-- The term `mult(z) · Arg₋ z` of the negative-branch phase sum, indexed by `z ≠ 1`. -/
def phaseTerm (z : {z : ℂ // z ≠ 1}) : ℝ :=
  (eigenMult U z : ℝ) * argNeg z

/-- The negative-branch phase sum `Φ₋ = ∑_{z ∈ σ_p(U) \ {1}} Arg₋ z`, eigenvalues counted with
multiplicity. -/
def phaseSum : ℝ := ∑' z, phaseTerm U z

end

lemma argNeg_nonpos (z : ℂ) : argNeg z ≤ 0 := by
  unfold argNeg
  split_ifs with h
  · exact h.le
  · linarith [Complex.arg_le_pi z, Real.pi_pos]

omit [CompleteSpace H] in
/-- The eigenspaces of `U` at `z ≠ 1` are finite-dimensional when `U - I` is compact. -/
lemma finiteDimensional_eigenspace {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {z : ℂ}
    (hz : z ≠ 1) : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) := by
  refine finiteDimensional_of_compact_scalar hC (U.isClosed_eigenspace z) (sub_ne_zero.mpr hz) fun v => ?_
  have hv : U (v : H) = z • (v : H) := Module.End.mem_eigenspace_iff.mp v.2
  rw [sub_apply, one_apply_eq_self, hv, sub_smul, one_smul]

/-- An eigenvalue of a unitary operator has modulus one. -/
lemma norm_eq_one_of_eigen {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H)) {z : ℂ} {v : H}
    (hv : v ≠ 0) (h : U v = z • v) : ‖z‖ = 1 := by
  have hn : ‖U v‖ = ‖v‖ := by
    grind [Unitary.norm_map ⟨U, hU⟩ v]
  rw [h, norm_smul] at hn
  
  field_simp at hn
  exact hn

/-- A summable multiplicity-weighted phase sum is the sum over a family listing the nonunit
eigenvalues of `U` with multiplicity. -/
theorem exists_eigen_family {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (hs : Summable (phaseTerm U)) :
    ∃ (ι : Type) (z : ι → ℂ), (∀ i, ‖z i‖ = 1) ∧ (∀ i, z i ≠ 1) ∧
      (∀ (c : ℂ) (v : H), v ≠ 0 → U v = c • v → c ≠ 1 → ∃ i, z i = c) ∧
      Summable (fun i => argNeg (z i)) ∧ ∑' i, argNeg (z i) = phaseSum U := by
  have hfib : ∀ z : {z : ℂ // z ≠ 1},
      ∑' k : Fin (eigenMult U z), -argNeg z = -phaseTerm U z := by
    simp [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, phaseTerm]
  have hsum : Summable (fun p : (Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)) =>
      argNeg p.1.1) := by
    have hneg : Summable (fun p : (Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)) =>
        -argNeg p.1.1) := by
      rw [summable_sigma_of_nonneg (fun p => neg_nonneg.mpr (argNeg_nonpos _))]
      refine ⟨fun z => (hasSum_fintype _).summable, ?_⟩
      simp only [hfib]
      exact hs.neg
    simpa using hneg.neg
  refine ⟨(Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)), fun p => p.1.1, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨z, k⟩
    
    haveI := finiteDimensional_eigenspace hC z.2
    obtain ⟨⟨v, hv⟩, hv0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Fin.pos k)
    exact norm_eq_one_of_eigen hU (fun h => hv0 (by simp [h]))
      (Module.End.mem_eigenspace_iff.mp hv)
  · rintro ⟨z, k⟩
    exact z.2
  · intro c v hv0 hv hc
    haveI := finiteDimensional_eigenspace hC hc
    
    exact ⟨⟨⟨c, hc⟩, ⟨0, (Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨v, Module.End.mem_eigenspace_iff.mpr hv⟩, fun h => hv0 (by simpa using h)⟩)⟩⟩, rfl⟩
  · exact hsum
  · rw [hsum.tsum_sigma, phaseSum]
    congr 1
    ext z
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, phaseTerm]

end General

open Classical in
/-- The monodromy `U_E` of the boundary transport of `γ` at energy `E` (the identity if no
transport exists; for Lipschitz `γ` the transport exists and `U_E` does not depend on the
choice of transport). -/
def monodromyAt (γ : ℝ → ℂ) (E : ℝ) : ShiftOp :=
  if h : ∃ W, IsTransport γ E W then monodromy h.choose else 1

/-- For Lipschitz `γ`, `monodromyAt γ E` is the monodromy of any transport at energy `E`. -/
lemma monodromyAt_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : TransportPath} (hW : IsTransport γ E W) : monodromyAt γ E = monodromy W := by
  have h : ∃ W, IsTransport γ E W := ⟨W, hW⟩
  rw [monodromyAt, dif_pos h, monodromy, monodromy,
    transport_unique_of_lipschitz γ hK E h.choose_spec hW ⟨by positivity, le_rfl⟩]

/-- Definition 5.19 (negative arguments and the phase integer): the phase integer
`M(E) = (E|Ω|/2 - Φ₋(E)) / (2π)` of the domain `Ω` with boundary parametrization `γ`. -/
def phaseCount (Ω : Set ℂ) (γ : ℝ → ℂ) (E : ℝ) : ℝ :=
  ((volume Ω).toReal * E / 2 - phaseSum (monodromyAt γ E)) / anglePeriod

end PolyaNeumann
