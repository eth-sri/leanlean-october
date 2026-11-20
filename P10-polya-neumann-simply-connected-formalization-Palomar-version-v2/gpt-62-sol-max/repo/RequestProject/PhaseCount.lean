module

public import RequestProject.NormAttained
public import RequestProject.Phase
public import RequestProject.Transport
public import Mathlib.LinearAlgebra.Eigenspace.Basic

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

open scoped Real ComplexConjugate
open MeasureTheory

namespace PolyaNeumann

section General

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section

variable (U : H →L[ℂ] H)
include U

/-- The (geometric) multiplicity of `z` as an eigenvalue of `U`: the dimension of the
eigenspace `ker(U - z)` (zero if `z` is not an eigenvalue). -/
def eigenMult  (z : ℂ) : ℕ :=
  Module.finrank ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)

/-- The term `mult(z) · Arg₋ z` of the negative-branch phase sum, indexed by `z ≠ 1`. -/
def phaseTerm  (z : {z : ℂ // z ≠ 1}) : ℝ :=
  (eigenMult U z : ℝ) * argNeg z

/-- The negative-branch phase sum `Φ₋ = ∑_{z ∈ σ_p(U) \ {1}} Arg₋ z`, eigenvalues counted with
multiplicity. -/
def phaseSum  : ℝ := ∑' z, phaseTerm U z

end

lemma argNeg_nonpos (z : ℂ) : argNeg z ≤ 0 := by
  unfold argNeg
  split_ifs with h
  gcongr
  · linarith [Complex.arg_le_pi z, Real.pi_pos]

omit [CompleteSpace H] in
/-- The eigenspaces of `U` at `z ≠ 1` are finite-dimensional when `U - I` is compact. -/
lemma finiteDimensional_eigenspace {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1)) {z : ℂ}
    (hz : z ≠ 1) : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) := by
  set C : H →L[ℂ] H := (-(z - 1)⁻¹) • (U - 1) with hCdef
  have hCc : IsCompactOperator C := hC.smul _
  have hfin := finiteDimensional_ker_one_add hCc
  have hz' : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have heq : Module.End.eigenspace (U : H →ₗ[ℂ] H) z =
      LinearMap.ker ((1 + C : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
    ext v
    rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
    simp only [ContinuousLinearMap.coe_coe, hCdef, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]
    constructor
    · intro h
      have h' : z • v - v = (z - 1) • v := by rw [sub_smul, one_smul]
      simp_all
    · intro h
      have h2 : (z - 1) • v = U v - v := by
        have h3 := congrArg (fun w => (z - 1) • w) h
        simp only [smul_add, smul_smul, mul_neg, mul_inv_cancel₀ hz', neg_one_smul,
          smul_zero] at h3
        exact (add_neg_eq_zero.mp h3)
      rw [sub_smul, one_smul] at h2
      simp_all
  rw [heq]
  assumption

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
include U hU

/-- An eigenvalue of a unitary operator has modulus one. -/
lemma norm_eq_one_of_eigen  {z : ℂ} {v : H}
    (hv : v ≠ 0) (h : U v = z • v) : ‖z‖ = 1 := by
  have hn : ‖U v‖ = ‖v‖ := by
    have := Unitary.norm_map ⟨U, hU⟩ v
    assumption
  simp_all [norm_smul]

/-- Eigenvectors of a unitary operator for distinct eigenvalues are orthogonal. -/
lemma inner_eq_zero_of_eigen_unitary 
    {z z' : ℂ} {v w : H} (hv : U v = z • v) (hw : U w = z' • w) (hzz : z ≠ z')
    (hz : ‖z‖ = 1) : inner ℂ v w = 0 := by
  have hpres : inner ℂ (U v) (U w) = inner ℂ v w := by
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.mul_def,
      (Unitary.mem_iff.mp hU).1, ContinuousLinearMap.one_apply]
  rw [hv, hw, inner_smul_left, inner_smul_right, ← mul_assoc] at hpres
  have h1 : conj z * z' ≠ 1 := by
    intro h
    apply hzz
    have : z * (conj z * z') = z := by simp_all
    rw [← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz] at this
    simp_all
  grind

end

section

variable (U : H →L[ℂ] H)
include U

/-- The index set listing the eigenvalues `z ≠ 1` of `U` with multiplicity. -/
abbrev EigIdx  : Type := Σ z : {z : ℂ // z ≠ 1}, Fin (eigenMult U z)

/-- An orthonormal basis of each eigenspace, glued together: the eigenvector `e_p`. -/
def eigVec  (p : EigIdx U) : H :=
  haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ)) :=
    Module.finite_of_finrank_pos (Fin.pos p.2)
  ((stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ))) p.2 : H)

end

omit [CompleteSpace H] in
lemma eigVec_mem (U : H →L[ℂ] H) (p : EigIdx U) :
    eigVec U p ∈ Module.End.eigenspace (U : H →ₗ[ℂ] H) (p.1 : ℂ) := by
  unfold eigVec
  simp

omit [CompleteSpace H] in
lemma eigVec_eigen (U : H →L[ℂ] H) (p : EigIdx U) :
    U (eigVec U p) = (p.1 : ℂ) • eigVec U p :=
  Module.End.mem_eigenspace_iff.mp (eigVec_mem U p)

section

variable {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
include U hU

lemma orthonormal_eigVec  :
    Orthonormal ℂ (eigVec U) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨z, hz⟩, k⟩ ⟨⟨z', hz'⟩, k'⟩
  by_cases hzz : z = z'
  · subst hzz
    haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
      Module.finite_of_finrank_pos (Fin.pos k)
    have := (orthonormal_iff_ite.mp
      (stdOrthonormalBasis ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal) k k'
    aesop
  · have hv : eigVec U ⟨⟨z, hz⟩, k⟩ ≠ 0 := by
      haveI : FiniteDimensional ℂ (Module.End.eigenspace (U : H →ₗ[ℂ] H) z) :=
        Module.finite_of_finrank_pos (Fin.pos k)
      have := (stdOrthonormalBasis ℂ
        (Module.End.eigenspace (U : H →ₗ[ℂ] H) z)).orthonormal.ne_zero k
      simpa [eigVec] using this
    have hz1 := norm_eq_one_of_eigen hU hv (eigVec_eigen U _)
    rw [inner_eq_zero_of_eigen_unitary hU (eigVec_eigen U _) (eigVec_eigen U ⟨⟨z', hz'⟩, k'⟩)
      (fun h => hzz h) hz1, if_neg]
    simp_all

lemma norm_eigVal  (p : EigIdx U) :
    ‖(p.1 : ℂ)‖ = 1 :=
  norm_eq_one_of_eigen hU ((orthonormal_eigVec hU).ne_zero p) (eigVec_eigen U p)

end

/-- Restrict the full orthonormal eigenvector listing to a finite set of eigenvalues. -/
lemma exists_orthonormal_eigen_family {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (s : Finset {z : ℂ // z ≠ 1}) :
    ∃ e : (Σ z : s, Fin (eigenMult U z)) → H, Orthonormal ℂ e ∧
      ∀ p, U (e p) = ((p.1 : {z : ℂ // z ≠ 1}) : ℂ) • e p := by
  let i := (Equiv.subtypeSigmaEquiv (fun z : {z : ℂ // z ≠ 1} => Fin (eigenMult U z)) (· ∈ s)).symm
  exact ⟨fun p => eigVec U (i p).1,
    (orthonormal_eigVec hU).comp _ (Subtype.val_injective.comp i.injective), fun p => eigVec_eigen U _⟩

omit [CompleteSpace H] in
lemma eigenMult_pos_of_eigen {U : H →L[ℂ] H} (hC : IsCompactOperator ⇑(U - 1))
    {z : ℂ} (hz : z ≠ 1) {v : H} (hv : v ≠ 0) (he : U v = z • v) :
    0 < eigenMult U z := by
  letI := finiteDimensional_eigenspace hC hz
  exact Module.finrank_pos_iff_exists_ne_zero.mpr
    ⟨⟨v, Module.End.mem_eigenspace_iff.mpr he⟩, fun h => hv (congrArg Subtype.val h)⟩

lemma eigVal_mem_spectrum {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (p : EigIdx U) : (p.1 : ℂ) ∈ spectrum ℂ U := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (Module.End.hasEigenvalue_of_hasEigenvector ⟨eigVec_mem U p,
    (orthonormal_eigVec hU).ne_zero p⟩).mem_spectrum

omit [CompleteSpace H] in
/-- The distance sum on the eigenvector listing has the multiplicities as fiber sizes. -/
lemma summable_norm_eigIdx {U : H →L[ℂ] H}
    (h : Summable (fun z : {z : ℂ // z ≠ 1} => (eigenMult U z : ℝ) * ‖(z : ℂ) - 1‖)) :
    Summable (fun p : EigIdx U => ‖(p.1 : ℂ) - 1‖) := by
  rw [summable_sigma_of_nonneg fun _ => norm_nonneg _]
  refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
  simpa [tsum_fintype, Finset.sum_const, nsmul_eq_mul] using h

/-- A largest spectral displacement supplies a term in the nonpositive phase sum. -/
lemma norm_sub_one_le_neg_phaseSum {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hC : IsCompactOperator ⇑(U - 1)) (hs : Summable (phaseTerm U)) :
    ‖U - 1‖ ≤ -phaseSum U := by
  have hn (z : {z : ℂ // z ≠ 1}) : 0 ≤ -phaseTerm U z :=
    neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (argNeg_nonpos _))
  rw [phaseSum, ← tsum_neg]
  by_cases h : U = 1
  · simpa [h] using tsum_nonneg hn
  obtain ⟨z, v, hv, he, hz, e⟩ := exists_eigenvalue_norm_sub_one hU hC h
  have hm : (1 : ℝ) ≤ eigenMult U z := by exact_mod_cast eigenMult_pos_of_eigen hC hz hv he
  rw [← e]
  refine (norm_sub_one_le_neg_argNeg (norm_eq_one_of_eigen hU hv he)).trans
    ((?_ : -argNeg z ≤ -phaseTerm U ⟨z, hz⟩).trans (hs.neg.le_tsum ⟨z, hz⟩ fun i _ => hn i))
  rw [phaseTerm, ← mul_neg]
  exact le_mul_of_one_le_left (neg_nonneg.mpr (argNeg_nonpos _)) hm

end General

open Classical in
/-- The monodromy `U_E` of the boundary transport of `γ` at energy `E` (the identity if no
transport exists; for Lipschitz `γ` the transport exists and `U_E` does not depend on the
choice of transport). -/
def monodromyAt (γ : ℝ → ℂ) (E : ℝ) : Ell2 →L[ℂ] Ell2 :=
  if h : ∃ W, IsTransport γ E W then monodromy h.choose else 1

/-- For Lipschitz `γ`, `monodromyAt γ E` is the monodromy of any transport at energy `E`. -/
lemma monodromyAt_eq {γ : ℝ → ℂ} {K : NNReal} (hK : LipschitzWith K γ) {E : ℝ}
    {W : ℝ → Ell2 →L[ℂ] Ell2} (hW : IsTransport γ E W) : monodromyAt γ E = monodromy W := by
  have h : ∃ W, IsTransport γ E W := ⟨W, hW⟩
  rw [monodromyAt, dif_pos h, monodromy, monodromy,
    transport_unique_of_lipschitz γ hK E h.choose_spec hW ⟨by positivity, le_rfl⟩]

/-- Definition 5.19 (negative arguments and the phase integer): the phase integer
`M(E) = (E|Ω|/2 - Φ₋(E)) / (2π)` of the domain `Ω` with boundary parametrization `γ`. -/
def phaseCount (Ω : Set ℂ) (γ : ℝ → ℂ) (E : ℝ) : ℝ :=
  ((volume Ω).toReal * E / 2 - phaseSum (monodromyAt γ E)) / (2 * π)

end PolyaNeumann
