module

public import RequestProject.PlanarTypes

public import RequestProject.LocalConformalHardySubspace
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# The actual positive Fourier Hilbert basis

The orthogonal complement of the full nonpositive space has the standard
positive-frequency basis. Finite linear combinations in this basis, or
the full standard basis, have genuinely finite Fourier support.
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set
open scoped InnerProductSpace

theorem stdBasisZ_mem_nonpositive  (hn : n ≤ 0) :
    stdBasisZ n ∈ nonpositiveFourierSubspace := by
  intro k hk
  have hkn : k ≠ n := by omega
  simp [stdBasisZ_apply, hkn]

theorem nonpositive_orthogonal_coefficient_eq_zero
    (b : nonpositiveFourierSubspaceᗮ)  (hn : n ≤ 0) :
    (b : L2Z) n = 0 := by
  have h := (Submodule.mem_orthogonal _ _).mp b.property (stdBasisZ n)
    (stdBasisZ_mem_nonpositive hn)
  simpa [stdBasisZ_apply, lp.inner_single_left] using h

theorem stdBasisZ_mem_nonpositive_orthogonal  (hn : 0 < n) :
    stdBasisZ n ∈ nonpositiveFourierSubspaceᗮ := by
  have heq : posProj (stdBasisZ n) = stdBasisZ n := by
    apply lp.ext
    funext k
    by_cases hkn : k = n
    · subst k
      simp [posProj, hn]
    · simp [posProj, stdBasisZ_apply, hkn]
  rw [← heq]
  exact posProj_mem_nonpositive_orthogonal _

def positiveFourierVector (n : {n : ℤ // 0 < n}) :
    nonpositiveFourierSubspaceᗮ :=
  ⟨stdBasisZ n, stdBasisZ_mem_nonpositive_orthogonal n.property⟩

theorem orthonormal_positiveFourierVector :
    Orthonormal ℂ positiveFourierVector := (stdBasisZ.orthonormal.comp Subtype.val Subtype.val_injective).codRestrict
    nonpositiveFourierSubspaceᗮ
    (fun n => stdBasisZ_mem_nonpositive_orthogonal n.property)

theorem positiveFourierVector_span_orthogonal_eq_bot :
    (Submodule.span ℂ (range positiveFourierVector))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro b hb
  apply Subtype.ext
  apply lp.ext
  funext n
  by_cases hn : 0 < n
  · have h := (Submodule.mem_orthogonal _ _).mp hb
      (positiveFourierVector ⟨n, hn⟩)
      (Submodule.subset_span ((⟨⟨n, hn⟩, rfl⟩)))
    change ⟪stdBasisZ n, b⟫_ℂ = 0 at h
    simpa [stdBasisZ_apply, lp.inner_single_left] using h
  simp_all [nonpositive_orthogonal_coefficient_eq_zero]

def positiveFourierHilbertBasis  :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_positiveFourierVector
    positiveFourierVector_span_orthogonal_eq_bot

@[simp] theorem positiveFourierHilbertBasis_apply n :
    positiveFourierHilbertBasis n = positiveFourierVector n := congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    orthonormal_positiveFourierVector positiveFourierVector_span_orthogonal_eq_bot) n

/-- The linear subspace of sequences having genuinely finite support. -/
def finiteFourierSubmodule : Submodule ℂ L2Z where
  carrier := {b | (Function.support (b : FourierSeq)).Finite}
  zero_mem' := Set.finite_empty.subset fun n hn => hn (by simp)
  add_mem' := by
    intro b d hb hd
    refine (hb.union hd).subset ?_
    intro n hn
    by_contra h
    aesop
  smul_mem' := by
    intro a b hb
    refine hb.subset ?_
    simp_all

theorem stdBasisZ_mem_finiteFourierSubmodule n :
    stdBasisZ n ∈ finiteFourierSubmodule := by
  refine (finite_singleton n).subset ?_
  intro k hk
  by_contra hkn
  have hkn' : k ≠ n := by simpa   using hkn
  exact hk (by simp [stdBasisZ_apply, hkn'])

theorem finite_support_of_mem_span_stdBasisZ 
    (hb : b ∈ Submodule.span ℂ (range stdBasisZ)) :
    (Function.support (b : FourierSeq)).Finite := by
  apply (show Submodule.span ℂ (range stdBasisZ) ≤ finiteFourierSubmodule from ?_) hb
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact stdBasisZ_mem_finiteFourierSubmodule n

theorem finite_support_of_mem_span_positiveFourierHilbertBasis
    
    (hb : b ∈ Submodule.span ℂ (range positiveFourierHilbertBasis)) :
    (Function.support ((b : L2Z) : FourierSeq)).Finite := by
  have hle : Submodule.span ℂ (range positiveFourierHilbertBasis) ≤
      finiteFourierSubmodule.comap nonpositiveFourierSubspaceᗮ.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    rw [positiveFourierHilbertBasis_apply]
    exact stdBasisZ_mem_finiteFourierSubmodule n
  exact hle hb

theorem isSobolevSeq_of_finite_fourier_support s {b : L2Z}
    (hb : (Function.support (b : FourierSeq)).Finite) :
    IsSobolevSeq s (b : FourierSeq) := by
  apply summable_of_finite_support
  refine hb.subset ?_
  intro n hn
  simp_all

end PolyaNeumann

end
