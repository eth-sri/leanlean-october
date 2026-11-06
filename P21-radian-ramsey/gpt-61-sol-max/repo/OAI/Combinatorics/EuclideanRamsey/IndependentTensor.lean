/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/IndependentTensor.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

public import Mathlib.Algebra.Module.LocalizedModule.Int

@[expose] public section

namespace OAI.EuclideanRamsey.IndependentTensor

noncomputable section
open scoped TensorProduct
open TensorProduct

variable (ι : Type*)

abbrev Poly := MvPolynomial ι ℚ
abbrev Rat := FractionRing (Poly ι)
abbrev JointPoly := MvPolynomial (ι ⊕ ι) ℚ
abbrev JointField := FractionRing (JointPoly ι)

def polyToRat : Poly ι →ₐ[ℚ] Rat ι :=
  IsScalarTower.toAlgHom ℚ (Poly ι) (Rat ι)

def jointToField : JointPoly ι →ₐ[ℚ] JointField ι :=
  IsScalarTower.toAlgHom ℚ (JointPoly ι) (JointField ι)

/-- A rational-function copy in a chosen injective family of joint variables. -/
def variableMap (f : ι → ι ⊕ ι) (hf : Function.Injective f) : Rat ι →ₐ[ℚ] JointField ι :=
  IsFractionRing.liftAlgHom (K := Rat ι) (g := (jointToField ι).comp (MvPolynomial.rename f))
    ((IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
      (MvPolynomial.rename_injective f hf))

abbrev leftMap : Rat ι →ₐ[ℚ] JointField ι := variableMap ι Sum.inl Sum.inl_injective
abbrev rightMap : Rat ι →ₐ[ℚ] JointField ι := variableMap ι Sum.inr Sum.inr_injective

@[simp] theorem variableMap_algebraMap (f : ι → ι ⊕ ι) (hf : Function.Injective f) (p : Poly ι) :
    variableMap ι f hf (algebraMap (Poly ι) (Rat ι) p) =
      algebraMap (JointPoly ι) (JointField ι) (MvPolynomial.rename f p) := by
  simp [variableMap, IsFractionRing.liftAlgHom_apply, jointToField]

/-- The map to the joint rational-function field. -/
def tensorEmbedding : Rat ι ⊗[ℚ] Rat ι →ₐ[ℚ] JointField ι :=
  Algebra.TensorProduct.lift (leftMap ι) (rightMap ι) (fun _ _ => Commute.all _ _)

lemma localized_injective {R A B D : Type*} [CommRing R] [AddCommGroup A] [Module R A] [Ring B] [Ring D]
    [Algebra R B] (S : Submonoid R)
    (f : A →ₗ[R] B) [IsLocalizedModule S f] (g : B →+* D)
    (hf : Function.Injective (g ∘ f)) : Function.Injective g := by
  apply (injective_iff_map_eq_zero g).mpr
  intro x hx
  obtain ⟨s,a,ha⟩ := IsLocalizedModule.exists_integer_multiple S f x
  have haz : a = 0 := hf (by simp [ha, Algebra.smul_def, hx])
  apply IsLocalizedModule.smul_injective f s
  simp only [Submonoid.smul_def, ←ha, haz, map_zero, smul_zero]


/-- The two independent rational-function copies embed faithfully. -/
theorem tensorEmbedding_injective : Function.Injective (tensorEmbedding ι) := by
  let half : Rat ι ⊗[ℚ] Poly ι →ₐ[ℚ] JointField ι :=
    (tensorEmbedding ι).comp (Algebra.TensorProduct.map (AlgHom.id ℚ (Rat ι)) (polyToRat ι))
  have hh : Function.Injective half := by
    apply localized_injective (nonZeroDivisors (Poly ι))
      (AlgebraTensorModule.rTensor ℚ (Poly ι) (Algebra.linearMap (Poly ι) (Rat ι))) half.toRingHom
    change Function.Injective (half.comp (Algebra.TensorProduct.map (polyToRat ι) (AlgHom.id ℚ (Poly ι))))
    convert (IsFractionRing.injective (JointPoly ι) (JointField ι)).comp
      (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).injective using 1
    change _ = ⇑((jointToField ι).comp (MvPolynomial.tensorEquivSum ℚ ι ι ℚ).toAlgHom)
    congr 1
    apply Algebra.TensorProduct.ext <;> ext i <;> simp [half,polyToRat,jointToField,tensorEmbedding]
  let e := Algebra.TensorProduct.comm ℚ (Rat ι) (Rat ι)
  apply Function.Injective.of_comp_right (g := e) ?_ e.surjective
  apply localized_injective (nonZeroDivisors (Poly ι))
    (AlgebraTensorModule.rTensor ℚ (Rat ι) (Algebra.linearMap (Poly ι) (Rat ι)))
    ((tensorEmbedding ι).comp e.toAlgHom).toRingHom
  change Function.Injective (((tensorEmbedding ι).comp e.toAlgHom).comp
    (Algebra.TensorProduct.map (polyToRat ι) (AlgHom.id ℚ (Rat ι))))
  dsimp only [e]
  rw [AlgHom.comp_assoc, Algebra.TensorProduct.comm_comp_map, ← AlgHom.comp_assoc]
  exact hh.comp (Algebra.TensorProduct.comm ℚ (Poly ι) (Rat ι)).injective


end

end OAI.EuclideanRamsey.IndependentTensor
