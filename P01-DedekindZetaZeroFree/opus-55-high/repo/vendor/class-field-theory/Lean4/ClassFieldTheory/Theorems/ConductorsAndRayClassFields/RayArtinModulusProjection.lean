module

public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassFieldRealization
public import ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassIdealModulusProjection
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayClassIdealModulusProjectionPrime
public import ClassFieldTheory.AlgebraicNumberTheory.RayClass.PrimeGeneration
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.PublicRayClassComparison
public import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalArtin
public import ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ArithmeticUnramifiedPrimeArtin

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


/-!
# Naturality of ray Artin maps under reduction of the modulus

An embedding between two realizations of ray class fields intertwines the
Artin action with the canonical projection of ray class groups.  The
statement uses only Mathlib and public Definitions vocabulary; the idelic
implementation appears only in the proof.
-/

open scoped Classical NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

 local instance rayArtinModulusProjection_rayClassGroupCommGroup
    {K : Type} [Field K] [NumberField K]
    (m : RayClassModulus K) : CommGroup (RayClassGroup m) :=
  { (inferInstance : Group (RayClassGroup m)) with mul_comm := mul_comm' }

private theorem rayClassGroup_hom_ext_of_prime
    {K : Type} [Field K] [NumberField K]
    {G : Type} [CommGroup G]
    (n : RayClassModulus K)
    (f g : RayClassGroup n →* G)
    (hprime : ∀ (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support),
        f (rayClassOfFinitePrime n v hv) =
          g (rayClassOfFinitePrime n v hv)) :
    f = g := by
  let n' := GlobalClassFieldComparison.rayClassModulusToOriginal K n
  let e := GlobalClassFieldComparison.rayClassGroupEquivOriginal K n
  let ι : RayClass.primeToModulusIdeals n' →* RayClassGroup n :=
    e.symm.toMonoidHom.comp
      (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n'))
  have hιprime (v : HeightOneSpectrum (𝓞 K))
      (hv : v ∉ n.finitePart.support) :
      ι (RayClass.primeToModulusIdeal n' v hv) =
        rayClassOfFinitePrime n v hv := by
    rfl
  have hι : Function.Surjective ι := by
    intro q
    obtain ⟨I, hI⟩ :=
      QuotientGroup.mk'_surjective
        (RayClass.principalRayIdealSubgroup n') (e q)
    refine ⟨I, ?_⟩
    apply e.injective
    change e (e.symm
      (QuotientGroup.mk' (RayClass.principalRayIdealSubgroup n') I)) = e q
    rw [e.apply_symm_apply]
    exact hI
  have hcomp : f.comp ι = g.comp ι := by
    refine RayClass.primeToModulusIdeals_hom_ext
      (G := G) n' (f.comp ι) (g.comp ι) ?_
    intro v hv
    change f (ι (RayClass.primeToModulusIdeal n' v hv)) =
      g (ι (RayClass.primeToModulusIdeal n' v hv))
    rw [hιprime v hv]
    exact hprime v hv
  apply MonoidHom.ext
  intro q
  obtain ⟨I, rfl⟩ := hι q
  exact congrArg
    (fun h : RayClass.primeToModulusIdeals n' →* G => h I) hcomp
