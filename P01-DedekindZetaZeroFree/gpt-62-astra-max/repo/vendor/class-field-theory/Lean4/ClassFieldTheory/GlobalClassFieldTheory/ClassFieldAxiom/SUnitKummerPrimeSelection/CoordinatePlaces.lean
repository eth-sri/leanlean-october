module

public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.BasePlaceSelection
public import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.FinitePlaceDecomposition

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Coordinate places in an S-unit Kummer extension

This file lifts the chosen base places to coordinate places in the full
Kummer extension and proves the required decomposition and unramifiedness
properties.
-/

open scoped NumberField Classical IsMulCommutative
open NumberField IsDedekindDomain
open KummerTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

section FinitePlaces

variable {K : Type} [Field K]
    [NumberField K]

section

variable {Omega : Type} [Field Omega] [Algebra K Omega] [IsSepClosure K Omega]
    (E : IntermediateField K Omega) [FiniteDimensional K E] [IsGalois K E] [IsMulCommutative Gal(E/K)]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v) (r : ℕ) (eG : Gal(E/K) ≃* (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))

/-- A completely decomposed coordinate place above the `i`-th chosen
base prime. -/
theorem exists_sUnitKummerCoordinatePlace
    (i : Fin
      (sUnitKummerPrimeCount E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG) S
        (sUnitKummerKernelGenerator E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG) S
        (sUnitKummerKernelGenerator E n hmu
          p v hp hv hn r eG S i)
    ∃ q : HeightOneSpectrum (𝓞 Ni),
      _root_.finitePlaceBelow (K := K) q =
          sUnitKummerChosenBasePlaces E n hmu
            p v hp hv hn r eG S i ∧
        _root_.finitePlaceDecompositionGroup (L := N) q =
          ⊤ := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension (Omega := Omega) n S'
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional
      (K := K) (Omega := Omega) n (by
        exact_mod_cast n.ne_zero) hmu S'
  let Ni :=
    enlargedSUnitKummerCyclicFixedField
        E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
         E n r eG) S
      (sUnitKummerKernelGenerator
          E n hmu
        p v hp hv hn r eG S i)
  let :=
    NumberField.of_module_finite K Ni
  let :=
    enlargedSUnitKummerCyclicFixedField_isGalois
        E n hmu
      (galois_pow_eq_one_of_equiv_pi_zmod
         E n r eG) S
      (sUnitKummerKernelGenerator
          E n hmu
        p v hp hv hn r eG S i)
  have h :=
    sUnitKummerChosenBasePlaces_mem_coordinateBasePlaceCandidates
        E n hmu
      p v hp hv hn r eG S i
  change ∃ q : HeightOneSpectrum (𝓞 Ni),
    _root_.finitePlaceBelow q =
        sUnitKummerChosenBasePlaces
            E n hmu
          p v hp hv hn r eG S i ∧
      _root_.finitePlaceDecompositionGroup
            q =
        ⊤ at h
  exact h

/-- The selected coordinate place above the `i`-th chosen base prime. -/
noncomputable def sUnitKummerCoordinatePlace
    (i : Fin
      (sUnitKummerPrimeCount
        (K := K) E n hmu r S)) :=
  Classical.choose
    (exists_sUnitKummerCoordinatePlace
      (K := K) (Omega := Omega) E n hmu
      p v hp hv hn r eG S i)

/-- The selected coordinate place lies over the corresponding chosen
base prime. -/
@[simp]
theorem sUnitKummerCoordinatePlace_below
    (i : Fin
      (sUnitKummerPrimeCount E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG) S
        (sUnitKummerKernelGenerator E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    _root_.finitePlaceBelow (K := K)
        (sUnitKummerCoordinatePlace E n hmu
          p v hp hv hn r eG S i) =
      sUnitKummerChosenBasePlaces E n hmu
        p v hp hv hn r eG S i :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace E n hmu
      p v hp hv hn r eG S i)).1

end

/-- The selected coordinate place is completely decomposed in the full
Kummer extension over its coordinate fixed field. -/
@[simp]
theorem sUnitKummerCoordinatePlace_decompositionGroup
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
    let Ni :=
      enlargedSUnitKummerCyclicFixedField
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG) S
        (sUnitKummerKernelGenerator E n hmu
          p v hp hv hn r eG S i)
    letI : NumberField Ni :=
      NumberField.of_module_finite K Ni
    letI : IsGalois Ni N :=
      enlargedSUnitKummerCyclicFixedField_isGalois
        (K := K) (Omega := Omega) E n hmu
        (galois_pow_eq_one_of_equiv_pi_zmod E n r eG) S
        (sUnitKummerKernelGenerator E n hmu
          p v hp hv hn r eG S i)
    _root_.finitePlaceDecompositionGroup
        (K := Ni) (L := N)
        (sUnitKummerCoordinatePlace E n hmu
          p v hp hv hn r eG S i) =
      ⊤ :=
  (Classical.choose_spec
    (exists_sUnitKummerCoordinatePlace E n hmu
      p v hp hv hn r eG S i)).2

/-- The `i`-th selected base prime is unramified in the full Kummer
extension. -/
theorem sUnitKummerChosenBasePlace_not_mem_ramified
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    sUnitKummerChosenBasePlaces E n hmu
        p v hp hv hn r eG S i ∉
      _root_.ramifiedBaseFinitePlaces
        (K := K) (L := N) := by
  dsimp only
  intro hram
  apply
    sUnitKummerChosenBasePlaces_not_mem_avoided
        E n hmu
      p v hp hv hn r eG S i
  unfold sUnitKummerAvoidedBasePlaces
  dsimp only
  exact
    Finset.mem_union_left _
      (Finset.mem_union_right _ hram)

/-- The chosen completed place at `p_i` is unramified in `N/K`. -/
theorem sUnitKummerChosenBasePlace_isUnramified
    {Omega : Type} [Field Omega] [Algebra K Omega]
    [IsSepClosure K Omega]
    (E : IntermediateField K Omega)
    [FiniteDimensional K E] [IsGalois K E]
    [IsMulCommutative Gal(E/K)]
    (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v)
    (hn : (n : ℕ) = p ^ v)
    (r : ℕ)
    (eG :
      Gal(E/K) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (i : Fin
      (sUnitKummerPrimeCount E n hmu r S)) :
    let S' :=
      enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
    let N :=
      fullSUnitKummerExtension (Omega := Omega) n S'
    let hnK : ((n : ℕ) : K) ≠ 0 := by
      exact_mod_cast n.ne_zero
    letI : FiniteDimensional K N :=
      fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
    letI : IsGalois K N :=
      fullSUnitKummerExtension_isGalois n S'
    letI : NumberField N :=
      NumberField.of_module_finite K N
    _root_.ChosenFinitePlaceIsUnramified
      (K := K) (L := N)
      (sUnitKummerChosenBasePlaces E n hmu
        p v hp hv hn r eG S i) := by
  dsimp only
  let S' :=
    enlargeByFiniteKummerRadicalSupport (L := E) n hmu S
  let N :=
    fullSUnitKummerExtension (Omega := Omega) n S'
  have hnK : ((n : ℕ) : K) ≠ 0 := by
    exact_mod_cast n.ne_zero
  let : FiniteDimensional K N :=
    fullSUnitKummerExtension_finiteDimensional n hnK hmu S'
  let : IsGalois K N :=
    fullSUnitKummerExtension_isGalois n S'
  let :=
    NumberField.of_module_finite K N
  apply
    _root_.chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  by_contra hram
  apply
    sUnitKummerChosenBasePlace_not_mem_ramified
        E n hmu
      p v hp hv hn r eG S i
  rw [_root_.mem_ramifiedBaseFinitePlaces_iff]
  exact
    ⟨_,
      _root_.finitePlaceExtensionCentre_liesOver

        _
        (_root_.chosenFinitePlaceExtension
           _),
      hram⟩

end FinitePlaces

end GlobalClassFieldTheory.ClassFieldAxiom

end
