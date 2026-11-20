module

public import ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
public import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.MaximalKummerNorm

@[expose] public section

/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

set_option autoImplicit false

/-!
# Nondegeneracy of the local Hilbert pairing

The maximal finite Kummer extension identifies the common kernel of the
local Hilbert-symbol characters with the subgroup of powers.  The resulting
symbol therefore descends to a nondegenerate pairing on the local power-class
group.
-/

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open KummerTheory LocalFieldTheory

variable (K : Type) [Field K]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

private theorem maximalLocalKummerPairing_eq_transpose
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    let Delta := maximalKummerSubgroup K n
    let E := maximalLocalKummerExtension K n
    letI : FiniteDimensional K E :=
      maximalKummerRadicalExtension_finiteDimensional K n hnK hmu
    letI : IsAbelianGalois K E :=
      kummerRadicalExtension_isAbelianGalois
        (K := K) (Omega := SeparableClosure K) n hmu Delta.1
    let hDelta : Delta.1 ≤
        finiteKummerRadicalSubgroup (K := K) (L := E) n :=
      le_finiteKummerRadicalSubgroup_kummerRadicalExtension
        n hnK Delta.1
    maximalLocalKummerPairingRightHom K n hnK hmu a b =
      (nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu).symm
        (restrictedKummerTranspose n hmu Delta hDelta
          (maximalLocalKummerNormResidueAutomorphism K n hnK hmu a)
          (maximalRestrictedRadicalQuotientEquiv K n
            (QuotientGroup.mk'
              (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b))) := rfl

/-- An element in the left kernel of every local Hilbert-symbol character
is exactly an `n`-th power. -/
theorem localHilbertSymbol_left_kernel
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ) :
    (∀ b : Kˣ, localHilbertSymbol K n hnK hmu a b = 1) ↔
      a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  let Delta := maximalKummerSubgroup K n
  let E := maximalLocalKummerExtension K n
  let P := (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
  let hDelta : Delta.1 ≤
      finiteKummerRadicalSubgroup (K := K) (L := E) n :=
    le_finiteKummerRadicalSubgroup_kummerRadicalExtension
      n hnK Delta.1
  let : FiniteDimensional K E :=
    maximalKummerRadicalExtension_finiteDimensional K n hnK hmu
  let : IsAbelianGalois K E :=
    kummerRadicalExtension_isAbelianGalois
      (K := K) (Omega := SeparableClosure K) n hmu Delta.1
  constructor
  · intro h
    let sigma :=
      maximalLocalKummerNormResidueAutomorphism K n hnK hmu a
    have hsigma : sigma = 1 := by
      apply
        (restrictedKummerTranspose_injective_of_adjoin
          n hmu Delta hDelta
          (kummerRadicalExtension_internalRoots_adjoin_eq_top
              n Delta))
      rw [map_one]
      apply MonoidHom.ext
      intro q
      obtain ⟨q, rfl⟩ :=
        (maximalRestrictedRadicalQuotientEquiv K n).surjective q
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective P q
      let e := nthRootsSubgroupEquivOfPrimitiveRoots K E n hmu
      apply e.symm.injective
      have hpair : maximalLocalKummerPairingRightHom K n hnK hmu a b = 1 := by
        rw [maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom]
        exact h b
      have hcompare := maximalLocalKummerPairing_eq_transpose K n hnK hmu a b
      change
        maximalLocalKummerPairingRightHom K n hnK hmu a b =
          e.symm
            (restrictedKummerTranspose n hmu Delta hDelta sigma
              (maximalRestrictedRadicalQuotientEquiv K n
                (QuotientGroup.mk' P b))) at hcompare
      rw [← hcompare, hpair]
      change 1 = e.symm 1
      exact (map_one e.symm).symm
    have haNorm : a ∈ localNormSubgroup K E := by
      rw [← abelianLocalArtinMonoidHom_ker K E, MonoidHom.mem_ker]
      change sigma = 1
      exact hsigma
    have hmax := maximalKummerNormSubgroup_eq_powMonoidHom_range
      (K := K) (Omega := SeparableClosure K) n hnK hmu
    change localNormSubgroup K E = P at hmax
    rw [hmax] at haNorm
    exact haNorm
  · intro ha b
    obtain ⟨c, hc⟩ := (MonoidHom.mem_range (G := Kˣ)).1 ha
    have hca : c ^ (n : ℕ) = a := by
      simpa only [powMonoidHom_apply] using hc
    rw [← hca]
    change localHilbertSymbolHom K n hnK hmu b (c ^ (n : ℕ)) = 1
    rw [map_pow]
    apply Subtype.ext
    exact (KummerTheory.mem_nthRootsSubgroup_iff K).mp
      (localHilbertSymbol K n hnK hmu c b).property

/-- An element in the right kernel of every local Hilbert-symbol character
is exactly an `n`-th power. -/
theorem localHilbertSymbol_right_kernel
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (∀ a : Kˣ, localHilbertSymbol K n hnK hmu a b = 1) ↔
      b ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  rw [← localHilbertSymbol_left_kernel K n hnK hmu b]
  constructor
  · intro h a
    rw [localHilbertSymbol_skew K n hnK hmu b a, h a, inv_one]
  · intro h a
    rw [localHilbertSymbol_skew K n hnK hmu a b, h a, inv_one]

 section

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)

noncomputable def localHilbertRightPowerClassHom (a : Kˣ) :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
      nthRootsSubgroup K (n : ℕ) :=
  QuotientGroup.lift
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
    (maximalLocalKummerPairingRightHom K n hnK hmu a) (by
      intro b hb
      rw [MonoidHom.mem_ker]
      obtain ⟨c, rfl⟩ := (MonoidHom.mem_range).1 hb
      rw [powMonoidHom_apply, map_pow]
      apply Subtype.ext
      change
        (↑(maximalLocalKummerPairingRightHom K n hnK hmu a c) : Kˣ) ^
          (n : ℕ) = 1
      exact (KummerTheory.mem_nthRootsSubgroup_iff K).mp
        (maximalLocalKummerPairingRightHom K n hnK hmu a c).property)

@[simp]
private theorem localHilbertRightPowerClassHom_mk (a b : Kˣ) :
    localHilbertRightPowerClassHom K n hnK hmu a
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b) =
      maximalLocalKummerPairingRightHom K n hnK hmu a b :=
  rfl

 noncomputable def localHilbertPowerClassLeftHom :
    Kˣ →*
      ((Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
        nthRootsSubgroup K (n : ℕ)) where
  toFun a := localHilbertRightPowerClassHom K n hnK hmu a
  map_one' := by
    apply MonoidHom.ext
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range q
    change maximalLocalKummerPairingRightHom K n hnK hmu 1 b = 1
    rw [maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom]
    exact map_one (localHilbertSymbolHom K n hnK hmu b)
  map_mul' := by
    intro a c
    apply MonoidHom.ext
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
      (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range q
    change
      maximalLocalKummerPairingRightHom K n hnK hmu (a * c) b =
        maximalLocalKummerPairingRightHom K n hnK hmu a b *
          maximalLocalKummerPairingRightHom K n hnK hmu c b
    rw [maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom,
      maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom,
      maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom]
    exact map_mul (localHilbertSymbolHom K n hnK hmu b) a c

 theorem powMonoidHom_range_le_localHilbertPowerClassLeftHom_ker :
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range ≤
      MonoidHom.ker (localHilbertPowerClassLeftHom K n hnK hmu) := by
  intro a ha
  rw [MonoidHom.mem_ker]
  obtain ⟨c, hc⟩ := (MonoidHom.mem_range).1 ha
  have hca : c ^ (n : ℕ) = a := by
    simpa using hc
  apply MonoidHom.ext
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range q
  change maximalLocalKummerPairingRightHom K n hnK hmu a b = 1
  rw [← hca, maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom]
  rw [map_pow]
  apply Subtype.ext
  exact (KummerTheory.mem_nthRootsSubgroup_iff K).mp
    (localHilbertSymbol K n hnK hmu c b).property

end

/-- The local Hilbert symbol descended in both variables to the local
power-class group. -/
noncomputable def localHilbertPairing
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
      ((Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
        nthRootsSubgroup K (n : ℕ)) :=
  QuotientGroup.lift
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
    (localHilbertPowerClassLeftHom K n hnK hmu)
    (powMonoidHom_range_le_localHilbertPowerClassLeftHom_ker
      K n hnK hmu)

section

variable (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)

/-- Evaluation of the descended pairing agrees with the original local
Hilbert symbol on representatives. -/
@[simp]
theorem localHilbertPairing_apply (a b : Kˣ) :
    localHilbertPairing K n hnK hmu
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range b) =
      localHilbertSymbol K n hnK hmu a b := by
  solve_by_elim [maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom]

/-- The transposed descended pairing, viewed as a homomorphism into the
character group. -/
noncomputable def localHilbertPairingFlip :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
      ((Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
        nthRootsSubgroup K (n : ℕ)) where
  toFun b :=
    { toFun := fun a => localHilbertPairing K n hnK hmu a b
      map_one' := by
        rw [map_one]
        rfl
      map_mul' := by
        intro a c
        rw [map_mul]
        rfl }
  map_one' := by
    apply MonoidHom.ext
    intro a
    exact map_one (localHilbertPairing K n hnK hmu a)
  map_mul' := by
    intro b c
    apply MonoidHom.ext
    intro a
    exact map_mul (localHilbertPairing K n hnK hmu a) b c

end

/-- The descended local Hilbert pairing separates power classes in its
left variable. -/
theorem localHilbertPairing_injective_left
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Injective (localHilbertPairing K n hnK hmu) := by
  intro q r hqr
  let P := (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective P q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective P r
  apply (QuotientGroup.eq_iff_div_mem).2
  apply (localHilbertSymbol_left_kernel K n hnK hmu (a / c)).1
  intro b
  have hv := DFunLike.congr_fun hqr (QuotientGroup.mk' P b)
  change
    maximalLocalKummerPairingRightHom K n hnK hmu a b =
      maximalLocalKummerPairingRightHom K n hnK hmu c b at hv
  let localHilbertSymbolHom₀ := localHilbertSymbolHom K n hnK hmu b
  have hvSymbol :
      localHilbertSymbolHom₀ a =
        localHilbertSymbolHom₀ c := by
    exact
      (maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom
        K n hnK hmu a b).symm.trans
        (hv.trans
          (maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom
            K n hnK hmu c b))
  calc
    _ =
        localHilbertSymbolHom₀ a /
          localHilbertSymbolHom₀ c :=
      map_div (localHilbertSymbolHom₀) a c
    _ = localHilbertSymbolHom₀ c /
        localHilbertSymbolHom₀ c :=
      congrArg
        (fun z => z / localHilbertSymbolHom₀ c) hvSymbol
    _ = 1 := div_self' (localHilbertSymbolHom₀ c)

/-- The descended local Hilbert pairing separates power classes in its
right variable. -/
theorem localHilbertPairing_injective_right
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Function.Injective (localHilbertPairingFlip K n hnK hmu) := by
  intro q r hqr
  let P := (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective P q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective P r
  apply (QuotientGroup.eq_iff_div_mem).2
  apply (localHilbertSymbol_right_kernel K n hnK hmu (b / c)).1
  intro a
  have hv := DFunLike.congr_fun hqr (QuotientGroup.mk' P a)
  change
    localHilbertPairing K n hnK hmu
        (QuotientGroup.mk' P a) (QuotientGroup.mk' P b) =
      localHilbertPairing K n hnK hmu
        (QuotientGroup.mk' P a) (QuotientGroup.mk' P c) at hv
  let maximalLocalKummerPairingRightHom₀ := maximalLocalKummerPairingRightHom K n hnK hmu a
  change
      maximalLocalKummerPairingRightHom₀ b =
        maximalLocalKummerPairingRightHom₀ c at hv
  calc
    _ =
        maximalLocalKummerPairingRightHom₀ (b / c) :=
      (maximalLocalKummerPairingRightHom_eq_localHilbertSymbolHom
        K n hnK hmu a (b / c)).symm
    _ = maximalLocalKummerPairingRightHom₀ b /
        maximalLocalKummerPairingRightHom₀ c :=
      map_div (maximalLocalKummerPairingRightHom₀) b c
    _ = maximalLocalKummerPairingRightHom₀ c /
        maximalLocalKummerPairingRightHom₀ c :=
      congrArg
        (fun z =>
          z / maximalLocalKummerPairingRightHom₀ c) hv
    _ = 1 := div_self'
      (maximalLocalKummerPairingRightHom₀ c)

/-- The local Hilbert pairing on power classes is nondegenerate in both
variables. -/
theorem localHilbertPairing_nondegenerate
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    (∀ a,
      (∀ b, localHilbertPairing K n hnK hmu a b = 1) → a = 1) ∧
    (∀ b,
      (∀ a, localHilbertPairing K n hnK hmu a b = 1) → b = 1) := by
  constructor
  · intro a ha
    apply localHilbertPairing_injective_left K n hnK hmu
    apply MonoidHom.ext
    intro b
    rw [ha b, map_one]
    rfl
  · intro b hb
    apply localHilbertPairing_injective_right K n hnK hmu
    apply MonoidHom.ext
    intro a
    change localHilbertPairing K n hnK hmu a b =
      localHilbertPairing K n hnK hmu a 1
    rw [hb a, map_one]

end Kummer
end LocalClassFieldTheory

end
