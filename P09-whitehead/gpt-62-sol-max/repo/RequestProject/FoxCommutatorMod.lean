module

public import Mathlib
public import RequestProject.FoxRequirementMod

@[expose] public section

/-!
# The requirements modulo `m` pass to the commutator subgroup

`RequestProject/FoxCommutator.lean` proves the integral half of the application of
Lemma 2.1 made at the end of Section 2: if the integral requirements (2.2) hold for a
normal subgroup `N` whose abelianization `N/[N,N]` is torsion free, then they hold for
`[N,N]`.  The paper imposes the requirements modulo every prime as well, and applies
Lemma 2.1 over `𝔽ₚ` in exactly the same way.  This file carries out that half.

The link between the two descriptions is the reduction of coefficients
`ℤ[G] → 𝔽ₚ[G]` (`coeffHom`): the requirement modulo `m` of
`RequestProject/FoxRequirementMod.lean`, stated as a divisibility of coset sums, is
precisely the statement that the Fox boundary of the reduced presentation matrix is
injective over `ZMod m` (`forall_foxSatMod_iff_injective`).  For `m = p` prime the
coefficients form a field, so Lemma 2.1 applies and gives
`foxSatMod_commutator`.
-/


namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

/-! ### Reduction of coefficients `ℤ[G] → k[G]` -/

/-- Coefficientwise reduction of the group ring along the unique ring map `ℤ → k`. -/
noncomputable def coeffHom (k : Type*) [CommRing k] (H : Type*) [Group H] :
    MonoidAlgebra ℤ H →+* MonoidAlgebra k H :=
  MonoidAlgebra.mapRingHom H (Int.castRingHom k)

variable {k : Type*} [CommRing k]

theorem quotRingHom_coeffHom (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    quotRingHom k M (coeffHom k G x) = coeffHom k (G ⧸ M) (quotRingHom ℤ M x) :=
  DFunLike.congr_fun (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (Int.castRingHom k) (QuotientGroup.mk' M)).symm x

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `k[G]`. -/
noncomputable def coeffVec (k : Type*) [CommRing k] (H : Type*) [Group H] {J : Type*}
    (v : J →₀ MonoidAlgebra ℤ H) : J →₀ MonoidAlgebra k H :=
  Finsupp.mapRange (coeffHom k H) (map_zero _) v

@[simp] theorem coeffVec_apply (v : J →₀ MonoidAlgebra ℤ G) (j : J) :
    coeffVec k G v j = coeffHom k G (v j) := rfl

/-- Every vector over `ZMod m [G]` comes from a vector over `ℤ[G]`. -/
theorem exists_coeffVec (m : ℕ) (w : J →₀ MonoidAlgebra (ZMod m) G) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, coeffVec (ZMod m) G v = w :=
  Finsupp.mapRange_surjective _ (map_zero _) (MonoidAlgebra.map_surjective
    (Int.castRingHom (ZMod m)).toAddMonoidHom ZMod.intCast_surjective) w

/-! ### The reduced presentation matrix -/

/-- The Fox boundary matrix of the presentation, read over `k`. -/
noncomputable def bMod (k : Type*) [CommRing k] (H : Type*) [Group H] {I J : Type*}
    (b : I → J → MonoidAlgebra ℤ H) (i : I) (j : J) : MonoidAlgebra k H :=
  coeffHom k H (b i j)

theorem bMod_col_finite (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (j : J) : {i | bMod k G b i j ≠ 0}.Finite := by
  refine (hcol j).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi ⊢
  intro h
  exact hi (by simp [bMod, h])

theorem foxBoundaryK_bMod (b : I → J → MonoidAlgebra ℤ G) (v : J →₀ MonoidAlgebra ℤ G)
    (i : I) :
    foxBoundaryK k (bMod k G b) (coeffVec k G v) i = coeffHom k G (foxBoundary b v i) := by
  change ((v.mapRange (coeffHom k G) (map_zero _)).sum fun j a => a * coeffHom k G (b i j)) =
    coeffHom k G (v.sum fun j a => a * b i j)
  rw [Finsupp.sum_mapRange_index (fun j => zero_mul _), map_finsuppSum]
  simp only [map_mul]

/-! ### The requirement modulo `m` is injectivity of the boundary over `ZMod m` -/

/-- Vanishing modulo `m` of a coefficient vector is vanishing of its reduction over
`ZMod m`. -/
theorem vanishesModN_iff_zmod (m : ℕ) (M : Subgroup G) [M.Normal] (x : MonoidAlgebra ℤ G) :
    VanishesModN m M x.coeff ↔ quotRingHom (ZMod m) M (coeffHom (ZMod m) G x) = 0 := by
  rw [vanishesModN_iff_dvd_coeff, quotRingHom_coeffHom, MonoidAlgebra.ext_iff, Finsupp.ext_iff]
  simp only [coeffHom, MonoidAlgebra.coeff_mapRingHom, Int.coe_castRingHom,
    MonoidAlgebra.coeff_zero, Finsupp.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **The requirements modulo `m` are exactly the injectivity of the Fox boundary over
`ZMod m`.**  This is the analogue over `ZMod m` of
`FiniteChains.forall_foxSat_iff_injective`; for `m = 0` the two statements agree. -/
theorem forall_foxSatMod_iff_injective (m : ℕ) (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod m b v M) ↔
      Function.Injective
        (boundaryMapK (ZMod m) (bMod (ZMod m) G b) (bMod_col_finite b hcol) M) := by
  have hs : Function.Surjective (redVecK (ZMod m) M ∘ (coeffVec (ZMod m) G :
      (J →₀ MonoidAlgebra ℤ G) → _)) := Function.Surjective.comp (exists_liftK M) (exists_coeffVec m)
  rw [injective_iff_map_eq_zero, hs.forall]
  simp only [FoxSatMod, vanishesModN_iff_zmod, Function.comp_apply, Finsupp.ext_iff, Finsupp.zero_apply,
    boundaryMapK_redVecK, foxBoundaryK_bMod, redVecK_apply, coeffVec_apply, quotRingHom_coeffHom]

/-! ### Lemma 2.1 over `𝔽ₚ` -/

/-- **The requirements modulo a prime pass to the commutator subgroup.**  This is the
half modulo `p` of the application of Lemma 2.1 at the end of Section 2. -/
theorem foxSatMod_commutator (p : ℕ) [Fact p.Prime] (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSatMod p b v ⁅N, N⁆ := by
  have hle  := Subgroup.commutator_le_left N N
  rw [forall_foxSatMod_iff_injective p b hcol]
  exact injective_boundaryMapK_of_injective _ _ ⁅N, N⁆ N hle
    ((forall_foxSatMod_iff_injective p b hcol N).1 h)

end FiniteChains
