module

public import RequestProject.HurewiczDictionary
public import RequestProject.CoverAcyclic
public import RequestProject.FrameworkNecessityTF
public import RequestProject.NecessityLocallyFinite

@[expose] public section

/-!
# The Hurewicz input for a presented complex is a theorem

Let `K` be the two-complex of a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩`, let `F`
be the free group on the generators, `R = ⟪r_1, …, r_m⟫` the relator subgroup and
`G = π₁(K) = F/R`.  The requirements (2.2) of Section 2 are attached to the Fox matrix
`b i j = ∂r_j/∂x_i` read in `ℤ[G]`.

`RequestProject/HurewiczDictionary.lean` proves, for a normal subgroup `Ñ ◁ F` containing
the relators, that the Fox vector of `w ∈ Ñ` is a boundary of the chain complex of the
cover exactly when `w ∈ R·[Ñ, Ñ]`, and deduces that `Ñ/(R·[Ñ, Ñ])` is torsion free as soon
as the Fox boundary is injective modulo every prime.

This file transports that statement across the identification `G/N ≅ F/Ñ`
(`FiniteChains.quotQuotEquivPres`) and obtains the Hurewicz input of Section 2 as a
theorem: for every normal subgroup `N ◁ G` satisfying the requirements (2.2) modulo every
prime, the abelianization `N/[N, N]` is torsion free
(`FiniteChains.isMulTorsionFree_of_foxSatMod_pres`).

Consequently the implication `(1) ⇒ (2)` of Theorem A holds for a presented complex with
only two topological inputs left: the cell data of the chains and the construction of the
cover (`FiniteChains.hasAcyclicRegularCover_of_cellDataMod_pres`).
-/

namespace FiniteChains

open MonoidAlgebra


/-! ### Transport of the lifting property along isomorphisms -/

/-- `LiftsMod` transfers along additive isomorphisms intertwining the two maps. -/
theorem liftsMod_of_addEquiv {U V U' V' : Type*} [AddCommGroup U] [AddCommGroup V]
    [AddCommGroup U'] [AddCommGroup V'] (f : U →+ V) (f' : U' →+ V')
    (eU : U ≃+ U') (eV : V ≃+ V') (hcomm : ∀ u, f' (eU u) = eV (f u)) (n : ℕ)
    (h : LiftsMod f n) : LiftsMod f' n := by
  intro u' ⟨w', hw'⟩
  obtain ⟨u, rfl⟩ : ∃ u, eU u = u' := ⟨eU.symm u', eU.apply_symm_apply u'⟩
  have hfu : eV (f u) = n • w' := by rw [← hcomm u]; exact hw'
  have : f u = n • eV.symm w' := by
    apply eV.injective
    rw [hfu, map_nsmul, eV.apply_symm_apply]
  obtain ⟨u₀, hu₀⟩ := h u ⟨eV.symm w', this⟩
  exact ⟨eU u₀, by rw [hu₀, map_nsmul]⟩

/-! ### A torsion-freeness criterion -/

/-- If, in a normal subgroup `N`, a power of an element lying in `[N, N]` forces the element
itself into `[N, N]`, then the abelian group `N/[N, N]` is torsion free. -/
theorem isMulTorsionFree_map_commutator_of_pow {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] (hkey : ∀ g ∈ N, ∀ n : ℕ, n ≠ 0 → g ^ n ∈ ⁅N, N⁆ → g ∈ ⁅N, N⁆) :
    IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  haveI hcomm : IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) :=
    isMulCommutative_map_commutator N
  constructor
  intro n hn a b hab
  have hab' : a ^ n = b ^ n := hab
  have hcab : Commute a b⁻¹ := hcomm.is_comm.comm a b⁻¹
  have hone : (a * b⁻¹) ^ n = 1 := by
    rw [hcab.mul_pow, hab', inv_pow, mul_inv_cancel]
  obtain ⟨z, hz, hzeq⟩ := (a * b⁻¹).2
  have hzn : z ^ n ∈ ⁅N, N⁆ := by
    have hz1 : (QuotientGroup.mk' ⁅N, N⁆) (z ^ n) = 1 := by
      rw [map_pow, hzeq]
      exact congrArg Subtype.val hone
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz1
  have hzmem : z ∈ ⁅N, N⁆ := hkey z hz n hn hzn
  have hab1 : (a * b⁻¹) = 1 := by
    apply Subtype.ext
    show ((a * b⁻¹ : N.map (QuotientGroup.mk' ⁅N, N⁆)) : G ⧸ ⁅N, N⁆)
      = ((1 : N.map (QuotientGroup.mk' ⁅N, N⁆)) : G ⧸ ⁅N, N⁆)
    rw [Subgroup.coe_one, ← hzeq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hzmem
  exact mul_inv_eq_one.1 hab1

/-! ### The presented complex -/

variable {α : Type*} [Fintype α] [DecidableEq α] {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The relator subgroup `R = ⟪r_1, …, r_m⟫ ◁ F`. -/
def relSub : Subgroup (FreeGroup α) := Subgroup.normalClosure (Set.range ρ)

instance relSub_normal : (relSub ρ).Normal := Subgroup.normalClosure_normal

/-- The fundamental group `G = π₁(K) = F/R` of the presented complex. -/
abbrev PresGroup : Type _ := FreeGroup α ⧸ relSub ρ

/-- The Fox boundary matrix of the presentation, read in `ℤ[G]`. -/
noncomputable def foxMatrixPres (i : α) (j : J) : MonoidAlgebra ℤ (PresGroup ρ) :=
  quotRingHom ℤ (relSub ρ) (fox i (ρ j))

omit [Fintype α] [Fintype J] in
theorem foxMatrixPres_col_finite (j : J) : {i : α | foxMatrixPres ρ i j ≠ 0}.Finite :=
  (fox_generator_support_finite (ρ j)).subset (by
    intro i hi
    by_contra hz
    simp only [Set.mem_setOf_eq, not_not] at hz
    exact hi (by simp only [foxMatrixPres, hz, map_zero]))

section Subgroups

variable (Nt : Subgroup (FreeGroup α)) [Nt.Normal] (hR : relSub ρ ≤ Nt)

/-- The normal subgroup `N = Ñ/R ◁ G` attached to `Ñ ◁ F`. -/
def presSub : Subgroup (PresGroup ρ) := Nt.map (QuotientGroup.mk' (relSub ρ))

instance presSub_normal : (presSub ρ Nt).Normal :=
  Subgroup.Normal.map ‹Nt.Normal› _ (QuotientGroup.mk'_surjective _)

/-- The identification `G/N ≅ F/Ñ` of the deck group of the cover. -/
noncomputable def quotQuotEquivPres :
    (PresGroup ρ ⧸ presSub ρ Nt) ≃* (FreeGroup α ⧸ Nt) :=
  QuotientGroup.quotientQuotientEquivQuotient (relSub ρ) Nt hR

omit [Fintype α] [DecidableEq α] [Fintype J] in
theorem quotQuotEquivPres_mk (w : FreeGroup α) :
    quotQuotEquivPres ρ Nt hR
        (QuotientGroup.mk (QuotientGroup.mk w : PresGroup ρ) : PresGroup ρ ⧸ presSub ρ Nt)
      = (QuotientGroup.mk w : FreeGroup α ⧸ Nt) :=
  (MulEquiv.eq_symm_apply (quotQuotEquivPres ρ Nt hR)).mp rfl

/-- The induced isomorphism of group rings `ℤ[G/N] ≅ ℤ[F/Ñ]`. -/
noncomputable def ringEquivPres :
    MonoidAlgebra ℤ (PresGroup ρ ⧸ presSub ρ Nt) ≃ₐ[ℤ] MonoidAlgebra ℤ (FreeGroup α ⧸ Nt) :=
  MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR)

omit [Fintype α] [DecidableEq α] [Fintype J] in
/-- The reduction of the group ring of the free group to `ℤ[F/Ñ]` factors through the two
successive quotients. -/
theorem ringEquivPres_quot (x : MonoidAlgebra ℤ (FreeGroup α)) :
    ringEquivPres ρ Nt hR (quotRingHom ℤ (presSub ρ Nt) (quotRingHom ℤ (relSub ρ) x))
      = proj Nt x := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  | single g n =>
      rw [quotRingHom_single, quotRingHom_single, proj_single]
      show MonoidAlgebra.domCongr ℤ ℤ (quotQuotEquivPres ρ Nt hR) (single _ n) = _
      rw [MonoidAlgebra.domCongr_single, quotQuotEquivPres_mk]

end Subgroups

end FiniteChains
