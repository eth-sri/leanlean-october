module


public import RequestProject.FoxRequirement
public import RequestProject.BoundaryRing

@[expose] public section

/-!
# The requirements pass to the commutator subgroup (Lemma 2.1 in the paper's application)

Section 2 applies Lemma 2.1 with `Q = G/[N,N]`, `H = N/[N,N]` and `f = ∂_{2,[N,N]}` to
conclude that, if the requirements (2.2) hold for a normal subgroup `N` and `N/[N,N]` is
torsion free, then they also hold for `[N,N]`.

This file carries out that application.  The requirements are the ones formalized in
`RequestProject/FoxRequirement.lean`, and the algebraic input is the unconditional Lemma 2.1
of `RequestProject/LemmaTwoOne.lean`.
-/

noncomputable section

open scoped commutatorElement

namespace FiniteChains

open MonoidAlgebra

variable {G : Type*} [Group G] {I J : Type*}

section

variable (M : Subgroup G) [M.Normal] (v : J →₀ MonoidAlgebra ℤ G)

/-- Coefficientwise reduction of a vector over `ℤ[G]` to a vector over `ℤ[G/M]`. -/
def redVec :=
  redVecK ℤ M v

@[simp] theorem redVec_apply (j : J) :
    redVec M v j = quotRingHom ℤ M (v j) := rfl

end

section

variable (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite)
    (M : Subgroup G)
    [M.Normal]

variable (j : J)

/-- The Fox boundary `∂_{2,M}` as a map of free left `ℤ[G/M]`-modules. -/
def boundaryMap :=
  boundaryMapK ℤ b hcol M

theorem boundaryMap_apply_coord
    (u : J →₀ MonoidAlgebra ℤ _) (i : I) :
    boundaryMap b hcol M u i = ∑ j ∈ u.support, u j * quotRingHom ℤ M (b i j) :=
  by apply boundaryMapK_apply_coord

theorem boundaryMap_redVec
    (v : J →₀ MonoidAlgebra ℤ G) (i : I) :
    boundaryMap b hcol M (redVec M v) i = quotRingHom ℤ M (foxBoundary b v i) :=
  by apply boundaryMapK_redVecK

end

section

variable (M : Subgroup G) [M.Normal]

/-- Reduction of `x ∈ ℤ[G]` vanishes exactly when, inside every coset of `M`, the
coefficients of `x` add up to zero. -/
theorem vanishesMod_iff_quotRingHom_eq_zero (x : MonoidAlgebra ℤ G) :
    VanishesMod M x.coeff ↔ quotRingHom ℤ M x = 0 := by
  classical
  have hval : ∀ g : G, (quotRingHom ℤ M x).coeff (g) =
      ∑ h ∈ x.coeff.support.filter (fun h => h * g⁻¹ ∈ M), x.coeff h := by
    intro g
    show (Finsupp.mapDomain (QuotientGroup.mk' M) x.coeff) g = _
    rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finset.sum_filter]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finsupp.single_apply]
    congr 1
    simp only [eq_iff_iff, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    constructor
    · intro hh
      have h2 := Subgroup.Normal.conj_mem (inferInstance) _ (by simpa using M.inv_mem hh) h
      have hgr : h * (g⁻¹ * h) * h⁻¹ = h * g⁻¹ := by group
      simp_all
    · intro hh
      have h2 := Subgroup.Normal.conj_mem (inferInstance) _ (by simpa using M.inv_mem hh) h⁻¹
      have hgr : h⁻¹ * (g * h⁻¹) * h⁻¹⁻¹ = h⁻¹ * g := by group
      simp_all
  constructor
  · intro h
    ext q
    induction q using QuotientGroup.induction_on with
    | H g => aesop
  · intro h g
    rw [← hval g, h]
    simp

/-- Every vector over `ℤ[G/M]` lifts to a vector over `ℤ[G]`. -/
theorem exists_lift (u : J →₀ MonoidAlgebra ℤ _) :
    ∃ v : J →₀ MonoidAlgebra ℤ G, redVec M v = u := exists_liftK M u

end

variable (b : I → J → MonoidAlgebra ℤ G) (hcol : ∀ j, {i | b i j ≠ 0}.Finite)

/-- The requirements attached to all coefficient vectors hold at `M` exactly when the
reduced boundary map is injective. -/
theorem forall_foxSat_iff_injective (M : Subgroup G) [M.Normal] :
    (∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v M) ↔
      Function.Injective (boundaryMap b hcol M) := by
  classical
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨v, rfl⟩ := exists_lift M u
    have hbd : ∀ i, VanishesMod M (foxBoundary b v i).coeff := by
      intro i
      rw [vanishesMod_iff_quotRingHom_eq_zero, ← boundaryMap_redVec b hcol M v i, hu]
      rfl
    refine Finsupp.ext fun j => ?_
    exact (vanishesMod_iff_quotRingHom_eq_zero M _).1 ((h v hbd) j)
  · intro h v hbd j
    rw [vanishesMod_iff_quotRingHom_eq_zero]
    have hu : boundaryMap b hcol M (redVec M v) = 0 := by
      refine Finsupp.ext fun i => ?_
      simp_all [boundaryMap_redVec, vanishesMod_iff_quotRingHom_eq_zero]
    have hz : redVec M v = 0 := h (by assumption)
    have := congrArg (fun w : J →₀ MonoidAlgebra ℤ _ => w j) hz
    assumption

/-- **Lemma 2.1 for a pair of normal subgroups.**  If `C ≤ N` are normal subgroups of `G`
with `N/C` torsion-free abelian, then injectivity of the boundary reduced modulo `N`
implies injectivity of the boundary reduced modulo `C`.  This is the case `k = ℤ` of
`FiniteChains.injective_boundaryMapK_of_injective`. -/
theorem injective_boundaryMap_of_injective (C N : Subgroup G) [C.Normal] [N.Normal]
    (hCN : C ≤ N)
    [IsMulCommutative (N.map (QuotientGroup.mk' C))]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' C))]
    (h : Function.Injective (boundaryMap b hcol N)) :
    Function.Injective (boundaryMap b hcol C) :=
  injective_boundaryMapK_of_injective b hcol C N hCN h

/-- The image of `N` in `G/[N,N]`, that is `N/[N,N]`, is abelian. -/
instance isMulCommutative_map_commutator (N : Subgroup G) [N.Normal] :
    IsMulCommutative (N.map (QuotientGroup.mk' ⁅N, N⁆)) := by
  constructor
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨m, hm, rfl⟩ := hy
  apply Subtype.ext
  show (QuotientGroup.mk' ⁅N, N⁆ n) * (QuotientGroup.mk' ⁅N, N⁆ m)
      = (QuotientGroup.mk' ⁅N, N⁆ m) * (QuotientGroup.mk' ⁅N, N⁆ n)
  rw [← map_mul, ← map_mul]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.eq]
  have hgr : (n * m)⁻¹ * (m * n) = ⁅m⁻¹, n⁻¹⁆ := by group
  rw [hgr]
  exact Subgroup.commutator_mem_commutator (N.inv_mem hm) (N.inv_mem hn)

/-- **The requirements pass to the commutator subgroup.**  If every requirement (2.2) holds
for the normal subgroup `N` and `N/[N,N]` is torsion free, then every requirement holds for
`[N,N]`. -/
theorem foxSat_commutator (b : I → J → MonoidAlgebra ℤ G)
    (hcol : ∀ j, {i | b i j ≠ 0}.Finite) (N : Subgroup G) [N.Normal]
    [IsMulTorsionFree (N.map (QuotientGroup.mk' ⁅N, N⁆))]
    (h : ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v N) :
    ∀ v : J →₀ MonoidAlgebra ℤ G, FoxSat b v ⁅N, N⁆ := by
  rw [forall_foxSat_iff_injective b hcol]
  exact injective_boundaryMap_of_injective b hcol _ N (Subgroup.commutator_le_left N N)
    ((forall_foxSat_iff_injective b hcol N).1 h)

end FiniteChains
