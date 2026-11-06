import RequestProject.Pi2Dictionary
import RequestProject.CycleLiftingFinsupp
import RequestProject.CoverComplexFinsupp
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open MonoidAlgebra
universe u
variable {α J : Type u} {Nsub : Subgroup (FreeGroup α)} [Nsub.Normal]
variable {Q K : Type u} [Group Q]

theorem fs_mapDomain_prodMap_id_apply (Φ : (FreeGroup α ⧸ Nsub) →* Q)
    (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) q j :
    Finsupp.mapDomain (Prod.map (⇑Φ) id) u (q, j)
      = (MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j)).coeff q := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ =>
      rw [Finsupp.mapDomain_add, Finsupp.add_apply, h₁, h₂]
      simp [map_add]
  | single p n =>
      cases' p with q₀ j₀
      rw [Finsupp.mapDomain_single, fsCoords_single]
      by_cases hj : j = j₀
      · simp_all [Finsupp.single_eq_same, MonoidAlgebra.mapDomain_single, MonoidAlgebra.coeff_single, Finsupp.single_apply]
      simp_all

/-- **Pushing a two-chain of the cover to the next stage is zero iff its Fox coordinates
die.**  Here `Φ` is the map of deck groups and `g` the (injective) inclusion of the sets of
two-cells. -/
theorem fs_mapDomain_prodMap_eq_zero_iff (Φ : (FreeGroup α ⧸ Nsub) →* Q) (g : J → K)
    (hg : Function.Injective g) (u : ((FreeGroup α ⧸ Nsub) × J) →₀ ℤ) :
    Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0 ↔
      ∀ j, MonoidAlgebra.mapDomainRingHom ℤ Φ (fsCoords Nsub J u j) = 0 := by
  classical
  have hfac : (Prod.map (⇑Φ) g) = (Prod.map id g) ∘ (Prod.map (⇑Φ) id) := by
    rfl
  have hinj : Function.Injective (Prod.map (id : Q → Q) g) :=
    Function.Injective.prodMap Function.injective_id hg
  rw [hfac, Finsupp.mapDomain_comp]
  constructor
  · intro h j
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) id) u = 0 := by
      refine Finsupp.mapDomain_injective hinj ?_
      simp_all
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun q => ?_
    rw [← fs_mapDomain_prodMap_id_apply Φ u q j, h0]
    simp
  · intro h
    have h0 : Finsupp.mapDomain (Prod.map (⇑Φ) id) u = 0 := by
      refine Finsupp.ext fun p => ?_
      cases' p with q j
      rw [fs_mapDomain_prodMap_id_apply Φ u q j, h j]
      simp
    simp_all


variable [DecidableEq α]

/-- The actual cellular two-cycle condition, for arbitrary cell sets. -/
theorem fs_univCover_zero_pi2_iff (ρ : J → FreeGroup α)
    (Φ : PresGroup ρ →* Q) (g : J → K) (hg : Function.Injective g) :
    (∀ u : ((PresGroup ρ) × J) →₀ ℤ, bdry2 (univCover ρ) u = 0 →
        Finsupp.mapDomain (Prod.map (⇑Φ) g) u = 0) ↔
    (∀ v : J →₀ CoverRing (relSub ρ),
        (∀ i, ∑ j ∈ v.support, v j * foxMatrixPres ρ i j = 0) →
        Finsupp.mapDomain g
          (v.mapRange (MonoidAlgebra.mapDomainRingHom ℤ Φ) (map_zero _)) = 0) := by
  classical
  have hcycle : ∀ u : ((PresGroup ρ) × J) →₀ ℤ,
      bdry2 (univCover ρ) u = 0 ↔
      coverSecondBoundary _ ρ (fsCoords _ J u) = 0 := by
    intro u
    rw [fs_coverComplex_bdry2]
    exact (map_eq_zero_iff _ (fsCoords (relSub ρ) α).injective).symm
  constructor
  · intro H v hv
    let u := (fsCoords _ J).symm v
    have he : fsCoords _ J u = v := LinearEquiv.apply_symm_apply _ v
    have hc : bdry2 (univCover ρ) u = 0 := by
      rw [hcycle, he]
      apply Finsupp.ext
      simp_all [fs_coverSecondBoundary_apply, Finsupp.zero_apply]
    grind [fs_mapDomain_prodMap_eq_zero_iff Φ g hg, mapDomain_mapRange_eq_zero_iff Φ g hg]
  · intro H u hu
    have hc := (hcycle u).mp hu
    have hz := H (fsCoords _ J u) (fun i => by
      have hi := congrArg (· i) hc
      grind [fs_coverSecondBoundary_apply, Finsupp.zero_apply])
    rw [mapDomain_mapRange_eq_zero_iff Φ g hg] at hz
    exact (fs_mapDomain_prodMap_eq_zero_iff Φ g hg u).mpr hz
