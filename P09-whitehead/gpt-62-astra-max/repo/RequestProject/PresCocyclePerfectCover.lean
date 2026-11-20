module

public import RequestProject.PresCocycleCoverFoxBoundary
public import RequestProject.PresPosetGroupEquiv
public import RequestProject.PresPosetConnected
public import RequestProject.ConnectedCellularZeroFillings

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal] (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

theorem quotient_monodromy_alphaFree :
    ((Coc w _ (quotient_relators_close w N hword)).monodromy _).comp
      (alphaFree w) = QuotientGroup.mk' N := by
  aesop

theorem quotient_monodromy_surjective : Function.Surjective
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)) := by
  intro g
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective N g
  exact ⟨alphaFree w x, (DFunLike.congr_fun
    (quotient_monodromy_alphaFree w N hword) x).trans hx⟩

theorem quotient_isConnected (hpos : ∀ j, 0 < (w j).length) :
    IsConnected (orderCx (QuotientCover w N hword)) :=
  (Coc w _ (quotient_relators_close w N hword)).cover_isConnected _
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hpos j)))
    (quotient_monodromy_surjective w N hword)

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
  (hpos : ∀ j, 0 < (w j).length) (H : Subgroup (PresGroup ρ)) [H.Normal]

abbrev subgroupPreimage := H.comap (QuotientGroup.mk' (relSub ρ))

include hw in
omit [H.Normal] in
theorem subgroupPreimage_contains_relators (j : J) :
    FreeGroup.mk (w j) ∈ subgroupPreimage ρ H := by
  change (QuotientGroup.mk _) ∈ H
  erw [hw j, (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure _)] <;> simp_all

abbrev SubgroupCover := QuotientCover w _
  (subgroupPreimage_contains_relators w ρ hw H)
abbrev subgroupCoc := Coc w _
  (quotient_relators_close w (subgroupPreimage ρ H)
    (subgroupPreimage_contains_relators w ρ hw H))

include hpos in
/-- Reading identifies the actual monodromy kernel with the specified original subgroup. -/
theorem subgroup_monodromy_kernel_iff (z : Pi1 _ _) :
    (subgroupCoc w ρ hw H).monodromy _ z = 1 ↔ readingPresW ρ w hw z ∈ H := by
  obtain ⟨g, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  induction g using QuotientGroup.induction_on with
  | _ x =>
    rw [readingPresW_alphaHomW]
    change (subgroupCoc w ρ hw H).monodromy _ (alphaFree w x) = 1 ↔ _
    rw [show (subgroupCoc w ρ hw H).monodromy _ _ =
        QuotientGroup.mk x from DFunLike.congr_fun (quotient_monodromy_alphaFree w
          _ (subgroupPreimage_contains_relators w ρ hw H)) x] <;> simp_all

def subgroupKernelHom :=
  ((readingPresW ρ w hw).comp
    ((subgroupCoc w ρ hw H).monodromy _).ker.subtype).codRestrict H (by
      intro z
      exact (subgroup_monodromy_kernel_iff w ρ hw hpos H z.val).mp z.property)

theorem subgroupKernelHom_bijective : Function.Bijective (subgroupKernelHom w ρ hw hpos H) := by
  constructor
  · intro z t he
    apply Subtype.ext
    exact readingPresW_injective w ρ hw hpos (congrArg Subtype.val he)
  · intro g
    let z := alphaHomW ρ w hw g.val
    have hz :=
      (subgroup_monodromy_kernel_iff w ρ hw hpos H z).mpr (by
        grind [readingPresW_alphaHomW])
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    apply readingPresW_alphaHomW <;> assumption

/-- Fundamental group of the genuine covering, with its original subgroup marking. -/
noncomputable def subgroupCoverPi1Equiv :=
  ((subgroupCoc w ρ hw H).coverPi1KernelEquiv _).trans
    (MulEquiv.ofBijective (subgroupKernelHom w ρ hw hpos H)
      (subgroupKernelHom_bijective w ρ hw hpos H))

section

variable (hperf : ⁅H, H⁆ = H)
include hperf

include hpos in
theorem subgroupCover_pi1_perfect :
    commutator (Pi1 (orderCx (SubgroupCover w ρ hw H))
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))) = ⊤ := by
  have hH : commutator H = ⊤ := by
    apply top_unique
    intro g _
    have hg : g.val ∈ (commutator H).map H.subtype := by
      erw [H.map_subtype_commutator, hperf]
      exact g.property
    simp_all
  let e := (subgroupCoverPi1Equiv w ρ hw hpos H).symm
  have he := map_commutator_eq H e.toMonoidHom
  erw [hH, Subgroup.map_top_of_surjective _ e.surjective, (MonoidHom.range_eq_top.mpr e.surjective), ← commutator_def] at he <;> simp_all

include hpos in
/-- Perfectness supplies genuine strict one-cycle fillings, with no finite-cell restriction. -/
theorem subgroupCover_one_cycle_filling
    (c : StrictOrdEdge (SubgroupCover w ρ hw H) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (SubgroupCover w ρ hw H)) c = 0) :
    ∃ d : StrictOrdTri (SubgroupCover w ρ hw H) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (SubgroupCover w ρ hw H)) d = c := by
  let C := SubgroupCover w ρ hw H
  have hweak : Comb.bdry1 _ (chain1 (strictOrderIncl C) c) = 0 := by
    rw [bdry1_chain1, hc, map_zero]
  obtain ⟨d, hd⟩ := oneCycle_filling_of_perfect_pi1 _
    _
    (quotient_isConnected w (subgroupPreimage ρ H)
      (subgroupPreimage_contains_relators w ρ hw H) hpos)
    (subgroupCover_pi1_perfect w ρ hw hpos H hperf) _ hweak
  exact ⟨normalizeOrdChain2 d, by
    erw [bdry2_normalizeOrdChain2, hd]
    exact normalizeOrdChain1_inclusion c⟩

end

variable [DecidableEq α]

include hpos in
/-- The specified perfect subgroup and finite-support Fox tests give a genuinely acyclic poset cover. -/
theorem subgroupCover_isAcyclic
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ _, FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) : IsAcyclic (strictOrderCx (SubgroupCover w ρ hw H)) := by
  let N := subgroupPreimage ρ H
  have hR : relSub ρ ≤ N := by
    intro r hr
    change (QuotientGroup.mk r) ∈ H
    erw [(QuotientGroup.eq_one_iff r).mpr hr] <;> simp_all
  have hNeq : presSub ρ N = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hinj : Function.Injective (coverSecondBoundary N ρ) := by
    apply fs_injective_boundary_of_foxSat ρ N hR
    simp_all
  have hi : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))) := by
    erw [(funext hw)]
    exact hinj
  refine ⟨?_, subgroupCover_one_cycle_filling w ρ hw hpos H hperf, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    apply quotient_two_cycle_zero <;> assumption
  · exact strict_order_zeroCycle_filling_of_connected (P := SubgroupCover w ρ hw H)
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))
      (quotient_isConnected w N (subgroupPreimage_contains_relators w ρ hw H) hpos)

end FiniteChains.PresModel.PresCocycleCover
