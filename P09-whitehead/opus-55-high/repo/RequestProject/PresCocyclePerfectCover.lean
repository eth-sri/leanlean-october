import RequestProject.PresCocycleCoverFoxBoundary
import RequestProject.PresPosetGroupEquiv
import RequestProject.PresPosetConnected
import RequestProject.ConnectedCellularZeroFillings
import RequestProject.Tac


bwd

set_option maxHeartbeats 1600000

namespace FiniteChains.PresModel.PresCocycleCover
open Comb
universe u
variable {α J : Type u} (w : J → List (α × Bool))
  (N : Subgroup (FreeGroup α)) [N.Normal] (hword : ∀ j, FreeGroup.mk (w j) ∈ N)

theorem quotient_monodromy_alphaFree :
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)).comp
      (alphaFree w) = QuotientGroup.mk' N := by
  aesop

theorem quotient_monodromy_surjective : Function.Surjective
    ((Coc w (qof N) (quotient_relators_close w N hword)).monodromy (ptBase w)) := by
  intro g
  cases' QuotientGroup.mk'_surjective N g with x hx
  exact ⟨alphaFree w x, (DFunLike.congr_fun
    (quotient_monodromy_alphaFree w N hword) x).trans hx⟩

theorem quotient_isConnected (hpos : ∀ j, 0 < (w j).length) :
    IsConnected (orderCx (QuotientCover w N hword)) :=
  (Coc w _ (quotient_relators_close w N hword)).cover_isConnected _
    (presPos_isConnected w (by grind))
    (quotient_monodromy_surjective w N hword)

variable (ρ : J → FreeGroup α) (hw : ∀ j, FreeGroup.mk (w j) = ρ j)
  (hpos : ∀ j, 0 < (w j).length) (H : Subgroup (PresGroup ρ)) [H.Normal]

abbrev subgroupPreimage := H.comap (QuotientGroup.mk' _)

include hw in
omit [H.Normal] in
theorem subgroupPreimage_contains_relators (j : J) :
    FreeGroup.mk (w j) ∈ subgroupPreimage ρ H := by
  simp [hw j, (QuotientGroup.eq_one_iff _).mpr
    (Subgroup.subset_normalClosure (Set.mem_range_self j))]

abbrev SubgroupCover := QuotientCover w _
  (subgroupPreimage_contains_relators w ρ hw H)
abbrev subgroupCoc := Coc w _
  (quotient_relators_close w _
    (subgroupPreimage_contains_relators w ρ hw H))

include hpos in
/-- Reading identifies the actual monodromy kernel with the specified original subgroup. -/
theorem subgroup_monodromy_kernel_iff (z : Pi1 (orderCx (PresPos w)) (ptBase w)) :
    (subgroupCoc w ρ hw H).monodromy (ptBase w) z = 1 ↔ readingPresW ρ w hw z ∈ H := by
  obtain ⟨g, rfl⟩ := alphaHomW_surjective w ρ hw hpos z
  induction g using QuotientGroup.induction_on with
  | _ x =>
    rw [readingPresW_alphaHomW]
    simp [show (subgroupCoc w ρ hw H).monodromy _ (alphaFree w x) =
        QuotientGroup.mk x from DFunLike.congr_fun (quotient_monodromy_alphaFree w
          _ (subgroupPreimage_contains_relators w ρ hw H)) x]

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
        grind [show readingPresW ρ w hw z = g.val from readingPresW_alphaHomW ρ w hw g.val])
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    exact readingPresW_alphaHomW ρ w hw g.val

/-- Fundamental group of the genuine covering, with its original subgroup marking. -/
noncomputable def subgroupCoverPi1Equiv :
    Pi1 (orderCx (SubgroupCover w ρ hw H)) ((subgroupCoc w ρ hw H).coverBase (ptBase w)) ≃* H :=
  ((subgroupCoc w ρ hw H).coverPi1KernelEquiv _).trans
    (MulEquiv.ofBijective _
      (subgroupKernelHom_bijective w ρ hw hpos H))

include hpos in
theorem subgroupCover_pi1_perfect (hperf : ⁅H, H⁆ = H) :
    commutator (Pi1 (orderCx (SubgroupCover w ρ hw H))
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))) = ⊤ := by
  have hH : commutator H = ⊤ := by
    apply top_unique
    intro g _
    have hg : g.val ∈ (commutator H).map H.subtype := by
      simp [H.map_subtype_commutator, hperf]
    simp_all
  let e := (subgroupCoverPi1Equiv w ρ hw hpos H).symm
  have hr : e.toMonoidHom.range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have he := map_commutator_eq H e.toMonoidHom
  rwd [hH, Subgroup.map_top_of_surjective _ e.surjective, hr] at he
  exact he.symm

include hpos in
/-- Perfectness supplies genuine strict one-cycle fillings, with no finite-cell restriction. -/
theorem subgroupCover_one_cycle_filling (hperf : ⁅H, H⁆ = H)
    (c : StrictOrdEdge (SubgroupCover w ρ hw H) →₀ ℤ)
    (hc : Comb.bdry1 (strictOrderCx (SubgroupCover w ρ hw H)) c = 0) :
    ∃ d : StrictOrdTri (SubgroupCover w ρ hw H) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (SubgroupCover w ρ hw H)) d = c := by
  let C := SubgroupCover w ρ hw H
  have hweak : Comb.bdry1 _ (chain1 (strictOrderIncl C) c) = 0 := by
    rwd [bdry1_chain1, hc, map_zero]
  obtain ⟨d, hd⟩ := oneCycle_filling_of_perfect_pi1 (orderCx C)
    _
    (quotient_isConnected w _
      _ hpos)
    (subgroupCover_pi1_perfect w ρ hw hpos H hperf) _ hweak
  exact ⟨normalizeOrdChain2 d, by
    rwd [bdry2_normalizeOrdChain2, hd]
    exact normalizeOrdChain1_inclusion c⟩

variable [DecidableEq α]

include hpos in
/-- The specified perfect subgroup and finite-support Fox tests give a genuinely acyclic poset cover. -/
theorem subgroupCover_isAcyclic
    (hsat : ∀ v : J →₀ MonoidAlgebra ℤ (PresGroup ρ), FoxSat (foxMatrixPres ρ) v H)
    (hperf : ⁅H, H⁆ = H) : IsAcyclic (strictOrderCx (SubgroupCover w ρ hw H)) := by
  let N := subgroupPreimage ρ H
  have hR : relSub ρ ≤ N := by
    intro r hr
    change (QuotientGroup.mk r : PresGroup ρ) ∈ H
    simp [(QuotientGroup.eq_one_iff r).mpr hr]
  have hNeq : presSub ρ N = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hinj : Function.Injective (coverSecondBoundary N ρ) := by
    apply fs_injective_boundary_of_foxSat ρ N hR
    simp_all
  have hi : Function.Injective (coverSecondBoundary N (fun j => FreeGroup.mk (w j))) := by
    simp_all
  refine ⟨?_, subgroupCover_one_cycle_filling w ρ hw hpos H hperf, ?_⟩
  · apply (injective_iff_map_eq_zero _).mpr
    exact quotient_two_cycle_zero w N _ hpos hi
  · exact strict_order_zeroCycle_filling_of_connected (P := SubgroupCover w ρ hw H)
      ((subgroupCoc w ρ hw H).coverBase (ptBase w))
      (quotient_isConnected w N _ hpos)
