module

public import RequestProject.PresWordEmbeddingUniversal
public import RequestProject.PresUniversalFoxKernelEquiv
public import RequestProject.OrderRealizationPi2Criterion
public import RequestProject.StrictOrderNormalizationMaps


@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.PresModel.PresWordEmbedding
open Comb
variable {α β J K : Type}
variable {w : J → List (α × Bool)} {v : K → List (β × Bool)}
  (h : PresWordEmbedding w v) (hw : ∀ j, 0 < (w j).length) (hv : ∀ k, 0 < (v k).length)

include hw hv in
/-- Dimension two removes all genuine three-boundaries in the universal
presentation model. Thus its actual pi2 map is zero exactly when the strict
universal two-cycle map is zero. -/
theorem killsPi2_iff_strict_cycles_zero :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩ ↔
      ∀ c : StrictOrdTri (UOrder _ (ptBase w)) →₀ ℤ,
        Comb.bdry2 (strictOrderCx (UOrder _ (ptBase w))) c = 0 →
          chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c = 0 := by
  erw [killsPi2_orderRealization_iff_universal_cycles_bound h.posMap h.posMap.monotone _
    (presPos_isConnected w (fun j => List.length_pos_iff.mp (hw j)))
    (presPos_isConnected v (fun j => List.length_pos_iff.mp (hv j)))]
  constructor
  · intro hz c hc
    have hi : Comb.bdry2 _
        (chain2 (strictOrderIncl _) c) = 0 := by
      rw [bdry2_chain2, hc, map_zero]
    obtain ⟨b, hb⟩ := hz _ hi
    have he := congrArg normalizeOrdChain2 hb
    erw [presPos_cover_normalized_three_boundary_zero,
      normalizeOrdChain2_strict_map h.universalMap h.universalMap_strictMono, (normalizeOrdChain2_inclusion c)] at he
    exact he.symm
  · intro hz c hc
    let d := chain2 (orderCxMap h.universalMap h.universalMap.monotone) c
    have hd : Comb.bdry2 _ d = 0 := by
      rw [bdry2_chain2, hc, map_zero]
    have hn : normalizeOrdChain2 d = 0 := by
      erw [normalizeOrdChain2_strict_map h.universalMap h.universalMap_strictMono]
      solve_by_elim [normalizeOrdChain2_cycle]
    have he := ordNormalization_cycle_boundary d hd
    erw [hn, map_zero, sub_zero] at he
    exact ⟨ordNormalizationHomotopy2 d, he.symm⟩

variable [DecidableEq α]
  (ρ : J → FreeGroup α) (σ : K → FreeGroup β)
  (hwm : ∀ j, FreeGroup.mk (w j) = ρ j) (hvm : ∀ k, FreeGroup.mk (v k) = σ k)

/-- The actual Fox-kernel equivalence has exactly the lifted-relator group
coordinates used by the naturality theorem. -/
theorem foxCycle_coordinates
    (c : LinearMap.ker (Comb.bdry2 _)) :
    groupCellChainEquiv.symm (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw c).val =
      presUniversalRelatorGroupChainEquiv ρ w hwm hw
        (presCoverRelatorChain w uOrderEnd (presUniversalEnd_isPosetCover w hw) hw c.val) := by
  erw [LinearEquiv.symm_apply_apply]; rfl

include hw hv in
/-- Exact naturality with the Fox boundary kernel. -/
theorem strict_cycles_zero_iff_fox :
    (∀ c : StrictOrdTri (UOrder _ (ptBase w)) →₀ ℤ,
      Comb.bdry2 (strictOrderCx (UOrder _ (ptBase w))) c = 0 →
        chain2 (strictOrderCxMap h.universalMap h.universalMap_strictMono) c = 0) ↔
    ∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell)
        (groupCellChainEquiv.symm z.val) = 0 := by
  constructor
  · intro hz z
    obtain ⟨c, rfl⟩ := (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw).surjective z
    erw [foxCycle_coordinates hw ρ hwm c,
      ← h.universalRelatorChain_group_map ρ σ hwm hvm hw hv,
      hz c.val c.property, map_zero, map_zero]
  · intro hz c hc
    apply presCoverRelatorChain_cycle_injective v uOrderEnd (presUniversalEnd_isPosetCover v hv)
      hv _ 0 (by rw [bdry2_chain2, hc, map_zero]) (map_zero _) _
    apply (presUniversalRelatorGroupChainEquiv σ v hvm hv).injective
    erw [map_zero, map_zero, h.universalRelatorChain_group_map]
    have he := hz (presUniversalTwoCycleFoxKernelEquiv ρ w hwm hw ⟨c, hc⟩)
    rwa [foxCycle_coordinates hw ρ hwm] at he

include hw hv in
/-- The genuine topological pi2-killing condition is precisely the algebraic
Fox-cycle condition for this labelled presentation inclusion. All comparison
maps and naturality statements in this equivalence have been proved. -/
theorem killsPi2_iff_fox :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap h.posMap h.posMap.monotone,
        (orderNerveRealizationMap h.posMap h.posMap.monotone).hom.continuous⟩ ↔
    ∀ z : LinearMap.ker ((coverSecondBoundary (relSub ρ) ρ).restrictScalars ℤ),
      Finsupp.mapDomain (Prod.map (h.groupHom ρ σ hwm hvm) h.cell)
        (groupCellChainEquiv.symm z.val) = 0 :=
  (h.killsPi2_iff_strict_cycles_zero hw hv).trans (h.strict_cycles_zero_iff_fox hw hv ρ σ hwm hvm)

end FiniteChains.PresModel.PresWordEmbedding
