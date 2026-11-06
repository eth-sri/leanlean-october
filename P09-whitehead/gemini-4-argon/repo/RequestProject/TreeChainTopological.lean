module

public import RequestProject.TreeUnivCoverIso
public import RequestProject.TreeChain

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb.SpanningTree

universe u

variable {X Y : Complex2.{u}} {TX : SpanningTree X} {TY : SpanningTree Y}
  {h : Hom X Y} (hiff : ∀ e : X.E, TY.isTree (h.onE e) ↔ TX.isTree e)

theorem uvQ_univLiftV {x₀ : X.V} (c : UV X x₀) :
    uvQ (T := TY) (univLiftV x₀ h c)
      = presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
          (treeRel_onF hiff) (uvQ (T := TX) c) := by
  induction c using UV.ind with
  | h p =>
      show QuotientGroup.mk (pathWord TY (mapPath h p.1)) = _
      rw [pathWord_mapPath hiff]; rfl

variable [DecidableEq (NonTree TX)] [DecidableEq (NonTree TY)]

theorem uvFace_univLiftF (hE : Function.Injective h.onE) {x₀ : X.V} (F : UF X x₀) :
    uvFace TY (univLiftF x₀ h F)
      = (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
          (treeRel TY) h.onF (treeRel_onF hiff)).onF (uvFace TX F) := by
  show ((uvQ (T := TY) (univLiftV x₀ h F.1.1), h.onF F.1.2) : (treeUniv TY).F)
    = Prod.map (presInclGroupHom (nonTreeIncl hiff) (treeRel TX) (treeRel TY) h.onF
        (treeRel_onF hiff)) h.onF (uvQ (T := TX) F.1.1, F.1.2)
  rw [uvQ_univLiftV hiff]; rfl

theorem chain2_treeUnivHom_square (hE : Function.Injective h.onE) {x₀ : X.V}
    (u : (uCover X x₀).F →₀ ℤ) :
    chain2 (treeUnivHom TY (h.onV x₀)) (chain2 (univLift X h x₀) u)
      = chain2 (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
          (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)) (chain2 (treeUnivHom TX x₀) u) := by
  show Finsupp.mapDomain (uvFace TY) (Finsupp.mapDomain (univLiftF x₀ h) u)
    = Finsupp.mapDomain (univCoverInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE)
        (treeRel TX) (treeRel TY) h.onF (treeRel_onF hiff)).onF (Finsupp.mapDomain (uvFace TX) u)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  exact congrArg (Finsupp.mapDomain · u) (funext (uvFace_univLiftF hiff hE))

theorem zeroPi2_presInclHom_of_zeroPi2 (hE : Function.Injective h.onE) (hzero : ZeroPi2 h) :
    ZeroPi2 (presInclHom (nonTreeIncl hiff) (nonTreeIncl_injective hiff hE) (treeRel TX)
      (treeRel TY) h.onF (treeRel_onF hiff)) := by
  refine (Comb.zeroPi2_presInclHom_iff (ρ := treeRel TX) (σ := treeRel TY) (nonTreeIncl hiff)
    (nonTreeIncl_injective hiff hE) h.onF (treeRel_onF hiff)).2 fun v hv => ?_
  obtain ⟨u, rfl⟩ := chain2_treeUnivHom_surjective TX (x₀ := TX.root) v
  rw [← chain2_treeUnivHom_square hiff hE u,
    hzero TX.root u ((mem_pi2_iff_bdry2_univCover TX u).2 hv), map_zero]
