import Mathlib.Tactic

import RequestProject.OrderUniversalMap
import RequestProject.OrderRealizationCockcroft

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open TopologicalSingular
variable {P Q : Type} [PartialOrder P] [PartialOrder Q]

  (f : P → Q)
  (hf : Monotone f)
/-- The zero-map test on order H2 is exactly finite three-fillability of every
pushed-forward two-cycle. -/
theorem orderNerveH2Map_eq_zero_iff   :
    orderNerveH2Map f hf = 0 ↔
      ∀ (c : OrdTri P →₀ ℤ), bdry2 (orderCx P) c = 0 →
        ∃ b : OrdTet Q →₀ ℤ, ordBoundary3 b = chain2 (orderCxMap f hf) c := by
  constructor
  · intro hz c hc
    have h := congrArg (fun g : OrderNerveH2 P →ₗ[ℤ] OrderNerveH2 Q =>
      g (orderNerveH2Class P c hc)) hz
    rw  [orderNerveH2Map_class] at h
    exact (orderNerveH2Class_eq_zero_iff Q _ _).mp h
  · intro hb
    apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H c =>
      change orderNerveH2Map f hf (orderNerveH2Class P c.val c.property) = 0
      rw  [orderNerveH2Map_class]
      exact (orderNerveH2Class_eq_zero_iff Q _ _).mpr (hb c.val c.property)

/-- Exact bridge between actual topological pi2 and actual order homology on
the constructed universal covers. The lifting and Hurewicz comparisons are proved. -/
theorem killsPi2_orderRealization_iff_universalH2_zero
      (a : P)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
      orderNerveH2Map (uOrderMap f hf a) (uOrderMap f hf a).monotone = 0 := by
  letI := uOrderRealization_simplyConnected a
  letI := uOrderRealization_simplyConnected (f a)
  let F : C(orderNerveRealization P, orderNerveRealization Q) :=
    ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩
  let G : C(orderNerveRealization (UOrder P a), orderNerveRealization (UOrder Q (f a))) :=
    ⟨orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone,
      (orderNerveRealizationMap (uOrderMap f hf a) (uOrderMap f hf a).monotone).hom.continuous⟩
  have he : (uOrderRealizationProjection (f a)).comp G =
      F.comp (uOrderRealizationProjection a) := by
    apply ContinuousMap.ext
    exact uOrderMap_realization_projection f hf a
  have hk : Whitehead.KillsPi2 F ↔ Whitehead.KillsPi2 G := by
    grind [Whitehead.killsPi2_covering_precomp_iff, FiniteChains.Comb.uOrderRealizationProjection_isCoveringMap, FiniteChains.Comb.uOrderRealizationProjection_surjective, Whitehead.killsPi2_covering_postcomp_iff]
  change Whitehead.KillsPi2 F ↔ _
  rw  [hk, killsPi2_iff_singularH2_map_eq_zero
    (orderNerveRealizationVertex (P := UOrder P a) (UV.base (orderCx P) a)) G]
  exact ⟨orderH2Map_zero_of_orderNerveSingularH2Map_zero _ _,
    orderNerveSingularH2Map_zero_of_orderH2Map_zero _ _⟩

/-- A cycle-level criterion for the genuine pi2-killing condition in Challenge. -/
theorem killsPi2_orderRealization_iff_universal_cycles_bound
      (a : P)
    (hP : IsConnected (orderCx P)) (hQ : IsConnected (orderCx Q)) :
    Whitehead.KillsPi2
      ⟨orderNerveRealizationMap f hf, (orderNerveRealizationMap f hf).hom.continuous⟩ ↔
      ∀ (c : OrdTri (UOrder P a) →₀ ℤ), bdry2 (orderCx (UOrder P a)) c = 0 →
        ∃ b : OrdTet (UOrder Q (f a)) →₀ ℤ, ordBoundary3 b =
          chain2 (orderCxMap (uOrderMap f hf a) (uOrderMap f hf a).monotone) c := by
  rw  [killsPi2_orderRealization_iff_universalH2_zero f hf a hP hQ,
    orderNerveH2Map_eq_zero_iff]

end FiniteChains.Comb
