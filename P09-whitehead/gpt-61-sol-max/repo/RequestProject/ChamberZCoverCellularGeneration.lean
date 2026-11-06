import Mathlib.Tactic

import RequestProject.ChamberZCoverDegreeGeneration
import RequestProject.OrderNormalizationSupport

/-! Genuine finite cellular two-cycle generation in the actual covering poset. -/

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V}
  {X : Type u} [PartialOrder X] [Nonempty X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}
  {P : Type u} [PartialOrder P] {f : P → Zpos A X M att}

theorem exists_cover_base_cellular_cycle (hf : IsPosetCover f)
    (z : OrdTri P →₀ ℤ) (hz : Comb.bdry2 (orderCx P) z = 0) :
    ∃ c : OrdTri P →₀ ℤ,
      c ∈ Finsupp.supported ℤ ℤ (ordTriOn (fun p => InZBase (f p))) ∧
      Comb.bdry2 (orderCx P) c = 0 ∧
      ∃ y : OrdTet P →₀ ℤ, z = c + ordBoundary3 y := by
  obtain ⟨c₀, hc₀, y₀, hy₀, hdc₀, he₀⟩ := exists_cover_base_twoCycle hf
    (ordNerveChain2_mem_inc z) (ordNerveChain2_lengthProjection z)
    ((ordNerveChain2_cycle_iff z).mpr hz)
  let c := lengthProjection 3 c₀
  let y := lengthProjection 4 y₀
  have hc : c ∈ IncOn (fun p => InZBase (f p)) := lengthProjection_mem_incOn _ hc₀
  have hy : y ∈ Nerve.Inc P := lengthProjection_mem_inc _ hy₀
  have hdc : Nerve.bdry c = 0 := by
    dsimp only [c]
    rw [← lengthProjection_bdry, hdc₀, map_zero]
  have he : ordNerveChain2 z = c + Nerve.bdry y := by
    have h := congrArg (lengthProjection 3) he₀
    rw [ordNerveChain2_lengthProjection, map_add, lengthProjection_bdry] at h
    exact h
  have hec : ordNerveChain2 (decodeOrdNerve2 c) = c := by
    rw [ordNerveChain2_decode (incOn_le_inc _ hc)]
    exact lengthProjection_idempotent _ _
  have hey : ordNerveChain3 (decodeOrdNerve3 y) = y := by
    rw [ordNerveChain3_decode hy]
    exact lengthProjection_idempotent _ _
  refine ⟨decodeOrdNerve2 c, decodeOrdNerve2_supported hc, ?_, decodeOrdNerve3 y, ?_⟩
  · apply (ordNerveChain2_cycle_iff _).mp
    rw [hec, hdc]
  · apply ordNerveChain2_injective
    rw [map_add, hec, ordNerveChain2_ordBoundary3, hey]
    exact he

end FiniteChains.Davis
