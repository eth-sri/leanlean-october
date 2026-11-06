import RequestProject.OrderComparableCollapse
import RequestProject.Tac


/-! Finite strict three-chains witnessing a pointwise order homotopy. -/
bwd

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P]

theorem strict_cycle_comparable_boundary g h
    hg hh (hgh : ∀ x, g x ≤ h x)
    (c : StrictOrdTri P →₀ ℤ) (hc : bdry2 (strictOrderCx P) c = 0) :
    ∃ y : StrictOrdTet P →₀ ℤ,
      strictOrdBoundary3 y = normalizedStrictChain2 h hh c -
        normalizedStrictChain2 g hg c := by
  let w := chain2 (strictOrderIncl P) c
  have hw : bdry2 _ w = 0 := by
    rw [bdry2_chain2, hc, map_zero]
  let p := Nerve.prism g h (ordNerveChain2 w)
  have hp :=
    Nerve.prism_mem_inc hg hh hgh (ordNerveChain2_mem_inc w)
  have hd := (ordNerveChain2_cycle_iff w).mpr hw
  have hb : Nerve.bdry p = Nerve.cmap h (ordNerveChain2 w) -
      Nerve.cmap g (ordNerveChain2 w) := by
    simpa [p, hd] using Nerve.bdry_prism_add_prism_bdry g h (ordNerveChain2 w)
  let b := Nerve.lengthProjection 4 p
  have hbi : b ∈ Nerve.Inc P := Nerve.lengthProjection_mem_inc _ hp
  have hdeg : Nerve.lengthProjection 4 b = b := Nerve.lengthProjection_idempotent _ _
  have hy : ordBoundary3 (decodeOrdNerve3 b) =
      chain2 (orderCxMap h hh) w - chain2 (orderCxMap g hg) w := by
    apply ordNerveChain2_injective
    simp [ordNerveChain2_ordBoundary3, ordNerveChain3_decode hbi, hdeg, map_sub, b, ← Nerve.lengthProjection_bdry, hb, ← ordNerveChain2_chain2 h hh, ← ordNerveChain2_chain2 g hg, ordNerveChain2_lengthProjection]
  refine ⟨normalizeOrdChain3 (decodeOrdNerve3 b), ?_⟩
  have hn := congrArg normalizeOrdChain2 hy
  rwa [normalizeOrdChain2_ordBoundary3, map_sub] at hn

theorem normalizedStrictChain2_id (c : StrictOrdTri P →₀ ℤ) :
    normalizedStrictChain2 id monotone_id c = c := by
  induction c using Finsupp.induction_linear with
  | zero => rfl
  | add c d hc hd => simp_all
  | single t n =>
    rw [normalizedStrictChain2_single]
    simp [normalizeOrdTriangle, orderCxMap, strictOrderIncl, t.2.1, t.2.2]
