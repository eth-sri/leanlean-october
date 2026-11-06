import RequestProject.CellComplex
import RequestProject.StrictOrderChains
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
universe u

/-- Paths from a chosen vertex fill every augmented cellular zero-cycle. -/
theorem zeroCycle_filling_of_connected X (a : X.V)
    (hX : IsConnected X) c (hc : augC X c = 0) :
    ∃ b, bdry1 X b = c := by
  classical
  choose p hp using hX a
  let s :=
    Finsupp.linearCombination ℤ (fun v => pathChain (p v))
  have hs (z : X.V →₀ ℤ) : bdry1 X (s z) = z - augC X z • Finsupp.single a 1 := by
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z t hz ht =>
      rw [map_add, map_add, hz, ht, map_add, add_smul]
      abel
    | single v n =>
      rw [Finsupp.linearCombination_single, map_smul, bdry1_pathChain_of_isPath (hp v),
        augC_single, smul_sub]
      simp
  exact ⟨s c, by simp_all⟩

/-- Normalizing a weak edge filling gives the required strict cellular filling. -/
theorem strict_order_zeroCycle_filling_of_connected {P} [PartialOrder P]
    (a : P) (hP : IsConnected (orderCx P)) (c : P →₀ ℤ)
    (hc : augC (strictOrderCx P) c = 0) :
    ∃ b : StrictOrdEdge P →₀ ℤ, bdry1 (strictOrderCx P) b = c := by
  cases' zeroCycle_filling_of_connected _ a hP c hc with b hb
  exact ⟨normalizeOrdChain1 b, by rw [bdry1_normalizeOrdChain1, hb]⟩
