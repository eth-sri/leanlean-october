module
public import KKP.Graph
@[expose] public section

/-! # The connected counterexample family and its exact positive spectral gap -/

namespace KKP
/-- The complete graph, forbidden-subgraph, and ordered-spectrum certificate. -/
theorem connected_counterexample_family (s : ℕ) (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 ∧
      (656 * (s : ℝ) ^ 2 - 1366 * (s : ℝ) + 62) /
          (3 * (37 * (s : ℝ) - 1) ^ 2) ≤
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 -
          (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 :=
  ⟨forbidden_chromaticNumber, forbidden_color_critical, bridgeGraph_connected s (by omega),
    bridgeGraph_free s, bridgeGraph_edge_count s (by omega), bridgeGraph_spectral_gap s hs,
    bridgeGraph_spectral_excess s hs⟩

/-- The connected counterexamples have arbitrarily large edge counts. -/
theorem unbounded_connected_counterexamples (B : ℕ) :
    ∃ s : ℕ, 3 ≤ s ∧ B ≤ (bridgeGraph s).edgeFinset.card ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      (4 / 3 : ℝ) * ((bridgeGraph s).edgeFinset.card : ℝ) <
        BN.lambda1 (bridgeGraph s) ^ 2 + BN.lambda2 (bridgeGraph s) ^ 2 :=
  unbounded_counterexamples B
end KKP
