module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

/-!
# The tripartite graph and clique joined by a bridge

The vertices are three classes of size `s`, together with four clique vertices.
Only the vertices with zero coordinates are joined across the two components.
All forbidden copies mean injective graph homomorphisms, hence need not be induced.
-/

namespace KKP

/-- Vertices of the graph `K_{s,s,s}` joined to `K₄`. -/
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4

/-- The literal adjacency relation: tripartite edges, clique edges, and one bridge. -/
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
  | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The connected counterexample family, with a single bridge between its components. -/
def bridgeGraph (s : ℕ) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun v w => match v, w with
    | .inl (_, _), .inl (_, _) => fun h => Ne.symm h
    | .inr _, .inr _ => fun h => Ne.symm h
    | .inl (_, _), .inr _ => fun h => h
    | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun v => match v with
    | .inl (_, _) => fun h => h rfl
    | .inr _ => fun h => h rfl⟩

instance bridgeAdjDecidable (s : ℕ) : DecidableRel (bridgeGraph s).Adj :=
  fun v w => match v, w with
    | .inl (i, _), .inl (j, _) => inferInstanceAs (Decidable (i ≠ j))
    | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))
    | .inl (i, a), .inr b =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))
    | .inr b, .inl (i, a) =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))

/-- The forbidden graph `K₅` with just the edge between vertices 3 and 4 removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun i j h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun i h => h.1 rfl⟩

instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)))

/-- Every edge of the forbidden graph is in a triangle. -/
theorem forbidden_edge_triangle {i j : Fin 5} (h : forbiddenGraph.Adj i j) :
    ∃ k : Fin 5, forbiddenGraph.Adj i k ∧ forbiddenGraph.Adj j k := by
  revert i j
  decide +kernel

/-- For a positive class size, every vertex can reach clique vertex zero. -/
theorem bridgeGraph_connected (s : ℕ) (hs : 0 < s) : (bridgeGraph s).Connected := by
  let a : Fin s := ⟨0, hs⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable (bridgeGraph s)).mpr
  refine ⟨.inr 0, ?_⟩
  rintro (⟨i, b⟩ | b)
  · have hbridge : (bridgeGraph s).Reachable (.inr 0) (.inl (0, a)) :=
      SimpleGraph.Adj.reachable (by simp [bridgeGraph, bridgeAdj, a])
    by_cases hi : i = 0
    · subst i
      exact hbridge.trans ((SimpleGraph.Adj.reachable (by simp [bridgeGraph, bridgeAdj] :
        (bridgeGraph s).Adj (.inl (0, a)) (.inl (1, a)))).trans
          (SimpleGraph.Adj.reachable (by simp [bridgeGraph, bridgeAdj] :
            (bridgeGraph s).Adj (.inl (1, a)) (.inl (0, b)))))
    · exact hbridge.trans (SimpleGraph.Adj.reachable
        (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hi))
  · by_cases hb : b = 0
    · subst b; exact SimpleGraph.Reachable.rfl
    · exact SimpleGraph.Adj.reachable (by simpa [bridgeGraph, bridgeAdj] using Ne.symm hb)

/-- The first integer witness, equal to one on the tripartite component. -/
def witnessU (s : ℕ) : BridgeVertex s → ℝ
  | .inl _ => 1
  | .inr _ => 0

/-- The second integer witness, balanced on the first part and constant on the clique. -/
def witnessV (s : ℕ) : BridgeVertex s → ℝ
  | .inl (i, a) => if i.val = 0 then (if a.val = 0 then (s : ℝ) - 1 else -1) else 0
  | .inr _ => 3 * (s : ℝ)

/-- A triangle cannot cross the bridge. -/
theorem triangle_same_side {s : ℕ} {x y z : BridgeVertex s}
    (hxy : (bridgeGraph s).Adj x y) (hxz : (bridgeGraph s).Adj x z)
    (hyz : (bridgeGraph s).Adj y z) : x.isLeft = y.isLeft := by
  rcases x with ⟨i, a⟩ | b <;> rcases y with ⟨j, c⟩ | d <;> rcases z with ⟨k, e⟩ | f <;>
    simp_all [bridgeGraph, bridgeAdj]

/-- No injective, edge-preserving copy of `K₅−e` exists in the bridge graph. -/
theorem bridgeGraph_free (s : ℕ) : forbiddenGraph.Free (bridgeGraph s) := by
  classical
  rintro ⟨f⟩
  have hside (i : Fin 5) : (f i).isLeft = (f 0).isLeft := by
    by_cases hi : i = 0
    · subst i; rfl
    have ha : forbiddenGraph.Adj i 0 := by simp [forbiddenGraph, hi]
    obtain ⟨k, hik, h0k⟩ := forbidden_edge_triangle ha
    exact triangle_same_side (f.toHom.map_rel ha) (f.toHom.map_rel hik)
      (f.toHom.map_rel h0k)
  cases hf0 : f 0 with
  | inl p =>
    have hleft (i : Fin 5) : ∃ p : Fin 3 × Fin s, f i = .inl p := by
      have h := hside i
      cases hfi : f i <;> simp_all
    choose p hp using hleft
    let c : Fin 4 → Fin 3 := fun i => (p (i.castLE (by decide))).1
    have hc : Function.Injective c := by
      intro i j heq
      by_contra hne
      have hne' : i.castLE (show 4 ≤ 5 by decide) ≠ j.castLE (by decide) :=
        (Fin.castLE_injective _).ne hne
      have ha : forbiddenGraph.Adj (i.castLE (by decide)) (j.castLE (by decide)) := by
        simp only [forbiddenGraph]
        exact ⟨hne', by have hi := i.isLt; have hj := j.isLt; simp only [Fin.val_castLE]; omega⟩
      have h := f.toHom.map_rel ha
      change (bridgeGraph s).Adj (f _) (f _) at h
      rw [hp, hp] at h
      exact h heq
    have hcard := Fintype.card_le_of_injective c hc
    norm_num at hcard
  | inr b =>
    have hright (i : Fin 5) : ∃ b : Fin 4, f i = .inr b := by
      have h := hside i
      cases hfi : f i <;> simp_all
    choose c hc using hright
    have hinj : Function.Injective c := fun i j heq => f.injective (by
      change f i = f j
      rw [hc, hc, heq])
    have hcard := Fintype.card_le_of_injective c hinj
    norm_num at hcard

open Matrix

/-- The integer witnesses are perpendicular. -/
theorem witnesses_orthogonal (s : ℕ) (hs : 0 < s) :
    witnessU s ⬝ᵥ witnessV s = 0 := by
  cases s with
  | zero => omega
  | succ s =>
    simp [dotProduct, Fintype.sum_sum_type, witnessU, witnessV,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Squared norm of the first witness. -/
theorem witnessU_norm (s : ℕ) : witnessU s ⬝ᵥ witnessU s = 3 * (s : ℝ) := by
  simp [dotProduct, Fintype.sum_sum_type, witnessU, Fintype.card_prod]

/-- Squared norm of the second witness. -/
theorem witnessV_norm (s : ℕ) (hs : 0 < s) :
    witnessV s ⬝ᵥ witnessV s = (s : ℝ) * (37 * (s : ℝ) - 1) := by
  cases s with
  | zero => omega
  | succ s =>
    simp [dotProduct, Fintype.sum_sum_type, Fintype.sum_prod_type, witnessV, Fin.sum_univ_succ]
    ring

/-- A proper four-coloring of `K₅−e`. -/
def forbiddenColoring : forbiddenGraph.Coloring (Fin 4) :=
  .mk ![0, 1, 2, 3, 3] (by decide +kernel)

/-- Its chromatic number is exactly four, witnessed by a four-clique and a coloring. -/
theorem forbidden_chromaticNumber : forbiddenGraph.chromaticNumber = 4 := by
  apply le_antisymm (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenColoring⟩)
  apply SimpleGraph.le_chromaticNumber_of_pairwise_adj
    (ι := Fin 4) (by simp) (fun i => i.castLE (by decide))
  intro i j hij
  revert i j
  decide +kernel

/-- Deleting the core edge `{0,1}` permits a proper three-coloring. -/
def forbiddenDeletedColoring :
    (forbiddenGraph.deleteEdges {s(0, 1)}).Coloring (Fin 3) :=
  .mk ![0, 0, 1, 2, 2] (by decide +kernel)

/-- The forbidden graph is color-critical in the edge-deletion sense. -/
theorem forbidden_color_critical :
    ∃ i j : Fin 5, forbiddenGraph.Adj i j ∧
      (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber := by
  refine ⟨0, 1, by decide, ?_⟩
  rw [forbidden_chromaticNumber]
  exact lt_of_le_of_lt
    (SimpleGraph.Colorable.chromaticNumber_le ⟨forbiddenDeletedColoring⟩) (by norm_num)

end KKP
