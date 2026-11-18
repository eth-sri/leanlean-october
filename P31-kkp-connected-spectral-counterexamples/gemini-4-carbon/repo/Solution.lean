module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

/-! # The connected counterexample family and its exact positive spectral gap -/

open Fintype

namespace BN
noncomputable section
variable {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The adjacency eigenvalues of a finite simple graph, indexed with algebraic
multiplicity by its vertex type. -/
def adjacencyEigenvalues := (G.isHermitian_adjMatrix ℝ).eigenvalues

/-- The adjacency eigenvalues in nonincreasing order. The value at `i` is the
paper's `λ_{i+1}(G)`. -/
def adjacencyEigenvalues₀ := (G.isHermitian_adjMatrix ℝ).eigenvalues₀

/-- The largest adjacency eigenvalue `λ₁(G)`. -/
def lambda1 [Nonempty V] := adjacencyEigenvalues₀ G ⟨0, card_pos⟩

/-- The second-largest adjacency eigenvalue `λ₂(G)`. -/
def lambda2 [Nontrivial V] := adjacencyEigenvalues₀ G ⟨1, one_lt_card⟩
end
end BN

namespace KKP

/-- Vertices of the graph `K_{s,s,s}` joined to `K₄`. -/
abbrev BridgeVertex (s) := Fin 3 × Fin s ⊕ Fin 4

/-- The literal adjacency relation: tripartite edges, clique edges, and one bridge. -/
def bridgeAdj (s) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0

/-- The connected counterexample family, with a single bridge between its components. -/
def bridgeGraph (s) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun
    | .inl (_, _), .inl (_, _) | .inr _, .inr _ => fun h => h.symm
    | .inl (_, _), .inr _ | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun | .inl (_, _) | .inr _ => fun h => h rfl⟩

instance bridgeAdjDecidable (s) : DecidableRel (bridgeGraph s).Adj
  | .inl (i, _), .inl (j, _) => inferInstanceAs (Decidable (i ≠ j))
  | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))
  | .inl (i, a), .inr b | .inr b, .inl (i, a) =>
    inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))

/-- The forbidden graph `K₅` with just the edge between vertices 3 and 4 removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

open Matrix WithLp SimpleGraph Finset Fin BN InnerProductSpace

local instance : DecidableRel forbiddenGraph.Adj :=
  by unfold forbiddenGraph; infer_instance

private lemma free_aux :
    ∀ {a v}, forbiddenGraph ≤ (bridgeGraph 1).comap (vecCons a v) →
      v 2 = v 3 ∧ (v 2).isRight := by unfold LE.le instLE; decide +kernel

attribute [local simp] bridgeGraph bridgeAdj dotProduct sum_sum_type sum_prod_type
  sum_univ_three sum_univ_four val_eq_zero_iff sum_add_distrib inner_add_right
  real_inner_smul_right vecTail lambda1 lambda2 adjacencyEigenvalues₀

/-- The complete graph, forbidden-subgraph, and ordered-spectrum certificate. -/
theorem connected_counterexample_family (s) (hs : 3 ≤ s) :
    forbiddenGraph.chromaticNumber = 4 ∧
      (∃ i j, forbiddenGraph.Adj i j ∧
        (forbiddenGraph.deleteEdges {s(i, j)}).chromaticNumber < forbiddenGraph.chromaticNumber) ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      #(bridgeGraph s).edgeFinset = 3 * s ^ 2 + 7 ∧
      (656 * ↑s ^ 2 - 1366 * ↑s + 62) / (3 * (37 * ↑s - 1) ^ 2) ≤
        lambda1 (bridgeGraph s) ^ 2 + lambda2 (bridgeGraph s) ^ 2 -
          4 / 3 * #(bridgeGraph s).edgeFinset ∧
      4 / 3 * #(bridgeGraph s).edgeFinset <
        lambda1 (bridgeGraph s) ^ 2 + lambda2 (bridgeGraph s) ^ 2 := by
  have : NeZero s := ⟨by omega⟩
  refine (and_iff_left_of_imp fun hchr => ⟨⟨0, 1, by decide, hchr ▸
    (Colorable.chromaticNumber_le (n := 3) ⟨⟨predAbove 0 ∘ predAbove 3, by decide⟩⟩).trans_lt
      (by decide)⟩, ?_, ?_, (and_iff_left_of_imp fun hm => ?_).2 ?_⟩).2
    (le_antisymm (Colorable.chromaticNumber_le ⟨⟨predAbove 3, by decide⟩⟩)
      (le_chromaticNumber_of_pairwise_adj (by simp) castSucc (by unfold Pairwise; decide)))
  · have r {u} (v) (h : (bridgeGraph s).Adj u v := by simp [*]) := h.reachable
    exact (connected_iff_exists_forall_reachable _).2 ⟨.inl (0, 0), fun
      | .inl (i, _) => if hi : i = 0 then .trans (r (.inl (1, 0))) (r _) else r _ (Ne.symm hi)
      | .inr b => .trans (r (.inr 0)) (if hb : 0 = b then hb ▸ .rfl else r _)⟩
  · rintro ⟨⟨f, hr⟩, hf⟩
    obtain ⟨hde, h⟩ := free_aux fun i j h => by
      rw [cons_head_tail (Sum.map (.map id 0) id ∘ f : _ → BridgeVertex 1)]; have := hr h
      cases h1 : f i <;> cases h2 : f j <;> simp_all
    cases h3 : f 3 <;> cases h4 : f 4 <;> simp_all
    cases hf (h3.trans h4.symm)
  · have : (3 : ℝ) ≤ s := mod_cast hs
    set d : ℝ := 37 * s - 1
    have : 0 < d := by linarith
    rw [hm, div_le_iff₀ (by positivity)]; push_cast
    refine (and_iff_left_of_imp fun h => by nlinarith).2 ?_
    let hA := (bridgeGraph s).isHermitian_adjMatrix ℝ
    let hT := isSymmetric_toEuclideanLin_iff.mpr hA
    let e := hT.eigenvectorBasis finrank_euclideanSpace
    let lam (k : Fin 2) := hA.eigenvalues₀ ⟨k, k.2.trans_le one_lt_card⟩
    let U : BridgeVertex s → ℝ := 1 ⊕ᵥ 0
    let W : BridgeVertex s → ℝ :=
      (fun (i, x) => if i = 0 then (if x = 0 then ↑s else 0) + -1 else 0) ⊕ᵥ 3 * s
    let u0 := ⟪e 0, toLp 2 U⟫_ℝ
    let w0 := ⟪e 0, toLp 2 W⟫_ℝ
    set B : ℝ := 114 * s - 6
    have hQ (k) (α β : ℝ) (hz : k ≠ 0 → α * u0 + β * w0 = 0) :
        0 ≤ 3 * (lam k - 2 * s) * α ^ 2 - 6 * α * β + (d * lam k - B) * β ^ 2 := by
      let z := α • U + β • W
      have hdot (w) : _ = z ⬝ᵥ w := e.sum_inner_mul_inner (toLp 2 w) (toLp 2 z)
      have hle : z ⬝ᵥ (bridgeGraph s).adjMatrix ℝ *ᵥ z ≤ lam k * z ⬝ᵥ z := by
        rw [← hdot, ← hdot, mul_sum]
        refine sum_le_sum fun i _ => ?_
        rcases lt_or_ge i.1 k with h | h
        · simp -zetaDelta [-bridgeGraph, show i = 0 from val_eq_zero_iff.1 <| by omega,
            z, u0, w0, hz (by omega)]
        · rw [← toLpLin_apply, hT, hT.apply_eigenvectorBasis,
            real_inner_smul_right, real_inner_comm (e i), mul_assoc]
          exact mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone h) (mul_self_nonneg _)
      rw [dotProduct_mulVec_adjMatrix] at hle
      simp +contextual -zetaDelta [z, U, W, add_mul, mul_add, ite_mul, mul_ite] at hle
      ring_nf at hle ⊢; nlinarith
    let X := d * lam 0
    let Y := d * lam 1
    let S := 2 * s * d + B
    suffices S ^ 2 - 2 * d * (2 * s * B - 3) ≤ X ^ 2 + Y ^ 2 by
      dsimp [S, X, Y, lam, d, B] at *; ring_nf at *; linarith
    by_cases h : S ≤ X
    · dsimp [S] at *; nlinarith [sq_nonneg Y, show 0 < ↑s * d by nlinarith]
    · have : 2 * ↑s ≤ lam 0 := by linarith [hQ 0 1 0 nofun]
      have : 0 < X - B := by dsimp [X]; nlinarith
      have : 3 ≤ (lam 0 - 2 * s) * (X - B) := by nlinarith [hQ 0 (X - B) 3 nofun]
      have := sq_nonneg (Y - (S - X)); dsimp [S, X, Y] at *
      suffices 2 * ↑s * d + B ≤ d * lam 0 + d * lam 1 by nlinarith
      by_cases h2 : 2 * ↑s ≤ lam 1
      · nlinarith
      · have hu := sq_pos_of_ne_zero fun h : u0 = 0 =>
          h2 (by linarith [hQ 1 1 0 fun _ => by linarith])
        nlinarith [hQ 1 w0 (-u0) fun _ => by ring,
          sq_nonneg ((2 * ↑s - lam 1) * w0 - u0),
          mul_pos (show 0 < lam 0 - lam 1 by linarith) hu]
  · apply Nat.mul_left_cancel zero_lt_two
    rw [two_mul_card_edgeFinset, card_filter]
    simp +contextual [-sum_boole]; ring

/-- Connected forbidden-free counterexamples occur above every prescribed edge threshold. -/
theorem unbounded_connected_counterexamples (B) :
    ∃ s, 3 ≤ s ∧ B ≤ #(bridgeGraph s).edgeFinset ∧
      (bridgeGraph s).Connected ∧ forbiddenGraph.Free (bridgeGraph s) ∧
      4 / 3 * #(bridgeGraph s).edgeFinset <
        lambda1 (bridgeGraph s) ^ 2 + lambda2 (bridgeGraph s) ^ 2 :=
  let ⟨_, _, hc, hf, hm, _, hex⟩ := connected_counterexample_family (B + 3) (by omega)
  ⟨_, by omega, hm ▸ by nlinarith, hc, hf, hex⟩

end KKP
