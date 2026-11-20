module
public import Mathlib
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
@[expose] public section

namespace KKP
open SimpleGraph Matrix

/-- Three parts of size `s`, together with four clique vertices. -/
abbrev BridgeVertex (s : ℕ) := (Fin 3 × Fin s) ⊕ Fin 4
/-- Tripartite adjacency, clique adjacency, and the unique zero-coordinate bridge. -/
def bridgeAdj (s : ℕ) : BridgeVertex s → BridgeVertex s → Prop
  | .inl (i, _), .inl (j, _) => i ≠ j
  | .inr a, .inr b => a ≠ b
  | .inl (i, a), .inr b | .inr b, .inl (i, a) => i.val = 0 ∧ a.val = 0 ∧ b.val = 0
/-- The literal simple graph in the counterexample family. -/
def bridgeGraph (s : ℕ) : SimpleGraph (BridgeVertex s) where
  Adj := bridgeAdj s
  symm := ⟨fun
    | .inl (_, _), .inl (_, _) | .inr _, .inr _ => fun h => Ne.symm h
    | .inl (_, _), .inr _ | .inr _, .inl (_, _) => fun h => h⟩
  loopless := ⟨fun
    | .inl (_, _) | .inr _ => fun h => h rfl⟩
instance bridgeAdjDecidable (s : ℕ) : DecidableRel (bridgeGraph s).Adj :=
  fun
    | .inl (i, _), .inl (j, _) => inferInstanceAs (Decidable (i ≠ j))
    | .inr a, .inr b => inferInstanceAs (Decidable (a ≠ b))
    | .inl (i, a), .inr b | .inr b, .inl (i, a) =>
      inferInstanceAs (Decidable (i.val = 0 ∧ a.val = 0 ∧ b.val = 0))
/-- The complete graph on five vertices with only the edge `{3,4}` removed. -/
def forbiddenGraph : SimpleGraph (Fin 5) where
  Adj i j := i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1, fun hji => h.2 ⟨hji.2, hji.1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
instance forbiddenAdjDecidable : DecidableRel forbiddenGraph.Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ ¬ (3 ≤ i.val ∧ 3 ≤ j.val)))

theorem bridgeGraph_connected {s : ℕ} (hs : 0 < s) : (bridgeGraph s).Connected := by
  let a : Fin s := ⟨0, hs⟩
  refine (connected_iff_exists_forall_reachable _).mpr ⟨.inr 0, ?_⟩
  rintro (⟨i, b⟩ | b)
  · refine (Adj.reachable (v := .inl (0, a)) ?_).trans ?_
    · exact ⟨rfl, rfl, rfl⟩
    fin_cases i
    · refine ⟨.cons (v := .inl (1, a)) ?_ (.cons ?_ .nil)⟩ <;> exact of_decide_eq_true rfl
    all_goals exact Adj.reachable (of_decide_eq_true rfl)
  · exact (preconnected_top 0 b).map ⟨Sum.inr, id⟩

/-- A triangle in the graph on singleton parts has at most one common
neighbor, and any such neighbor belongs to the clique. -/
private lemma triangle_common_neighbor :
    let A := (bridgeGraph 1).Adj
    ∀ a b, A a b → ∀ c, A a c → A b c → ∀ d, A a d → A b d → A c d →
      ∀ e, A a e → A b e → A c e → d = e ∧ d.isRight := by
  decide +kernel

theorem bridgeGraph_free (s : ℕ) : forbiddenGraph.Free (bridgeGraph s) := by
  rintro ⟨f⟩
  let p : bridgeGraph s →g bridgeGraph 1 := ⟨Sum.map (fun v => (v.1, 0)) id, by
    rintro (⟨i, a⟩ | a) (⟨j, b⟩ | b) <;> simp +contextual [bridgeGraph, bridgeAdj]⟩
  let q := p.comp f.toHom
  obtain ⟨he, hr⟩ : q 3 = q 4 ∧ (q 3).isRight := by
    apply triangle_common_neighbor (q 0) (q 1) _ (q 2)
    all_goals exact q.map_rel (by decide)
  apply f.injective.ne (by decide : (3 : Fin 5) ≠ 4)
  cases ha : f 3 <;> cases hb : f 4 <;> simp_all [p, q]

/-- The two unnormalized witness columns. The second is balanced on the
bridge's tripartite part and constant on the clique. -/
def witnesses (s : ℕ) : Matrix (BridgeVertex s) (Fin 2) ℝ
  | .inl (i, a), j => ![1, if i = 0 then (if a.val = 0 then (s : ℝ) - 1 else -1) else 0] j
  | .inr _, j => ![0, 3 * (s : ℝ)] j

/-- A test vector for the largest eigenvalue, supported on the tripartite side
and the clique's bridge endpoint. -/
def peakWitness (s : ℕ) : Matrix (BridgeVertex s) (Fin 1) ℝ
  | .inl _, _ => 2 * (s : ℝ)
  | .inr b, _ => if b = 0 then 1 else 0

lemma witness_forms {s : ℕ} (hs : 0 < s) :
    let x : ℝ := s
    let W := witnesses s
    let Z := peakWitness s
    let A := (bridgeGraph s).adjMatrix ℝ
    (bridgeGraph s).edgeFinset.card = 3 * s ^ 2 + 7 ∧
    Wᵀ * W = diagonal ![3 * x, x * (37 * x - 1)] ∧
    Wᵀ * A * W = !![6 * x ^ 2, 3 * x; 3 * x, x * (114 * x - 6)] ∧
    Zᵀ * Z = diagonal (fun _ => 12 * x ^ 3 + 1) ∧ Zᵀ * A * Z = !![24 * x ^ 4 + 4 * x] := by
  rcases s with _ | s
  · omega
  repeat' constructor
  all_goals first
    | rw [← Nat.mul_left_cancel_iff zero_lt_two, ← sum_degrees_eq_twice_card_edges]
      simp_rw [degree, neighborFinset_eq_filter, Finset.card_filter]
    | ext i j; fin_cases i <;> fin_cases j
  all_goals
    simp [peakWitness, witnesses, mul_apply, adjMatrix, bridgeGraph, bridgeAdj, Fintype.sum_sum_type,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.sum_add_distrib, -Finset.sum_boole] <;> ring

end KKP
