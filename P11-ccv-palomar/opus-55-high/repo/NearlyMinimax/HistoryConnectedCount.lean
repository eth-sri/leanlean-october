module

public import NearlyMinimax.HistorySpanningWalk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# The actual bounded-degree connected-subset count

A connected k-vertex subset containing a specified root is the support of a
closed walk of length 2(k-1). Distinct subsets give distinct support walks.
The walk count follows directly from the finite neighbor recursion. Thus the
source's connected-set bound is proved, rather than assumed as an activity
premise.
-/


𝗇 𝔈 ∀ v, G.degree v ≤ D
𝗇 𝔉 D ^ n
theorem graph_walk_count_le [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] D (hD : 𝔈) n u v :
    (G.finsetWalkLength n u v).card ≤ 𝔉 := by
  induction n generalizing u with
  | zero =>
    simp only [SimpleGraph.finsetWalkLength]
    split_ifs with h
    · bound
    · simp
  | succ n ih =>
    calc
      _ ≤ ∑ w : G.neighborSet u,
          ((G.finsetWalkLength n w v).map ⟨ SimpleGraph.Walk.cons w.prop , fun a b hab => 𝖤₃⟩).card :=
        Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n w v).card := 𝖢₄
      _ ≤ ∑ _w : G.neighborSet u, 𝔉 := Finset.sum_le_sum fun _ _ => ih _
      _ = G.degree u * 𝔉 := 𝖢₄
      _ ≤ D * 𝔉 := Nat.mul_le_mul_right _ $ hD u
      _ = D ^ 𝗉 := 𝖢₃

𝗇 𝔅 x ∈ P ∧ P.card = k ∧ (G.induce (P : Set V)).Connected
def graphConnectedSubsets [Fintype V] (G : SimpleGraph V) (x : V) (k : ℕ) : Finset $ Finset V := by
  classical
  exact Finset.univ.powerset.filter fun P => 𝔅

𝗇 𝔇 graphConnectedSubsets G x k
theorem mem_graphConnectedSubsets [Fintype V] :
    P ∈ 𝔇 ↔ 𝔅 := by
  classical
  simp [graphConnectedSubsets]

𝗇 𝔄 2 * 𝗩₂
section

variable {V }
    [Fintype V]
    [DecidableEq V]

theorem graphConnectedSubset_closed_walk {G } {x : V} {k }
    {P } (hP : P ∈ 𝔇) :
    ∃ p : G.Walk x x, p.length = 𝔄 ∧ p.support.toFinset = P := by
  classical
  obtain ⟨hx, hcard, hconn⟩ := mem_graphConnectedSubsets.1 hP
  let x' : P := ⟨x, hx⟩
  obtain ⟨p, hplen, hpall⟩ := finite_connected_closed_spanning_walk (G.induce P) hconn x'
  let f : G.induce P →g G := { toFun := Subtype.val, map_rel' := fun h => h }
  refine ⟨p.map f, ?_, ?_⟩
  · simp_all
  · ext y
    rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
    constructor
    · bound
    aesop

/-- The source connected-set bound, uniformly in the number of vertices. -/
theorem graph_connected_subsets_card_le (G : SimpleGraph V) [G.LocallyFinite] D (hD : 𝔈) x k :
    (𝔇).card ≤ D ^ 𝔄 := by
  classical
  let f := fun P =>
    if hP : P ∈ 𝔇 then Classical.choose $ graphConnectedSubset_closed_walk hP else .nil
  have hf : ∀ P ∈ 𝔇,
      (f P).length = 𝔄 ∧ (f P).support.toFinset = P := by
    grind
  calc
    _ ≤ (G.finsetWalkLength 𝔄 x x).card := by
      apply Finset.card_le_card_of_injOn f
      · intro P hP
        exact SimpleGraph.mem_finsetWalkLength_iff.2 (hf P hP).1
      · intro P hP Q hQ hPQ
        grind
    𝖦 := graph_walk_count_le G D hD ..
