
import proofs.HordijkSteelThreshold.FoodWordParents
import proofs.HordijkSteelThreshold.BinaryWordCode
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic




namespace HordijkSteelThreshold

/-- The actual finite word-graph vertex domain: one food root and only
nonfood words inside the ambient cap. No parity condition above N is needed. -/
abbrev BoundedFoodWord (L N : ℕ) :=
  {s : List Bool // s = [] ∨ L < s.length ∧ s.length ≤ N}

variable {L N : ℕ} (v : BoundedFoodWord L N)

theorem boundedFoodWord_length_le  :
    v.val.length ≤ N := by grind

instance boundedFoodWord_finite (L N : ℕ) : Finite (BoundedFoodWord L N) := (List.finite_length_le Bool N).subset fun s hs =>
    boundedFoodWord_length_le (⟨s, hs⟩)

noncomputable instance boundedFoodWord_fintype (L N : ℕ) : Fintype (BoundedFoodWord L N) :=
  Fintype.ofFinite _

def boundedFoodRoot (L N : ℕ) : BoundedFoodWord L N := ⟨[], Or.inl rfl⟩

def boundedFoodLeft  : BoundedFoodWord L N :=
  ⟨foodWordLeft L v.val, by grind [foodWordLeft]⟩

def boundedFoodRight  : BoundedFoodWord L N :=
  ⟨foodWordRight L v.val, by grind [foodWordRight]⟩

theorem boundedFoodParents_commute  :
    boundedFoodLeft (boundedFoodRight v) = boundedFoodRight (boundedFoodLeft v) := by
  
  grind [boundedFoodLeft, boundedFoodRight, foodWordLeft, foodWordRight]

/-- Label a vertex by parity along its right-parent path. Root edges carry
zero, so extra recursion depth does not alter the intended path parity. -/
def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) 
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

variable {V E : Type*}

/-- A cut in a finite graph with separately indexed edges, including parallel
edges. Its definition never identifies edges with equal endpoints. -/
def booleanEdgeCut  (edges : Finset E) (a b : E → V)
    (label : V → Bool)  := edges.filter fun e => label (a e) ≠ label (b e)

variable (active : Finset E) (a b : E → V)

abbrev indexedEdgeReach    :=
  Relation.EqvGen fun x y => ∃ e ∈ active, a e = x ∧ b e = y





/-- Any pair connected in the host but disconnected by the enabled edges
has a disabled separating bond. The conclusion gives global cut minimality,
which is what the diamond-potential argument requires. -/
theorem exists_disabled_separating_bond  [DecidableEq E]
    (edges active : Finset E) (a b : _) (x y : V)
    (hhost : indexedEdgeReach edges a b x y)
    (hxy : ¬ indexedEdgeReach active a b x y) :
    let cut := booleanEdgeCut edges a b
    ∃ f : _, f x ≠ f y ∧
      cut f ⊆ edges \ active ∧
      (cut f).Nonempty ∧
      ∀ g : _, (cut g).Nonempty →
        cut g ⊆ cut f →
        cut g = cut f := by
  classical
  let cut := booleanEdgeCut edges a b
  have hn : ∃ f : V → Bool, f x ≠ f y ∧
      cut f ⊆ edges \ active := by
       let f  := fun v => decide (indexedEdgeReach active a b x v)
       refine ⟨f, ?_, ?_⟩
       · have hx : indexedEdgeReach active a b x x := Relation.EqvGen.refl x
         simp [f, hx, hxy]
       · intro e he
         obtain ⟨heE, hdiff⟩ := Finset.mem_filter.mp he
         refine Finset.mem_sdiff.mpr ⟨heE, ?_⟩
         intro heA
         have hab : indexedEdgeReach active a b _ _ :=
           Relation.EqvGen.rel _ _ ⟨e, heA, rfl, rfl⟩
         exact hdiff (by simp [f, rel_congr_right (a := x) hab])

  obtain ⟨f, ⟨hf, hc⟩, hmin⟩ :=
    (measure (fun f : V → Bool => (cut f).card)).wf.has_min _ hn
  refine ⟨f, hf, hc, ?_, ?_⟩
  · by_contra hn
    apply hf
    exact Relation.EqvGen.eqvGen_le (r' := fun x y => f x = f y) (by
      rintro _ _ ⟨e, he, rfl, rfl⟩
      by_contra hd
      exact hn ⟨e, Finset.mem_filter.mpr ⟨he, hd⟩⟩) x y hhost
  · intro g hgne hgsub
    by_cases hsep : g x ≠ g y
    · exact Finset.eq_of_subset_of_card_le hgsub (Nat.le_of_not_gt (hmin g ⟨hsep, hgsub.trans hc⟩))
    · have heq : (cut fun v => f v ^^ g v) =
          cut f \ cut g := by
        ext e
        have hh := @hgsub e
        simp [cut, booleanEdgeCut] at hh ⊢
        grind [Bool.eq_false_or_eq_true (f (a e))]
      have hsmall := Finset.card_lt_card (Finset.sdiff_ssubset hgsub hgne)
      have hm := hmin (fun v => f v ^^ g v) ⟨(by simpa [not_ne_iff.mp hsep] using hf), (by
        rw [heq]
        exact Finset.sdiff_subset.trans hc)⟩
      change ¬(cut _).card < _ at hm
      rw [heq] at hm
      exact (hm hsmall).elim

variable (L N : ℕ)

abbrev WordBasicEdge  := BoundedFoodWord L N × Bool

noncomputable def wordBasicEdges  : Finset (WordBasicEdge L N) := by
  classical
  exact Finset.univ.filter fun e => e.1 ≠ boundedFoodRoot L N

def wordEdgeParent {L N : ℕ} (e : WordBasicEdge L N)  :=
  if e.2 then boundedFoodRight e.1 else boundedFoodLeft e.1

theorem wordGraph_reaches_root  (v : _) :
    indexedEdgeReach (wordBasicEdges L N) Prod.fst wordEdgeParent v (boundedFoodRoot L N) := by
  by_cases hr : v = boundedFoodRoot L N
  · rw [hr]
    exact Relation.EqvGen.refl _
  · exact _root_.trans
      (Relation.EqvGen.rel _ _ ⟨(v, true), by grind [wordBasicEdges], rfl, rfl⟩)
      (wordGraph_reaches_root (boundedFoodRight v))
termination_by v.val.length
decreasing_by grind [boundedFoodRight, foodWordRight, boundedFoodRoot]

abbrev wordGraph_connected  (u v : _)  :=
  _root_.trans (wordGraph_reaches_root L N u)
    (_root_.symm (wordGraph_reaches_root L N v))

noncomputable def wordGraphCut {L N : ℕ} (f : _)  := booleanEdgeCut (wordBasicEdges L N) Prod.fst wordEdgeParent f

end HordijkSteelThreshold
