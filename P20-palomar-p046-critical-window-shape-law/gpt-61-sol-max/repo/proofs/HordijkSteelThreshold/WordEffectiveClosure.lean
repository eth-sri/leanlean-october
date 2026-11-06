import proofs.RAFCriticalWindowQuantitative.ComputableParameters

import proofs.RAFCriticalWindowQuantitative.FiniteClosure
import proofs.HordijkSteelThreshold.WordContourProbability
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import proofs.HordijkSteelThreshold.WordParentFibers
import proofs.HordijkSteelThreshold.WordGraphCuts
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov




namespace HordijkSteelThreshold


variable {L N M w : ℕ}
variable (f : BoundedFoodWord L N → Bool) (hL : 2*w ≤ L)
def shortBinaryWords : ℕ → Finset (List Bool)
  | 0 => {[]}
  | k + 1 => insert [] (Finset.univ.biUnion
      (fun b => (shortBinaryWords k).image (List.cons b)))

theorem mem_shortBinaryWords (s : List Bool) (k : ℕ) :
    s ∈ shortBinaryWords k ↔ s.length ≤ k := by
  induction k generalizing s <;> cases s <;> grind [shortBinaryWords]

theorem shortBinaryWords_card (N : ℕ) : (shortBinaryWords N).card + 1 = 2 ^ (N + 1) := by
  induction N with
  | zero => simp [shortBinaryWords]
  | succ N ih =>
    simp_all [shortBinaryWords, Finset.card_image_of_injective, List.cons_injective,
      Finset.disjoint_left, Disjoint.symm]; grind

/-- A deliberately loose core envelope; counting both paddings separately removes
dependence on the length of the core and on the ambient molecular universe. -/
def coreWordEnvelope (core : List Bool) (k : ℕ)  :=
  (shortBinaryWords k ×ˢ shortBinaryWords k).image fun lr => lr.1 ++ core ++ lr.2



def quadParity (f : Fin 4 → Bool)  := (f 0 ^^ f 1 ^^ f 2) ^^ f 3





def wordDiamondSlot  (v : BoundedFoodWord L N)  :=
  ![(v, false), (v, true), (boundedFoodRight v, false), (boundedFoodLeft v, true)]

noncomputable def wordEdgeIndicator  (F : Finset _)
    (e : WordBasicEdge L N)  := decide (e ∈ F)

theorem wordParents_root (L N : ℕ) :
    boundedFoodLeft (boundedFoodRoot L N) = boundedFoodRoot L N ∧
    boundedFoodRight (boundedFoodRoot L N) = boundedFoodRoot L N := by tauto


theorem wordCut_indicator  
    (e : _) :
    wordEdgeIndicator (wordGraphCut f) e = (f e.1 ^^ f (wordEdgeParent e)) := by
  apply Bool.eq_iff_iff.mpr
  by_cases hr : e.1 = boundedFoodRoot L N <;>
    simp [wordEdgeIndicator, wordGraphCut, booleanEdgeCut, wordBasicEdges,
      wordEdgeParent, hr, wordParents_root]

/-- Sharing a diamond transfers ambient cut parity, hence a closed subset
of a word cut is itself a word cut. -/
theorem wordDiamond_closed_subset_cut  
    (F : _) (hsub : F ⊆ wordGraphCut f)
    (hclosed : ∀ v i j, wordDiamondSlot v i ∈ F →
      wordDiamondSlot v j ∈ wordGraphCut f → wordDiamondSlot v j ∈ F) :
    ∃ g : _, wordGraphCut g = F := by
  let le := fun v => wordEdgeIndicator F (v, false)
  let re := fun v => wordEdgeIndicator F (v, true)
  let g := diamondPotential boundedFoodRight re
  refine ⟨g N, ?_⟩
  ext e
  have hpar (v : BoundedFoodWord L N) :
      (((le v ^^ re v) ^^ le (boundedFoodRight v)) ^^ re (boundedFoodLeft v)) = false := by
    change quadParity (fun i => wordEdgeIndicator F (wordDiamondSlot v i)) = false
    by_cases h : ∃ i, wordDiamondSlot v i ∈ F
    · obtain ⟨i, hi⟩ := h
      have he (j : _) : wordEdgeIndicator F (wordDiamondSlot v j) =
          wordEdgeIndicator (wordGraphCut f) (wordDiamondSlot v j) := by
        simp only [wordEdgeIndicator, decide_eq_decide]
        exact ⟨fun h => hsub h, hclosed v i j hi⟩
      simp_rw [he]
      simp [quadParity, wordCut_indicator, wordDiamondSlot, wordEdgeParent,
        boundedFoodParents_commute, Bool.xor_left_comm]
    · simp_all [quadParity, wordEdgeIndicator]
  have hbasic := hsub.trans (Finset.filter_subset _ _)
  have hn (b : Bool) : (boundedFoodRoot L N, b) ∉ F := by
    intro h
    have := hbasic h
    simp [wordBasicEdges] at this
  have hp (k : ℕ) (v : BoundedFoodWord L N) (hv : v.val.length ≤ k) :
      ((g k v ^^ g k (boundedFoodLeft v)) = le v) ∧
      ((g k v ^^ g k (boundedFoodRight v)) = re v) := by
    induction k generalizing v with
    | zero =>
      have he : v = boundedFoodRoot L N := Subtype.ext (List.length_eq_zero_iff.mp (by omega))
      simp [g, diamondPotential, he, le, re, wordEdgeIndicator, hn]
    | succ k ih =>
      obtain ⟨hil, hir⟩ := ih (boundedFoodRight v)
        (by
          simp only [boundedFoodRight, foodWordRight]
          split <;> simp only [List.length_nil, List.length_dropLast] <;> omega)
      have hd := hpar v
      simp only [g, diamondPotential]
      rw [← boundedFoodParents_commute v]
      constructor
      · apply Bool.xor_left_inj (z := le v).mp
        simpa [← hil, Bool.xor_assoc, Bool.xor_left_comm, Bool.xor_comm] using hd
      · rw [← hir]
        simp [g]
  have hp := hp N e.1 (boundedFoodWord_length_le _)
  have he : (g N e.1 ^^ g N (wordEdgeParent e)) = wordEdgeIndicator F e := by
    rcases e with ⟨v, b⟩
    cases b
    · exact hp.1
    · exact hp.2
  have hi := wordCut_indicator (g N) e
  rw [he] at hi
  simpa only [wordEdgeIndicator, decide_eq_decide] using hi


open Classical


/-- Two indexed edges share a finite diamond; loops are harmless for reachability. -/
def wordDiamondAdjacent  (e d : WordBasicEdge L N)  :=
  ∃ v i j, wordDiamondSlot v i = e ∧ wordDiamondSlot v j = d

def wordContourReach  (C : Finset (WordBasicEdge L N)) :=
  Relation.EqvGen fun e d => e ∈ C ∧ d ∈ C ∧ wordDiamondAdjacent e d


section
open SimpleGraph

variable (L N : ℕ)

def wordContourGraph  : SimpleGraph (WordBasicEdge L N) where
  Adj e d := e ∈ wordBasicEdges L N ∧ d ∈ wordBasicEdges L N ∧
    e ≠ d ∧ wordDiamondAdjacent e d
  symm := ⟨by grind [wordDiamondAdjacent]⟩
  loopless := ⟨by tauto⟩




set_option maxHeartbeats 800000 in
theorem wordContour_tour {L N : ℕ} (C : _)
    (hsub : C ⊆ wordBasicEdges L N) (r : _) (hr : r ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C r d) :
    ∃ p : (wordContourGraph L N).Walk r r,
      p.support.toFinset = C ∧ p.length = 2*(C.card-1) := by
  have hcross (S : _) (hs : S ⊆ C) (hr : r ∈ S) (hne : S ≠ C) :
      ∃ u ∈ S, ∃ v ∈ C, v ∉ S ∧ (wordContourGraph L N).Adj u v := by
    by_contra h
    have inv : ∀ u v, wordContourReach C u v → _ :=
      Relation.EqvGen.eqvGen_le (r' := fun u v => u ∈ S ↔ v ∈ S) (by
        rintro u v ⟨hu, hv, w, i, j, hi, hj⟩
        have huv : wordDiamondAdjacent u v := ⟨w,i,j,hi,hj⟩
        have hvu : wordDiamondAdjacent v u := ⟨w,j,i,hj,hi⟩
        grind [wordContourGraph])
    exact hne (Finset.Subset.antisymm hs fun d hd => (inv r d (hconn d hd)).mp hr)
  clear hconn hsub
  generalize wordContourGraph L N = G at *
  let rec extend (p : G.Walk r r) (hp : p.support.toFinset ⊆ C)
      (hl : p.length = 2 * (p.support.toFinset.card - 1)) :
      ∃ q : G.Walk r r, q.support.toFinset = C ∧ q.length = 2 * (C.card - 1) := by
    by_cases he : p.support.toFinset = C
    · measurability
    have hrp := List.mem_toFinset.mpr p.start_mem_support
    obtain ⟨u, hu, v, hv, hvs, huv⟩ := hcross _ hp hrp he
    let hu := List.mem_toFinset.mp hu
    let z0 := p.takeUntil u hu
    let q := z0.append
      ((Walk.cons huv (Walk.cons huv.symm Walk.nil)).append (p.dropUntil u hu))
    have hql : q.length = p.length + 2 := by
      have h := congrArg Walk.length (p.take_spec hu)
      simp only [Walk.length_append] at h
      simp_all +arith +zetaDelta
    have hqs : q.support.toFinset = insert v p.support.toFinset := by
      ext x
      have h : x ∈ p.support ↔ x ∈ z0.support ∨ x ∈ (p.dropUntil u hu).support := by
        conv_lhs => rw [← p.take_spec hu]
        exact Walk.mem_support_append_iff _ _
      clear * - h
      measurability
    have hqsub : q.support.toFinset ⊆ C := by
      rw [hqs]
      exact Finset.insert_subset hv hp
    have hc : q.support.toFinset.card = p.support.toFinset.card + 1 := by simp_all
    have hpos := Finset.card_pos.mpr ⟨r, hrp⟩
    exact extend q hqsub (by omega)
  termination_by C.card - p.support.toFinset.card
  decreasing_by
    change C.card - q.support.toFinset.card < C.card - p.support.toFinset.card
    have := Finset.card_le_card hqsub
    omega

  exact extend Walk.nil (by simpa using hr) (by simp)

variable (r : WordBasicEdge L N) (b : ℕ)

noncomputable def wordAnchoredContours   :=
  (wordBasicEdges L N).powerset.filter fun C => C.card = b ∧ r ∈ C ∧
    ∀ d ∈ C, wordContourReach C r d

/-- Literal indexed-edge contour count, uniform in the ambient word cap. -/
theorem wordAnchoredContours_card   :
    (wordAnchoredContours L N r b).card ≤ 81 ^ (b - 1)  := by
  let G := wordContourGraph L N
  have hd : ∀ e, (G.neighborFinset e).card ≤ 9 := by
    intro e
    let wordDiamondIncidence := Finset.univ.filter fun v : BoundedFoodWord L N =>
      ∃ i, wordDiamondSlot v i = e
    let wordDiamondEdges (v : BoundedFoodWord L N) := Finset.univ.image (wordDiamondSlot v)
    let wordDiamondNeighbors := wordDiamondIncidence.biUnion fun v => (wordDiamondEdges v).erase e
    by_cases he : e ∈ wordBasicEdges L N
    · 
      exact (Finset.card_le_card (by
                                   intro d hd
                                   obtain ⟨_, _, hn, ha⟩ := (mem_neighborFinset _ _ _).mp hd
                                   show d ∈ wordDiamondNeighbors
                                   simp [wordDiamondNeighbors, wordDiamondIncidence, wordDiamondEdges]
                                   grind [wordDiamondAdjacent])).trans ((by
                                                                                                      have hn := by simpa [wordBasicEdges] using he
                                                                                                      have hs : wordDiamondIncidence ⊆
                                                                                                          insert e.1 (Finset.univ.filter fun v => wordEdgeParent (v,!e.2) = e.1) := by
                                                                                                        intro v hv
                                                                                                        have h := (Finset.mem_filter.mp hv).2
                                                                                                        cases hb : e.2 <;> simp_all [Fin.exists_fin_succ, wordDiamondSlot, wordEdgeParent] <;> grind
                                                                                                      have hcard := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
                                                                                                      have hf := boundedFoodParent_fiber_card e.1 hn !e.2

                                                                                                      refine (Finset.card_biUnion_le_card_mul _ _ 3 ?_).trans ?_
                                                                                                      · intro v hv
                                                                                                        obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hv).2
                                                                                                        have hm : e ∈ wordDiamondEdges v := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
                                                                                                        have hc : (wordDiamondEdges v).card ≤ 4 := Finset.card_image_le.trans (by decide)
                                                                                                        rw [Finset.card_erase_of_mem hm]
                                                                                                        omega
                                                                                                      · omega))
    · have hz : (wordContourGraph L N).neighborFinset e = ∅ := by
        ext d
        simp only [Finset.notMem_empty, iff_false]
        intro hd
        exact he ((mem_neighborFinset _ _ _).mp hd).1
      simp_all [G]
  have hw (n : ℕ) (u v : WordBasicEdge L N) : (G.finsetWalkLength n u v).card ≤ 9^n := by
    induction n generalizing u v with
    | zero =>
      simp [finsetWalkLength]
      split
      · subst v; simp
      · simp
    | succ n ih =>
      refine (Finset.card_biUnion_le_card_mul _ _ (9^n) ?_).trans ?_
      · intro w _
        simpa using ih w v
      · simpa [pow_succ', SimpleGraph.neighborFinset] using
          Nat.mul_le_mul_right (9^n) (hd u)

  change _ ≤ (9^2)^(b-1)
  rw [← pow_mul]
  exact (Finset.card_le_card (by
    intro C hC
    obtain ⟨hpow, hb, hr, hc⟩ := Finset.mem_filter.mp hC
    obtain ⟨p, hp, hl⟩ := wordContour_tour C (Finset.mem_powerset.mp hpow) r hr hc
    exact Finset.mem_image.mpr ⟨p, mem_finsetWalkLength_iff.mpr (by omega), hp⟩)).trans
      (Finset.card_image_le.trans (hw _ r r))
end

open SimpleGraph

/-- End insertion/deletion on uncontracted words, including the empty word. -/
def endWordGraph : SimpleGraph (List Bool) where
  Adj u v := ∃ b : Bool, v = b :: u ∨ u = b :: v ∨
    v = u ++ [b] ∨ u = v ++ [b]
  symm := ⟨by aesop⟩
  loopless := ⟨by simp_all⟩


/-- A slot belonging to an actual edge is at most one end edit from its diamond product.
The actual-edge premise prevents a contracted-root jump. -/
theorem wordDiamondSlot_product_walk  (v : _) (i : Fin 4)
    (he : wordDiamondSlot v i ∈ wordBasicEdges L N) :
    ∃ p : endWordGraph.Walk (wordDiamondSlot v i).1.val v.val, p.length ≤ 1 := by
  fin_cases i
  · tauto
  · tauto
  · 
    obtain ⟨b, hb⟩ := boundedFoodParent_preimage v (boundedFoodRight v) true (by
                                                                         simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    
    exact ⟨Walk.cons ⟨b, Or.inr (Or.inr (Or.inl hb))⟩ Walk.nil, Nat.le_refl _⟩
  · 
    obtain ⟨b, hb⟩ := boundedFoodParent_preimage v (boundedFoodLeft v) false (by
                                                                       simpa [wordBasicEdges, wordDiamondSlot] using he) rfl
    
    exact ⟨Walk.cons ⟨b, Or.inl hb⟩ Walk.nil, Nat.le_refl _⟩

/-- Lift a contour walk to literal end edits, paying at most two per diamond step. -/
theorem wordContour_walk_lift  {e d : _}
    (p : (wordContourGraph L N).Walk e d) :
    ∃ q : endWordGraph.Walk e.1.val d.1.val, q.length ≤ 2 * p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, by simp⟩
  | @cons u v w huv p ih =>
    obtain ⟨a,i,j,rfl,rfl⟩ := huv.2.2.2
    obtain ⟨q,hq⟩ := wordDiamondSlot_product_walk a i huv.1
    obtain ⟨t,ht⟩ := wordDiamondSlot_product_walk a j huv.2.1
    obtain ⟨s,hs⟩ := ih
    refine ⟨(q.append t.reverse).append s, ?_⟩
    simp
    omega


def actualBinaryWords (N : ℕ)  := (shortBinaryWords N).erase []

theorem mem_actualBinaryWords (s : List Bool) (N : ℕ) :
    s ∈ actualBinaryWords N ↔ s ≠ [] ∧ s.length ≤ N := by
  simp [actualBinaryWords, mem_shortBinaryWords]

theorem actualBinaryWords_card (N : ℕ) : (actualBinaryWords N).card = 2 ^ (N + 1) - 2 := by
  have h := shortBinaryWords_card N
  grind [actualBinaryWords, mem_shortBinaryWords]





theorem endWord_strip_padding (l core r : List Bool) :
    ∃ p : endWordGraph.Walk (l ++ core ++ r) core, p.length = l.length + r.length := by
  induction l with
  | nil =>
    simp only [List.nil_append, List.length_nil, zero_add]
    induction r using List.reverseRecOn with
    | nil => simp
    | append_singleton r b ih =>
      obtain ⟨p,hp⟩ := ih
      rw [← List.append_assoc]
      exact ⟨Walk.cons ⟨b, Or.inr (Or.inr (Or.inr rfl))⟩ p, by change p.length + 1 = _; simp [hp]⟩
  | cons b l ih =>
    obtain ⟨p,hp⟩ := ih
    exact ⟨Walk.cons ⟨b, Or.inr (Or.inl rfl)⟩ p, by change p.length + 1 = _; simp [hp]; omega⟩

/-- Explicit path through a common core, with an exact cancellation-free length identity. -/
theorem endWord_common_core_walk (u v core : List Bool)
    (hu : ∃ l r : List Bool, u = l ++ core ++ r)
    (hv : ∃ l r : List Bool, v = l ++ core ++ r) :
    ∃ p : endWordGraph.Walk u v, p.length + 2 * core.length = u.length + v.length := by
  obtain ⟨l, r, rfl⟩ := hu
  obtain ⟨a, b, rfl⟩ := hv
  obtain ⟨p, hp⟩ := endWord_strip_padding l core r
  obtain ⟨q, hq⟩ := endWord_strip_padding a core b
  refine ⟨p.append q.reverse, ?_⟩
  simp
  omega

theorem endWord_walk_length_bound {u v : List Bool} (p : endWordGraph.Walk u v) :
    v.length ≤ u.length + p.length := by
  induction p with
  | nil => simp
  | @cons u v w ha p ih =>
    have hv : v.length ≤ u.length + 1 := by grind [HordijkSteelThreshold.endWordGraph]
    simp_all ; omega


/-- A central word with padding at least the walk length cannot be erased by end edits. -/
theorem endWord_walk_protects_core {u v : List Bool} (p : endWordGraph.Walk u v)
    (core left right : List Bool) (hu : u = left ++ core ++ right)
    (hl : p.length ≤ left.length) (hr : p.length ≤ right.length) :
    ∃ l r : List Bool, v = l ++ core ++ r := by
  induction p generalizing left right with
  | nil => exact ⟨left, right, hu⟩
  | @cons u v w ha p ih =>
    simp only [Walk.length_cons] at hl hr
    obtain ⟨b, h | h | h | h⟩ := ha
    · refine ih (b :: left) right ?_ ?_ (by omega)
      · simp_all
      · simp_all; omega
    · cases left with
      | nil => simp_all
      | cons c t =>
        have hv := congrArg List.tail h
        simp [hu] at hv
        refine ih t right (by simpa using hv.symm) ?_ (by omega)
        simp at hl
        omega
    · refine ih left (right ++ [b]) ?_ (by omega) ?_
      · simp_all
      · simp_all; omega
    · have hn : right ≠ [] := by intro he; simp_all
      have hv := congrArg List.dropLast h
      rw [hu, (List.dropLast_append_getLast hn).symm] at hv
      simp [← List.append_assoc] at hv
      refine ih left right.dropLast hv.symm (by omega) ?_
      simp_all
      omega




section
variable (core : List Bool) (hc : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r) (v : BoundedFoodWord L N)

include hc in
/-- A word avoiding the core of every boundary product lies on the food side.
Right truncation cannot cross such a boundary before reaching food. -/
theorem wordCut_core_avoiding_root (v : BoundedFoodWord L N)
    (hv : ¬ ∃ l r : List Bool, v.val = l ++ core ++ r) :
    f v = f (boundedFoodRoot L N) := by
  by_cases hr : v = boundedFoodRoot L N
  · rw [hr]
  have heq : f v = f (boundedFoodRight v) := by
    by_contra hneq
    exact hv (hc (v, true) (by
      simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, wordEdgeParent, hr, hneq]))
  rw [heq]
  by_cases hp : boundedFoodRight v = boundedFoodRoot L N
  · rw [hp]
  apply wordCut_core_avoiding_root (boundedFoodRight v)
  rintro ⟨l, r, hparent⟩
  obtain ⟨b, hb⟩ := boundedFoodParent_preimage v (boundedFoodRight v) true hp rfl
  exact hv ⟨l, r ++ [b], by simp_all⟩
termination_by v.val.length
decreasing_by grind [boundedFoodRight, foodWordRight, boundedFoodRoot]
end

section
variable {A : Type*} (g : List Bool → A)



/-- If both parent moves above M preserve labels, all words from M through N share a label.
The spare level M+1 is essential. -/
theorem highBand_label_constant  (M N : ℕ)
    (hMN : M < N)
    (hparent : ∀ s : List Bool, M < s.length → s.length ≤ N →
      g s = g s.tail ∧ g s = g s.dropLast)
    (u v : List Bool) (hu : M ≤ u.length ∧ u.length ≤ N)
    (hv : M ≤ v.length ∧ v.length ≤ N) : g u = g v := by
  have rotate (front middle : List Bool) (ht : front.length + middle.length = M) :
      g (front ++ middle) = g (middle ++ List.replicate front.length false) := by
    induction front generalizing middle with
    | nil => simp
    | cons a front ih =>
      simp only [List.length_cons] at ht
      have h := hparent (a :: front ++ middle ++ [false])
        (by simp; omega) (by simp; omega)
      simp only [List.dropLast_concat] at h
      simp only [List.cons_append, List.tail_cons] at h
      have := ih (middle ++ [false]) (by simp_all; omega)
      simp_all [List.append_assoc, List.replicate_succ]
      grind
  let base := List.replicate M false
  let rec descend (s : List Bool) (hlo : M ≤ s.length) (hhi : s.length ≤ N) : g s = g base := by
    by_cases he : s.length = M
    · simpa [base, he] using rotate s [] (by simp [he])
    · exact (hparent s (by omega) hhi).2.trans
        (descend s.dropLast (by simp; omega) (by simp; omega))
  termination_by s.length
  decreasing_by simp; omega
  exact (descend u hu.1 hu.2).trans (descend v hv.1 hv.2).symm
end

section

noncomputable def boundedWordLabel 
    (s : List Bool)  :=
  if hs : s = [] ∨ L < s.length ∧ s.length ≤ N then f ⟨s, hs⟩
  else f (boundedFoodRoot L N)

theorem boundedWordLabel_eq 
    (u : _) : boundedWordLabel f u.val = f u := by solve_by_elim [dite_eq_left]

variable (hLM : L < M)

include hLM in
/-- Above every boundary product, both literal parents preserve the cut label. -/
theorem wordCut_above_boundary_parents  (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (s : List Bool) (hs : M < s.length) (hN : s.length ≤ N) :
    boundedWordLabel f s = boundedWordLabel f s.tail ∧
    boundedWordLabel f s = boundedWordLabel f s.dropLast := by
  let u : BoundedFoodWord L N := ⟨s, Or.inr ⟨by omega, hN⟩⟩
  have hn : u ≠ boundedFoodRoot L N := by grind [boundedFoodRoot]
  have heq (b : Bool) : boundedWordLabel f s =
      boundedWordLabel f (wordEdgeParent (u, b)).val := by
    rw [boundedWordLabel_eq f u, boundedWordLabel_eq]
    by_contra h
    have hh := hcut (u, b) (by
      simp [wordGraphCut, booleanEdgeCut, wordBasicEdges, hn, h])
    change s.length ≤ M at hh
    omega
  have hlong : ¬ s.length ≤ L + 1 := by omega
  simpa [wordEdgeParent, boundedFoodLeft, boundedFoodRight, foodWordLeft, foodWordRight, hlong, u]
    using And.intro (heq false) (heq true)

include hLM in
/-- A nonfood-side word cannot be longer than all boundary products when they share a core. -/
theorem wordCut_nonfood_length_le  (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M)
    (core : List Bool) (hne : core ≠ [])
    (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r)
    (u : _) (hu : f u ≠ f (boundedFoodRoot L N)) :
    u.val.length ≤ M := by
  by_contra h
  have hN := boundedFoodWord_length_le u
  have hMN : M < N := by omega
  cases core with
  | nil => exact (hne rfl).elim
  | cons a t =>
    let v : BoundedFoodWord L N := ⟨List.replicate M !a, Or.inr (by simp_all; omega)⟩
    have ha : ¬ ∃ l r : List Bool, v.val = l ++ (a :: t) ++ r := by
      rintro ⟨l, r, he⟩
      have hm : a ∈ v.val := by rw [he]; simp
      grind
    apply hu
    apply Eq.trans _ (wordCut_core_avoiding_root f (a :: t) hcore v ha)
    simpa [boundedWordLabel_eq] using highBand_label_constant (boundedWordLabel f) M N hMN
      (wordCut_above_boundary_parents f hLM hcut) u.val v.val
      ⟨by omega, boundedFoodWord_length_le u⟩ ⟨by simp [v], boundedFoodWord_length_le v⟩

end

section

noncomputable def wordNonfoodSide  :=
  Finset.univ.filter fun u => f u ≠ f (boundedFoodRoot L N)

@[simp] theorem mem_wordNonfoodSide 
    (u : _) : u ∈ wordNonfoodSide f ↔ f u ≠ f (boundedFoodRoot L N) := by
  simp [wordNonfoodSide]


variable (hLM : L < M) (hcut : ∀ e ∈ wordGraphCut f, e.1.val.length ≤ M) (core : List Bool) (hne : core ≠ []) (hcore : ∀ e ∈ wordGraphCut f, ∃ l r : List Bool, e.1.val = l ++ core ++ r) (k : ℕ) (hM : M ≤ core.length + k)



include hLM hcut hne hcore hM in
/-- If the food-containing side is the smaller molecular side, a small core envelope
forces the ambient cap itself to be small. Total molecular mass is 2^(N+1)-2. -/
theorem wordFoodSide_minor_cap_bound 
    (hminor : (2 ^ (N + 1) - 2) - (wordNonfoodSide f).card ≤ (wordNonfoodSide f).card) :
    N ≤ 2 * (k + 1) := by
  have hc : (wordNonfoodSide f).card < 2 ^ (2 * (k + 1)) := calc
    _ ≤ (coreWordEnvelope core k).card := Finset.card_le_card_of_injOn (f := Subtype.val)
      (by
        intro u hu
        have hg : ∃ l r, u.val = l ++ core ++ r := by
          by_contra h
          exact (mem_wordNonfoodSide f u).mp hu (wordCut_core_avoiding_root f core hcore u h)
        have hl := (wordCut_nonfood_length_le f hLM hcut core hne hcore u
          ((mem_wordNonfoodSide f u).mp hu)).trans hM
        simp_all [coreWordEnvelope]
        grind [mem_shortBinaryWords]) Subtype.val_injective.injOn
    _ ≤ (shortBinaryWords k).card * (shortBinaryWords k).card :=
      Finset.card_image_le.trans (by simp)
    _ < 2 ^ (k+1) * 2 ^ (k+1) := by have := shortBinaryWords_card k; nlinarith
    _ = _ := by rw [← pow_add, two_mul]
  exact (pow_le_pow_iff_right₀ (by decide : _ < 2)).mp (by omega)

end



/-- A cut side counted in actual molecules, including each food word separately. -/
noncomputable def wordMolecularSide  (c : Bool) :=
  (actualBinaryWords N).filter fun s => boundedWordLabel f s = c


/-- The complement of the molecular food side is exactly the list image of the nonfood vertices. -/
theorem molecular_food_complement  :
    actualBinaryWords N \ wordMolecularSide f (f (boundedFoodRoot L N)) =
      (wordNonfoodSide f).image Subtype.val := by
  ext s
  simp
  grind [actualBinaryWords, wordMolecularSide, boundedFoodRoot, wordNonfoodSide, HordijkSteelThreshold.boundedWordLabel, mem_actualBinaryWords, boundedFoodWord_length_le]

section
/-- Six end edits and a stay-put choice; duplicates only decrease cardinality. -/
def endWordChoices (s : List Bool)  :=
  insert s (insert s.tail (insert s.dropLast
    ((Finset.univ.image fun b => b :: s) ∪
     (Finset.univ.image fun b => s ++ [b]))))



variable {u v : List Bool}

def endWordBall 
  | 0, s => {s}
  | k + 1, s => (endWordChoices s).biUnion (endWordBall k)

variable (k : ℕ) (s : List Bool)

theorem endWordBall_card  : (endWordBall k s).card ≤ 7 ^ k := by
  induction k generalizing s with
  | zero => simp [endWordBall]
  | succ k ih =>
    apply (Finset.card_biUnion_le_card_mul _ _ (7^k) fun v _ => ih v).trans
    rw [pow_succ']
    gcongr
    unfold endWordChoices
    grind [Finset.card_insert_le, Finset.card_union_le, Fintype.card_bool]

theorem endWord_walk_mem_ball  (p : endWordGraph.Walk u v)
    (k : ℕ) (hk : p.length ≤ k) : v ∈ endWordBall k u  := by
  induction p generalizing k with
  | nil =>
    induction k <;> grind [endWordBall, endWordChoices]
  | cons ha p ih =>
    cases k with
    | zero => simp_all
    | succ k =>
      refine Finset.mem_biUnion.mpr ⟨_, ?_, ih k (by simpa using hk)⟩
      clear hk
      simp_all [endWordGraph, endWordChoices]
      aesop
end

section

variable (L N : ℕ) (s : List Bool)

noncomputable def wordBallEdgeAnchors  (r : ℕ) :=
  (wordBasicEdges L N).filter fun e => e.1.val ∈ endWordBall r s



variable (b : ℕ)

/-- A finite envelope for all size-b contours whose smaller side contains molecule s. -/
noncomputable def wordMoleculeContourEnvelope   :=
  (wordBallEdgeAnchors L N s (64 * b)).biUnion fun e => wordAnchoredContours L N e b



end

open RAF.Polymer unitInterval



noncomputable def contourBudget (a : I) (k : ℕ) : ENNReal :=
  molecularContourConstant * (1-toNNReal a^2)^k




/-- A per-molecule envelope of all positive-size disabled contours. Its
probability bounds actual smaller-side membership by the compiled anchor theorem. -/
def moleculeContourBad  (s : List Bool)
    (ω : Reaction N → Prop)  :=
  ∃ j : ℕ, ∃ C ∈ wordMoleculeContourEnvelope L N s (j+1),
    contourDetoursFailed hL C (fun r ω => ω r) ω


section


/-- Project an actual molecule to the finite graph, contracting all food words. -/
noncomputable def molecularWordVertex (L N : ℕ) (s : List Bool)  :=
  if h : L < s.length ∧ s.length ≤ N then ⟨s, Or.inr h⟩ else boundedFoodRoot L N


theorem molecularWordVertex_label  (f : _)
    (s : List Bool) : f (molecularWordVertex L N s) = boundedWordLabel f s := by grind [molecularWordVertex, boundedWordLabel, boundedFoodRoot]

variable (ω : Reaction N → Prop)

noncomputable def wordEffectiveEdges   :=
  (wordBasicEdges L N).filter fun e => ∃ j : Fin w,
    ∀ a ∈ wordDetourSourceReactions hL (e,j), ω a



theorem wordMolecularSide_complement_of_ne 
    (f : BoundedFoodWord L N → Bool) (c d : Bool) (hcd : c ≠ d) :
    actualBinaryWords N \ wordMolecularSide f c = wordMolecularSide f d := by
  grind [cases Bool, wordMolecularSide]


end





theorem molecularWordVertex_food {L N : ℕ} (s : List Bool) (hs : s.length ≤ L) :
    molecularWordVertex L N s = boundedFoodRoot L N := by grind [molecularWordVertex]

open RAF.Concrete

noncomputable def staticOpenReactions  (ω : Reaction N → Prop)  :=
  Finset.univ.filter ω

variable (ω : Reaction N → Prop)



abbrev wordEffective_reach_generated_iff {u v : _}
    (h : indexedEdgeReach (wordEffectiveEdges hL ω) Prod.fst wordEdgeParent u v) :=
  Relation.EqvGen.eqvGen_le (r' := fun u v : BoundedFoodWord L N =>
    contractedWordGenerated L (staticOpenReactions ω) u.val ↔
      contractedWordGenerated L (staticOpenReactions ω) v.val) (by
    rintro _ _ ⟨e, he, rfl, rfl⟩
    obtain ⟨hb, j, hj⟩ := Finset.mem_filter.mp he
    have hn := (Finset.mem_filter.mp hb).2
    have hf := Relation.EqvGen.eqvGen_le (r' := fun s t =>
      contractedWordGenerated L (staticOpenReactions ω) s ↔
        contractedWordGenerated L (staticOpenReactions ω) t) (by
      rintro _ _ ⟨r, hr, rfl, rfl⟩
      have hnr : r.1.1 ≠ boundedFoodRoot L N := by
        clear h he hb hj
        simp_all [wordDetourKeys, wordDetourLower, wordEdgeParent]; aesop
      obtain ⟨a, ha⟩ : ∃ a, wordShortSourceOption hL r = some a := by
        simp [wordShortSourceOption, hnr]
      have hS : a ∈ staticOpenReactions ω := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        hj a (Finset.mem_biUnion.mpr ⟨r, hr, Option.mem_toFinset.mpr ha⟩)⟩
      simp only [wordShortSourceOption, dite_eq_right hnr, Option.some.injEq] at ha
      cases ha
      obtain ⟨hl, hc⟩ := temporaryReactionClosure_rules (L:=L) (staticOpenReactions ω) _ hS
      clear * - hL hS hl hc hnr
      rcases r with ⟨⟨v, side⟩, j⟩
      cases side <;> simp [wordShortStart, wordShortEnd, wordDropShort]
      all_goals grind [contractedWordGenerated_iff, temporaryReactionClosure_food,
        sourceShortSplit, sourceWordMolecule_length, sourceWordMolecule_word,
        sourceShortReaction_product, sourceShortReaction_leftLength,
        molLength_reactionLeft, molLength_reactionRight, molLength_reactionProduct, reaction_length_add,
        moleculeWord_reactionLeft, moleculeWord_reactionRight]) _ _ (wordDetour_reach_parent (e,j))
    simpa [wordShortStart, contractFoodWord,
      ite_eq_right (not_le.mpr (boundedFoodWord_nonroot_length e.1 hn))] using hf) _ _ h

theorem molecularWordVertex_val {L N : ℕ} (s : List Bool) (hN : s.length ≤ N) :
    (molecularWordVertex L N s).val = contractFoodWord L s := by grind [molecularWordVertex, contractFoodWord, boundedFoodRoot]

end HordijkSteelThreshold
