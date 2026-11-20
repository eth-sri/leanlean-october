module
public import PottsDiscontinuity.TorusTopology.SquareSecants

/-! # Turning number of a simple lattice polygon -/
@[expose] public section
namespace PottsDiscontinuity.TorusTopology
open SimpleGraph Planar.Medial Secant
def squareDartCompass (d : FK.squareLattice.Dart) : Fin 4 := lab d.fst d.snd

def squareWalkCompassDirections {u v : ℤ × ℤ} (p : FK.squareLattice.Walk u v) := p.darts.map squareDartCompass

def squareWalkCyclicTurn {u : ℤ × ℤ} (p : FK.squareLattice.Walk u u) := compassWordCyclicTurn (squareWalkCompassDirections p)

variable {a b c d : V}

section
variable (f : V → V)
include f

private def along (q : G.Walk b c) : ℤ := (q.darts.map fun e => cut (f e.fst) (f e.snd)).sum

@[simp] private lemma along_nil : along f (Walk.nil : G.Walk a a) = 0 := rfl

end
@[simp] private lemma along_cons (f : V → V) (h : G.Adj a b) (q : G.Walk b c) :
    along f (.cons h q) = cut (f a) (f b) + along f q := rfl
@[simp] private lemma dirs_cons (h : G.Adj a b) (q : G.Walk b c) :
    squareWalkCompassDirections (.cons h q) = lab a b :: squareWalkCompassDirections q := rfl

/-- Glue a strip of disjoint cells by telescoping their common sides. -/
private lemma strip {x y : V} (h : G.Adj a b) (q : G.Walk x y) (ha : a ∉ q.support) (hb : b ∉ q.support) :
    along (·-a) q + cut (y-a) (y-b) = cut (x-a) (x-b) + along (·-b) q := by
  induction q with
  | nil => simp
  | @cons x y z g q ih =>
    simp only [Walk.support_cons,List.mem_cons,not_or] at ha hb
    have := cell h g ha.1 (fun e => ha.2 (e ▸ q.start_mem_support)) hb.1 (fun e => hb.2 (e ▸ q.start_mem_support))
    simp only [along_cons]; linarith [ih ha.2 hb.2]

/-- Sweep the secant across the path between the first and last edges. This
variation compares all the interior turns to secants based at the two ends.
The ends `a,d` may coincide, but neither may lie on the middle path. -/
private lemma fan (q : G.Walk b c) (h : G.Adj a b) (k : G.Adj c d) (hq : q.IsPath) (hn : ¬q.Nil)
    (ha : a ∉ q.support) (hd : d ∉ q.support) :
    compassWordTurn (lab a b :: squareWalkCompassDirections q ++ [lab c d]) = idx (lab c d) - idx (lab a b) +
      4*(along (·-a) q + cut (c-a) (c-b) + cut (c-b) (d-b) + along (d-·) q) := by
  induction q generalizing a d with
  | nil => exact (hn .nil).elim
  | @cons b u c g r ih =>
    obtain ⟨hr,hbr⟩ := (Walk.cons_isPath_iff _ _).mp hq
    simp only [Walk.support_cons,List.mem_cons,not_or] at ha hd
    have ht := local_turn h g (fun e => ha.2 (e ▸ r.start_mem_support))
    simp only [dirs_cons, List.cons_append, along_cons, compassWordTurn]
    cases hnil : r with
    | nil =>
      have ht' := local_turn g k (Ne.symm hd.1)
      simp only [along_nil, squareWalkCompassDirections, Walk.darts_nil, List.map_nil, List.nil_append, compassWordTurn]
      linarith
    | cons g' r' =>
      have hrn : ¬r.Nil := by simp [hnil]
      have h₃ := ih g k hr hrn hbr hd.2
      rw [← hnil]; simp only [List.cons_append] at h₃; linear_combination ht + h₃ - 4*(strip h r ha.2 hbr) - 4*(cell g k (fun e => hbr (e ▸ r.end_mem_support)) (Ne.symm hd.1) (mt hr.nil_iff_eq.mpr hrn) (fun e => hd.2 (e ▸ r.start_mem_support)))

/-- Along a path to the right of the cut vertex, the outgoing secants read
just the difference of the endpoint heights, and the incoming ones read zero. -/
private lemma right_half (a : V) (q : G.Walk b c) (ha : a ∉ q.support) (hmin : ∀ x ∈ q.support, a.1 ≤ x.1) :
    along (·-a) q = up (c-a) - up (b-a) ∧ along (a-·) q = 0 := by
  induction q with
  | nil => simp
  | @cons x y z g r ih =>
    simp only [Walk.support_cons, List.mem_cons, not_or] at ha hmin
    obtain ⟨h₁,h₂⟩ := ih ha.2 (by grind)
    have hx := hmin x (.inl rfl); have hay : a ≠ y := fun e => ha.2 (e ▸ r.start_mem_support)
    have hax := ha.1; have hadj := (FK.squareLattice_adj_iff _ _).mp g
    simp only [ne_eq,Prod.ext_iff] at hay hax
    simp only [along_cons,h₁,h₂,cut,up,Prod.fst_sub,Prod.snd_sub,sub_pos]; split_ifs <;> omega

private lemma uncons {p : G.Walk a b} (hn : ¬p.Nil) : ∃ (x : V) (h : G.Adj a x) (r : G.Walk x b), p = .cons h r := by
  cases p with
  | nil => exact (hn .nil).elim
  | cons h r => exact ⟨_, h, r, rfl⟩

private lemma at_min (p : G.Walk a a) (hp : p.IsCycle) (hmin : ∀ x ∈ p.support, a.1 ≤ x.1) :
    squareWalkCyclicTurn p = 4 ∨ squareWalkCyclicTurn p = -4 := by
  obtain ⟨b,h,r,rfl⟩ := uncons hp.not_nil
  obtain ⟨u,g,s,e⟩ := uncons (Walk.not_nil_of_isCycle_cons hp)
  obtain ⟨c,q,k,eq⟩ := Walk.exists_cons_eq_concat g s
  have er := e.trans eq
  clear e eq; subst r
  have ⟨hq,ha⟩ := (Walk.isPath_concat _).mp ((Walk.cons_isCycle_iff _ _).mp hp).1
  have hn : ¬q.Nil := by have hlen := hp.three_le_length; simp [Walk.not_nil_iff_lt_length] at hlen ⊢; omega
  have hm (x) (hx : x ∈ q.support) : a.1 ≤ x.1 := hmin _ (by simp [*])
  obtain ⟨h₁,h₂⟩ := right_half a q ha hm
  have hf := fan q h k hq hn ha ha
  rw [h₁,h₂,add_zero] at hf
  have hdir : squareWalkCompassDirections (.cons h (q.concat k)) = lab a b :: squareWalkCompassDirections q ++ [lab c a] := by
    simp [squareWalkCompassDirections, squareDartCompass]
  have hl : (lab a b :: squareWalkCompassDirections q ++ [lab c a]).getLast (by simp) = lab c a := List.getLast_append_singleton _
  simp only [List.cons_append] at hf hl
  simp only [squareWalkCyclicTurn,hdir,List.cons_append,compassWordCyclicTurn_cons,hl,hf]
  exact corner h k (hm _ q.start_mem_support) (hm _ q.end_mem_support) (mt hq.nil_iff_eq.mpr hn)

theorem squareWalkCyclicTurn_eq_four_or_neg_four {u : ℤ × ℤ}
    (p : FK.squareLattice.Walk u u) (hp : p.IsCycle) :
    squareWalkCyclicTurn p = 4 ∨ squareWalkCyclicTurn p = -4 := by
  classical
  obtain ⟨a,ha,hmin⟩ := p.support.toFinset.exists_min_image Prod.fst ⟨u, List.mem_toFinset.mpr p.start_mem_support⟩
  have ha' := List.mem_toFinset.mp ha
  have ht := at_min _ (hp.rotate ha') (fun x hx => hmin x <| List.mem_toFinset.mpr <| (p.mem_support_rotate_iff ..).mp hx)
  have h : squareWalkCyclicTurn p = squareWalkCyclicTurn (p.rotate a ha') := by
    obtain ⟨n,hn⟩ := ((p.rotate_darts a ha').symm.map squareDartCompass)
    change _ = squareWalkCompassDirections (p.rotate a ha') at hn
    simp only [squareWalkCyclicTurn, ← hn, compassWordCyclicTurn]
    rw [List.rotate_rotate, Nat.add_comm n 1, ← List.rotate_rotate, ← List.zipWith_rotate_distrib _ _ _ _ (by simp)]
    exact (List.rotate_perm ..).sum_eq.symm
  simp_all

end PottsDiscontinuity.TorusTopology
