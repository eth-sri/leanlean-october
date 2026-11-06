module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterMap

/-!
# WP-I, part 2: breadth-first search, the invariants

The mathematics of the RAM breadth-first search (`ClusterBfsRam.lean`) on a rotation system
`G : Env` (`ClusterMap.lean`), from a source `s`, writing the label `L` into the reached
vertices.  The state is the queue `q` (entries `q 0, …, q (t-1)`, head index `h`), the label
array `lab` (initially `lab0`), the level array `lev` and the parent-dart array `par` (the dart
through which a vertex was discovered).

* `Env.Inv` (outer loop: the entries before `h` are processed) and `Env.InvIn` (inner loop: the
  first `j` darts of the rotation orbit of `first (q h)` are processed);
* `Inv.init`, `Inv.start`, `InvIn.skip`, `InvIn.push`, `InvIn.finish`: the transitions;
* `InvIn.visited_iff`: the visited test `lab w < nv` decides membership in the queue;
* `Inv.reach_iff` (at the end, `h = t`): the queue holds exactly the vertices reachable from
  `s`; `Inv.lev_head_le`: every unblocked dart between reached vertices raises the level by at
  most one; parents (`Inv.par`) lower it by exactly one.
-/

namespace Chazelle.Core.Cluster

@[expose] public section

namespace Env

variable (G : Env)

/-- The dart `e` at `u` is *processed*: if it is unblocked and leads to an unblocked vertex,
that vertex is in the queue with level at most `lev u + 1`. -/
def Done (lev q : ℕ → ℕ) (t u e : ℕ) : Prop :=
  G.db e ≠ 1 → G.vb (G.head e) ≠ 1 →
    (∃ j, j < t ∧ q j = G.head e) ∧ lev (G.head e) ≤ lev u + 1

/-- The parent record of the queue entry `i`: the dart `par (q i)` is unblocked, leads to
`q i` from an earlier entry, whose level is one less. -/
def ParOK (lev par q : ℕ → ℕ) (i : ℕ) : Prop :=
  par (q i) < G.N ∧ G.db (par (q i)) ≠ 1 ∧ G.head (par (q i)) = q i ∧
    ∃ j, j < i ∧ G.vert (par (q i)) = q j ∧ lev (q i) = lev (q j) + 1

/-- **The invariant of the outer loop** (entries before `h` processed). -/
structure Inv (s L : ℕ) (lab0 lab lev par q : ℕ → ℕ) (h t : ℕ) : Prop where
  ht : h ≤ t
  tn : t ≤ G.nv
  t0 : 0 < t
  q0 : q 0 = s
  qlt : ∀ i, i < t → q i < G.nv
  qinj : ∀ i, i < t → ∀ j, j < t → q i = q j → i = j
  lab_in : ∀ i, i < t → lab (q i) = L
  lab_out : ∀ v, v < G.nv → (∀ i, i < t → q i ≠ v) → lab v = lab0 v
  mono : ∀ i j, i ≤ j → j < t → lev (q i) ≤ lev (q j)
  span : ∀ i, i < t → h < t → lev (q i) ≤ lev (q h) + 1
  reach : ∀ i, i < t → G.Reach s (q i) ∧ G.vb (q i) ≠ 1
  lev0 : lev s = 0
  par : ∀ i, i < t → 0 < i → G.ParOK lev par q i
  done : ∀ i, i < h → ∀ e, e < G.N → G.vert e = q i → G.Done lev q t (q i) e

/-- **The invariant of the inner loop**: at the entry `h`, the first `j` darts of the rotation
orbit of `first (q h)` are processed. -/
structure InvIn (s L : ℕ) (lab0 lab lev par q : ℕ → ℕ) (h t j : ℕ) : Prop where
  inv : G.Inv s L lab0 lab lev par q h t
  hlt : h < t
  jle : j ≤ per G.rot G.N (G.first (q h))
  cur : ∀ i, i < j → G.Done lev q t (q h) (G.rot^[i] (G.first (q h)))

/-- The precondition of a search from `s` with label `L`: a well-formed rotation system, `s` an
unblocked vertex, `L < nv`, and every vertex reachable from `s` carries the sentinel `nv`. -/
structure Pre (s L : ℕ) (lab0 : ℕ → ℕ) : Prop where
  ok : G.OK
  s_lt : s < G.nv
  s_vb : G.vb s ≠ 1
  L_lt : L < G.nv
  fresh : ∀ w, w < G.nv → G.Reach s w → lab0 w = G.nv

variable {G}

/-- Processed darts stay processed when the queue grows and old levels are kept. -/
theorem Done.mono {lev q lev' q' : ℕ → ℕ} {t t' u e : ℕ} (h : G.Done lev q t u e)
    (htt : t ≤ t') (hq : ∀ i, i < t → q' i = q i) (hlev : ∀ i, i < t → lev' (q i) = lev (q i))
    (hu : lev' u = lev u) : G.Done lev' q' t' u e := by
  grind [Chazelle.Core.Cluster.Env.Done]

/-- A dart leaving a reached vertex through an unblocked dart to an unblocked vertex is a step. -/
theorem step_of_dart {u e : ℕ} (he : e < G.N) (hdb : G.db e ≠ 1) (hve : G.vert e = u)
    (hu : G.vb u ≠ 1) (hw : G.vb (G.head e) ≠ 1) : G.Step u (G.head e) :=
  ⟨e, he, hdb, hve, rfl, hu, hw⟩

/-! ## The transitions -/

section
variable {s L : ℕ} {lab0 lab lev par q : ℕ → ℕ}
/-- **Start**: the queue holds the source only. -/
theorem Inv.init (hp : G.Pre s L lab0)
    (hq : q 0 = s) (hlab : ∀ v, v < G.nv → lab v = if v = s then L else lab0 v)
    (hlev : lev s = 0) : G.Inv s L lab0 lab lev par q 0 1 := by
  refine ⟨by omega, by have := hp.s_lt; omega, by omega, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlev,
    ?_, ?_⟩
  · intro i hi; rw [show i = 0 by omega, hq]; exact hp.s_lt
  · omega
  · intro i hi; rw [show i = 0 by omega, hq, hlab s hp.s_lt, ite_eq_left rfl]
  · grind
  · grind
  · simp_all
  · ram_grind
  all_goals omega

section
variable {h t : ℕ} (hI : G.Inv s L lab0 lab lev par q h t)
include h t hI
/-- Entering the inner loop at an unprocessed entry. -/
theorem Inv.start (hht : h < t) :
    G.InvIn s L lab0 lab lev par q h t 0 :=
  by ram_grind

/-- The pigeonhole principle for the queue: a vertex outside a full-length queue is impossible,
so there is room for one more entry. -/
theorem Inv.t_lt_of_notMem {w : ℕ} (hw : w < G.nv)
    (hnot : ∀ i, i < t → q i ≠ w) : t < G.nv := by
  classical
  by_contra hge
  have ht : t = G.nv := le_antisymm hI.tn (by omega)
  have hsub : (Finset.range t).image q ⊆ Finset.range G.nv := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_range.mpr (hI.qlt i (Finset.mem_range.mp hi))
  have hcard : ((Finset.range t).image q).card = t := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hI.qinj i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj) hij
  have heq : (Finset.range t).image q = Finset.range G.nv :=
    Finset.eq_of_subset_of_card_le hsub (by simp_all)
  grind


end

section
variable {h t j : ℕ} (hI : G.InvIn s L lab0 lab lev par q h t j)
include h t j hI
/-- **The visited test.**  For an unblocked dart `e` at the head entry leading to an unblocked
vertex `w`, `lab w < nv` holds exactly when `w` is in the queue. -/
theorem InvIn.visited_iff (hp : G.Pre s L lab0) {e : ℕ} (he : e < G.N)
    (hdb : G.db e ≠ 1) (hve : G.vert e = q h) (hw : G.vb (G.head e) ≠ 1) :
    lab (G.head e) < G.nv ↔ ∃ i, i < t ∧ q i = G.head e := by
  classical
  have hwn : G.head e < G.nv := hp.ok.vert_lt _ (hp.ok.opp_lt e he)
  constructor
  · intro hlt
    by_contra hnot
    push Not at hnot
    have hreach : G.Reach s (G.head e) :=
      Relation.ReflTransGen.tail (hI.inv.reach h hI.hlt).1
        (step_of_dart he hdb hve (hI.inv.reach h hI.hlt).2 hw)
    rw [hI.inv.lab_out _ hwn hnot, hp.fresh _ hwn hreach] at hlt
    omega
  · rintro ⟨i, hi, hqi⟩
    rw [← hqi, hI.inv.lab_in i hi]
    exact hp.L_lt

/-- **Skip** a dart that is blocked, leads to a blocked vertex, or to a vertex already queued. -/
theorem InvIn.skip (hj : j < per G.rot G.N (G.first (q h)))
    (hcase : G.db (G.rot^[j] (G.first (q h))) = 1 ∨
      G.vb (G.head (G.rot^[j] (G.first (q h)))) = 1 ∨
      ∃ i, i < t ∧ q i = G.head (G.rot^[j] (G.first (q h)))) :
    G.InvIn s L lab0 lab lev par q h t (j + 1) := by
  refine ⟨hI.inv, hI.hlt, hj, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
  · exact hI.cur i hi
  · intro h1 h2
    rcases hcase with hc | hc | ⟨i', hi', hq⟩
    · omega
    · omega
    · refine ⟨⟨i', hi', hq⟩, ?_⟩
      rw [← hq]
      exact hI.inv.span i' hi' hI.hlt

/-- **Push** the head `w` of an unblocked dart `e` (the `j`-th dart at the head entry) to an
unblocked, unqueued vertex: label, level `lev (q h) + 1`, parent dart `e`, queue entry `t`. -/
theorem InvIn.push (hp : G.Pre s L lab0)
    (hj : j < per G.rot G.N (G.first (q h)))
    (hdb : G.db (G.rot^[j] (G.first (q h))) ≠ 1)
    (hw : G.vb (G.head (G.rot^[j] (G.first (q h)))) ≠ 1)
    (hnot : ∀ i, i < t → q i ≠ G.head (G.rot^[j] (G.first (q h)))) :
    G.InvIn s L lab0 (Function.update lab (G.head (G.rot^[j] (G.first (q h)))) L)
      (Function.update lev (G.head (G.rot^[j] (G.first (q h)))) (lev (q h) + 1))
      (Function.update par (G.head (G.rot^[j] (G.first (q h)))) (G.rot^[j] (G.first (q h))))
      (Function.update q t (G.head (G.rot^[j] (G.first (q h))))) h (t + 1) (j + 1) := by
  set e := G.rot^[j] (G.first (q h)) with he_def
  set w := G.head e with hw_def
  set u := q h with hu_def
  obtain ⟨hI0, hht, _, hcur⟩ := hI
  have hqh : q h < G.nv := hI0.qlt h hht
  have hfirst := hp.ok.first_lt _ hqh
  have he : e < G.N := hp.ok.injOn.iterate_lt j hfirst
  have hve : G.vert e = u := by rw [he_def, hp.ok.vert_iterate j hfirst, hp.ok.vert_first _ hqh]
  have hwn : w < G.nv := hp.ok.vert_lt _ (hp.ok.opp_lt e he)
  have htn : t < G.nv := hI0.t_lt_of_notMem hwn hnot
  have hne : ∀ i, i < t → q i ≠ w := hnot
  -- the new functions agree with the old ones on the old queue
  have hq' : ∀ i, i < t → Function.update q t w i = q i := fun i hi =>
    Function.update_of_ne (by omega) _ _
  have hqt : Function.update q t w t = w := Function.update_self _ _ _
  have hlev' : ∀ i, i < t → Function.update lev w (lev u + 1) (q i) = lev (q i) := fun i hi =>
    Function.update_of_ne (hne i hi) _ _
  have hlevw : Function.update lev w (lev u + 1) w = lev u + 1 := Function.update_self _ _ _
  have hlevu : Function.update lev w (lev u + 1) u = lev u := hlev' h hht
  have hpar' : ∀ i, i < t → Function.update par w e (q i) = par (q i) := fun i hi =>
    Function.update_of_ne (hne i hi) _ _
  have hlab' : ∀ v, v ≠ w → Function.update lab w L v = lab v := fun v hv =>
    Function.update_of_ne hv _ _
  have hreach_u := hI0.reach h hht
  refine ⟨⟨by  omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_⟩, by omega, by rw [hq' h hht]; exact hj, ?_⟩
  · rw [hq' 0 hI0.t0]; exact hI0.q0
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hq' i hi]; exact hI0.qlt i hi
    · rw [hqt]; exact hwn
  · intro i hi k hk hik
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl <;>
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hq' i hi, hq' k hk] at hik; exact hI0.qinj i hi k hk hik
    · rw [hq' i hi, hqt] at hik; exact absurd hik (hne i hi)
    · rw [hq' k hk, hqt] at hik; exact absurd hik.symm (hne k hk)
    · rfl
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hq' i hi, hlab' _ (hne i hi)]; exact hI0.lab_in i hi
    · ram_simp
  · intro v hv hvn
    have hvw : v ≠ w := fun h => hvn t (by omega) (by rw [hqt, h])
    rw [hlab' v hvw]
    exact hI0.lab_out v hv (fun i hi => by rw [← hq' i hi]; exact hvn i (by omega))
  · intro i k hik hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · rw [hq' i (by omega), hq' k hk, hlev' i (by omega), hlev' k hk]
      exact hI0.mono i k hik hk
    · rw [hqt, hlevw]
      rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < k + 1 by omega) with hi | rfl
      · rw [hq' i hi, hlev' i hi]
        exact hI0.span i hi hht
      · rw [hqt, hlevw]
  · intro i hi _
    rw [hq' h hht, hlevu]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hq' i hi, hlev' i hi]; exact hI0.span i hi hht
    · rw [hqt, hlevw]
  · intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · rw [hq' i hi]; exact hI0.reach i hi
    · rw [hqt]
      exact ⟨Relation.ReflTransGen.tail hreach_u.1 (step_of_dart he hdb hve hreach_u.2 hw), hw⟩
  · rw [← hI0.q0, hlev' 0 hI0.t0, hI0.q0]; exact hI0.lev0
  · intro i hi hi0
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · obtain ⟨p1, p2, p3, k, hk, p4, p5⟩ := hI0.par i hi hi0
      unfold ParOK
      rw [hq' i hi, hpar' i hi, hlev' i hi]
      ram_grind
    · unfold ParOK
      rw [hqt, Function.update_self, hlevw]
      ram_grind
  · intro i hi e' he' hve'
    rw [hq' i (by  omega)] at hve' ⊢
    exact (hI0.done i hi e' he' hve').mono (by omega) hq' hlev'
      (hlev' i (by  omega))
  · intro i hi
    rw [hq' h hht]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact (hcur i hi).mono (by omega) hq' hlev' hlevu
    · intro _ _
      ram_grind


end

/-- `InvIn.skip` with the dart named. -/
theorem InvIn.skip' {h t j e : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hj : j < per G.rot G.N (G.first (q h)))
    (he : G.rot^[j] (G.first (q h)) = e)
    (hcase : G.db e = 1 ∨ G.vb (G.head e) = 1 ∨ ∃ i, i < t ∧ q i = G.head e) :
    G.InvIn s L lab0 lab lev par q h t (j + 1) := by
  subst he; exact hI.skip hj hcase

/-- `InvIn.push` with the dart, its head and the new level named. -/
theorem InvIn.push' {h t j e w lu : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0)
    (hj : j < per G.rot G.N (G.first (q h))) (he : G.rot^[j] (G.first (q h)) = e)
    (hwe : G.head e = w) (hlu : lev (q h) + 1 = lu) (hdb : G.db e ≠ 1) (hw : G.vb w ≠ 1)
    (hnot : ∀ i, i < t → q i ≠ w) :
    G.InvIn s L lab0 (Function.update lab w L) (Function.update lev w lu)
      (Function.update par w e) (Function.update q t w) h (t + 1) (j + 1) := by
  subst he hwe hlu; exact hI.push hp hj hdb hw hnot

/-- **Finish** the head entry: all its darts are processed. -/
theorem InvIn.finish {h t j : ℕ}
    (hI : G.InvIn s L lab0 lab lev par q h t j) (hp : G.Pre s L lab0)
    (hj : j = per G.rot G.N (G.first (q h))) :
    G.Inv s L lab0 lab lev par q (h + 1) t := by
  obtain ⟨hI0, hht, _, hcur⟩ := hI
  refine { hI0 with ht := hht, span := ?_, done := ?_ }
  · intro i hi hh
    exact (hI0.span i hi hht).trans (by have := hI0.mono h (h + 1) (by omega) hh; omega)
  · intro i hi e he hve
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact hI0.done i hi e he hve
    · obtain ⟨k, hk, rfl⟩ := (hp.ok.orbit_iff (hI0.qlt i hht)).mp ⟨he, hve⟩
      simp_all

section
variable {h t : ℕ} (hI : G.Inv s L lab0 lab lev par q h t)
include h t hI
/-- Levels are bounded by queue positions. -/
theorem Inv.lev_le : ∀ i, i < t → lev (q i) ≤ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [hI.q0, hI.lev0]
    · obtain ⟨-, -, -, j, hj, -, hl⟩ := hI.par i hi hpos
      grind

/-- The degree sum of the processed queue entries is at most `N`. -/
theorem Inv.sum_deg_le (hok : G.OK) {n : ℕ} (hn : n ≤ t) :
    ∑ i ∈ Finset.range n, G.deg (q i) ≤ G.N := by
  classical
  rw [← Finset.sum_image (f := G.deg) (g := q) (s := Finset.range n)]
  · refine hok.sum_deg_le _ (fun u hu => ?_)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hI.qlt i (by grind)
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hI.qinj i (by omega) j (by omega) hij

/-! ## The end of the search -/



end

end

section
variable {s L : ℕ} {lab0 lab lev par q : ℕ → ℕ} {t : ℕ} (hI : G.Inv s L lab0 lab lev par q t t)
include s L lab0 lab lev par hI
/-- At the end (`h = t`), every step from a queued vertex leads to a queued vertex. -/
theorem Inv.closed {i w : ℕ} (hi : i < t) (hs : G.Step (q i) w) :
    ∃ j, j < t ∧ q j = w := by
  obtain ⟨e, he, hdb, hve, rfl, _, hw⟩ := hs
  exact (hI.done i hi e he hve hdb hw).1

/-- **The queue holds the component**: at the end, a vertex is queued iff it is reachable. -/
theorem Inv.reach_iff (w : ℕ) :
    G.Reach s w ↔ ∃ j, j < t ∧ q j = w := by
  constructor
  · intro h
    induction h with
    | refl => ram_grind
    | tail _ hs ih =>
      obtain ⟨j, hj, rfl⟩ := ih
      exact hI.closed hj hs
  · ram_grind

/-- **Levels across darts**: at the end, an unblocked dart from a reached vertex to an unblocked
vertex raises the level by at most one. -/
theorem Inv.lev_head_le {i e : ℕ} (hi : i < t) (he : e < G.N)
    (hve : G.vert e = q i) (hdb : G.db e ≠ 1) (hw : G.vb (G.head e) ≠ 1) :
    lev (G.head e) ≤ lev (q i) + 1 :=
  (hI.done i hi e he hve hdb hw).2


end

end Env

end

end Chazelle.Core.Cluster
