module

public import Chazelle.Core.ClusterBfs

/-!
# WP-I, part 4: component labelling, the invariants

The labelling driver runs one breadth-first search (`ClusterBfsRam.lean`) from every unblocked,
unlabelled vertex `v`, with label `v`.  With a *symmetric* rotation system (`Env.Sym`: `opp` is an
involution and the dart flags are symmetric) reachability is an equivalence on the unblocked
vertices (`Env.reach_symm`, `Env.reach_trans`), and the invariant `Env.LInv` (labelled vertices
are reached from their label, labels are constant on components, the vertices before `v` are
labelled) is kept by each step (`LInv.skip`, `LInv.bfs`).  At the end (`LInv.final`) two unblocked
vertices have the same label iff they are connected.
-/

namespace Chazelle.Core.Cluster

@[expose] public section

namespace Env

variable (G : Env)

/-- A symmetric rotation system: `opp` is an involution and the dart flags are symmetric. -/
def Sym : Prop := ∀ d, d < G.N → G.opp (G.opp d) = d ∧ G.db (G.opp d) = G.db d

variable {G}

/-- Steps are symmetric. -/
theorem step_symm (hok : G.OK) (hs : G.Sym) {u w : ℕ} (h : G.Step u w) : G.Step w u := by
  obtain ⟨d, hd, hdb, hv, hh, hu, hw⟩ := h
  obtain ⟨h1, h2⟩ := hs d hd
  refine ⟨G.opp d, hok.opp_lt d hd, by rw [h2]; exact hdb, hh, ?_, hw, hu⟩
  unfold head; rw [h1, hv]

/-- Reachability is symmetric. -/
theorem reach_symm (hok : G.OK) (hs : G.Sym) {u w : ℕ} (h : G.Reach u w) : G.Reach w u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (step_symm hok hs hst) ih

/-- Reachability is transitive. -/
theorem reach_trans {u v w : ℕ} (h1 : G.Reach u v) (h2 : G.Reach v w) : G.Reach u w :=
  Relation.ReflTransGen.trans h1 h2

/-- A vertex reachable from a vertex is a vertex. -/
theorem reach_lt (hok : G.OK) {u w : ℕ} (h : G.Reach u w) (hu : u < G.nv) : w < G.nv := by
  induction h with
  | refl => exact hu
  | tail _ hst _ =>
    obtain ⟨d, hd, -, -, rfl, -, -⟩ := hst
    exact hok.vert_lt _ (hok.opp_lt d hd)

variable (G)

/-- **The labelling invariant** after the vertices `0, …, v - 1`: every labelled vertex (label
`≠ nv`) is unblocked and reached from its label `< nv`; labels are constant on components; the
unblocked vertices before `v` are labelled. -/
structure LInv (lab : ℕ → ℕ) (v : ℕ) : Prop where
  lbl : ∀ x, x < G.nv → lab x ≠ G.nv → lab x < G.nv ∧ G.vb x ≠ 1 ∧ G.Reach (lab x) x
  comp : ∀ x y, x < G.nv → lab x ≠ G.nv → G.Reach x y → lab y = lab x
  cover : ∀ x, x < v → x < G.nv → G.vb x ≠ 1 → lab x ≠ G.nv

variable {G}

/-- The start: all vertices carry the sentinel. -/
theorem LInv.init {lab : ℕ → ℕ} (h : ∀ x, x < G.nv → lab x = G.nv) : G.LInv lab 0 :=
  ⟨fun x hx hne => absurd (h x hx) hne, fun x _ hx hne => absurd (h x hx) hne,
    fun x hx => absurd hx (Nat.not_lt_zero x)⟩

/-- Skip a blocked or already labelled vertex. -/
theorem LInv.skip {lab : ℕ → ℕ} {v : ℕ} (hI : G.LInv lab v)
    (hcase : G.vb v = 1 ∨ lab v ≠ G.nv) : G.LInv lab (v + 1) := by
  refine ⟨hI.lbl, hI.comp, fun x hx hxn hvb => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
  · exact hI.cover x hx hxn hvb
  · rcases hcase with h | h
    · exact absurd h hvb
    · exact h

/-- The precondition of the search from an unblocked, unlabelled vertex: every vertex reachable
from it is unlabelled. -/
theorem LInv.fresh (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} {v : ℕ} (hI : G.LInv lab v)
    (_hv : v < G.nv) (hlv : lab v = G.nv) :
    ∀ w, w < G.nv → G.Reach v w → lab w = G.nv := by
  intro w hw hr
  by_contra hne
  have := hI.comp w v hw hne (reach_symm hok hs hr)
  rw [hlv] at this
  exact hne this.symm

/-- **The search step**: after a search from the unblocked, unlabelled vertex `v` with label `v`
(queue `q` of length `t`, final invariant `Inv … t t`), the invariant holds at `v + 1`. -/
theorem LInv.bfs (hok : G.OK) (hs : G.Sym) {lab lab' lev par q : ℕ → ℕ} {v t : ℕ}
    (hI : G.LInv lab v) (hv : v < G.nv)
    (hB : G.Inv v v lab lab' lev par q t t) : G.LInv lab' (v + 1) := by
  have hQ : ∀ w, G.Reach v w ↔ ∃ i, i < t ∧ q i = w := hB.reach_iff
  have hin : ∀ w, G.Reach v w → lab' w = v := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := (hQ w).mp hw
    exact hB.lab_in i hi
  have hout : ∀ w, w < G.nv → ¬ G.Reach v w → lab' w = lab w := by
    intro w hw hnot
    exact hB.lab_out w hw (fun i hi hqi => hnot ((hQ w).mpr ⟨i, hi, hqi⟩))
  have hvn : v ≠ G.nv := by omega
  refine ⟨fun x hx hne => ?_, fun x y hx hne hxy => ?_, fun x hx hxn hvb => ?_⟩
  · by_cases hr : G.Reach v x
    · obtain ⟨i, hi, rfl⟩ := (hQ x).mp hr
      rw [hin _ hr]
      exact ⟨hv, (hB.reach i hi).2, hr⟩
    · rw [hout x hx hr] at hne ⊢
      exact hI.lbl x hx hne
  · by_cases hr : G.Reach v x
    · rw [hin x hr, hin y (reach_trans hr hxy)]
    · have hy : y < G.nv := reach_lt hok hxy hx
      have hry : ¬ G.Reach v y := fun h => hr (reach_trans h (reach_symm hok hs hxy))
      rw [hout x hx hr] at hne ⊢
      rw [hout y hy hry]
      exact hI.comp x y hx hne hxy
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx' | rfl
    · by_cases hr : G.Reach v x
      · rw [hin x hr]; exact hvn
      · rw [hout x hxn hr]; exact hI.cover x hx' hxn hvb
    · rw [hin x Relation.ReflTransGen.refl]; exact hvn

/-- **Accounting of a search step**: the unlabelled vertices after the search are those before
it minus the queue (of length `t`); hence their number and degree sum drop by `t` and by the
degree sum of the queue. -/
theorem LInv.unlab_split (hok : G.OK) (hs : G.Sym) {lab lab' lev par q : ℕ → ℕ} {v t : ℕ}
    (hI : G.LInv lab v) (hv : v < G.nv) (hlv : lab v = G.nv)
    (hB : G.Inv v v lab lab' lev par q t t) :
    ((Finset.range G.nv).filter (fun x => lab' x = G.nv)).card + t =
      ((Finset.range G.nv).filter (fun x => lab x = G.nv)).card ∧
    ∑ x ∈ (Finset.range G.nv).filter (fun x => lab' x = G.nv), G.deg x +
      ∑ i ∈ Finset.range t, G.deg (q i) =
      ∑ x ∈ (Finset.range G.nv).filter (fun x => lab x = G.nv), G.deg x := by
  classical
  have hQ : ∀ w, G.Reach v w ↔ ∃ i, i < t ∧ q i = w := hB.reach_iff
  have hfresh := hI.fresh hok hs hv hlv
  set U := (Finset.range G.nv).filter (fun x => lab x = G.nv)
  set U' := (Finset.range G.nv).filter (fun x => lab' x = G.nv)
  set Q := (Finset.range t).image q
  have hvn : v ≠ G.nv := by omega
  have hQU : Q ⊆ U := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at hi
    have hqn := hB.qlt i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqn, hfresh _ hqn (hB.reach i hi).1⟩
  have hU : U = U' ∪ Q := by
    ext x
    simp only [U, U', Q, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨hx, hl⟩
      by_cases hq : ∃ i, i < t ∧ q i = x
      · exact Or.inr hq
      · push Not at hq
        exact Or.inl ⟨hx, by rw [hB.lab_out x hx hq]; exact hl⟩
    · rintro (⟨hx, hl⟩ | ⟨i, hi, rfl⟩)
      · refine ⟨hx, ?_⟩
        by_cases hq : ∃ i, i < t ∧ q i = x
        · obtain ⟨i, hi, rfl⟩ := hq
          rw [hB.lab_in i hi] at hl; exact absurd hl hvn
        · push Not at hq
          rw [← hB.lab_out x hx hq]; exact hl
      · exact ⟨hB.qlt i hi, hfresh _ (hB.qlt i hi) (hB.reach i hi).1⟩
  have hdisj : Disjoint U' Q := by
    rw [Finset.disjoint_left]
    intro x hx hxq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxq
    rw [Finset.mem_range] at hi
    have := (Finset.mem_filter.mp hx).2
    rw [hB.lab_in i hi] at this
    exact hvn this
  have hinj : Set.InjOn q (Finset.range t) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hB.qinj i hi j hj hij
  have hQc : Q.card = t := by rw [Finset.card_image_of_injOn hinj, Finset.card_range]
  have hQs : ∑ x ∈ Q, G.deg x = ∑ i ∈ Finset.range t, G.deg (q i) := Finset.sum_image hinj
  refine ⟨?_, ?_⟩
  · rw [hU, Finset.card_union_of_disjoint hdisj, hQc]
  · rw [hU, Finset.sum_union hdisj, hQs]

/-- **The end of the labelling**: every unblocked vertex is labelled, and two unblocked vertices
have the same label iff they are connected. -/
theorem LInv.final (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} (hI : G.LInv lab G.nv) :
    (∀ x, x < G.nv → G.vb x ≠ 1 → lab x < G.nv) ∧
    ∀ x y, x < G.nv → y < G.nv → G.vb x ≠ 1 → G.vb y ≠ 1 → (lab x = lab y ↔ G.Reach x y) := by
  have hlab : ∀ x, x < G.nv → G.vb x ≠ 1 → lab x ≠ G.nv := fun x hx hvb => hI.cover x hx hx hvb
  refine ⟨fun x hx hvb => (hI.lbl x hx (hlab x hx hvb)).1, fun x y hx hy hvx hvy => ⟨fun h => ?_,
    fun h => (hI.comp x y hx (hlab x hx hvx) h).symm⟩⟩
  obtain ⟨-, -, hrx⟩ := hI.lbl x hx (hlab x hx hvx)
  obtain ⟨-, -, hry⟩ := hI.lbl y hy (hlab y hy hvy)
  rw [h] at hrx
  exact reach_trans (reach_symm hok hs hrx) hry

end Env

end

end Chazelle.Core.Cluster
