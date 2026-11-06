module

public meta import Chazelle.Arithmetic

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

section
variable (hok : G.OK) (hs : G.Sym) {u w : ℕ}
include hok hs
/-- Steps are symmetric. -/
theorem step_symm (h : G.Step u w) : G.Step w u := by
  obtain ⟨d, hd, hdb, hv, hh, hu, hw⟩ := h
  obtain ⟨h1, h2⟩ := hs d hd
  refine ⟨G.opp d, hok.opp_lt d hd, by omega, hh, ?_, hw, hu⟩
  omega_nf

/-- Reachability is symmetric. -/
theorem reach_symm (h : G.Reach u w) : G.Reach w u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hst ih => exact Relation.ReflTransGen.head (step_symm hok hs hst) ih


end

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

section
variable {lab : ℕ → ℕ}
/-- The start: all vertices carry the sentinel. -/
theorem LInv.init (h : ∀ x, x < G.nv → lab x = G.nv) : G.LInv lab 0 :=
  ⟨fun x hx hne => absurd (h x hx) hne, fun x _ hx hne => absurd (h x hx) hne,
    fun x hx => absurd hx (Nat.not_lt_zero x)⟩

/-- Skip a blocked or already labelled vertex. -/
theorem LInv.skip {v : ℕ} (hI : G.LInv lab v)
    (hcase : G.vb v = 1 ∨ lab v ≠ G.nv) : G.LInv lab (v + 1) := by
  refine ⟨hI.lbl, hI.comp, fun x hx hxn hvb => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
  · exact hI.cover x hx hxn hvb
  omega


end

/-- The precondition of the search from an unblocked, unlabelled vertex: every vertex reachable
from it is unlabelled. -/
theorem LInv.fresh (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} {v : ℕ} (hI : G.LInv lab v)
    (_hv : v < G.nv) (hlv : lab v = G.nv) :
    ∀ w, w < G.nv → G.Reach v w → lab w = G.nv := by
  intro w hw hr
  by_contra hne
  have := hI.comp w v hw hne (reach_symm hok hs hr)
  omega

section
variable (hok : G.OK) (hs : G.Sym) {lab lab' lev par q : ℕ → ℕ} {v t : ℕ} (hI : G.LInv lab v) (hv : v < G.nv)
include hok hs hI hv
/-- **The search step**: after a search from the unblocked, unlabelled vertex `v` with label `v`
(queue `q` of length `t`, final invariant `Inv … t t`), the invariant holds at `v + 1`. -/
theorem LInv.bfs
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
      ram_grind
    · rw [hout x hx hr] at hne ⊢
      exact hI.lbl x hx hne
  · grind [Chazelle.Core.Cluster.Env.reach_trans, Chazelle.Core.Cluster.Env.reach_lt, Chazelle.Core.Cluster.Env.reach_symm, Chazelle.Core.Cluster.Env.LInv.comp]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx' | rfl
    · by_cases hr : G.Reach v x
      · grind
      · rw [hout x hxn hr]; exact hI.cover x hx' hxn hvb
    · rw [hin x Relation.ReflTransGen.refl]; exact hvn

/-- **Accounting of a search step**: the unlabelled vertices after the search are those before
it minus the queue (of length `t`); hence their number and degree sum drop by `t` and by the
degree sum of the queue. -/
theorem LInv.unlab_split (hlv : lab v = G.nv)
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
  
  have hU : U = U' ∪ Q := by
    ext x
    simp only [U, U', Q, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
      Finset.mem_image]
    constructor
    · rintro ⟨hx, hl⟩
      by_cases hq : ∃ i, i < t ∧ q i = x
      · ram_grind
      · push Not at hq
        exact Or.inl ⟨hx, by rw [hB.lab_out x hx hq]; exact hl⟩
    · rintro (⟨hx, hl⟩ | ⟨i, hi, rfl⟩)
      · refine ⟨hx, ?_⟩
        by_cases hq : ∃ i, i < t ∧ q i = x
        · grind
        · push Not at hq
          rw [← hB.lab_out x hx hq]; exact hl
      ram_grind
  have hdisj : Disjoint U' Q := by
    rw [Finset.disjoint_left]
    intro x hx hxq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hxq
    rw [Finset.mem_range] at hi
    have := (Finset.mem_filter.mp hx).2
    rw [hB.lab_in i hi] at this
    omega
  have hinj : Set.InjOn q (Finset.range t) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hB.qinj i hi j hj hij
  have hQc : Q.card = t := by grind
  have hQs : ∑ x ∈ Q, G.deg x = ∑ i ∈ Finset.range t, G.deg (q i) := Finset.sum_image hinj
  refine ⟨?_, ?_⟩
  · rw [hU, Finset.card_union_of_disjoint hdisj, hQc]
  · rw [hU, Finset.sum_union hdisj, hQs]


end

/-- **The end of the labelling**: every unblocked vertex is labelled, and two unblocked vertices
have the same label iff they are connected. -/
theorem LInv.final (hok : G.OK) (hs : G.Sym) {lab : ℕ → ℕ} (hI : G.LInv lab G.nv) :
    (∀ x, x < G.nv → G.vb x ≠ 1 → lab x < G.nv) ∧
    ∀ x y, x < G.nv → y < G.nv → G.vb x ≠ 1 → G.vb y ≠ 1 → (lab x = lab y ↔ G.Reach x y) := by
  grind [Chazelle.Core.Cluster.Env.LInv.cover, Chazelle.Core.Cluster.Env.LInv.lbl, Chazelle.Core.Cluster.Env.LInv.comp, Chazelle.Core.Cluster.Env.reach_symm, Chazelle.Core.Cluster.Env.reach_trans]

end Env

end

end Chazelle.Core.Cluster
