module

public import Chazelle.Merge.Augmented
public import Chazelle.Chain.Weight

/-!
# Conformality restoration (Chazelle §3.2, Lemmas 3.3 and 3.4), Euclidean part

Chazelle makes the fusion `S` of two submaps conformal (p. 511–512): "For any region with more than
four arcs, let us apply Lemma 3.2 to every pair of nonconsecutive arcs until we find a chord which
we can add to `S`.  We iterate on this process until no region has more than four arcs. …
Lemma 3.3 tells us that this chord addition process will not stop until `S` becomes conformal."

> **Lemma 3.3.** *Let `A₁, …, A_k` be the clockwise circular sequence of arcs around a region of
> `S`.  If `k > 4`, then there exist `i, j` such that (i) `i − j ≠ −1, 0, 1 (mod k)` and (ii) `A_i`
> has a vertex of `∂C` that sees `A_j`.*

The paper's proof ("try all possible cases with five nodes of degree 1") works in the visibility
tree, whose nodes have degree `≤ 4` "since no two distinct vertices of `C` have the same
y-coordinate".  This file proves the Euclidean content for an arbitrary finite chord system
`ChordSystem D F` on a connected domain (the *full map* `F`: the vertex chords `C.chords`, or an
augmented map such as `C.chords ∪ S₀` for an augmented submap `S₀ ⊆ augChords C`), with chain
instances at the end.

## Exit chords and degrees

`exitsIn D W U` is the set of chords of `W` touching `U`.  For a region `R` of a submap `S`,
`exitsIn D S R` is the set of exit chords of `R`, and
`ncard_neighborSet_eq_exits`: **the degree of `R` in the tree of `S` is its number of exit
chords** (distinct chords give distinct dual edges, `edgeOfIn_injOn`).  Hence
`chain_isConformal_iff`: `C.IsConformal S ↔ ∀ R, |exits R| ≤ 4`.

The one-chord bookkeeping is `IsSplit` (the data of `ChordSystem.regionsIn_insert`): adding
`e ∈ F \ S` inside the region `R` of `S` replaces `R` by `R₁, R₂`; the exit chords of `R` are
shared out between `R₁` and `R₂` (`IsSplit.exits_eq_union`, `IsSplit.ncard_exits`), both get `e`
in addition (`exits_insert₁/₂`), and every other region keeps its exit chords (`exits_other`).

## Lemma 3.3 (`lemma_3_3`)

*If every region of the full map `F` inside the region `R` of `S ⊆ F` has at most `Δ` exit
chords, and `R` has more than `Δ` exit chords in `S`, then some chord `e ∈ F \ S` lies inside `R`
and separates the exit chords of `R` into two groups of at least two* (each of the two regions of
`insert e S` inside `R` is touched by `≥ 2` exit chords of `R`).

The proof is an induction on the number of chords of `F` inside `R` (`splitStatement`), counting
only a subset `W ⊆ S` of the exit chords: if `R` contains no chord of `F` it is a region of `F`
(`mem_regionsIn_of_interiorChords_eq_empty`) and has at most `Δ` exit chords; otherwise a chord
`e` inside `R` either already works or cuts off a part `R₁` with at most one counted exit chord,
and one recurses into `R₂`, counting `e` iff it replaces that exit chord
(`splitStatement_aux`).  This is the "sink" argument of the paper's tree picture: a subtree of a
tree of maximal degree `Δ` with more than `Δ` boundary edges has an internal edge with at least two
boundary edges on each side.

**Arcs versus exit chords.**  The boundary of a region alternates exit chords and arcs (Lemma 2.2;
the arc structure `Chazelle.Chain.ArcLink` is not related to the exit chords in the project), so
"`e` joins two nonconsecutive arcs of `R`" is the statement that `e` separates the exit chords of
`R` into two groups of at least two, which is what is proved; "`k > 4` arcs" is replaced by "more
than `Δ` exit chords".

**Degeneracies: the correct version.**  The paper's degree bound `Δ = 4` for the full map needs
distinct heights.  In the project's exact model (no perturbation, chords are point sets, so
collinear vertex chords that coincide count once) the bound fails: for a chain with `k` downward
spikes whose tips (local minima) lie on one horizontal line, the chords between consecutive tips
are `k - 1` distinct chords all bounding the region just below the tips, and that region of the
full map contains no chord at all.  So the paper's Lemma 3.3 is **false** in the exact model for a
submap equal to the full map, and no tie-break on chords can help (the region has no interior
chord to add).  The correct statement is the one above with the *local* hypothesis
`∀ U ∈ regions F, U ⊆ R → |exits_F U| ≤ Δ`; in general position (distinct heights of the vertices
of `C`) the full vertex map satisfies it with `Δ = 4` (p. 495; this geometric fact is not proved
here, `chain_lemma_3_3` takes `C.IsConformal F` as a hypothesis).

## Lemma 3.4 (`lemma_3_4`, `lemma_3_4_regions`, `chain_lemma_3_4`)

A *restoration step* `ConfStep D F Δ S S'` adds to `S` a chord given by Lemma 3.3 in a region with
more than `Δ` exit chords.  The *excess* `potential D Δ S = Σ_R (|exits R| - Δ)` drops by at least
one at each step when `Δ ≥ 3` (`potential_confStep`: a region with `d > Δ` exit chords is replaced
by two with `d₁ + 1, d₂ + 1` exit chords, `d₁ + d₂ = d`, `d₁, d₂ ≥ 2`), vanishes exactly on
submaps whose regions have at most `Δ` exit chords (`potential_eq_zero_iff`), and is at most
`2 |S|` (`potential_le`).  Hence:

* `confStep_run`: every run of `k` restoration steps from `S` has `k ≤ potential S ≤ 2 |S|`;
* `lemma_3_4`: if the regions of `F` have at most `Δ ≥ 3` exit chords, restoration steps from any
  `S ⊆ F` reach a submap `T ⊇ S` all of whose regions have at most `Δ` exit chords, after adding
  at most `2 |S| = 2 (#regions(S) − 1)` chords (`K = 2`);
* `chain_lemma_3_4`: for a finite `F ⊆ augChords C` with `C.IsConformal F`, every `S ⊆ F` extends
  to a conformal `T ⊆ F` with `|T \ S| ≤ 2 |S|`.

The algorithmic parts (Lemma 3.2 to *find* the chord, costs) are not in this file.
-/

namespace Chazelle.Merge

@[expose] public section

open Set
open Chazelle.Chain (ChordSystem freeIn regionsIn mem_regionsIn TouchesIn DualAdjIn dualTreeIn
  dualGraphIn edgeOfIn regionsIn_subset regionsIn_nonempty regionsIn_eq_component
  regionsIn_disjoint_of_ne regionsIn_eq_or_disjoint regionsIn_empty freeIn_anti
  regionsIn_eq_of_subset subset_regionsIn_of_inter regionsIn_isPreconnected)

variable {D : Set Point} {F : Set (Set Point)}

/-! ### Exit chords -/

/-- The *exit chords* of a set `U` (typically a region) among a family `W` of chords: the chords
of `W` touching `U`.  For a region `R` of a submap `S`, `exitsIn D S R` is the set of exit chords
of `R` (p. 493), and its cardinality is the degree of `R` in the tree of the submap
(`ncard_neighborSet_eq_exits`). -/
def exitsIn (D : Set Point) (W : Set (Set Point)) (U : Set Point) : Set (Set Point) :=
  {c | c ∈ W ∧ TouchesIn D c U}

theorem exitsIn_mono {W W' : Set (Set Point)} (h : W ⊆ W') (U : Set Point) :
    exitsIn D W U ⊆ exitsIn D W' U := fun _ hc => ⟨h hc.1, hc.2⟩

theorem exitsIn_subset (W : Set (Set Point)) (U : Set Point) : exitsIn D W U ⊆ W :=
  fun _ hc => hc.1

theorem exitsIn_finite (hF : ChordSystem D F) {W : Set (Set Point)} (hW : W ⊆ F)
    (U : Set Point) : (exitsIn D W U).Finite :=
  (hF.finite.subset hW).subset (exitsIn_subset W U)

/-- The chords of `F` not in `S` whose open part lies in `R`: the chords of the full map in the
interior of the region `R`. -/
def interiorChords (D : Set Point) (F S : Set (Set Point)) (R : Set Point) : Set (Set Point) :=
  {e | e ∈ F ∧ e ∉ S ∧ e ∩ D ⊆ R}

/-! ### Splitting a region by one chord -/

/-- The data of `ChordSystem.regionsIn_insert`: adding the chord `e ∉ S` whose open part lies in
the region `R` of `S` splits `R` into the two regions `R₁ ≠ R₂` of `insert e S`, and leaves the
other regions unchanged. -/
structure IsSplit (D : Set Point) (S : Set (Set Point)) (e R R₁ R₂ : Set Point) : Prop where
  mem : R ∈ regionsIn D S
  sub : e ∩ D ⊆ R
  ne : R₁ ≠ R₂
  union : R₁ ∪ R₂ = R \ e
  mem₁ : R₁ ∈ regionsIn D (insert e S)
  mem₂ : R₂ ∈ regionsIn D (insert e S)
  eq : regionsIn D (insert e S) = (regionsIn D S \ {R}) ∪ {R₁, R₂}

section
variable (hF : ChordSystem D F) {S : Set (Set Point)} (hS : S ⊆ F) {e : Set Point} (he : e ∈ F) (heS : e ∉ S)
include hF hS he heS
/-- The open part of a chord of `F` not in `S` lies in a region of `S`. -/
theorem exists_region_of_chord : ∃ R ∈ regionsIn D S, e ∩ D ⊆ R := by
  obtain ⟨R, hR, heR, -⟩ := hF.regionsIn_insert hS he heS
  grind

/-- Every chord of `F \ S` inside a region `R` of `S` splits it. -/
theorem exists_split {R : Set Point} (hR : R ∈ regionsIn D S)
    (heR : e ∩ D ⊆ R) : ∃ R₁ R₂ : Set Point, IsSplit D S e R R₁ R₂ := by
  obtain ⟨R', hR', heR', R₁, R₂, hne, hunion, h1, h2, heq⟩ := hF.regionsIn_insert hS he heS
  have hRR' : R = R' :=
    regionsIn_eq_of_subset hR hR' (hF.chord_inter_nonempty_isPreconnected he).1 heR heR'
  subst hRR'
  exact ⟨R₁, R₂, ⟨hR, heR, hne, hunion, h1, h2, heq⟩⟩


end

namespace IsSplit

variable {S : Set (Set Point)} {e R R₁ R₂ : Set Point}

section
variable (h : IsSplit D S e R R₁ R₂)
include h
theorem symm : IsSplit D S e R R₂ R₁ :=
  ⟨h.mem, h.sub, h.ne.symm, by rw [union_comm, h.union], h.mem₂, h.mem₁,
    by rw [h.eq, pair_comm]⟩

theorem sub₁ : R₁ ⊆ R := fun p hp => by
  have : p ∈ R₁ ∪ R₂ := Or.inl hp
  rw [h.union] at this
  exact this.1

theorem sub₂ : R₂ ⊆ R := h.symm.sub₁


end

section
variable (h : IsSplit D S e R R₁ R₂) {P : Set Point}
include h
/-- The regions of `insert e S`: the old regions other than `R`, and `R₁`, `R₂`. -/
theorem mem_cases
    (hP : P ∈ regionsIn D (insert e S)) :
    (P ∈ regionsIn D S ∧ P ≠ R) ∨ P = R₁ ∨ P = R₂ := by
  rw [h.eq] at hP
  grind

/-- An old region other than `R` is disjoint from `R`. -/
theorem disjoint_of_ne (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : Disjoint P R :=
  regionsIn_disjoint_of_ne hP h.mem hPR

/-- The regions of `insert e S` inside `R` are `R₁` and `R₂`. -/
theorem eq_of_subset
    (hP : P ∈ regionsIn D (insert e S)) (hPR : P ⊆ R) : P = R₁ ∨ P = R₂ := by
  rcases h.mem_cases hP with ⟨h1, h2⟩ | h3
  · obtain ⟨p, hp⟩ := regionsIn_nonempty hP
    exact absurd (hPR hp) ((h.disjoint_of_ne h1 h2).notMem_of_mem_left hp)
  · exact h3

/-- An old region other than `R` is a region of `insert e S`. -/
theorem mem_of_ne (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : P ∈ regionsIn D (insert e S) := by
  rw [h.eq]
  simp_all


end

/-- `e` does not touch the old regions other than `R`. -/
theorem not_touches (hF : ChordSystem D F) (hS : S ⊆ F) (h : IsSplit D S e R R₁ R₂)
    {P : Set Point} (hP : P ∈ regionsIn D S) (hPR : P ≠ R) : ¬ TouchesIn D e P := by
  rintro ⟨z, hz, hzP⟩
  have hdisj : Disjoint (closure P) R :=
    (h.disjoint_of_ne hP hPR).closure_left (hF.regionsIn_open hS h.mem)
  exact hdisj.notMem_of_mem_left hzP (h.sub hz)

/-- `R₁ ≠ R` (and it is not an old region). -/
theorem ne_of_mem_old (h : IsSplit D S e R R₁ R₂) {P : Set Point} (hP : P ∈ regionsIn D S)
    (hPR : P ≠ R) : P ≠ R₁ := by
  rintro rfl
  obtain ⟨p, hp⟩ := regionsIn_nonempty hP
  exact (h.disjoint_of_ne hP hPR).notMem_of_mem_left hp (h.sub₁ hp)

section
variable (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S) (h : IsSplit D S e R R₁ R₂)
include hF hS he heS h
/-- The new chord touches exactly the two new regions. -/
theorem touches_iff :
    ∀ W ∈ regionsIn D (insert e S), TouchesIn D e W ↔ W = R₁ ∨ W = R₂ :=
  hF.touches_iff_of_split hS he heS h.mem h.sub h.union h.mem₁ h.mem₂ h.eq

theorem touches₁ : TouchesIn D e R₁ :=
  (h.touches_iff hF hS he heS R₁ h.mem₁).2 (Or.inl rfl)

theorem touches₂ : TouchesIn D e R₂ :=
  (h.touches_iff hF hS he heS R₂ h.mem₂).2 (Or.inr rfl)

/-- **The exit chords of `R` are shared out between `R₁` and `R₂`**: for `W ⊆ S`, a chord of
`W` touches `R` iff it touches `R₁` or `R₂`, and it cannot touch both. -/
theorem exits_eq_union {W : Set (Set Point)} (hW : W ⊆ S) :
    exitsIn D W R = exitsIn D W R₁ ∪ exitsIn D W R₂ := by
  ext c
  constructor
  · rintro ⟨hcW, hcR⟩
    have hce : e ≠ c := fun hce => heS (hce ▸ hW hcW)
    rcases hF.touches_split_or he (hS (hW hcW)) hce h.union hcR with h1 | h2
    · exact Or.inl ⟨hcW, h1⟩
    · exact Or.inr ⟨hcW, h2⟩
  · rintro (⟨hcW, h1⟩ | ⟨hcW, h2⟩)
    · exact ⟨hcW, Chazelle.Merge.touchesIn_mono h1 h.sub₁⟩
    · exact ⟨hcW, Chazelle.Merge.touchesIn_mono h2 h.sub₂⟩


end

theorem exits_disjoint (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F)
    (h : IsSplit D S e R R₁ R₂) {W : Set (Set Point)} (hW : W ⊆ S) :
    Disjoint (exitsIn D W R₁) (exitsIn D W R₂) := by
  refine Set.disjoint_left.2 fun c hc1 hc2 => ?_
  obtain ⟨hcW, h1⟩ := hc1
  obtain ⟨-, h2⟩ := hc2
  have hcS : c ∈ S := hW hcW
  -- `c` touches a region `Z ≠ R` of `S`
  obtain ⟨Z₁, Z₂, hZne, hZ₁, hZ₂, htZ, -⟩ := regionsIn_erase hF hS hcS
  have hZ : ∃ Z ∈ regionsIn D S, Z ≠ R ∧ TouchesIn D c Z := by
    grind
  obtain ⟨Z, hZ, hZR, hcZ⟩ := hZ
  have hS' : insert e S ⊆ F := insert_subset he hS
  obtain ⟨Y₁, Y₂, -, -, -, htY, -⟩ := regionsIn_erase hF hS' (mem_insert_of_mem e hcS)
  have e1 := (htY R₁ h.mem₁).1 h1
  have e2 := (htY R₂ h.mem₂).1 h2
  have e3 := (htY Z (h.mem_of_ne hZ hZR)).1 hcZ
  have n1 : Z ≠ R₁ := h.ne_of_mem_old hZ hZR
  have n2 : Z ≠ R₂ := h.symm.ne_of_mem_old hZ hZR
  have hne := h.ne
  grind

section
variable (hF : ChordSystem D F) (hS : S ⊆ F) (he : e ∈ F) (heS : e ∉ S) (h : IsSplit D S e R R₁ R₂)
include hF hS he heS h
/-- **Counting form**: `|exits_W R| = |exits_W R₁| + |exits_W R₂|` for `W ⊆ S`. -/
theorem ncard_exits {W : Set (Set Point)} (hW : W ⊆ S) :
    (exitsIn D W R).ncard = (exitsIn D W R₁).ncard + (exitsIn D W R₂).ncard := by
  rw [h.exits_eq_union hF hS he heS hW]
  exact ncard_union_eq (h.exits_disjoint hF hS he hW) (exitsIn_finite hF (hW.trans hS) _)
    (exitsIn_finite hF (hW.trans hS) _)

/-- The exit chords of `R₁` in `insert e S` are those in `S` and `e`. -/
theorem exits_insert₁ :
    (exitsIn D (insert e S) R₁).ncard = (exitsIn D S R₁).ncard + 1 := by
  have : exitsIn D (insert e S) R₁ = insert e (exitsIn D S R₁) := by
    ext c
    simp only [exitsIn, mem_insert_iff, mem_ofPred_eq]
    constructor
    · simp_all
    · rintro (rfl | ⟨hc, ht⟩)
      · exact ⟨Or.inl rfl, h.touches₁ hF hS he heS⟩
      simp_all
  rw [this, ncard_insert_of_notMem (fun h' => heS h'.1) (exitsIn_finite hF hS _)]

theorem exits_insert₂ :
    (exitsIn D (insert e S) R₂).ncard = (exitsIn D S R₂).ncard + 1 :=
  h.symm.exits_insert₁ hF hS he heS


end

/-- The other regions keep their exit chords. -/
theorem exits_other (hF : ChordSystem D F) (hS : S ⊆ F) (h : IsSplit D S e R R₁ R₂)
    {P : Set Point} (hP : P ∈ regionsIn D S) (hPR : P ≠ R) :
    exitsIn D (insert e S) P = exitsIn D S P := by
  ext c
  simp only [exitsIn, mem_insert_iff, mem_ofPred_eq]
  constructor
  · rintro ⟨rfl | hc, ht⟩
    · exact absurd ht (h.not_touches hF hS hP hPR)
    simp_all
  simp_all

end IsSplit

/-! ### Exit chords under insertion of a chord -/

section
variable {W : Set (Set Point)} {e U : Set Point}
theorem exitsIn_insert_of_touches
    (h : TouchesIn D e U) : exitsIn D (insert e W) U = insert e (exitsIn D W U) := by
  aesop (add simp [exitsIn, mem_insert_iff, mem_ofPred_eq]) (add safe (by omega))

theorem exitsIn_insert_of_not_touches
    (h : ¬ TouchesIn D e U) : exitsIn D (insert e W) U = exitsIn D W U := by
  aesop (add simp [exitsIn, mem_insert_iff, mem_ofPred_eq]) (add safe (by omega))

/-! ### Lemma 3.3: a region with many exit chords contains a splitting chord -/


end

section
variable (hF : ChordSystem D F)
include hF
/-- **A region of `S` containing no chord of the full map is a region of the full map.** -/
theorem mem_regionsIn_of_interiorChords_eq_empty {S : Set (Set Point)}
    (hS : S ⊆ F) {R : Set Point} (hR : R ∈ regionsIn D S)
    (h : interiorChords D F S R = ∅) : R ∈ regionsIn D F := by
  obtain ⟨p, hp⟩ := regionsIn_nonempty hR
  have hRF : R ⊆ freeIn D F := by
    intro q hq
    have hqS := regionsIn_subset hR hq
    refine ⟨hqS.1, ?_⟩
    rintro ⟨e, he, hqe⟩
    have heS : e ∉ S := fun heS => hqS.2 ⟨e, heS, hqe⟩
    have hsub : e ∩ D ⊆ R :=
      subset_regionsIn_of_inter hR (hF.chord_inter_nonempty_isPreconnected he).2
        (hF.chord_inter_subset_freeIn hS he heS) ⟨q, ⟨hqe, hqS.1⟩, hq⟩
    have hmem : e ∈ interiorChords D F S R := ⟨he, heS, hsub⟩
    simp_all
  have heq : R = connectedComponentIn (freeIn D F) p := by
    apply Subset.antisymm
    · exact (regionsIn_isPreconnected hR).subset_connectedComponentIn hp hRF
    · rw [regionsIn_eq_component hR hp]
      exact connectedComponentIn_mono p (freeIn_anti D hS)
  rw [heq]
  exact mem_regionsIn (hRF hp)

/-- If a region `R` of `S` contains no chord of the full map, its exit chords are bounded by the
maximal number `Δ` of exit chords of a region of the full map. -/
theorem exits_le_of_interiorChords_eq_empty {S W : Set (Set Point)}
    (hS : S ⊆ F) (hW : W ⊆ S) {R : Set Point} (hR : R ∈ regionsIn D S)
    (h : interiorChords D F S R = ∅) {Δ : ℕ}
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ) :
    (exitsIn D W R).ncard ≤ Δ :=
  (ncard_le_ncard (exitsIn_mono (hW.trans hS) R) (exitsIn_finite hF subset_rfl R)).trans
    (hΔ R (mem_regionsIn_of_interiorChords_eq_empty hF hS hR h) subset_rfl)

theorem interiorChords_finite (S : Set (Set Point)) (R : Set Point) :
    (interiorChords D F S R).Finite :=
  hF.finite.subset fun _ h => h.1


end

/-- The statement proved by induction for Lemma 3.3 (with a set `W ⊆ S` of *counted* exit
chords). -/
def SplitStatement (D : Set Point) (F : Set (Set Point)) (Δ n : ℕ) : Prop :=
  ∀ (S W : Set (Set Point)) (R : Set Point), S ⊆ F → W ⊆ S → R ∈ regionsIn D S →
    (interiorChords D F S R).ncard ≤ n →
    (∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ) →
    Δ < (exitsIn D W R).ncard →
    ∃ f ∈ F, f ∉ S ∧ f ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D (insert f S), P ⊆ R → 2 ≤ (exitsIn D W P).ncard

section
variable (hF : ChordSystem D F)
include hF
/-- The inductive step of Lemma 3.3 when the chord `e` cuts off at most one counted exit chord
(`|exits_W R₁| ≤ 1`): recurse into `R₂`, counting `e` as an exit chord iff it replaces one. -/
theorem splitStatement_aux {Δ n : ℕ} (ih : SplitStatement D F Δ n)
    {S W : Set (Set Point)} {e R R₁ R₂ : Set Point} (hS : S ⊆ F) (hW : W ⊆ S) (he : e ∈ F)
    (heS : e ∉ S) (h : IsSplit D S e R R₁ R₂)
    (hn : (interiorChords D F S R).ncard ≤ n + 1)
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ)
    (hdeg : Δ < (exitsIn D W R).ncard) (ha : (exitsIn D W R₁).ncard ≤ 1) :
    ∃ f ∈ F, f ∉ S ∧ f ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D (insert f S), P ⊆ R → 2 ≤ (exitsIn D W P).ncard := by
  classical
  have hS' : insert e S ⊆ F := insert_subset he hS
  have heW : e ∉ W := fun h' => heS (hW h')
  set a₁ := (exitsIn D W R₁).ncard with ha₁
  set W' : Set (Set Point) := if a₁ = 1 then insert e W else W with hW'def
  have hW'2 : W' ⊆ insert e W := by
    grind
  have hW'3 : W' ⊆ insert e S := hW'2.trans (insert_subset_insert hW)
  -- the counted exit chords of `R₂` now include `e` iff `a₁ = 1`
  have hcount : (exitsIn D W' R₂).ncard = a₁ + (exitsIn D W R₂).ncard := by
    by_cases h1 : a₁ = 1
    · have : W' = insert e W := by simp_all
      rw [this, exitsIn_insert_of_touches (h.touches₂ hF hS he heS),
        ncard_insert_of_notMem (fun h' => heW h'.1) (exitsIn_finite hF (hW.trans hS) _), h1]
      omega
    grind
  -- `W'` counts at most `a₁` more exit chords than `W`, and none more away from `e`
  have hN1 : ∀ Q, ¬ TouchesIn D e Q → (exitsIn D W' Q).ncard ≤ (exitsIn D W Q).ncard := by
    intro Q hQ
    have : exitsIn D W' Q ⊆ exitsIn D W Q := by
      rw [← exitsIn_insert_of_not_touches (W := W) hQ]
      exact exitsIn_mono hW'2 Q
    exact ncard_le_ncard this (exitsIn_finite hF (hW.trans hS) Q)
  have hN2 : ∀ Q, (exitsIn D W' Q).ncard ≤ (exitsIn D W Q).ncard + a₁ := by
    intro Q
    by_cases h1 : a₁ = 1
    · have : W' = insert e W := by simp_all
      rw [this, h1]
      calc (exitsIn D (insert e W) Q).ncard ≤ (insert e (exitsIn D W Q)).ncard := by
            refine ncard_le_ncard ?_ ((exitsIn_finite hF (hW.trans hS) Q).insert e)
            rintro c ⟨hc | hc, ht⟩
            · simp_all
            · exact Or.inr ⟨hc, ht⟩
        _ ≤ (exitsIn D W Q).ncard + 1 := ncard_insert_le _ _
    grind
  -- the recursion into `R₂`
  have hint : (interiorChords D F (insert e S) R₂).ncard ≤ n := by
    have hsub : interiorChords D F (insert e S) R₂ ⊆ interiorChords D F S R \ {e} := by
      rintro f ⟨hf, hfS, hfR⟩
      exact ⟨⟨hf, fun h' => hfS (mem_insert_of_mem e h'), hfR.trans h.sub₂⟩,
        fun h' => hfS (mem_singleton_iff.1 h' ▸ mem_insert e S)⟩
    have hmem : e ∈ interiorChords D F S R := ⟨he, heS, h.sub⟩
    have h1 := ncard_le_ncard hsub ((interiorChords_finite hF S R).sdiff)
    have h2 := ncard_sdiff_singleton_add_one hmem (interiorChords_finite hF S R)
    omega
  have hΔ' : ∀ U ∈ regionsIn D F, U ⊆ R₂ → (exitsIn D F U).ncard ≤ Δ :=
    fun U hU hUR => hΔ U hU (hUR.trans h.sub₂)
  have hdeg' : Δ < (exitsIn D W' R₂).ncard := by
    rw [hcount, ha₁, ← h.ncard_exits hF hS he heS hW]
    exact hdeg
  obtain ⟨f, hf, hfS', hfR₂, hQ⟩ := ih (insert e S) W' R₂ hS' hW'3 h.mem₂ hint hΔ' hdeg'
  have hfS : f ∉ S := fun h' => hfS' (mem_insert_of_mem e h')
  have hfe : f ≠ e := fun h' => hfS' (h' ▸ mem_insert e S)
  refine ⟨f, hf, hfS, hfR₂.trans h.sub₂, ?_⟩
  intro P hP hPR
  obtain ⟨Q₁, Q₂, hQs⟩ := exists_split hF hS' hf hfS' h.mem₂ hfR₂
  -- the regions of `insert f (insert e S)` inside `R` other than `R₁` lie in `R₂`
  have hK : ∀ Q ∈ regionsIn D (insert f (insert e S)), Q ⊆ R → Q ≠ R₁ → Q ⊆ R₂ := by
    intro Q hQ hQR hQ1
    rcases hQs.mem_cases hQ with ⟨hQ', hQ2⟩ | rfl | rfl
    · rcases h.mem_cases hQ' with ⟨hQ'', hQR'⟩ | rfl | rfl
      · obtain ⟨p, hp⟩ := regionsIn_nonempty hQ
        exact absurd (hQR hp) ((h.disjoint_of_ne hQ'' hQR').notMem_of_mem_left hp)
      all_goals grind
    · exact hQs.sub₁
    · exact hQs.sub₂
  have hR₁mem : R₁ ∈ regionsIn D (insert f (insert e S)) := hQs.mem_of_ne h.mem₁ h.ne
  have hT : insert f S ⊆ F := insert_subset hf hS
  have heT : e ∉ insert f S := by
    grind
  have hswap : insert e (insert f S) = insert f (insert e S) := insert_comm e f S
  have htR₁ : TouchesIn D e R₁ := h.touches₁ hF hS he heS
  obtain ⟨P₀, hP₀, heP₀⟩ := exists_region_of_chord hF hT he heT
  obtain ⟨P₁, P₂, hPs⟩ := exists_split hF hT he heT hP₀ heP₀
  by_cases hPP : P = P₀
  · subst hPP
    have hW_T : W ⊆ insert f S := hW.trans (subset_insert f S)
    rw [hPs.ncard_exits hF hT he heT hW_T]
    have hP₁mem : P₁ ∈ regionsIn D (insert f (insert e S)) := by rw [← hswap]; exact hPs.mem₁
    have hP₂mem : P₂ ∈ regionsIn D (insert f (insert e S)) := by rw [← hswap]; exact hPs.mem₂
    have hR₁' : R₁ ∈ regionsIn D (insert e (insert f S)) := by grind
    rcases (hPs.touches_iff hF hT he heT R₁ hR₁').1 htR₁ with h1 | h1
    · have hP₂R₂ : P₂ ⊆ R₂ := hK P₂ hP₂mem (hPs.sub₂.trans hPR)
        (fun h' => hPs.ne (h1.symm.trans h'.symm))
      grind
    · have hP₁R₂ : P₁ ⊆ R₂ := hK P₁ hP₁mem (hPs.sub₁.trans hPR)
        (fun h' => hPs.ne (h'.trans h1))
      grind
  · have hPe : ¬ TouchesIn D e P := hPs.not_touches hF hT hP hPP
    have hPmem : P ∈ regionsIn D (insert f (insert e S)) := by
      rw [← hswap]; exact hPs.mem_of_ne hP hPP
    grind

/-- **Lemma 3.3, induction.** -/
theorem splitStatement (Δ : ℕ) : ∀ n, SplitStatement D F Δ n := by
  intro n
  induction n with
  | zero =>
    intro S W R hS hW hR hn hΔ hdeg
    have hempty : interiorChords D F S R = ∅ :=
      (ncard_eq_zero (interiorChords_finite hF S R)).1 (Nat.le_zero.1 hn)
    exact absurd (exits_le_of_interiorChords_eq_empty hF hS hW hR hempty hΔ) (not_le.2 hdeg)
  | succ n ih =>
    intro S W R hS hW hR hn hΔ hdeg
    by_cases hempty : interiorChords D F S R = ∅
    · exact absurd (exits_le_of_interiorChords_eq_empty hF hS hW hR hempty hΔ) (not_le.2 hdeg)
    obtain ⟨e, he, heS, heR⟩ := nonempty_iff_ne_empty.2 hempty
    obtain ⟨R₁, R₂, h⟩ := exists_split hF hS he heS hR heR
    by_cases ha₁ : (exitsIn D W R₁).ncard ≤ 1
    · exact splitStatement_aux hF ih hS hW he heS h hn hΔ hdeg ha₁
    by_cases ha₂ : (exitsIn D W R₂).ncard ≤ 1
    · exact splitStatement_aux hF ih hS hW he heS h.symm hn hΔ hdeg ha₂
    refine ⟨e, he, heS, heR, fun P hP hPR => ?_⟩
    rcases h.eq_of_subset hP hPR with rfl | rfl <;> omega

section
variable {S : Set (Set Point)} (hS : S ⊆ F)
include S hS
/-- **Lemma 3.3 (Chazelle, p. 511), Euclidean form.**  Let `F` be a finite chord system (the full
map: the vertex chords `C.chords`, or an augmented map `C.chords ∪ S₀`), `S ⊆ F` a submap and
`R` a region of `S`.  Suppose every region of the full map inside `R` has at most `Δ` exit chords
(in general position `Δ = 4`; see the module docstring for degenerate inputs), while `R` has more
than `Δ` exit chords in `S`.  Then some chord `e` of the full map lies inside `R` (`e ∉ S`, its
open part in `R`) and **separates the exit chords of `R` into two groups of at least two**: each
of the two regions of `insert e S` inside `R` is touched by at least two exit chords of `R`.
(Equivalently, `e` joins two nonconsecutive arcs of `R`.) -/
theorem lemma_3_3 {Δ : ℕ}
    {R : Set Point} (hR : R ∈ regionsIn D S)
    (hΔ : ∀ U ∈ regionsIn D F, U ⊆ R → (exitsIn D F U).ncard ≤ Δ)
    (hdeg : Δ < (exitsIn D S R).ncard) :
    ∃ e ∈ F, e ∉ S ∧ e ∩ D ⊆ R ∧
      ∀ P ∈ regionsIn D (insert e S), P ⊆ R → 2 ≤ (exitsIn D S P).ncard :=
  splitStatement hF Δ _ S S R hS subset_rfl hR le_rfl hΔ hdeg

/-! ### The degree of a region is its number of exit chords -/

/-- The edge of the dual tree contributed by a chord of `S` is the pair of the two regions it
touches. -/
theorem edgeOfIn_eq {c : Set Point}
    (hc : c ∈ S) {U V : Set Point} (hU : U ∈ regionsIn D S) (hV : V ∈ regionsIn D S)
    (hne : U ≠ V) (hcU : TouchesIn D c U) (hcV : TouchesIn D c V) :
    edgeOfIn D S c = s(U, V) := by
  have h := hF.touches_iff hS hc
  unfold edgeOfIn
  rw [dite_eq_left h]
  grind


end

/-- **Distinct chords give distinct edges of the dual tree** (the dual graph has no multiple
edges: it is a tree with exactly `|S|` edges). -/
theorem edgeOfIn_injOn (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set (Set Point)} (hS : S ⊆ F) : InjOn (edgeOfIn D S) S := by
  have hfin : S.Finite := hF.finite.subset hS
  have hsub := hF.dualGraph_edgeSet_subset hS
  have hEfin : (dualGraphIn D S).edgeSet.Finite := (hfin.image _).subset hsub
  have : Finite (dualGraphIn D S).edgeSet := hEfin.to_subtype
  have h1 : Nat.card (dualTreeIn D S).edgeSet ≤ Nat.card (dualGraphIn D S).edgeSet :=
    Nat.card_le_card_of_injective _
      (SimpleGraph.Embedding.mapEdgeSet (SimpleGraph.Embedding.induce (regionsIn D S))).injective
  have h2 := hF.dualTree_card_edgeSet hD hne hS
  simp only [Nat.card_coe_set_eq] at h1 h2
  have h3 : (dualGraphIn D S).edgeSet.ncard ≤ (edgeOfIn D S '' S).ncard :=
    ncard_le_ncard hsub (hfin.image _)
  have h4 : (edgeOfIn D S '' S).ncard ≤ S.ncard := ncard_image_le hfin
  exact injOn_of_ncard_image_eq (by omega) hfin


end

/-- The neighbours of a region `U` in the dual graph of `S`. -/
def neighborsIn (D : Set Point) (S : Set (Set Point)) (U : Set Point) : Set (Set Point) :=
  {X | DualAdjIn D S U X}

section
variable (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty) {S : Set (Set Point)} (hS : S ⊆ F)
include hF hD hne hS
/-- **The degree of a region in the tree of a submap is its number of exit chords.** -/
theorem ncard_neighborsIn_eq_exits {U : Set Point}
    (hU : U ∈ regionsIn D S) : (neighborsIn D S U).ncard = (exitsIn D S U).ncard := by
  classical
  have hfinR := hF.regionsIn_finite hD hne hS
  have hNfin : (neighborsIn D S U).Finite := hfinR.subset fun X hX => hX.2.1
  -- the region on the other side of an exit chord
  let other : Set Point → Set Point := fun c =>
    if h : ∃ X ∈ regionsIn D S, X ≠ U ∧ TouchesIn D c X then Classical.choose h else ∅
  have hother : ∀ c ∈ exitsIn D S U, other c ∈ regionsIn D S ∧ other c ≠ U ∧
      TouchesIn D c (other c) := by
    rintro c ⟨hc, hcU⟩
    have hex : ∃ X ∈ regionsIn D S, X ≠ U ∧ TouchesIn D c X := by
      obtain ⟨Z₁, Z₂, hZne, hZ₁, hZ₂, htZ, -⟩ := regionsIn_erase hF hS hc
      by_cases h1 : Z₁ = U
      · exact ⟨Z₂, hZ₂, fun h' => hZne (h1.trans h'.symm), (htZ Z₂ hZ₂).2 (Or.inr rfl)⟩
      · exact ⟨Z₁, hZ₁, h1, (htZ Z₁ hZ₁).2 (Or.inl rfl)⟩
    have := Classical.choose_spec hex
    simp only [other, dite_eq_left hex]
    exact ⟨this.1, this.2.1, this.2.2⟩
  -- the other region is the unique region `≠ U` touched by the chord
  have huniq : ∀ c ∈ exitsIn D S U, ∀ X ∈ regionsIn D S, X ≠ U → TouchesIn D c X →
      other c = X := by
    intro c hc X hX hXU hcX
    obtain ⟨ho, hoU, hco⟩ := hother c hc
    obtain ⟨Z₁, Z₂, -, -, -, htZ, -⟩ := regionsIn_erase hF hS hc.1
    rcases (htZ _ ho).1 hco with e1 | e1 <;> rcases (htZ _ hX).1 hcX with e2 | e2 <;>
      rcases (htZ _ hU).1 hc.2 with e3 | e3
    all_goals first
      | exact e1.trans e2.symm
      | exact absurd (e1.trans e3.symm) hoU
      | exact absurd (e2.trans e3.symm) hXU
  apply le_antisymm
  · -- every neighbour is the other region of an exit chord
    have hsub : neighborsIn D S U ⊆ other '' exitsIn D S U := by
      rintro X ⟨-, hX, hUX, c, hc, hcU, hcX⟩
      exact ⟨c, ⟨hc, hcU⟩, huniq c ⟨hc, hcU⟩ X hX hUX.symm hcX⟩
    exact (ncard_le_ncard hsub ((exitsIn_finite hF hS U).image _)).trans
      (ncard_image_le (exitsIn_finite hF hS U))
  · refine ncard_le_ncard_of_injOn other ?_ ?_ hNfin
    · intro c hc
      obtain ⟨ho, hoU, hco⟩ := hother c hc
      exact ⟨hU, ho, hoU.symm, c, hc.1, hc.2, hco⟩
    · intro c hc c' hc' hcc
      obtain ⟨ho, hoU, hco⟩ := hother c hc
      obtain ⟨-, -, hco'⟩ := hother c' hc'
      rw [← hcc] at hco'
      have e1 := edgeOfIn_eq hF hS hc.1 hU ho hoU.symm hc.2 hco
      have e2 := edgeOfIn_eq hF hS hc'.1 hU ho hoU.symm hc'.2 hco'
      exact edgeOfIn_injOn hF hD hne hS hc.1 hc'.1 (e1.trans e2.symm)

/-- **Degree = number of exit chords**, for the dual tree on the regions of `S`. -/
theorem ncard_neighborSet_eq_exits (U : regionsIn D S) :
    ((dualTreeIn D S).neighborSet U).ncard = (exitsIn D S U).ncard := by
  rw [← ncard_neighborsIn_eq_exits hF hD hne hS U.2,
    ← ncard_image_of_injective _ Subtype.val_injective]
  congr 1
  ext X
  constructor
  · rintro ⟨V, hV, rfl⟩
    exact hV
  · intro hX
    exact ⟨⟨X, hX.2.1⟩, hX, rfl⟩

/-! ### Lemma 3.4: conformality restoration -/

/-- Sums over the regions after inserting a chord: the region `R` is replaced by `R₁`, `R₂`. -/
theorem finsum_regions_insert {e R R₁ R₂ : Set Point} (h : IsSplit D S e R R₁ R₂)
    (f g : Set Point → ℕ) (hfg : ∀ X ∈ regionsIn D S, X ≠ R → g X = f X) :
    (∑ᶠ X ∈ regionsIn D (insert e S), g X) + f R =
      (∑ᶠ X ∈ regionsIn D S, f X) + g R₁ + g R₂ := by
  have hfin := hF.regionsIn_finite hD hne hS
  have h1 : regionsIn D S = insert R (regionsIn D S \ {R}) :=
    (insert_sdiff_singleton.trans (insert_eq_of_mem h.mem)).symm
  have hdisj : Disjoint (regionsIn D S \ {R}) {R₁, R₂} := by
    refine Set.disjoint_left.2 fun X hX hX' => ?_
    simp only [mem_insert_iff, mem_singleton_iff] at hX'
    rcases hX' with rfl | rfl
    · exact h.ne_of_mem_old hX.1 hX.2 rfl
    · exact h.symm.ne_of_mem_old hX.1 hX.2 rfl
  have hsum : (∑ᶠ X ∈ regionsIn D S \ {R}, g X) = ∑ᶠ X ∈ regionsIn D S \ {R}, f X :=
    finsum_mem_congr rfl fun X hX => hfg X hX.1 hX.2
  have h2 : (∑ᶠ X ∈ regionsIn D S, f X) = f R + ∑ᶠ X ∈ regionsIn D S \ {R}, f X := by
    conv_lhs => rw [h1]
    exact finsum_mem_insert f (fun h' => h'.2 rfl) hfin.sdiff
  rw [h.eq, finsum_mem_union hdisj hfin.sdiff (toFinite _), finsum_mem_pair h.ne, h2, hsum]
  ring


end

/-- The *excess* of a submap: `Σ_R (|exits R| - Δ)` over its regions (truncated subtraction).
It vanishes iff every region has at most `Δ` exit chords. -/
noncomputable def potential (D : Set Point) (Δ : ℕ) (S : Set (Set Point)) : ℕ :=
  ∑ᶠ R ∈ regionsIn D S, ((exitsIn D S R).ncard - Δ)

/-- The excess after inserting one chord. -/
theorem potential_insert (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set (Set Point)} (hS : S ⊆ F) {e R R₁ R₂ : Set Point} (he : e ∈ F) (heS : e ∉ S)
    (h : IsSplit D S e R R₁ R₂) (Δ : ℕ) :
    potential D Δ (insert e S) + ((exitsIn D S R).ncard - Δ) =
      potential D Δ S + ((exitsIn D S R₁).ncard + 1 - Δ) +
        ((exitsIn D S R₂).ncard + 1 - Δ) := by
  unfold potential
  rw [finsum_regions_insert hF hD hne hS h (fun X => (exitsIn D S X).ncard - Δ)
    (fun X => (exitsIn D (insert e S) X).ncard - Δ)
    (fun X hX hXR => by simp only [h.exits_other hF hS hX hXR]),
    h.exits_insert₁ hF hS he heS, h.exits_insert₂ hF hS he heS]

theorem potential_empty (hD : IsPreconnected D) (hne : D.Nonempty) (Δ : ℕ) :
    potential D Δ ∅ = 0 := by
  aesop (add simp [potential, finsum_mem_singleton, exitsIn, ncard_empty, Nat.zero_sub]) (add safe (by omega))

/-- **The excess is at most twice the number of chords**: `potential ≤ 2 |S|`. -/
theorem potential_le (hF : ChordSystem D F) (hD : IsPreconnected D) (hne : D.Nonempty)
    {S : Set (Set Point)} (hS : S ⊆ F) (Δ : ℕ) : potential D Δ S ≤ 2 * S.ncard := by
  have hfin : S.Finite := hF.finite.subset hS
  induction S, hfin using Set.Finite.induction_on with
  | empty => rw [potential_empty hD hne]; omega
  | @insert c S hcS hSfin ih =>
    have hS' : S ⊆ F := (subset_insert c S).trans hS
    have hc : c ∈ F := hS (mem_insert c S)
    obtain ⟨R, hR, hcR⟩ := exists_region_of_chord hF hS' hc hcS
    obtain ⟨R₁, R₂, h⟩ := exists_split hF hS' hc hcS hR hcR
    have e1 := potential_insert hF hD hne hS' hc hcS h Δ
    have e2 := h.ncard_exits hF hS' hc hcS (subset_refl S)
    have e3 := ih hS'
    rw [ncard_insert_of_notMem hcS hSfin]
    omega

/-- **One step of conformality restoration** (p. 512): some region `R` of `S` has more than `Δ`
exit chords, and the chord `e` of the full map inside `R` given by Lemma 3.3 is added; `e`
separates the exit chords of `R` into two groups of at least two. -/
def ConfStep (D : Set Point) (F : Set (Set Point)) (Δ : ℕ) (S S' : Set (Set Point)) : Prop :=
  ∃ R ∈ regionsIn D S, Δ < (exitsIn D S R).ncard ∧ ∃ e ∈ F, e ∉ S ∧ e ∩ D ⊆ R ∧
    S' = insert e S ∧ ∀ P ∈ regionsIn D (insert e S), P ⊆ R → 2 ≤ (exitsIn D S P).ncard

/-- A restoration step adds exactly one chord of the full map. -/
theorem ConfStep.subset (hF : ChordSystem D F) {Δ : ℕ} {S S' : Set (Set Point)}
    (h : ConfStep D F Δ S S') (hS : S ⊆ F) : S' ⊆ F ∧ S ⊆ S' ∧ S'.ncard = S.ncard + 1 := by
  obtain ⟨-, -, -, e, he, heS, -, rfl, -⟩ := h
  exact ⟨insert_subset he hS, subset_insert e S,
    ncard_insert_of_notMem heS (hF.finite.subset hS)⟩

/-! ### The chain instances -/

section ChainInstance

variable (C : Chain)

end ChainInstance

end

end Chazelle.Merge
