module

public import Chazelle.Core.Facts2
public import Chazelle.Core.FactsL23
public import Chazelle.Merge.Granularity
public import Chazelle.Core.SpecMerge
public import Chazelle.Rwx

/-!
# WP-F, part 1: arcs as gaps between cut keys, and weights

Facts about the arcs of a finite admissible family `G` of a model satisfying the walk axioms,
used by the granularity enforcement (`GranularizeSpec`):

* `arc_start_unique`, `arc_end_unique`: two arcs of a nonempty family starting (ending) at the
  same key coincide (same other end, same region);
* `faces_mono`: facing a set is monotone in the set;
* `exists_pos_after_both`: a position inside a walk edge just after a key, inside two cyclic
  intervals that contain the keys just after it;
* `le_weight`, `weight_le`: the weight of a region is the largest weight of its arcs;
* `arcWt_zero_zero`, `arcWt_le_zero_zero`: the pinned arc `(0, 0)` of the empty family meets every
  counted walk edge.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

variable {M : Model}

/-! ## Faces -/

/-- Facing a set is monotone in the set. -/
theorem faces_mono {p : ℕ} {t : ℝ} {U U' : Set Point} (h : M.Faces p t U) (hUU : U ⊆ U') :
    M.Faces p t U' :=
  h.mono fun _ hδ => hUU hδ

/-! ## Arcs with a common end -/

/-- **Two arcs starting at the same key coincide** (nonempty family): the same end, the same
region. -/
theorem arc_start_unique {G : Set (Set Point)} (hne : G.Nonempty) {X Y : Set Point}
    (hX : X ∈ M.regions G) (hY : Y ∈ M.regions G) {a b b' : ℝ} (h : M.IsArc G X a b)
    (h' : M.IsArc G Y a b') : b = b' ∧ X = Y := by
  obtain ⟨-, hb, hab⟩ := WalkAx.arc_cuts hne h
  obtain ⟨-, hb', hab'⟩ := WalkAx.arc_cuts hne h'
  have hbb : b = b' := by
    by_contra hne'
    by_cases h1 : sideInArc a b b'
    · exact h.2.2.2.2.2.1 b' h1 hb'
    · have h2 : sideInArc a b' b := by
        by_contra h3
        exact h1 ((Chazelle.Core.cyc_rot hab hab' hne').2 h3)
      exact h'.2.2.2.2.2.1 b h2 hb
  subst hbb
  refine ⟨rfl, ?_⟩
  obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne h
  exact WalkAx.faces_unique hX hY hf (h'.2.2.2.2.2.2 p t hp ht.1 ht.2 hin)

/-- **Two arcs ending at the same key coincide** (nonempty family). -/
theorem arc_end_unique {G : Set (Set Point)} (hne : G.Nonempty) {X Y : Set Point}
    (hX : X ∈ M.regions G) (hY : Y ∈ M.regions G) {a a' b : ℝ} (h : M.IsArc G X a b)
    (h' : M.IsArc G Y a' b) : a = a' ∧ X = Y := by
  obtain ⟨ha, -, hab⟩ := WalkAx.arc_cuts hne h
  obtain ⟨ha', -, hab'⟩ := WalkAx.arc_cuts hne h'
  have haa : a = a' := by
    refine Chazelle.Core.cyc_start_eq hab hab' (fun h1 => h.2.2.2.2.2.1 a' h1 ha')
      (fun h1 => h'.2.2.2.2.2.1 a h1 ha)
  subst haa
  refine ⟨rfl, ?_⟩
  obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne h
  exact WalkAx.faces_unique hX hY hf (h'.2.2.2.2.2.2 p t hp ht.1 ht.2 hin)

/-! ## Positions just after a key -/

/-- The keys just after `k` lie in every cyclic interval containing `k`. -/
theorem eventually_in_of_mem {a b k : ℝ} (h : sideInArc a b k) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sideInArc a b (k + ε) := Chazelle.Core.cyc_open h

/-- **A position just after a key** `p + t` (with `0 ≤ t < 1`), inside a walk edge, satisfying
two eventual properties of the keys just after it. -/
theorem exists_pos_after_both {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) {A B : ℝ → Prop}
    (hA : ∀ᶠ ε in 𝓝[>] (0 : ℝ), A ((p : ℝ) + t + ε))
    (hB : ∀ᶠ ε in 𝓝[>] (0 : ℝ), B ((p : ℝ) + t + ε)) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, A (p + t') ∧ B (p + t') := by
  obtain ⟨ε, h1, h2, h3⟩ := ((WalkAx.exists_pos_after ht ht1).and (hA.and hB)).exists
  refine ⟨t + ε, h1, ?_, ?_⟩
  · rwx [← add_assoc]
  · rwx [← add_assoc]

/-! ## Weights -/

/-- The set of weights of the arcs of `U`. -/
def arcWts (M : Model) (G : Set (Set Point)) (U : Set Point) : Set ℕ :=
  (fun ab : ℝ × ℝ => M.arcWt ab.1 ab.2) '' {ab | M.IsArc G U ab.1 ab.2}

theorem weight_eq (G : Set (Set Point)) (U : Set Point) : M.weight G U = sSup (arcWts M G U) :=
  rfl

theorem arcWts_finite (hM : WalkAx M) {G : Set (Set Point)} (hG : G ⊆ M.Adm) (hfin : G.Finite)
    {U : Set Point} (hU : U ∈ M.regions G) : (arcWts M G U).Finite :=
  (hM.arcs_bound hG hfin hU).1.image _

/-- An arc weighs at most the weight of its region. -/
theorem le_weight (hM : WalkAx M) {G : Set (Set Point)} (hG : G ⊆ M.Adm) (hfin : G.Finite)
    {U : Set Point} (hU : U ∈ M.regions G) {a b : ℝ} (h : M.IsArc G U a b) :
    M.arcWt a b ≤ M.weight G U :=
  le_csSup (arcWts_finite hM hG hfin hU).bddAbove ⟨(a, b), h, rfl⟩

/-- A bound on all arcs bounds the weight. -/
theorem weight_le {G : Set (Set Point)} {U : Set Point} {w : ℕ}
    (h : ∀ a b, M.IsArc G U a b → M.arcWt a b ≤ w) : M.weight G U ≤ w := by
  rw [weight_eq]
  rcases (arcWts M G U).eq_empty_or_nonempty with he | hne
  · rw [he, csSup_empty]; exact Nat.zero_le _
  · refine csSup_le hne ?_
    rintro _ ⟨ab, hab, rfl⟩
    exact h ab.1 ab.2 hab

/-! ## The pinned arc of the empty family -/

/-- The pinned arc `(0, 0)` meets every counted edge: it weighs the most. -/
theorem arcWt_le_zero_zero (a b : ℝ) : M.arcWt a b ≤ M.arcWt 0 0 := by
  rw [Model.arcWt_eq, Model.arcWt_eq]
  refine Set.ncard_le_ncard ?_ (M.arcEdges_finite 0 0)
  rintro p ⟨hp, hc, t, ht0, ht1, -⟩
  refine ⟨hp, hc, t, ht0, ht1, ?_⟩
  unfold sideInArc
  rw [ite_eq_right (lt_irrefl (0:ℝ))]
  left
  positivity

/-- The pinned arc weighs `size`. -/
theorem arcWt_zero_zero : M.arcWt 0 0 = M.size := by
  unfold Model.arcWt Model.size
  congr 1
  ext p
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hc, -⟩; exact ⟨hp, hc⟩
  · rintro ⟨hp, hc⟩
    refine ⟨hp, hc, 1 / 2, by norm_num, by norm_num, ?_⟩
    unfold sideInArc
    rw [ite_eq_right (lt_irrefl (0:ℝ))]
    left
    positivity

/-- **The empty family**: its only region is the domain, whose only arc is the pinned `(0, 0)`. -/
theorem isArc_empty_iff (hM : WalkAx M) {U : Set Point} (hU : U ∈ M.regions ∅) {a b : ℝ} :
    M.IsArc ∅ U a b ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    rcases h.2.2.2.2.1 with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
    · exact absurd hc (notMem_empty c)
    · exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    have hn : (0 : ℝ) < M.W.n := by
      have : 0 < M.W.n := by
        by_contra h0
        obtain ⟨z, hz⟩ := hM.nonempty
        obtain ⟨s, -, -, p, hp, -⟩ := hM.reach z hz (fun i hi => absurd hi (by omega))
        omega
      exact_mod_cast this
    refine ⟨le_rfl, hn, le_rfl, hn, Or.inr ⟨rfl, rfl, rfl⟩, fun x _ ⟨c, hc, _⟩ => ?_, ?_⟩
    · exact absurd hc (notMem_empty c)
    · intro p t hp ht0 ht1 _
      obtain ⟨V, hV, hfV⟩ := hM.exists_faces_of_not_cut (empty_subset _) finite_empty hp
        ⟨ht0, ht1⟩ (fun ⟨c, hc, _⟩ => absurd hc (notMem_empty c))
      have hD : M.regions ∅ = {M.D} := Chazelle.Chain.regionsIn_empty hM.preconn hM.nonempty
      have e1 : U = M.D := by rw [hD] at hU; exact hU
      have e2 : V = M.D := by rw [hD] at hV; exact hV
      rwx [e1, ← e2]

/-- The weight of the only region of the empty family is `size`. -/
theorem weight_empty (hM : WalkAx M) {U : Set Point} (hU : U ∈ M.regions ∅) :
    M.weight ∅ U = M.size := by
  refine le_antisymm (weight_le fun a b h => ?_) ?_
  · rw [← arcWt_zero_zero]; exact arcWt_le_zero_zero a b
  · rw [← arcWt_zero_zero]
    exact le_weight hM (empty_subset _) finite_empty hU ((isArc_empty_iff hM hU).2 ⟨rfl, rfl⟩)

end

end Gran

end Chazelle.Core
