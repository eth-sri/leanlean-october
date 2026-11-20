module
public import ADR11.Nonbinary.FiveTaxa

/-! Reconstruct the hierarchy from rooted triples. Each internal edge is
isolated by just three leaves: two in different children of the clade and
one in its parent but outside the clade. Extend this triple to five leaves. -/
@[expose] public section
namespace ADR11
open Finset
variable {X : Type*} [Fintype X] [DecidableEq X]

private theorem five_cover (hX : 5 ≤ Fintype.card X) (a b c : X) :
    ∃ S : Finset X, #S = 5 ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S := by
  obtain ⟨S,h,-,hS⟩ := exists_subsuperset_card_eq (subset_univ ({a,b,c} : Finset X))
    (card_insert_le .. |>.trans (Nat.succ_le_succ card_le_two) |>.trans (by decide : 3 ≤ 5))
    (by simpa using hX)
  exact ⟨S,hS,h (by simp),h (by simp),h (by simp)⟩

private theorem trace_iff {A B S : Finset X} (h : traceOn S A = traceOn S B)
    {x : X} (hx : x ∈ S) : x ∈ A ↔ x ∈ B := by
  simpa using (Finset.ext_iff.mp h ⟨x,hx⟩)

/-- Choose the triple in the *second* tree. Its edge is isolated there;
in the first tree it can only gain length on restriction. -/
private theorem bound (hX : 5 ≤ Fintype.card X) {σ τ : SpeciesTree X}
    (h : σ.unrootedDist id = τ.unrootedDist id) {A : Finset X} (h2 : 2 ≤ #A) (hu : A ≠ univ) : σ.edge A ≤ τ.edge A := by
  obtain ⟨a,ha,b,hb,hab,span⟩ := τ.span h2
  obtain ⟨P,_,hp,parent⟩ := τ.least_at (P := (A ⊂ ·)) ⟨univ,τ.univ_mem,ssubset_univ_iff.mpr hu⟩ (fun _ h => h.subset ha)
  obtain ⟨c,hc,hcA⟩ := exists_of_ssubset hp
  obtain ⟨S,hS,as,bs,cs⟩ := five_cover hX a b c
  have ht : 2 ≤ #(traceOn S A) := one_lt_card.mpr ⟨⟨a,as⟩,mem_pre.mpr ha,⟨b,bs⟩,mem_pre.mpr hb,fun e => hab (congrArg Subtype.val e)⟩
  have hn : traceOn S A ≠ univ := fun e => hcA (mem_pre.mp (e ▸ mem_univ (⟨c,cs⟩ : S)))
  have key := SpeciesTree.edge_eq (appC_sameRootedMetricTree (by simpa using hS) _ _ (unrootedDist_restrict_eq h S ⟨a,as⟩)) ht
  simp only [SpeciesTree.restrict,SpeciesTree.pull_edge _ _ _ ht hn] at key
  refine (single_le_sum (s := univ.filter (traceOn S · = traceOn S A)) (fun C _ => σ.edge_nonneg C) (mem_filter.mpr ⟨mem_univ A,rfl⟩)).trans_eq (key.trans ?_)
  apply sum_eq_single_of_mem A (by simp); intro C hC ne
  have e := (mem_filter.mp hC).2
  unfold SpeciesTree.edge; split_ifs with hm; swap; rfl
  have sub := span C (mem_erase.mp hm).2 ((trace_iff e as).2 ha) ((trace_iff e bs).2 hb)
  exact (hcA ((trace_iff e cs).mp (parent C (mem_erase.mp hm).2 (sub.ssubset_of_ne ne.symm) hc))).elim

theorem Challenge.proposition11_theorem9 (hX : 5 ≤ Fintype.card X) (σ τ : SpeciesTree X)
    (h : σ.unrootedDist id = τ.unrootedDist id) : σ.SameRootedMetricTree τ :=
  SpeciesTree.same_of_edge fun _ h2 hu => le_antisymm (bound hX h h2 hu) (bound hX h.symm h2 hu)

end ADR11
