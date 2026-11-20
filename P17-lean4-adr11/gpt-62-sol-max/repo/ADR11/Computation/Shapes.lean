module

public import ADR11.Computation.Small
public import ADR11.MSC.Relabel
meta import ADR11.Computation.Small
meta import ADR11.MSC.Relabel

@[expose] public section

namespace ADR11
open Finset _root_.ADR11.Computation

variable {X Y Z : Type*}

/-- The normalized five-leaf topology with `k` cherries. -/
def U5 (k : Fin 3) : For 5 := unroot (codedHierarchy 5 ([3, 24].take k.val))

private theorem relabelFamily_trans (e : X ≃ Y) (f : Y ≃ Z) (F : ClusterFamily X) :
    relabelFamily f (relabelFamily e F) = relabelFamily (e.trans f) F := by
  simp [relabelFamily, ← Equiv.finsetCongr_trans]

abbrev compatibleCodes (n a b : ℕ) : Prop :=
  decC n a ⊆ decC n b ∨ decC n b ⊆ decC n a ∨ Disjoint (decC n a) (decC n b)

/-- Extend the laminar families of the tail by the head only when it fits. -/
def rootings (n : ℕ) : List ℕ → List (List ℕ)
  | [] => [[]]
  | a :: as =>
    let R := rootings n as
    R ++ (R.filter fun cs => decide (∀ b ∈ cs, compatibleCodes n a b)).map (a :: ·)

private theorem mem_rootings {n : ℕ} {cs codes : List ℕ} (h : cs.Sublist codes)
    (hl : cs.Pairwise (compatibleCodes n)) : cs ∈ rootings n codes := by
  induction h with
  | slnil => simp [rootings]
  | cons a _ ih => exact List.mem_append_left _ (ih hl)
  | cons_cons a _ ih =>
    obtain ⟨ha, hs⟩ := List.pairwise_cons.1 hl
    simp only [rootings, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨_, ⟨ih hs, ha⟩, rfl⟩

private theorem SpeciesTree.coded_in {n : ℕ} (σ : TreeOn n) {codes : List ℕ}
    (h : internalClusters σ ⊆ codes.toFinset.image (decC n)) :
    ∃ cs ∈ rootings n codes, σ.clusters = codedHierarchy n cs := by
  let cs := codes.filter fun c => decC n c ∈ internalClusters σ
  have he : (cs.map (decC n)).toFinset = internalClusters σ := by
    ext A
    simp [cs, List.mem_map]
    grind [List.mem_toFinset]
  have hc (c : ℕ) (hm : c ∈ cs) : decC n c ∈ σ.clusters :=
    (mem_filter.1 (of_decide_eq_true (List.mem_filter.1 hm).2)).1
  exact ⟨cs, mem_rootings List.filter_sublist
    (List.pairwise_of_forall_mem_list fun a ha b hb => σ.laminar _ (hc a ha) _ (hc b hb)),
    by rw [codedHierarchy, he, hierarchyOf_internalClusters]⟩

def possibleCodes (n : ℕ) : List ℕ := (List.range (2 ^ n - 1)).filter fun c => 2 ≤ #(decC n c)

def quartetRootings := rootings 4 (possibleCodes 4)

private theorem codes_cover : ∀ n ∈ ([4, 5] : List ℕ), ∀ A : Cl n, 2 ≤ #A → A ≠ univ →
    A ∈ (possibleCodes n).toFinset.image (decC n) := by decide +kernel

theorem exists_code {n : ℕ} (σ : TreeOn n) (hn : n ∈ ([4, 5] : List ℕ)) :
    ∃ cs ∈ rootings n (possibleCodes n), σ.clusters = codedHierarchy n cs :=
  σ.coded_in fun A h => codes_cover n hn A (mem_filter.1 h).2.1 (mem_filter.1 h).2.2

/-- All topologies on a small set of leaves, without branch lengths. -/
def smallTopologies (n : ℕ) : Finset (For n) :=
  (rootings n (possibleCodes n)).toFinset.image fun cs => unroot (codedHierarchy n cs)

theorem topology_mem {n : ℕ} (σ : TreeOn n) (hn : n ∈ ([4, 5] : List ℕ)) :
    unroot σ.clusters ∈ smallTopologies n := by
  obtain ⟨cs, hm, he⟩ := exists_code σ hn
  exact mem_image.2 ⟨cs, List.mem_toFinset.2 hm, congrArg unroot he.symm⟩

def pendantCode (i : Fin 5) : ℕ := 31 - 2 ^ i.val

def informativeCodes : List ℕ := [3, 28, 24, 7] ++ (List.finRange 5).map pendantCode

def fiveRootings : List (List ℕ) :=
  (rootings 5 informativeCodes).filter fun cs => unroot (codedHierarchy 5 cs) ∈ univ.image U5

private theorem supported5 : ∀ k : Fin 3, ∀ A ∈ U5 k, 2 ≤ #A →
    A ∈ informativeCodes.toFinset.image (decC 5) := by decide +kernel

theorem internal_mem_codes (σ : TreeOn 5) {k : Fin 3}
    (hU : unroot σ.clusters = U5 k) : internalClusters σ ⊆ informativeCodes.toFinset.image (decC 5) := by
  intro A hA
  obtain ⟨hA, hc, hu⟩ := mem_filter.1 hA
  exact supported5 k A (hU ▸ mem_unroot.2 (Or.inl ⟨hA, hu⟩)) hc

theorem exists_rootCode5 (σ : TreeOn 5) {k : Fin 3}
    (hU : unroot σ.clusters = U5 k) : ∃ cs ∈ fiveRootings, σ.clusters = codedHierarchy 5 cs := by
  obtain ⟨cs, hm, e⟩ := σ.coded_in (internal_mem_codes σ hU)
  exact ⟨cs, List.mem_filter.2 ⟨hm, decide_eq_true (e ▸ hU.symm ▸ mem_image_of_mem U5 (mem_univ _))⟩, e⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
theorem rootings_literal :
    (quartetRootings = eval% quartetRootings) ∧ (fiveRootings = eval% fiveRootings) := by decide +kernel

section
attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem check5 : ∀ U ∈ smallTopologies 5, ∃ e ∈ (univ : Finset (Equiv.Perm (Fin 5))),
    ∃ k : Fin 3, relabelFamily e U = U5 k := by decide +kernel

end

/-- On five taxa the unrooted tree has zero, one, or two cherries. -/
theorem exists_equiv_unroot_eq_U5 [Fintype X] [DecidableEq X] (hX : Fintype.card X = 5) (σ : SpeciesTree X) :
    ∃ e : X ≃ Fin 5, ∃ k : Fin 3, unroot (σ.relabel e).clusters = U5 k := by
  let f := Fintype.equivFinOfCardEq hX
  obtain ⟨e, -, k, he⟩ := check5 _ (topology_mem (σ.relabel f) (by decide))
  exact ⟨f.trans e, k, by simpa only [SpeciesTree.relabel_clusters, unroot_relabelFamily,
    relabelFamily_trans] using he⟩

end ADR11
