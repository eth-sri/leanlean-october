import Mathlib.Tactic

import RequestProject.NerveSupport
import RequestProject.NervePrism

/-!
# Relative chain gluing: pieces that are acyclic only relative to a fixed subcomplex

`RequestProject/NerveSupport.lean` glues *acyclic* pieces along acyclic intersections.  The
object `Z` of modified chambers has pieces of two kinds: the ordinary chambers, which are
acyclic, and the modified chambers, which deformation-retract onto their copy of the base poset
and therefore only contribute the cycles of that copy.  This file provides the corresponding
relative statement and its gluing lemma.

* `FiniteChains.Nerve.AcyclicRelIn U B` — every increasing cycle supported on `U` is the sum of
  an increasing **cycle supported on `B`** and a boundary of an increasing chain supported on
  `U`;
* `FiniteChains.Nerve.acyclicRelIn_of_acyclicIn` — an acyclic piece is relatively acyclic over
  any `B`;
* `FiniteChains.Nerve.acyclicRelIn_of_retraction` — **a piece that retracts, below the
  identity, onto a part of `B` is relatively acyclic over `B`**: this is the prism homotopy of
  `RequestProject/NervePrism.lean` applied to the retraction;
* `FiniteChains.Nerve.acyclicRelIn_union_of_unmixed` — the gluing step: an unmixed union of two
  relatively acyclic pieces with acyclic intersection is relatively acyclic.

The proofs run through the coefficients exactly as in the absolute case; no long exact sequence
is used.
-/

namespace FiniteChains.Nerve



variable {P : Type u} [Preorder P] {Q : Type u} [Preorder Q]

/-! ### Pushforward along a monotone map -/

omit [Preorder P] [Preorder Q] in
theorem cmap_comp (f : P → Q) {R : Type u} (g : Q → R) (x : Ch P) :
    cmap g (cmap f x) = cmap (g ∘ f) x := by
  refine ext_apply (F := (cmap g).comp (cmap f)) (G := cmap (g ∘ f)) ?_ x
  intro l
  simp 

/-- The image of an increasing chain under a monotone map all of whose values satisfy `B` is
supported on `B`. -/
theorem cmap_mem_incOn_of_maps {f : P → Q} (hf : Monotone f) {B : Q → Prop}
    (hB : ∀ p : P, B (f p)) {x : Ch P} (hx : x ∈ Inc P) : cmap f x ∈ IncOn B := by
  refine AddSubgroup.closure_induction (p := fun y _ => cmap f y ∈ IncOn B) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨l, hl, rfl⟩
    rw [cmap_of]
    refine of_mem_incOn (List.isChain_map_of_isChain f (fun _ _ h => hf h) hl) ?_
    intro a ha
    obtain ⟨b, -, rfl⟩ := List.mem_map.1 ha
    exact hB b
  · simp
  · aesop
  · simp_all

/-- Pushforward along a monotone map of (possibly different) posets preserves increasing
chains. -/
abbrev cmap_mem_inc_of_monotone {f : P → Q} (hf : Monotone f) {x : Ch P} (hx : x ∈ Inc P)  :=
  incOn_le_inc _
    (cmap_mem_incOn_of_maps (B := fun _ : Q => True) hf (fun _ => trivial) hx)

/-- Acyclicity is transported along an order isomorphism of posets. -/
theorem exists_bdry_eq_of_cycle_of_orderIso (e : P ≃o Q)
    (h : ∀ x ∈ Inc Q, bdry x = 0 → ∃ y ∈ Inc Q, bdry y = x) :
    ∀ x ∈ Inc P, bdry x = 0 → ∃ y ∈ Inc P, bdry y = x := by
  intro x hx hcyc
  have hx'  := cmap_mem_inc_of_monotone (f := (e : P → Q)) e.monotone hx
  have hcyc' : bdry (cmap e x) = 0 := by rw [← cmap_bdry, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := h _ hx' hcyc'
  refine ⟨cmap e.symm y,
    cmap_mem_inc_of_monotone (f := (e.symm : Q → P)) e.symm.monotone hy, ?_⟩
  rw [← cmap_bdry, hdy, cmap_comp]
  have hcomp : ((e.symm : Q → P) ∘ (e : P → Q)) = id := by
    funext p
    simp
  rw [hcomp, cmap_id]

/-! ### Relative acyclicity -/

/-- **Acyclicity of `U` relative to `B`**: every increasing cycle supported on `U` differs, by
the boundary of an increasing chain supported on `U`, from an increasing cycle supported on
`B`. -/
def AcyclicRelIn (U B : P → Prop)  :=
  ∀ z ∈ IncOn U, bdry z = 0 →
    ∃ c ∈ IncOn B, ∃ y ∈ IncOn U, bdry c = 0 ∧ z = c + bdry y

/-- An acyclic piece is relatively acyclic over any subcomplex. -/
theorem acyclicRelIn_of_acyclicIn {U B : P → Prop} (hU : AcyclicIn U) : AcyclicRelIn U B := by
  intro z hz hcyc
  obtain ⟨y, hy, hdy⟩ := hU z hz hcyc
  exact ⟨0, AddSubgroup.zero_mem _, y, hy, by simp, by rw [hdy, zero_add]⟩

/-- **A piece that retracts onto part of `Base`, below the identity, is acyclic relative to
`Base`.**  This is the prism homotopy between the identity and the retraction: every cycle of
the piece is its own image under the retraction plus a boundary, and that image is a cycle
supported on `Base`.  It is exactly the situation of a modified chamber, which retracts onto its
copy of the base poset. -/
theorem acyclicRelIn_of_retraction {U Base : P → Prop} (hne : ∃ p : P, U p)
    (ρ : {p : P // U p} → {p : P // U p}) (hmono : Monotone ρ) (hρle : ∀ q, ρ q ≤ q)
    (hbase : ∀ q, Base (ρ q).1) :
    AcyclicRelIn U Base := by
  intro z hz hcyc
  obtain ⟨z', hz', rfl⟩ := exists_preimage_of_mem_incOn U hz
  have hcyc' : bdry z' = 0 := by
    refine cmap_val_injective U hne ?_
    rw [cmap_bdry, hcyc, map_zero]
  have hid  :=
    bdry_prism_add_prism_bdry ρ id z'
  rw [hcyc', map_zero, add_zero, cmap_id] at hid
  have hyInc  :=
    prism_mem_inc hmono monotone_id hρle hz'
  
  refine ⟨cmap Subtype.val (cmap ρ z'), ?_, cmap Subtype.val (prism ρ id z'),
    cmap_val_mem_incOn U hyInc, ?_, ?_⟩
  · rw [cmap_comp]
    exact cmap_mem_incOn_of_maps
      (f := (Subtype.val : {p : P // U p} → P) ∘ ρ) (fun _ _ h => hmono h)
      (fun q => hbase q) hz'
  · rw [← cmap_bdry, ← cmap_bdry, hcyc', map_zero, map_zero]
  · have h : z' = cmap ρ z' + bdry (prism ρ id z') := by
      rw [hid]
      abel
    rw [← cmap_bdry]
    rw [← map_add, ← h]

end FiniteChains.Nerve

