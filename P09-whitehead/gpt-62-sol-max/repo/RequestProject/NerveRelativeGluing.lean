module

public import RequestProject.NerveSupport
public import RequestProject.NervePrism

@[expose] public section

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

namespace FiniteChains
namespace Nerve

universe u

variable {P : Type u} [Preorder P] {Q : Type u} [Preorder Q]

/-! ### Pushforward along a monotone map -/

omit [Preorder P] [Preorder Q] in
theorem cmap_comp (f : P → Q) {R : Type u} (g : Q → R) (x : Ch P) :
    cmap g (cmap f x) = cmap (g ∘ f) x := by
  refine ext_apply (F := (cmap g).comp (cmap f)) (G := cmap (g ∘ f)) ?_ x
  intro l
  simp [Function.comp_def]

/-- Support of an increasing chain maps into the image of its support predicate. -/
theorem cmap_mem_incOn {f : P → Q} (hf : Monotone f) {A : P → Prop} {B : Q → Prop}
    (hB : ∀ p, A p → B (f p)) {x : Ch P} (hx : x ∈ IncOn A) : cmap f x ∈ IncOn B := by
  apply map_mem_of_mem_closure (cmap f) ?_ hx
  rintro _ ⟨l, ⟨hl, hA⟩, rfl⟩
  rw [cmap_of]
  refine of_mem_incOn (List.isChain_map_of_isChain f (fun _ _ h => hf h) hl) ?_
  grind

/-- A monotone map whose image lies in `B` sends increasing chains into `IncOn B`. -/
theorem cmap_mem_incOn_of_maps {f : P → Q} (hf : Monotone f) {B : Q → Prop}
    (hB : ∀ p : P, B (f p)) {x : Ch P} (hx : x ∈ Inc P) : cmap f x ∈ IncOn B :=
  cmap_mem_incOn hf (A := fun _ : P => True) (fun p _ => hB p) (by simpa only [incOn_true] using hx)

/-- Pushforward along a monotone map of (possibly different) posets preserves increasing
chains. -/
theorem cmap_mem_inc_of_monotone {f : P → Q} (hf : Monotone f) {x : Ch P} (hx : x ∈ Inc P) :
    cmap f x ∈ Inc Q :=
  incOn_le_inc _
    (cmap_mem_incOn_of_maps (B := fun _  => True) hf (fun _ => trivial) hx)

/-- Acyclicity is transported along an order isomorphism of posets. -/
theorem exists_bdry_eq_of_cycle_of_orderIso (e : P ≃o Q)
    (h : ∀ x ∈ Inc Q, bdry x = 0 → ∃ y ∈ Inc Q, bdry y = x) :
    ∀ x ∈ Inc P, bdry x = 0 → ∃ y ∈ Inc P, bdry y = x := by
  intro x hx hcyc
  have hx'  := cmap_mem_inc_of_monotone (f := e) e.monotone hx
  have hcyc' : bdry (cmap e x) = 0 := by rw [← cmap_bdry, hcyc, map_zero]
  obtain ⟨y, hy, hdy⟩ := h _ hx' hcyc'
  refine ⟨cmap e.symm y,
    cmap_mem_inc_of_monotone (f := e.symm) e.symm.monotone hy, ?_⟩
  rw [← cmap_bdry, hdy, cmap_comp]
  have hcomp : (e.symm ∘ e) = id := by
    funext p
    simp
  rw [hcomp, cmap_id]

/-! ### Relative acyclicity -/

/-- **Acyclicity of `U` relative to `B`**: every increasing cycle supported on `U` differs, by
the boundary of an increasing chain supported on `U`, from an increasing cycle supported on
`B`. -/
def AcyclicRelIn (U B : P → Prop) : Prop :=
  ∀ z ∈ IncOn U, bdry z = 0 →
    ∃ c ∈ IncOn B, ∃ y ∈ IncOn U, bdry c = 0 ∧ z = c + bdry y

/-- An acyclic piece is relatively acyclic over any subcomplex. -/
theorem acyclicRelIn_of_acyclicIn {U B : P → Prop} (hU : AcyclicIn U) : AcyclicRelIn U B := by
  intro z hz hcyc
  obtain ⟨y, hy, hdy⟩ := hU z hz hcyc
  exact ⟨0, AddSubgroup.zero_mem _, y, hy, by simp, by rw [hdy, zero_add]⟩

/-- A monotone retraction comparable to the identity moves cycles by a prism boundary. -/
theorem acyclicRelIn_of_comparable_retraction {U B : P → Prop}
    (ρ : {p : P // U p} → {p : P // U p}) (hmono : Monotone ρ)
    (hcmp : (∀ p, ρ p ≤ p) ∨ (∀ p, p ≤ ρ p)) (hbase : ∀ p, B (ρ p).1) :
    AcyclicRelIn U B := by
  intro c hc hcyc
  obtain ⟨c', hc', rfl⟩ := exists_preimage_of_mem_incOn U hc
  have hc₀ : bdry c' = 0 := cmap_val_injective U (by rw [cmap_bdry, hcyc, map_zero])
  have hp (f g : {p : P // U p} → {p : P // U p}) :
      bdry (prism f g c') = cmap g c' - cmap f c' := by
    simpa only [hc₀, map_zero, add_zero] using bdry_prism_add_prism_bdry f g c'
  have he : ∃ y ∈ Inc {p : P // U p}, bdry y = c' - cmap ρ c' := by
    rcases hcmp with hl | hr
    · exact ⟨_, prism_mem_inc hmono monotone_id hl hc', by simpa only [cmap_id] using hp ρ id⟩
    · exact ⟨_, (Inc _).neg_mem (prism_mem_inc monotone_id hmono hr hc'),
        by rw [map_neg, hp, cmap_id, neg_sub]⟩
  obtain ⟨y, hy, hdy⟩ := he
  refine ⟨cmap Subtype.val (cmap ρ c'), ?_, cmap Subtype.val y, cmap_val_mem_incOn U hy, ?_, ?_⟩
  · rw [cmap_comp]
    exact cmap_mem_incOn_of_maps (f := Subtype.val ∘ ρ) hmono hbase hc'
  · simp only [← cmap_bdry, hc₀, map_zero]
  · rw [← cmap_bdry, hdy, map_sub, add_sub_cancel]

end Nerve
end FiniteChains
