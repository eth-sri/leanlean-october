/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import InfinitaryLogic.Methods.LocalEMFamily
public import InfinitaryLogic.Methods.Henkin.Construction
public import InfinitaryLogic.Methods.TailIndiscernible
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite

/-!
# The local EM context, layer 1: deep interpretation and realize bridges

The semantic layer of the `EMContext` re-base, **generic over `Λ`**: the deep interpretation of
closed `Λ[[J]]`-terms in a source model and the realize bridges connecting it to the syntactic
de-substitution pipeline of `LocalEMFamily.lean`. Mirrors the `skolemColim`-specific chain of
`EMTermModel.lean`, with one systematic simplification: every original proof touched the language
structure only through `letI := skolemColimStructure L`, so here the structure is simply the
ambient instance `[Λ.Structure M]` — `localColimStructure` enters only at instantiation sites
(as in `LocalEMExtraction.lean`). No `[Nonempty M]` is needed (no Hilbert choice in this layer).

Contents (source lemma in `EMTermModel.lean` in parentheses):
* `locDeepInterp` (`deepInterp`) + `locDeepInterp_func`, and the realization bridges
  `locDeepInterp_eq_realize`, `locDeepInterp_subst`, `locDeepInterp_onTerm_subst`;
* the support bridge `locJSupport_onTerm_subst_subset` (`jSupport_onTerm_subst_subset`);
* the ordered-position/`Fin`-arity bridges `locDeepInterp_eq_realize_pos`,
  `locDeTermFin_realize` (`deepInterp_eq_realize_fin`), and the **superset realization
  invariance** `locDeTermFin_realize_superset`;
* the atom bridges `realize_locDeEqAtom(_superset)`, `realize_locDeRelAtom(_superset)` — the
  superset variants route through `locDeTermFin_realize_superset` instead of re-deriving the
  per-term key inline as the originals do;
* the general formula bridge `realize_locDeForm` (`realize_deForm`), consuming
  `realize_openBounds` (imported explicitly from `Methods/Henkin/Construction.lean`) and
  `realize_relabel_sumInr_zero` (from the `Lomega1omega` core).

This file also carries the generic quotient layer: `locDeepInterp_snoc`, the eventual-equality
relation `LocalEMEq` (refl/symm) with its support-enlargement engine
(`LocalEMEq_eventually_on_superset`, `eventually_locDeepInterp_superset_iff`,
`eventually_locRelMap_superset_iff`), the `LocalEMContext` standing-data structure, and (in the
`Quotient` section) the carrier + `Λ[[J]]`-`Structure`. The tail-indiscernibility predicate
`IsLomega1omegaIndiscernibleOnTail` comes from the neutral `Methods/TailIndiscernible.lean`, so this
file stays EM-free.

Next layers (subsequent chunks): the `skolemNeedSymbol` witness-term transport and the
family-membership-carrying restricted truth lemma.
-/

@[expose] public section

namespace FirstOrder.Language

variable (Λ : Language.{0, 0}) (J : Type) [LinearOrder J]

/-! ### Support of substituted base-language terms (syntactic) -/

/-! ### Deep interpretation -/

section DeepInterp

variable {M : Type} [Λ.Structure M] (a : ℕ → M)

/-- The **deep interpretation** of a closed `Λ[[J]]`-term at depth `d` relative to a support `S`:
interpret each `J`-constant `c_j` by the source sequence at position `d + deepRank S j` (so
support constants map to a strictly-increasing deep tuple of `a`), and evaluate in `M`'s ambient
`Λ`-structure. -/
noncomputable def locDeepInterp (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) : M :=
  letI : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  t.realize Empty.elim

/-- **De-substitution bridge**: the deep interpretation of a closed term equals the
*de-substituted* `Λ`-term `constantsToVars t` (each skeleton constant `c_j` turned into the
variable `Sum.inl j`) realized with `j ↦ a (d + deepRank S j)`. Turns the support machinery from
combinatorial into semantic — the right-hand side is a genuine formula realization, so tail
indiscernibility applies. -/
theorem locDeepInterp_eq_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t =
      t.constantsToVars.realize (Sum.elim (fun j => a (d + deepRank J S j)) Empty.elim) := by
  let : (constantsOn J).Structure M := constantsOn.structure (fun j => a (d + deepRank J S j))
  show t.realize Empty.elim = _
  exact (Term.realize_constantsToVars (t := t) (v := Empty.elim)).symm

/-! ### Ordered-position and `Fin`-arity realize bridges -/

/-- **Ordered-position realize bridge**: the deep interpretation is the realize of the
ordered-position de-substituted term on the *consecutive* deep tuple `n ↦ a (d + n)` — exactly
the shape tail indiscernibility consumes (a strictly-increasing deep tuple). -/
theorem locDeepInterp_eq_realize_pos (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty) :
    locDeepInterp Λ J a d S t = (locDeTermPos Λ J S t).realize (fun n => a (d + n)) := by
  rw [locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  congr 1
  funext x
  cases x with
  | inl j => rfl
  | inr e => exact e.elim

/-- **`Fin`-arity realize bridge**: the deep interpretation is the realize of the
`Fin S.card`-indexed de-substituted term on the consecutive deep tuple `i ↦ a (d + i)`, directly
feeding the atoms. -/
theorem locDeTermFin_realize (d : ℕ) (S : Finset J) (t : Λ[[J]].Term Empty)
    (hsub : locJSupport Λ J t ⊆ S) :
    locDeepInterp Λ J a d S t
      = (locDeTermFin Λ J S t hsub).realize (fun i : Fin S.card => a (d + i)) := by
  rw [locDeepInterp_eq_realize_pos, locDeTermFin]
  symm
  exact Term.realize_restrictVar (fun n => a (d + n)) (fun _ => rfl)

/-- **Superset realization invariance**: the `Fin`-arity de-substituted term over `S`, realized
on the `T`-induced deep tuple `i ↦ a (d + deepRank T (orderEmbOfFin S i))`, equals the deep
interpretation over the larger support `T`. The core shared by the equality- and relation-atom
superset bridges (restrictVar realize with a `dite`-extended assignment, then
`realize_eq_of_eq_on_varFinset` to discard the junk, then `orderEmbOfFin_deepRank`). -/
theorem locDeTermFin_realize_superset (d : ℕ) (S T : Finset J) (w : Λ[[J]].Term Empty)
    (hw : locJSupport Λ J w ⊆ S) :
    (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = locDeepInterp Λ J a d T w := by
  have hrv : (locDeTermFin Λ J S w hw).realize
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i)))
      = (locDeTermPos Λ J S w).realize
        (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0)) := by
    rw [locDeTermFin]
    refine Term.realize_restrictVar
      (fun n => a (d + if h : n < S.card then deepRank J T (S.orderEmbOfFin rfl ⟨n, h⟩) else 0))
      (fun x => ?_)
    simp only [dite_eq_left (Finset.mem_range.mp (locDeTermPos_varFinset_subset (Λ := Λ) (J := J) hw x.2))]
  rw [hrv, locDeepInterp_eq_realize, locDeTermPos, Term.realize_relabel]
  apply Term.realize_eq_of_eq_on_varFinset
  intro x hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (locConstantsToVars_varFinset_subset Λ J w hx)
  have hjS : j ∈ S := hw hj
  have hlt : deepRank J S j < S.card := deepRank_lt_card (J := J) hjS
  have hdite : (if h : deepRank J S j < S.card then
      deepRank J T (S.orderEmbOfFin rfl ⟨deepRank J S j, h⟩) else 0) = deepRank J T j := by
    rw [dite_eq_left hlt, orderEmbOfFin_deepRank J S rfl hjS hlt]
  simp only [Function.comp_apply, Sum.elim_inl]
  exact congrArg (fun m => a (d + m)) hdite

/-! ### Atom and formula realize bridges -/

/-- **Equality-atom realize bridge**: the local de-substituted equality atom holds on the
consecutive deep tuple `i ↦ a (d + i)` iff `t` and `u` have equal deep interpretations at depth
`d` over `S`. -/
theorem realize_locDeEqAtom (d : ℕ) (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim (fun i : Fin S.card => a (d + i)) ↔
      locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr, ← locDeTermFin_realize (t := t) (hsub := ht),
    ← locDeTermFin_realize (t := u) (hsub := hu)]

/-- **Superset equality-atom bridge**: the *same* atom over `S`, realized on the `T`-induced deep
tuple (`S ⊆ T`), holds iff `t` and `u` have equal deep interpretations over `T`. One
arity-`S.card` formula carries both the `S`-truth (consecutive tuple) and the `T`-truth (this
strictly-increasing tuple) — the input to tail indiscernibility. -/
theorem realize_locDeEqAtom_superset (d : ℕ) {S T : Finset J} (_hST : S ⊆ T)
    (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S) :
    (locDeEqAtom Λ J S t u ht hu).Realize Empty.elim
        (fun i : Fin S.card => a (d + deepRank J T (S.orderEmbOfFin rfl i))) ↔
      locDeepInterp Λ J a d T t = locDeepInterp Λ J a d T u := by
  rw [locDeEqAtom, canonEqAtom, BoundedFormulaω.realize_equal, Term.realize_relabel,
    Term.realize_relabel, Sum.elim_comp_inr,
    locDeTermFin_realize_superset (w := t) (hw := ht),
    locDeTermFin_realize_superset (w := u) (hw := hu)]

/-! ### Eventual deep equality `LocalEMEq` and the support-enlargement engine -/

/-- **Eventual deep equality**: closed terms `t, u` are identified when, for all sufficiently deep
interpretations of their **combined** skeleton support, they evaluate equally in `M`. (The combined
support means both terms are read against the same ordered finite skeleton.) -/
def LocalEMEq (t u : Λ[[J]].Term Empty) : Prop :=
  ∀ᶠ d in Filter.atTop,
    locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) t =
      locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) u

theorem LocalEMEq.refl (t : Λ[[J]].Term Empty) : LocalEMEq Λ J a t t :=
  Filter.Eventually.of_forall fun _ => rfl

theorem LocalEMEq.symm {t u : Λ[[J]].Term Empty} (h : LocalEMEq Λ J a t u) :
    LocalEMEq Λ J a u t := by
  unfold LocalEMEq
  rw [Finset.union_comm (locJSupport Λ J u) (locJSupport Λ J t)]
  exact h.mono fun _ hd => hd.symm

/-- **Support-enlargement *iff*** (the symmetric core): on the deep tail the deep equality over the
combined support `S₀` is *equivalent* to the deep equality over any larger support `S ⊇ S₀`. Both
directions — descending from a larger support back to `S₀` is what `LocalEMContext.trans` needs. -/
theorem eventually_locDeepInterp_superset_iff
    {Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)}
    (hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ)
    {t u : Λ[[J]].Term Empty}
    (hmem : (⟨(locJSupport Λ J t ∪ locJSupport Λ J u).card,
        locDeEqAtom Λ J (locJSupport Λ J t ∪ locJSupport Λ J u) t u Finset.subset_union_left
          Finset.subset_union_right⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ)
    {S : Finset J} (hS : locJSupport Λ J t ∪ locJSupport Λ J u ⊆ S) :
    ∀ᶠ d in Filter.atTop,
      (locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) t
            = locDeepInterp Λ J a d (locJSupport Λ J t ∪ locJSupport Λ J u) u ↔
          locDeepInterp Λ J a d S t = locDeepInterp Λ J a d S u) := by
  obtain ⟨N, hN⟩ := hind hmem
  rw [Filter.eventually_atTop]
  refine ⟨N, fun d hd => ?_⟩
  set S₀ := locJSupport Λ J t ∪ locJSupport Λ J u with hS₀def
  have hsmono : StrictMono (fun i : Fin S₀.card => d + (i : ℕ)) :=
    fun i i' hii' => Nat.add_lt_add_left hii' d
  have hs'mono : StrictMono (fun i : Fin S₀.card => d + deepRank J S (S₀.orderEmbOfFin rfl i)) := by
    intro i i' hii'
    refine Nat.add_lt_add_left
      (deepRank_lt_of_lt (J := J) ?_ ((S₀.orderEmbOfFin rfl).strictMono hii')) d
    exact hS (Finset.orderEmbOfFin_mem S₀ rfl i)
  have hiff := hN (fun i => d + (i : ℕ)) (fun i => d + deepRank J S (S₀.orderEmbOfFin rfl i))
    hsmono hs'mono (fun k => le_trans hd (Nat.le_add_right d k))
    (fun k => le_trans hd (Nat.le_add_right d _))
  have hb0 := realize_locDeEqAtom Λ J a d S₀ t u Finset.subset_union_left Finset.subset_union_right
  have hbS := realize_locDeEqAtom_superset Λ J a d hS t u Finset.subset_union_left
    Finset.subset_union_right
  exact Iff.trans hb0.symm (Iff.trans hiff hbS)

end DeepInterp

/-! ### The local EM quotient context

To avoid threading the indiscernible sequence, its tail-indiscernible family, and the atomic-diagram
membership through every congruence proof, we bundle them in a `LocalEMContext`. Every quotient
operation then uses `LocalEMEq_eventually_on_superset` (via the support-enlargement *iff*) as its
standing congruence engine. Generic over `Λ` and `[Λ.Structure M]`; the countable local instance is
built in `LocalEMExtraction.lean`. -/

section Quotient

variable {M : Type} [Λ.Structure M]

/-- The **standing data** for the local EM quotient over a fixed source model `M`: a sequence `a` of
deep indiscernibles, a tail-indiscernible family `Γ`, and the fact that every de-substituted atom
lies in `Γ`. The structure accepts an *arbitrary* `Γ`; the countable local family `ΓEMlocal` and its
tail-indiscernible sequence discharge these fields at instantiation (`LocalEMExtraction.lean`). -/
structure LocalEMContext where
  /-- The deep indiscernible sequence. -/
  a : ℕ → M
  /-- The tail-indiscernible formula family. -/
  Γ : Set (Σ n, Λ.BoundedFormulaω Empty n)
  /-- Tail indiscernibility of `a` on `Γ`. -/
  hind : IsLomega1omegaIndiscernibleOnTail (L := Λ) a Γ
  /-- Every de-substituted equality atom is in `Γ`. -/
  atom_mem : ∀ (S : Finset J) (t u : Λ[[J]].Term Empty)
    (ht : locJSupport Λ J t ⊆ S) (hu : locJSupport Λ J u ⊆ S),
    (⟨S.card, locDeEqAtom Λ J S t u ht hu⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ
  /-- Every de-substituted relation atom is in `Γ`. -/
  rel_mem : ∀ (S : Finset J) {l : ℕ} (R : Λ.Relations l)
    (ts : Fin l → Λ[[J]].Term Empty) (ht : ∀ i, locJSupport Λ J (ts i) ⊆ S),
    (⟨S.card, locDeRelAtom Λ J S R ts ht⟩ : Σ n, Λ.BoundedFormulaω Empty n) ∈ Γ

/-- **Transitivity of `LocalEMEq`** (the congruence engine's first payoff): enlarge to the union of
all three supports, transport both hypotheses up to it via the enlargement *iff*, chain the
equalities in `M`, and descend back to the `(t,v)`-support. -/
theorem LocalEMContext.trans (ctx : LocalEMContext Λ J (M := M))
    {t u v : Λ[[J]].Term Empty}
    (h1 : LocalEMEq Λ J ctx.a t u) (h2 : LocalEMEq Λ J ctx.a u v) : LocalEMEq Λ J ctx.a t v := by
  set S := locJSupport Λ J t ∪ locJSupport Λ J u ∪ locJSupport Λ J v with hSdef
  have hsub_tu : locJSupport Λ J t ∪ locJSupport Λ J u ⊆ S := Finset.subset_union_left
  have hsub_uv : locJSupport Λ J u ∪ locJSupport Λ J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_right).trans Finset.subset_union_left) Finset.subset_union_right
  have hsub_tv : locJSupport Λ J t ∪ locJSupport Λ J v ⊆ S :=
    Finset.union_subset
      ((Finset.subset_union_left).trans Finset.subset_union_left) Finset.subset_union_right
  have iff_tu := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ t u Finset.subset_union_left Finset.subset_union_right) hsub_tu
  have iff_uv := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ u v Finset.subset_union_left Finset.subset_union_right) hsub_uv
  have iff_tv := eventually_locDeepInterp_superset_iff Λ J ctx.a ctx.hind
    (ctx.atom_mem _ t v Finset.subset_union_left Finset.subset_union_right) hsub_tv
  have hS_tu := (h1.and iff_tu).mono (fun _ p => p.2.mp p.1)
  have hS_uv := (h2.and iff_uv).mono (fun _ p => p.2.mp p.1)
  have hS_tv := (hS_tu.and hS_uv).mono (fun _ p => p.1.trans p.2)
  exact (iff_tv.and hS_tv).mono (fun _ p => p.1.mpr p.2)

/-- `LocalEMEq` is an equivalence relation on closed terms (refl/symm need no context; trans is
`LocalEMContext.trans`). -/
def LocalEMContext.setoid (ctx : LocalEMContext Λ J (M := M)) :
    Setoid (Λ[[J]].Term Empty) where
  r := LocalEMEq Λ J ctx.a
  iseqv := ⟨fun t => LocalEMEq.refl Λ J ctx.a t, fun h => LocalEMEq.symm Λ J ctx.a h,
    fun h1 h2 => LocalEMContext.trans (Λ := Λ) (J := J) ctx h1 h2⟩

/-- The **local EM term-model carrier** for a context: closed `Λ[[J]]`-terms modulo `LocalEMEq`. -/
def LocalEMContext.Carrier (ctx : LocalEMContext Λ J (M := M)) : Type :=
  Quotient ctx.setoid

/-- A common support covering all argument representatives — the support over which a relation's deep
truth is read. -/
noncomputable def LocalEMContext.commonSupport (ctx : LocalEMContext Λ J (M := M)) {n : ℕ}
    (xs : Fin n → ctx.Carrier) : Finset J :=
  Finset.univ.biUnion fun i => locJSupport Λ J (Quotient.out (xs i))

/-- The **local EM term-model structure** on the carrier: function symbols act by term formation
`f([t̄]) := [func f t̄]` (skeleton constants are the arity-0 case), and a relation holds iff it holds
in `M` on the deep interpretations for all sufficiently deep `d` (read over a common support of the
arguments). Well-definedness is proved separately via the enlargement-invariance congruence engine. -/
@[reducible] noncomputable def LocalEMContext.structure (ctx : LocalEMContext Λ J (M := M)) :
    Λ[[J]].Structure ctx.Carrier where
  funMap {_} f xs := Quotient.mk ctx.setoid (Term.func f fun i => Quotient.out (xs i))
  RelMap {n} R xs :=
    ∀ᶠ d in Filter.atTop,
      letI : (constantsOn J).Structure M :=
        constantsOn.structure fun j => ctx.a (d + deepRank J (ctx.commonSupport (xs := xs)) j)
      @Structure.RelMap (Λ[[J]]) M _ n R
        fun i => locDeepInterp Λ J ctx.a d (ctx.commonSupport (xs := xs)) (Quotient.out (xs i))

/-- The **base `Λ`-structure** on the carrier: the reduct of the term-model `[[J]]`-structure along
the skeleton-constant inclusion (a base function/relation symbol acts as its `Sum.inl` image). -/
@[reducible] noncomputable def LocalEMContext.structureBase (ctx : LocalEMContext Λ J (M := M)) :
    Λ.Structure ctx.Carrier where
  funMap {n} f xs := @Structure.funMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl f) xs
  RelMap {n} R xs := @Structure.RelMap (Λ[[J]]) ctx.Carrier ctx.structure n (Sum.inl R) xs

end Quotient

end FirstOrder.Language
