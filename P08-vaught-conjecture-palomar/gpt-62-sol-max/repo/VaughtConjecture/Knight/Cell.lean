/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import VaughtConjecture.AmalgamationPlan.Plan
public import VaughtConjecture.Knight.Value

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open scoped Cardinal

variable {ι : Type*}

/-- The product preorder on graded indices `(B, j)` (cf. Knight, Def. 2.5.1): `X ≤ Y` iff the
scope of `X` is contained in that of `Y` and the grade of `X` is at most that of `Y`. -/
def GradedLe (X Y : Finset ι × ℕ) : Prop :=
  X.1 ⊆ Y.1 ∧ X.2 ≤ Y.2

theorem GradedLe.antisymm' {κ : Type*} {X Y : Finset κ × ℕ} (h₁ : GradedLe X Y)
    (h₂ : GradedLe Y X) :
    X = Y :=
  Prod.ext (Finset.Subset.antisymm h₁.1 h₂.1) (le_antisymm h₁.2 h₂.2)

theorem GradedLe.refl (X : Finset ι × ℕ) : GradedLe X X :=
  ⟨Finset.Subset.refl _, le_rfl⟩

theorem GradedLe.trans {X Y Z : Finset ι × ℕ} (hXY : GradedLe X Y) (hYZ : GradedLe Y Z) :
    GradedLe X Z :=
  ⟨hXY.1.trans hYZ.1, hXY.2.trans hYZ.2⟩

variable [DecidableEq ι]

/-- A **cell scheme** on the finite set `A` (Knight's "domain" of a type, Defs. 2.4.*/2.5.*):
a support plan `plan` on `A` and `card` cells, the `d`-th cell having graded index
`cell d = (scope, grade)` in the graded plan `P̂`.  The cells are indexed by `Fin card`, so
schemes with the same `plan`, `card` and `cell` are definitionally equal. -/
structure CellScheme (A : Finset ι) where
  /-- The support plan of the scheme. -/
  plan : Finset (Finset ι)
  /-- `plan` is a support plan on `A`. -/
  isPlan : Plan.IsPlan A plan
  /-- The number of cells. -/
  card : ℕ
  /-- The graded index (scope, grade) of each cell. -/
  cell : Fin card → (Finset ι × ℕ)
  /-- Every cell's graded index lies in the graded plan `P̂`. -/
  cell_mem : ∀ d : Fin card, cell d ∈ Plan.gradedPlan plan

/-- The cells of a scheme `D`: the canonical index type `Fin D.card`. -/
abbrev Cell {A : Finset ι} (D : CellScheme A) : Type := Fin D.card

namespace CellScheme

variable {A : Finset ι} (D : CellScheme A)

/-- The **scope** of a cell: the visible face it sees. -/
def scope (d : Cell D) : Finset ι := (D.cell d).1

/-- The **grade** of a cell (Knight's "arity" of the cell): its graded index `j`. -/
def grade (d : Cell D) : ℕ := (D.cell d).2

@[simp] theorem cell_eq (d : Cell D) : D.cell d = (D.scope d, D.grade d) := rfl

/-- The scope of a cell is a visible face of the plan. -/
theorem scope_mem_plan (d : Cell D) : D.scope d ∈ D.plan :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).1

theorem scope_subset (d : Cell D) : D.scope d ⊆ A :=
  D.isPlan.subset_of_mem (D.scope_mem_plan d)

/-- The grade of a cell is positive. -/
theorem grade_pos (d : Cell D) : 0 < D.grade d :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).2.1

/-- The grade of a cell is at most the size of its scope. -/
theorem grade_le_card_scope (d : Cell D) : D.grade d ≤ (D.scope d).card :=
  (Plan.mem_gradedPlan.mp (D.cell_mem d)).2.2

/-- The lower set of cells whose graded index lies below `BJ` (Knight-VC's `restrict`;
Def. 2.5.2 style).  This is a lower set in the graded preorder `GradedLe`, not a face
restriction of the scheme.  The semantic row of a cell `Sig` lives on `D.below (D.cell Sig)`. -/
def below (BJ : Finset ι × ℕ) : Type :=
  { d : Cell D // GradedLe (D.cell d) BJ }

/-- Restrict an equivalence of occurrences to smaller grade cuts. -/
def restrictBelowEquiv {κ : Type*} [DecidableEq κ] {A' : Finset κ} {D' : CellScheme A'}
    {S : Finset ι} {T : Finset κ} {k l i j : ℕ}
    (e : D.below (S, k) ≃ D'.below (T, l)) (hi : i ≤ k) (hj : j ≤ l)
    (he : ∀ a : D.below (S, k), D.grade a.1 ≤ i ↔ D'.grade (e a).1 ≤ j) :
    D.below (S, i) ≃ D'.below (T, j) where
  toFun a :=
    let x : D.below (S, k) := ⟨a.1, a.2.1, a.2.2.trans hi⟩
    ⟨(e x).1, (e x).2.1, (he x).mp a.2.2⟩
  invFun b :=
    let y : D'.below (T, l) := ⟨b.1, b.2.1, b.2.2.trans hj⟩
    ⟨(e.symm y).1, (e.symm y).2.1, (he (e.symm y)).mpr (by rw [e.apply_symm_apply]; exact b.2.2)⟩
  left_inv a := by
    apply Subtype.ext
    change (e.symm (e (⟨a.1, a.2.1, a.2.2.trans hi⟩ : D.below (S, k)))).1 = a.1
    exact congrArg Subtype.val (e.symm_apply_apply _)
  right_inv b := by
    apply Subtype.ext
    change (e (e.symm (⟨b.1, b.2.1, b.2.2.trans hj⟩ : D'.below (T, l)))).1 = b.1
    exact congrArg Subtype.val (e.apply_symm_apply _)


/-- `D.below BJ` is finite: a subtype of the finite index type `Cell D`.  (Stated explicitly
because `below` is not reducible.) -/
instance finite_below (BJ : Finset ι × ℕ) : Finite (D.below BJ) := by
  unfold below
  exact Subtype.finite

/-- The cell schemes over `Fin n` form a countable type: all data fields are `Finset`/`ℕ`
data (`isPlan` and `cell_mem` are proofs), so the scheme injects into
`Finset (Finset (Fin n)) × Σ c, (Fin c → Finset (Fin n) × ℕ)`. -/
instance countable_fin (n : ℕ) :
    Countable (CellScheme (ι := Fin n) (Finset.univ : Finset (Fin n))) := by
  let f : CellScheme (ι := Fin n) (Finset.univ : Finset (Fin n)) →
      Finset (Finset (Fin n)) × (Σ c : ℕ, Fin c → (Finset (Fin n) × ℕ)) :=
    fun d => (d.plan, ⟨d.card, d.cell⟩)
  have hinj : Function.Injective f := by
    rintro ⟨p1, ip1, c1, cl1, cm1⟩ ⟨p2, ip2, c2, cl2, cm2⟩ h
    aesop
  exact hinj.countable

end CellScheme

/-- Ordinals `≤ α` form a countable set when `α.card ≤ ℵ₀`: `Set.Iic α ⊆ Set.Iio (α + 1)` and
`#(Set.Iio (α + 1)) = lift (α + 1).card ≤ ℵ₀` (`Cardinal.mk_Iio_ordinal`). -/
theorem Ordinal.countable_Iic_of_card_le_aleph0 {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    (Set.Iic α).Countable := by
  rw [← Set.countable_coe_iff, ← Cardinal.mk_le_aleph0_iff]
  have hsucc : (Order.succ α).card ≤ ℵ₀ := by
    simp_all
  calc #(Set.Iic α) ≤ #(Set.Iio (Order.succ α)) :=
        Cardinal.mk_le_mk_of_subset
          (fun β hβ => Set.mem_Iio.mpr (Order.lt_succ_iff.mpr (Set.mem_Iic.mp hβ)))
    _ = Cardinal.lift.{1} (Order.succ α).card := Cardinal.mk_Iio_ordinal _
    _ ≤ ℵ₀ := by rw [Cardinal.lift_le_aleph0]; assumption

/-- The labels non-strictly bounded at a countable stage `α` (`x ≤ ofOrd α ∨ x = ⊤`) form a
countable type: they lie in `{⊤, ⊥} ∪ ofOrd '' Set.Iic α`.  (The stage types use the strict
bound, `ExtOrd.countable_bounded_lt` below.) -/
theorem ExtOrd.countable_bounded {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    Countable {x : ExtOrd // x ≤ ExtOrd.ofOrd α ∨ x = ⊤} := by
  have key : {x : ExtOrd | x ≤ ExtOrd.ofOrd α ∨ x = ⊤}
      ⊆ insert ⊤ (insert ⊥ (ExtOrd.ofOrd '' Set.Iic α)) := by
    rintro x (hle | htop)
    · rcases ExtOrd.cases x with rfl | rfl | ⟨β, rfl⟩
      all_goals simp_all
    tauto
  have hc : (insert (⊤ : ExtOrd) (insert ⊥ (ExtOrd.ofOrd '' Set.Iic α))).Countable :=
    (((Ordinal.countable_Iic_of_card_le_aleph0 hα).image _).insert _).insert _
  exact (hc.mono key).to_subtype

/-- The labels **strictly** bounded at a countable stage `α` (`x < ofOrd α ∨ x = ⊤`, the label
bound of a stage-`α` type under the strict convention of #84) form a countable type: they
inject into the non-strictly bounded labels of `ExtOrd.countable_bounded`. -/
theorem ExtOrd.countable_bounded_lt {α : Ordinal.{0}} (hα : α.card ≤ ℵ₀) :
    Countable {x : ExtOrd // x < ExtOrd.ofOrd α ∨ x = ⊤} := by
  have := ExtOrd.countable_bounded hα
  exact Function.Injective.countable
    (f := fun x : {x : ExtOrd // x < ExtOrd.ofOrd α ∨ x = ⊤} =>
      (⟨x.1, x.2.imp le_of_lt id⟩ : {x : ExtOrd // x ≤ ExtOrd.ofOrd α ∨ x = ⊤}))
    fun _ _ h => Subtype.ext (Subtype.mk.inj h)

namespace CellScheme

variable {m n : ℕ} (D : CellScheme (ι := Fin n) Finset.univ) (f : Fin m ↪ Fin n)

/-- The cells of `D` **visible through** `f`: those whose scope lies in the range of `f`. -/
def visibleCells : Finset (Cell D) :=
  Finset.univ.filter (fun d => D.scope d ⊆ Finset.univ.image f)

theorem mem_visibleCells {d : Cell D} :
    d ∈ D.visibleCells f ↔ D.scope d ⊆ Finset.univ.image f := by
  simp [visibleCells]

/-- The graded index of a cell of `D` pulled back along `f`: the preimage of its scope under
`f`, with the same grade. -/
def pullCell (d : Cell D) : Finset (Fin m) × ℕ :=
  (Finset.univ.filter (fun i => f i ∈ D.scope d), D.grade d)

/-- The pulled-back scope maps back onto the original scope when the latter is visible. -/
theorem image_pullCell_fst {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    (D.pullCell f d).1.image f = D.scope d := by grind [pullCell]

theorem card_pullCell_fst {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    (D.pullCell f d).1.card = (D.scope d).card := by
  rw [← Finset.card_image_of_injective _ f.injective, image_pullCell_fst D f hd]

/-- The graded preorder is reflected by pulling back visible cells. -/
theorem gradedLe_pullCell_iff {a b : Cell D} (ha : D.scope a ⊆ Finset.univ.image f) :
    GradedLe (D.pullCell f a) (D.pullCell f b) ↔ GradedLe (D.cell a) (D.cell b) := by
  simp only [GradedLe, pullCell, cell_eq]
  refine and_congr_left' ⟨fun h x hx => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp (ha hx)
    exact (Finset.mem_filter.mp (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))).2
  aesop

/-- The **face restriction** of a cell scheme along `f : Fin m ↪ Fin n` whose range is a
visible face (Knight, Def. 3.1.5; the scheme part of Knight-VC `typeMap`): the pullback plan
`{C ⊆ Fin m | f[C] ∈ D.plan}`, and the cells of `D` visible through `f`, pulled back along `f`
and enumerated in increasing order. -/
noncomputable def restrictFace (hr : Finset.univ.image f ∈ D.plan) :
    CellScheme (ι := Fin m) Finset.univ where
  plan := (Finset.univ : Finset (Fin m)).powerset.filter (fun C => C.image f ∈ D.plan)
  isPlan := Plan.pullback_isPlan_fin f D.isPlan hr
  card := (D.visibleCells f).card
  cell i := D.pullCell f ((D.visibleCells f).orderEmbOfFin rfl i)
  cell_mem i := by
    have hvis := (D.mem_visibleCells f).mp ((D.visibleCells f).orderEmbOfFin_mem rfl i)
    refine Plan.mem_gradedPlan.mpr ⟨?_, D.grade_pos _, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        by rw [image_pullCell_fst D f hvis]; exact D.scope_mem_plan _⟩
    · rw [card_pullCell_fst D f hvis]; exact D.grade_le_card_scope _

variable (hr : Finset.univ.image f ∈ D.plan)

theorem restrictFace_plan :
    (D.restrictFace f hr).plan =
      (Finset.univ : Finset (Fin m)).powerset.filter (fun C => C.image f ∈ D.plan) := rfl

/-- The plan of the restriction is the (defined) pullback plan. -/
theorem pullbackPlan_eq_restrictFace_plan :
    Plan.pullbackPlan f D.plan = some (D.restrictFace f hr).plan :=
  Plan.pullbackPlan_eq_some f hr

/-- Membership in the restricted plan: a face of `Fin m` is visible iff its image is. -/
theorem mem_restrictFace_plan {C : Finset (Fin m)} :
    C ∈ (D.restrictFace f hr).plan ↔ C.image f ∈ D.plan := by
  simp [restrictFace_plan]

theorem card_restrictFace : (D.restrictFace f hr).card = (D.visibleCells f).card := rfl

namespace restrictFace

/-- The cell map of a face restriction: the `i`-th cell of `D.restrictFace f hr` is the `i`-th
visible cell of `D` in increasing order (Knight-VC: `canonEquivFin` of the visible subtype). -/
noncomputable def toCell : Cell (D.restrictFace f hr) ↪o Cell D :=
  (D.visibleCells f).orderEmbOfFin (D.card_restrictFace f hr).symm

theorem scope_toCell_subset (i : Cell (D.restrictFace f hr)) :
    D.scope (toCell D f hr i) ⊆ Finset.univ.image f :=
  (D.mem_visibleCells f).mp ((D.visibleCells f).orderEmbOfFin_mem _ i)

theorem toCell_strictMono : StrictMono (toCell D f hr) := (toCell D f hr).strictMono

theorem toCell_injective : Function.Injective (toCell D f hr) := (toCell D f hr).injective

/-- Every visible cell of `D` is hit by the cell map. -/
theorem exists_toCell_eq {d : Cell D} (hd : D.scope d ⊆ Finset.univ.image f) :
    ∃ i, toCell D f hr i = d := by
  have hmem : d ∈ Set.range (toCell D f hr) := by
    rw [toCell, Finset.range_orderEmbOfFin]; exact (D.mem_visibleCells f).mpr hd
  assumption

theorem cell_eq (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).cell i = D.pullCell f (toCell D f hr i) := rfl

@[simp] theorem scope_restrictFace (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).scope i =
      Finset.univ.filter (fun j => f j ∈ D.scope (toCell D f hr i)) := rfl

@[simp] theorem grade_restrictFace (i : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).grade i = D.grade (toCell D f hr i) := rfl

/-- The image under `f` of a restricted scope is the original scope. -/
theorem image_scope_restrictFace (i : Cell (D.restrictFace f hr)) :
    ((D.restrictFace f hr).scope i).image f = D.scope (toCell D f hr i) :=
  (by solve_by_elim [image_pullCell_fst, scope_toCell_subset])

/-- The graded preorder of the restriction is the graded preorder of `D` on the visible
cells. -/
theorem gradedLe_restrictFace_iff {i j : Cell (D.restrictFace f hr)} :
    GradedLe ((D.restrictFace f hr).cell i) ((D.restrictFace f hr).cell j) ↔
      GradedLe (D.cell (toCell D f hr i)) (D.cell (toCell D f hr j)) :=
  (by solve_by_elim [gradedLe_pullCell_iff, scope_toCell_subset])

/-- Knight-VC `gradedLe_pullback_to_orig`. -/
theorem gradedLe_of_restrictFace {i j : Cell (D.restrictFace f hr)}
    (h : GradedLe ((D.restrictFace f hr).cell i) ((D.restrictFace f hr).cell j)) :
    GradedLe (D.cell (toCell D f hr i)) (D.cell (toCell D f hr j)) :=
  (by grind [gradedLe_restrictFace_iff])

/-- Transport of the lower set below a restricted cell `Sig` into the lower set below
`toCell Sig` in `D` (the index map of the semantic rows). -/
noncomputable def belowMap (Sig : Cell (D.restrictFace f hr)) :
    (D.restrictFace f hr).below ((D.restrictFace f hr).cell Sig) →
      D.below (D.cell (toCell D f hr Sig)) :=
  fun d => ⟨toCell D f hr d.1, gradedLe_of_restrictFace D f hr d.2⟩

section Emb

variable {k : ℕ} {e : Fin k → Cell D}

theorem visibleCells_eq_image_of_emb (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hsurj : ∀ d, D.scope d ⊆ Finset.univ.image f → ∃ c, e c = d) :
    D.visibleCells f = Finset.univ.image e := by grind [mem_visibleCells]

theorem card_restrictFace_of_emb (he : StrictMono e)
    (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hsurj : ∀ d, D.scope d ⊆ Finset.univ.image f → ∃ c, e c = d) :
    (D.restrictFace f hr).card = k := by
  rw [card_restrictFace, visibleCells_eq_image_of_emb D f hvis hsurj,
    Finset.card_image_of_injective _ he.injective, Finset.card_univ, Fintype.card_fin]

theorem toCell_cast_eq_of_emb (he : StrictMono e)
    (hvis : ∀ c, D.scope (e c) ⊆ Finset.univ.image f)
    (hk : (D.restrictFace f hr).card = k) (c : Fin k) :
    toCell D f hr (Fin.cast hk.symm c) = e c := by
  have hk' : (D.visibleCells f).card = k := hk
  rw [Finset.orderEmbOfFin_unique hk' (fun c => (D.mem_visibleCells f).mpr (hvis c)) he, toCell,
    Finset.orderEmbOfFin_eq_orderEmbOfFin_iff, Fin.val_cast]

end Emb

end restrictFace

end CellScheme

end VaughtConjecture.Knight
