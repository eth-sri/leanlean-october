/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import InfinitaryLogic.Scott.AtomicDiagram

@[expose] public section

namespace VaughtConjecture.Knight

open FirstOrder Language Structure TypeTower

universe w w'

/-- The relational chart language at a limit stage `α`, with one `n`-ary relation for each
stage type in `S α n`. -/
def stageLang (α : LimitStage) : Language.{0, 1} where
  Functions _ := Empty
  Relations n := S α.1 n

instance stageLang.isRelational (α : LimitStage) : (stageLang α).IsRelational :=
  fun _ => inferInstanceAs (IsEmpty Empty)

/-- The relation `P_p` holds of a tuple in a stage chart structure. -/
abbrev StageHolds {α : LimitStage} {M : Type w} [(stageLang α).Structure M] {n : ℕ}
    (p : S α.1 n) (xs : Fin n → M) : Prop :=
  RelMap (L := stageLang α) (n := n) p xs

/-- The chart-language structure associated to a Knight realization: `P_p(x̄)` means that
`x̄` is injective and the realization labels it by `p`. -/
@[instance_reducible] noncomputable def stageStructureOf {α : LimitStage} {M : Type w}
    (R : KnightRealization α M) : (stageLang α).Structure M where
  funMap f := isEmptyElim f
  RelMap p xs := ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some p

theorem stageHolds_stageStructureOf {α : LimitStage} {M : Type w}
    (R : KnightRealization α M) {n : ℕ} (p : S α.1 n) (xs : Fin n → M) :
    @StageHolds α M (stageStructureOf R) n p xs ↔
      ∃ h : Function.Injective xs, R.eval ⟨xs, h⟩ = some p :=
  Iff.rfl

/-- The stage chart encoding reflects isomorphisms: an isomorphism of chart structures already
transports every `Option`-valued realization label.  No modelhood or transfer hypothesis is
needed. -/
theorem isIsoOfStageStructureEquiv {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (e : @Language.Equiv (stageLang α) M N (stageStructureOf R) (stageStructureOf R')) :
    R.IsIso R'
      (@Language.Equiv.toEquiv (stageLang α) M N (stageStructureOf R) (stageStructureOf R') e) := by
  let instM : (stageLang α).Structure M := stageStructureOf R
  let instN : (stageLang α).Structure N := stageStructureOf R'
  let e' : M ≃[stageLang α] N := e
  intro n t
  let ee : M ≃ N := e'.toEquiv
  have key : ∀ p : S α.1 n,
      @StageHolds α N instN n p (⇑e' ∘ ⇑t) ↔ @StageHolds α M instM n p t :=
    fun p => StrongHomClass.map_rel e' p t
  change R'.eval (t.trans ee.toEmbedding) = R.eval t
  apply Option.ext
  intro p
  constructor
  · intro ht
    have htarget : @StageHolds α N instN n p (⇑e' ∘ ⇑t) := by
      refine ⟨e'.toEquiv.injective.comp t.injective, ?_⟩
      solve_by_elim
    obtain ⟨hsrc, hsource⟩ := (key p).mp htarget
    solve_by_elim
  · intro hs
    have hsource : @StageHolds α M instM n p t := ⟨t.injective, hs⟩
    obtain ⟨htgt, htarget⟩ := (key p).mpr hsource
    solve_by_elim

/-- Exact face consistency determines every relation atom on every (possibly repeated)
subtuple of a labelled injective tuple.  A visible face gives its unique pulled-back label;
an invisible face gives no label (a *negative* atomic fact), and a repeated subtuple satisfies
no chart relation.  Visible-face consistency alone would not prove the negative facts. -/
theorem stageHolds_comp_iff_of_eval {α : LimitStage} {M : Type w}
    {R : KnightRealization α M} (hR : R.IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n} (ht : R.eval t = some p)
    {m : ℕ} (q : S α.1 m) (f : Fin m → Fin n) :
    @StageHolds α M (stageStructureOf R) m q (t ∘ f) ↔
      ∃ hf : Function.Injective f, typeMap ⟨f, hf⟩ p = some q := by
  rw [stageHolds_stageStructureOf]
  constructor
  · rintro ⟨htf, hq⟩
    have hf : Function.Injective f := fun i j hij => by aesop
    refine ⟨hf, ?_⟩
    have hface := hR t p (⟨f, hf⟩ : Fin m ↪ Fin n) ht
    have he : (⟨t ∘ f, htf⟩ : Fin m ↪ M) = (⟨f, hf⟩ : Fin m ↪ Fin n).trans t := by
      ext i
      rfl
    simp_all
  · rintro ⟨hf, hq⟩
    have htf : Function.Injective (t ∘ f) := t.injective.comp hf
    refine ⟨htf, ?_⟩
    have hface := hR t p (⟨f, hf⟩ : Fin m ↪ Fin n) ht
    aesop

/-- Two labelled tuples carrying the same full chart have the same atomic chart-language type.
This includes equality atoms, repeated relation tuples, and invisible faces. -/
theorem sameAtomicType_of_eval_eq_some {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    {n : ℕ} {a : Fin n ↪ M} {b : Fin n ↪ N} {p : S α.1 n}
    (ha : R.eval a = some p) (hb : R'.eval b = some p) :
    @SameAtomicType (stageLang α) M (stageStructureOf R) n N (stageStructureOf R') a b := by
  intro idx
  cases idx with
  | eq i j =>
      simp only [AtomicIdx.holds]
      simp
  | rel q f =>
      exact (stageHolds_comp_iff_of_eval hR ha q f).trans
        (stageHolds_comp_iff_of_eval hR' hb q f).symm

/-- A common projected chart for two tuples: each tuple is the same coordinate projection of
an injective tuple carrying one common full chart.  The selector may repeat coordinates, so this
also covers arbitrary finite tuples rather than only embeddings. -/
def HasCommonChart {α : LimitStage} {M : Type w} {N : Type w'}
    (R : KnightRealization α M) (R' : KnightRealization α N) {n : ℕ}
    (a : Fin n → M) (b : Fin n → N) : Prop :=
  ∃ (m : ℕ) (ta : Fin m ↪ M) (tb : Fin m ↪ N) (σ : Fin n → Fin m) (p : S α.1 m),
    R.eval ta = some p ∧ R'.eval tb = some p ∧ ta ∘ σ = a ∧ tb ∘ σ = b

/-- Common projected charts determine the complete atomic diagram in the chart language. -/
theorem sameAtomicType_of_commonChart {α : LimitStage} {M : Type w} {N : Type w'}
    {R : KnightRealization α M} {R' : KnightRealization α N}
    (hR : R.IsExactParentConsistent) (hR' : R'.IsExactParentConsistent)
    {n : ℕ} {a : Fin n → M} {b : Fin n → N} (h : HasCommonChart R R' a b) :
    @SameAtomicType (stageLang α) M (stageStructureOf R) n N (stageStructureOf R') a b := by
  let instM : (stageLang α).Structure M := stageStructureOf R
  let instN : (stageLang α).Structure N := stageStructureOf R'
  obtain ⟨m, ta, tb, σ, p, hta, htb, ha, hb⟩ := h
  have hfull := (sameAtomicType_of_eval_eq_some hR hR' hta htb).relabel σ
  simp_all

end VaughtConjecture.Knight
