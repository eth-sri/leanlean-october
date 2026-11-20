/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Mathlib.Order.Lattice.Nat
public import VaughtConjecture.Knight.Model

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd VaughtConjecture.AmalgamationPlan

open CellScheme.restrictFace (toCell)

universe w w'

namespace StageType

variable {α : Ordinal.{0}} {m n : ℕ}

/-- If `typeMap f q = some p`, the range of `f` is a visible face of the plan of `q`. -/
theorem visible_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : Finset.univ.image f ∈ q.scheme.scheme.plan :=
  (typeMap_isSome_iff f q).mp (by simp_all)

/-- If `typeMap f q = some p`, then `p` is the face restriction of `q` along `f`. -/
theorem restrictFace_eq_of_typeMap_eq_some {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) : q.restrictFace f (visible_of_typeMap_eq_some h) = p := by
  have h' := typeMap_eq_some f q (visible_of_typeMap_eq_some h)
  simp_all

/-- The cell of `q` underlying a cell of its restriction `p` (the paper's `Ξ ∈ dom p ⊆ dom q`):
transport along the restriction equation, then the cell map `toCell` of the face
restriction. -/
noncomputable def mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) : Cell q.scheme.scheme :=
  toCell q.scheme.scheme f (visible_of_typeMap_eq_some h)
    (SemScheme.castCell (congrArg StageType.scheme (restrictFace_eq_of_typeMap_eq_some h).symm)
      Xi)

/-- The label of the underlying cell is the label of the restricted cell (Def. 3.2.5: the
cells of `dom p` carry the same values in `q`). -/
theorem label_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    q.label (mapCell h Xi) = p.label Xi := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  rfl

/-- The grade of the underlying cell is the grade of the restricted cell. -/
theorem grade_mapCell {q : S α n} {p : S α m} {f : Fin m ↪ Fin n}
    (h : typeMap f q = some p) (Xi : Cell p.scheme.scheme) :
    q.scheme.scheme.grade (mapCell h Xi) = p.scheme.scheme.grade Xi := by
  obtain ⟨hr, rfl⟩ : ∃ hr, q.restrictFace f hr = p :=
    ⟨visible_of_typeMap_eq_some h, restrictFace_eq_of_typeMap_eq_some h⟩
  rfl

/-- The grades of full-scope cells labelled `∞`: the set whose supremum is the paper's `K^p`
(Def. 5.3.1 clause 2: "`K^p` is the greatest natural number such that for some
`Θ ∈ D^{A,K^p}`, `p(Θ) = ∞`"). -/
def topGrades (p : S α n) : Set ℕ :=
  {k | ∃ Θ : Cell p.scheme.scheme, p.scheme.scheme.scope Θ = Finset.univ ∧
    p.scheme.scheme.grade Θ = k ∧ p.label Θ = ⊤}

theorem topGrades_bddAbove (p : S α n) : BddAbove p.topGrades := by
  refine ⟨n, fun k hk => ?_⟩
  obtain ⟨Θ, hsc, rfl, -⟩ := hk
  have h1 := p.scheme.scheme.grade_le_card_scope Θ
  simp_all

/-- The paper's `K^p` (Def. 5.3.1): the greatest grade of a full-scope `∞`-cell (`0` when
there is none — under clause 2 the set is nonempty, `grade_mem_topGrades`). -/
noncomputable def topGrade (p : S α n) : ℕ := sSup p.topGrades

/-- If any cell of `p` is labelled `∞`, some full-scope cell of the same grade is labelled `∞`
(availability, Def. 2.5.4(2), against the full-scope cell of that grade provided by
completeness, Def. 2.5.15) — so the defining set of `K^p` is nonempty whenever clause 2 of
Def. 5.3.1 applies. -/
theorem grade_mem_topGrades {p : S α n} {Xi : Cell p.scheme.scheme} (hXi : p.label Xi = ⊤) :
    p.scheme.scheme.grade Xi ∈ p.topGrades := by
  have hmem : ((Finset.univ : Finset (Fin n)), p.scheme.scheme.grade Xi) ∈
      Plan.gradedPlan p.scheme.scheme.plan := by
    refine Plan.mem_gradedPlan.mpr
      ⟨p.scheme.scheme.isPlan.domain_mem, p.scheme.scheme.grade_pos Xi, ?_⟩
    have h1 := p.scheme.scheme.grade_le_card_scope Xi
    exact h1.trans (Finset.card_le_card (Finset.subset_univ _))
  obtain ⟨d, hd⟩ := p.scheme.complete _ hmem
  have hd' := Prod.ext_iff.mp hd
  have hscope : p.scheme.scheme.scope Xi ⊆ p.scheme.scheme.scope d := by
    simp_all
  have hgrade : p.scheme.scheme.grade Xi = p.scheme.scheme.grade d := hd'.2.symm
  obtain ⟨Xi', hcell, hle⟩ := p.respects.availability Xi d hscope hgrade
  have hXi' := Prod.ext_iff.mp (hcell.trans hd)
  refine ⟨Xi', hXi'.1, hXi'.2, ?_⟩
  simp_all

/-- Clause 2.(a) of Def. 5.3.1: some full-scope `∞`-cell `Θ` of grade `K^p` sees, below
itself, an `∞`-cell `Σ` with `E(Θ)(Σ) ⊔⁺_{K^p} K^p ≤ E(Θ)(Ξ)` — the evidence in `p` that
`M⁺(Ξ)` is at least `α + K^p`.  Then `p⁺(Ξ) = α + K^p`. -/
def ProvisionalCap (p : S α n) (Xi : Cell p.scheme.scheme) : Prop :=
  ∃ (Θ : Cell p.scheme.scheme)
    (hXi : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ))
    (Sig : p.scheme.scheme.below (p.scheme.scheme.cell Θ)),
    p.scheme.scheme.scope Θ = Finset.univ ∧ p.scheme.scheme.grade Θ = p.topGrade ∧
    p.label Θ = ⊤ ∧ p.label Sig.1 = ⊤ ∧
    extVisibilityReplace (p.scheme.rows.E Θ Sig) p.topGrade p.topGrade ≤
      p.scheme.rows.E Θ ⟨Xi, hXi⟩

/-- Clause 2.(b) of Def. 5.3.1: some full-scope `∞`-cell `Θ` of grade `K^p` has
`E(Θ)(Ξ) = E(Θ)(Ξ) ⊔⁺_{K^p} i` — the row pins the value `α + i`.  Then `p⁺(Ξ) = α + i`.
(Independence of `i` from `Θ` is Lemma 5.3.2, a consistency theorem — not needed here:
`someProvisionalValue` selects the least band index, and under `¬ ProvisionalCap` every witness
forces `i < K^p`, `ProvisionalBand.lt_topGrade`.) -/
def ProvisionalBand (p : S α n) (Xi : Cell p.scheme.scheme) (i : ℕ) : Prop :=
  ∃ (Θ : Cell p.scheme.scheme)
    (hXi : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ)),
    p.scheme.scheme.scope Θ = Finset.univ ∧ p.scheme.scheme.grade Θ = p.topGrade ∧
    p.label Θ = ⊤ ∧
    p.scheme.rows.E Θ ⟨Xi, hXi⟩ =
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXi⟩) p.topGrade i

/-- **A provisional value `p⁺(Ξ)`** (Def. 5.3.1, cell-dependent — not Knight-VC's uniform
`topLiftType` cap, KVC-d3): clause 1 keeps the label when it is not `∞`; clause 2.(a) caps at
`α + K^p`; clause 2.(b) reads the **least** band index off a witnessing row.  The final `⊤`
branch is unreachable (`exists_provisionalBand`, `someProvisionalValue_ne_top`): the paper leaves
clause 2 partial and the totality is availability + completeness.

This function is a **witness/chooser**, not the primary interface: the API works with the
relation `IsProvisionalValue` (Def. 5.3.1 as a graph), and this chooser only discharges its
totality (`isProvisionalValue_someProvisionalValue`).  Band-index independence (Lemma 5.3.2,
`ProvisionalBand.unique` in `Knight/ProvisionalUniqueness.lean`) makes the relation
single-valued, so the chooser computes *the* value (`isProvisionalValue_iff`). -/
noncomputable def someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) : ExtOrd :=
  open Classical in
  if p.label Xi = ⊤ then
    if p.ProvisionalCap Xi then ofOrd (α + p.topGrade)
    else if h : ∃ i, p.ProvisionalBand Xi i then ofOrd (α + Nat.find h)
    else ⊤
  else p.label Xi

theorem someProvisionalValue_of_ne_top {p : S α n} {Xi : Cell p.scheme.scheme}
    (h : p.label Xi ≠ ⊤) : p.someProvisionalValue Xi = p.label Xi := by
  unfold someProvisionalValue
  simp_all

theorem someProvisionalValue_of_cap {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : p.ProvisionalCap Xi) :
    p.someProvisionalValue Xi = ofOrd (α + p.topGrade) := by
  unfold someProvisionalValue
  simp_all

/-- **Clause 2 of Def. 5.3.1 is total**: if `p(Ξ) = ∞` and clause 2.(a) does not apply, some
band witnesses clause 2.(b).  Proof: `K^p ∈ topGrades` (`grade_mem_topGrades` at `Ξ` plus
`Nat.sSup_mem`) provides a full-scope `∞`-cell `Θ` of grade `K^p` with `Ξ` below it; the row
value `E(Θ)(Ξ)` cannot be `-∞`, `∞`, or self-visible at `K^p` (each would fire clause 2.(a)
with `Σ := Ξ`), so it is an ordinal with finite part `< K^p`, and that finite part is the
band. -/
theorem exists_provisionalBand {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    ∃ i, p.ProvisionalBand Xi i := by
  have hmem := grade_mem_topGrades htop
  have hbdd := p.topGrades_bddAbove
  have hK : p.topGrade ∈ p.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  obtain ⟨Θ, hsc, hgr, hΘtop⟩ := hK
  have hXile : p.scheme.scheme.grade Xi ≤ p.topGrade := le_csSup hbdd hmem
  have hXimem : GradedLe (p.scheme.scheme.cell Xi) (p.scheme.scheme.cell Θ) := by
    (constructor <;> simp_all)
  have hnotself :
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) p.topGrade p.topGrade ≠
        p.scheme.rows.E Θ ⟨Xi, hXimem⟩ := fun hself =>
    hcap ⟨Θ, hXimem, ⟨Xi, hXimem⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) with hbot | htop' | ⟨β, hβ⟩
  · simp_all
  · simp_all
  · rw [hβ, extVisibilityReplace_ofOrd] at hnotself
    have hfp : finitePart β < p.topGrade := by
      by_contra hge
      exact hnotself (congrArg ofOrd ((visibilityReplace_self_iff β _).mpr (not_lt.mp hge)))
    refine ⟨finitePart β, Θ, hXimem, hsc, hgr, hΘtop, ?_⟩
    have hvr : visibilityReplace β p.topGrade (finitePart β) = β := by
      unfold visibilityReplace ordinalReplace
      rw [ite_eq_left hfp]
      exact decomposition β
    simp_all

/-- Under `¬` clause 2.(a), every band index is `< K^p` (it is the finite part of an ordinal
row value that is not self-visible at `K^p`). -/
theorem ProvisionalBand.lt_topGrade {p : S α n} {Xi : Cell p.scheme.scheme} {i : ℕ}
    (h : p.ProvisionalBand Xi i) (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    i < p.topGrade := by
  obtain ⟨Θ, hXimem, hsc, hgr, hΘtop, heq⟩ := h
  have hnotself :
      extVisibilityReplace (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) p.topGrade p.topGrade ≠
        p.scheme.rows.E Θ ⟨Xi, hXimem⟩ := fun hself =>
    hcap ⟨Θ, hXimem, ⟨Xi, hXimem⟩, hsc, hgr, hΘtop, htop, le_of_eq hself⟩
  rcases ExtOrd.cases (p.scheme.rows.E Θ ⟨Xi, hXimem⟩) with hbot | htop' | ⟨β, hβ⟩
  · rw [hbot] at hnotself
    trivial
  · rw [htop'] at hnotself
    trivial
  · rw [hβ, extVisibilityReplace_ofOrd] at hnotself heq
    have hfp : finitePart β < p.topGrade := by
      by_contra hge
      exact hnotself (congrArg ofOrd ((visibilityReplace_self_iff β _).mpr (not_lt.mp hge)))
    have hβeq : β = limitPart β + (i : Ordinal) := by
      have h0 := ofOrd_inj.mp heq
      unfold visibilityReplace ordinalReplace at h0
      grind
    have hcast : (i : Ordinal.{0}) = (finitePart β : Ordinal.{0}) :=
      add_left_cancel (hβeq.symm.trans (decomposition β).symm)
    have : i = finitePart β := by exact_mod_cast hcast
    omega

/-- The band branch of `someProvisionalValue`: when `p(Ξ) = ∞` and clause 2.(a) fails, the value
is `α + i` for a band index `i < K^p`. -/
theorem someProvisionalValue_of_band {p : S α n} {Xi : Cell p.scheme.scheme}
    (htop : p.label Xi = ⊤) (hcap : ¬ p.ProvisionalCap Xi) :
    ∃ i, p.ProvisionalBand Xi i ∧ i < p.topGrade ∧
      p.someProvisionalValue Xi = ofOrd (α + i) := by
  have hex := exists_provisionalBand htop hcap
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex,
    (Nat.find_spec hex).lt_topGrade htop hcap, ?_⟩
  unfold someProvisionalValue
  simp_all

/-- **Def. 5.3.1 as a graph — the primary interface**: `v` is a provisional value of the cell
`Ξ` in `p`.  Clause 1 (`p(Ξ) < ∞`): `v = p(Ξ)`; clause 2.(a): `v = α + K^p`; clause 2.(b):
`v = α + i` for **some** band index `i`.  Stated relationally so that no noncanonical
selection enters the API: Lemma 5.3.2 (band-index independence of the witnessing `Θ`, a
consistency theorem, `ProvisionalBand.unique` in `Knight/ProvisionalUniqueness.lean`) makes the
relation single-valued (`IsProvisionalValue.unique`); `someProvisionalValue` (the least band
index) is a witness of totality (`isProvisionalValue_someProvisionalValue`) and computes the
unique value (`isProvisionalValue_iff`), but is not part of the primary interface. -/
def IsProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) (v : ExtOrd) : Prop :=
  (p.label Xi ≠ ⊤ ∧ v = p.label Xi) ∨
  (p.label Xi = ⊤ ∧ p.ProvisionalCap Xi ∧ v = ofOrd (α + p.topGrade)) ∨
  (p.label Xi = ⊤ ∧ ¬ p.ProvisionalCap Xi ∧
    ∃ i, p.ProvisionalBand Xi i ∧ v = ofOrd (α + i))

/-- The chooser realizes the relation (totality witness; the choice — least band index — is
canonical only in the sense of being deterministic, and is not exposed by the relational
interface). -/
theorem isProvisionalValue_someProvisionalValue (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.IsProvisionalValue Xi (p.someProvisionalValue Xi) := by
  by_cases htop : p.label Xi = ⊤
  · by_cases hcap : p.ProvisionalCap Xi
    · exact Or.inr (Or.inl ⟨htop, hcap, someProvisionalValue_of_cap htop hcap⟩)
    · obtain ⟨i, hband, -, hval⟩ := someProvisionalValue_of_band htop hcap
      tauto
  solve_by_elim [someProvisionalValue_of_ne_top]

/-- Every provisional value is `≤ α + K^p` (the conservative-estimate reading after
Def. 5.3.1). -/
theorem IsProvisionalValue.le {p : S α n} {Xi : Cell p.scheme.scheme} {v : ExtOrd}
    (h : p.IsProvisionalValue Xi v) : v ≤ ofOrd (α + p.topGrade) := by
  rcases h with ⟨hne, rfl⟩ | ⟨-, -, rfl⟩ | ⟨htop, hcap, i, hband, rfl⟩
  · rcases p.label_bound Xi with hlt | htop'
    · refine le_of_lt (hlt.trans_le (ofOrd_le_ofOrd.mpr ?_))
      simp
    trivial
  · rfl
  · rw [ofOrd_le_ofOrd]
    have hcast : (i : Ordinal.{0}) < (p.topGrade : Ordinal.{0}) := by
      exact_mod_cast hband.lt_topGrade htop hcap
    exact add_le_add (le_refl α) hcast.le

/-- `p⁺(Ξ) ≤ α + K^p` (the conservative-estimate reading after Def. 5.3.1). -/
theorem someProvisionalValue_le (p : S α n) (Xi : Cell p.scheme.scheme) :
    p.someProvisionalValue Xi ≤ ofOrd (α + p.topGrade) := by
  by_cases htop : p.label Xi = ⊤
  · by_cases hcap : p.ProvisionalCap Xi
    · rw [someProvisionalValue_of_cap htop hcap]
    · obtain ⟨i, -, hlt, hval⟩ := someProvisionalValue_of_band htop hcap
      (simp_all <;> omega)
  · rw [someProvisionalValue_of_ne_top htop]
    rcases p.label_bound Xi with hlt | htop'
    · refine le_of_lt (hlt.trans_le (ofOrd_le_ofOrd.mpr ?_))
      simp
    trivial

end StageType

namespace KnightRealization

open StageType

variable {α : LimitStage} {M : Type w}

/-- **Def. 5.3.9, dominating form**: the provisional values of (the images of) the cell `Ξ` of
`p` — intended as the type of `R` at `t` — stabilize to `γ` on a dominating set of labelled
tuples: every tuple `s` admits a labelled common extension `u` of `s` and `t` whose type gives
the underlying cell of `Ξ` the provisional value `γ` (relationally, `IsProvisionalValue` — no
chooser is consulted; once Lemma 5.3.2 lands at #51 the relation is the function graph).
The paper's "dominating (equivalently
coinitial, Cor. 5.3.8) set of finite subsets `A` of `M`" — the equivalence and the uniqueness
of `γ` are model theorems (directedness of labelled extensions), for #51, not definitional
here. -/
def StabilizesTo (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) : Prop :=
  ∀ {m : ℕ} (s : Fin m ↪ M),
    ∃ (m' : ℕ) (u : Fin m' ↪ M) (g : Fin m ↪ Fin m') (f : Fin n ↪ Fin m')
      (q : S α.1 m') (hpq : typeMap f q = some p),
      R.eval u = some q ∧ g.trans u = s ∧ f.trans u = t ∧
      q.IsProvisionalValue (mapCell hpq Xi) γ

/-- **The value `M⁺(Ξ)` as a graph** (Def. 5.3.9): `M⁺(Ξ) = γ` iff either `γ < α + ω` and the
provisional values stabilize to `γ`, or `γ = ∞` and no value below `α + ω` stabilizes.  Total
by construction; functional only under the model axioms (see `StabilizesTo`). -/
def HasStableValue (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (γ : ExtOrd) : Prop :=
  (γ < ofOrd (α.1 + Ordinal.omega0) ∧ R.StabilizesTo t p Xi γ) ∨
  (γ = ⊤ ∧ ∀ δ : ExtOrd, δ < ofOrd (α.1 + Ordinal.omega0) → ¬ R.StabilizesTo t p Xi δ)

/-- **Def. 5.4.2**: the cell `∞̃ := Xi` of `p` — intended as the type of `R` at `t` — is an
**anchor at infinity with threshold `K'`**, "minimal at infinity": it is labelled `∞` (implicit
in the paper's `∞̃`, see the module docstring), and in the type `q` of every labelled tuple
extending `t`, for every `∞`-cell `Θ` of grade `≥ K'` and every `∞`-cell `Σ` below `Θ`,

`E(Θ)(Σ) ⊔⁺_{K'} K' ≥ E(Θ)(∞̃)`, strictly when the grade of `Θ` exceeds `K'`.

(`M(Θ) = ∞` is read as the label of `Θ`, Def. 3.2.5: labels are preserved by restriction,
`label_mapCell`.) -/
def IsInfinityAnchor (R : KnightRealization α M) {n : ℕ} (t : Fin n ↪ M) (p : S α.1 n)
    (Xi : Cell p.scheme.scheme) (K' : ℕ) : Prop :=
  p.label Xi = ⊤ ∧
  ∀ {m : ℕ} (s : Fin m ↪ M) (f : Fin n ↪ Fin m) (q : S α.1 m),
    f.trans s = t → R.eval s = some q →
    ∀ (hpq : typeMap f q = some p) (Θ : Cell q.scheme.scheme),
      K' ≤ q.scheme.scheme.grade Θ → q.label Θ = ⊤ →
      ∀ Sig : q.scheme.scheme.below (q.scheme.scheme.cell Θ), q.label Sig.1 = ⊤ →
      ∀ hXi : GradedLe (q.scheme.scheme.cell (mapCell hpq Xi)) (q.scheme.scheme.cell Θ),
        q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi⟩ ≤
          extVisibilityReplace (q.scheme.rows.E Θ Sig) K' K' ∧
        (K' < q.scheme.scheme.grade Θ →
          q.scheme.rows.E Θ ⟨mapCell hpq Xi, hXi⟩ <
            extVisibilityReplace (q.scheme.rows.E Θ Sig) K' K')

/-- `R` has an **anchor at infinity** (Def. 5.4.2): some cell of some realized type is minimal
at infinity at some threshold. -/
def HasInfinityAnchor (R : KnightRealization α M) : Prop :=
  ∃ (n : ℕ) (t : Fin n ↪ M) (p : S α.1 n), R.eval t = some p ∧
    ∃ (Xi : Cell p.scheme.scheme) (K' : ℕ), R.IsInfinityAnchor t p Xi K'

/-- **Hollowness** (Def. 5.4.2): `R` is hollow iff it has no anchor at infinity.  The paper
frames the definition for models of characteristic arity `K` with `0 < K ≤ ∞`; the framing
hypothesis belongs to the consumers (#52).  This is **not** orbit homogeneity (Knight-VC's
`IsHollow`, renamed `IsOrbitHomogeneous` there) — banned identification 1; orbit homogeneity
is deliberately not defined in this module. -/
def IsHollow (R : KnightRealization α M) : Prop := ¬ R.HasInfinityAnchor

end KnightRealization

end VaughtConjecture.Knight
