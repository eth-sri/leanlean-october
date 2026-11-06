/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.ModelMap

/-! # Limits of coherent chains under strict reduction (#46 bounded probe)

The bounded strict-reduction limit probe of #46.  The rebuild's reduction (`Knight/Reduction`)
fixes the scheme and all rows and strictly truncates the finitely many labels (`truncExt α`:
ordinals `≥ α` become `⊤`, ordinals `< α` are kept).  For a coherent chain this forces
**finite-stage stabilization**: a cell label that is ever not `⊤` is strictly below its stage
bound, hence literally constant from there on (`ExtOrd.IsTruncChain.eq_of_ne_top`); schemes are
finite, so past a single index (`stabIndex`) the whole chain of types is constant modulo the
stage bound.  The probe's decisive observation is that "modulo the stage bound" is a triviality
here: a stage type strictly bounded at `γ` **is** a stage type at every `δ ≥ γ`
(`StageType.castLE` — same scheme, same labels, same `respects` proof; only the strict bound
weakens), and reduction of such a lift is again a lift (`reduceType_castLE`,
by `truncExt_id_of_bound`).  So the limit of a coherent chain is `castLE` of one sufficiently
high stage, its `RespectsSemantics` proof is **definitionally** the proof at that stage
(`limitOfChain_label` is `rfl`), and no semantic inverse-limit argument occurs anywhere.
**The #46 stop condition does not fire.**

Contents:

* `StageType.castLE` and its laws (`reduceType_castLE`: reduction of a lift is a lift);
* `ExtOrd.IsTruncChain` / `ExtOrd.limitOfTruncChain` — the limit of a coherent label chain
  (the eventual constant if the chain is ever not `⊤`, else `⊤`), with the exact reduct
  equation `truncExt (c i) (lim v) = v i` and the strict bound at every upper stage;
* `StageType.IsReduceChain` / `StageType.limitOfChain` — the limit of a coherent chain of
  stage types at an upper bound `δ` of the stages, with `reduceType_limitOfChain`
  (**reductions equal the chain entries**) and cofinal-reduction injectivity
  (`eq_of_forall_reduceType_eq`: the limit is canonical when the stages are cofinal in `δ` —
  finite label arithmetic, unrelated to uniqueness of prolongations, which stays avoided);
* `KnightRealization.IsReductChain` / `KnightRealization.limitOfChain` — the fixed-carrier
  limit of a coherent chain of realizations under literal reduct equations (the shape every
  certified link normalizes to, `prolongsToIn_isModelClass_iff_on` via `IsModel.map`), with
  `reduct_limitOfChain`: lower reducts of the limit **equal** the chain entries;
* modelhood at the limit (`IsModel.limitOfChain`): if every chain entry is a model and the
  stages are cofinal in `δ`, the limit is a model of `S^δ`.  Every clause of Def. 3.2.1 is a
  bounded request — it mentions one tuple and finitely many cells — so it is served by
  choosing one sufficiently high stage and transporting the witness: consistency and the
  request families ride on the reduct equations plus `truncExt` arithmetic
  (`truncExt_eq_bot_iff` for the `−∞`-pattern, `γ + ω ≤ c i` for uniformity,
  inflationarity for dominance); cofinality supplies the stage for the ordinal-parameter
  clauses and for the `−∞`-pattern's label-fixing stage.

Only ω-indexed chains are treated: the #46 outer limit is a *countable*-cofinal assembly, and
every countable `LimitStage` has cofinality `ω`, so an ω-subchain always exists; the bounded probe
does not need a general chain index. -/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight

open Value ExtOrd TypeTower

universe w

/-! ### Stage weakening of stage types -/

namespace StageType

variable {α β γ : Ordinal.{0}} {n : ℕ}

/-- **Stage weakening**: a stage type strictly bounded at `α` is literally one at every
`β ≥ α` — same scheme, same labels, same respect proof; only the strict label bound weakens.
(Not a section of anything by fiat: `reduceType_castLE` proves reduction undoes it.) -/
def castLE (h : α ≤ β) (t : S α n) : S β n where
  scheme := t.scheme
  label := t.label
  label_bound d := (t.label_bound d).imp (fun hlt => hlt.trans_le (ofOrd_le_ofOrd.mpr h)) id
  respects := t.respects

/-- **Reduction undoes stage weakening**: reducing the lift of `t : S α n` to any intermediate
limit stage `β` with `α ≤ β ≤ γ` is again the lift of `t` — the labels are already strictly
bounded at `α` (`truncExt_id_of_bound`).  At `β = α` this is a one-sided inverse:
`reduceType ∘ castLE = id`. -/
theorem reduceType_castLE (hβ : Order.IsSuccLimit β) (hαβ : α ≤ β) (hαγ : α ≤ γ)
    (hβγ : β ≤ γ) (t : S α n) :
    reduceType hβ hβγ (castLE hαγ t) = castLE hαβ t :=
  StageType.ext rfl (heq_of_eq (funext fun d =>
    truncExt_id_of_bound ((t.label_bound d).imp
      (fun hlt => hlt.trans_le (ofOrd_le_ofOrd.mpr hαβ)) id)))

end StageType

/-! ### Cell transport calculus -/

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Reading a stage-type equality at one cell (the pointwise inverse of
`ext_of_scheme_label`). -/
theorem label_congr {t₁ t₂ : S α n} (h : t₁ = t₂) (d : Cell t₁.scheme.scheme) :
    t₁.label d = t₂.label (SemScheme.castCell (congrArg StageType.scheme h) d) := by
  subst h; rfl

/-- `HEq`-free extensionality: two stage types are equal when their schemes are equal and
their labels agree across the cell transport. -/
theorem ext_of_scheme_label {t₁ t₂ : S α n} (hs : t₁.scheme = t₂.scheme)
    (hl : ∀ d : Cell t₁.scheme.scheme, t₁.label d = t₂.label (SemScheme.castCell hs d)) :
    t₁ = t₂ := by
  obtain ⟨X₁, l₁, b₁, r₁⟩ := t₁
  obtain ⟨X₂, l₂, b₂, r₂⟩ := t₂
  revert hl
  change X₁ = X₂ at hs
  subst hs
  intro hl
  exact StageType.ext rfl (heq_of_eq (funext fun d => hl d))

end StageType

/-! ### Limits of coherent label chains -/

namespace ExtOrd

/-- **Coherence of a label chain** along the stage sequence `c` under strict truncation
(Def. 3.1.2 at a single cell): every entry is the truncation of every later entry. -/
def IsTruncChain (c : ℕ → Ordinal.{0}) (v : ℕ → ExtOrd) : Prop :=
  ∀ ⦃i j : ℕ⦄, i ≤ j → v i = truncExt (c i) (v j)

variable {c : ℕ → Ordinal.{0}} {v : ℕ → ExtOrd}

/-- **Finite-stage stabilization at one cell**: an entry that is not `⊤` is strictly below its
stage bound, so strict truncation fixes it — every later entry equals it. -/
theorem IsTruncChain.eq_of_ne_top (hv : IsTruncChain c v) {i j : ℕ} (hij : i ≤ j)
    (hi : v i ≠ ⊤) : v j = v i := by
  have h := hv hij
  have hlt : v j < ofOrd (c i) := by
    by_contra hle
    exact hi (h.trans (truncExt_eq_top_of_ge (not_lt.mp hle)))
  rw [h, truncExt_id_of_lt hlt]

/-- **Cofinal truncation-injectivity**: two labels strictly bounded at `δ` with equal
truncations at stages cofinal in `δ` are equal.  Finite label arithmetic, not an
inverse-limit argument. -/
theorem eq_of_forall_truncExt_eq {x y : ExtOrd} {δ : Ordinal.{0}} {c : ℕ → Ordinal.{0}}
    (hcof : ∀ γ : Ordinal.{0}, γ < δ → ∃ i, γ < c i)
    (hx : x < ofOrd δ ∨ x = ⊤) (hy : y < ofOrd δ ∨ y = ⊤)
    (h : ∀ i, truncExt (c i) x = truncExt (c i) y) : x = y := by
  have key : ∀ {z : ExtOrd}, z < ofOrd δ → ∃ i, z < ofOrd (c i) := by
    intro z hz
    rcases ExtOrd.cases z with rfl | rfl | ⟨β, rfl⟩
    · exact ⟨0, bot_lt_ofOrd _⟩
    · exact absurd hz (not_lt.mpr le_top)
    · obtain ⟨i, hi⟩ := hcof β (ofOrd_lt_ofOrd.mp hz)
      exact ⟨i, ofOrd_lt_ofOrd.mpr hi⟩
  rcases hx with hx | rfl
  · obtain ⟨i, hi⟩ := key hx
    have hxi := h i
    rw [truncExt_id_of_lt hi] at hxi
    rcases lt_or_ge y (ofOrd (c i)) with hyi | hyi
    · rwa [truncExt_id_of_lt hyi] at hxi
    · rw [truncExt_eq_top_of_ge hyi] at hxi
      exact absurd (hxi ▸ hi) not_top_lt
  · rcases hy with hy | rfl
    · obtain ⟨i, hi⟩ := key hy
      have hyi := h i
      rw [truncExt_top, truncExt_id_of_lt hi] at hyi
      exact hyi
    · rfl

end ExtOrd

/-! ### Limits of coherent chains of stage types -/

namespace StageType

variable {n : ℕ} {c : ℕ → LimitStage}

/-- A monotone sequence of limit stages, read at the underlying ordinals. -/
theorem stage_le (hc : Monotone c) {i j : ℕ} (h : i ≤ j) : (c i).1 ≤ (c j).1 := hc h

variable {p : ∀ i, S (c i).1 n} {hc : Monotone c}

/-- **Coherence of a chain of stage types under strict reduction** along the monotone limit
stages `c`: every entry is the vertical reduction of every later entry (Knight's
`S^{ι_{α,β}}`-compatibility, Def. 5.1.1 shape). -/
def IsReduceChain (hc : Monotone c) (p : ∀ i, S (c i).1 n) : Prop :=
  ∀ ⦃i j : ℕ⦄ (h : i ≤ j), reduceType (c i).2 (stage_le hc h) (p j) = p i

/-- Reduction fixes schemes, so the schemes of a coherent chain are all equal. -/
theorem IsReduceChain.scheme_eq (hp : IsReduceChain hc p) {i j : ℕ} (h : i ≤ j) :
    (p j).scheme = (p i).scheme :=
  congrArg StageType.scheme (hp h)

/-- A cell of the base entry, transported to stage `i` of the chain. -/
def IsReduceChain.cell (hp : IsReduceChain hc p) (i : ℕ)
    (d : Cell (p 0).scheme.scheme) : Cell (p i).scheme.scheme :=
  SemScheme.castCell (hp.scheme_eq (Nat.zero_le i)).symm d

/-- The label chain of one transported cell is a coherent label chain. -/
theorem IsReduceChain.isTruncChain (hp : IsReduceChain hc p) (d : Cell (p 0).scheme.scheme) :
    ExtOrd.IsTruncChain (fun i => (c i).1) (fun i => (p i).label (hp.cell i d)) := by
  intro i j hij
  exact (label_congr (hp hij) (hp.cell j d)).symm

open Classical in
/-- A stage index past which every cell's label chain has stabilised: for each of the finitely
many cells, an index witnessing a non-`⊤` value if there is one (the chain is constant from
there on), joined over the cells. -/
def IsReduceChain.stabIndex (hp : IsReduceChain hc p) : ℕ :=
  Finset.univ.sup fun d : Cell (p 0).scheme.scheme =>
    if h : ∃ i, (p i).label (hp.cell i d) ≠ ⊤ then h.choose else 0

/-- Past `stabIndex`, every cell's label agrees with its value at `stabIndex`. -/
theorem IsReduceChain.label_stab (hp : IsReduceChain hc p) (d : Cell (p 0).scheme.scheme)
    {j : ℕ} (hj : hp.stabIndex ≤ j) :
    (p j).label (hp.cell j d) = (p hp.stabIndex).label (hp.cell hp.stabIndex d) := by
  classical
  have hvc := hp.isTruncChain d
  by_cases hex : ∃ i, (p i).label (hp.cell i d) ≠ ⊤
  · have hle : hex.choose ≤ hp.stabIndex := by
      refine le_trans ?_ (Finset.le_sup (f := fun d : Cell (p 0).scheme.scheme =>
        if h : ∃ i, (p i).label (hp.cell i d) ≠ ⊤ then h.choose else 0) (Finset.mem_univ d))
      rw [dite_eq_left hex]
    have h1 := hvc.eq_of_ne_top hle hex.choose_spec
    have h2 := hvc.eq_of_ne_top (hle.trans hj) hex.choose_spec
    exact h2.trans h1.symm
  · push Not at hex
    rw [hex j, hex hp.stabIndex]

/-- **Finite-stage stabilization**: past `stabIndex`, the chain is literally constant modulo
stage weakening. -/
theorem IsReduceChain.eq_castLE_stab (hp : IsReduceChain hc p) {j : ℕ}
    (hj : hp.stabIndex ≤ j) :
    p j = castLE (stage_le hc hj) (p hp.stabIndex) := by
  refine ext_of_scheme_label (hp.scheme_eq hj) fun d => ?_
  exact hp.label_stab (SemScheme.castCell (hp.scheme_eq (Nat.zero_le j)) d) hj

/-- **The limit of a coherent chain of stage types** at an upper bound `δ` of the stages: the
stabilized entry, stage-weakened to `δ`.  Its scheme, labels and — decisively — its
`RespectsSemantics` proof are **literally** those of the sufficiently high stage
`p stabIndex` (`limitOfChain_scheme`, `limitOfChain_label` are `rfl`): respect is inherited
by finite-stage stabilization, and the #46 stop condition does not fire. -/
def limitOfChain (hp : IsReduceChain hc p) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) : S δ.1 n :=
  castLE (hδ hp.stabIndex) (p hp.stabIndex)

/-- **Lower reductions of the limit equal the chain entries** — the acceptance equation
("reductions equal stages"). -/
theorem reduceType_limitOfChain (hp : IsReduceChain hc p) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) :
    reduceType (c i).2 (hδ i) (limitOfChain hp δ hδ) = p i := by
  rcases le_total i hp.stabIndex with hii | hii
  · exact hp hii
  · rw [hp.eq_castLE_stab hii]
    exact reduceType_castLE (c i).2 (stage_le hc hii) (hδ hp.stabIndex) (hδ i) (p hp.stabIndex)

/-- A stage of the sequence past which strict truncation fixes every label of a stage-`δ`
type: finitely many cells, and cofinality supplies a stage above each non-`⊤` label. -/
theorem exists_truncExt_label_id (hc : Monotone c) {δ : LimitStage}
    (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1) (q : S δ.1 n) :
    ∃ i₀ : ℕ, ∀ d : Cell q.scheme.scheme, truncExt (c i₀).1 (q.label d) = q.label d := by
  classical
  choose g hg using fun d : Cell q.scheme.scheme =>
    show ∃ i, q.label d = ⊤ ∨ q.label d < ofOrd (c i).1 from by
      rcases q.label_bound d with hlt | htop
      · rcases ExtOrd.cases (q.label d) with hbot | htop' | ⟨β, hβ⟩
        · exact ⟨0, Or.inr (hbot ▸ bot_lt_ofOrd _)⟩
        · exact ⟨0, Or.inl htop'⟩
        · obtain ⟨i, hi⟩ := hcof β (ofOrd_lt_ofOrd.mp (hβ ▸ hlt))
          exact ⟨i, Or.inr (hβ ▸ ofOrd_lt_ofOrd.mpr hi)⟩
      · exact ⟨0, Or.inl htop⟩
  refine ⟨Finset.univ.sup g, fun d => ?_⟩
  rcases hg d with htop | hlt
  · rw [htop, truncExt_top]
  · exact truncExt_id_of_lt (hlt.trans_le (ofOrd_le_ofOrd.mpr
      (stage_le hc (Finset.le_sup (Finset.mem_univ d)))))

/-- **Cofinal-reduction injectivity**: two stage-`δ` types with equal reductions at a chain of
stages cofinal in `δ` are equal (schemes are fixed by reduction; labels by
`ExtOrd.eq_of_forall_truncExt_eq`).  This makes the limit canonical under cofinality.  It is
finite label arithmetic — in particular *not* Knight's uniqueness of expansions (Lemma 5.5.2),
which stays avoided. -/
theorem eq_of_forall_reduceType_eq {δ : LimitStage} {q₁ q₂ : S δ.1 n}
    (hδ : ∀ i, c i ≤ δ) (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1)
    (h : ∀ i, reduceType (c i).2 (hδ i) q₁ = reduceType (c i).2 (hδ i) q₂) : q₁ = q₂ := by
  have hs0 := congrArg StageType.scheme (h 0)
  have hs : q₁.scheme = q₂.scheme := hs0
  exact ext_of_scheme_label hs fun d =>
    ExtOrd.eq_of_forall_truncExt_eq (c := fun i => (c i).1) hcof (q₁.label_bound d)
      (q₂.label_bound _) fun i => label_congr (h i) d

end StageType

/-! ### Limits of coherent fixed-carrier chains of realizations -/

namespace KnightRealization

variable {M : Type w} {c : ℕ → LimitStage} {hc : Monotone c}

/-- **A coherent fixed-carrier chain of realizations** under literal reduct equations: every
entry is the reduct of every later entry, on one carrier `M`.  This is the shape every chain
of certified links normalizes to (`prolongsToIn_isModelClass_iff_on`, via `IsModel.map`). -/
def IsReductChain (hc : Monotone c) (R : ∀ i, KnightRealization (c i) M) : Prop :=
  ∀ ⦃i j : ℕ⦄ (h : i ≤ j), (R j).reduct (hc h) = R i

variable {R : ∀ i, KnightRealization (c i) M}

theorem IsReductChain.eval_eq (hR : IsReductChain hc R) {i j : ℕ} (h : i ≤ j) {n : ℕ}
    (t : Fin n ↪ M) :
    (R i).eval t = ((R j).eval t).map (reduceType (c i).2 (StageType.stage_le hc h)) := by
  rw [← hR h]; rfl

/-- Definedness is constant along a coherent chain. -/
theorem IsReductChain.exists_eval_eq_some_iff (hR : IsReductChain hc R) {n : ℕ}
    (t : Fin n ↪ M) (i j : ℕ) :
    (∃ q, (R i).eval t = some q) ↔ (∃ q, (R j).eval t = some q) := by
  have key {a b : ℕ} (hab : a ≤ b) : (∃ q, (R a).eval t = some q) ↔ ∃ q, (R b).eval t = some q := by
    rw [hR.eval_eq hab t]
    cases (R b).eval t
    · exact ⟨fun ⟨_, h⟩ => (by cases h), fun ⟨_, h⟩ => (by cases h)⟩
    · exact ⟨fun _ => ⟨_, rfl⟩, fun _ => ⟨_, rfl⟩⟩
  rcases le_total i j with h | h
  · exact key h
  · exact (key h).symm

/-- The stage-type chain of one everywhere-defined tuple is a coherent chain. -/
theorem IsReductChain.isReduceChain_choose (hR : IsReductChain hc R) {n : ℕ}
    {t : Fin n ↪ M} (ht : ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q) :
    StageType.IsReduceChain hc fun i => (ht i).choose := by
  intro i j hij
  have h := hR.eval_eq hij t
  rw [(ht i).choose_spec, (ht j).choose_spec, Option.map_some] at h
  exact (Option.some_inj.mp h).symm

open Classical in
/-- **The limit of a coherent fixed-carrier chain of realizations**: on each tuple, `none` if
the chain is (equivalently: anywhere) undefined there, else the limit of the stage-type chain
of its labels (`StageType.limitOfChain`). -/
def limitOfChain (hc : Monotone c) (R : ∀ i, KnightRealization (c i) M)
    (hR : IsReductChain hc R) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ) :
    KnightRealization δ M where
  eval {n} t :=
    if ht : ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q then
      some (StageType.limitOfChain (hR.isReduceChain_choose ht) δ hδ)
    else none

/-- **Lower reducts of the limit equal the chain entries literally** — the acceptance test of
the probe ("the union is a model; reductions equal stages", equation half). -/
theorem reduct_limitOfChain (hR : IsReductChain hc R) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) :
    (limitOfChain hc R hR δ hδ).reduct (hδ i) = R i := by
  refine Realization.ext fun {n} t => ?_
  rw [Realization.reduct_eval]
  dsimp only [limitOfChain]
  split_ifs with ht
  · rw [(ht i).choose_spec]
    exact congrArg some (StageType.reduceType_limitOfChain (hR.isReduceChain_choose ht) δ hδ i)
  · push Not at ht
    obtain ⟨j, hj⟩ := ht
    cases hcase : (R i).eval t with
    | none => rfl
    | some q =>
      exact absurd ((hR.exists_eval_eq_some_iff t i j).mp ⟨q, hcase⟩) (not_exists.mpr hj)

theorem limitOfChain_eval_map (hR : IsReductChain hc R) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) {n : ℕ} (t : Fin n ↪ M) :
    ((limitOfChain hc R hR δ hδ).eval t).map (reduceType (c i).2 (hδ i)) = (R i).eval t :=
  congrArg (fun R' => R'.eval t) (reduct_limitOfChain hR δ hδ i)

/-! ### Def. 3.2.1 at the limit, clause by clause -/

/-- **Exact parent consistency passes to the limit** (clause (2)): on a visible face the two
labels have equal reductions at every stage — the chain's consistency plus
`typeMap_reduceType_comm` — hence are equal by cofinal-reduction injectivity; on an invisible
face both sides are undefined (visibility reads the scheme, which the whole chain shares). -/
theorem IsReductChain.isExactParentConsistent_limit (hR : IsReductChain hc R)
    (hcons : ∀ i, (R i).IsExactParentConsistent) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ)
    (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1) :
    (limitOfChain hc R hR δ hδ).IsExactParentConsistent := by
  intro m n t q f hq
  change S δ.1 n at q
  change (limitOfChain hc R hR δ hδ).eval (f.trans t) = typeMap f q
  have hi (i : ℕ) : ((limitOfChain hc R hR δ hδ).eval (f.trans t)).map (reduceType (c i).2 (hδ i)) =
      (typeMap f q).map (reduceType (c i).2 (hδ i)) := by
    rw [limitOfChain_eval_map,
      hcons i t _ f (by rw [← limitOfChain_eval_map hR δ hδ i, hq]; rfl)]
    exact typeMap_reduceType_comm (c i).2 (hδ i) f q
  rcases h1 : (limitOfChain hc R hR δ hδ).eval (f.trans t) with _ | r₁ <;>
    rcases h2 : typeMap f q with _ | r₂
  · rfl
  · have h0 := hi 0; rw [h1, h2] at h0; cases h0
  · have h0 := hi 0; rw [h1, h2] at h0; cases h0
  · refine congrArg some (StageType.eq_of_forall_reduceType_eq hδ hcof fun i => ?_)
    have hi' := hi i; rw [h1, h2] at hi'; exact Option.some_inj.mp hi'

/-- **Initial-segment covering passes to the limit** (clause (3)): the covering witness of any
one stage is everywhere defined, hence defined at the limit. -/
theorem IsReductChain.isInitialSegmentCovering_limit (hR : IsReductChain hc R)
    (hcov : (R 0).IsInitialSegmentCovering) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ) :
    (limitOfChain hc R hR δ hδ).IsInitialSegmentCovering := by
  intro n t
  obtain ⟨k, s, hst, hsome⟩ := hcov t
  refine ⟨k, s, hst, ?_⟩
  rw [← limitOfChain_eval_map hR δ hδ 0] at hsome
  cases h : (limitOfChain hc R hR δ hδ).eval s <;> rw [h] at hsome <;> exact hsome

/-- **Realized families lift to the limit**: a witness for the tuple `t` at one stage `i`
of the chain is everywhere defined; the limit label of the extended tuple reduces at stage `i`
to the stage-`i` witness, so any family closed under "reduction lands in `U`" is realized at
the limit.  The coface condition is exact parent consistency of the limit. -/
theorem IsReductChain.realizesSome_limit (hR : IsReductChain hc R) {δ : LimitStage}
    {hδ : ∀ i, c i ≤ δ}
    (hcons : (limitOfChain hc R hR δ hδ).IsExactParentConsistent)
    {n : ℕ} {t : Fin n ↪ M} {p : S δ.1 n}
    (hpt : (limitOfChain hc R hR δ hδ).eval t = some p) (i : ℕ)
    {U : Set (S (c i).1 (n + 1))} {U' : Set (S δ.1 (n + 1))}
    (hU : ∀ q' : S δ.1 (n + 1), reduceType (c i).2 (hδ i) q' ∈ U → q' ∈ U')
    (h : (R i).RealizesSome t (reduceType (c i).2 (hδ i) p) U) :
    RealizesSome (limitOfChain hc R hR δ hδ) t p U' := by
  obtain ⟨y, hy, q, hqU, _, hq⟩ := h
  rw [← limitOfChain_eval_map hR δ hδ i] at hq
  cases hq' : (limitOfChain hc R hR δ hδ).eval (snoc t y hy) with
  | none => rw [hq'] at hq; cases hq
  | some q' =>
    rw [hq'] at hq; cases hq
    exact ⟨y, hy, q', hU q' hqU, isCoface_of_consistent hcons hpt hq', hq'⟩

/-- **Modelhood passes to the limit of a coherent chain of models** whose stages are cofinal
in `δ`: every clause of Def. 3.2.1 is a bounded request — one tuple, finitely many cells, at
most one ordinal parameter — served by choosing a sufficiently high stage of the chain and
transporting its witness up.  Uniformity and dominance pick a stage above `γ` (cofinality);
the `−∞`-pattern picks a stage fixing every label of the source type
(`exists_truncExt_label_id`) so the pattern source transfers verbatim, and reduction
preserves and reflects `⊥` (`truncExt_eq_bot_iff`); generalised saturation is scheme-only and
uses stage `0`. -/
theorem IsModel.limitOfChain (hc : Monotone c) {R : ∀ i, KnightRealization (c i) M}
    (hR : IsReductChain hc R) (hmod : ∀ i, (R i).IsModel) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1) :
    IsModel (KnightRealization.limitOfChain hc R hR δ hδ) := by
  have hcons := hR.isExactParentConsistent_limit (fun i => (hmod i).consistent) δ hδ hcof
  have heval {n} {t : Fin n ↪ M} {p : S δ.1 n}
      (hp' : (KnightRealization.limitOfChain hc R hR δ hδ).eval t = some p) (i : ℕ) :
      (R i).eval t = some (reduceType (c i).2 (hδ i) p) := by
    rw [← limitOfChain_eval_map hR δ hδ i, hp']; rfl
  refine ⟨(hmod 0).nonempty, hcons,
    hR.isInitialSegmentCovering_limit (hmod 0).covering δ hδ,
    fun t p hp' D hD => hR.realizesSome_limit hcons hp' 0 (fun _ => id)
      ((hmod 0).genSat t _ (heval hp' 0) D ⟨hD.visible, hD.restrict⟩),
    fun t p hp' D hD q' hq' hext => ?_,
    fun t p hp' γ hγ hγδ => ?_,
    fun t p hp' γ hγδ => ?_⟩
  · obtain ⟨i₀, hi₀⟩ := StageType.exists_truncExt_label_id hc hcof p
    refine hR.realizesSome_limit hcons hp' i₀ ?_
      ((hmod i₀).bottomPattern t _ (heval hp' i₀) D ⟨hD.visible, hD.restrict⟩ q' hq' fun d =>
        (hext d).trans (hi₀ d).symm)
    rintro _ ⟨hsch, hpat⟩
    exact ⟨hsch, fun Θ => truncExt_eq_bot_iff.symm.trans (hpat Θ)⟩
  · obtain ⟨i₁, hi₁⟩ := hcof γ hγδ
    refine hR.realizesSome_limit hcons hp' i₁ ?_
      ((hmod i₁).uniformity t _ (heval hp' i₁) γ hγ hi₁)
    rintro q'' ⟨Sig, h1, h2⟩
    change ofOrd γ ≤ truncExt (c i₁).1 (q''.label Sig) at h1
    change truncExt (c i₁).1 (q''.label Sig) < ofOrd (γ + Ordinal.omega0) at h2
    have hlt : q''.label Sig < ofOrd (c i₁).1 :=
      not_le.mp fun hle => ne_top_of_lt h2 (truncExt_eq_top_of_ge hle)
    rw [truncExt_id_of_lt hlt] at h1 h2
    exact ⟨Sig, h1, h2⟩
  · obtain ⟨i₁, hi₁⟩ := hcof γ hγδ
    refine hR.realizesSome_limit hcons hp' i₁ ?_
      ((hmod i₁).highGradeDominance t _ (heval hp' i₁) γ hi₁)
    rintro q'' ⟨Sig, hg, hl⟩
    change ofOrd γ < truncExt (c i₁).1 (q''.label Sig) at hl
    refine ⟨Sig, hg, ?_⟩
    rcases lt_or_ge (q''.label Sig) (ofOrd (c i₁).1) with hlt | hge
    · rwa [truncExt_id_of_lt hlt] at hl
    · exact (ofOrd_lt_ofOrd.mpr hi₁).trans_le hge
