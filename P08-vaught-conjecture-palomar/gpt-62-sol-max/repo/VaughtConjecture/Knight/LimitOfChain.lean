/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.ModelMap

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd TypeTower

universe w

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

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- Reading a stage-type equality at one cell (the pointwise inverse of
`ext_of_scheme_label`). -/
theorem label_congr {t₁ t₂ : S α n} (h : t₁ = t₂) (d : Cell t₁.scheme.scheme) :
    t₁.label d = t₂.label (SemScheme.castCell (congrArg StageType.scheme h) d) := by aesop

/-- `HEq`-free extensionality: two stage types are equal when their schemes are equal and
their labels agree across the cell transport. -/
theorem ext_of_scheme_label {t₁ t₂ : S α n} (hs : t₁.scheme = t₂.scheme)
    (hl : ∀ d : Cell t₁.scheme.scheme, t₁.label d = t₂.label (SemScheme.castCell hs d)) :
    t₁ = t₂ := by
  obtain ⟨X₁, l₁, b₁, r₁⟩ := t₁
  obtain ⟨X₂, l₂, b₂, r₂⟩ := t₂
  revert hl
  change X₁ = X₂ at hs
  aesop

end StageType

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

end ExtOrd

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
noncomputable def IsReduceChain.cell (hp : IsReduceChain hc p) (i : ℕ)
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
noncomputable def IsReduceChain.stabIndex (hp : IsReduceChain hc p) : ℕ :=
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
      simp_all
    have h1 := hvc.eq_of_ne_top hle hex.choose_spec
    have h2 := hvc.eq_of_ne_top (hle.trans hj) hex.choose_spec
    simp_all
  simp_all

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
noncomputable def limitOfChain (hp : IsReduceChain hc p) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) : S δ.1 n :=
  castLE (hδ hp.stabIndex) (p hp.stabIndex)

theorem limitOfChain_def (hp : IsReduceChain hc p) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ) :
    limitOfChain hp δ hδ = castLE (hδ hp.stabIndex) (p hp.stabIndex) := rfl

/-- **Lower reductions of the limit equal the chain entries** — the acceptance equation
("reductions equal stages"). -/
theorem reduceType_limitOfChain (hp : IsReduceChain hc p) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) :
    reduceType (c i).2 (hδ i) (limitOfChain hp δ hδ) = p i := by
  rcases le_total i hp.stabIndex with hii | hii
  · tauto
  · rw [hp.eq_castLE_stab hii, limitOfChain_def]
    (apply reduceType_castLE <;> assumption)

/-- The limit's scheme equals the scheme of every chain entry. -/
theorem limitOfChain_scheme_eq (hp : IsReduceChain hc p) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) : (limitOfChain hp δ hδ).scheme = (p i).scheme :=
  congrArg StageType.scheme (reduceType_limitOfChain hp δ hδ i)

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
        all_goals simp_all
      tauto
  refine ⟨Finset.univ.sup g, fun d => ?_⟩
  rcases hg d with htop | hlt
  · simp_all
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
  refine ext_of_scheme_label hs fun d => ?_
  refine ExtOrd.eq_of_forall_truncExt_eq (c := fun i => (c i).1) hcof (q₁.label_bound d)
    (q₂.label_bound (SemScheme.castCell hs d)) fun i => ?_
  have hli := label_congr (h i) d
  assumption

end StageType

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
  have key : ∀ {a b : ℕ}, a ≤ b → (∃ q, (R b).eval t = some q) →
      ∃ q, (R a).eval t = some q := by
    intro a b hab h
    obtain ⟨q, hq⟩ := h
    exact ⟨reduceType (c a).2 (StageType.stage_le hc hab) q,
      by rw [hR.eval_eq hab t, hq]; rfl⟩
  have key2 : ∀ {a b : ℕ}, a ≤ b → (∃ q, (R a).eval t = some q) →
      ∃ q, (R b).eval t = some q := by
    intro a b hab h
    obtain ⟨q, hq⟩ := h
    have heq := hR.eval_eq hab t
    rw [hq] at heq
    cases hcase : (R b).eval t with
    | none => rw [hcase] at heq; trivial
    | some r => exact ⟨r, rfl⟩
  rcases le_total i j with h | h
  all_goals solve_by_elim

theorem IsReductChain.forall_exists_of_eval_eq_some (hR : IsReductChain hc R) {n : ℕ}
    {t : Fin n ↪ M} {i : ℕ} {q : S (c i).1 n} (hq : (R i).eval t = some q) :
    ∀ j, ∃ q', (R j).eval t = some q' :=
  fun j => (hR.exists_eval_eq_some_iff t i j).mp ⟨q, hq⟩

/-- The stage-type chain of one everywhere-defined tuple is a coherent chain. -/
theorem IsReductChain.isReduceChain_choose (hR : IsReductChain hc R) {n : ℕ}
    {t : Fin n ↪ M} (ht : ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q) :
    StageType.IsReduceChain hc fun i => (ht i).choose := by
  intro i j hij
  have h := hR.eval_eq hij t
  grind

open Classical in
/-- **The limit of a coherent fixed-carrier chain of realizations**: on each tuple, `none` if
the chain is (equivalently: anywhere) undefined there, else the limit of the stage-type chain
of its labels (`StageType.limitOfChain`). -/
noncomputable def limitOfChain (hc : Monotone c) (R : ∀ i, KnightRealization (c i) M)
    (hR : IsReductChain hc R) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ) :
    KnightRealization δ M where
  eval {n} t :=
    if ht : ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q then
      some (StageType.limitOfChain (hR.isReduceChain_choose ht) δ hδ)
    else none

theorem limitOfChain_eval_pos (hR : IsReductChain hc R) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) {n : ℕ} {t : Fin n ↪ M}
    (ht : ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q) :
    (limitOfChain hc R hR δ hδ).eval t
      = some (StageType.limitOfChain (hR.isReduceChain_choose ht) δ hδ) :=
  dite_eq_left ht

theorem limitOfChain_eval_neg (hR : IsReductChain hc R) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) {n : ℕ} {t : Fin n ↪ M}
    (ht : ¬ ∀ i, ∃ q : S (c i).1 n, (R i).eval t = some q) :
    (limitOfChain hc R hR δ hδ).eval t = none :=
  dite_eq_right ht

/-- **Lower reducts of the limit equal the chain entries literally** — the acceptance test of
the probe ("the union is a model; reductions equal stages", equation half). -/
theorem reduct_limitOfChain (hR : IsReductChain hc R) (δ : LimitStage)
    (hδ : ∀ i, c i ≤ δ) (i : ℕ) :
    (limitOfChain hc R hR δ hδ).reduct (hδ i) = R i := by
  refine Realization.ext fun {n} t => ?_
  rw [Realization.reduct_eval]
  by_cases ht : ∀ j, ∃ q : S (c j).1 n, (R j).eval t = some q
  · rw [limitOfChain_eval_pos hR δ hδ ht, (ht i).choose_spec]
    exact congrArg some (StageType.reduceType_limitOfChain (hR.isReduceChain_choose ht) δ hδ i)
  · rw [limitOfChain_eval_neg hR δ hδ ht]
    push Not at ht
    obtain ⟨j, hj⟩ := ht
    cases hcase : (R i).eval t with
    | none => rfl
    | some q =>
      exact absurd ((hR.exists_eval_eq_some_iff t i j).mp ⟨q, hcase⟩) (not_exists.mpr hj)

/-- Elimination for a label of the limit: the tuple is everywhere defined and the label is the
stage-type limit of its chain. -/
theorem IsReductChain.exists_eq_limit (hR : IsReductChain hc R) {δ : LimitStage}
    {hδ : ∀ i, c i ≤ δ} {n : ℕ} {t : Fin n ↪ M} {p : S δ.1 n}
    (hp' : (limitOfChain hc R hR δ hδ).eval t = some p) :
    ∃ ht : ∀ j, ∃ q : S (c j).1 n, (R j).eval t = some q,
      p = StageType.limitOfChain (hR.isReduceChain_choose ht) δ hδ := by grind [limitOfChain_eval_pos, limitOfChain_eval_neg]

/-- **Exact parent consistency passes to the limit** (clause (2)): on a visible face the two
labels have equal reductions at every stage — the chain's consistency plus
`typeMap_reduceType_comm` — hence are equal by cofinal-reduction injectivity; on an invisible
face both sides are undefined (visibility reads the scheme, which the whole chain shares). -/
theorem IsReductChain.isExactParentConsistent_limit (hR : IsReductChain hc R)
    (hcons : ∀ i, (R i).IsExactParentConsistent) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ)
    (hcof : ∀ γ : Ordinal.{0}, γ < δ.1 → ∃ i, γ < (c i).1) :
    (limitOfChain hc R hR δ hδ).IsExactParentConsistent := by
  intro m n t q f hq
  obtain ⟨ht, rfl⟩ := hR.exists_eq_limit hq
  set L := StageType.limitOfChain (hR.isReduceChain_choose ht) δ hδ with hLdef
  change (limitOfChain hc R hR δ hδ).eval (f.trans t) = typeMap f L
  by_cases hvis : Finset.univ.image f ∈ L.scheme.scheme.plan
  · -- the face is visible at every stage
    have hvis_j : ∀ j, Finset.univ.image f ∈ ((ht j).choose).scheme.scheme.plan := fun j =>
      StageType.limitOfChain_scheme_eq (hR.isReduceChain_choose ht) δ hδ j ▸ hvis
    have htf : ∀ j, ∃ q' : S (c j).1 m, (R j).eval (f.trans t) = some q' := by
      intro j
      refine ⟨((ht j).choose).restrictFace f (hvis_j j), ?_⟩
      rw [hcons j t _ f (ht j).choose_spec]
      apply typeMap_eq_some
    rw [limitOfChain_eval_pos hR δ hδ htf, typeMap_eq_some f L hvis]
    refine congrArg some (StageType.eq_of_forall_reduceType_eq hδ hcof fun i => ?_)
    rw [StageType.reduceType_limitOfChain (hR.isReduceChain_choose htf) δ hδ i]
    -- compute the reduction of the restriction through `typeMap_reduceType_comm`
    have h1 := typeMap_reduceType_comm (c i).2 (hδ i) f L
    rw [StageType.reduceType_limitOfChain (hR.isReduceChain_choose ht) δ hδ i,
      typeMap_eq_some f L hvis, Option.map_some] at h1
    have h4 : (htf i).choose = ((ht i).choose).restrictFace f (hvis_j i) := by
      have hcomb := ((htf i).choose_spec).symm.trans (hcons i t _ f (ht i).choose_spec)
      exact Option.some_inj.mp (hcomb.trans (typeMap_eq_some f _ (hvis_j i)))
    rw [h4]
    exact Option.some_inj.mp ((typeMap_eq_some f _ (hvis_j i)).symm.trans h1)
  · -- the face is invisible at every stage
    rw [typeMap_eq_none f L hvis]
    refine limitOfChain_eval_neg hR δ hδ fun hall => ?_
    obtain ⟨q0, hq0⟩ := hall 0
    have h0 := hcons 0 t _ f (ht 0).choose_spec
    rw [hq0] at h0
    have hvis0 : Finset.univ.image f ∈ ((ht 0).choose).scheme.scheme.plan := by
      by_contra hno
      exact Option.some_ne_none q0 (h0.trans (typeMap_eq_none f _ hno))
    exact hvis
      ((StageType.limitOfChain_scheme_eq (hR.isReduceChain_choose ht) δ hδ 0).symm ▸ hvis0)

/-- **Initial-segment covering passes to the limit** (clause (3)): the covering witness of any
one stage is everywhere defined, hence defined at the limit. -/
theorem IsReductChain.isInitialSegmentCovering_limit (hR : IsReductChain hc R)
    (hcov : (R 0).IsInitialSegmentCovering) (δ : LimitStage) (hδ : ∀ i, c i ≤ δ) :
    (limitOfChain hc R hR δ hδ).IsInitialSegmentCovering := by
  intro n t
  obtain ⟨k, s, hst, hsome⟩ := hcov t
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
  refine ⟨k, s, hst, ?_⟩
  rw [limitOfChain_eval_pos hR δ hδ (hR.forall_exists_of_eval_eq_some hq)]
  rfl

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
  rw [← reduct_limitOfChain hR δ hδ i] at h
  exact h.of_reduct (hδ i) hcons hpt hU

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
  have hcons : (KnightRealization.limitOfChain hc R hR δ hδ).IsExactParentConsistent :=
    hR.isExactParentConsistent_limit (fun i => (hmod i).consistent) δ hδ hcof
  refine ⟨(hmod 0).nonempty, hcons,
    hR.isInitialSegmentCovering_limit (hmod 0).covering δ hδ, ?_, ?_, ?_, ?_⟩
  all_goals
    intro n t p hp
    have eval_i (i : ℕ) : (R i).eval t = some (reduceType (c i).2 (hδ i) p) := by
      rw [← reduct_limitOfChain hR δ hδ i, Realization.reduct_eval, hp]
      rfl
  · intro D hD
    exact hR.realizesSome_limit hcons hp 0 (fun _ h => h)
      ((hmod 0).genSat t _ (eval_i 0) D ⟨hD.visible, hD.restrict⟩)
  · intro D hD q' hq' hext
    obtain ⟨i, hi⟩ := StageType.exists_truncExt_label_id hc hcof p
    have hD' : ExtendsDomain (reduceType (c i).2 (hδ i) p) D := ⟨hD.visible, hD.restrict⟩
    refine hR.realizesSome_limit hcons hp i ?_
      ((hmod i).bottomPattern t _ (eval_i i) D hD' q' hq' fun d => ?_)
    · rintro q ⟨hq, hpat⟩
      exact ⟨hq, fun d => truncExt_eq_bot_iff.symm.trans (hpat d)⟩
    · exact (hext d).trans (hi d).symm
  · intro γ hγ hγδ
    obtain ⟨i, hi⟩ := hcof γ hγδ
    exact hR.realizesSome_limit hcons hp i (fun _ => (reduce_mem_uniformity hi (hδ i)).mp)
      ((hmod i).uniformity t _ (eval_i i) γ hγ hi)
  · intro γ hγδ
    obtain ⟨i, hi⟩ := hcof γ hγδ
    exact hR.realizesSome_limit hcons hp i (fun _ => (reduce_mem_dominance hi (hδ i)).mp)
      ((hmod i).highGradeDominance t _ (eval_i i) γ hi)

end KnightRealization

end VaughtConjecture.Knight
