/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProvisionalRatchet
public import VaughtConjecture.Knight.FiniteBandReadback
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Knight.Rank

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace StageType

variable {α β : Ordinal.{0}} {n m : ℕ}

/-- A cell of full grade has full scope. -/
theorem scope_eq_univ_of_grade_eq {q : S β n} {Θ : Cell q.scheme.scheme}
    (h : q.scheme.scheme.grade Θ = n) : q.scheme.scheme.scope Θ = Finset.univ := by
  apply Finset.eq_univ_of_card
  refine le_antisymm (Finset.card_le_univ _) ?_
  have := q.scheme.scheme.grade_le_card_scope Θ
  simp_all

/-- A full-grade `∞`-cell makes the top grade the arity. -/
theorem topGrade_eq_of_top_fullGrade {q : S β n} {Θ : Cell q.scheme.scheme}
    (hgr : q.scheme.scheme.grade Θ = n) (htop : q.label Θ = ⊤) : q.topGrade = n := by
  have hmem : n ∈ q.topGrades := ⟨Θ, scope_eq_univ_of_grade_eq hgr, hgr, htop⟩
  have hbdd := q.topGrades_bddAbove
  refine le_antisymm ?_ (le_csSup hbdd hmem)
  obtain ⟨Θ', hsc, hgr', -⟩ : q.topGrade ∈ q.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  rw [← hgr']
  refine (q.scheme.scheme.grade_le_card_scope Θ').trans ?_
  simp_all

/-- `mapCell` does not see the reduction (the schemes agree definitionally). -/
theorem mapCell_reduceType (hα : Order.IsSuccLimit α) (h : α ≤ β) {q : S β n} {p : S β m}
    {f : Fin m ↪ Fin n} (hpq : typeMap f q = some p)
    (hpq' : typeMap f (reduceType hα h q) = some (reduceType hα h p))
    (Xi : Cell p.scheme.scheme) : mapCell hpq' Xi = mapCell hpq Xi := rfl

theorem typeMap_reduceType_eq_some (hα : Order.IsSuccLimit α) (h : α ≤ β) {q : S β n}
    {p : S β m} {f : Fin m ↪ Fin n} (hpq : typeMap f q = some p) :
    typeMap f (reduceType hα h q) = some (reduceType hα h p) := by
  rw [typeMap_reduceType_comm, hpq, Option.map_some]

/-- **Lemma 5.5.2, `∞` case**: if `N(Ξ) = ∞` and some cell `Σ` has `N(Σ) = α + i₀` with
`i₀ < p.topGrade^q`, then the reduct's provisional value at `Ξ` is not `α + k` for any `k <
    p.topGrade^q`. -/
theorem not_isProvisionalValue_of_expansion_top (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    {q : S β n} (Xi Sig : Cell q.scheme.scheme) (hXi : q.label Xi = ⊤) {i₀ : ℕ}
    (hSig : q.label Sig = ofOrd (α + i₀)) (hi₀ : i₀ < (reduceType hα hαβ q).topGrade)
    {k : ℕ} (hk : k < (reduceType hα hαβ q).topGrade) :
    ¬ (reduceType hα hαβ q).IsProvisionalValue Xi (ofOrd (α + k)) := by
  set p := reduceType hα hαβ q with hp
  have hptop : p.label Xi = ⊤ := truncExt_eq_top_iff.mpr (by simp [hXi])
  have hpSig : p.label Sig = ⊤ := truncExt_eq_top_iff.mpr (by simp [hSig])
  have hiK : ofOrd (α + i₀) < ofOrd (α + p.topGrade) := by simp [hi₀]
  have hcap : p.ProvisionalCap Xi := by
    obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop⟩ := exists_top_witness hptop
    have hgr' : q.scheme.scheme.grade Θ = p.topGrade := hgr
    have hSigΘ : GradedLe (q.scheme.scheme.cell Sig) (q.scheme.scheme.cell Θ) := by
      constructor
      · change q.scheme.scheme.scope Sig ⊆ q.scheme.scheme.scope Θ
        rw [show q.scheme.scheme.scope Θ = Finset.univ from hsc]
        exact Finset.subset_univ _
      · change q.scheme.scheme.grade Sig ≤ q.scheme.scheme.grade Θ
        exact hgr' ▸ grade_le_topGrade_of_top hpSig
    obtain ⟨g, σ, hganti, -, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
    have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ :=
      hgr' ▸ reduced_label_ge_add_grade hα hαβ hΘtop
    let a := q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩
    let u := q.scheme.rows.E Θ ⟨Sig, hSigΘ⟩
    have ha : ofOrd (α + p.topGrade) ≤ σ a := by
      have h := hloc ⟨Xi, hXiΘ⟩
      change min (q.label Xi) (q.label Θ) = _ at h
      rw [hXi, min_eq_right le_top] at h
      exact hΘK.trans (h.trans_le (min_le_left _ _))
    obtain ⟨hu, huK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Sig, hSigΘ⟩)
      (by change q.label Sig < _; rw [hSig]; exact hiK.trans_le hΘK)
    rw [hgr'] at huK
    change σ u = q.label Sig at hu
    rw [hSig] at hu
    obtain ⟨μ, hμ, hf, hband⟩ := lift_visibility_band hα hi₀ hu (hσ5 u _ huK)
    refine ⟨Θ, hXiΘ, ⟨Sig, hSigΘ⟩, hsc, hgr, hΘtop, hpSig, ?_⟩
    change extVisibilityReplace u p.topGrade p.topGrade ≤ a
    rw [hμ, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hf]
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p.topGrade ≠ 0)
    by_contra! hl
    have hle : a ≤ ofOrd (limitPart μ + j) := by
      apply le_of_lt_ofOrd_add_one
      simpa only [hj, Nat.cast_succ, add_assoc] using hl
    have h := (hσmono hle).trans_eq (hband j (by omega))
    have hj' : ofOrd (α + j) < ofOrd (α + p.topGrade) := by simp [hj]
    exact (not_le_of_gt hj') (ha.trans h)
  rintro (⟨hne, -⟩ | ⟨-, -, heq⟩ | ⟨-, hncap, -⟩)
  · exact hne hptop
  · simp_all
  · exact hncap hcap

end StageType

namespace KnightRealization

open StageType

variable {α β : LimitStage} {M : Type w}

/-- The reduct labels what `N` labels. -/
theorem reduct_eval_some (hαβ : α ≤ β) {N : KnightRealization β M} {n : ℕ} {t : Fin n ↪ M}
    {p' : S β.1 n} (hp' : N.eval t = some p') :
    (N.reduct hαβ).eval t = some (reduceType α.2 hαβ p') := by aesop

/-- A labelled cover of `x` containing `s`, of arity `≥ k`. -/
theorem IsModel.exists_labelledExt_le_arity {N : KnightRealization β M} (hN : N.IsModel)
    (x : N.LabelledExt) (k : ℕ) {m : ℕ} (s : Fin m ↪ M) :
    ∃ y : N.LabelledExt, x ≤ y ∧ k ≤ y.arity ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s := by
  obtain ⟨y₁, hxy₁, g₁, hg₁⟩ := hN.exists_labelledExt_le x s
  have := hN.infinite_carrier
  let bt : Fin k ↪ M := Fin.valEmbedding.trans (Infinite.natEmbedding M)
  obtain ⟨y₂, hy₁y₂, g₂, -⟩ := hN.exists_labelledExt_le y₁ bt
  obtain ⟨f₁₂, hf₁₂, -⟩ := id hy₁y₂
  refine ⟨y₂, hxy₁.trans hy₁y₂, ?_, g₁.trans f₁₂, ?_⟩
  · have := Fintype.card_le_of_embedding g₂
    simp_all
  · rw [Function.Embedding.trans_assoc, hf₁₂, hg₁]

/-- A labelled cover of `x` containing `s`, of arity `> k`, with a full-grade cell labelled
above `α` (high-grade dominance in `N` at `α < α + ω`). -/
theorem IsModel.exists_cover_fullGrade (hβ : β.1 = α.1 + Ordinal.omega0)
    {N : KnightRealization β M} (hN : N.IsModel) (x : N.LabelledExt) (k : ℕ) {m : ℕ}
    (s : Fin m ↪ M) :
    ∃ y : N.LabelledExt, x ≤ y ∧ k < y.arity ∧ (∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s) ∧
      ∃ Θ : Cell y.type.scheme.scheme, y.type.scheme.scheme.grade Θ = y.arity ∧
        ofOrd α.1 < y.type.label Θ := by
  obtain ⟨y₂, hxy₂, hk, g, hg⟩ := hN.exists_labelledExt_le_arity x k s
  have hlt : α.1 < β.1 := by simp_all
  obtain ⟨z, hz, q'', ⟨Θ, hgr, hlab⟩, hcof, heval⟩ :=
    hN.highGradeDominance y₂.tuple y₂.type y₂.eval_eq α.1 hlt
  let y : N.LabelledExt := LabelledExt.mk (y₂.arity + 1) (snoc y₂.tuple z hz) q'' heval
  have hy₂y : y₂ ≤ y := ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc y₂.tuple z hz, hcof⟩
  obtain ⟨f, hf, -⟩ := id hy₂y
  refine ⟨y, hxy₂.trans hy₂y, Nat.lt_succ_of_le hk, ⟨g.trans f, ?_⟩, Θ, hgr, hlab⟩
  rw [Function.Embedding.trans_assoc, hf, hg]

variable {N : KnightRealization β M}

/-- **Case `N(Ξ) < α`**: the label is kept by every cover, so it stabilizes. -/
theorem stabilizesTo_of_lt (hαβ : α ≤ β) (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) (hlt : p'.label Xi < ofOrd α.1) :
    KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi (p'.label Xi) := by
  intro m s
  let x : KnightRealization.LabelledExt (N.reduct hαβ) := ⟨n, t, reduceType α.2 hαβ p',
      reduct_eval_some hαβ hp'⟩
  obtain ⟨y, ⟨f, hf, hpq⟩, g, hg⟩ :=
    exists_labelledExt_le (hN.consistent_reduct hαβ) (hN.covering_reduct hαβ) x s
  refine ⟨y.arity, y.tuple, g, f, y.type, hpq, y.eval_eq, hg, hf, Or.inl ⟨?_, ?_⟩⟩
  · rw [label_mapCell hpq Xi]
    change truncExt α.1 (p'.label Xi) ≠ ⊤
    rw [truncExt_id_of_lt hlt]
    aesop
  · rw [label_mapCell hpq Xi]
    change p'.label Xi = truncExt α.1 (p'.label Xi)
    rw [truncExt_id_of_lt hlt]

/-- **Case `N(Ξ) = α + i`**: covers of top grade `> i` compute the provisional value `α + i`. -/
theorem stabilizesTo_of_band (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0) (hN : N.IsModel)
    {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) {i : ℕ}
    (hXi : p'.label Xi = ofOrd (α.1 + i)) :
    KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi (ofOrd (α.1 +
        i)) := by
  intro m s
  let x : N.LabelledExt := ⟨n, t, p', hp'⟩
  obtain ⟨y, ⟨f, hf, hpq'⟩, hk, ⟨g, hg⟩, Θ, hgr, hlab⟩ := hN.exists_cover_fullGrade hβ x i s
  have hpq : typeMap f (reduceType α.2 hαβ y.type) = some (reduceType α.2 hαβ p') :=
    typeMap_reduceType_eq_some α.2 hαβ hpq'
  refine ⟨y.arity, y.tuple, g, f, reduceType α.2 hαβ y.type, hpq, reduct_eval_some hαβ y.eval_eq,
    hg, hf, ?_⟩
  rw [mapCell_reduceType α.2 hαβ hpq' hpq Xi]
  have hK : (reduceType α.2 hαβ y.type).topGrade = y.arity :=
    topGrade_eq_of_top_fullGrade (q := reduceType α.2 hαβ y.type) hgr
      (truncExt_eq_top_of_ge hlab.le)
  refine isProvisionalValue_band_of_expansion α.2 hαβ (mapCell hpq' Xi) ?_ (by omega)
  rw [label_mapCell hpq' Xi, hXi]

/-- **Case `N(Ξ) = ∞`**: no value `< α + ω` stabilizes. -/
theorem not_stabilizesTo_of_top (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) (hXi : p'.label Xi = ⊤)
    (δ : ExtOrd) (hδ : δ < ofOrd (α.1 + Ordinal.omega0)) :
    ¬ KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi δ := by
  intro hst
  have hlab_top : (reduceType α.2 hαβ p').label Xi = ⊤ := by
    change truncExt α.1 (p'.label Xi) = ⊤
    simp_all
  -- Step 1: `δ = α + k` for some `k` (any provisional value at an `∞`-cell is `≥ α`)
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, δ = ofOrd (α.1 + k) := by
    obtain ⟨m', u, g, f, q, hpq, hu, hgu, hft, hval⟩ := hst t
    refine ExtOrd.exists_nat_of_mem_band ?_ hδ
    have htop : q.label (mapCell hpq Xi) = ⊤ := by
      rw [label_mapCell (p := reduceType α.2 hαβ p') hpq Xi, hlab_top]
    rcases hval with ⟨hne, -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, j, -, rfl⟩
    all_goals simp_all
  -- Step 2: a cell `Σ` with `N(Σ) = α + i₀` (uniformity in `N` at `α`)
  have hlt : α.1 < β.1 := by simp_all
  obtain ⟨z, hz, q₁, ⟨Sig₀, hSlo, hShi⟩, hcof₁, heval₁⟩ :=
    hN.uniformity t p' hp' α.1 (Or.inr α.2) hlt
  obtain ⟨i₀, hSig₀⟩ := ExtOrd.exists_nat_of_mem_band hSlo hShi
  let x₁ : N.LabelledExt := ⟨n + 1, snoc t z hz, q₁, heval₁⟩
  -- Step 3: a cover `y ≥ x₁` of top grade `> max i₀ k`
  obtain ⟨y, ⟨f₁, hf₁, hpq₁⟩, hk, -, Θ, hgr, hlab⟩ :=
    hN.exists_cover_fullGrade hβ x₁ (max i₀ k) t
  have hKy : (reduceType α.2 hαβ y.type).topGrade = y.arity :=
    topGrade_eq_of_top_fullGrade (q := reduceType α.2 hαβ y.type) hgr
      (truncExt_eq_top_of_ge hlab.le)
  -- Step 4: a member `w` of the stable set above `y`
  obtain ⟨m', u, g, f, q, hpq, hu, hgu, hft, hval⟩ := hst y.tuple
  obtain ⟨w', hw', hqw'⟩ := Option.map_eq_some_iff.mp hu
  change reduceType α.2 hαβ w' = q at hqw'
  subst hqw'
  have hgw : typeMap g w' = some y.type := by
    have := hN.consistent u w' g hw'
    rw [hgu, y.eval_eq] at this
    solve_by_elim
  have hfw : typeMap f w' = some p' := by
    have := hN.consistent u w' f hw'
    aesop
  -- the cells of `Ξ` and `Σ` in `w`
  have hXiw : w'.label (mapCell hfw Xi) = ⊤ := by rw [label_mapCell hfw Xi, hXi]
  have hSigw : w'.label (mapCell hgw (mapCell hpq₁ Sig₀)) = ofOrd (α.1 + i₀) := by
    rw [label_mapCell hgw, label_mapCell hpq₁, hSig₀]
  -- top grades
  have hKw : y.arity ≤ (reduceType α.2 hαβ w').topGrade := by
    rw [← hKy]
    exact topGrade_le_of_typeMap_eq_some (typeMap_reduceType_eq_some α.2 hαβ hgw)
  have hi₀ : i₀ < (reduceType α.2 hαβ w').topGrade :=
    by lia
  have hkw : k < (reduceType α.2 hαβ w').topGrade :=
    by lia
  (apply not_isProvisionalValue_of_expansion_top <;> assumption)

/-- **Lemma 5.5.2 (labels)**: every label of a model-valued expansion is the stabilized value
of the source cell. -/
theorem hasStableValue_of_expansion (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) :
    KnightRealization.HasStableValue (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi (p'.label Xi) := by
  rcases ExtOrd.cases (p'.label Xi) with hb | ht | ⟨μ, hμ⟩
  · left
    refine ⟨?_, stabilizesTo_of_lt hαβ hN hp' Xi (by simp_all)⟩
    simp_all
  · right
    grind [not_stabilizesTo_of_top]
  · left
    rcases lt_or_ge μ α.1 with hlt | hge
    · refine ⟨?_, stabilizesTo_of_lt hαβ hN hp' Xi (by simp_all)⟩
      rw [hμ]
      exact ofOrd_lt_ofOrd.mpr (hlt.trans (lt_add_of_pos_right _ Ordinal.omega0_pos))
    · have hbound : p'.label Xi < ofOrd β.1 := by
        rcases p'.label_bound Xi with h | h
        · assumption
        · rw [h] at hμ
          exact absurd hμ.symm (ofOrd_ne_top μ)
      have hbound' : p'.label Xi < ofOrd (α.1 + Ordinal.omega0) := by
        simp_all
      rw [hμ] at hbound'
      obtain ⟨i, hi⟩ := ExtOrd.exists_nat_of_mem_band (x := ofOrd μ) (ofOrd_le_ofOrd.mpr hge)
        hbound'
      grind [stabilizesTo_of_band]

end KnightRealization

end VaughtConjecture.Knight

namespace VaughtConjecture.Knight.KnightRealization

open TypeTower StageType

universe w

variable {α β : LimitStage} {M : Type w}

/-- `hasStableValue_of_expansion` with the reduct type as a free variable. -/
theorem hasStableValue_of_expansion_of_eq (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    {N : KnightRealization β M} (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') {p : S α.1 n} (hp : reduceType α.2 hαβ p' = p)
    (Xi : Cell p'.scheme.scheme) :
    KnightRealization.HasStableValue (N.reduct hαβ) t p
      (SemScheme.castCell (congrArg StageType.scheme hp) Xi) (p'.label Xi) := by
  subst hp
  exact hasStableValue_of_expansion hαβ hβ hN hp' Xi

/-- **Lemma 5.5.2, label agreement**: two model-valued expansions of the same reduct agree on
every label. -/
theorem label_eq_of_expansions (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    {N N' : KnightRealization β M} (hN : N.IsModel) (hN' : N'.IsModel)
    (hred : N.reduct hαβ = N'.reduct hαβ) {n : ℕ} {t : Fin n ↪ M} {p' p'' : S β.1 n}
    (hp' : N.eval t = some p') (hp'' : N'.eval t = some p'') (hsch : p'.scheme = p''.scheme)
    (Xi : Cell p'.scheme.scheme) :
    p'.label Xi = p''.label (SemScheme.castCell hsch Xi) := by
  have hr : reduceType α.2 hαβ p' = reduceType α.2 hαβ p'' := by
    have h1 := reduct_eval_some hαβ hp'
    have h2 := reduct_eval_some hαβ hp''
    grind
  have H1 := hasStableValue_of_expansion hαβ hβ hN hp' Xi
  have H2 := hasStableValue_of_expansion_of_eq hαβ hβ hN' hp'' hr.symm
    (SemScheme.castCell hsch Xi)
  rw [← hred] at H2
  have H2' : KnightRealization.HasStableValue (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi
      (p''.label (SemScheme.castCell hsch Xi)) := H2
  exact HasStableValue.unique (hN.consistent_reduct hαβ) (hN.covering_reduct hαβ)
    (reduct_eval_some hαβ hp') H1 H2'

/-- **Successor-expansion uniqueness** (Lemma 5.5.2): two models of `S^{α+ω}` with the same
reduct to `α` are equal. -/
theorem eq_of_reduct_eq (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    {N N' : KnightRealization β M} (hN : N.IsModel) (hN' : N'.IsModel)
    (hred : N.reduct hαβ = N'.reduct hαβ) : N = N' := by
  apply Realization.ext
  intro n t
  have hr : (N.eval t).map (knightTower.reduce hαβ) = (N'.eval t).map (knightTower.reduce hαβ) :=
    congrArg (fun R : KnightRealization α M => R.eval t) hred
  rcases hp' : N.eval t with _ | p' <;> rcases hp'' : N'.eval t with _ | p''
  · rfl
  · simp_all
  · simp_all
  · congr 1
    have hsch : p'.scheme = p''.scheme := by
      rw [hp', hp''] at hr
      have hr' : reduceType α.2 hαβ p' = reduceType α.2 hαβ p'' :=
        Option.some_injective _ hr
      exact congrArg (fun q : S α.1 n => q.scheme) hr'
    have hlab := label_eq_of_expansions hαβ hβ hN hN' hred hp' hp'' hsch
    obtain ⟨sc, lab, bnd, resp⟩ := p'
    obtain ⟨sc', lab', bnd', resp'⟩ := p''
    simp only at hsch
    subst hsch
    refine StageType.ext rfl (heq_of_eq (funext fun Xi => ?_))
    tauto

/-- The block form: two models at block `ξ + 1` with the same reduct to block `ξ` are equal. -/
theorem eq_of_reduct_eq_blockStage {ξ : Ordinal.{0}}
    {N N' : KnightRealization (blockStage (ξ + 1)) M} (hN : N.IsModel) (hN' : N'.IsModel)
    (hred : N.reduct (blockStage_le_succ ξ) = N'.reduct (blockStage_le_succ ξ)) : N = N' :=
  eq_of_reduct_eq (blockStage_le_succ ξ) (blockStage_succ_toOrdinal ξ) hN hN' hred

end VaughtConjecture.Knight.KnightRealization
