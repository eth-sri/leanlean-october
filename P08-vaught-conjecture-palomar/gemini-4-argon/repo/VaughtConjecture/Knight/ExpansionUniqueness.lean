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

/-!
# Direct successor-expansion uniqueness (Lemma 5.5.2: "target labels are source stable
values")

Let `N` be a model of `S^{α+ω}` and `R := N ↾ α` its reduct.  For every tuple `t` labelled
`p'` in `N` and every cell `Ξ` of `p'`, the label `N(Ξ) = p'.label Ξ` is **the** stabilized
value `M⁺(Ξ)` of `R` (`HasStableValue`).  Since `HasStableValue` is functional
(`HasStableValue.unique`, Lemma 5.3.7's consequence), two model-valued expansions of `R` to
`α + ω` agree on every label — without constructing `M⁺`.

## The mechanism

The key simplification over the paper's proof: **orderliness alone** forces every cell `Θ`
with source label `∞` (`ofOrd α ≤ N(Θ)`) to carry an `N`-label `≥ α + grade Θ`
(`label_ge_add_grade`): a label in `[α, α + ω)` self-visible at grade `K` has finite part
`≥ K`.  Hence every full-scope `K^q`-grade `∞`-cell `Θ` has `N(Θ) ≥ α + K^q`, which pins the
transform of the labelling at `Θ` (Def. 2.5.4(1)) on all cells with `N`-label `< α + K^q`:
`σ (E(Θ)(Ξ)) = N(Ξ)`, with `σ (E(Θ)(Ξ)) ≤ g K^q`, so clause 5 of Def. 2.3.9 applies.

* **Band case** (`isProvisionalValue_band_of_expansion`): `N(Ξ) = α + i < α + K^q` ⇒
  `q⁺(Ξ) = α + i` (no cap: a cap witness `Σ` would push `N(Ξ) ≥ α + K^q`; the band index is
  read off `E(Θ)(Ξ)` through clause 5 at its own finite part).
* **`∞` case** (`not_isProvisionalValue_of_expansion_top`): `N(Ξ) = ∞`, `N(Σ) = α + i₀`
  with `i₀ < K^q` ⇒ `q⁺(Ξ) ≠ α + k` for every `k < K^q` (the row `E(Θ)(Ξ)` is either below
  the limit band of `E(Θ)(Σ)`, giving `N(Θ) ≤ α`; in its band, giving `N(Ξ) < α + K^q`; or
  above it, giving the cap).
* Covers of large top grade are supplied by high-grade dominance in `N` (a full-grade cell
  labelled above `α` makes `K^q` the arity), `Σ` by uniformity in `N` at `α`.

**Simpler than the paper.**  Knight's proof reads the band index off the target label through
the locality transform without the cap by the top cell's label, and refutes the cap case by
`p'(Σ) ≥ α ⇒ p'(Ξ) ≥ α + K^p`; both steps need the top cell's own label to exceed the labels
being compared, which the printed argument does not arrange.  Here that is supplied once, by
orderliness (`label_ge_add_grade`), for every full-scope top-grade cell — and the covers only
need `K^q` larger than the band index (high-grade dominance at `γ = α`), not a cell labelled
above `α + i`.  No `M⁺` is constructed: uniqueness is functionality of `HasStableValue`
(`HasStableValue.unique`, Lemma 5.3.7) plus this label lemma.

Construction-private (not root-exported).
-/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

namespace StageType

variable {α β : Ordinal.{0}} {n m : ℕ}

/-! ### Orderliness at `∞`-cells of the reduct -/

/-- A cell of full grade has full scope. -/
theorem scope_eq_univ_of_grade_eq {q : S β n} {Θ : Cell q.scheme.scheme}
    (h : q.scheme.scheme.grade Θ = n) : q.scheme.scheme.scope Θ = Finset.univ :=
  Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
    (by have := q.scheme.scheme.grade_le_card_scope Θ; simpa [h] using this))

/-- A full-grade `∞`-cell makes the top grade the arity. -/
theorem topGrade_eq_of_top_fullGrade {q : S β n} {Θ : Cell q.scheme.scheme}
    (hgr : q.scheme.scheme.grade Θ = n) (htop : q.label Θ = ⊤) : q.topGrade = n := by
  have hmem : n ∈ q.topGrades := ⟨Θ, scope_eq_univ_of_grade_eq hgr, hgr, htop⟩
  have hbdd := q.topGrades_bddAbove
  refine le_antisymm ?_ (le_csSup hbdd hmem)
  obtain ⟨Θ', hsc, hgr', -⟩ : q.topGrade ∈ q.topGrades := Nat.sSup_mem ⟨_, hmem⟩ hbdd
  simpa [← hgr', hsc] using q.scheme.scheme.grade_le_card_scope Θ'

theorem typeMap_reduceType_eq_some (hα : Order.IsSuccLimit α) (h : α ≤ β) {q : S β n}
    {p : S β m} {f : Fin m ↪ Fin n} (hpq : typeMap f q = some p) :
    typeMap f (reduceType hα h q) = some (reduceType hα h p) := by
  rw [typeMap_reduceType_comm, hpq, Option.map_some]

/-! ### The `∞` case -/

/-- **Lemma 5.5.2, `∞` case**: if `N(Ξ) = ∞` and some cell `Σ` has `N(Σ) = α + i₀` with
`i₀ < p.topGrade^q`, then the reduct's provisional value at `Ξ` is not `α + k` for any `k <
    p.topGrade^q`. -/
theorem not_isProvisionalValue_of_expansion_top (hα : Order.IsSuccLimit α) (hαβ : α ≤ β)
    {q : S β n} (Xi Sig : Cell q.scheme.scheme) (hXi : q.label Xi = ⊤) {i₀ : ℕ}
    (hSig : q.label Sig = ofOrd (α + i₀)) (hi₀ : i₀ < (reduceType hα hαβ q).topGrade)
    {k : ℕ} (hk : k < (reduceType hα hαβ q).topGrade) :
    ¬ (reduceType hα hαβ q).IsProvisionalValue Xi (ofOrd (α + k)) := by
  set p := reduceType hα hαβ q
  have hptop : p.label Xi = ⊤ := by change truncExt α (q.label Xi) = ⊤; rw [hXi, truncExt_top]
  have hpSig : p.label Sig = ⊤ := by
    change truncExt α (q.label Sig) = ⊤
    rw [hSig]
    exact truncExt_eq_top_of_ge (ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le))
  have hi₀K : ofOrd (α + i₀) < ofOrd (α + p.topGrade) :=
    ofOrd_lt_ofOrd.mpr ((add_lt_add_iff_left α).mpr (Nat.cast_lt.mpr hi₀))
  have hcap : p.ProvisionalCap Xi := by
    obtain ⟨Θ, hXiΘ, hsc, hgr, hΘtop⟩ := exists_top_witness hptop
    have hSigΘ : GradedLe (q.scheme.scheme.cell Sig) (q.scheme.scheme.cell Θ) :=
      ⟨by change _ ⊆ p.scheme.scheme.scope Θ; rw [hsc]; exact Finset.subset_univ _,
       by change _ ≤ p.scheme.scheme.grade Θ; rw [hgr]; exact grade_le_topGrade_of_top hpSig⟩
    obtain ⟨g, σ, hganti, hσbot, hσmono, hσ5, hloc, hΘg⟩ := locality_label_data q Θ
    have hΘK : ofOrd (α + p.topGrade) ≤ q.label Θ := by
      simpa [show q.scheme.scheme.grade Θ = p.topGrade from hgr] using
        label_ge_add_grade hα (q := q) Θ (truncExt_eq_top_iff.mp hΘtop)
    set a := q.scheme.rows.E Θ ⟨Xi, hXiΘ⟩
    set u := q.scheme.rows.E Θ ⟨Sig, hSigΘ⟩
    have hσa : ofOrd (α + p.topGrade) ≤ σ a := by
      have hd := hloc ⟨Xi, hXiΘ⟩
      change min (q.label Xi) (q.label Θ) = min (σ a) (g (q.scheme.scheme.grade Xi)) at hd
      rw [hXi, min_eq_right le_top] at hd
      exact hΘK.trans (hd.le.trans (min_le_left _ _))
    obtain ⟨hσu, hσuK⟩ := sigma_eq_of_lt_label hganti hΘg (hloc ⟨Sig, hSigΘ⟩)
      (by rw [hSig]; exact hi₀K.trans_le hΘK)
    change σ u = q.label Sig at hσu
    change σ u ≤ g (q.scheme.scheme.grade Θ) at hσuK
    rw [show q.scheme.scheme.grade Θ = p.topGrade from hgr] at hσuK
    rw [hSig] at hσu
    rcases ExtOrd.cases u with hb | ht | ⟨μ, hμ⟩
    · rw [hb, hσbot] at hσu; exact absurd hσu.symm (ofOrd_ne_bot _)
    · exact absurd (hσa.trans ((hσmono le_top).trans (ht ▸ hσu).le)) (not_le.mpr hi₀K)
    · have hfpα : finitePart (α + i₀) < p.topGrade := by
        rw [finitePart_succLimit_add_nat hα]; exact hi₀
      have h5K := hσ5 u p.topGrade hσuK p.topGrade le_rfl
      rw [hσu, hμ, extVisibilityReplace_ofOrd, extVisibilityReplace_ofOrd,
        visibilityReplace_of_finitePart_lt hfpα, limitPart_succLimit_add_nat hα] at h5K
      have hfpμ : finitePart μ < p.topGrade := by
        by_contra hge'
        rw [(visibilityReplace_self_iff μ p.topGrade).mpr (not_lt.mp hge'), ← hμ, hσu, ofOrd_inj] at h5K
        exact hi₀.ne (Nat.cast_injective (add_left_cancel h5K))
      rcases ExtOrd.cases a with hb' | ht' | ⟨ν, hν⟩
      · rw [hb', hσbot] at hσa; exact absurd hσa (not_le.mpr (bot_lt_ofOrd _))
      · exact ⟨Θ, hXiΘ, ⟨Xi, hXiΘ⟩, hsc, hgr, hΘtop, hptop, by change _ ≤ a; rw [ht']; exact le_top⟩
      · rcases lt_or_ge ν (limitPart μ) with hlo | hhi
        · have hle0 : a ≤ extVisibilityReplace u p.topGrade 0 := by
            rw [hν, hμ, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpμ,
              ofOrd_le_ofOrd, Nat.cast_zero, add_zero]
            exact hlo.le
          have h50 := hσ5 u p.topGrade hσuK 0 (Nat.zero_le _)
          rw [hσu, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpα,
            limitPart_succLimit_add_nat hα, Nat.cast_zero, add_zero] at h50
          exact (not_le_of_gt ((ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)).trans_lt hi₀K)
            (hσa.trans (h50 ▸ hσmono hle0))).elim
        · rcases lt_or_ge ν (limitPart μ + p.topGrade) with hmid | hbig
          · have hlpν : limitPart ν = limitPart μ := limitPart_eq_of_le_of_lt hhi hmid
            have hfpν : finitePart ν < p.topGrade := by
              rw [← decomposition ν, hlpν] at hmid
              exact_mod_cast (add_lt_add_iff_left _).mp hmid
            have heq : a = extVisibilityReplace u p.topGrade (finitePart ν) := by
              rw [hν, hμ, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpμ,
                ← hlpν, decomposition]
            have h5j := hσ5 u p.topGrade hσuK (finitePart ν) hfpν.le
            rw [← heq, hσu, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpα,
              limitPart_succLimit_add_nat hα] at h5j
            rw [h5j, ofOrd_le_ofOrd] at hσa
            exact (not_lt_of_ge (Nat.cast_le.mp ((add_le_add_iff_left _).mp hσa)) hfpν).elim
          · refine ⟨Θ, hXiΘ, ⟨Sig, hSigΘ⟩, hsc, hgr, hΘtop, hpSig, ?_⟩
            change extVisibilityReplace u p.topGrade p.topGrade ≤ a
            rw [hν, hμ, extVisibilityReplace_ofOrd, visibilityReplace_of_finitePart_lt hfpμ,
              ofOrd_le_ofOrd]
            exact hbig
  rintro (⟨hne, -⟩ | ⟨-, -, heq⟩ | ⟨-, hncap, -⟩)
  · exact hne hptop
  · exact hk.ne (Nat.cast_injective (add_left_cancel (ofOrd_inj.mp heq)))
  · exact hncap hcap

end StageType

/-! ### The realization level -/

namespace KnightRealization

open StageType

variable {α β : LimitStage} {M : Type w}

/-- The reduct labels what `N` labels. -/
theorem reduct_eval_some (hαβ : α ≤ β) {N : KnightRealization β M} {n : ℕ} {t : Fin n ↪ M}
    {p' : S β.1 n} (hp' : N.eval t = some p') :
    (N.reduct hαβ).eval t = some (reduceType α.2 hαβ p') := by
  rw [Realization.reduct_eval, hp']; rfl

/-- A labelled cover of `x` containing `s`, of arity `≥ k`. -/
theorem IsModel.exists_labelledExt_le_arity {N : KnightRealization β M} (hN : N.IsModel)
    (x : N.LabelledExt) (k : ℕ) {m : ℕ} (s : Fin m ↪ M) :
    ∃ y : N.LabelledExt, x ≤ y ∧ k ≤ y.arity ∧ ∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s := by
  obtain ⟨y₁, hxy₁, g₁, hg₁⟩ := hN.exists_labelledExt_le x s
  have := hN.infinite_carrier
  obtain ⟨y₂, hy₁y₂, g₂, -⟩ :=
    hN.exists_labelledExt_le y₁ (Fin.valEmbedding.trans (Infinite.natEmbedding M) : Fin k ↪ M)
  obtain ⟨f₁₂, hf₁₂, -⟩ := id hy₁y₂
  exact ⟨y₂, hxy₁.trans hy₁y₂, by simpa using Fintype.card_le_of_embedding g₂, g₁.trans f₁₂,
    by rw [Function.Embedding.trans_assoc, hf₁₂, hg₁]⟩

/-- A labelled cover of `x` containing `s`, of arity `> k`, with a full-grade cell labelled
above `α` (high-grade dominance in `N` at `α < α + ω`). -/
theorem IsModel.exists_cover_fullGrade (hβ : β.1 = α.1 + Ordinal.omega0)
    {N : KnightRealization β M} (hN : N.IsModel) (x : N.LabelledExt) (k : ℕ) {m : ℕ}
    (s : Fin m ↪ M) :
    ∃ y : N.LabelledExt, x ≤ y ∧ k < y.arity ∧ (∃ g : Fin m ↪ Fin y.arity, g.trans y.tuple = s) ∧
      ∃ Θ : Cell y.type.scheme.scheme, y.type.scheme.scheme.grade Θ = y.arity ∧
        ofOrd α.1 < y.type.label Θ := by
  obtain ⟨y₂, hxy₂, hk, g, hg⟩ := hN.exists_labelledExt_le_arity x k s
  obtain ⟨z, hz, q'', ⟨Θ, hgr, hlab⟩, hcof, heval⟩ :=
    hN.highGradeDominance y₂.tuple y₂.type y₂.eval_eq α.1
      (hβ ▸ lt_add_of_pos_right _ Ordinal.omega0_pos)
  let y : N.LabelledExt := ⟨y₂.arity + 1, snoc y₂.tuple z hz, q'', heval⟩
  have hy₂y : y₂ ≤ y := ⟨Fin.castSuccEmb, castSuccEmb_trans_snoc y₂.tuple z hz, hcof⟩
  obtain ⟨f, hf, -⟩ := id hy₂y
  exact ⟨y, hxy₂.trans hy₂y, Nat.lt_succ_of_le hk,
    ⟨g.trans f, by rw [Function.Embedding.trans_assoc, hf, hg]⟩, Θ, hgr, hlab⟩

variable {N : KnightRealization β M}

/-- **Case `N(Ξ) < α`**: the label is kept by every cover, so it stabilizes. -/
theorem stabilizesTo_of_lt (hαβ : α ≤ β) (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) (hlt : p'.label Xi < ofOrd α.1) :
    KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi (p'.label Xi) := by
  intro m s
  obtain ⟨y, ⟨f, hf, hpq⟩, g, hg⟩ :=
    exists_labelledExt_le (hN.consistent_reduct hαβ) (hN.covering_reduct hαβ)
      ⟨n, t, reduceType α.2 hαβ p', reduct_eval_some hαβ hp'⟩ s
  refine ⟨y.arity, y.tuple, g, f, y.type, hpq, y.eval_eq, hg, hf, Or.inl ?_⟩
  rw [label_mapCell hpq Xi]
  change truncExt α.1 (p'.label Xi) ≠ ⊤ ∧ p'.label Xi = truncExt α.1 (p'.label Xi)
  rw [truncExt_id_of_lt hlt]
  exact ⟨hlt.ne_top, rfl⟩

/-- **Case `N(Ξ) = α + i`**: covers of top grade `> i` compute the provisional value `α + i`. -/
theorem stabilizesTo_of_band (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0) (hN : N.IsModel)
    {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) {i : ℕ}
    (hXi : p'.label Xi = ofOrd (α.1 + i)) :
    KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi (ofOrd (α.1 +
        i)) := by
  intro m s
  obtain ⟨y, ⟨f, hf, hpq'⟩, hk, ⟨g, hg⟩, Θ, hgr, hlab⟩ :=
    hN.exists_cover_fullGrade hβ ⟨n, t, p', hp'⟩ i s
  refine ⟨y.arity, y.tuple, g, f, reduceType α.2 hαβ y.type,
    typeMap_reduceType_eq_some α.2 hαβ hpq', reduct_eval_some hαβ y.eval_eq, hg, hf, ?_⟩
  have hK : (reduceType α.2 hαβ y.type).topGrade = y.arity :=
    topGrade_eq_of_top_fullGrade (q := reduceType α.2 hαβ y.type) hgr
      (truncExt_eq_top_of_ge hlab.le)
  exact isProvisionalValue_band_of_expansion α.2 hαβ (mapCell hpq' Xi)
    (by rw [label_mapCell hpq' Xi, hXi]) (hK.symm ▸ hk)

/-- **Case `N(Ξ) = ∞`**: no value `< α + ω` stabilizes. -/
theorem not_stabilizesTo_of_top (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') (Xi : Cell p'.scheme.scheme) (hXi : p'.label Xi = ⊤)
    (δ : ExtOrd) (hδ : δ < ofOrd (α.1 + Ordinal.omega0)) :
    ¬ KnightRealization.StabilizesTo (N.reduct hαβ) t (reduceType α.2 hαβ p') Xi δ := by
  intro hst
  have hlab_top : (reduceType α.2 hαβ p').label Xi = ⊤ := by
    change truncExt α.1 (p'.label Xi) = ⊤; rw [hXi, truncExt_top]
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, δ = ofOrd (α.1 + k) := by
    obtain ⟨m', u, g, f, q, hpq, hu, hgu, hft, hval⟩ := hst t
    refine ExtOrd.exists_nat_of_mem_band ?_ hδ
    have htop : q.label (mapCell hpq Xi) = ⊤ := by
      rw [label_mapCell (p := reduceType α.2 hαβ p') hpq Xi, hlab_top]
    rcases hval with ⟨hne, -⟩ | ⟨-, -, rfl⟩ | ⟨-, -, j, -, rfl⟩
    · exact absurd htop hne
    · exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
    · exact ofOrd_le_ofOrd.mpr (le_add_of_nonneg_right zero_le)
  obtain ⟨z, hz, q₁, ⟨Sig₀, hSlo, hShi⟩, hcof₁, heval₁⟩ :=
    hN.uniformity t p' hp' α.1 (Or.inr α.2) (hβ ▸ lt_add_of_pos_right _ Ordinal.omega0_pos)
  obtain ⟨i₀, hSig₀⟩ := ExtOrd.exists_nat_of_mem_band hSlo hShi
  obtain ⟨y, ⟨f₁, hf₁, hpq₁⟩, hk, -, Θ, hgr, hlab⟩ :=
    hN.exists_cover_fullGrade hβ ⟨n + 1, snoc t z hz, q₁, heval₁⟩ (max i₀ k) t
  have hKy : (reduceType α.2 hαβ y.type).topGrade = y.arity :=
    topGrade_eq_of_top_fullGrade (q := reduceType α.2 hαβ y.type) hgr
      (truncExt_eq_top_of_ge hlab.le)
  obtain ⟨m', u, g, f, q, hpq, hu, hgu, hft, hval⟩ := hst y.tuple
  obtain ⟨w', hw', hqw'⟩ := Option.map_eq_some_iff.mp hu
  change reduceType α.2 hαβ w' = q at hqw'
  subst hqw'
  have hgw : typeMap g w' = some y.type := by
    have := hN.consistent u w' g hw'; rw [hgu, y.eval_eq] at this; exact this.symm
  have hfw : typeMap f w' = some p' := by
    have := hN.consistent u w' f hw'; rw [hft, hp'] at this; exact this.symm
  have hKw : y.arity ≤ (reduceType α.2 hαβ w').topGrade :=
    hKy ▸ topGrade_le_of_typeMap_eq_some (typeMap_reduceType_eq_some α.2 hαβ hgw)
  exact not_isProvisionalValue_of_expansion_top α.2 hαβ (mapCell (q := w') (p := p') hfw Xi)
    (mapCell hgw (mapCell hpq₁ Sig₀)) (by rw [label_mapCell hfw Xi, hXi])
    (by rw [label_mapCell hgw, label_mapCell hpq₁, hSig₀])
    ((le_max_left _ _).trans_lt (hk.trans_le hKw))
    ((le_max_right _ _).trans_lt (hk.trans_le hKw)) hval

/-- **Lemma 5.5.2 (labels)**: every label of a model-valued expansion is the stabilized value
of the source cell. -/
theorem hasStableValue_of_expansion (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    {N : KnightRealization β M} (hN : N.IsModel) {n : ℕ} {t : Fin n ↪ M} {p' : S β.1 n}
    (hp' : N.eval t = some p') {p : S α.1 n} (hp : reduceType α.2 hαβ p' = p)
    (Xi : Cell p'.scheme.scheme) :
    KnightRealization.HasStableValue (N.reduct hαβ) t p
      (SemScheme.castCell (congrArg StageType.scheme hp) Xi) (p'.label Xi) := by
  subst hp
  rcases ExtOrd.cases (p'.label Xi) with hb | ht | ⟨μ, hμ⟩
  · exact Or.inl ⟨hb ▸ bot_lt_ofOrd _, stabilizesTo_of_lt hαβ hN hp' Xi (hb ▸ bot_lt_ofOrd _)⟩
  · exact Or.inr ⟨ht, not_stabilizesTo_of_top hαβ hβ hN hp' Xi ht⟩
  · rcases lt_or_ge μ α.1 with hlt | hge
    · exact Or.inl ⟨hμ ▸ ofOrd_lt_ofOrd.mpr (hlt.trans (lt_add_of_pos_right _ Ordinal.omega0_pos)),
        stabilizesTo_of_lt hαβ hN hp' Xi (hμ ▸ ofOrd_lt_ofOrd.mpr hlt)⟩
    · have hbound' : ofOrd μ < ofOrd (α.1 + Ordinal.omega0) :=
        hμ ▸ hβ ▸ (p'.label_bound Xi).resolve_right (hμ ▸ ofOrd_ne_top μ)
      obtain ⟨i, hi⟩ := ExtOrd.exists_nat_of_mem_band (ofOrd_le_ofOrd.mpr hge) hbound'
      rw [hμ, hi]
      exact Or.inl ⟨hi ▸ hbound', stabilizesTo_of_band hαβ hβ hN hp' Xi (hμ.trans hi)⟩

/-- **Successor-expansion uniqueness** (Lemma 5.5.2): two models of `S^{α+ω}` with the same
reduct to `α` are equal. -/
theorem eq_of_reduct_eq (hαβ : α ≤ β) (hβ : β.1 = α.1 + Ordinal.omega0)
    {N N' : KnightRealization β M} (hN : N.IsModel) (hN' : N'.IsModel)
    (hred : N.reduct hαβ = N'.reduct hαβ) : N = N' := by
  refine Realization.ext fun {n} t => ?_
  have hr : (N.eval t).map (knightTower.reduce hαβ) = (N'.eval t).map (knightTower.reduce hαβ) :=
    congrArg (fun R : KnightRealization α M => R.eval t) hred
  rcases hp' : N.eval t with _ | p' <;> rcases hp'' : N'.eval t with _ | p''
  · rfl
  · rw [hp', hp''] at hr
    have : (none : Option (S α.1 n)) = some (reduceType α.2 hαβ p'') := hr
    cases this
  · rw [hp', hp''] at hr
    have : some (reduceType α.2 hαβ p') = (none : Option (S α.1 n)) := hr
    cases this
  · congr 1
    rw [hp', hp''] at hr
    have hr' : reduceType α.2 hαβ p' = reduceType α.2 hαβ p'' := Option.some_injective _ hr
    obtain ⟨sc, lab, bnd, resp⟩ := p'
    obtain ⟨sc', lab', bnd', resp'⟩ := p''
    cases congrArg StageType.scheme hr'
    refine StageType.ext rfl (heq_of_eq (funext fun Xi => ?_))
    have H1 := hasStableValue_of_expansion hαβ hβ hN hp' rfl Xi
    have H2 := hasStableValue_of_expansion hαβ hβ hN' hp'' hr'.symm Xi
    rw [← hred] at H2
    exact HasStableValue.unique (hN.consistent_reduct hαβ) (hN.covering_reduct hαβ)
      (reduct_eval_some hαβ hp') H1 H2

/-- The block form: two models at block `ξ + 1` with the same reduct to block `ξ` are equal. -/
theorem eq_of_reduct_eq_blockStage {ξ : Ordinal.{0}}
    {N N' : KnightRealization (blockStage (ξ + 1)) M} (hN : N.IsModel) (hN' : N'.IsModel)
    (hred : N.reduct (blockStage_le_succ ξ) = N'.reduct (blockStage_le_succ ξ)) : N = N' :=
  eq_of_reduct_eq (blockStage_le_succ ξ) (blockStage_succ_toOrdinal ξ) hN hN' hred
