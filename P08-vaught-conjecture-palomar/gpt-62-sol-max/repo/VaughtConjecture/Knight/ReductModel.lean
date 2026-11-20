/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Model
public import VaughtConjecture.Knight.Coface
public import VaughtConjecture.Knight.SuccLimitBandArithmetic

@[expose] public section

namespace VaughtConjecture.Knight

open Value ExtOrd TypeTower

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- **The `−∞`-pattern transfers across truncation of the face.**  For `p : S β n` (any stage
`β`), `D` an extension domain of `dom p`, a limit `α`, and `q'` respecting `D.rows` and
extending the **truncated** `p` (`q' ∘ cellOf = truncExt α ∘ p.label`), there is `q''`
respecting `D.rows`, extending the **untruncated** `p`, with the same `⊥`-pattern as `q'` on
every cell of `D`.  This is `exists_respects_extends_capped` at the positive cutoff
`γ = n + 1`: the capped-agreement premise holds since `n + 1 < ω ≤ α` (on a face cell either
truncation is the identity, or both sides cap to `γ`), and `q'' ∧ γ = q' ∧ γ` with `γ > ⊥`
preserves and reflects `⊥`. -/
theorem exists_respects_extends_of_truncated {β : Ordinal.{0}} (hα : Order.IsSuccLimit α)
    {p : S β n} {D : SemScheme (n + 1)} (hD : ExtendsDomain p D)
    {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    (hext : ∀ d, q' (hD.cellOf d) = truncExt α (p.label d)) :
    ∃ q'' : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q'' ∧
      (∀ d, q'' d = ⊥ ↔ q' d = ⊥) ∧ ∀ d, q'' (hD.cellOf d) = p.label d := by
  have hγα : ofOrd (n + 1 : ℕ) ≤ ofOrd α :=
    ofOrd_le_ofOrd.mpr
      ((Ordinal.natCast_lt_omega0 _).le.trans (Ordinal.omega0_le_of_isSuccLimit hα))
  have hne : ofOrd (n + 1 : ℕ) ≠ ⊥ := ofOrd_ne_bot _
  obtain ⟨q'', hq'', hcap, hext''⟩ := exists_respects_extends_capped hD hq'
    (by rw [extVisibilityReplace_self_iff]; exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_natCast]⟩)) (fun d => by
      rw [hext d]
      rcases le_or_gt (ofOrd α) (p.label d) with h | h
      · rw [truncExt_eq_top_of_ge h, min_eq_right le_top, min_eq_right (hγα.trans h)]
      · rw [truncExt_id_of_lt h])
  grind

end StageType

namespace KnightRealization

universe w

variable {M : Type w} {n : ℕ} {α β : LimitStage}

/-- A label of the reduct is the reduction of a label of the original. -/
theorem eval_reduct_eq_some (h : α ≤ β) {R : KnightRealization β M} {t : Fin n ↪ M}
    {p' : S α.1 n} (hp' : (R.reduct h).eval t = some p') :
    ∃ p : S β.1 n, R.eval t = some p ∧ reduceType α.2 h p = p' := by
  have hp'' : (R.eval t).map (reduceType α.2 h) = some p' := hp'
  exact Option.map_eq_some_iff.mp hp''

/-- **Realized families reduce.**  If `R` realizes some member of `U` over `t` as a coface of
`p`, and reduction sends `U` into `U'`, then the reduct realizes some member of `U'` over `t`
as a coface of `reduce p` (the coface condition by `typeMap_reduceType_comm`). -/
theorem RealizesSome.reduct (h : α ≤ β) {R : KnightRealization β M} {t : Fin n ↪ M}
    {p : S β.1 n} {U : Set (S β.1 (n + 1))} {U' : Set (S α.1 (n + 1))}
    (hU : ∀ q ∈ U, reduceType α.2 h q ∈ U') (hR : R.RealizesSome t p U) :
    RealizesSome (R.reduct h) t (reduceType α.2 h p) U' := by
  obtain ⟨y, hy, q, hqU, hqc, hq⟩ := hR
  refine ⟨y, hy, reduceType α.2 h q, hU q hqU, ?_, ?_⟩
  · exact (typeMap_reduceType_comm α.2 h Fin.castSuccEmb q).trans
      (congrArg (Option.map (reduceType α.2 h)) hqc)
  aesop

/-- Lift an actual coface from the reduct, reflecting family membership. -/
theorem RealizesSome.of_reduct {R : KnightRealization β M} (h : α ≤ β)
    {t : Fin n ↪ M} {p : S β.1 n} (hc : R.IsExactParentConsistent) (hp : R.eval t = some p)
    {U : Set (S α.1 (n + 1))} {V : Set (S β.1 (n + 1))}
    (hU : ∀ q, reduceType α.2 h q ∈ U → q ∈ V)
    (hr : RealizesSome (R.reduct h) t (reduceType α.2 h p) U) : R.RealizesSome t p V := by
  obtain ⟨y, hy, q, hq, -, hq'⟩ := hr
  obtain ⟨r, hr', rfl⟩ := eval_reduct_eq_some h hq'
  exact ⟨y, hy, r, hU r hq, isCoface_of_consistent hc hp hr', hr'⟩

theorem reduce_mem_uniformity {q : S β.1 (n + 1)} {γ : Ordinal.{0}} (hγ : γ < α.1) (h : α ≤ β) :
    reduceType α.2 h q ∈ UniformityFamily γ ↔ q ∈ UniformityFamily γ := by
  have hb := ofOrd_le_ofOrd.mpr (add_omega0_le_of_lt_isSuccLimit α.2 hγ)
  change (∃ d, ofOrd γ ≤ truncExt α.1 (q.label d) ∧
    truncExt α.1 (q.label d) < ofOrd (γ + Ordinal.omega0)) ↔
    ∃ d, ofOrd γ ≤ q.label d ∧ q.label d < ofOrd (γ + Ordinal.omega0)
  simp only [truncExt_lt_iff hb]
  constructor <;> rintro ⟨d, hl, hr⟩
  · rw [truncExt_id_of_lt (hr.trans_le hb)] at hl
    exact ⟨d, hl, hr⟩
  · exact ⟨d, hl.trans (truncExt_le_self _ _), hr⟩

theorem reduce_mem_dominance {q : S β.1 (n + 1)} {γ : Ordinal.{0}} (hγ : γ < α.1) (h : α ≤ β) :
    reduceType α.2 h q ∈ HighGradeDominanceFamily γ ↔ q ∈ HighGradeDominanceFamily γ := by
  change (∃ d, q.scheme.scheme.grade d = n + 1 ∧ ofOrd γ < truncExt α.1 (q.label d)) ↔ _
  simp only [lt_truncExt_iff (ofOrd_lt_ofOrd.mpr hγ)]
  rfl

/-- Every model clause transfers under strict vertical reduction. -/
theorem IsModel.reduct {R : KnightRealization β M} (hR : R.IsModel) (h : α ≤ β) :
    IsModel (R.reduct h) := by
  refine ⟨hR.nonempty, hR.consistent_reduct h, hR.covering_reduct h, ?_, ?_, ?_, ?_⟩
  all_goals
    intro n t p hp
    obtain ⟨q, hq, rfl⟩ := eval_reduct_eq_some h hp
  · intro D hD
    exact (hR.genSat t q hq D ⟨hD.visible, hD.restrict⟩).reduct h fun _ hr => hr
  · intro D hD q' hq' hext
    have hD' : ExtendsDomain q D := ⟨hD.visible, hD.restrict⟩
    obtain ⟨q'', hq'', hpat, hext''⟩ :=
      StageType.exists_respects_extends_of_truncated α.2 hD' hq' fun d => hext d
    refine (hR.bottomPattern t q hq D hD' q'' hq'' hext'').reduct h ?_
    rintro r ⟨hrD, hr⟩
    exact ⟨hrD, fun d => truncExt_eq_bot_iff.trans ((hr d).trans (hpat _))⟩
  · intro γ hns hγ
    exact (hR.uniformity t q hq γ hns (hγ.trans_le h)).reduct h
      fun _ => (reduce_mem_uniformity hγ h).mpr
  · intro γ hγ
    exact (hR.highGradeDominance t q hq γ (hγ.trans_le h)).reduct h
      fun _ => (reduce_mem_dominance hγ h).mpr

end KnightRealization

end VaughtConjecture.Knight
