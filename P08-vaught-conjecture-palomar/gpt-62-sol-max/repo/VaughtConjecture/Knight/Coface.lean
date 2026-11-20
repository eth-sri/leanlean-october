/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.Knight.CappedLifting

@[expose] public section

namespace VaughtConjecture.Knight

open VaughtConjecture.AmalgamationPlan

open Value ExtOrd

open CellScheme.restrictFace (toCell belowEquiv belowEquiv_symm_mk toCell_belowEquiv_symm_val
  pushGraded gradedLe_cell_pushGraded_iff)

section Below

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- A cell scheme over `Fin 0` has no cells (grades are positive and bounded by the size of
the scope). -/
theorem CellScheme.isEmpty_cell_fin0 (C : CellScheme (ι := Fin 0) Finset.univ) :
    IsEmpty (Cell C) :=
  ⟨fun d => by
    have h1 := C.grade_pos d
    have h2 := C.grade_le_card_scope d
    rw [Finset.card_eq_zero.mpr (Finset.eq_empty_of_isEmpty _)] at h2
    omega⟩

end Below

/-- Every domain on `Fin (n+1)` has a labelling respecting its rows (no stage bound): the row
of a full-grade cell `Σ ∈ D^{A,|A|}`, which respects `E⟨A,|A|⟩ = E` by consistency
(the untruncated half of Prop. 4.3.24, `StageType.ofScheme`). -/
theorem SemScheme.exists_respectsSemantics {n : ℕ} (D : SemScheme (n + 1)) :
    ∃ q : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q :=
  -- Existence alone needs neither a full-grade owner nor consistency.
  ⟨_, RespectsSemantics.bot _⟩

namespace FiniteCoverReceiving

/-- Every cell of a scheme on `m` points has grade at most `m`. -/
theorem grade_le_points {m : ℕ} (D : SemScheme m) (d : Cell D.scheme) : D.scheme.grade d ≤ m :=
  (CellScheme.grade_le_card_scope _ d).trans
    ((Finset.card_le_univ _).trans_eq (Fintype.card_fin _))

/-- Every cell lies below the full index `(univ, m)`. -/
theorem gradedLe_full {m : ℕ} (D : SemScheme m) (d : Cell D.scheme) :
    GradedLe (D.scheme.cell d) (Finset.univ, m) :=
  ⟨Finset.subset_univ _, grade_le_points D d⟩

end FiniteCoverReceiving

/-- Extend a lawful prescription on any visible face without changing the ambient cap. -/
theorem SemScheme.extend_capped {k m : ℕ} (D : SemScheme m)
    (g : Fin k ↪ Fin m) (hv : Finset.univ.image g ∈ D.scheme.plan)
    {p : Cell (D.restrictFace g hv).scheme → ExtOrd}
    (hp : RespectsSemantics (D.restrictFace g hv).rows p) {q : Cell D.scheme → ExtOrd}
    (hq : RespectsSemantics D.rows q) {γ : ExtOrd} (hγ : SelfVis m γ)
    (hcap : ∀ d, min (q (toCell D.scheme g hv d)) γ = min (p d) γ) :
    ∃ l, RespectsSemantics D.rows l ∧ (∀ d, min (l d) γ = min (q d) γ) ∧
      ∀ d, l (toCell D.scheme g hv d) = p d := by
  by_cases hk : 0 < k
  swap
  · obtain rfl : k = 0 := by omega
    exact ⟨q, hq, fun _ => rfl, fun d => ((CellScheme.isEmpty_cell_fin0 _).false d).elim⟩
  let CI : Finset (Fin m) × ℕ := (Finset.univ.image g, k)
  let BJ : Finset (Fin m) × ℕ := (Finset.univ, m)
  have hcardg : (Finset.univ.image g).card = k := by
    rw [Finset.card_image_of_injective _ g.injective, Finset.card_univ, Fintype.card_fin]
  have hkm : k ≤ m := by
    rw [← hcardg]
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have hCI : CI ∈ Plan.gradedPlan D.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨hv, hk, by grind⟩
  have hBJ : BJ ∈ Plan.gradedPlan D.scheme.plan :=
    Plan.mem_gradedPlan.mpr ⟨D.scheme.isPlan.domain_mem, hk.trans_le hkm, by
      change m ≤ (Finset.univ : Finset (Fin m)).card
      rw [Finset.card_univ, Fintype.card_fin]⟩
  have hle : GradedLe CI BJ := ⟨Finset.subset_univ _, hkm⟩
  have hpush : pushGraded g ((Finset.univ : Finset (Fin k)), k) = CI := rfl
  let pC : D.scheme.below CI → ExtOrd :=
    (fun d => p d.1) ∘ (belowEquiv D.scheme g hv hpush).symm
  have hpC : RespectsSemanticsBelow D.rows CI pC :=
    (hp.toBelow (Finset.univ, k)).of_restrictFace hpush
  have hall : ∀ d : Cell D.scheme, GradedLe (D.scheme.cell d) BJ := FiniteCoverReceiving.gradedLe_full D
  have hcapC : ∀ d : D.scheme.below CI,
      min (q (CellScheme.below.mono hle d).1) γ = min (pC d) γ := by
    intro d
    have h := hcap ((belowEquiv D.scheme g hv hpush).symm d).1
    change min (q (toCell D.scheme g hv ((belowEquiv D.scheme g hv hpush).symm d).1)) γ =
      min (p ((belowEquiv D.scheme g hv hpush).symm d).1) γ at h
    rwa [toCell_belowEquiv_symm_val] at h
  have hc : ∀ c : Cell (D.scheme.restrictFace g hv),
      GradedLe (D.scheme.cell (toCell D.scheme g hv c)) CI := fun c =>
    (gradedLe_cell_pushGraded_iff D.scheme g hv c).mp (FiniteCoverReceiving.gradedLe_full (D.restrictFace g hv) c)
  have hface : ∀ c : Cell (D.scheme.restrictFace g hv),
      pC ⟨toCell D.scheme g hv c, hc c⟩ = p c := by
    intro c
    change p ((belowEquiv D.scheme g hv hpush).symm ⟨toCell D.scheme g hv c, hc c⟩).1 = p c
    rw [belowEquiv_symm_mk]
  obtain ⟨q'', hq'', hq''γ, hq''p⟩ :=
    CoatomBoundaryExtension.lift_of_bountiful D.bountiful hCI hBJ hle
      pC (fun d => q d.1) γ hpC (hq.toBelow BJ) hγ hcapC
  refine ⟨fun d => q'' ⟨d, hall d⟩, hq''.toRespects hall, by solve_by_elim,
    fun c => ?_⟩
  calc q'' ⟨toCell D.scheme g hv c, hall _⟩
      = q'' (CellScheme.below.mono hle ⟨toCell D.scheme g hv c, hc c⟩) := rfl
    _ = pC ⟨toCell D.scheme g hv c, hc c⟩ := hq''p _
    _ = p c := hface c

namespace StageType

variable {α : Ordinal.{0}} {n : ℕ}

/-- The stage type at a limit stage `α` on the domain `D` obtained by reducing a labelling `q'`
respecting the rows of `D` (no stage bound on `q'`): labels `truncExt α ∘ q'` (Def. 3.1.2),
respect by `RespectsSemantics.truncate` (Lemma 3.1.3, reduction half).  `StageType.ofScheme`
is the instance at the row of a full-grade cell. -/
noncomputable def ofRespects (hα : Order.IsSuccLimit α) (D : SemScheme n)
    (q' : Cell D.scheme → ExtOrd) (hq' : RespectsSemantics D.rows q') : S α n where
  scheme := D
  label d := truncExt α (q' d)
  label_bound _ := truncExt_bound α _
  respects := hq'.truncate hα

/-- Truncation fixes a prescribed stage-valued face. -/
theorem typeMap_ofRespects {m : ℕ} (hα : Order.IsSuccLimit α) {D : SemScheme m}
    (g : Fin n ↪ Fin m) (hv : Finset.univ.image g ∈ D.scheme.plan) {p : S α n}
    (hs : D.restrictFace g hv = p.scheme) {q : Cell D.scheme → ExtOrd}
    (hq : RespectsSemantics D.rows q)
    (hext : ∀ d, q (toCell D.scheme g hv d) = p.label (SemScheme.castCell hs d)) :
    typeMap g (ofRespects hα D q hq) = some p := by
  rw [typeMap_eq_some _ _ hv, Option.some.injEq]
  have hl : ∀ d, truncExt α (q (toCell D.scheme g hv d)) = p.label (SemScheme.castCell hs d) :=
    fun d => (congrArg (truncExt α) (hext d)).trans (truncExt_id_of_bound (p.label_bound _))
  obtain ⟨ps, pl, pb, pr⟩ := p
  dsimp only at hs hl ⊢
  cases hs
  exact StageType.ext rfl (heq_of_eq (funext hl))

theorem isCoface_ofRespects (hα : Order.IsSuccLimit α) {p : S α n} {D : SemScheme (n + 1)}
    (hD : ExtendsDomain p D) {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    (hext : ∀ d, q' (hD.cellOf d) = p.label d) : IsCoface p (ofRespects hα D q' hq') := by
  obtain ⟨ps, pl, pb, pr⟩ := p
  obtain ⟨hv, hs⟩ := hD
  dsimp only at hs
  cases hs
  exact typeMap_ofRespects hα Fin.castSuccEmb hv rfl hq' hext

/-- Capped extension along the initial face. -/
theorem exists_respects_extends_capped {p : S α n} {D : SemScheme (n + 1)}
    (hD : ExtendsDomain p D) {q' : Cell D.scheme → ExtOrd} (hq' : RespectsSemantics D.rows q')
    {γ : ExtOrd} (hγ : extVisibilityReplace γ (n + 1) (n + 1) = γ)
    (hcap : ∀ d, min (q' (hD.cellOf d)) γ = min (p.label d) γ) :
    ∃ q'' : Cell D.scheme → ExtOrd, RespectsSemantics D.rows q'' ∧
      (∀ d, min (q'' d) γ = min (q' d) γ) ∧ ∀ d, q'' (hD.cellOf d) = p.label d := by
  obtain ⟨ps, pl, pb, pr⟩ := p
  obtain ⟨hv, hs⟩ := hD
  dsimp only at hs
  cases hs
  exact D.extend_capped Fin.castSuccEmb hv pr hq' hγ hcap

/-- **Bountifulness at the cutoff `γ = −∞` extends `p` to any extension domain** — the case
`γ = ⊥` of `exists_respects_extends_capped`.  For `p : S α n` and `D` a domain on `n+1` with
`D⟨n,n⟩ = dom p`, there is a labelling of `D` respecting its rows (no stage bound) and agreeing
with `p.label` on the cells of the old face: take any respecting labelling `q₀` of `D`
(`SemScheme.exists_respectsSemantics`) as the large labelling; at `γ = ⊥` the self-visibility
premise is `extVisibilityReplace_bot` and the capped-agreement premise
`(q₀ ∧ ⊥) ↾ D⟨C,m+1⟩ = p ∧ ⊥` is automatic (both sides are `⊥`); the conclusion
`q' ∧ ⊥ = q₀ ∧ ⊥` is vacuous and is discarded, and `q' ↾ dom p = p` is literal agreement. -/
theorem exists_respects_extends {p : S α n} {D : SemScheme (n + 1)} (hD : ExtendsDomain p D) :
    ∃ q' : Cell D.scheme → ExtOrd,
      RespectsSemantics D.rows q' ∧ ∀ d, q' (hD.cellOf d) = p.label d := by
  obtain ⟨q₀, hq₀⟩ := D.exists_respectsSemantics
  obtain ⟨q', hq', -, hext⟩ := exists_respects_extends_capped hD hq₀
    (extVisibilityReplace_bot _ _) (fun d => by simp)
  tauto

/-- **Cofaces over a given extension domain** (Prop. 4.3.23 for a given `D`, from
bountifulness alone): at a limit stage `α`, every extension domain `D` of `dom p`
(`ExtendsDomain p D`) carries a coface of `p`.  Built from `exists_respects_extends`
(bountifulness at `γ = ⊥`) and `isCoface_ofRespects` (truncation to `α`). -/
theorem exists_coface_of_extendsDomain (hα : Order.IsSuccLimit α) (p : S α n)
    (D : SemScheme (n + 1)) (hD : ExtendsDomain p D) :
    ∃ q : S α (n + 1), q.scheme = D ∧ IsCoface p q := by
  obtain ⟨q', hq', hext⟩ := exists_respects_extends hD
  exact ⟨ofRespects hα D q' hq', rfl, isCoface_ofRespects hα hD hq' hext⟩

/-- **Def. 3.2.1(4)(a)(ii) is never vacuous**: for `D` an extension domain of `dom p` and `q'`
a labelling of `D` respecting its rows (no stage bound) and extending `p` along the cell map
of the initial face, the prescribed-`−∞`-pattern family `BottomPatternFamily D q'` contains a
coface of `p` — the reduction of `q'` itself: `truncExt α` preserves and reflects `⊥`
(`truncExt_eq_bot_iff`), so the `−∞`-pattern on `D^{≤ n}` is that of `q'`, and it fixes `p`
on the face (`isCoface_ofRespects`). -/
theorem bottomPatternFamily_nonempty (hα : Order.IsSuccLimit α) {p : S α n}
    {D : SemScheme (n + 1)} (hD : ExtendsDomain p D) (q' : Cell D.scheme → ExtOrd)
    (hq' : RespectsSemantics D.rows q') (hext : ∀ d, q' (hD.cellOf d) = p.label d) :
    ∃ q ∈ BottomPatternFamily (α := α) D q', IsCoface p q :=
  ⟨ofRespects hα D q' hq', ⟨rfl, fun _ => truncExt_eq_bot_iff⟩, isCoface_ofRespects hα hD hq' hext⟩

end StageType

end VaughtConjecture.Knight
