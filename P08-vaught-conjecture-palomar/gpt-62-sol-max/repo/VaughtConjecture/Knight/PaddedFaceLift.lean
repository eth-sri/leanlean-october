/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedOwnerRepair
public import VaughtConjecture.Knight.SemScheme
public import VaughtConjecture.Knight.SingleFaceTailRestoration

@[expose] public section

namespace VaughtConjecture.Knight.PaddedFaceLift

open Transform Value ExtOrd GradeTailRestoration CoatomBoundaryExtension

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {A : Finset ι} {B : Finset κ}
  {D : CellScheme B} {E : CellScheme A} {J J₀ : Finset κ × ℕ} {j : ℕ}

abbrev Agreement (emb : D.below J → E.below (A, j))
    (p : D.below J → ExtOrd) (q : E.below (A, j) → ExtOrd) (γ : ExtOrd) : Prop :=
  ∀ d, min (q (emb d)) γ = min (p d) γ

abbrev Result (re : Semantics E) (emb : D.below J → E.below (A, j))
    (p : D.below J → ExtOrd) (q : E.below (A, j) → ExtOrd) (γ : ExtOrd) : Prop :=
  ∃ r, RespectsSemanticsBelow re (A, j) r ∧ (∀ d, r (emb d) = p d) ∧
    ∀ d, min (r d) γ = min (q d) γ

abbrev Lift (rd : Semantics D) (re : Semantics E) (emb : D.below J → E.below (A, j)) : Prop :=
  ∀ {p q}, RespectsSemanticsBelow rd J p → RespectsSemanticsBelow re (A, j) q →
    ∀ {γ}, SelfVis j γ → Agreement emb p q γ → Result re emb p q γ

abbrev Restore (rd : Semantics D) (re : Semantics E) (emb : D.below J → E.below (A, j)) : Prop :=
  ∀ {p u}, RespectsSemanticsBelow rd J p → RespectsSemanticsBelow re (A, j) u →
    ∀ {M}, SelfVis j M → (∀ d, u (emb d) = min (p d) M) → (∀ d, u d ≤ M) →
    (∀ d, D.grade d.1 = j → p d ≤ M) → Result re emb p u M

variable {rd : Semantics D} {re : Semantics E}

/-- Transport the predecessor lift, then replace the lower part of the ambient
without changing any upper locality condition. -/
theorem restore_of_lower {k : ℕ} {E₀ : CellScheme A} {re₀ : Semantics E₀}
    {emb : D.below J → E.below (A, k + 1)} {lo : D.below J₀ → E₀.below (A, k)}
    (hJ : GradedLe J₀ J) (hj : J.2 ≤ k + 1)
    (cut : ∀ d : D.below J, D.grade d.1 ≤ k → GradedLe (D.cell d.1) J₀)
    (hgrade : ∀ d, E.grade (emb d).1 = D.grade d.1)
    (e : E₀.below (A, k) ≃ E.below (A, k))
    (he : ∀ p, RespectsSemanticsBelow re₀ (A, k) p ↔
      RespectsSemanticsBelow re (A, k) (p ∘ e.symm))
    (comm : ∀ d, lowerIncl (Nat.le_succ k) (e (lo d)) = emb (CellScheme.below.mono hJ d))
    (lift : Lift rd re₀ lo) : Restore rd re emb := by
  intro p u hp hu M hM hread hbound hmax
  let u₀ := u ∘ lowerIncl (Nat.le_succ k) ∘ e
  have hu₀ : RespectsSemanticsBelow re₀ (A, k) u₀ := (he _).mpr (by
    simpa only [u₀, Function.comp_def, Equiv.apply_symm_apply, lowerIncl, CellScheme.below.mono] using
      hu.mono (show GradedLe (A, k) (A, k + 1) from ⟨Finset.Subset.refl _, Nat.le_succ k⟩))
  obtain ⟨v, hv, hval, hcap⟩ := lift (hp.mono hJ) hu₀ (hM.mono (Nat.le_succ k)) (fun d => by
    change min (u (lowerIncl _ (e (lo d)))) M = _
    rw [comm, hread, min_assoc, min_self])
  let v' := v ∘ e.symm
  have hag (d) : min (v' d) M = min (u (lowerIncl (Nat.le_succ k) d)) M := by
    simpa only [v', u₀, Function.comp_apply, Equiv.apply_symm_apply] using hcap (e.symm d)
  refine ⟨splice u v', splice_respects (Nat.le_succ k) hu ((he _).mp hv)
    (fun d _ => hbound d) hag, ?_, splice_cap (Nat.le_succ k) hag⟩
  intro d
  by_cases hd : D.grade d.1 ≤ k
  · have hl : E.grade (emb d).1 ≤ k := (hgrade d).le.trans hd
    let d₀ : D.below J₀ := ⟨d.1, cut d hd⟩
    have heq : e (lo d₀) = ⟨(emb d).1, (emb d).2.1, hl⟩ :=
      Subtype.ext (congrArg (fun x : E.below (A, k + 1) => x.1) (comm d₀))
    rw [splice_low _ _ _ hl, ← heq]
    simpa only [v', Function.comp_apply, Equiv.symm_apply_apply,
      show CellScheme.below.mono hJ d₀ = d from Subtype.ext rfl] using hval d₀
  · rw [splice_high _ _ _ (by simpa only [hgrade] using hd), hread, min_eq_left]
    apply hmax
    have : D.grade d.1 ≤ k + 1 := d.2.2.trans hj
    omega

abbrev Active (rd : Semantics D) (re : Semantics E) (emb : D.below J → E.below (A, j)) : Prop :=
  ∀ {p q}, RespectsSemanticsBelow rd J p → RespectsSemanticsBelow re (A, j) q →
    ∀ {γ}, SelfVis j γ → ⊥ < γ → (∃ d, D.grade d.1 = j ∧ γ < p d) →
    Agreement emb p q γ → Result re emb p q γ

theorem active_of_capped {emb : D.below J → E.below (A, j)}
    (complete : ∀ d : D.below J, D.grade d.1 = j → ∃ c : Cell D, D.cell c = J ∧ J.2 = j)
    (capped : PaddedOwnerRepair.Capped rd re emb) (restore : Restore rd re emb) :
    Active rd re emb := by
  intro p q hp hq γ hγ hpos hactive hag
  obtain ⟨d, hd, hpd⟩ := hactive
  obtain ⟨c₀, hc₀, hJ⟩ := complete d hd
  have hJ' : J = (J.1, j) := Prod.ext rfl hJ
  obtain ⟨c, hc, hmax⟩ := AmbientGradeCharts.exists_maximizer hp
    ⟨⟨c₀, hc₀ ▸ GradedLe.refl _⟩, hc₀.trans hJ'⟩
  have hg : D.grade c.1 = j := congrArg Prod.snd hc
  have hpc := hpd.trans_le (hmax d hd)
  obtain ⟨u, hu, hread, hcap, hbound⟩ := capped c (hc.trans hJ'.symm) hg hp hq hγ hpos hpc hag
  have hM : SelfVis j (p c) := hg ▸ (hp.orderly c).symm
  obtain ⟨r, hr, hval, hrM⟩ := restore hp hu hM hread hbound hmax
  exact ⟨r, hr, hval, by grind⟩

/-- Supply a chart only if a highest-grade value is active; otherwise the
lower lift fills the inactive tail. This also covers a missing highest grade. -/
theorem lift_of_capped {emb : D.below J → E.below (A, j)}
    (complete : ∀ d : D.below J, D.grade d.1 = j → ∃ c : Cell D, D.cell c = J ∧ J.2 = j)
    (bottom : (∃ d : D.below J, D.grade d.1 = j) → ∀ {p}, RespectsSemanticsBelow rd J p →
      ∃ r, RespectsSemanticsBelow re (A, j) r ∧ ∀ d, r (emb d) = p d)
    (capped : (∃ d : D.below J, D.grade d.1 = j) → PaddedOwnerRepair.Capped rd re emb)
    (restore : Restore rd re emb) : Lift rd re emb := by
  intro p q hp hq γ hγ hag
  by_cases ha : ∃ d, D.grade d.1 = j ∧ γ < p d
  · have howner : ∃ d : D.below J, D.grade d.1 = j := by
      tauto
    by_cases hz : γ = ⊥
    · obtain ⟨r, hr, hval⟩ := bottom howner hp
      exact ⟨r, hr, hval, by simp_all⟩
    · exact active_of_capped complete (capped howner) restore hp hq hγ
        (bot_lt_iff_ne_bot.mpr hz) ha hag
  · obtain ⟨r, hr, hread, hcap⟩ := restore hp (hq.cap hγ) hγ hag
      (fun _ => min_le_right _ _) (fun d hd => le_of_not_gt (fun lt => ha ⟨d, hd, lt⟩))
    grind

/-- The full owner is available if the source contains an occurrence of the
required grade. This works for nominal and arity-capped cutoffs alike. -/
theorem complete_full {n i j : ℕ} (S : SemScheme n) (hj : 0 < j) (hi : i ≤ j)
    (d : S.scheme.below (Finset.univ, i)) (hd : S.scheme.grade d.1 = j) :
    ∃ c, S.scheme.cell c = (Finset.univ, i) ∧ i = j := by
  have hle : j ≤ n := hd ▸ (S.scheme.grade_le_card_scope d.1).trans (by simpa using Finset.card_le_univ (S.scheme.scope d.1))
  have he : i = j := hi.antisymm (hd ▸ d.2.2)
  obtain ⟨c, hc⟩ := S.complete (Finset.univ, i) (AmalgamationPlan.Plan.mem_gradedPlan.mpr
    ⟨S.scheme.isPlan.domain_mem, by simpa [he] using hj, by simpa [he] using hle⟩)
  exact ⟨c, hc, he⟩

end VaughtConjecture.Knight.PaddedFaceLift
