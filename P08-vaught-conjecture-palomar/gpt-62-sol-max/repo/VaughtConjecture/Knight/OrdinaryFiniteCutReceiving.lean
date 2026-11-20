/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.OrdinaryReceivingProbe
public import VaughtConjecture.Knight.CappedDonorComparisonRequest
public import VaughtConjecture.Knight.TopSupportReceiving
public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.Reduction
public import VaughtConjecture.Knight.ActualOccurrence
public import VaughtConjecture.Knight.CapObservation

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryModelReceiving

open TypeTower StageType KnightRealization Value ExtOrd CappedDonor OrdinaryReceivingProbe

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- Realize the probe over the private context, then restrict its donor to the requested cut. -/
theorem fc_of_reference (hM : R.IsModel) {n : ℕ} {t : Fin n ↪ M} {p : S α.1 n}
    (hp : R.eval t = some p) (q : S α.1 (n + 1))
    {I : Type*} [Fintype I] {N : ℕ} (hN : 4 ≤ N)
    {u : Fin N ↪ M} {p₀ : S α.1 N} (hu : R.eval u = some p₀)
    (e : Fin n ↪ Fin N) (hut : e.trans u = t)
    (Rf : Ref I n N N q.scheme p₀.scheme) (hRp : Rf.p = q.label) (hRv : Rf.vact = p₀.label)
    (T : WholeDonorAttachment.SharedFace p₀.scheme q.scheme p.scheme e) (hface : Aligned T Rf)
    {δ : ExtOrd} (hδ : δ ≤ Rf.cut Rf.vactL) :
    ∃ (y : M) (hy : y ∉ Set.range t) (q' : S α.1 (n + 1)), R.eval (snoc t y hy) = some q' ∧
      ∃ h : q'.scheme = q.scheme,
        ∀ d, min (q'.label d) δ = min (q.label (SemScheme.castCell h d)) δ := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 4 := ⟨N - 4, by omega⟩
  subst hut
  let W := T.boundary
  have hW := WholeDonorAttachment.union e
  let D := OrdinaryReceivingAssembly.semScheme W Rf hW hface
  have RC := private_receipt W Rf hW hface
  have RD := request_receipt W Rf hW hface
  obtain ⟨a, r, hr, -, hrv, hg, -⟩ := exists_raw_display W Rf hW hface
  -- the model's prescribed-bottom-pattern clause over the private tuple
  obtain ⟨y, hy, q₁, ⟨h₁, hpat⟩, hcof, hev⟩ := hM.bottomPattern u p₀ hu D RC.extendsDomain r hr
    (fun d => (congrArg r (RC.occurrence d)).trans ((hrv d).trans (congrFun hRv d)))
  -- the realized section on the probe
  let qq : Cell D.scheme → ExtOrd := fun c => q₁.label (SemScheme.castCell h₁.symm c)
  have hqq : RespectsSemantics D.rows qq := respects_castCell h₁ q₁.respects
  let t' : S α.1 (k + 5) := ⟨D, qq, fun c => q₁.label_bound _, hqq⟩
  have ht' : q₁ = t' := StageType.eq_of_label h₁ (fun i => rfl)
  rw [ht'] at hcof hev
  -- literal private retention
  have hretain : ∀ d, qq ((privateFace W Rf hW hface).map d) = Rf.vact d := by
    rw [hRv]
    exact (RC.labels_iff (q := t') p₀ rfl).1 hcof
  have hgate : qq (gate W Rf hW hface a) ≠ ⊥ := by
    intro hb
    have := (hpat ⟨_, Finset.subset_univ _, (gate_grade W Rf hW hface a).le⟩).mp hb
    rw [hg] at this
    exact top_ne_bot this
  have hread := readback_below W Rf hW hface hqq hretain a hgate hδ
  obtain ⟨hy', -, heval⟩ := restrict_actual_extension hM.consistent e rfl hy hev
    (typeMap_eq_some (onePointProj e) t' RD.visible)
  refine ⟨y, hy', _, heval, RD.restrict_eq, fun d => ?_⟩
  have key := hread (SemScheme.castCell RD.restrict_eq d)
  exact (congrArg (fun a => min (qq a) δ) (RD.toCell_eq d)).trans
    (key.trans (congrArg (fun f => min (f (SemScheme.castCell RD.restrict_eq d)) δ) hRp))

/-- **Every model satisfies finite-cut receiving**: reference acquisition above the requested
cutoff and above the threshold floor `3`, then `fc_of_reference`. -/
theorem finiteCutReceiving (hM : R.IsModel) : FiniteCutReceiving R := by
  intro n t p hp P hP δ hδbot hδα
  obtain ⟨ν, rfl, hν⟩ : ∃ ν : Ordinal.{0}, δ = ofOrd ν ∧ ν < α.1 := by
    rcases ExtOrd.cases δ with rfl | rfl | ⟨ν, rfl⟩
    all_goals simp_all
  obtain ⟨C, T, Rf, hRp, hRv, hface, hNmin, hlt⟩ :=
    exists_ref_above_cut_min hM p hp P hP ν hν 3
  exact fc_of_reference hM hp P (by omega) C.eval_ctx C.proj C.proj_ctx Rf hRp hRv T hface hlt.le

end VaughtConjecture.Knight.OrdinaryModelReceiving
