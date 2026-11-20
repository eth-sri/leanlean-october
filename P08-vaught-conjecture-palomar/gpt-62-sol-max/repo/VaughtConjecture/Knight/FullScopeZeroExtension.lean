module

public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.Domain

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {K : ℕ}

namespace CellScheme

section Complete

variable {BJ : Finset ι × ℕ} {u : Cell D → ExtOrd} {p : D.below BJ → ExtOrd}

open Classical in
/-- Replace the labels on a lower set, keeping all other labels. -/
noncomputable def complete (u : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) (d : Cell D) : ExtOrd :=
  if h : GradedLe (D.cell d) BJ then p ⟨d, h⟩ else u d

theorem complete_present (u : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) (d : D.below BJ) :
    complete u p d.1 = p d := by
  rcases d with ⟨d, hd⟩
  rw [complete, dif_pos hd]

theorem complete_outside (u : Cell D → ExtOrd) (p : D.below BJ → ExtOrd)
    (d : Cell D) (h : ¬ GradedLe (D.cell d) BJ) : complete u p d = u d := by rw [complete, dif_neg h]

theorem complete_future (u : Cell D → ExtOrd) (p : D.below BJ → ExtOrd) (d : Cell D)
    (h : BJ.2 < D.grade d) : complete u p d = u d :=
  complete_outside u p d (fun hd => h.not_ge hd.2)

theorem complete_cases {P : Cell D → ExtOrd → Prop}
    (hp : ∀ d : D.below BJ, P d.1 (p d))
    (hu : ∀ d, ¬ GradedLe (D.cell d) BJ → P d (u d)) (d : Cell D) : P d (complete u p d) := by
  by_cases h : GradedLe (D.cell d) BJ
  · rw [complete, dif_pos h]
    exact hp ⟨d, h⟩
  · rw [complete, dif_neg h]
    exact hu d h

theorem complete_lawful (u : Cell D → ExtOrd) {sem : Semantics D}
    (hp : RespectsSemanticsBelow sem BJ p) :
    RespectsSemanticsBelow sem BJ (fun d => complete u p d.1) := by
  simpa only [complete_present] using hp

theorem complete_visible (u : Cell D → ExtOrd) {sem : Semantics D}
    (hu : ∀ d, SelfVis 1 (u d)) (hp : RespectsSemanticsBelow sem BJ p) (d : Cell D) :
    SelfVis 1 (complete u p d) :=
  complete_cases (P := fun _ x => SelfVis 1 x)
    (fun d => (show SelfVis (D.grade d.1) (p d) from (hp.orderly d).symm).mono
      (D.grade_pos d.1)) (fun d _ => hu d) d

theorem complete_cap (u : Cell D → ExtOrd) {γ : ExtOrd}
    (h : ∀ d, min (p d) γ = min (u d.1) γ) (d : Cell D) :
    min (complete u p d) γ = min (u d) γ :=
  complete_cases (P := fun a x => min x γ = min (u a) γ) h (fun _ _ => rfl) d

end Complete

/-- A lower labelling at full scope, with bottom at every higher-grade cell. -/
noncomputable abbrev zeroAbove (q : D.below (A, K) → ExtOrd) := complete (fun _ => ⊥) q

theorem zeroAbove_low (q : D.below (A, K) → ExtOrd) (d : D.below (A, K)) :
    zeroAbove q d.1 = q d := complete_present _ q d

theorem zeroAbove_high (q : D.below (A, K) → ExtOrd) {d : Cell D} (hd : ¬ D.grade d ≤ K) :
    zeroAbove q d = ⊥ := complete_outside _ q d (fun h => hd h.2)

theorem zeroAbove_apply (q : Cell D → ExtOrd) (d : Cell D) :
    zeroAbove (K := K) (fun x => q x.1) d = if D.grade d ≤ K then q d else ⊥ := by
  by_cases h : D.grade d ≤ K
  · rw [if_pos h]
    exact zeroAbove_low _ ⟨d, D.scope_subset d, h⟩
  · rw [zeroAbove_high _ h, if_neg h]

end CellScheme

/-- Extending a respecting full-scope lower labelling by bottom preserves respect. -/
theorem RespectsSemanticsBelow.zeroAbove {sem : Semantics D} {q : D.below (A, K) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (A, K) q) :
    RespectsSemantics sem (CellScheme.zeroAbove q) := by
  have mem (d : Cell D) (hd : D.grade d ≤ K) : GradedLe (D.cell d) (A, K) :=
    ⟨D.scope_subset d, hd⟩
  refine ⟨?_, ?_, ?_⟩
  · intro d
    by_cases hd : D.grade d ≤ K
    · rw [CellScheme.zeroAbove_low q ⟨d, mem d hd⟩]
      apply hq.orderly
    · rw [CellScheme.zeroAbove_high q hd]
      rfl
  · intro Sig
    by_cases hSig : D.grade Sig ≤ K
    · refine transformsTo_congr rfl rfl ?_ (hq.locality ⟨Sig, mem Sig hSig⟩)
      funext d
      rw [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩,
        CellScheme.zeroAbove_low q ⟨d.1, mem d.1 (d.2.2.trans hSig)⟩]
      rfl
    · refine transformsTo_congr rfl rfl ?_ (TransformsTo.to_bot _)
      funext d
      rw [CellScheme.zeroAbove_high q hSig, min_eq_right bot_le]
  · intro Sig Xi₀ hs hg
    by_cases hSig : D.grade Sig ≤ K
    · have hXi₀ : D.grade Xi₀ ≤ K := hg ▸ hSig
      obtain ⟨Xi, hc, hle⟩ :=
        hq.availability ⟨Sig, mem Sig hSig⟩ ⟨Xi₀, mem Xi₀ hXi₀⟩ hs hg
      refine ⟨Xi.1, hc, ?_⟩
      rwa [CellScheme.zeroAbove_low q ⟨Sig, mem Sig hSig⟩, CellScheme.zeroAbove_low q Xi]
    · exact ⟨Xi₀, rfl, by rw [CellScheme.zeroAbove_high q hSig]; exact bot_le⟩

end VaughtConjecture.Knight
