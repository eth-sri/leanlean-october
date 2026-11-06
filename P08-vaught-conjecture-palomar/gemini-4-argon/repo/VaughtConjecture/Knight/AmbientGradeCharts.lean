/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.FreeDiagonal

/-! # Arbitrary ambients represented grade by grade

Availability promotes each label to a full-scope controller at the same grade.
Taking a maximum among those finitely many controllers yields one controller
dominating the entire grade. Normalizing its actual locality witness then reads
that grade exactly, and all lower grades capped at its own label. This strengthens
the per-cell availability observation in `Knight/Producer.lean` to an exact
grade-by-grade representation on arbitrary lower domains, without assuming a
bountiful scheme or that the ambient is one of its semantic rows.

At an external cap, a grade is frozen if its maximum lies strictly below the
cap. Otherwise any replacement maximum must be a controller whose *old* label
already reaches the cap. The eligible set is preserved exactly. These facts do
not assume a designated controller stays maximal, nor that one controller
dominates labels at other grades.

The charts are extracted from respect, not a converse characterization of it.
Recombining or changing charts still requires every controller locality and
availability. In particular their shifters are not asserted bottom-reflecting,
and no unrestricted composition of faithful transformations is used.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AmbientGradeCharts

open Transform Value ExtOrd VaughtConjecture.AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

/-- A normalized witness at a controller dominating its own grade. -/
structure Chart (sem : Semantics D) (BJ : Finset ι × ℕ) (q : D.below BJ → ExtOrd)
    (k : ℕ) where
  owner : D.below BJ
  index : D.cell owner.1 = (BJ.1, k)
  dominates : ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q owner
  shift : ExtOrd → ExtOrd
  witness : Witness (gTop k) shift
  read : ∀ d : D.below (D.cell owner.1),
    shift (sem.E owner.1 d) = min (q (CellScheme.below.incl owner d)) (q owner)

namespace Chart

variable {k : ℕ} (C : Chart sem BJ q k)

theorem grade : D.grade C.owner.1 = k := congrArg Prod.snd C.index

/-- Every occurrence of grade at most `k` lies below this full-scope owner. -/
def occurrence (d : D.below BJ) (hd : D.grade d.1 ≤ k) : D.below (D.cell C.owner.1) :=
  ⟨d.1, by rw [C.index]; exact ⟨d.2.1, hd⟩⟩

theorem read_capped (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd)) = min (q d) (q C.owner) :=
  C.read (C.occurrence d hd)

/-- Exact readback on the owner's grade, including all its sibling controllers. -/
theorem read_grade (d : D.below BJ) (hd : D.grade d.1 = k) :
    C.shift (sem.E C.owner.1 (C.occurrence d hd.le)) = q d := by
  rw [C.read_capped, min_eq_left (C.dominates d hd)]

/-- If this grade's maximum reaches the external cap, its one witness recovers
the externally capped labels at every lower grade as well. -/
theorem read_under_cap {γ : ExtOrd} (hactive : γ ≤ q C.owner)
    (d : D.below BJ) (hd : D.grade d.1 ≤ k) :
    min (C.shift (sem.E C.owner.1 (C.occurrence d hd))) γ = min (q d) γ := by
  rw [C.read_capped, min_assoc, min_eq_right hactive]

end Chart

/-- One full-scope controller suffices to make the maximizing set nonempty.
Availability, not a cross-grade domination assumption, supplies the final bound. -/
theorem exists_maximizer (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k) ∧
      ∀ d : D.below BJ, D.grade d.1 = k → q d ≤ q c := by
  classical
  let _ := Fintype.ofFinite (D.below BJ)
  let s := Finset.univ.filter (fun c : D.below BJ => D.cell c.1 = (BJ.1, k))
  have hs : s.Nonempty := by
    obtain ⟨c, hc⟩ := hfull
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image s q hs
  have hci : D.cell c.1 = (BJ.1, k) := (Finset.mem_filter.mp hc).2
  refine ⟨c, hci, ?_⟩
  intro d hd
  have hscope : D.scope d.1 ⊆ D.scope c.1 := by
    change D.scope d.1 ⊆ (D.cell c.1).1
    rw [hci]
    exact d.2.1
  have hgrade : D.grade d.1 = D.grade c.1 := hd.trans (congrArg Prod.snd hci).symm
  obtain ⟨e, he, hde⟩ := hq.availability d c hscope hgrade
  exact hde.trans (hmax e (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.trans hci⟩))

/-- Extract an actual bounded faithful witness; bottom and literal top need no exclusion. -/
theorem exists_chart (hq : RespectsSemanticsBelow sem BJ q) {k : ℕ}
    (hfull : ∃ c : D.below BJ, D.cell c.1 = (BJ.1, k)) :
    Nonempty (Chart sem BJ q k) := by
  obtain ⟨c, hc, hmax⟩ := exists_maximizer hq hfull
  let self : D.below (D.cell c.1) := ⟨c.1, GradedLe.refl _⟩
  let p : D.below (D.cell c.1) → ExtOrd := fun d => q (CellScheme.below.incl c d)
  have hm : ∀ d : D.below (D.cell c.1), D.grade d.1 ≤ D.grade self.1 := fun d => d.2.2
  have hv : SelfVis (D.grade self.1) (p self) := (hq.orderly c).symm
  obtain ⟨τ, hτ, _, hr⟩ := exists_bounded_exact_capped_witness hm hv (hq.locality c)
  have hg : D.grade self.1 = k := congrArg Prod.snd hc
  exact ⟨⟨c, hc, hmax, τ, hg ▸ hτ, hr⟩⟩

/-! ## Exact cap-preservation obligations -/

/-- The literal part of a cap equation; this statement also applies at cap top. -/
theorem eq_of_cap_below {a b γ : ExtOrd} (h : min a γ = min b γ) (hb : b < γ) : a = b := by
  rw [min_eq_left hb.le] at h
  have ha : a < γ := (min_lt_iff.mp (h.trans_lt hb)).resolve_right (lt_irrefl γ)
  rwa [min_eq_left ha.le] at h

theorem cap_reaches_iff {a b γ : ExtOrd} (h : min a γ = min b γ) : γ ≤ a ↔ γ ≤ b := by
  constructor
  · intro ha
    apply min_eq_right_iff.mp
    exact h.symm.trans (min_eq_right ha)
  · intro hb
    apply min_eq_right_iff.mp
    exact h.trans (min_eq_right hb)

/-- Source-side cap agreement transfers through a monotone shifter once the
image of the source cap reaches the output cap. Bottom reflection is unnecessary
for this equation; no preservation of respect is asserted. -/
theorem map_cap_agreement {τ : ExtOrd → ExtOrd} (hτ : Monotone τ)
    {a b δ γ : ExtOrd} (hab : min a δ = min b δ) (hγ : γ ≤ τ δ) :
    min (τ a) γ = min (τ b) γ := by
  calc
    min (τ a) γ = min (τ (min a δ)) γ := by
      rw [hτ.map_min, min_assoc, min_eq_right hγ]
    _ = min (τ (min b δ)) γ := by rw [hab]
    _ = min (τ b) γ := by rw [hτ.map_min, min_assoc, min_eq_right hγ]

open GradeTailRestoration in
theorem restore_of_lower {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    {A : Finset ιA} {B : Finset ιB} {T : CellScheme A} {rows : Semantics T}
    {T₀ : CellScheme A} {rows₀ : Semantics T₀}
    {D : CellScheme B} {sem : Semantics D} {idx₀ idx₁ : Finset ιB × ℕ} {k : ℕ}
    (hidx : GradedLe idx₀ idx₁)
    {faceAt₀ : D.below idx₀ → T₀.below (A, k)}
    {faceAt₁ : D.below idx₁ → T.below (A, k + 1)}
    (hgrade : ∀ d, T.grade (faceAt₁ d).1 = D.grade d.1)
    (hd_le : ∀ d : D.below idx₁, D.grade d.1 ≤ k + 1)
    (e : T₀.below (A, k) ≃ T.below (A, k))
    (he_iff : ∀ p : T₀.below (A, k) → ExtOrd,
      RespectsSemanticsBelow rows₀ (A, k) p ↔ RespectsSemanticsBelow rows (A, k) (p ∘ e.symm))
    (down : ∀ d : D.below idx₁, D.grade d.1 ≤ k → D.below idx₀)
    {p : D.below idx₁ → ExtOrd} {u : T.below (A, k + 1) → ExtOrd} {M : ExtOrd}
    (hp : RespectsSemanticsBelow sem idx₁ p)
    (hu : RespectsSemanticsBelow rows (A, k + 1) u)
    (hM : SelfVis (k + 1) M)
    (hprev : ∀ {p₀ : D.below idx₀ → ExtOrd} {q₀ : T₀.below (A, k) → ExtOrd},
      RespectsSemanticsBelow sem idx₀ p₀ → RespectsSemanticsBelow rows₀ (A, k) q₀ →
      SelfVis k M → (∀ d, min (q₀ (faceAt₀ d)) M = min (p₀ d) M) →
      ∃ v, RespectsSemanticsBelow rows₀ (A, k) v ∧ (∀ d, v (faceAt₀ d) = p₀ d) ∧
        ∀ d, min (v d) M = min (q₀ d) M)
    (hread : ∀ d, u (faceAt₁ d) = min (p d) M)
    (hbound : ∀ d, u d ≤ M)
    (hmax : ∀ d, D.grade d.1 = k + 1 → p d ≤ M)
    (hid : ∀ d : D.below idx₀,
      lowerIncl (Nat.le_succ k) (e (faceAt₀ d)) =
        faceAt₁ (CellScheme.below.mono hidx d) := by intro; rfl)
    (hdown_val : ∀ d hd, (down d hd).1 = d.1 := by intros; rfl)
    (hdown_face : ∀ d hd,
      (⟨(faceAt₁ d).1, (faceAt₁ d).2.1, (hgrade d).le.trans hd⟩ : T.below (A, k)) =
        e (faceAt₀ (down d hd)) := by intros; rfl) :
    ∃ r, RespectsSemanticsBelow rows (A, k + 1) r ∧
      (∀ d, r (faceAt₁ d) = p d) ∧
      ∀ d, min (r d) M = min (u d) M := by
  let u₁ := fun d => u (lowerIncl (Nat.le_succ k) (e d))
  have hu₁ : RespectsSemanticsBelow rows₀ (A, k) u₁ := by
    apply (he_iff u₁).mpr
    have h := hu.mono (show GradedLe (A, k) (A, k + 1) from ⟨Finset.Subset.refl _, Nat.le_succ k⟩)
    simpa only [u₁, Function.comp_def, Equiv.apply_symm_apply, lowerIncl, CellScheme.below.mono] using h
  obtain ⟨v, hv, hvread, hvcap⟩ := hprev (hp.mono hidx) hu₁ (hM.mono (Nat.le_succ k)) fun d => by
    change min (u (lowerIncl _ (e _))) M = min (p (CellScheme.below.mono hidx d)) M
    rw [hid, hread, min_assoc, min_self]
  let v₁ := v ∘ e.symm
  have hag (d) : min (v₁ d) M = min (u (lowerIncl (Nat.le_succ k) d)) M := by
    simpa only [u₁, v₁, Function.comp_apply, Equiv.apply_symm_apply] using hvcap (e.symm d)
  refine ⟨splice u v₁, splice_respects (Nat.le_succ k) hu ((he_iff v).mp hv)
    (fun d _ => hbound d) hag, ?_, splice_cap (Nat.le_succ k) hag⟩
  intro d
  by_cases hd : D.grade d.1 ≤ k
  · have hd' : T.grade (faceAt₁ d).1 ≤ k := (hgrade d).le.trans hd
    rw [splice_low u v₁ _ hd']
    change v (e.symm _) = p d
    rw [hdown_face d hd, Equiv.symm_apply_apply]
    exact (hvread (down d hd)).trans (congrArg p (Subtype.ext (hdown_val d hd)))
  · rw [splice_high u v₁ _ (by simpa only [hgrade] using hd), hread]
    have := hd_le d
    exact min_eq_left (hmax d (by omega))

theorem active_lift_of_restore {ιA ιB : Type*} [DecidableEq ιA] [DecidableEq ιB]
    {A : Finset ιA} {B : Finset ιB} {T : CellScheme A} {rows : Semantics T}
    {D : CellScheme B} {sem : Semantics D} {idx : Finset ιB × ℕ} {g : ℕ}
    {faceAt : D.below idx → T.below (A, g)}
    {p : D.below idx → ExtOrd} {q : T.below (A, g) → ExtOrd}
    (hp : RespectsSemanticsBelow sem idx p)
    (hq : RespectsSemanticsBelow rows (A, g) q)
    {γ : ExtOrd} (hγ : SelfVis g γ) (hpos : ⊥ < γ)
    {d₀ : D.below idx} (hd₀ : D.grade d₀.1 = g) (hpd₀ : γ < p d₀)
    (c₀ : Cell D) (hc₀ : D.cell c₀ = idx) (hgc₀ : idx.2 = g)
    (hcapped : ∀ c : D.below idx, D.cell c.1 = idx → D.grade c.1 = g → γ < p c →
      ∃ u, RespectsSemanticsBelow rows (A, g) u ∧
        (∀ d, u (faceAt d) = min (p d) (p c)) ∧
        (∀ d, min (u d) γ = min (q d) γ) ∧ (∀ d, u d ≤ p c))
    (hrestore : ∀ {u : T.below (A, g) → ExtOrd} {M : ExtOrd},
      RespectsSemanticsBelow rows (A, g) u → SelfVis g M →
      (∀ d, u (faceAt d) = min (p d) M) → (∀ d, u d ≤ M) →
      (∀ d, D.grade d.1 = g → p d ≤ M) →
      ∃ r, RespectsSemanticsBelow rows (A, g) r ∧
        (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) M = min (u d) M) :
    ∃ r, RespectsSemanticsBelow rows (A, g) r ∧
      (∀ d, r (faceAt d) = p d) ∧ ∀ d, min (r d) γ = min (q d) γ := by
  obtain ⟨c, hc, hmax⟩ := exists_maximizer hp
    ⟨⟨c₀, by rw [hc₀]; exact GradedLe.refl _⟩, hc₀⟩
  have hg : D.grade c.1 = g := (congrArg Prod.snd hc).trans hgc₀
  have hpc : γ < p c := hpd₀.trans_le (hmax d₀ (hd₀.trans hgc₀.symm))
  obtain ⟨u, hu, hread, hcap, hbound⟩ := hcapped c hc hg hpc
  have hM : SelfVis g (p c) := by simpa only [hg] using (hp.orderly c).symm
  obtain ⟨r, hr, hrr, hrc⟩ := hrestore hu hM hread hbound
    (fun e he => hmax e (he.trans hgc₀.symm))
  exact ⟨r, hr, hrr, fun e => (GradeTailRestoration.cap_below (hrc e) hpc.le).trans (hcap e)⟩
