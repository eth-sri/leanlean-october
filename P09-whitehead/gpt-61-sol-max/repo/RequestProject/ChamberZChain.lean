import Mathlib.Tactic

import RequestProject.ChamberZPoset
import RequestProject.NerveRelativeGluing
import RequestProject.DavisChainAcyclic

/-!
# Chains of the complex `Z` of modified chambers: only the copies of the base survive

This file applies the already-proved results to the actual object built in
`RequestProject/ChamberZPoset.lean`:

* the ordinary chambers of `Z` are acyclic — they are still cones on their apex
  (`FiniteChains.Davis.acyclicIn_zchamber_unmarked`);
* a modified chamber retracts, below the identity, onto its copy of the base poset, hence is
  acyclic **relative** to the union of those copies
  (`FiniteChains.Davis.acyclicRelIn_zchamber_marked`);
* the attaching intersection of a chamber of `Z` is `J_w`, which is acyclic by the mirror
  contraction (`FiniteChains.Davis.acyclicIn_zJSet`);
* gluing these along the filtration by word length
  (`FiniteChains.Nerve.acyclicRelIn_union_of_unmixed`) gives the main result

  `FiniteChains.Davis.exists_base_cycle_of_cycle`: **every increasing cycle of `Z`, in every
  degree, is the sum of an increasing cycle supported on the adjoined copies of the base and
  the boundary of an increasing chain of `Z`.**

In particular ordinary chambers contribute nothing and each modified chamber contributes exactly
the cycles of its copy of the base: this is the chain-level form, for the actual object `Z`, of
"the modified chambers contribute the cycles of their copies of the base".  It is a statement
about `Z` itself; transporting it to the universal cover with group-ring coefficients is a
separate obligation.
-/

namespace FiniteChains.Davis


open RACG Mirror Comb Nerve


variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-- **The base subcomplex of `Z`**: the union of the adjoined copies of the base poset. -/
def InZBase : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-! ### Ordinary chambers -/

omit [Fintype V] in
theorem not_isMarkedApex_apex {w : CayGroup A} (hw : ¬ M w) :
    ¬ IsMarkedApex M (chamberPt w (isSimplex_empty (A := A))) := by
  rintro ⟨-, h⟩
  rw [chamberPt_empty_rep] at h
  exact hw h

/-- The apex of an unmarked chamber, as a cell of `Z`. -/
noncomputable def zApex {w : CayGroup A} (hw : ¬ M w) : Zpos A X M att :=
  zOld (chamberPt w (isSimplex_empty (A := A))) (not_isMarkedApex_apex hw)

section
omit [Fintype V]
theorem inZChamber_zApex {w : CayGroup A} (hw : ¬ M w) :
    InZChamber w (zApex (X := X) (att := att) hw) :=
  chamberPt_inChamber w (isSimplex_empty (A := A))

/-- The apex is the least cell of an unmarked chamber. -/
theorem zApex_le {w : CayGroup A} (hw : ¬ M w) {z : Zpos A X M att} (hz : InZChamber w z) :
    zApex (X := X) (att := att) hw ≤ z := by
  cases z with
  | inl p =>
      solve_by_elim [FiniteChains.Davis.le_of_inChamber, FiniteChains.Davis.chamberPt_inChamber, FiniteChains.Davis.isSimplex_empty, Finset.empty_subset]
  | inr wx =>
      exact absurd (hz ▸ wx.1.2) hw
end

/-! ### Modified chambers -/

/-! ### The attaching intersection -/

/-- The attaching subcomplex of the chamber of `w` inside `Z` is the attaching subcomplex of the
chamber `F_w` of the Davis poset. -/
noncomputable def zJSetOrderIso (w : CayGroup A) :
    {z : Zpos A X M att // ZJSet w z} ≃o ChamberInter A w where
  toFun z :=
    match z with
    | ⟨Sum.inl p, h⟩ => ⟨p.1, (jSet_iff.1 h).1, (jSet_iff.1 h).2⟩
    | ⟨Sum.inr _, h⟩ => h.elim
  invFun q :=
    ⟨zOld q.1 (by
        rintro ⟨hemp, -⟩
        obtain ⟨s, hs⟩ := q.2.2
        rw [hemp] at hs
        simp at hs),
      show JSet w q.1 from jSet_iff.2 ⟨q.2.1, q.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨p | wx, h⟩
    · rfl
    · exact h.elim
  right_inv q := rfl
  map_rel_iff' {z z'} := by
    rcases z with ⟨p | wx, h⟩
    · rcases z' with ⟨q | wy, h'⟩
      · exact Iff.rfl
      · exact h'.elim
    · exact h.elim

/-! ### The filtration by word length -/

/-- The union of the chambers of `Z` of length at most `n`. -/
def ZUpto (n : ℕ) (z : Zpos A X M att)  := ∃ y : CayGroup A, RACG.clen A y ≤ n ∧ InZChamber y z

section
omit [Fintype V]
theorem zUpto_up {n : ℕ} {z z' : Zpos A X M att} (h : z ≤ z') (hz : ZUpto n z) : ZUpto n z' := by
  grind [FiniteChains.Davis.ZUpto, inZChamber_of_le]

theorem zUpto_zero_iff (z : Zpos A X M att) : ZUpto 0 z ↔ InZChamber (1 : CayGroup A) z := by
  constructor
  · rintro ⟨y, hy, hyz⟩
    have  := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 hy)
    rwa [this] at hyz
  · intro h
    exact ⟨1, by simp, h⟩
end

/-! ### The whole complex -/

/-- The length of the chamber a cell of `Z` belongs to. -/
noncomputable def zlen : Zpos A X M att → ℕ
  | Sum.inl p => RACG.clen A p.1.rep
  | Sum.inr wx => RACG.clen A wx.1.1

omit [Fintype V] in
theorem zUpto_zlen (z : Zpos A X M att) : ZUpto (zlen z) z := by
  cases z with
  | inl p => exact ⟨p.1.rep, le_refl _, inChamber_rep p.1⟩
  | inr wx => exact ⟨wx.1.1, le_refl _, rfl⟩

end FiniteChains.Davis

