import Mathlib.Tactic

import RequestProject.ChamberZChain
import RequestProject.ChamberZPi1
import RequestProject.OrderComplexPi1Transfer
import RequestProject.CombCoveringLift

/-!
# A copy of the base is injective in `π₁(Z)` — with no extension over the cone

`RequestProject/ChamberZPi1.lean` splits a copy of the base off `π₁(Z)` under the extra
hypothesis that the attaching map extends monotonically over the cone point of a chamber.  That
hypothesis is dropped here.

The argument is the van Kampen retraction on path classes of
`RequestProject/OrderComplexRetraction.lean`, applied to the chamber filtration of the actual
complex `Z` of `RequestProject/ChamberZPoset.lean`:

* the attaching intersection of a chamber of `Z` is `J_w`, which is nonempty, connected and
  simply connected (`FiniteChains.Davis.connectedIn_zJSet`,
  `FiniteChains.Davis.simplyConnectedIn_zJSet`);
* chains of `Z` are unmixed because chambers are upward closed, and the intersection of a
  chamber with the earlier ones is exactly `J_w` (`mem_earlier_zchamber_iff`);
* the modified chamber retracts monotonically onto its copy of the base, which gives the
  initial step (`FiniteChains.Davis.injIn_zchamber_base`); no extension over the cone is used,
  because the retraction is only used inside one chamber;
* the filtration by word length is exhausted step by step
  (`FiniteChains.Davis.injIn_zupto`), and a null-homotopy, being a finite derivation, lies in
  some initial union (`FiniteChains.Davis.injIn_zpos`).

The conclusion is `FiniteChains.Davis.pi1Map_zNew_injective_uncond`: for every marked chamber
`w` the inclusion of the copy of the base induces an **injective** map
`π₁(X) → π₁(Z)`; the hypotheses contain neither an extension over the cone nor the desired
injectivity itself.
-/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis


open RACG Mirror Comb


variable {V : Type u} [DecidableEq V] [Fintype V] {A : CommRel V} {X : Type u} [Preorder X]
  {M : CayGroup A → Prop} {att : NeSpx A →o X}

/-! ### The copy of the base attached at a marked chamber -/

/-- The copy of the base poset glued into the modified chamber of `w`. -/
def InZBaseAt (w : CayGroup A) : Zpos A X M att → Prop
  | Sum.inl _ => False
  | Sum.inr wx => wx.1.1 = w

section
omit [Fintype V]
theorem inZBaseAt_imp_inZChamber {w : CayGroup A} {z : Zpos A X M att}
    (h : InZBaseAt w z) : InZChamber w z := by
  cases z with
  | inl p => exact h.elim
  | inr wx => exact h

@[simp] theorem inZBaseAt_zNew (w : {w : CayGroup A // M w}) (x : X) :
    InZBaseAt (att := att) w.1 (zNew w x) := rfl
end

/-- The retraction of the copy of the base onto the base poset itself. -/
def zBaseRetr (w : CayGroup A) : {z : Zpos A X M att // InZBaseAt w z} → X
  | ⟨Sum.inl _, h⟩ => h.elim
  | ⟨Sum.inr wx, _⟩ => wx.2

section
omit [Fintype V]
@[simp] theorem zBaseRetr_zNew (w : {w : CayGroup A // M w}) (x : X) :
    zBaseRetr (att := att) w.1 ⟨zNew w x, inZBaseAt_zNew w x⟩ = x := rfl

theorem zBaseRetr_monotone (w : CayGroup A) :
    Monotone (zBaseRetr (A := A) (X := X) (M := M) (att := att) w) := by
  rintro ⟨p | ⟨u, x⟩, hz⟩ ⟨q | ⟨v, y⟩, hz'⟩ h
  · exact hz.elim
  · exact hz.elim
  · exact hz'.elim
  · exact h.2
end

/-! ### The attaching intersection of a chamber of `Z` -/

variable {w : CayGroup A}
  (hw : w ≠ 1)
include hw in
/-- `J_w` inside `Z` is connected. -/
theorem connectedIn_zJSet   :
    ConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  connectedIn_of_isConnected
    (isConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_isConnected hw))

include hw in
/-- `J_w` inside `Z` is simply connected. -/
theorem simplyConnectedIn_zJSet   :
    SimplyConnectedIn (ZJSet (A := A) (X := X) (M := M) (att := att) w) :=
  simplyConnectedIn_of_simplyConnected
    (simplyConnected_orderCx_of_orderIso (zJSetOrderIso (X := X) (att := att) w)
      (chamberInter_simplyConnected hw))

include hw in
/-- `J_w` inside `Z` is nonempty. -/
theorem exists_zJSet   :
    ∃ z : Zpos A X M att, ZJSet w z :=
  ⟨((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).1,
    ((zJSetOrderIso (X := X) (att := att) w).symm (interTop hw)).2⟩

/-! ### The initial step: the modified chamber retracts onto its copy of the base -/

section
omit [Fintype V]
/-- **Inside a modified chamber, the copy of the base is injective on path classes.**  This is
the monotone retraction of the mapping cylinder; it involves no extension of the attaching map
over the cone point. -/
theorem injIn_zchamber_base {w : CayGroup A} (hw : M w) :
    InjIn (InZChamber (A := A) (X := X) (M := M) (att := att) w) (InZBaseAt w) := by
  refine injIn_of_monotone_retraction (fun z hz => inZBaseAt_imp_inZChamber hz)
    (fun z => (zChamberRetr hw z).1)
    (fun z z' h => zChamberRetr_monotone hw h) ?_ ?_
  · intro z
    obtain ⟨x, hx⟩ := zChamberRetr_mem hw z
    show InZBaseAt w (zChamberRetr hw z).1
    rw [hx]
    exact rfl
  · rintro ⟨p | ⟨u, x⟩, hz⟩ hb
    · exact hb.elim
    · rfl

/-! ### The filtration by word length -/

theorem inZBaseAt_imp_zUpto {w : CayGroup A} {n : ℕ} (hn : RACG.clen A w ≤ n)
    {z : Zpos A X M att} (h : InZBaseAt w z) : ZUpto n z :=
  ⟨w, hn, inZBaseAt_imp_inZChamber h⟩
end

variable {w0 : CayGroup A}
  (hw0 : M w0)
include hw0 in
/-- **One chamber of the filtration is added.** -/
theorem injIn_zupto_insert   (n : ℕ)
    (hprev : RACG.clen A w0 ≤ n → InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n)
      (InZBaseAt w0)) :
    ∀ S : Set (CayGroup A), S.Finite → (∀ y ∈ S, RACG.clen A y = n + 1) →
      (RACG.clen A w0 ≤ n ∨ w0 ∈ S) →
      InjIn (fun z : Zpos A X M att => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z) (InZBaseAt w0) := by
  intro S hS
  induction S, hS using Set.Finite.induction_on with
  | empty =>
      simp_all
  | @insert x S hxS hSfin ih =>
      intro hlen hbase
      have hxlen  := hlen x (Set.mem_insert _ _)
      have hx1 : x ≠ 1 := by
        intro h
        rw [h, clen_one] at hxlen
        omega
      set Prev : Zpos A X M att → Prop :=
        fun z => ZUpto n z ∨ ∃ y ∈ S, InZChamber y z with hPrevDef
      have hup : ∀ z z' : Zpos A X M att, z ≤ z' → Prev z → Prev z' := by
        classical grind [zUpto_up, inZChamber_of_le]
      have hinter : ∀ z : Zpos A X M att, (Prev z ∧ InZChamber x z) ↔ ZJSet x z := by
        intro z
        constructor
        · rintro ⟨hprev', hzx⟩
          rcases hprev' with ⟨y, hy, hyz⟩ | ⟨y, hyS, hyz⟩
          · classical grind [FiniteChains.Davis.mem_shorter_zchamber_iff]
          · classical grind [FiniteChains.Davis.mem_earlier_zchamber_iff, Set.mem_insert_of_mem]
        · intro hJ
          have hzx  := zJSet_imp_inZChamber hJ
          obtain ⟨y, hylt, hyz⟩ := (mem_shorter_zchamber_iff hzx).2 hJ
          exact ⟨Or.inl ⟨y, by omega, hyz⟩, hzx⟩
      obtain ⟨j0, hj0⟩ := exists_zJSet (X := X) (M := M) (att := att) hx1
      have hmixPrev : ∀ a b : Zpos A X M att, a ≤ b →
          (fun z => Prev z ∨ InZChamber x z) a → (fun z => Prev z ∨ InZChamber x z) b →
          (Prev a ∧ Prev b) ∨ (InZChamber x a ∧ InZChamber x b) := by
        rintro a b hab (ha | ha) _
        · exact Or.inl ⟨ha, hup a b hab ha⟩
        · classical grind [inZChamber_of_le]
      have hmain : InjIn (fun z : Zpos A X M att => Prev z ∨ InZChamber x z) (InZBaseAt w0) := by
        by_cases hin : RACG.clen A w0 ≤ n ∨ w0 ∈ S
        · -- the copy of the base is already inside the earlier union
          have hPrevInj  := ih (fun y hy =>
            hlen y (Set.mem_insert_of_mem _ hy)) hin
          have hcopy : ∀ z : Zpos A X M att, InZBaseAt w0 z → Prev z := by
            grind [inZBaseAt_imp_zUpto, inZBaseAt_imp_inZChamber]
          refine injIn_trans hcopy ?_ hPrevInj
          exact injIn_union_of_unmixed (B := InZChamber x) (J := ZJSet x) hmixPrev
            (fun z => (hinter z).symm) (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0
        · -- the chamber added now is the marked chamber carrying the copy
          have hw0x : w0 = x := by
            grind
          subst hw0x
          have hchamber : InjIn (fun z : Zpos A X M att => Prev z ∨ InZChamber w0 z)
              (InZChamber w0) := by
            refine injIn_union_of_unmixed (B := Prev) (J := ZJSet w0) ?_
              (fun z => by
                rw [← hinter z]
                exact and_comm)
              (connectedIn_zJSet hx1) (simplyConnectedIn_zJSet hx1) hj0
            rintro a b hab (ha | ha) _
            · exact Or.inr ⟨ha, hup a b hab ha⟩
            · grind
          exact injIn_trans (fun z hz => inZBaseAt_imp_inZChamber hz) hchamber
            (injIn_zchamber_base hw0)
      refine injIn_congr_left (fun z => ?_) hmain
      constructor
      · grind
      · grind

include hw0 in
/-- **A copy of the base is injective on path classes inside every initial union of chambers.** -/
theorem injIn_zupto   :
    ∀ n : ℕ, RACG.clen A w0 ≤ n →
      InjIn (ZUpto (A := A) (X := X) (M := M) (att := att) n) (InZBaseAt w0) := by
  intro n
  induction n with
  | zero =>
      intro h
      have hw1  := (RACG.clen_eq_zero_iff A).1 (Nat.le_zero.1 h)
      subst hw1
      exact injIn_congr_left (fun z => (zUpto_zero_iff z).symm) (injIn_zchamber_base hw0)
  | succ n ih =>
      intro h
      have hcond : RACG.clen A w0 ≤ n ∨ w0 ∈ {x : CayGroup A | RACG.clen A x = n + 1} := by
        grind
      have hstep := injIn_zupto_insert hw0 n ih {x : CayGroup A | RACG.clen A x = n + 1}
        (level_finite A (n + 1)) (fun _ hy => hy) hcond
      refine injIn_congr_left (fun z => ?_) hstep
      constructor
      · rintro (⟨y, hy, hyz⟩ | ⟨y, hy, hyz⟩)
        · exact ⟨y, by omega, hyz⟩
        · exact ⟨y, le_of_eq hy, hyz⟩
      · rintro ⟨y, hy, hyz⟩
        rcases Nat.lt_or_ge (RACG.clen A y) (n + 1) with h' | h'
        · exact Or.inl ⟨y, by omega, hyz⟩
        · exact Or.inr ⟨y, le_antisymm hy h', hyz⟩

include hw0 in
/-- **A copy of the base is injective on path classes inside the whole of `Z`.**  A homotopy is a
finite derivation, so it involves only finitely many cells and therefore lies in some initial
union of chambers. -/
theorem injIn_zpos   :
    InjIn (fun _ : Zpos A X M att => True) (InZBaseAt w0) := by
  intro v l hv hp hl hnull
  obtain ⟨n, hn⟩ := exists_htpyIn_of_htpy
    (D := fun n => ZUpto (A := A) (X := X) (M := M) (att := att) n)
    (fun m n hmn z hz => by
      grind [FiniteChains.Davis.ZUpto])
    (fun z => ⟨zlen z, zUpto_zlen z⟩) (htpyIn_true_iff.mp hnull)
  refine injIn_zupto hw0 (max n (RACG.clen A w0)) (le_max_right _ _) v l hv hp hl ?_
  refine HtpyIn.mono (fun z hz => ?_) hn
  obtain ⟨y, hy, hyz⟩ := hz
  exact ⟨y, le_trans hy (le_max_left _ _), hyz⟩

/-! ### The conclusion for the fundamental group -/

/-- **Unconditional injectivity of a copy of the base in `π₁(Z)`.**  For every marked chamber
`w` of the model `Z` of modified chambers, and for every base point of the base poset `X`, the
inclusion of the copy of `X` glued into the chamber of `w` induces an injective homomorphism
`π₁(X) → π₁(Z)`.

No extension of the attaching map over the cone point of a chamber is assumed: the attaching map
`att` is the given monotone map on nonempty simplices only. -/
abbrev pi1Map_zNew_injective_uncond (w : {w : CayGroup A // M w}) (x : X)  :=
  pi1Map_injective_of_injIn (Bp := InZBaseAt w.1) (injIn_zpos w.2)
    (zNew_monotone w) (fun y => inZBaseAt_zNew w y)
    (zBaseRetr_monotone (A := A) (X := X) (M := M) (att := att) w.1)
    (fun y => zBaseRetr_zNew w y) x

/-- **Composing with a covering.**  If `Z` covers a complex `W`, the copy of the base is still
injective on fundamental groups after pushing down to `W`, because a covering is injective on
fundamental groups.  This is the covering step of the comparison with the article's complex; the
identification of `W` with the presentation complex of the substituted presentation is a
separate statement, and is not proved here. -/
abbrev pi1Map_zNew_covering_injective {W : Comb.Complex2}
    (q : Comb.Hom (orderCx (Zpos A X M att)) W) (hq : Comb.IsCovering q)
    (w : {w : CayGroup A // M w}) (x : X)  :=
  (Comb.pi1Map_injective_of_isCovering hq _).comp (pi1Map_zNew_injective_uncond w x)

end FiniteChains.Davis

