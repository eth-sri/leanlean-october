module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTValid

/-!
# WP-E, the candidate test on the RAM, part 11: the validity bit

`validS kc ls tn tp` computes the validity bit `83010` of the candidate test (`ValidB`): the
region must have an exit chord (`83050`), the direction must point into the left sector (`ls`);
then the arc scan decides; at a walk vertex (height code `0`, which is the canonical code of a
vertex) an arc beginning (ending) at the vertex also qualifies if the turn from the next edge
(to the previous edge) is positive and no exit chord leaves the vertex in the direction (the exit
scan).

* `valid_rs`: `83010 = 1` iff `ValidB`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- Set the flag `r` if `50210 = 1`. -/
def setIf1 (r : ℕ) : Stmt := .ifLtN 50210 83023 .skip (.ifLtN 83023 50210 .skip (setF r))

theorem setIf1_rs {r : ℕ} (hr : Scr r) (hI : TInv W c₀ c) :
    RS P W c₀ (setIf1 r) c 5 (fun c' => FlagUpd c c' r (c.nreg 50210 = 1)) := by
  have h1 := hI.h23
  unfold setIf1
  by_cases a : c.nreg 50210 < 1
  · exact RS.ifT (⋄) (leaf_skip hI (by omega))
  · by_cases b : 1 < c.nreg 50210
    · exact RS.ifF (⋄) (RS.ifT (by omega) (leaf_skip hI (by omega)))
    · exact RS.ifF (⋄) (RS.ifF (by omega) (leaf_set hI hr le_rfl (by omega)))

/-- If the flag `f` is set, run the turning test `t` and record a positive turn in `83052`. -/
def condTurn (f : ℕ) (t : Stmt) : Stmt := .ifLtN f 83023 .skip (.seq t (setIf1 83052))

theorem condTurn_rs {f : ℕ} {t : Stmt} {Kt : ℕ} {turn : Prop}
    (ht : ∀ c, TInv W c₀ c → c.nreg ALLOC + Kt ≤ W →
      ∃ c' k, Exec P W t c c' k ∧ k ≤ Kt ∧ (c'.nreg 50210 = 1 ↔ turn) ∧ TStep W c₀ c c' k)
    (hI : TInv W c₀ c) (hf : c.nreg f ≤ 1) (hroom : c.nreg ALLOC + Kt ≤ W) :
    RS P W c₀ (condTurn f t) c (Kt + 7) (fun c' => FlagUpd c c' 83052 (c.nreg f = 1 ∧ turn)) := by
  have h1 := hI.h23
  unfold condTurn
  by_cases a : c.nreg f < 1
  · exact RS.ifT (⋄) (leaf_skip hI (by omega))
  · refine RS.ifF (⋄) (RS.seq (RS.op (ht c hI hroom)) fun c₁ hI₁ _ ⟨v₁, h8₁⟩ =>
      (setIf1_rs (by unfold Scr; omega) hI₁).mono le_rfl fun c₂ ⟨u1, u2, a₂⟩ => ?_)
    have e52 : c₁.nreg 83052 = c.nreg 83052 := h8₁ _ (⊛) (by norm_num)
    refine ⟨?_, fun h => u2 (by rw [e52]; exact h), (Agr.of_band h8₁ []).trans a₂⟩
    Ξ u1, e52, v₁
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨⋄, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact Or.inl h
      · exact Or.inr h

/-- **The vertex case**: an arc begins (ends) at the vertex with a positive turn, and no exit
chord leaves the vertex in the direction. -/
def vertexCase (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (tn tp : Stmt) : Stmt :=
  .seq (.instr (.constN 83052 0)) (.seq (condTurn 83043 tn) (.seq (condTurn 83044 tp)
    (.ifLtN 83052 83023 .skip (.seq (exitScan kc) (.ifLtN 83046 83023 (setF 83010) .skip)))))

/-- The cost bound of the vertex case. -/
def vertexK (Kk Kt D : ℕ) : ℕ := 1 + ((Kt + 7) + ((Kt + 7) + (exitScanK Kk D + 5)))

/-- The scratch registers of the validity check. -/
def validScr : List ℕ := [83010, 83030, 83031, 83032, 83033, 83034, 83035, 83036, 83037, 83038,
  83039, 83040, 83041, 83042, 83043, 83044, 83046, 83047, 83048, 83050, 83051, 83052]

theorem vertexCase_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk) {tn tp : Stmt}
    {Kt : ℕ} (hT : TurnOK tn tp Kt) (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hv : c₀.nreg 83006 = 0)
    (h10 : c.nreg 83010 = 0) (h43 : c.nreg 83043 ≤ 1) (h44 : c.nreg 83044 ≤ 1)
    (hroom : c.nreg ALLOC + vertexK Kk Kt (N.region (c₀.nreg 83002)).chords.length ≤ W) :
    RS P W c₀ (vertexCase kc tn tp) c (vertexK Kk Kt (N.region (c₀.nreg 83002)).chords.length)
      (fun c' => c'.nreg 83010 ≤ 1 ∧
        (c'.nreg 83010 = 1 ↔ ((c.nreg 83043 = 1 ∧ TurnNB M (xOf c₀) (c₀.nreg 83008)) ∨
          (c.nreg 83044 = 1 ∧ TurnPB M (xOf c₀) (c₀.nreg 83008))) ∧
          Clear M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧ Agr c c' validScr) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rw [hI.h23] at this; exact this
  unfold vertexCase vertexK
  refine RS.seq (RS.const hI (r := 83052) (v := 0) (by unfold Scr; omega) (⋄))
    fun c₁ hI₁ hA₁ h₁ => ?_
  have q43 : c₁.nreg 83043 = c.nreg 83043 := by rw [h₁, upd_ne (⊛)]
  have q44 : c₁.nreg 83044 = c.nreg 83044 := by rw [h₁, upd_ne (⊛)]
  refine RS.seq (condTurn_rs (fun c h1 h2 => hT.1 P W M N c₀ c hE h1 h2) hI₁ (by rw [q43]; exact h43)
    (by unfold vertexK at hroom; omega)) fun c₂ hI₂ hA₂ ⟨u1, u2, a₂⟩ => ?_
  have q44' : c₂.nreg 83044 = c.nreg 83044 := by
    rw [a₂ _ (⊛) (by norm_num) (by simp), q44]
  refine RS.seq (condTurn_rs (fun c h1 h2 => hT.2 P W M N c₀ c hE h1 hv h2) hI₂ (by rw [q44']; exact h44)
    (by unfold vertexK at hroom; omega)) fun c₃ hI₃ hA₃ ⟨v1, v2, a₃⟩ => ?_
  have e52 : c₁.nreg 83052 = 0 := Ρ h₁, upd_eq
  have ok : c₃.nreg 83052 = 1 ↔ ((c.nreg 83043 = 1 ∧ TurnNB M (xOf c₀) (c₀.nreg 83008)) ∨
      (c.nreg 83044 = 1 ∧ TurnPB M (xOf c₀) (c₀.nreg 83008))) := by
    rw [v1, u1, e52, q43, q44']; simp
  have ok1 : c₃.nreg 83052 ≤ 1 := v2 (u2 (⋄))
  have a13 : Agr c c₃ [83052] := (((Agr.of_upd h₁).trans a₂).trans a₃).mono (✓)
  have e10 : c₃.nreg 83010 = 0 := by rw [a13 _ (⊛) (by norm_num) (by simp), h10]
  have h1 := hI₃.h23
  by_cases hok : c₃.nreg 83052 < 1
  · refine (RS.ifT (⋄) (RS.skip (K := 0) hI₃ (Q := fun c' => c'.nreg 83010 ≤ 1 ∧
      (c'.nreg 83010 = 1 ↔ ((c.nreg 83043 = 1 ∧ TurnNB M (xOf c₀) (c₀.nreg 83008)) ∨
        (c.nreg 83044 = 1 ∧ TurnPB M (xOf c₀) (c₀.nreg 83008))) ∧
        Clear M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧ Agr c c' validScr)
      ⟨⋄, ?_, a13.mono (by simp [validScr])⟩)).mono (by omega) (fun _ h => h)
    Ξ e10
    constructor
    · intro h; omega
    · rintro ⟨h, -⟩; have := ok.2 h; omega
  · refine RS.ifF (⋄) ?_
    refine RS.seq (exitScan_rs hK hE hI₃ (by unfold vertexK at hroom; omega))
      fun c₄ hI₄ hA₄ ⟨b1, b2, a₄⟩ => ?_
    have e10' : c₄.nreg 83010 = 0 := by rw [a₄ _ (⊛) (by norm_num) (by simp), e10]
    have h1' := hI₄.h23
    have hok' : c₃.nreg 83052 = 1 := ⋄
    have agr : Agr c c₄ validScr := (a13.trans a₄).mono (⊚ validScr)
    by_cases hb : c₄.nreg 83046 < c₄.nreg 83023
    · refine (RS.ifT hb (RS.const hI₄ (r := 83010) (v := 1) (by unfold Scr; omega)
        hW1)).mono (⊛) fun c' h' => ⟨by rw [h', upd_eq], ?_, ?_⟩
      · Ξ h', upd_eq
        ϴ true_iff
        refine ⟨ok.1 hok', ?_⟩
        by_contra hc
        have := b2.2 hc
        omega
      · exact agr.trans (Agr.of_upd h') |>.mono (⊚ validScr)
    · refine (RS.ifF hb (RS.skip (K := 0) hI₄ (Q := fun c' => c'.nreg 83010 ≤ 1 ∧
        (c'.nreg 83010 = 1 ↔ ((c.nreg 83043 = 1 ∧ TurnNB M (xOf c₀) (c₀.nreg 83008)) ∨
          (c.nreg 83044 = 1 ∧ TurnPB M (xOf c₀) (c₀.nreg 83008))) ∧
          Clear M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧ Agr c c' validScr)
        ⟨⋄, ?_, agr⟩)).mono (by omega) (fun _ h => h)
      Ξ e10'
      constructor
      · intro h; omega
      · rintro ⟨-, hc⟩
        exact absurd (b2.1 (⋄)) (not_not.2 hc)


/-- **The validity check.** -/
def validS (kc : ℕ → ℕ → ℕ → ℕ → Stmt) (ls tn tp : Stmt) : Stmt :=
  .seq (.instr (.constN 83010 0)) (.seq (tRegLen 2) (.seq (.instr (.copyN 83050 50210))
    (.ifLtN 83050 83023 .skip (.seq ls (.ifLtN 50210 83023 .skip (.seq (arcScan kc)
      (.ifLtN 83042 83023 (.ifLtN 83006 83023 (vertexCase kc tn tp) .skip) (setF 83010))))))))

/-- The cost bound of the validity check for a region with `A` arcs and `D` exit chords. -/
def validK (Kk Kl Kt A D : ℕ) : ℕ :=
  1 + (13 + (1 + ((Kl + (arcScanK Kk A + (vertexK Kk Kt D + 4) + 2)) + 2)))

/-- **Contract of the validity check**: `83010 = 1` iff `ValidB`. -/
theorem valid_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk) {ls : Stmt} {Kl : ℕ}
    (hL : LeftOK ls Kl) {tn tp : Stmt} {Kt : ℕ} (hT : TurnOK tn tp Kt)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hroom : c.nreg ALLOC + validK Kk Kl Kt (N.region (c₀.nreg 83002)).arcs.length
      (N.region (c₀.nreg 83002)).chords.length ≤ W) :
    RS P W c₀ (validS kc ls tn tp) c (validK Kk Kl Kt (N.region (c₀.nreg 83002)).arcs.length
      (N.region (c₀.nreg 83002)).chords.length) (fun c' => c'.nreg 83010 ≤ 1 ∧
        (c'.nreg 83010 = 1 ↔ ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
        Agr c c' validScr) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rw [hI.h23] at this; exact this
  unfold validS validK
  refine RS.seq (RS.const hI (r := 83010) (v := 0) (by unfold Scr; omega) (⋄))
    fun c₁ hI₁ hA₁ h₁ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) (Or.inr rfl) hE hI₁ (by unfold validK at hroom; omega)))
    fun c₂ hI₂ hA₂ ⟨v₂, h8₂⟩ => ?_
  refine RS.seq (RS.copy hI₂ (r := 83050) (a := 50210) (by unfold Scr; omega))
    fun c₃ hI₃ hA₃ h₃ => ?_
  have a₃ : Agr c c₃ [83010, 83050] :=
    (((Agr.of_upd h₁).trans (Agr.of_band h8₂ [])).trans (Agr.of_upd h₃)).mono (✓)
  have e50 : c₃.nreg 83050 = (N.region (c₀.nreg 83002)).chords.length := by
    rw [h₃, upd_eq, v₂]; rfl
  have e10 : c₃.nreg 83010 = 0 := by
    rw [h₃, upd_ne (⊛), h8₂ _ (by norm_num) (by norm_num), h₁, upd_eq]
  have h1 := hI₃.h23
  -- no exit chord: invalid
  by_cases hD0 : c₃.nreg 83050 < c₃.nreg 83023
  · refine (RS.ifT hD0 (RS.skip (K := 0) hI₃ (Q := fun c' => c'.nreg 83010 ≤ 1 ∧
      (c'.nreg 83010 = 1 ↔ ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
      Agr c c' validScr) ⟨⋄, ?_, a₃.mono (by simp [validScr])⟩)).mono (by omega)
      (fun _ h => h)
    Ξ e10
    refine ⟨fun h => ⋄, fun ⟨hne, _⟩ => ?_⟩
    have : (N.region (c₀.nreg 83002)).chords.length = 0 := ⋄
    rw [List.length_eq_zero_iff] at this
    exact absurd this hne
  refine RS.ifF hD0 ?_
  have hne : (N.region (c₀.nreg 83002)).chords ≠ [] := by
    intro h; rw [h] at e50; simp at e50; omega
  have hFne : (N.F M (Qof P)).Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, i ∈ (N.region (c₀.nreg 83002)).chords := by
      rcases hl : (N.region (c₀.nreg 83002)).chords with _ | ⟨a, l⟩
      · exact absurd hl hne
      · exact ⟨a, ✓⟩
    obtain ⟨-, -, -, reg, -, -, -, hregs, -⟩ := hE.hNF
    exact ⟨_, chord_toSet_mem' (((hregs _ hE.hr).1 i).1 hi).1⟩
  refine RS.seq (RS.op (hL P W M N c₀ c₃ hE hI₃ (by unfold validK at hroom; omega)))
    fun c₄ hI₄ hA₄ ⟨bL, h8₄⟩ => ?_
  have h1' := hI₄.h23
  have a₄ : Agr c c₄ [83010, 83050] := (a₃.trans (Agr.of_band h8₄ [])).mono (✓)
  have e10' : c₄.nreg 83010 = 0 := by rw [h8₄ _ (⊛) (by norm_num), e10]
  by_cases hL0 : c₄.nreg 50210 < c₄.nreg 83023
  · refine (RS.ifT hL0 (RS.skip (K := 0) hI₄ (Q := fun c' => c'.nreg 83010 ≤ 1 ∧
      (c'.nreg 83010 = 1 ↔ ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
      Agr c c' validScr) ⟨⋄, ?_, a₄.mono (by simp [validScr])⟩)).mono (by omega)
      (fun _ h => h)
    Ξ e10'
    refine ⟨fun h => ⋄, fun ⟨_, hl, _⟩ => ?_⟩
    have := bL.2.2 hl
    omega
  have hLt : LeftB M P (xOf c₀) (c₀.nreg 83008) := bL.2.1 (by have := bL.1; omega)
  refine RS.ifF hL0 ?_
  refine RS.seq (arcScan_rs hK hE hFne hI₄ (by unfold validK at hroom; omega))
    fun c₅ hI₅ hA₅ ⟨f1, f2, f3, i1, i2, i3, a₅⟩ => ?_
  have agr5 : Agr c c₅ validScr := (a₄.trans a₅).mono (⊚ validScr)
  have e10'' : c₅.nreg 83010 = 0 := by
    rw [a₅ _ (⊛) (by norm_num) (by simp), e10']
  have h1'' := hI₅.h23
  have i6 : c₅.nreg 83006 = c₀.nreg 83006 := hI₅.hin 83006 (⊛) (by norm_num)
  -- the canonical code of the candidate
  have hz : M.param (Qof P) (xOf c₀) = 0 ↔ c₀.nreg 83006 = 0 := by
    constructor
    · intro h0
      rcases hE.hxc with h | h
      · exact h
      · exact absurd h0 (ne_of_gt h)
    · intro h0
      exact WalkKey.param_of_code_zero h0
  by_cases hin : c₅.nreg 83042 < c₅.nreg 83023
  · refine RS.ifT hin ?_
    have nIn : ¬ FIn M P N (c₀.nreg 83002) (xOf c₀) := fun h => by have := i1.2 h; omega
    by_cases hv : c₅.nreg 83006 < c₅.nreg 83023
    · refine (RS.ifT hv (vertexCase_rs hK hT hE hI₅ (by rw [← i6]; omega) e10'' f2 f3
        (by unfold validK at hroom; omega))).mono (⋄) fun c' ⟨v1, v2, a'⟩ =>
        ⟨v1, ?_, agr5.trans a' |>.mono (⊚ validScr)⟩
      Ξ v2, i2, i3
      unfold ValidB
      have h0 : M.param (Qof P) (xOf c₀) = 0 := hz.2 (⋄)
      ϴ nIn, false_or, h0, true_and
      exact ⟨fun h => ⟨hne, hLt, h⟩, fun ⟨_, _, h⟩ => h⟩
    · refine (RS.ifF hv (RS.skip (K := 0) hI₅ (Q := fun c' => c'.nreg 83010 ≤ 1 ∧
        (c'.nreg 83010 = 1 ↔ ValidB M P N (c₀.nreg 83002) (xOf c₀) (c₀.nreg 83008)) ∧
        Agr c c' validScr) ⟨⋄, ?_, agr5⟩)).mono (by omega) (fun _ h => h)
      Ξ e10''
      refine ⟨fun h => ⋄, fun ⟨_, _, h⟩ => ?_⟩
      rcases h with h | ⟨h0, -⟩
      · exact absurd h nIn
      · have := hz.1 h0; omega
  · refine (RS.ifF hin (RS.const hI₅ (r := 83010) (v := 1) (by unfold Scr; omega) hW1)).mono
      (⋄) fun c' h' => ⟨by rw [h', upd_eq], ?_, ?_⟩
    · Ξ h', upd_eq
      ϴ true_iff
      exact ⟨hne, hLt, Or.inl (i1.1 (⋄))⟩
    · exact (agr5.trans (Agr.of_upd h')).mono (⊚ validScr)

end

end Restore

end Chazelle.Core
