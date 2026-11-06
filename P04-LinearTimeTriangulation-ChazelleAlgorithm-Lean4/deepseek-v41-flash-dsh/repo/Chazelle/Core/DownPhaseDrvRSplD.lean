module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRSplC

/-!
# Down-phase driver (RAM side): the splice, part 3 (the merge)

`splC_exec`: `spl5 ; cpS ; spl6 ; cpS ; mergeE` copies `E` and the sorted new codes side by side
into a fresh array and merges them into a second fresh array (register `210071`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- The third part of the splice. -/
def splC : Stmt := .seq spl5 (.seq cpS (.seq spl6 (.seq cpS mergeE)))

/-- The registers `spl5`, `spl6` write. -/
def Bs56 (r : ℕ) : Bool :=
  decide (r = 210030) || decide (210061 ≤ r ∧ r ≤ 210063) || decide (210070 ≤ r ∧ r ≤ 210073) ||
    decide (r = 9999)

/-- The registers `spl6` writes. -/
def Bs6 (r : ℕ) : Bool := decide (210061 ≤ r ∧ r ≤ 210063)

theorem wrM2_spl5 : wrM2 Bs56 (fun _ => false) spl5 = true := ⌖
theorem wrM2_spl6 : wrM2 Bs6 (fun _ => false) spl6 = true := ⌖
theorem wrM2_cpS : wrM2 Bcp (fun _ => false) cpS = true := ⌖

/-- The cost of `splC`. -/
def splCCost (K K₂ : ℕ) : ℕ := 14 * K + 7 * (2 * K₂) + 11026 * (2 * (K + K₂)) + 40

section exec

variable {P : Polygon} {W : ℕ}


/-- **The merged event list.** -/
theorem splC_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {D T SE Rb K K₂ : ℕ} {M : Model} {L' : List (ℕ × ℕ × ℕ)}
    {E E₂ : List ℕ}
    (h27 : c.nreg 210027 = 2 * K) (h28 : c.nreg 210028 = 2 * K₂) (h29 : c.nreg 210029 = 2 * (K + K₂))
    (h04 : c.nreg 210004 = SE) (h48 : c.nreg 210048 = Rb) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L'.length)
    (hlen : L'.length = K + K₂)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hok : ChordTriplesOK M (Qof P) L') (hrec : RecsAt c.nmem T L')
    (hT : T + 8 * L'.length ≤ c.nreg ALLOC)
    (hE : seg c.nmem SE (2 * K) = E) (hSE : SE + 2 * K ≤ c.nreg ALLOC)
    (hE₂ : seg c.nmem Rb (2 * K₂) = E₂) (hRb : Rb + 2 * K₂ ≤ c.nreg ALLOC)
    (hcodes : ∀ x ∈ E ++ E₂, x < 2 * L'.length)
    (hroom : c.nreg ALLOC + 4 * (2 * (K + K₂)) + splCCost K K₂ + 1 ≤ W) :
    ∃ c' k, Exec P W splC c c' k ∧ k ≤ splCCost K K₂ ∧ WordsBounded W c' ∧
      c'.nreg 210071 = c.nreg ALLOC + 2 * (K + K₂) ∧
      c'.nreg ALLOC = c.nreg ALLOC + 2 * (K + K₂) + 2 * (K + K₂) ∧
      seg c'.nmem (c'.nreg 210071) (2 * (K + K₂)) = List.merge E E₂ (DownDrv.codeLeB M (Qof P) L') ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bs56 r = false → Bcp r = false →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A₃ := c.nreg ALLOC with hA₃
  set h := 2 * (K + K₂) with hh
  -- the arrays and the arguments of the first copy
  obtain ⟨c₁, k₁, e₁, hk₁, v30, v71, vA, v70, v72, v73, v61, v62, v63, hm₁⟩ : ∃ c₁ k₁,
      Exec P W spl5 c c₁ k₁ ∧ k₁ = 9 ∧ c₁.nreg 210030 = A₃ ∧ c₁.nreg 210071 = A₃ + h ∧
      c₁.nreg ALLOC = A₃ + h + h ∧ c₁.nreg 210070 = A₃ ∧ c₁.nreg 210072 = 2 * K ∧
      c₁.nreg 210073 = h ∧ c₁.nreg 210061 = 2 * K ∧ c₁.nreg 210062 = SE ∧ c₁.nreg 210063 = A₃ ∧
      c₁.nmem = c.nmem := by
    unfold spl5
    exec_block
    all_goals try (config_simp; (try simp only [h29, h27, h04, show c.nreg 9999 = A₃ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h29, h27, h04, show c.nreg 9999 = A₃ from rfl])
  have g₁ : ∀ r, Bs56 r = false → c₁.nreg r = c.nreg r := (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).1
  -- copy `E`
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, hs₂, hm₂, f₂⟩ := cpS_exec (P := P) e₁.wb_right v61 v62 v63
    (by rw [g₁ _ (by decide), h34]) (Or.inl (by omega)) (by omega) (by omega)
  have g₂ := f₂.1
  -- the arguments of the second copy
  obtain ⟨c₃, k₃, e₃, hk₃, u61, u62, u63, hm₃⟩ : ∃ c₃ k₃, Exec P W spl6 c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 210061 = 2 * K₂ ∧ c₃.nreg 210062 = Rb ∧ c₃.nreg 210063 = A₃ + 2 * K ∧
      c₃.nmem = c₂.nmem := by
    have a28 : c₂.nreg 210028 = 2 * K₂ := by rw [g₂ _ (by decide), g₁ _ (by decide), h28]
    have a48 : c₂.nreg 210048 = Rb := by rw [g₂ _ (by decide), g₁ _ (by decide), h48]
    have a30 : c₂.nreg 210030 = A₃ := by rw [g₂ _ (by decide), v30]
    have a27 : c₂.nreg 210027 = 2 * K := by rw [g₂ _ (by decide), g₁ _ (by decide), h27]
    unfold spl6
    exec_block
    all_goals try (config_simp; (try simp only [a28, a48, a30, a27]); omega)
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> (try simp only [a28, a48, a30, a27])
  have g₃ : ∀ r, Bs6 r = false → c₃.nreg r = c₂.nreg r :=
    (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).1
  -- copy the new codes
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, f₄⟩ := cpS_exec (P := P) e₃.wb_right u61 u62 u63
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h34]) (Or.inl (by omega))
    (by omega) (by omega)
  have g₄ := f₄.1
  -- registers before the merge
  have k5 : ∀ r, Bcp r = false → Bs6 r = false → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [g₄ r h1, g₃ r h2, g₂ r h1]
  have k : ∀ r, Bcp r = false → Bs56 r = false → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k5 r h1 (by
      simp only [Bs56, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
      simp only [Bs6, decide_eq_false_iff_not]; omega), g₁ r h2]
  have hlow4 : ∀ a, a < A₃ → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hm₄ a (Or.inl (by omega)), hm₃, hm₂ a (Or.inl (by omega)), hm₁]
  have hseg4 : seg c₄.nmem A₃ (2 * K) = E := by
    rw [seg_congr (m' := c₂.nmem) fun i hi => by rw [hm₄ _ (Or.inl (by omega)), hm₃], hs₂, hm₁, hE]
  have hseg4' : seg c₄.nmem (A₃ + 2 * K) (h - 2 * K) = E₂ := by
    rw [show h - 2 * K = 2 * K₂ by omega, hs₄, hm₃]
    rw [seg_congr (m' := c.nmem) fun i hi => by rw [hm₂ _ (Or.inl (by omega)), hm₁], hE₂]
  obtain ⟨hM₄, hwf₄⟩ := desc_agree hwf hM (m' := c₄.nmem) fun a ha => hlow4 a ha
  have hrec4 : RecsAt c₄.nmem T L' := fun q hq => by
    obtain ⟨r1, r2, r3, r4⟩ := hrec q hq
    exact ⟨by rw [hlow4 _ (by omega)]; exact r1, by rw [hlow4 _ (by omega)]; exact r2,
      by rw [hlow4 _ (by omega)]; exact r3, by rw [hlow4 _ (by omega)]; exact r4⟩
  -- the merge
  obtain ⟨c₅, k₅, e₅, hk₅, w₅, hseg5, hm₅, fr₅, hA₅, rr₅, rm₅, o₅, -, -, -, -⟩ :=
    mergeE_exec (P := P) (W := W) hG hWn c₄ w₄ (S := A₃) (Dst := A₃ + h) (mid := 2 * K) (hi := h)
      (D := D) (T := T) (M := M) (L := L') (E := E) (E₂ := E₂)
      (by rw [k5 _ (by decide) (by decide), v70]) (by rw [k5 _ (by decide) (by decide), v71])
      (by rw [k5 _ (by decide) (by decide), v72]) (by rw [k5 _ (by decide) (by decide), v73])
      (by omega) (by rw [k _ (by decide) (by decide), h40])
      (by rw [k _ (by decide) (by decide), h42]) (by rw [k _ (by decide) (by decide), h42'])
      (hwf₄.mono (by omega)) hM₄ hok hrec4 (by omega) hseg4 hseg4' hcodes (by omega) (by omega)
  have hA₄ : c₄.nreg ALLOC = A₃ + h + h := by rw [k5 _ (by decide) (by decide), vA]
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by unfold splCCost; omega, w₅, ?_, by rw [hA₅, hA₄], ?_, fun a ha => ?_,
    fun r hr h1 h2 hra => ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [fr₅ _ (by simp [bandOf, bSort, bSign, bBuild]) (by decide), k5 _ (by decide) (by decide), v71]
  · rw [fr₅ _ (by simp [bandOf, bSort, bSign, bBuild]) (by decide), k5 _ (by decide) (by decide), v71]
    exact hseg5
  · rw [hm₅ a (Or.inl (by omega)), hlow4 a ha]
  · rw [fr₅ r hr hra, k r h2 h1]
  · rw [rr₅ r hr, exec_frameM2 e₄ wrM2_cpS r rfl, exec_frameM2 e₃ wrM2_spl6 r rfl,
      exec_frameM2 e₂ wrM2_cpS r rfl, exec_frameM2 e₁ wrM2_spl5 r rfl]
  · rw [rm₅, f₄.2.2.1, (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).2.2.1, f₂.2.2.1,
      (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).2.2.1]
  · rw [o₅, f₄.2.2.2, (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).2.2.2, f₂.2.2.2,
      (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).2.2.2]

end exec

end

end DrvR

end Chazelle.Core
