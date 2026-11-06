module

public import Chazelle.Core.DownPhaseDrvRSplA
public import Chazelle.Core.NFBuildMain
public import Chazelle.Rwx
public import Chazelle.SimpTactics
set_option maxHeartbeats 4000000

/-!
# Down-phase driver (RAM side): the splice, part 1 (the new chord list)

`splA_exec`: `spl0 ; cpS ; spl1 ; cpS` writes `L ++ L₂` at the entry allocator `A₀` and sets the
size registers.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- A chord list read from a copied segment. -/
theorem chordListAt_of_seg {m m' : ℕ → ℕ} {B A : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : ChordListAt m B L) (hs : seg m' A (3 * L.length) = seg m B (3 * L.length)) :
    ChordListAt m' A L := by
  intro i hi
  have e : ∀ q, q < 3 * L.length → m' (A + q) = m (B + q) := fun q hq => by
    have := congrArg (fun l => l.getD q 0) hs
    simp only [SortL.seg_getD _ hq] at this
    exact this
  obtain ⟨h1, h2, h3⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rwx [e (3 * i) (by omega)]
  · rw [show A + 3 * i + 1 = A + (3 * i + 1) by ring, e _ (by omega),
      show B + (3 * i + 1) = B + 3 * i + 1 by ring]; exact h2
  · rw [show A + 3 * i + 2 = A + (3 * i + 2) by ring, e _ (by omega),
      show B + (3 * i + 2) = B + 3 * i + 2 by ring]; exact h3

/-- A chord list is the concatenation of its two parts. -/
theorem chordListAt_append {m : ℕ → ℕ} {A : ℕ} {L L₂ : List (ℕ × ℕ × ℕ)}
    (h₁ : ChordListAt m A L) (h₂ : ChordListAt m (A + 3 * L.length) L₂) :
    ChordListAt m A (L ++ L₂) := by
  intro i hi
  rw [List.length_append] at hi
  rcases Nat.lt_or_ge i L.length with h | h
  · rw [List.getD_append _ _ _ _ h]; exact h₁ i h
  · obtain ⟨a1, a2, a3⟩ := h₂ (i - L.length) (by omega)
    rw [List.getD_append_right _ _ _ _ h]
    refine ⟨?_, ?_, ?_⟩
    · rw [← a1]; congr 1; omega
    · rw [← a2]; congr 1; omega
    · rw [← a3]; congr 1; omega

/-- The registers `spl0 ; cpS ; spl1 ; cpS` writes. -/
def BsA (r : ℕ) : Bool :=
  decide (210025 ≤ r ∧ r ≤ 210029) || decide (r = 210034) || decide (210060 ≤ r ∧ r ≤ 210067) ||
    decide (r = 9999)

theorem wrM_spl0 : wrM BsA spl0 = true := by decide

/-- The registers `spl1` writes. -/
def Bs1 (r : ℕ) : Bool := decide (210061 ≤ r ∧ r ≤ 210063)

theorem wrM_spl1 : wrM Bs1 spl1 = true := by decide

theorem FrameM.of_s1 {c c' : Config} (h : FrameM Bs1 c c') : FrameM BsA c c' :=
  h.mono fun r hr => by
    sio only [Bs1, BsA, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢

theorem Bcp_BsA {r : ℕ} (h : Bcp r = true) : BsA r = true := by
  sio only [Bcp, BsA, Bool.or_eq_true, decide_eq_true_eq] at h ⊢

theorem FrameM.of_cp {c c' : Config} (h : FrameM Bcp c c') : FrameM BsA c c' :=
  h.mono fun _r hr => Bcp_BsA hr

section exec

variable {P : Polygon} {W : ℕ}

/-- **The new chord list.** -/
theorem splA_exec (c : Config) (hw : WordsBounded W c) {B K B₂ K₂ : ℕ}
    {L L₂ : List (ℕ × ℕ × ℕ)} (h02 : c.nreg 210002 = B) (h03 : c.nreg 210003 = K)
    (h20 : c.nreg 210020 = B₂) (h21 : c.nreg 210021 = K₂) (hK : K = L.length)
    (hK₂ : K₂ = L₂.length) (hL : ChordListAt c.nmem B L) (hL₂ : ChordListAt c.nmem B₂ L₂)
    (hB : B + 3 * K ≤ c.nreg ALLOC) (hB₂ : B₂ + 3 * K₂ ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 3 * (K + K₂) + 22 ≤ W) :
    ∃ c' k, Exec P W (.seq spl0 (.seq cpS (.seq spl1 cpS))) c c' k ∧
      k ≤ 21 * (K + K₂) + 30 ∧ WordsBounded W c' ∧
      c'.nreg 210025 = K + K₂ ∧ c'.nreg 210026 = c.nreg ALLOC ∧ c'.nreg 210027 = 2 * K ∧
      c'.nreg 210028 = 2 * K₂ ∧ c'.nreg 210029 = 2 * (K + K₂) ∧ c'.nreg 210034 = 1 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (K + K₂) ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (L ++ L₂) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ FrameM BsA c c' ∧ c'.rreg = c.rreg := by
  set A₀ := c.nreg ALLOC with hA₀
  -- sizes and the first copy's arguments
  obtain ⟨c₁, k₁, e₁, hk₁, v25, v26, v27, v28, v29, v34, vA, v67, v61, v62, v63, hm₁⟩ :
      ∃ c₁ k₁, Exec P W spl0 c c₁ k₁ ∧ k₁ = 14 ∧ c₁.nreg 210025 = K + K₂ ∧ c₁.nreg 210026 = A₀ ∧
      c₁.nreg 210027 = 2 * K ∧ c₁.nreg 210028 = 2 * K₂ ∧ c₁.nreg 210029 = 2 * (K + K₂) ∧
      c₁.nreg 210034 = 1 ∧ c₁.nreg ALLOC = A₀ + 3 * (K + K₂) ∧ c₁.nreg 210067 = 3 * K ∧
      c₁.nreg 210061 = 3 * K ∧ c₁.nreg 210062 = B ∧ c₁.nreg 210063 = A₀ ∧ c₁.nmem = c.nmem := by
    unfold spl0
    exec_block
    all_goals try (config_simp; (try simp only [h02, h03, h21, show c.nreg 9999 = A₀ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h02, h03, h21, show c.nreg 9999 = A₀ from rfl]) <;> omega
  have f₁ := exec_frameM e₁ wrM_spl0
  -- copy `L`
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, hs₂, hm₂, f₂⟩ := cpS_exec (P := P) e₁.wb_right v61 v62 v63 v34
    (Or.inl (by omega)) (by omega) (by omega)
  have g₂  := f₂.1
  -- the second copy's arguments
  obtain ⟨c₃, k₃, e₃, hk₃, w61, w62, w63, hm₃⟩ : ∃ c₃ k₃, Exec P W spl1 c₂ c₃ k₃ ∧ k₃ = 4 ∧
      c₃.nreg 210061 = 3 * K₂ ∧ c₃.nreg 210062 = B₂ ∧ c₃.nreg 210063 = A₀ + 3 * K ∧
      c₃.nmem = c₂.nmem := by
    have h21' : c₂.nreg 210021 = K₂ := by rw [g₂ _ (by decide), f₁.1 _ (by decide), h21]
    have h20' : c₂.nreg 210020 = B₂ := by rw [g₂ _ (by decide), f₁.1 _ (by decide), h20]
    have h26' : c₂.nreg 210026 = A₀ := by rw [g₂ _ (by decide), v26]
    have h67' : c₂.nreg 210067 = 3 * K := by rw [g₂ _ (by decide), v67]
    unfold spl1
    exec_block
    all_goals try (config_simp; (try simp only [h21', h20', h26', h67']); omega)
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> (try simp only [h21', h20', h26', h67']);
      omega
  have f₃ := exec_frameM e₃ wrM_spl1
  have g₃  := f₃.1
  -- copy `L₂`
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, f₄⟩ := cpS_exec (P := P) e₃.wb_right w61 w62 w63
    (by rw [g₃ _ (by decide), g₂ _ (by decide), v34]) (Or.inl (by omega)) (by omega) (by omega)
  have g₄  := f₄.1
  have k : ∀ r, Bcp r = false → Bs1 r = false → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    rw [g₄ r h1, g₃ r h2, g₂ r h1]
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, w₄,
    by rwx [k _ (by decide) (by decide)], by rwx [k _ (by decide) (by decide)],
    by rwx [k _ (by decide) (by decide)], by rwx [k _ (by decide) (by decide)],
    by rwx [k _ (by decide) (by decide)], by rwx [k _ (by decide) (by decide)],
    by rw [k _ (by decide) (by decide)]; exact vA, ?_, fun a ha => ?_,
    ((f₁.trans (FrameM.of_cp f₂)).trans (FrameM.of_s1 f₃)).trans (FrameM.of_cp f₄), ?_⟩
  · refine chordListAt_append (chordListAt_of_seg hL ?_) (chordListAt_of_seg hL₂ ?_)
    · rw [← hK]
      rw [seg_congr (m := c₄.nmem) (m' := c₂.nmem) fun i hi => by
        rw [hm₄ _ (Or.inl (by omega)), hm₃]]
      rw [hs₂, hm₁]
    · rw [← hK, ← hK₂, hs₄, hm₃]
      apply seg_congr; intro i hi
      rw [hm₂ _ (Or.inl (by omega)), hm₁]
  · rw [hm₄ _ (Or.inl (by omega)), hm₃, hm₂ _ (Or.inl (by omega)), hm₁]
  · funext r
    exact exec_frameM2 (.seq e₁ (.seq e₂ (.seq e₃ e₄))) (BN := BsA) (BR := fun _ => false)
      (by decide) r rfl

end exec

end

end DrvR

end Chazelle.Core
