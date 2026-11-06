module

public import Chazelle.Core.SweepEvLoopStartG
public import Chazelle.Rwx
public import Chazelle.UnfoldTactics

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, the program)

`start = head ; stStep ; stStep ; stLab ; stGap ; stLog` and its run step `start_irs` with the
raw post `SRaw` (the registers and memory of the start, read off the parts).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep

@[expose] public section

/-- The head: the start key `(cGL, 0)`, empty labels, pointer `0`, flags `0`. -/
def stHead : List Instr :=
  [.copyN kE cGL, .constN kH 0, .constN kN 0, .constN sP 0, .constN aF 0, .constN dF 0]

/-- **The program of the start of the event loop.** -/
def start : Stmt := .seq (block stHead) (.seq stStep (.seq stStep (.seq stLab (.seq stGap stLog))))

/-- The cost of the start. -/
def startK (T : ℕ) : ℕ :=
  6 + (stStepK + (stStepK + ((fposK 3 T + 4) + ((fposK 1 T + fposK 2 T + 5) + 16))))

theorem startK_le (T : ℕ) : startK T ≤ 200000 * (T + 1) := by
  ufo startK stStepK fposK

/-! ## The pointer after two steps -/

section Ptr

variable {P : Polygon} {J : Merge.Junction} {N₂ : NF}

theorem stepRes {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} {s s' : ℕ}
    (ha : ∀ hi : s < rs.length, soff P J rs[s] = Lst J → s' = s + 1)
    (hb : (∀ hi : s < rs.length, soff P J rs[s] ≠ Lst J) → s' = s) (j : ℕ) (hj : j = s) :
    (∀ hi : j < rs.length, soff P J rs[j] = Lst J → s' = j + 1) ∧
      ((∀ hi : j < rs.length, soff P J rs[j] ≠ Lst J) → s' = j) := by
  subst hj; exact ⟨ha, hb⟩

/-- **The pointer after two stop steps** skips exactly the stops at the start key. -/
theorem ptr_char (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N₂)
    {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    (hst : StopsOK J (N₂.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N₂ rs)) {s1 s2 : ℕ}
    (h1a : ∀ hi : 0 < rs.length, soff P J rs[0] = Lst J → s1 = 0 + 1)
    (h1b : (∀ hi : 0 < rs.length, soff P J rs[0] ≠ Lst J) → s1 = 0)
    (h2a : ∀ hi : s1 < rs.length, soff P J rs[s1] = Lst J → s2 = s1 + 1)
    (h2b : (∀ hi : s1 < rs.length, soff P J rs[s1] ≠ Lst J) → s2 = s1)
    (hat : ∀ i (hi : i < rs.length), i < s2 → soff P J rs[i] = Lst J) :
    ∀ i (hi : i < rs.length), i < s2 ↔ soff P J rs[i] = Lst J := by
  have ge : ∀ i (hi : i < rs.length), (Lst J : ℝ) ≤ soff P J rs[i] := fun i hi =>
    (stop_facts hst hi).2.2.2
  have s1le : s1 ≤ 1 := by
    by_cases h : ∃ hi : 0 < rs.length, soff P J rs[0] = Lst J
    · obtain ⟨hi, h⟩ := h; have := h1a hi h; omega
    · push Not at h; have := h1b h; omega
  have s2ge : s1 ≤ s2 := by
    by_cases h : ∃ hi : s1 < rs.length, soff P J rs[s1] = Lst J
    · obtain ⟨hi, h⟩ := h; have := h2a hi h; omega
    · push Not at h; have := h2b h; omega
  intro i hi
  refine ⟨hat i hi, fun hie => ?_⟩
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | h2
  · have := h1a hi hie; omega
  · have h0 : soff P J (rs[0]'(by omega)) = Lst J := by
      have := stops_sorted hst (i := 0) (i' := 1) (by omega) hi
      have := ge 0 (by omega)
      linarith
    have e1 : s1 = 1 := h1a (by omega) h0
    subst e1
    have := h2a hi hie
    omega
  · exfalso
    have h3 := stops_two hP hN hst (i := i - 2) (by omega)
    have e : rs[i - 2 + 2] = rs[i] := by congr 1; omega
    rw [e, hie] at h3
    have := ge (i - 2) (by omega)
    linarith

end Ptr

/-! ## The stop data along the start -/

theorem stopData_transport {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c c' : Config}
    {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (h : StopData P J N₂ c rs ax)
    (hsC : c'.nreg sC = c.nreg sC) (hsB : c'.nreg sB = c.nreg sB) (haB : c'.nreg aB = c.nreg aB)
    (hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧ c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) : StopData P J N₂ c' rs ax := by
  obtain ⟨hl, hlax, hSR, hAR, h5, h6, h7, h8⟩ := h
  refine ⟨by rwx [hsC], hlax, fun i hi => ?_, fun i hi => ?_, h5, h6, h7, h8⟩
  · rw [hsB, hm _ (by omega), hm _ (by omega), hm _ (by omega), hm _ (by omega), hm _ (by omega)]
    exact hSR i hi
  · rw [haB, hm _ (by omega), hm _ (by omega), hm _ (by omega), hm _ (by omega), hm _ (by omega)]
    exact hAR i hi

/-! ## Register sets -/

theorem fpr_stR {r : ℕ} (h : FPR r) : StR r := by
  unfold FPR FR at h; unfold StR
  simp [zT, fE, fA, fR, kE, kH, kN, kL, gN, gR, sP, dF, lC, sw] at h ⊢
  omega

theorem lblR_stR {r : ℕ} (h : LblR kN kL r) : StR r := by
  unfold LblR at h; unfold StR
  simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw] at h ⊢
  omega

theorem gapR_stR {r : ℕ} (h : GapR r) : StR r := by
  unfold GapR at h; unfold StR
  simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw] at h ⊢
  omega

/-- The raw post of the start. -/
def SRaw (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (c c' : Config) : Prop :=
  c'.nreg kE = pK0 J ∧ c'.nreg kH = 0 ∧ c'.nreg dF = 0 ∧ c'.nreg lC = 1 ∧
  c'.nreg sP ≤ rs.length ∧ (∀ i (hi : i < rs.length), i < c'.nreg sP ↔ soff P J rs[i] = Lst J) ∧
  c'.nreg kN ≤ 4 ∧ (∀ v ∈ lblOf c' kN kL, v < N₂.nRegions) ∧
  (∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax.getD i d5).1 = 1 →
    ∀ v ∈ axLabs (ax.getD i d5), v ∈ lblOf c' kN kL) ∧
  ((∀ i (hi : i < rs.length), soff P J rs[i] = Lst J → (ax.getD i d5).1 ≠ 1) →
    c'.nreg kN = 1 ∧ c'.nreg kL < N₂.nRegions ∧
    BeforeFaces (chainModel J.right) (vEnd J) 0
      (regOf (chainModel J.right) (Qof P) N₂ (c'.nreg kL))) ∧
  c'.nreg gN ≤ 2 ∧ (∀ i, i < c'.nreg gN → c'.nreg (gR + i) < N₂.nRegions) ∧
  (∀ V, GapLab J (N₂.F (chainModel J.right) (Qof P)) V →
    ∃ i, i < c'.nreg gN ∧ regOf (chainModel J.right) (Qof P) N₂ (c'.nreg (gR + i)) = V) ∧
  c'.nmem (c.nreg lB) = c'.nreg kE ∧ c'.nmem (c.nreg lB + 1) = c'.nreg kH ∧
  c'.nmem (c.nreg lB + 2) = c'.nreg kN ∧
  (∀ i, i < 4 → c'.nmem (c.nreg lB + 3 + i) = c'.nreg (kL + i)) ∧
  (∀ x, x < c.nreg ALLOC → (x < c.nreg lB ∨ c.nreg lB + 7 ≤ x) → c'.nmem x = c.nmem x) ∧
  (∀ r, bandOf r ∉ oracleBands → ¬ StR r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC

end

end SweepEv

end Chazelle.Core
