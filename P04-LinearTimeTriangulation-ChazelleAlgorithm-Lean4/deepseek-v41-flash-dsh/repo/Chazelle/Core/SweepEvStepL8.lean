module

public import Chazelle.Core.SweepEvStepL7

/-!
# The sweep (WP-D), stage 3: the log at the next key (Task L1)

**`SCtx.log'`**: the log of the next key is the log of the key followed by the record of the next
key (written by the next-key step): word facts, increasing offsets, no cut between consecutive
keys (`no_cut_iter`), label facts (`labIn_of_evInv` from `SCtx.labels`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-- In a list sorted strictly, every entry is at most the last one. -/
theorem stp_le_last {α : Type*} {f : α → ℝ} {l : List α} {y : α}
    (hpw : l.Pairwise (fun a b => f a < f b)) (hy : l.getLast? = some y) :
    ∀ a ∈ l, f a ≤ f y := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.1 hy
  intro a ha
  rcases List.mem_append.1 ha with h | h
  · exact (List.pairwise_append.1 hpw).2.2 a h y (List.mem_singleton_self y) |>.le
  · rw [List.mem_singleton] at h; rw [h]

namespace SCtx

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}
  {c cw cs co c' : Config} {A : Set (ℕ × ℕ × ℕ)} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
  (S : SCtx sh Bs F X Ok P W c₀ J N₁ N₂ c cw cs co c' A rs ax)
include S

set_option maxHeartbeats 4000000 in
/-- **The log at the next key.** -/
theorem log' : ∃ ls : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ), ls.length = c'.nreg lC ∧
    LogRecsAt c'.nmem (c'.nreg lB) ls ∧ LogWords P J N₂ ls ∧
    LogPre J (N₂.F (chainModel J.right) (Qof P)) (logOf J (Qof P) N₂ ls) ∧
    ls.getLast? = some (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL, c'.nreg (kL + 1),
      c'.nreg (kL + 2), c'.nreg (kL + 3)) := by
  classical
  have hP := S.E.hP
  have hS₂ : (chainModel J.right).ChordFamily (Qof P) (N₂.F (chainModel J.right) (Qof P)) :=
    S.E.hNF₂.1
  obtain ⟨hlt, hpw, -⟩ := stp_next_key S.E S.L S.hI S.hd
  obtain ⟨-, -, hcap, hlC'⟩ := stp_meas_step S.E S.L S.hI S.hd
  obtain ⟨hlabR, hinv⟩ := S.labels
  have hsome := stp_key_some S.hI S.hd
  obtain ⟨-, -, -, -, -, -, -, -, -, hkN4, -, -, -, r0, r1, r2, r3, -⟩ :=
    S.hI.2.2.2.2.2.2.2 hsome
  have elB : co.nreg lB = c.nreg lB := stp_co_keep S.hI (k := 2430) (by omega)
  have elC : co.nreg lC = c.nreg lC := stp_co_keep S.hI (k := 2431) (by omega)
  have elB' : c'.nreg lB = c.nreg lB := stp_iter_keep S.hI (k := 2430) (by omega)
  rw [elB, elC] at r0 r1 r2 r3
  obtain ⟨ls, hlen, hrec, hwords, hpre, hlast⟩ := S.L.log
  have l1 := S.L.lay1
  have l2 := S.L.lay2
  have l4 := S.L.lay4
  have hm : ∀ x, c.nreg lB ≤ x → x < c.nreg lB + 7 * c.nreg lC → c'.nmem x = c.nmem x :=
    fun x h1 h2 => stp_c'_mem S.L S.hI S.hd x (by omega) (by omega) (Or.inl h2)
  set r' : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL,
    c'.nreg (kL + 1), c'.nreg (kL + 2), c'.nreg (kL + 3)) with hr'
  refine ⟨ls ++ [r'], by simp [hlen, hlC'], ?_, ?_, ?_, List.getLast?_concat⟩
  · -- the records
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rw [elB']
    rcases Nat.lt_or_ge i ls.length with h | h
    · rw [List.getD_append _ _ _ _ h]
      obtain ⟨a0, a1, a2, a3, a4, a5, a6⟩ := hrec i h
      have hi' : i < c.nreg lC := hlen ▸ h
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hm _ (by omega) (by omega)]; exact a0
      · rw [hm _ (by omega) (by omega)]; exact a1
      · rw [hm _ (by omega) (by omega)]; exact a2
      · rw [hm _ (by omega) (by omega)]; exact a3
      · rw [hm _ (by omega) (by omega)]; exact a4
      · rw [hm _ (by omega) (by omega)]; exact a5
      · rw [hm _ (by omega) (by omega)]; exact a6
    · have hil : i = ls.length := by omega
      rw [List.getD_append_right _ _ _ _ h, show i - ls.length = 0 by omega, hil, hlen]
      simp only [List.getD_cons_zero]
      refine ⟨r0, r1, r2, ?_, ?_, ?_, ?_⟩
      · have := r3 0 (by norm_num); simpa using this
      · have := r3 1 (by norm_num)
        rwa [show c.nreg lB + 7 * c.nreg lC + 3 + 1 = c.nreg lB + 7 * c.nreg lC + 4 by ring] at this
      · have := r3 2 (by norm_num)
        rwa [show c.nreg lB + 7 * c.nreg lC + 3 + 2 = c.nreg lB + 7 * c.nreg lC + 5 by ring] at this
      · have := r3 3 (by norm_num)
        rwa [show c.nreg lB + 7 * c.nreg lC + 3 + 3 = c.nreg lB + 7 * c.nreg lC + 6 by ring] at this
  · -- the word facts
    intro r hr
    rcases List.mem_append.1 hr with h | h
    · exact hwords r h
    · rw [List.mem_singleton] at h
      subst h
      refine ⟨hpw, hkN4, fun h => ?_, fun h => hlabR 1 h, fun h => hlabR 2 h, fun h => hlabR 3 h⟩
      have := hlabR 0 h
      simpa using this
  · -- the log so far
    obtain ⟨hne, hall, hhead, hpwl, hcons, hlab⟩ := hpre
    set es := logOf J (Qof P) N₂ ls with hes
    set x' : ℕ × ℝ × Set (Set Point) := (c'.nreg kE,
      (chainModel J.whole).param (Qof P) ⟨c'.nreg kE, c'.nreg kH⟩, curLab P J N₂ c') with hx'
    have hmap : logOf J (Qof P) N₂ (ls ++ [r']) = es ++ [x'] := by
      simp [logOf, hes, hx', hr', curLab]
    rw [hmap]
    -- the last entry of the old log is the key
    set xc : ℕ × ℝ × Set (Set Point) := (c.nreg kE,
      (chainModel J.whole).param (Qof P) ⟨c.nreg kE, c.nreg kH⟩, curLab P J N₂ c) with hxc
    have hlastE : es.getLast? = some xc := by
      rw [hes, logOf, List.getLast?_map, hlast]
      simp [hxc, curLab]
    have hxcoff : oW J (xc.1 + xc.2.1) = keyOff P J c := rfl
    have hx'off : oW J (x'.1 + x'.2.1) = keyOff P J c' := rfl
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.1 hlastE
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hall x h
      · rw [List.mem_singleton] at h
        subst h
        exact ⟨hpw.1, hpw.2.1.1, hpw.2.1.2.1, by rw [hx'off]; linarith [S.L.keyL]⟩
    · intro x hx
      obtain ⟨a, es', hae⟩ := List.exists_cons_of_ne_nil hne
      rw [hae] at hhead
      rw [hae] at hx
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hhead a rfl
    · refine List.pairwise_append.2 ⟨hpwl, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      have := stp_le_last (f := fun x : ℕ × ℝ × Set (Set Point) => oW J (x.1 + x.2.1)) hpwl
        hlastE a ha
      rw [hx'off]
      rw [hxcoff] at this
      linarith
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_or_ge (i + 1) es.length with h | h
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ h]
        exact hcons i h
      · have hi' : i + 1 = es.length := by omega
        have hlen' : es.length = ys.length + 1 := by rw [hys]; simp
        have e1 : (es ++ [x']).getD i (0, 0, ∅) = xc := by
          rw [List.getD_append _ _ _ _ (by omega), hys,
            List.getD_append_right _ _ _ _ (by omega), show i - ys.length = 0 by omega]
          simp
        have e2 : (es ++ [x']).getD (i + 1) (0, 0, ∅) = x' := by
          rw [List.getD_append_right _ _ _ _ (by omega), show i + 1 - es.length = 0 by omega]
          simp
        rw [e1, e2, hxcoff, hx'off]
        exact no_cut_iter S.E S.L S.hI
    · intro x hx
      rcases List.mem_append.1 hx with h | h
      · exact hlab x h
      · rw [List.mem_singleton] at h
        subst h
        exact labIn_of_evInv hP hS₂.2.1 hS₂.1 hpw.1 hpw.2.1.1 hpw.2.1.2.1 hinv

end SCtx

end

end SweepEv

end Chazelle.Core
