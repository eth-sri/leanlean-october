module

public import Chazelle.Core.Lemma41Ram9

/-!
# WP-J, part 18: the level array of the next level

`rbS`: walking the back links from the last cell, write the entries `[descriptor, NF]` of the
next level from the end of a fresh array at the allocator (two words per node, the allocator
bumped by two per node).  `rbS_exec`, and `levelAt_of_cells`: the new array holds the level.

Registers: `160094` the new base, `160095` the write pointer, `160096` the cell, `160097` the
counter, `160098`/`160099` scratch; `160064` the number of cells, `160063` the last cell.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle.Merge Finset

@[expose] public section

/-- The start of the rebuild. -/
def rbInit : Stmt := block [.copyN 160094 9999, .addN 160095 9999 160064,
  .addN 160095 160095 160064, .copyN 160096 160063, .constN 160097 0]

/-- One entry, from the end. -/
def rbBody : Stmt := block [.subN 160095 160095 160080, .loadN 160098 160096,
  .storeN 160095 160098, .addN 160099 160096 160024, .loadN 160098 160099,
  .addN 160099 160095 160024, .storeN 160099 160098, .addN 160099 160096 160080,
  .loadN 160096 160099, .addN 160097 160097 160024, .addN 9999 9999 160080]

/-- **The rebuild of the level array.** -/
def rbS : Stmt := .seq rbInit (.whileLtN 160097 160064 rbBody)

/-- The registers written by `rbS` (besides the allocator). -/
def RbRG (r : ℕ) : Prop := 160094 ≤ r ∧ r ≤ 160099

/-- The registers written by `rbBody` (besides the allocator). -/
def RbBRG (r : ℕ) : Prop := 160095 ≤ r ∧ r ≤ 160099

section proofs

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
theorem rbBody_exec {c : Config} (hw : WordsBounded W c) {p0 e0 t Al : ℕ}
    (h95 : c.nreg 160095 = p0) (h96 : c.nreg 160096 = e0) (h97 : c.nreg 160097 = t)
    (hA : c.nreg ALLOC = Al) (h24 : c.nreg 160024 = 1) (h80 : c.nreg 160080 = 2)
    (hp : 2 ≤ p0) (he : e0 + 3 ≤ p0 - 2) (hWp : p0 ≤ W) (hWt : t + 1 ≤ W) (hWA : Al + 2 ≤ W) :
    ∃ c' k, Exec P W rbBody c c' k ∧ k = 11 ∧ WordsBounded W c' ∧
      c'.nreg 160095 = p0 - 2 ∧ c'.nreg 160096 = c.nmem (e0 + 2) ∧ c'.nreg 160097 = t + 1 ∧
      c'.nreg ALLOC = Al + 2 ∧ c'.nmem (p0 - 2) = c.nmem e0 ∧
      c'.nmem (p0 - 2 + 1) = c.nmem (e0 + 1) ∧
      (∀ a, a ≠ p0 - 2 → a ≠ p0 - 2 + 1 → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RbBRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA ⊢
  unfold rbBody
  exec_block
  all_goals try (config_simp; (try simp only [h95, h96, h97, hA, h24, h80]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 => ?_, fun r h1 h2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h95, h80]
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · config_simp; simp only [h97, h24]
  · config_simp; simp only [hA, h80]
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; split_ifs <;> omega
  · config_simp; simp only [h95, h96, h80, h24, Machine.upd_apply]; split_ifs <;> first | omega
  · unfold RbBRG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

set_option maxHeartbeats 8000000 in
theorem rbInit_exec {c : Config} (hw : WordsBounded W c) {B J : ℕ}
    (hA : c.nreg ALLOC = B) (h64 : c.nreg 160064 = J) (hW : B + 2 * J ≤ W) :
    ∃ c' k, Exec P W rbInit c c' k ∧ k = 5 ∧ WordsBounded W c' ∧
      c'.nreg 160094 = B ∧ c'.nreg 160095 = B + 2 * J ∧ c'.nreg 160096 = c.nreg 160063 ∧
      c'.nreg 160097 = 0 ∧ (∀ r, ¬ RbRG r → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  rw [hAl] at hA
  unfold rbInit
  exec_block
  all_goals try (config_simp; (try simp only [hA, h64]); omega)
  refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, fun r h1 => ?_, rfl, rfl, rfl, rfl⟩
  · config_simp; simp only [hA]
  · config_simp; simp only [hA, h64]; ring
  · config_simp
  · config_simp
  · unfold RbRG at h1
    simp only
    repeat (rw [Machine.upd_other _ _ _ (by omega)])

/-- The invariant of the rebuild after `t` entries. -/
def RbInv (W : ℕ) (c0 : Config) (B J : ℕ) (e : ℕ → ℕ) (t : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160097 = t ∧ c.nreg 160064 = J ∧ c.nreg 160095 = B + 2 * (J - t) ∧
    c.nreg ALLOC = B + 2 * t ∧ (t < J → c.nreg 160096 = e (J - 1 - t)) ∧
    (∀ k, J - t ≤ k → k < J → c.nmem (B + 2 * k) = c0.nmem (e k) ∧
      c.nmem (B + 2 * k + 1) = c0.nmem (e k + 1)) ∧
    (∀ a, (a < B + 2 * (J - t) ∨ B + 2 * J ≤ a) → c.nmem a = c0.nmem a) ∧
    (∀ r, ¬ RbBRG r → r ≠ ALLOC → c.nreg r = c0.nreg r) ∧
    c.rreg = c0.rreg ∧ c.rmem = c0.rmem ∧ c.output = c0.output

set_option maxHeartbeats 16000000 in
/-- **The rebuild.** -/
theorem rbS_exec {c : Config} (hw : WordsBounded W c) {B J : ℕ} {e : ℕ → ℕ}
    (hA : c.nreg ALLOC = B) (h64 : c.nreg 160064 = J) (h24 : c.nreg 160024 = 1)
    (h80 : c.nreg 160080 = 2) (h63 : 1 ≤ J → c.nreg 160063 = e (J - 1))
    (hcell : ∀ q, q < J → e q + 3 ≤ B) (hlink : ∀ q, q < J → 1 ≤ q → c.nmem (e q + 2) = e (q - 1))
    (hW : B + 2 * J + 1 ≤ W) :
    ∃ c' k, Exec P W rbS c c' k ∧ k ≤ 13 * J + 7 ∧ WordsBounded W c' ∧
      c'.nreg ALLOC = B + 2 * J ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧ c'.nreg 160094 = B ∧
      (∀ k, k < J → c'.nmem (B + 2 * k) = c.nmem (e k) ∧
        c'.nmem (B + 2 * k + 1) = c.nmem (e k + 1)) ∧
      (∀ a, (a < B ∨ B + 2 * J ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ RbRG r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAl : ALLOC = 9999 := rfl
  obtain ⟨c1, k1, e1, hk1, hw1, i94, i95, i96, i97, fr1, hm1, hrr1, hrm1, ho1⟩ :=
    rbInit_exec (P := P) hw hA h64 (by omega)
  have r1 : ∀ r, ¬ RbRG r → c1.nreg r = c.nreg r := fr1
  obtain ⟨c', k, e', ⟨t, ⟨hw', h97', h64', h95', hA', h96', hent, hout, fr', hrr', hrm', ho'⟩, htJ⟩,
      htest, hk, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := 160097) (b := 160064) (body := rbBody)
      (fun c => ∃ t, RbInv W c1 B J e t c ∧ t ≤ J) (fun c => 13 * (J - c.nreg 160097))
      (fun c => c.nreg ALLOC) (fun c ⟨t, h, _⟩ => h.1)
      (fun c2 ⟨t, ⟨hw2, h97, h64c, h95, hA2, h96, hent, hout, fr2, hrr2, hrm2, ho2⟩, htJ⟩ htest => by
        rw [h97, h64c] at htest
        have r24 : c2.nreg 160024 = 1 := by
          rw [fr2 _ (by unfold RbBRG; omega) (by rw [hAl]; omega), r1 _ (by unfold RbRG; omega)]
          exact h24
        have r80 : c2.nreg 160080 = 2 := by
          rw [fr2 _ (by unfold RbBRG; omega) (by rw [hAl]; omega), r1 _ (by unfold RbRG; omega)]
          exact h80
        set kk := J - 1 - t
        have hek := hcell kk (by omega)
        obtain ⟨c3, k3, e3, hk3, hw3, q95, q96, q97, qA, qm0, qm1, qm, fr3, hrr3, hrm3, ho3⟩ :=
          rbBody_exec (P := P) hw2 h95 (h96 htest) h97 hA2 r24 r80 (by omega) (by omega)
            (by omega) (by omega) (by omega)
        have q64 : c3.nreg 160064 = J := by
          rw [fr3 _ (by unfold RbBRG; omega) (by rw [hAl]; omega)]; exact h64c
        refine ⟨c3, k3, e3, ⟨t + 1, ⟨hw3, q97, q64, by rw [q95]; omega, by rw [qA]; ring,
          fun ht1 => ?_, fun k a1 a2 => ?_, fun a ha => ?_, fun r h1 h2 => ?_,
          by rw [hrr3, hrr2], by rw [hrm3, hrm2], by rw [ho3, ho2]⟩, by omega⟩, ?_, by omega⟩
        · rw [q96, hout _ (Or.inl (by omega)), hm1, hlink kk (by omega) (by omega)]
          all_goals (congr 1; try omega)
        · rcases Nat.lt_or_ge k (J - t) with hk | hk
          · have hkq : k = kk := by omega
            subst hkq
            refine ⟨?_, ?_⟩
            · rw [show B + 2 * (J - 1 - t) = B + 2 * (J - t) - 2 by omega, qm0,
                hout _ (Or.inl (by omega)), hm1]
            · rw [show B + 2 * (J - 1 - t) + 1 = B + 2 * (J - t) - 2 + 1 by omega, qm1,
                hout _ (Or.inl (by omega)), hm1]
          · obtain ⟨b1, b2⟩ := hent k hk a2
            rw [qm _ (by omega) (by omega), qm _ (by omega) (by omega)]
            exact ⟨b1, b2⟩
        · rw [qm _ (by omega) (by omega)]; exact hout a (by omega)
        · rw [fr3 r h1 h2]; exact fr2 r h1 h2
        · rw [q97, h97]; omega)
      ⟨0, ⟨hw1, i97, by rwa [r1 _ (by unfold RbRG; omega)], by rw [i95]; simp,
        by rw [r1 _ (by unfold RbRG; rw [hAl]; omega), hA]; simp,
        fun h => by rw [i96, h63 (by omega)]; congr 1, fun k a1 a2 => by omega,
        fun a _ => rfl, fun r _ _ => rfl, rfl, rfl, rfl⟩, Nat.zero_le _⟩
  have htJ' : t = J := by rw [h97', h64'] at htest; omega
  have hk' : k ≤ 13 * J + 2 := by
    have := hk; simp only [i97, Nat.sub_zero] at this; exact this
  have hA1 : c1.nreg ALLOC = B := by rw [r1 _ (by unfold RbRG; rw [hAl]; omega)]; exact hA
  refine ⟨c', k1 + k, .seq e1 e', by omega, hw', by rw [hA', htJ'], by omega,
    by rw [fr' _ (by unfold RbBRG; omega) (by rw [hAl]; omega)]; exact i94,
    fun k hk => ?_, fun a ha => ?_, fun r h1 h2 => ?_, by rw [hrr', hrr1], by rw [hrm', hrm1],
    by rw [ho', ho1]⟩
  · rw [← hm1]; exact hent k (by omega) hk
  · rw [hout a (by omega), hm1]
  · rw [fr' r (by unfold RbBRG; unfold RbRG at h1; omega) h2]; exact r1 r h1

end proofs

/-- **The new array holds the next level.** -/
theorem levelAt_of_cells {P : Polygon} {m m' : ℕ → ℕ} {B hp : ℕ} {ns : List Shp} {e : ℕ → ℕ}
    (hc : CellSt P m B hp ns e)
    (hent : ∀ k, k < ns.length → m' (B + 2 * k) = m (e k) ∧ m' (B + 2 * k + 1) = m (e k + 1))
    (hout : ∀ a, a < B → m' a = m a) : LevelAt P m' (B + 2 * ns.length) B hp ns := by
  intro k hk
  obtain ⟨-, -, C, h1, h2, h3⟩ := hc k hk
  refine ⟨C, h1, h2, ?_⟩
  rw [(hent k hk).1, (hent k hk).2]
  exact (h3.agree hout).mono (by omega)

end

end Chazelle.Core.L41
