module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.DownPhaseBaseLoop1

/-!
# Down phase, A1 (RAM, part 3): the event pass

`dLoop2` runs over the `2K` event codes of `E` (at `SE`); code `c` with table word
`v = X[c] = tbl c > 0` is kept and `v - 1 = newCode c` is appended at `SE'`.  After `t` events the
new list holds `dropE li n L (E.take t)` (`mem2`, invariant `Inv2`).
-/

namespace Chazelle.Core

namespace DownBase

open Machine Machine.Stmt Programs

@[expose] public section

/-- One more event of the renumbered list. -/
theorem dropE_take_succ {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {t : ℕ}
    (ht : t < E.length) :
    dropE li n L (E.take (t + 1)) = dropE li n L (E.take t) ++
      if keptC li n L (E.getD t 0) then [newCode li n L (E.getD t 0)] else [] := by
  have he : E.getD t 0 = E[t] := by
    simp_all
  unfold dropE
  rw [List.take_add_one, List.getElem?_eq_getElem ht, Option.toList_some, List.filter_append,
    List.map_append, he]
  congr 1
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp

theorem dropE_take_length_le {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} (t : ℕ) :
    (dropE li n L (E.take t)).length ≤ t := by
  unfold dropE
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le _ _)

/-- The memory after `t` events. -/
def mem2 (m₁ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) (SE' t a : ℕ) :
    ℕ :=
  if SE' ≤ a ∧ a < SE' + (dropE li n L (E.take t)).length then
    (dropE li n L (E.take t)).getD (a - SE') 0
  else m₁ a

section

variable {m₁ m : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {SE' t : ℕ} (hm : ∀ a, m a = mem2 m₁ li n L E SE' t a) (ht : t < E.length)
include hm ht

theorem mem2_keep
    (hk : keptC li n L (E.getD t 0) = true) (a : ℕ) :
    (if a = SE' + (dropE li n L (E.take t)).length then newCode li n L (E.getD t 0) else m a) =
      mem2 m₁ li n L E SE' (t + 1) a := by
  rw [hm a]
  unfold mem2
  rw [dropE_take_succ ht, ite_eq_left hk, List.length_append, List.length_singleton]
  set l := dropE li n L (E.take t)
  by_cases h1 : a = SE' + l.length
  · simp_all
  · rw [ite_eq_right h1]
    by_cases h2 : SE' ≤ a ∧ a < SE' + l.length
    · ram_simp [ite_eq_left h2, ite_eq_left, List.getD_append]
    ram_simp [ite_eq_right h2, ite_eq_right]

theorem mem2_skip
    (hk : keptC li n L (E.getD t 0) = false) (a : ℕ) : m a = mem2 m₁ li n L E SE' (t + 1) a := by
  rw [hm a]
  unfold mem2
  rw [dropE_take_succ ht, hk]
  simp

end

/-- The invariant of the event pass. -/
structure Inv2 (m₁ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
    (SE X SE' : ℕ) (c₁ d : Config) : Prop where
  t_le : d.nreg 200130 ≤ E.length
  r136 : d.nreg 200136 = E.length
  r131 : d.nreg 200131 = SE + d.nreg 200130
  r134 : d.nreg 200134 = SE' + (dropE li n L (E.take (d.nreg 200130))).length
  r121 : d.nreg 200121 = X
  r100 : d.nreg 200100 = 1
  r101 : d.nreg 200101 = 0
  fr : ∀ r, (r < 200130 ∨ 200135 < r) → d.nreg r = c₁.nreg r
  rr : d.rreg = c₁.rreg
  rm : d.rmem = c₁.rmem
  out : d.output = c₁.output
  mem : ∀ a, d.nmem a = mem2 m₁ li n L E SE' (d.nreg 200130) a

section exec

variable {P : Polygon} {W : ℕ}

section

variable {m₁ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}
    {SE X SE' : ℕ} (hE : ∀ t, t < E.length → m₁ (SE + t) = E.getD t 0)
    (hSE : SE + E.length ≤ SE') (hX : ∀ c, c < E.length → m₁ (X + c) = tbl li n L c)
    (hXS : X + E.length ≤ SE') (hEl : E.length = 2 * L.length)
    (hperm : E.Perm (List.range (2 * L.length))) (hW : SE' + E.length + 1 ≤ W)
    {c₁ d : Config} (hw : WordsBounded W d) (hI : Inv2 m₁ li n L E SE X SE' c₁ d)
include hE hSE hX hXS hEl hperm hW hw hI

set_option maxHeartbeats 4000000 in
/-- **One event.** -/
theorem dBody2_exec
    (ht : d.nreg 200130 < d.nreg 200136) :
    ∃ d' k, Exec P W dBody2 d d' k ∧ WordsBounded W d' ∧ Inv2 m₁ li n L E SE X SE' c₁ d' ∧
      d'.nreg 200130 = d.nreg 200130 + 1 ∧ 7 ≤ k ∧ k ≤ 11 := by
  rw [hI.r136] at ht
  set t := d.nreg 200130 with htdef
  set l := dropE li n L (E.take t) with hl
  have hll : l.length ≤ t := dropE_take_length_le t
  set c := E.getD t 0 with hc
  have hcE : c ∈ E := by
    simp_all
  have hc2 : c < E.length := by rw [hEl]; exact mem_lt hperm hcE
  have mSE : d.nmem (SE + t) = c := by
    frame_finish [hI.mem, mem2, ite_eq_right, hE t ht]
  have mX : d.nmem (X + c) = tbl li n L c := by
    rw [hI.mem]; frame_finish [mem2, ite_eq_right, hX c hc2]
  -- the load block
  obtain ⟨d₁, k₁, e₁, hk₁, v32, v31, v35, v33, r₁, m₁', rr₁, rm₁, o₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.loadN 200132 200131, .addN 200131 200131 200100, .addN 200135 200121 200132,
        .loadN 200133 200135]) d d₁ k₁ ∧ k₁ = 4 ∧ d₁.nreg 200132 = c ∧
      d₁.nreg 200131 = SE + t + 1 ∧ d₁.nreg 200135 = X + c ∧ d₁.nreg 200133 = tbl li n L c ∧
      (∀ r, r ≠ 200131 → r ≠ 200132 → r ≠ 200133 → r ≠ 200135 → d₁.nreg r = d.nreg r) ∧
      d₁.nmem = d.nmem ∧ d₁.rreg = d.rreg ∧ d₁.rmem = d.rmem ∧ d₁.output = d.output := by
    have h131 := hI.r131
    have h100 := hI.r100
    have h121 := hI.r121
    rw [← htdef] at h131
    exec_block
    all_goals try (simp (disch := omega) only [Machine.upd_same,
      Machine.upd_other, h131, h100, h121, mSE]; omega)
    simp_all <;> omega
  have g1 : ∀ r, (r < 200130 ∨ 200135 < r ∨ r = 200130 ∨ r = 200134) →
      d₁.nreg r = d.nreg r := fun r hr => (ram_app% (r₁ r ?_ ?_ ?_ ?_))
  -- the branch
  obtain ⟨d₂, k₂, e₂, hk₂, hk₂', g2, n134, mem2', rr₂, rm₂, o₂⟩ : ∃ d₂ k₂,
      Exec P W (.ifLtN 200101 200133 (block [.subN 200133 200133 200100, .storeN 200134 200133,
        .addN 200134 200134 200100]) .skip) d₁ d₂ k₂ ∧ 2 ≤ k₂ ∧ k₂ ≤ 4 ∧
      (∀ r, r ≠ 200133 → r ≠ 200134 → d₂.nreg r = d₁.nreg r) ∧
      d₂.nreg 200134 = SE' + (dropE li n L (E.take (t + 1))).length ∧
      (∀ a, d₂.nmem a = mem2 m₁ li n L E SE' (t + 1) a) ∧
      d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
    have h101 : d₁.nreg 200101 = 0 := by ram_rw [g1, hI.r101]
    have h134 : d₁.nreg 200134 = SE' + l.length := by ram_rw [g1, hI.r134]
    have h100 : d₁.nreg 200100 = 1 := by ram_rw [g1, hI.r100]
    have hsucc := dropE_take_succ (li := li) (n := n) (L := L) ht
    rw [← hc, ← hl] at hsucc
    cases hk : keptC li n L c
    · have hv : d₁.nreg 200133 = 0 := by rw [v33, tbl, hk]; rfl
      have hn : ¬ d₁.nreg 200101 < d₁.nreg 200133 := by rw [h101, hv]; omega
      rw [hk] at hsucc
      simp only [Bool.false_eq_true, ite_false, List.append_nil] at hsucc
      refine ⟨d₁, _, .ifLtN_false hn (.skip e₁.wb_right), le_rfl, by omega, fun _ _ _ => rfl,
        by rw [hsucc, h134], fun a => ?_, rfl, rfl, rfl⟩
      rw [m₁']
      exact mem2_skip hI.mem ht hk a
    · have hv : d₁.nreg 200133 = newCode li n L c + 1 := by rw [v33, tbl, hk]; rfl
      have hp : d₁.nreg 200101 < d₁.nreg 200133 := by rw [h101, hv]; omega
      rw [hk] at hsucc
      simp only [ite_true] at hsucc
      obtain ⟨d₂, k₂, e₂, hk₂, w134, r₂, mm₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂, Exec P W
          (block [.subN 200133 200133 200100, .storeN 200134 200133,
            .addN 200134 200134 200100]) d₁ d₂ k₂ ∧ k₂ = 3 ∧
          d₂.nreg 200134 = SE' + l.length + 1 ∧
          (∀ r, r ≠ 200133 → r ≠ 200134 → d₂.nreg r = d₁.nreg r) ∧
          (∀ a, d₂.nmem a = if a = SE' + l.length then newCode li n L c else d₁.nmem a) ∧
          d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
        have hw₁ := e₁.wb_right
        exec_block
        all_goals try (simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other, h134, h100, hv]; omega)
        refine ⟨rfl, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl, rfl, rfl⟩
        all_goals simp (disch := omega) only [Machine.upd_same,
          Machine.upd_other, h134, h100, hv, Machine.upd_apply]
        simp
      refine ⟨d₂, _, .ifLtN_true hp e₂, by omega, by omega, r₂,
        by rw [w134, hsucc, List.length_append, List.length_singleton]; ring, fun a => ?_,
        rr₂, rm₂, o₂⟩
      rw [mm₂, m₁']
      exact mem2_keep hI.mem ht hk a
  -- the increment
  have h130 : d₂.nreg 200130 = t := by frame_finish
  have h100 : d₂.nreg 200100 = 1 := by
    frame_finish
  have e₃ := Exec.addN (P := P) e₂.wb_right 200130 200130 200100 (by rw [h130, h100]; omega)
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg 200130 (d₂.nreg 200130 + d₂.nreg 200100) }
    with hd₃
  have g3 : ∀ r, r ≠ 200130 → d₃.nreg r = d₂.nreg r := fun r hr => by rw [hd₃]; simp [hr]
  have v3 : d₃.nreg 200130 = t + 1 := by rw [hd₃]; simp [h130, h100]
  have g : ∀ r, (r < 200130 ∨ 200135 < r) → d₃.nreg r = d.nreg r := fun r hr => by
    ram_rw [g3 r, g2 r, g1 r]
  refine ⟨d₃, _, .seq e₁ (.seq e₂ e₃), e₃.wb_right, ?_, v3, by omega, by omega⟩
  refine ⟨by rw [v3]; omega, by ram_rw [g, hI.r136], ?_, ?_,
    by ram_rw [g, hI.r121], by assumption,
    by ram_rw [g, hI.r101], fun r hr => by rw [g r hr, hI.fr r hr], ?_, ?_, ?_,
    fun a => ?_⟩
  · frame_finish
  · ram_rw [v3, g3, n134]
  · ram_post [rr₂, rr₁, hI.rr]
  · ram_post [rm₂, rm₁, hI.rm]
  · show d₂.output = c₁.output; rw [o₂, o₁, hI.out]
  · show d₂.nmem a = _; rw [v3, mem2']

/-- **The event pass.** -/
theorem dLoop2_exec
    (h0 : d.nreg 200130 = 0) :
    ∃ d' k, Exec P W dLoop2 d d' k ∧ WordsBounded W d' ∧ Inv2 m₁ li n L E SE X SE' c₁ d' ∧
      d'.nreg 200130 = E.length ∧ 7 * E.length ≤ k ∧ k ≤ 13 * E.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := Exec.whileLtN_growth (P := P) (W := W)
    (a := 200130) (b := 200136) (body := dBody2)
    (fun d => WordsBounded W d ∧ Inv2 m₁ li n L E SE X SE' c₁ d)
    (fun d => 13 * (E.length - d.nreg 200130)) (fun d => 7 * d.nreg 200130) (fun d hd => hd.1)
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ :=
        dBody2_exec hE hSE hX hXS hEl hperm hW hwd hId ht
      have := hId.r136
      refine ⟨d', k, e, ⟨hw', hI'⟩, ?_, ?_⟩
      · rw [hi']; rw [this] at ht; omega
      · rw [hi']; omega)
    ⟨hw, hI⟩
  have hi := hI'.t_le
  rw [hI'.r136] at htest
  have hend : d'.nreg 200130 = E.length := by omega
  refine ⟨d', k, e, hw', hI', hend, ?_, ?_⟩
  · rw [h0, hend] at hψ; omega
  · rw [h0] at hk; omega

end

end exec

end

end DownBase

end Chazelle.Core
