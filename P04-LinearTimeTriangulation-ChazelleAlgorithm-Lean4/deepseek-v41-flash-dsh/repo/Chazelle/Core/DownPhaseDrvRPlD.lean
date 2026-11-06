module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvRPlC

/-!
# Down-phase driver (RAM side): the leaf planner, part 4 (`plS_exec`)

**`plS_exec`**: for the host `H` at the handle `r219000` and the chunk size `C = r219002 ≥ 1`,
`plS` writes the table of `hostLeaves n C 0 H` at the entry allocator `A₀` (handle `r219003`,
count `r219004`) and moves the allocator past it, in `15 K + 70 |H| + 20` steps.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs BuildRam

@[expose] public section

theorem hostLeaves_take_drop (n C : ℕ) (H : Host) (i : ℕ) :
    hostLeaves n C 0 H = hostLeaves n C 0 (H.take i) ++
      hostLeaves n C (Host.pts n (H.take i)).length (H.drop i) := by
  conv_lhs => rw [← List.take_append_drop i H]
  Ξ hostLeaves_append, Nat.zero_add

theorem hostLeaves_take_le (n C : ℕ) (H : Host) (i : ℕ) :
    (hostLeaves n C 0 (H.take i)).length ≤ (hostLeaves n C 0 H).length := by
  rw [hostLeaves_take_drop n C H i, List.length_append]; omega

theorem pts_take_le (n : ℕ) (H : Host) (i : ℕ) :
    (Host.pts n (H.take i)).length ≤ (Host.pts n H).length := by
  conv_rhs => rw [← List.take_append_drop i H]
  rw [DownMath.pts_append, List.length_append]; omega

/-- The loop invariant of the planner after `i` items. -/
structure PlI (W n C HB T len K : ℕ) (H : Host) (c₀ : Config) (i : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  kc : PlConst n C c
  r05 : c.nreg 219005 = i
  r06 : c.nreg 219006 = len
  r08 : c.nreg 219008 = HB + 1 + 3 * i
  r07 : c.nreg 219007 = (Host.pts n (H.take i)).length
  r16 : c.nreg 219016 = T + 3 * (hostLeaves n C 0 (H.take i)).length
  r04 : c.nreg 219004 = (hostLeaves n C 0 (H.take i)).length
  r03 : c.nreg 219003 = T
  rA : c.nreg ALLOC = T
  il : i ≤ len
  tab : ChordListAt c.nmem T (hostLeaves n C 0 (H.take i))
  low : ∀ a, a < T → c.nmem a = c₀.nmem a
  fr : FrameM Bpl c₀ c

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 4000000 in
/-- **The leaf planner.** -/
theorem plS_exec {C : ℕ} (hC : 1 ≤ C) (hn3 : 3 ≤ P.n) (c : Config) (hw : WordsBounded W c)
    {H : Host} {HB : ℕ} (h00 : c.nreg 219000 = HB) (h02 : c.nreg 219002 = C)
    (hH : HostAt c.nmem HB H) (hwf : HostWF P.n H)
    (hHB : HB + 3 * H.length + 1 ≤ c.nreg ALLOC)
    (hW1 : c.nreg ALLOC + 3 * (hostLeaves P.n C 0 H).length + 1 ≤ W)
    (hW2 : (Host.pts P.n H).length + 2 * P.n + 1 ≤ W) :
    ∃ c' k, Exec P W plS c c' k ∧
      k ≤ 15 * (hostLeaves P.n C 0 H).length + 70 * H.length + 20 ∧ WordsBounded W c' ∧
      c'.nreg 219003 = c.nreg ALLOC ∧ c'.nreg 219004 = (hostLeaves P.n C 0 H).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (hostLeaves P.n C 0 H).length ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (hostLeaves P.n C 0 H) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ PlConst P.n C c' ∧
      (∀ r, Bpl r = false → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  set T := c.nreg ALLOC with hT
  set K := (hostLeaves P.n C 0 H).length with hK
  set len := H.length with hlen
  have hTW : T ≤ W := by omega
  -- initialization
  obtain ⟨c₁, k₁, e₁, hk₁, w₁, x01, x02, x17, x18, x19, x20, x26, x05, x06, x08, x07, x16, x04,
      x03, xA, xm⟩ : ∃ c₁ k₁, Exec P W plInit c c₁ k₁ ∧ k₁ = 13 ∧ WordsBounded W c₁ ∧
      c₁.nreg 219001 = P.n ∧ c₁.nreg 219002 = C ∧ c₁.nreg 219017 = 0 ∧ c₁.nreg 219018 = 1 ∧
      c₁.nreg 219019 = 2 ∧ c₁.nreg 219020 = 3 ∧ c₁.nreg 219026 = P.n - 1 ∧
      c₁.nreg 219005 = 0 ∧ c₁.nreg 219006 = len ∧ c₁.nreg 219008 = HB + 1 ∧
      c₁.nreg 219007 = 0 ∧ c₁.nreg 219016 = T ∧ c₁.nreg 219004 = 0 ∧ c₁.nreg 219003 = T ∧
      c₁.nreg ALLOC = T ∧ c₁.nmem = c.nmem := by
    have hl : c.nmem HB = len := hH.1
    have hT9 : c.nreg 9999 = T := rfl
    unfold plInit
    exec_block
    all_goals try (config_simp; (try simp only [h00, hl, h02, hT9]); omega)
    refine ⟨rfl, ‹_›, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h00, hl, h02, hT9])
  have fr₁ : FrameM Bpl c c₁ := exec_frameM e₁ (by decide)
  have h0 : hostLeaves P.n C 0 (H.take 0) = [] := by simp [hostLeaves]
  have h0p : (Host.pts P.n (H.take 0)).length = 0 := by simp [Host.pts]
  have I₁ : PlI W P.n C HB T len K H c 0 c₁ :=
    { wb := w₁, kc := ⟨x01, x02, x17, x18, x19, x20, x26⟩, r05 := x05, r06 := x06,
      r08 := by rw [x08], r07 := by rw [x07, h0p], r16 := by rw [x16, h0]; simp,
      r04 := by rw [x04, h0]; simp, r03 := x03, rA := xA, il := Nat.zero_le _,
      tab := fun i hi => by rw [h0] at hi; simp at hi, low := fun a _ => by rw [xm],
      fr := fr₁ }
  -- the item loop
  have hstep : ∀ c₂, (∃ i, PlI W P.n C HB T len K H c i c₂) → c₂.nreg 219005 < c₂.nreg 219006 →
      ∃ c₃ k₃, Exec P W plItem c₂ c₃ k₃ ∧ (∃ i, PlI W P.n C HB T len K H c i c₃) ∧
        (70 * (len - c₃.nreg 219005) + 15 * (K - c₃.nreg 219004)) + k₃ + 2 ≤
          70 * (len - c₂.nreg 219005) + 15 * (K - c₂.nreg 219004) := by
    rintro c₂ ⟨i, I⟩ hlt
    rw [I.r05, I.r06] at hlt
    obtain ⟨it, hitd⟩ : ∃ it, it = H.getD i (.run 0 0) := ⟨_, rfl⟩
    have hmem : it ∈ H := by
      rw [hitd, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem hlt
    have hwfi := hwf it hmem
    have hHi := hH.2 i hlt
    rw [← hitd] at hHi
    have haddr : HB + 1 + 3 * i + 3 ≤ T := by omega
    have l0 := I.low (HB + 1 + 3 * i) (by omega)
    have l1 := I.low (HB + 1 + 3 * i + 1) (by omega)
    have l2 := I.low (HB + 1 + 3 * i + 2) (by omega)
    have hit : ItemWords c₂.nmem (HB + 1 + 3 * i) it := by
      cases it with
      | run a ℓ =>
        obtain ⟨x1, x2, x3⟩ := hHi
        exact ⟨by rw [l0]; exact x1,
          by rw [l1, show HB + 1 + 3 * i + 1 = HB + 2 + 3 * i by omega]; exact x2,
          by rw [l2, show HB + 1 + 3 * i + 2 = HB + 3 + 3 * i by omega]; exact x3⟩
      | pt x =>
        cases x with
        | vtx j => show c₂.nmem _ = 1; rw [l0]; exact hHi.1
        | onEdge e h => show c₂.nmem _ = 2; rw [l0]; exact hHi.1
    have hwfi' : ItemOK P.n it := by
      cases it with
      | run a ℓ => exact hwfi
      | pt x => trivial
    have hsucc := hostLeaves_take_succ P.n C H hlt
    rw [← hitd] at hsucc
    have hpsucc := pts_take_succ P.n H hlt
    rw [← hitd] at hpsucc
    have hle1 := hostLeaves_take_le P.n C H (i + 1)
    rw [hsucc, List.length_append] at hle1
    have hpt := pts_take_le P.n H i
    obtain ⟨c₃, k₃, e₃, hk₃, b05, b08, b07, b16, b04, bL, bm, bf⟩ := plItem_exec (P := P) hC
      (by omega) c₂ I.wb I.kc (it := it) I.r05 I.r08 I.r07 I.r16 I.r04 hit hwfi' (by omega)
      (by omega) (by omega) (by omega) (by omega)
    have gI : ∀ r, Bitem r = false → c₃.nreg r = c₂.nreg r := bf.1
    refine ⟨c₃, k₃, e₃, ⟨i + 1, ?_⟩, ?_⟩
    · refine ⟨e₃.wb_right, I.kc.keep fun r hr => gI r (by
          simp only [Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega),
        b05, by rw [gI _ (by decide), I.r06], by rw [b08]; ring, ?_, ?_, ?_,
        by rw [gI _ (by decide), I.r03], by rw [gI _ (by decide), I.rA], by omega, ?_, ?_, ?_⟩
      · rw [b07, hpsucc]
      · rw [b16, hsucc, List.length_append]; ring
      · rw [b04, hsucc, List.length_append]
      · rw [hsucc]
        exact clAt_append (clAt_congr I.tab fun x _ hx => bm x (Or.inl hx)) bL
      · intro a ha
        rw [bm a (Or.inl (by omega)), I.low a ha]
      · exact I.fr.trans ⟨fun r hr => gI r (by
            simp only [Bpl, Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
            omega), fun r hr => bf.2.1 r (by
            simp only [Bpl, Bitem, Brun, Bch, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢
            omega), bf.2.2.1, bf.2.2.2⟩
    · rw [b05, b04, I.r04, I.r05]
      omega
  obtain ⟨c₂, k₂, e₂, ⟨i, I₂⟩, hend, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 219005) (b := 219006) (body := plItem)
    (fun c₂ => ∃ i, PlI W P.n C HB T len K H c i c₂)
    (fun c₂ => 70 * (len - c₂.nreg 219005) + 15 * (K - c₂.nreg 219004))
    (fun c₂ ⟨i, I⟩ => I.wb) hstep ⟨0, I₁⟩
  have hi : i = len := by rw [I₂.r05, I₂.r06] at hend; have := I₂.il; omega
  subst hi
  have htk : H.take len = H := by rw [hlen]; exact List.take_length
  have tab₂ := I₂.tab
  have r16₂ := I₂.r16
  have r04₂ := I₂.r04
  rw [htk] at tab₂ r16₂ r04₂
  have e₃ := Exec.copyN (P := P) e₂.wb_right 9999 219016
  have ex : Exec P W plS c _ (k₁ + (k₂ + 1)) := .seq e₁ (.seq e₂ e₃)
  have h0 : (hostLeaves P.n C 0 (H.take 0)).length = 0 := by simp [hostLeaves]
  refine ⟨_, k₁ + (k₂ + 1), ex, ?_, e₃.wb_right, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [I₁.r05, I₁.r04, h0] at hk₂
    omega
  · simp only; rw [Machine.upd_other _ _ _ (by decide)]; exact I₂.r03
  · simp only; rw [Machine.upd_other _ _ _ (by decide)]; exact r04₂
  · show upd c₂.nreg 9999 (c₂.nreg 219016) 9999 = T + 3 * K
    rw [Machine.upd_same, r16₂]
  · exact tab₂
  · exact I₂.low
  · exact I₂.kc.keep fun r hr => by
      simp only; rw [Machine.upd_other _ _ _ (by omega)]
  · intro r hr
    simp only
    rw [Machine.upd_other _ _ _ (by
      intro h; subst h; simp [Bpl] at hr)]
    exact I₂.fr.1 r hr
  · funext r; exact exec_frameM2 ex wrM2_plS r rfl
  · exact I₂.fr.2.2.1
  · exact I₂.fr.2.2.2

end exec

end

end DrvR

end Chazelle.Core
