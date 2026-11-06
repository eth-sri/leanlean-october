module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Ram2

/-!
# WP-J, part 8: the cover loop, executed

`coverS_exec`: from `x = a < b`, the records of `cover λ b a` are written at `R₀`, six words each,
with `160014` their number and `160010 = b` at the end; the tables are read below `R₀`.
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs

@[expose] public section

section proofs

variable {P : Polygon} {W : ℕ}

/-- The fixed registers of the cover loop. -/
structure CovRegs (c : Config) (lam b D PW T hp : ℕ) : Prop where
  r11 : c.nreg 160011 = b
  r26 : c.nreg 160026 = lam
  r24 : c.nreg 160024 = 1
  r20 : c.nreg 160020 = D
  r21 : c.nreg 160021 = PW
  r22 : c.nreg 160022 = T
  r27 : c.nreg 160027 = hp

theorem CovRegs.frame {c c' : Config} {lam b D PW T hp : ℕ} (h : CovRegs c lam b D PW T hp)
    (hr : ∀ r, ¬ CovRG r → c'.nreg r = c.nreg r) : CovRegs c' lam b D PW T hp := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [hr _ (by unfold CovRG AscRG; omega)]; assumption)

/-- The table facts read by the cover loop (in the memory `m0`, below `R₀`). -/
structure CovTab (m0 : ℕ → ℕ) (lam b D PW T R0 W : ℕ) : Prop where
  half : ∀ y, y ≤ b → m0 (D + y) = y / 2
  pow : ∀ i, i ≤ lam → m0 (PW + i) = 2 ^ i
  hD : D + b < R0
  hP : PW + lam < R0
  hT : T + lam ≤ R0
  ent : ∀ g, g ≤ lam - 1 → ∀ i, (i + 1) * 2 ^ g ≤ b →
    m0 (T + g) + 3 * i + 1 < R0 ∧ m0 (m0 (T + g) + 3 * i) + 4 < R0
  wb : b + 2 ^ lam ≤ W
  wR : R0 + 12 * lam + 6 ≤ W


/-- **One piece of the cover.** -/
theorem coverBody_exec {c : Config} (hw : WordsBounded W c) {lam b D PW T hp R0 x cnt : ℕ}
    {m0 : ℕ → ℕ} (hR : CovRegs c lam b D PW T hp) (hT : CovTab m0 lam b D PW T R0 W)
    (hl : 1 ≤ lam) (h10 : c.nreg 160010 = x) (hx : x < b) (h14 : c.nreg 160014 = cnt)
    (h15 : c.nreg 160015 = R0 + 6 * cnt) (hcnt : cnt + 1 ≤ 2 * lam)
    (hm : ∀ a, a < R0 → c.nmem a = m0 a) :
    ∃ c' k, Exec P W coverBody c c' k ∧ k ≤ 20 * lam + 70 ∧ WordsBounded W c' ∧
      c'.nreg 160010 = x + 2 ^ nextG lam b x ∧ c'.nreg 160014 = cnt + 1 ∧
      c'.nreg 160015 = R0 + 6 * (cnt + 1) ∧
      RecAt c'.nmem m0 R0 hp T (nextG lam b x, x) cnt ∧
      (∀ a, (a < R0 + 6 * cnt ∨ R0 + 6 * (cnt + 1) ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, ¬ CovRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  obtain ⟨r11, r26, r24, r20, r21, r22, r27⟩ := hR
  have hpl := Nat.one_le_two_pow (n := lam)
  -- the greedy grade
  obtain ⟨c1, k1, e1, hk1, hw1, h12, h13, fr1, hm1, hrr1, hrm1, ho1⟩ := ascS_exec (P := P) hw
    h10 r11 r26 r24 r20 r21 hl hx (fun y hy => by rw [hm _ (by have := hT.hD; omega)]; exact hT.half y hy)
    (fun i hi => by rw [hm _ (by have := hT.hP; omega)]; exact hT.pow i hi)
    (by have := hT.hD; have := hT.wR; omega) (by have := hT.hP; have := hT.wR; omega) hT.wb
  set g := nextG lam b x with hg
  have hok := nextG_spec (lam := lam) hx
  rw [← hg] at hok
  have hgl : g ≤ lam - 1 := nextG_le _ _ _
  obtain ⟨i, hi⟩ := hok.1
  have hq : x / 2 ^ g = i := by rw [hi, Nat.mul_div_cancel_left _ (by positivity)]
  have hib : (i + 1) * 2 ^ g ≤ b := by have := hok.2; rw [hi] at this; nlinarith
  obtain ⟨he1, he2⟩ := hT.ent g hgl i hib
  have g1 := fr1
  -- the entry
  obtain ⟨c2, k2, e2, hk2, hw2, h17, h18, fr2, hm2, hrr2, hrm2, ho2⟩ := entB_exec (P := P) hw1
    (T := T) (g := g) (q := i)
    (by rw [g1 _ (by unfold AscRG; omega)]; exact r22) h12 (by rw [h13, hq])
    (by rw [g1 _ (by unfold AscRG; omega)]; exact r24)
    (by have := hT.hT; have := hT.wR; omega)
    (by rw [hm1, hm _ (by have := hT.hT; omega)]; have := hT.wR; omega)
  have eT : c1.nmem (T + g) = m0 (T + g) := by rw [hm1]; exact hm _ (by have := hT.hT; omega)
  have eE : c1.nmem (m0 (T + g) + 3 * i) = m0 (m0 (T + g) + 3 * i) := by
    rw [hm1]; exact hm _ (by omega)
  have eF : c1.nmem (m0 (T + g) + 3 * i + 1) = m0 (m0 (T + g) + 3 * i + 1) := by
    rw [hm1]; exact hm _ (by omega)
  rw [eT, eE] at h17; rw [eT, eF] at h18
  -- the record
  obtain ⟨c3, k3, e3, hk3, hw3, s0, sj, s5, sout, h19, fr3, hrr3, hrm3, ho3⟩ := recB_exec (P := P)
    hw2 (rp := R0 + 6 * cnt) (d := m0 (m0 (T + g) + 3 * i))
    (nf := m0 (m0 (T + g) + 3 * i + 1)) (hp := hp)
    (by rw [fr2 _ (by omega) (by omega) (by omega), g1 _ (by unfold AscRG; omega)]; exact h15) h17 h18
    (by rw [fr2 _ (by omega) (by omega) (by omega), g1 _ (by unfold AscRG; omega)]; exact r27)
    (by rw [fr2 _ (by omega) (by omega) (by omega), g1 _ (by unfold AscRG; omega)]; exact r24)
    (by omega) (by have := hT.wR; omega)
  -- the advance
  obtain ⟨c4, k4, e4, hk4, hw4, a15, a14, a10, fr4, hm4, hrr4, hrm4, ho4⟩ := advB_exec (P := P)
    hw3 (rp := R0 + 6 * cnt + 5) (cnt := cnt) (PW := PW) (g := g) (x := x) h19
    (by rw [fr3 _ (by omega) (by omega) (by omega), fr2 _ (by omega) (by omega) (by omega),
      g1 _ (by unfold AscRG; omega)]; exact h14)
    (by rw [fr3 _ (by omega) (by omega) (by omega), fr2 _ (by omega) (by omega) (by omega),
      g1 _ (by unfold AscRG; omega)]; exact r21)
    (by rw [fr3 _ (by omega) (by omega) (by omega), fr2 _ (by omega) (by omega) (by omega)]
        exact h12)
    (by rw [fr3 _ (by omega) (by omega) (by omega), fr2 _ (by omega) (by omega) (by omega),
      g1 _ (by unfold AscRG; omega)]; exact h10)
    (by rw [fr3 _ (by omega) (by omega) (by omega), fr2 _ (by omega) (by omega) (by omega),
      g1 _ (by unfold AscRG; omega)]; exact r24)
    (by rw [sout _ (by have := hT.hP; omega), hm2, hm1, hm _ (by have := hT.hP; omega)]
        exact hT.pow g (by omega))
    (by have := hT.wR; omega) (by have := hT.wR; omega) (by have := hT.hP; have := hT.wR; omega)
    (by have := hok.2; have := hT.wb; omega)
  refine ⟨c4, k1 + (k2 + (k3 + k4)), .seq e1 (.seq e2 (.seq e3 e4)), by omega, hw4, a10, a14,
    by rw [a15]; ring, ⟨?_, fun j h1 h2 => ?_, ?_⟩, fun a ha => ?_, fun r hr => ?_,
    by rw [hrr4, hrr3, hrr2, hrr1], by rw [hrm4, hrm3, hrm2, hrm1],
    by rw [ho4, ho3, ho2, ho1]⟩
  · rw [hm4]; exact s0
  · simp only; rw [hq, hm4, sj j h1 h2, hm2, hm1, hm _ (by omega)]
  · simp only; rw [hq, hm4]; exact s5
  · rw [hm4, sout a (by omega), hm2, hm1]
  · unfold CovRG at hr
    rw [fr4 r (by omega) (by omega) (by unfold AscRG at hr; omega) (by omega),
      fr3 r (by unfold AscRG at hr; omega) (by unfold AscRG at hr; omega)
        (by unfold AscRG at hr; omega),
      fr2 r (by unfold AscRG at hr; omega) (by unfold AscRG at hr; omega)
        (by unfold AscRG at hr; omega), g1 r (by tauto)]


/-- **The cover loop.** -/
theorem coverS_exec {c : Config} (hw : WordsBounded W c) {lam b D PW T hp R0 a : ℕ}
    (hR : CovRegs c lam b D PW T hp) (hT : CovTab c.nmem lam b D PW T R0 W)
    (hl : 1 ≤ lam) (h10 : c.nreg 160010 = a) (_hab : a ≤ b) (hb : b - a ≤ 2 ^ lam)
    (h14 : c.nreg 160014 = 0) (h15 : c.nreg 160015 = R0) :
    ∃ c' k, Exec P W coverS c c' k ∧ k ≤ (20 * lam + 80) * (2 * lam) + 2 ∧
      WordsBounded W c' ∧ c'.nreg 160014 = (cover lam b a).length ∧
      c'.nreg 160015 = R0 + 6 * (cover lam b a).length ∧
      (∀ k, k < (cover lam b a).length →
        RecAt c'.nmem c.nmem R0 hp T ((cover lam b a).getD k (0, 0)) k) ∧
      (∀ x, (x < R0 ∨ R0 + 6 * (cover lam b a).length ≤ x) → c'.nmem x = c.nmem x) ∧
      (∀ r, ¬ CovRG r → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hlen := cover_length_le (b := b) (x := a) hl hb
  set L := cover lam b a with hL
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ (∀ r, ¬ CovRG r → c'.nreg r = c.nreg r) ∧
    c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
    ∃ x Wd, c'.nreg 160010 = x ∧ Wd ++ cover lam b x = L ∧ c'.nreg 160014 = Wd.length ∧
      c'.nreg 160015 = R0 + 6 * Wd.length ∧
      (∀ k, k < Wd.length → RecAt c'.nmem c.nmem R0 hp T (Wd.getD k (0, 0)) k) ∧
      (∀ y, (y < R0 ∨ R0 + 6 * Wd.length ≤ y) → c'.nmem y = c.nmem y)
  obtain ⟨c', k, e, ⟨hw', hr', hrr', hrm', ho', x, Wd, hx, hWd, h14', h15', hrec, hout⟩, htest,
      hk⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 160010) (b := 160011)
    (body := coverBody) I
    (fun c' => (20 * lam + 80) * (cover lam b (c'.nreg 160010)).length) (fun c' h => h.1)
    (fun c2 ⟨hw2, hr2, hrr2, hrm2, ho2, x, Wd, hx, hWd, h14, h15, hrec, hout⟩ htest => by
      have hR2 : CovRegs c2 lam b D PW T hp := hR.frame hr2
      rw [hx, hR2.r11] at htest
      have hWl : Wd.length + 1 ≤ 2 * lam := by
        have := congrArg List.length hWd
        rw [List.length_append, cover_of_lt htest, List.length_cons] at this
        omega
      obtain ⟨c3, k3, e3, hk3, hw3, a10, a14, a15, hr3, hout3, fr3, hrr3, hrm3, ho3⟩ :=
        coverBody_exec (P := P) hw2 hR2 hT hl hx htest h14 h15 hWl
          (fun y hy => hout y (Or.inl hy))
      refine ⟨c3, k3, e3, ⟨hw3, fun r hr => by rw [fr3 r hr, hr2 r hr], by rw [hrr3, hrr2],
        by rw [hrm3, hrm2], by rw [ho3, ho2], x + 2 ^ nextG lam b x,
        Wd ++ [(nextG lam b x, x)], a10, ?_, by rw [a14]; simp, by rw [a15]; simp,
        fun k hk => ?_, fun y hy => ?_⟩, ?_⟩
      · rw [List.append_assoc, List.singleton_append, ← cover_of_lt htest]; exact hWd
      · simp only [List.length_append, List.length_singleton] at hk
        rcases Nat.lt_or_ge k Wd.length with h | h
        · obtain ⟨b0, b1, b2⟩ := hrec k h
          rw [List.getD_append _ _ _ _ h]
          refine ⟨by rw [hout3 _ (by omega)]; exact b0, fun j h1 h2 => ?_, ?_⟩
          · rw [hout3 _ (by omega)]; exact b1 j h1 h2
          · rw [hout3 _ (by omega)]; exact b2
        · have hk' : k = Wd.length := by omega
          subst hk'
          rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
          simpa using hr3
      · simp only [List.length_append, List.length_singleton] at hy
        rw [hout3 y (by omega)]; exact hout y (by omega)
      · rw [a10, hx]
        have e := cover_of_lt (lam := lam) htest
        have hl2 : (cover lam b x).length = (cover lam b (x + 2 ^ nextG lam b x)).length + 1 := by
          rw [e, List.length_cons]
        rw [hl2, Nat.mul_add, Nat.mul_one]
        omega)
    ⟨hw, fun r _ => rfl, rfl, rfl, rfl, a, [], h10, by simp [hL], by simp [h14], by simp [h15],
      fun k hk => by simp at hk, fun y _ => rfl⟩
  have hR' : CovRegs c' lam b D PW T hp := hR.frame hr'
  rw [hx, hR'.r11] at htest
  have hWL : Wd = L := by rw [← hWd, cover_of_ge (by omega), List.append_nil]
  subst hWL
  refine ⟨c', k, e, ?_, hw', h14', h15', hrec, hout, hr', hrr', hrm', ho'⟩
  rw [h10] at hk
  have : (20 * lam + 80) * (cover lam b a).length ≤ (20 * lam + 80) * (2 * lam) :=
    Nat.mul_le_mul_left _ hlen
  rw [← hL] at hk this
  omega

end proofs

end

end Chazelle.Core.L41
