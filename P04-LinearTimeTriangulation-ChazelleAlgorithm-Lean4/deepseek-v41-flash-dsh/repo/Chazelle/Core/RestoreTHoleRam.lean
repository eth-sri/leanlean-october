module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTHoleMath

/-!
# WP-E, the candidate test on the RAM: small register programs for the holes

Register-only building blocks with exact effects (`Out`: only the listed registers change):
a conditional subtraction (`condSub`), the tour step of a tour position (`candS`, `candIdx`),
the wrap of a walk index (`nxtS`), and the lemma turning such an execution into a run step.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **Only the registers `L` change** (and nothing else of the configuration). -/
def Out (c c' : Config) (L : List ℕ) : Prop :=
  (∀ r, r ∉ L → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.nmem = c.nmem ∧
    c'.rmem = c.rmem ∧ c'.output = c.output

theorem Out.refl (c : Config) (L : List ℕ) : Out c c L :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Out.trans {c c₁ c₂ : Config} {L₁ L₂ : List ℕ} (h₁ : Out c c₁ L₁) (h₂ : Out c₁ c₂ L₂) :
    Out c c₂ (L₁ ++ L₂) :=
  ⟨fun r hr => by
    ϴ' List.mem_append, not_or at hr
    rw [h₂.1 r hr.2, h₁.1 r hr.1], h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.1.trans h₁.2.2.2.1, h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem Out.mono {c c' : Config} {L L' : List ℕ} (h : Out c c' L) (hL : ∀ r ∈ L, r ∈ L') :
    Out c c' L' := ⟨fun r hr => h.1 r (fun h' => hr (hL r h')), h.2⟩

/-- One register instruction. -/
theorem out_instr {i : Instr} {r v : ℕ}
    (hex : Exec P W (.instr i) c { c with nreg := upd c.nreg r v } 1) :
    ∃ c', Exec P W (.instr i) c c' 1 ∧ c'.nreg r = v ∧ Out c c' [r] :=
  ⟨_, hex, ✓, fun q hq => by simp only [List.mem_singleton] at hq; simp [upd, hq],
    rfl, rfl, rfl, rfl⟩

/-- **A run step** from an execution changing only scratch registers. -/
theorem RS.out {s : Stmt} {K : ℕ} {L : List ℕ} {Q : Config → Prop} (hI : TInv W c₀ c)
    (hL : ∀ r ∈ L, Scr r) {c' : Config} {k : ℕ} (ex : Exec P W s c c' k) (hk : k ≤ K)
    (ho : Out c c' L) (hq : Q c') : RS P W c₀ s c K Q := by
  obtain ⟨hI', hrf⟩ := hI.regs (c' := c') (k := k) ex.wb_right (fun r hr => ho.1 r (fun h => by
    have := hL r h; unfold Scr at this; omega)) ho.2.1 ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2
  exact ⟨c', k, ex, hk, hI', hrf, hq⟩

/-! ## A conditional subtraction -/

/-- `dst := a < b ? a : a - b`. -/
def condSub (dst a b : ℕ) : Stmt := .ifLtN a b (.instr (.copyN dst a)) (.instr (.subN dst a b))

theorem condSub_exec (hw : WordsBounded W c) (dst a b : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W (condSub dst a b) c c' k ∧
      c'.nreg dst = (if c.nreg a < c.nreg b then c.nreg a else c.nreg a - c.nreg b) ∧
      Out c c' [dst] := by
  unfold condSub
  by_cases h : c.nreg a < c.nreg b
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN hw dst a)
    exact ⟨c', _, ⋄, .ifLtN_true h e, by rw [v, ite_eq_left h], o⟩
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN hw dst a b)
    exact ⟨c', _, ⋄, .ifLtN_false h e, by rw [v, ite_eq_right h], o⟩

/-! ## The tour step of a tour position -/

/-- `dst := candIdx m S j` for `j` in `jr`, `S` in `sr`, `2m` in `mr` (`t` scratch). -/
def candS (dst jr sr mr : ℕ) : Stmt :=
  .ifLtN jr sr (.seq (.instr (.subN dst mr sr)) (.instr (.addN dst dst jr)))
    (.instr (.subN dst jr sr))

theorem candS_exec (hw : WordsBounded W c) {dst jr sr mr : ℕ} (hd1 : dst ≠ jr) (_hd2 : dst ≠ sr)
    (_hd3 : dst ≠ mr) {m S j : ℕ} (hj : c.nreg jr = j) (hs : c.nreg sr = S)
    (hm : c.nreg mr = 2 * m) (hS : S ≤ 2 * m) (hW : 2 * m ≤ W) (_hjm : j ≤ 2 * m) :
    ∃ c', ∃ k ≤ 4, Exec P W (candS dst jr sr mr) c c' k ∧ c'.nreg dst = candIdx m S j ∧
      Out c c' [dst] := by
  unfold candS
  by_cases h : c.nreg jr < c.nreg sr
  · obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw dst mr sr)
    obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right dst dst jr
      (by rw [v₁, o₁.1 jr (⊚ hd1.symm), hm, hs, hj]; Ξ' hj, hs at h; omega))
    refine ⟨c₂, _, ⋄, .ifLtN_true h (.seq e₁ e₂), ?_, (o₁.trans o₂).mono (✓)⟩
    Ξ v₂, v₁, o₁.1 jr (⊚ hd1.symm), hm, hs, hj
    Ξ' hj, hs at h
    unfold candIdx; rw [ite_eq_left h]; omega
  · obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.subN hw dst jr sr)
    refine ⟨c₁, _, ⋄, .ifLtN_false h e₁, ?_, o₁⟩
    Ξ v₁, hj, hs
    Ξ' hj, hs at h
    unfold candIdx; Ξ ite_eq_right h

/-! ## Wrapping a walk index -/

/-- `r := r < n ? r : 0` (`n` in `nr`). -/
def nxtS (r nr : ℕ) : Stmt := .ifLtN r nr .skip (.instr (.constN r 0))

theorem nxtS_exec (hw : WordsBounded W c) (r nr : ℕ) :
    ∃ c', ∃ k ≤ 3, Exec P W (nxtS r nr) c c' k ∧
      c'.nreg r = (if c.nreg r < c.nreg nr then c.nreg r else 0) ∧ Out c c' [r] := by
  unfold nxtS
  by_cases h : c.nreg r < c.nreg nr
  · exact ⟨c, _, ⋄, .ifLtN_true h (.skip hw), by rw [ite_eq_left h], Out.refl _ _⟩
  · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.constN hw r 0 (Nat.zero_le _))
    exact ⟨c', _, ⋄, .ifLtN_false h e, by rw [v, ite_eq_right h], o⟩

/-- The wrap of `q + 1` below `n` is `(q + 1) % n`. -/
theorem wrap_succ {q n : ℕ} (hq : q < n) : (if q + 1 < n then q + 1 else 0) = (q + 1) % n := by
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · Ξ show q + 1 = n by omega, Nat.mod_self

/-! ## The holes of the interior model -/

/-- **The hole of the candidate in the interior model** into `84009 … 84011`. -/
def intH : Stmt :=
  .seq (.instr (.inputSize 83090)) (.seq (.instr (.addN 83092 83005 83023)) (.seq (nxtS 83092 83090)
    (.seq (.ifLtN 83022 83005 (.instr (.subN 83093 83005 83023)) (.instr (.subN 83093 83090 83023)))
      (.seq (.instr (.constN 84009 1)) (.seq (.ifLtN 83022 83006 (.instr (.copyN 84010 83005))
        (.instr (.copyN 84010 83093))) (.instr (.copyN 84011 83092)))))))

theorem intH_exec (hw : WordsBounded W c) (hW : P.n + 2 ≤ W) (h22 : c.nreg 83022 = 0)
    (h23 : c.nreg 83023 = 1) (he : c.nreg 83005 < P.n) :
    ∃ c', ∃ k ≤ 20, Exec P W intH c c' k ∧ c'.nreg 84009 = 1 ∧
      c'.nreg 84010 = (if c.nreg 83006 = 0 then prevV P.n (c.nreg 83005) else c.nreg 83005) ∧
      c'.nreg 84011 = (c.nreg 83005 + 1) % P.n ∧
      Out c c' [83090, 83092, 83093, 84009, 84010, 84011] := by
  have hn : 1 ≤ P.n := ⋄
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.inputSize hw 83090 (⋄))
  have k1 := fun r (h : r ≠ 83090) => o₁.1 r (⊚ h)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.addN e₁.wb_right 83092 83005 83023
    (by rw [k1 _ (⋄), k1 _ (⋄), h23]; omega))
  have k2 := fun r (h : r ≠ 83092) => o₂.1 r (⊚ h)
  obtain ⟨c₃, k₃, hk₃, e₃, v₃, o₃⟩ := nxtS_exec (P := P) e₂.wb_right 83092 83090
  have k3 := fun r (h : r ≠ 83092) => o₃.1 r (⊚ h)
  have q92 : c₃.nreg 83092 = (c.nreg 83005 + 1) % P.n := by
    Ξ v₃, v₂, k2 _ (⋄), v₁, k1 _ (⋄), k1 _ (⋄), h23
    exact wrap_succ he
  have q90 : c₃.nreg 83090 = P.n := Ρ k3 _ (⋄), k2 _ (⋄), v₁
  have r05 : c₃.nreg 83005 = c.nreg 83005 := by
    Ξ k3 _ (⋄), k2 _ (⋄), k1 _ (⋄)
  have r22 : c₃.nreg 83022 = 0 := Ρ k3 _ (⋄), k2 _ (⋄), k1 _ (⋄), h22
  have r23 : c₃.nreg 83023 = 1 := Ρ k3 _ (⋄), k2 _ (⋄), k1 _ (⋄), h23
  -- the previous vertex
  obtain ⟨c₄, k₄, hk₄, e₄, v₄, o₄⟩ : ∃ c₄, ∃ k ≤ 3, Exec P W (.ifLtN 83022 83005
      (.instr (.subN 83093 83005 83023)) (.instr (.subN 83093 83090 83023))) c₃ c₄ k ∧
      c₄.nreg 83093 = prevV P.n (c.nreg 83005) ∧ Out c₃ c₄ [83093] := by
    by_cases h : c₃.nreg 83022 < c₃.nreg 83005
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN e₃.wb_right 83093 83005 83023)
      refine ⟨c', _, ⋄, .ifLtN_true h e, ?_, o⟩
      rw [v, r05, r23]; Ξ' r22, r05 at h
      unfold prevV
      rw [show c.nreg 83005 + P.n - 1 = (c.nreg 83005 - 1) + P.n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (⋄)]
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.subN e₃.wb_right 83093 83090 83023)
      refine ⟨c', _, ⋄, .ifLtN_false h e, ?_, o⟩
      rw [v, q90, r23]; Ξ' r22, r05 at h
      unfold prevV
      Ξ show c.nreg 83005 = 0 by omega, Nat.zero_add, Nat.mod_eq_of_lt (⋄)
  have k4 := fun r (h : r ≠ 83093) => o₄.1 r (⊚ h)
  obtain ⟨c₅, e₅, v₅, o₅⟩ := out_instr (P := P) (Exec.constN e₄.wb_right 84009 1 (⋄))
  have k5 := fun r (h : r ≠ 84009) => o₅.1 r (⊚ h)
  obtain ⟨c₆, k₆, hk₆, e₆, v₆, o₆⟩ : ∃ c₆, ∃ k ≤ 3, Exec P W (.ifLtN 83022 83006
      (.instr (.copyN 84010 83005)) (.instr (.copyN 84010 83093))) c₅ c₆ k ∧
      c₆.nreg 84010 = (if c.nreg 83006 = 0 then prevV P.n (c.nreg 83005) else c.nreg 83005) ∧
      Out c₅ c₆ [84010] := by
    have r5 : ∀ r, r ≠ 84009 → r ≠ 83093 → r ≠ 83092 → r ≠ 83090 → c₅.nreg r = c.nreg r :=
      fun r a b d e => Ρ k5 r a, k4 r b, k3 r d, k2 r d, k1 r e
    by_cases h : c₅.nreg 83022 < c₅.nreg 83006
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN e₅.wb_right 84010 83005)
      refine ⟨c', _, ⋄, .ifLtN_true h e, ?_, o⟩
      rw [r5 _ (⋄) (⋄) (⋄) (⋄),
        r5 _ (⋄) (⋄) (⋄) (⋄), h22] at h
      Ξ v, r5 _ (⋄) (⋄) (⋄) (⋄), ite_eq_right (⋄)
    · obtain ⟨c', e, v, o⟩ := out_instr (P := P) (Exec.copyN e₅.wb_right 84010 83093)
      refine ⟨c', _, ⋄, .ifLtN_false h e, ?_, o⟩
      rw [r5 _ (⋄) (⋄) (⋄) (⋄),
        r5 _ (⋄) (⋄) (⋄) (⋄), h22] at h
      Ξ v, k5 _ (⋄), v₄, ite_eq_left (⋄)
  obtain ⟨c₇, e₇, v₇, o₇⟩ := out_instr (P := P) (Exec.copyN e₆.wb_right 84011 83092)
  have ex : Exec P W intH c c₇ _ := .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  refine ⟨c₇, _, ⋄, ex, ?_, ?_, ?_, ?_⟩
  · Ξ o₇.1 _ (✓), o₆.1 _ (✓), v₅
  · Ξ o₇.1 _ (✓), v₆
  · Ξ v₇, o₆.1 _ (✓), k5 _ (⋄), k4 _ (⋄), q92
  · exact ((((((o₁.trans o₂).trans o₃).trans o₄).trans o₅).trans o₆).trans o₇).mono
      (by intro r hr; ϴ' List.mem_append, List.mem_cons, List.not_mem_nil, or_false at hr
          simp only [List.mem_cons, List.not_mem_nil, or_false]; omega)

end

end Restore

end Chazelle.Core
