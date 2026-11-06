module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvTFilt

/-!
# Down-phase transition (D2), RAM part 4: the loop of the filter pass

Invariant `FInv` of `fLoop` (record index `i` in `190030`): read cursor `CB + 5 i`, write
cursor `B' + 3 rank i`, kept count `rank i`, the constants, the other registers, and the memory
`memT` (the first `rank i` triples of `transL` at `B'`).  `fBody_exec` (one record),
`fLoop_exec` (the pass).
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)

@[expose] public section

/-- **The invariant of the filter pass.** -/
structure FInv (m₀ : ℕ → ℕ) (li : Bool) (n c₀ : ℕ) (L₀ : List (ℕ × ℕ × ℕ)) (CB B' : ℕ)
    (cI d : Config) : Prop where
  i_le : d.nreg 190030 ≤ L₀.length
  rK : d.nreg 190023 = L₀.length
  r31 : d.nreg 190031 = CB + 5 * d.nreg 190030
  r35 : d.nreg 190035 = B' + 3 * rankF (keepT li n c₀) L₀ (d.nreg 190030)
  r36 : d.nreg 190036 = rankF (keepT li n c₀) L₀ (d.nreg 190030)
  r10 : d.nreg 190010 = n - 1
  r14 : d.nreg 190014 = c₀
  r15 : d.nreg 190015 = c₀ + (n - 1)
  r16 : d.nreg 190016 = idxI li n 0
  r17 : d.nreg 190017 = 1
  r18 : d.nreg 190018 = 0
  fr : ∀ r, (r < 190030 ∨ 190039 < r) → d.nreg r = cI.nreg r
  rr : d.rreg = cI.rreg
  rm : d.rmem = cI.rmem
  out : d.output = cI.output
  mem : ∀ a, d.nmem a = memT m₀ li n c₀ L₀ B' (d.nreg 190030) a

/-- The records of the chord area: `(h, lp, rp)` of record `i` at `CB + 5 i`. -/
def RecsT (m : ℕ → ℕ) (CB : ℕ) (L₀ : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ i, i < L₀.length → m (CB + 5 * i) = (L₀.getD i (0, 0, 0)).1 ∧
    m (CB + 5 * i + 1) = (L₀.getD i (0, 0, 0)).2.1 ∧ m (CB + 5 * i + 2) = (L₀.getD i (0, 0, 0)).2.2

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
/-- **One record.** -/
theorem fBody_exec {m₀ : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
    (hR : RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : FInv m₀ li n c₀ L₀ CB B' cI d) (ht : d.nreg 190030 < d.nreg 190023) :
    ∃ d' k, Exec P W fBody d d' k ∧ WordsBounded W d' ∧ FInv m₀ li n c₀ L₀ CB B' cI d' ∧
      d'.nreg 190030 = d.nreg 190030 + 1 ∧ 3 ≤ k ∧ k ≤ 52 := by
  rw [hI.rK] at ht
  have hCB' : CB + 5 * L₀.length ≤ B' := hCB.resolve_left (by omega)
  set i := d.nreg 190030 with hi
  set x := L₀.getD i (0, 0, 0) with hx
  set j := rankF (keepT li n c₀) L₀ i with hj
  have hle := DownBase.rankF_le (keepT li n c₀) L₀ i
  obtain ⟨l1, l2, l3⟩ := hR i ht
  have hmL : ∀ q, q < 3 → d.nmem (CB + 5 * i + q) = m₀ (CB + 5 * i + q) := fun q hq => by
    rw [hI.mem]; grind [memT]
  have hW1 : 1 ≤ W := by omega
  clear hCB
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v32, v33, v34, v31, v37, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    fLoad_exec (P := P) d hw hI.r31 hI.r17 (by omega)
  rw [← hi] at v32 v33 v34 v31
  have hm0 := hmL 0 (by norm_num)
  rw [Nat.add_zero] at hm0
  rw [hm0, l1] at v32
  rw [hmL 1 (by norm_num), l2] at v33
  rw [hmL 2 (by norm_num), l3] at v34
  have g₁ : ∀ r, (r < 190031 ∨ 190037 < r) → d₁.nreg r = d.nreg r := fun r hr =>
    r₁ r (by omega) (by omega) (by omega) (by omega) (by omega)
  -- the two tests
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := fTest_exec (P := P) d₁ e₁.wb_right hW1
    (li := li) (n := n) (c₀ := c₀) (p := 190033) (by norm_num) (by norm_num) (by norm_num)
    (by rw [g₁ _ (by norm_num), hI.r14]) (by rw [g₁ _ (by norm_num), hI.r15])
    (by rw [g₁ _ (by norm_num), hI.r16])
  obtain ⟨d₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ := fTest_exec (P := P) d₂ e₂.wb_right hW1
    (li := li) (n := n) (c₀ := c₀) (p := 190034) (by norm_num) (by norm_num) (by norm_num)
    (by rw [r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r14])
    (by rw [r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r15])
    (by rw [r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r16])
  have hflag : d₃.nreg 190037 = if keepT li n c₀ x = true then 1 else 0 := by
    grind [keepT]
  -- the two maps
  obtain ⟨d₄, k₄, e₄, hk₄, v₄, r₄, m₄, rr₄, rm₄, o₄⟩ := fMap_exec (P := P) d₃ e₃.wb_right
    (n := n) (c₀ := c₀) (d := 190038) (p := 190033) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by rw [r₃ _ (by norm_num), r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r10])
    (by rw [r₃ _ (by norm_num), r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r14])
    (by rw [r₃ _ (by norm_num), r₂ _ (by norm_num), g₁ _ (by norm_num), hI.r15])
  obtain ⟨d₅, k₅, e₅, hk₅, v₅, r₅, m₅, rr₅, rm₅, o₅⟩ := fMap_exec (P := P) d₄ e₄.wb_right
    (n := n) (c₀ := c₀) (d := 190039) (p := 190034) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (by grind [Chazelle.Core.DrvT.FInv.r10])
    (by grind [Chazelle.Core.DrvT.FInv.r14])
    (by grind [Chazelle.Core.DrvT.FInv.r15])
  -- registers of `d₅`
  have g5 : ∀ r, r ≠ 190031 → r ≠ 190032 → r ≠ 190033 → r ≠ 190034 → r ≠ 190037 →
      r ≠ 190038 → r ≠ 190039 → d₅.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 a6 a7 => by
    grind
  have e32 : d₅.nreg 190032 = x.1 := by
    grind
  have e38 : d₅.nreg 190038 = mapE n c₀ x.2.1 := by
    ram_grind
  have e39 : d₅.nreg 190039 = mapE n c₀ x.2.2 := by
    ram_grind
  have f5 : d₅.nreg 190037 = if keepT li n c₀ x = true then 1 else 0 := by
    ram_grind
  have hm5 : d₅.nmem = d.nmem := by ram_grind
  -- the branch
  obtain ⟨d₆, k₆, e₆, hk₆, hk₆', g6, mem6, n35, n36, rr₆, rm₆, o₆⟩ : ∃ d₆ k₆,
      Exec P W (.ifLtN 190018 190037 fKeep .skip) d₅ d₆ k₆ ∧ 1 ≤ k₆ ∧ k₆ ≤ 8 ∧
      (∀ r, r ≠ 190035 → r ≠ 190036 → d₆.nreg r = d₅.nreg r) ∧
      (∀ a, d₆.nmem a = memT m₀ li n c₀ L₀ B' (i + 1) a) ∧
      d₆.nreg 190035 = B' + 3 * rankF (keepT li n c₀) L₀ (i + 1) ∧
      d₆.nreg 190036 = rankF (keepT li n c₀) L₀ (i + 1) ∧
      d₆.rreg = d₅.rreg ∧ d₆.rmem = d₅.rmem ∧ d₆.output = d₅.output := by
    have h18 : d₅.nreg 190018 = 0 := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), hI.r18]
    have h35 : d₅.nreg 190035 = B' + 3 * j := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), hI.r35]
    have h36 : d₅.nreg 190036 = j := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), hI.r36]
    have h17 : d₅.nreg 190017 = 1 := by
      rw [g5 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num), hI.r17]
    have hr := DownBase.rankF_succ (keepT li n c₀) (0, 0, 0) (L := L₀) ht
    cases hk : keepT li n c₀ x
    · rw [hk] at f5
      simp only [Bool.false_eq_true, ite_false] at f5
      have hn : ¬ d₅.nreg 190018 < d₅.nreg 190037 := by omega
      rw [← hx, hk] at hr
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
      refine ⟨d₅, _, .ifLtN_false hn (.skip e₅.wb_right), by omega, by omega,
        fun _ _ _ => rfl, fun a => ?_, by rw [h35, hr], by rw [h36, hr], rfl, rfl, rfl⟩
      rw [hm5, hI.mem a, ← hi]
      exact memT_drop ht (by omega) a
    · rw [hk] at f5
      simp only [ite_true] at f5
      have hp : d₅.nreg 190018 < d₅.nreg 190037 := by omega
      have hjK : j + 1 ≤ L₀.length := by
        
        
        omega
      obtain ⟨d₆, k₆, e₆', hk₆, w35, w36, r₆, mm₆, rr₆, rm₆, o₆⟩ :=
        fKeep_exec (P := P) d₅ e₅.wb_right h35 h36 h17 (by omega) (by omega)
      rw [← hx, hk] at hr
      simp only [ite_true] at hr
      refine ⟨d₆, _, .ifLtN_true hp e₆', by omega, by omega, r₆, fun a => ?_,
        by omega, by rw [w36, hr], rr₆, rm₆, o₆⟩
      rw [mm₆, e32, e38, e39, hm5]
      have := memT_keep (m₀ := m₀) (m := d.nmem) (B' := B') (hI.mem) ht
        (by omega) a
      rw [← hi, ← hj] at this
      rw [← this]
      simp only [trT, hx]
  -- the increment
  have h30 : d₆.nreg 190030 = i := by
    ram_grind
  have h17' : d₆.nreg 190017 = 1 := by
    grind [Chazelle.Core.DrvT.FInv.r17]
  have e₇ := Exec.addN (P := P) e₆.wb_right 190030 190030 190017 (by omega)
  set d₇ : Config := { d₆ with nreg := upd d₆.nreg 190030 (d₆.nreg 190030 + d₆.nreg 190017) }
    with hd₇
  have g7 : ∀ r, r ≠ 190030 → d₇.nreg r = d₆.nreg r := fun r hr => by rw [hd₇]; simp [hr]
  have v7 : d₇.nreg 190030 = i + 1 := by rw [hd₇]; simp [h30, h17']
  have g : ∀ r, (r < 190030 ∨ 190039 < r) → d₇.nreg r = d.nreg r := fun r hr => by
    rw [g7 r (by omega), g6 r (by omega) (by omega),
      g5 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have X' : Exec P W fBody d d₇ (k₁ + (k₂ + (k₃ + (k₄ + (k₅ + (k₆ + 1)))))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇)))))
  refine ⟨d₇, _, X', e₇.wb_right, ?_, v7, by omega, by omega⟩
  ram_grind

/-- **The filter pass.** -/
theorem fLoop_exec {m₀ : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {CB B' : ℕ}
    (hR : RecsT m₀ CB L₀) (hCB : L₀.length = 0 ∨ CB + 5 * L₀.length ≤ B')
    (hBW : B' + 3 * L₀.length + 3 ≤ W) {cI d : Config} (hw : WordsBounded W d)
    (hI : FInv m₀ li n c₀ L₀ CB B' cI d) (h0 : d.nreg 190030 = 0) :
    ∃ d' k, Exec P W fLoop d d' k ∧ WordsBounded W d' ∧ FInv m₀ li n c₀ L₀ CB B' cI d' ∧
      d'.nreg 190030 = L₀.length ∧ 3 * L₀.length ≤ k ∧ k ≤ 54 * L₀.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 190030) (b := 190023) (body := fBody)
    (fun d => WordsBounded W d ∧ FInv m₀ li n c₀ L₀ CB B' cI d)
    (fun d => 54 * (L₀.length - d.nreg 190030)) (fun d => 3 * d.nreg 190030) (fun d hd => hd.1)
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := fBody_exec hR hCB hBW hwd hId ht
      have := hId.rK
      refine ⟨d', k, e, ⟨hw', hI'⟩, ?_, ?_⟩
      all_goals omega)
    ⟨hw, hI⟩
  have hi := hI'.i_le
  rw [hI'.rK] at htest
  refine ⟨d', k, e, hw', hI', by omega, ?_, ?_⟩
  all_goals omega

end exec

end

end DrvT

end Chazelle.Core
