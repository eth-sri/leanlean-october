module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseBaseRam

/-!
# Down phase, A1 (RAM, part 2): the chord pass

`dLoop1` runs over the `K` chords of `L` (at `B`): kept triples (`keepX`) are appended at `B'`
(after `i` chords: `keepL` up to `rank i`), and the code table at `X` gets the entries
`newCode + 1` (or `0`) of the codes `2i`, `2i + 1` (`mem1`).  Invariant `Inv1`.
-/

namespace Chazelle.Core

namespace DownBase

open Machine Machine.Stmt Programs

@[expose] public section

/-- The invariant of the chord pass. -/
structure Inv1 (m₀ : ℕ → ℕ) (li : Bool) (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (B B' X : ℕ)
    (c₀ d : Config) : Prop where
  i_le : d.nreg 200110 ≤ L.length
  rK : d.nreg 200002 = L.length
  r111 : d.nreg 200111 = B + 3 * d.nreg 200110
  r117 : d.nreg 200117 = X + 2 * d.nreg 200110
  r118 : d.nreg 200118 = rankF (keepX li n) L (d.nreg 200110)
  r119 : d.nreg 200119 = B' + 3 * rankF (keepX li n) L (d.nreg 200110)
  r100 : d.nreg 200100 = 1
  r101 : d.nreg 200101 = 0
  r103 : d.nreg 200103 = if li then 1 else 0
  r104 : d.nreg 200104 = n - 1
  fr : ∀ r, (r < 200110 ∨ 200120 < r) → d.nreg r = c₀.nreg r
  rr : d.rreg = c₀.rreg
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output
  mem : ∀ a, d.nmem a = mem1 m₀ li n L B' X (d.nreg 200110) a

section exec

variable {P : Polygon} {W : ℕ}


/-- **One chord.** -/
theorem dBody1_exec {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B B' X : ℕ}
    (hL : ChordListAt m₀ B L) (hB : B + 3 * L.length ≤ B') (hX : X = B' + 3 * L.length)
    (hXW : X + 2 * L.length + 2 ≤ W) {c₀ d : Config} (hw : WordsBounded W d)
    (hI : Inv1 m₀ li n L B B' X c₀ d) (ht : d.nreg 200110 < d.nreg 200002) :
    ∃ d' k, Exec P W dBody1 d d' k ∧ WordsBounded W d' ∧ Inv1 m₀ li n L B B' X c₀ d' ∧
      d'.nreg 200110 = d.nreg 200110 + 1 ∧ 13 ≤ k ∧ k ≤ 45 := by
  rw [hI.rK] at ht
  set i := d.nreg 200110 with hi
  set x := L.getD i (0, 0, 0) with hx
  set j := rankF (keepX li n) L i with hj
  have hle := rankF_le (keepX li n) L i
  obtain ⟨l1, l2, l3⟩ := hL i ht
  have hmL : ∀ q, q < 3 → d.nmem (B + 3 * i + q) = m₀ (B + 3 * i + q) := fun q hq => by
    rw [hI.mem]; unfold mem1; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have hW1 : 1 ≤ W := by omega
  -- load
  obtain ⟨d₁, k₁, e₁, hk₁, v12, v13, v14, v11, v15, r₁, m₁, rr₁, rm₁, o₁⟩ :=
    dLoad_exec (P := P) d hw hI.r111 hI.r100 (by omega)
  rw [← hi] at v12 v13 v14 v11
  have hm0 := hmL 0 (by norm_num)
  rw [Nat.add_zero] at hm0
  rw [hm0, l1] at v12
  rw [hmL 1 (by norm_num), l2] at v13
  rw [hmL 2 (by norm_num), l3] at v14
  -- the two tests
  obtain ⟨d₂, k₂, e₂, hk₂, v₂, r₂, m₂, rr₂, rm₂, o₂⟩ := dTest_exec (P := P) d₁ e₁.wb_right hW1
    (li := li) (n := n) (p := 200113) (by norm_num)
    (by rw [r₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r101])
    (by rw [r₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r103])
    (by rw [r₁ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num), hI.r104])
  obtain ⟨d₃, k₃, e₃, hk₃, v₃, r₃, m₃, rr₃, rm₃, o₃⟩ := dTest_exec (P := P) d₂ e₂.wb_right hW1
    (li := li) (n := n) (p := 200114) (by norm_num)
    (by rw [r₂ _ (by norm_num) (by norm_num), r₁ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), hI.r101])
    (by rw [r₂ _ (by norm_num) (by norm_num), r₁ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), hI.r103])
    (by rw [r₂ _ (by norm_num) (by norm_num), r₁ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num), hI.r104])
  -- registers of `d₃`
  have g3 : ∀ r, r ≠ 200111 → r ≠ 200112 → r ≠ 200113 → r ≠ 200114 → r ≠ 200115 →
      r ≠ 200116 → d₃.nreg r = d.nreg r := fun r a1 a2 a3 a4 a5 a6 => by
    rw [r₃ r a5 a6, r₂ r a5 a6, r₁ r a1 a2 a3 a4 a5]
  have e12 : d₃.nreg 200112 = x.1 := by
    rw [r₃ _ (by norm_num) (by norm_num), r₂ _ (by norm_num) (by norm_num), v12]
  have e13 : d₃.nreg 200113 = x.2.1 := by
    rw [r₃ _ (by norm_num) (by norm_num), r₂ _ (by norm_num) (by norm_num), v13]
  have e14 : d₃.nreg 200114 = x.2.2 := by
    rw [r₃ _ (by norm_num) (by norm_num), r₂ _ (by norm_num) (by norm_num), v14]
  have hflag : d₃.nreg 200115 = if keepX li n x = true then 1 else 0 := by
    rw [v₃, v₂, v15, r₂ _ (by norm_num) (by norm_num), v12, v13,
      r₂ _ (by norm_num) (by norm_num), v14]
    rw [← hx]
    have hk := keepX_iff li n x
    by_cases h1 : x.1 = wStart li n x.2.1 <;> by_cases h2 : x.1 = wStart li n x.2.2 <;>
      simp [hk, h1, h2]
  have hm3 : d₃.nmem = d.nmem := by rw [m₃, m₂, m₁]
  -- the branch and the increment
  have hB' : B' + 3 * L.length ≤ X := by omega
  obtain ⟨d₄, k₄, e₄, hk₄, hk₄', g4, mem4, n117, n118, n119, rr₄, rm₄, o₄⟩ : ∃ d₄ k₄,
      Exec P W (.ifLtN 200101 200115 dKeep dDrop) d₃ d₄ k₄ ∧ 5 ≤ k₄ ∧ k₄ ≤ 16 ∧
      (∀ r, r ≠ 200117 → r ≠ 200118 → r ≠ 200119 → r ≠ 200120 → d₄.nreg r = d₃.nreg r) ∧
      (∀ a, d₄.nmem a = mem1 m₀ li n L B' X (i + 1) a) ∧
      d₄.nreg 200117 = X + 2 * (i + 1) ∧
      d₄.nreg 200118 = rankF (keepX li n) L (i + 1) ∧
      d₄.nreg 200119 = B' + 3 * rankF (keepX li n) L (i + 1) ∧
      d₄.rreg = d₃.rreg ∧ d₄.rmem = d₃.rmem ∧ d₄.output = d₃.output := by
    have h101 : d₃.nreg 200101 = 0 := by
      rw [g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), hI.r101]
    have h117 : d₃.nreg 200117 = X + 2 * i := by
      rw [g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), hI.r117]
    have h100 : d₃.nreg 200100 = 1 := by
      rw [g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), hI.r100]
    have hr := rankF_succ (keepX li n) (0, 0, 0) (L := L) ht
    cases hk : keepX li n x
    · -- dropped
      rw [hk] at hflag
      simp only [Bool.false_eq_true, ite_false] at hflag
      have hn : ¬ d₃.nreg 200101 < d₃.nreg 200115 := by rw [h101, hflag]; omega
      obtain ⟨d₄, k₄, e₄, hk₄, w117, r₄, mm₄, rr₄, rm₄, o₄⟩ :=
        dDrop_exec (P := P) d₃ e₃.wb_right h117 h100 h101 (by omega)
      rw [← hx, hk] at hr
      simp only [Bool.false_eq_true, ite_false, Nat.add_zero] at hr
      refine ⟨d₄, _, .ifLtN_false hn e₄, by omega, by omega, fun r a1 a2 a3 a4 => r₄ r a1,
        fun a => ?_, by rw [w117]; ring, ?_, ?_, rr₄, rm₄, o₄⟩
      · rw [mm₄, hm3]
        exact mem1_drop hI.mem ht hB' hk a
      · rw [r₄ _ (by norm_num), g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hI.r118, hr]
      · rw [r₄ _ (by norm_num), g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hI.r119, hr]
    · -- kept
      rw [hk] at hflag
      simp only [ite_true] at hflag
      have hp : d₃.nreg 200101 < d₃.nreg 200115 := by rw [h101, hflag]; omega
      have h119 : d₃.nreg 200119 = B' + 3 * j := by
        rw [g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hI.r119]
      have h118 : d₃.nreg 200118 = j := by
        rw [g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num), hI.r118]
      obtain ⟨d₄, k₄, e₄, hk₄, w119, w117, w118, r₄, mm₄, rr₄, rm₄, o₄⟩ :=
        dKeep_exec (P := P) d₃ e₃.wb_right h119 h117 h118 h100 (by omega) (by omega) (by omega)
      rw [← hx, hk] at hr
      simp only [ite_true] at hr
      refine ⟨d₄, _, .ifLtN_true hp e₄, by omega, by omega, r₄, fun a => ?_,
        by rw [w117]; ring, by rw [w118, hr], by rw [w119, hr]; ring, rr₄, rm₄, o₄⟩
      rw [mm₄, e12, e13, e14, hm3]
      exact mem1_keep hI.mem ht hB' hk a
  have h110 : d₄.nreg 200110 = i := by
    rw [g4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  have h100 : d₄.nreg 200100 = 1 := by
    rw [g4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      g3 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      hI.r100]
  have e₅ := Exec.addN (P := P) e₄.wb_right 200110 200110 200100 (by rw [h110, h100]; omega)
  set d₅ : Config := { d₄ with nreg := upd d₄.nreg 200110 (d₄.nreg 200110 + d₄.nreg 200100) }
    with hd₅
  have g5 : ∀ r, r ≠ 200110 → d₅.nreg r = d₄.nreg r := fun r hr => by rw [hd₅]; simp [hr]
  have v5 : d₅.nreg 200110 = i + 1 := by rw [hd₅]; simp [h110, h100]
  have g : ∀ r, (r < 200110 ∨ 200120 < r) → d₅.nreg r = d.nreg r := fun r hr => by
    rw [g5 r (by omega), g4 r (by omega) (by omega) (by omega) (by omega),
      g3 r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have X' : Exec P W dBody1 d d₅ (k₁ + (k₂ + (k₃ + (k₄ + 1)))) :=
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅)))
  refine ⟨d₅, _, X', e₅.wb_right, ?_, v5, by omega, by omega⟩
  refine ⟨by rw [v5]; omega, by rw [g _ (by norm_num), hI.rK], ?_, ?_, ?_, ?_,
    by rw [g _ (by norm_num), hI.r100], by rw [g _ (by norm_num), hI.r101],
    by rw [g _ (by norm_num), hI.r103], by rw [g _ (by norm_num), hI.r104],
    fun r hr => by rw [g r hr, hI.fr r hr], ?_, ?_, ?_, fun a => ?_⟩
  · rw [v5, g5 _ (by norm_num), g4 _ (by norm_num) (by norm_num) (by norm_num) (by norm_num),
      r₃ _ (by norm_num) (by norm_num), r₂ _ (by norm_num) (by norm_num), v11]
    ring
  · rw [v5, g5 _ (by norm_num), n117]
  · rw [v5, g5 _ (by norm_num), n118]
  · rw [v5, g5 _ (by norm_num), n119]
  · show d₄.rreg = c₀.rreg; rw [rr₄, rr₃, rr₂, rr₁, hI.rr]
  · show d₄.rmem = c₀.rmem; rw [rm₄, rm₃, rm₂, rm₁, hI.rm]
  · show d₄.output = c₀.output; rw [o₄, o₃, o₂, o₁, hI.out]
  · show d₄.nmem a = _; rw [v5, mem4]

/-- **The chord pass.** -/
theorem dLoop1_exec {m₀ : ℕ → ℕ} {li : Bool} {n : ℕ} {L : List (ℕ × ℕ × ℕ)} {B B' X : ℕ}
    (hL : ChordListAt m₀ B L) (hB : B + 3 * L.length ≤ B') (hX : X = B' + 3 * L.length)
    (hXW : X + 2 * L.length + 2 ≤ W) {c₀ d : Config} (hw : WordsBounded W d)
    (hI : Inv1 m₀ li n L B B' X c₀ d) (h0 : d.nreg 200110 = 0) :
    ∃ d' k, Exec P W dLoop1 d d' k ∧ WordsBounded W d' ∧ Inv1 m₀ li n L B B' X c₀ d' ∧
      d'.nreg 200110 = L.length ∧ 13 * L.length ≤ k ∧ k ≤ 47 * L.length + 2 := by
  obtain ⟨d', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 200110) (b := 200002) (body := dBody1)
    (fun d => WordsBounded W d ∧ Inv1 m₀ li n L B B' X c₀ d)
    (fun d => 47 * (L.length - d.nreg 200110)) (fun d => 13 * d.nreg 200110) (fun d hd => hd.1)
    (fun d ⟨hwd, hId⟩ ht => by
      obtain ⟨d', k, e, hw', hI', hi', hk1, hk2⟩ := dBody1_exec hL hB hX hXW hwd hId ht
      have := hId.rK
      refine ⟨d', k, e, ⟨hw', hI'⟩, ?_, ?_⟩
      · rw [hi']; Ξ' this at ht; omega
      · rw [hi']; omega)
    ⟨hw, hI⟩
  have hi := hI'.i_le
  Ξ' hI'.rK at htest
  refine ⟨d', k, e, hw', hI', ⋄, ?_, ?_⟩
  · Ξ' h0 at hψ; have : d'.nreg 200110 = L.length := ⋄
    Ξ' this at hψ; omega
  · Ξ' h0 at hk; omega

end exec

end

end DownBase

end Chazelle.Core
