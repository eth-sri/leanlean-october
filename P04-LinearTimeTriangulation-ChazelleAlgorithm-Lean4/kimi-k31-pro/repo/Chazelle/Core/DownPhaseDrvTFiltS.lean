module

public import Chazelle.Core.DownPhaseDrvTFiltL
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 8000000

/-!
# Down-phase transition (D2), RAM part 5: the filter procedure

`filtS = fSetup ; fLoop`: the set-up allocates `6 + 3 K₀` words at the allocator `A`: the
interior model descriptor `[1, bit]` at `D = A` and the output chord list at `B' = A + 6`, reads
the number `K₀` and the chord area `CB` of the normal form of the top chain (handle in
`coreReg 2`); then the pass writes `transL li n c₀ (triplesOf N)` at `B'` (`filtS_exec`).

`nfAt_robust_bound`: a normal form that is robust below `A` has its header and its chord
records below `A`.
-/

namespace Chazelle.Core

namespace DrvT

open Machine Machine.Stmt Programs BuildRam
open DownBase (rankF tw)

@[expose] public section

/-- **The set-up of the filter.** -/
def fSetup : Stmt := block [.copyN 190021 9999, .constN 190017 1, .constN 190018 0,
  .constN 190041 6, .addN 190022 190021 190041, .loadN 190023 230002, .constN 190042 3,
  .addN 190040 230002 190042, .loadN 190024 190040, .storeN 190021 190017,
  .addN 190040 190021 190017, .storeN 190040 190001, .addN 190043 190023 190023,
  .addN 190043 190043 190023, .addN 9999 190022 190043, .constN 190030 0,
  .copyN 190031 190024, .copyN 190035 190022, .constN 190036 0]

/-- **The filter procedure.** -/
def filtS : Stmt := .seq fSetup fLoop

/-- **A robust normal form lies below the bound**: its header and its chord records. -/
theorem nfAt_robust_bound {A : ℕ} {m : ℕ → ℕ} {B : ℕ} {N : NF}
    (h : Robust A m (fun m' => NFAt m' B N)) :
    B + 11 < A ∧ ∀ i, i < N.chords.length → m (B + 3) + 5 * i + 4 < A := by
  have h1 : B + 11 < A := by
    by_contra hc
    push Not at hc
    have := (h (Function.update m (B + 11) (N.dec.length + 1)) (fun a ha => by
      rw [Function.update_of_ne (by omega)])).2.2.2.2.1
    rw [Function.update_self] at this
    omega
  refine ⟨h1, fun i hi => ?_⟩
  by_contra hc
  push Not at hc
  set a := m (B + 3) + 5 * i + 4 with ha
  have hm : ∀ a', a' < A → Function.update m a ((N.chord i).dn + 1) a' = m a' := fun a' ha' => by
    rw [Function.update_of_ne (by omega)]
  have hN := h _ hm
  have h3 : Function.update m a ((N.chord i).dn + 1) (B + 3) = m (B + 3) := hm _ (by omega)
  have := (hN.2.2.2.2.2.1 i hi).2.2.2.2
  rw [h3, ← ha, Function.update_self] at this
  omega

section exec

variable {P : Polygon} {W : ℕ}

theorem fSetup_exec (c : Config) (hw : WordsBounded W c) {A Bn K₀ CB b : ℕ}
    (hA : c.nreg 9999 = A) (hBn : c.nreg 230002 = Bn) (hBnA : Bn + 11 < A)
    (hK : c.nmem Bn = K₀) (hCB : c.nmem (Bn + 3) = CB) (hb : c.nreg 190001 = b)
    (hroom : A + 6 + 3 * K₀ + 10 ≤ W) :
    ∃ c' k, Exec P W fSetup c c' k ∧ k = 19 ∧ c'.nreg 190021 = A ∧ c'.nreg 190022 = A + 6 ∧
      c'.nreg 190023 = K₀ ∧ c'.nreg 190024 = CB ∧ c'.nreg 190017 = 1 ∧ c'.nreg 190018 = 0 ∧
      c'.nreg 9999 = A + 6 + 3 * K₀ ∧ c'.nreg 190030 = 0 ∧ c'.nreg 190031 = CB ∧
      c'.nreg 190035 = A + 6 ∧ c'.nreg 190036 = 0 ∧
      (∀ r, (r < 190017 ∨ 190043 < r) → r ≠ 9999 → c'.nreg r = c.nreg r) ∧
      (∀ a, c'.nmem a = if a = A + 1 then b else if a = A then 1 else c.nmem a) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hAW : A ≤ W := by omega
  unfold fSetup
  exec_block
  all_goals try omega
  all_goals try (simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA, hBn, hK, hCB, hb]; omega)
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r a1 a2 => ?_, fun a => ?_, rfl,
    rfl, rfl⟩
  all_goals simp (disch := omega) only [Machine.upd_same,
    Machine.upd_other, hA, hBn, hK, hCB, hb]
  all_goals try omega
  all_goals (try simp [Machine.upd_apply])

/-- The records of a robust normal form, as triples. -/
theorem recsT_of_nfAt {A : ℕ} {m m' : ℕ → ℕ} {B : ℕ} {N : NF}
    (h : Robust A m (fun m'' => NFAt m'' B N)) (hm : ∀ a, a < A → m' a = m a) :
    RecsT m' (m (B + 3)) (triplesOf N) := by
  obtain ⟨-, hrec⟩ := nfAt_robust_bound h
  have hN := h.holds
  intro i hi
  have hi' : i < N.chords.length := by unfold triplesOf at hi; simpa using hi
  obtain ⟨e1, e2, e3, -, -⟩ := hN.2.2.2.2.2.1 i hi'
  have hb := hrec i hi'
  have hg : (triplesOf N).getD i (0, 0, 0) = ((N.chord i).h, (N.chord i).lp, (N.chord i).rp) := by
    unfold triplesOf NF.chord
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi',
      Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi', Option.getD_some]
  rw [hg]
  refine ⟨?_, ?_, ?_⟩
  · rwx [hm _ (by omega)]
  · rwx [hm _ (by omega)]
  · rwx [hm _ (by omega)]

/-- The list of a full pass, in memory. -/
theorem chordListAt_memT {m₀ m : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' : ℕ}
    (hm : ∀ a, m a = memT m₀ li n c₀ L₀ B' L₀.length a) :
    ChordListAt m B' (transL li n c₀ L₀) := by
  have hlen : rankF (keepT li n c₀) L₀ L₀.length = (transL li n c₀ L₀).length := by
    rw [DownBase.rankF_length]; unfold transL; rw [List.length_map]
  intro j hj
  have hq : ∀ q, q < 3 → m (B' + 3 * j + q) = tw (transL li n c₀ L₀) (3 * j + q) := by
    intro q hq
    rw [hm]; unfold memT; rw [hlen, ite_eq_left (by omega), show B' + 3 * j + q - B' = 3 * j + q by
      omega]
  refine ⟨?_, ?_, ?_⟩
  · have := hq 0 (by norm_num); rw [Nat.add_zero, Nat.add_zero] at this; rw [this]
    urs tw [show 3 * j % 3 = 0 by omega, show 3 * j / 3 = j by omega]
  · rw [hq 1 (by norm_num)]
    urs tw [show (3 * j + 1) % 3 = 1 by omega, show (3 * j + 1) / 3 = j by omega]
  · rw [hq 2 (by norm_num)]
    urs tw [show (3 * j + 2) % 3 = 2 by omega, show (3 * j + 2) / 3 = j by omega]

/-- **The filter procedure.** -/
theorem filtS_exec (c : Config) (hw : WordsBounded W c) {N : NF} {li : Bool} {n c₀ : ℕ}
    (hN : Robust (c.nreg ALLOC) c.nmem (fun m => NFAt m (c.nreg 230002) N))
    (h01 : c.nreg 190001 = if li then 1 else 0) (h10 : c.nreg 190010 = n - 1)
    (h14 : c.nreg 190014 = c₀) (h15 : c.nreg 190015 = c₀ + (n - 1))
    (h16 : c.nreg 190016 = idxI li n 0)
    (hroom : c.nreg ALLOC + 3 * N.chords.length + 20 ≤ W) :
    ∃ c' k, Exec P W filtS c c' k ∧ 6 + 3 * N.chords.length ≤ k ∧
      k ≤ 54 * N.chords.length + 21 ∧
      c'.nreg 190021 = c.nreg ALLOC ∧ c'.nreg 190022 = c.nreg ALLOC + 6 ∧
      c'.nreg 190036 = (transL li n c₀ (triplesOf N)).length ∧
      c'.nreg ALLOC = c.nreg ALLOC + 6 + 3 * N.chords.length ∧
      ChordListAt c'.nmem (c.nreg ALLOC + 6) (transL li n c₀ (triplesOf N)) ∧
      c'.nmem (c.nreg ALLOC) = 1 ∧ c'.nmem (c.nreg ALLOC + 1) = (if li then 1 else 0) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, (r < 190017 ∨ 190043 < r) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A := c.nreg ALLOC with hA
  set Bn := c.nreg 230002 with hBn
  have hNA := hN.holds
  obtain ⟨hBnA, -⟩ := nfAt_robust_bound hN
  set K₀ := N.chords.length with hK₀
  have hlen₀ : (triplesOf N).length = K₀ := by unfold triplesOf; rw [List.length_map]
  obtain ⟨c₁, k₁, e₁, hk₁, v21, v22, v23, v24, v17, v18, v99, v30, v31, v35, v36, g₁, mm₁,
    rr₁, rm₁, o₁⟩ := fSetup_exec (P := P) c hw (A := A) (Bn := Bn) (K₀ := K₀)
      (CB := c.nmem (Bn + 3)) (b := if li then 1 else 0) rfl rfl hBnA hNA.1 rfl h01 (by omega)
  have hlow₁ : ∀ a, a < A → c₁.nmem a = c.nmem a := fun a ha => by
    rw [mm₁, ite_eq_right (by omega), ite_eq_right (by omega)]
  have hR := recsT_of_nfAt hN hlow₁
  have hI₁ : FInv c₁.nmem li n c₀ (triplesOf N) (c.nmem (Bn + 3)) (A + 6) c₁ c₁ :=
    { i_le := by rwo [v30]
      rK := by rw [v23, hlen₀]
      r31 := by rwring [v31, v30]
      r35 := by rw [v35, v30]; simp [rankF]
      r36 := by rw [v36, v30]; simp [rankF]
      r10 := by rw [g₁ _ (by norm_num) (by norm_num), h10]
      r14 := by rw [g₁ _ (by norm_num) (by norm_num), h14]
      r15 := by rw [g₁ _ (by norm_num) (by norm_num), h15]
      r16 := by rw [g₁ _ (by norm_num) (by norm_num), h16]
      r17 := v17
      r18 := v18
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by rw [v30]; unfold memT; simp [rankF] }
  have hCB : (triplesOf N).length = 0 ∨
      c.nmem (Bn + 3) + 5 * (triplesOf N).length ≤ A + 6 := by
    rcases Nat.eq_zero_or_pos (triplesOf N).length with h0 | hpos
    · left; exact h0
    · right
      have := (nfAt_robust_bound hN).2 (K₀ - 1) (by omega)
      rw [hlen₀]
      have : c.nmem (Bn + 3) + 5 * (K₀ - 1) + 4 < A := this
      omega
  obtain ⟨c₂, k₂, e₂, hw₂, hI₂, h30, hk₂, hk₂'⟩ := fLoop_exec (P := P) hR hCB
    (by rwo [hlen₀]) e₁.wb_right hI₁ v30
  rw [hlen₀] at hk₂ hk₂' h30
  have g₂  := hI₂.fr
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI₂.rr.trans rr₁, hI₂.rm.trans rm₁, hI₂.out.trans o₁⟩
  · rw [g₂ _ (by norm_num), v21]
  · rw [g₂ _ (by norm_num), v22]
  · rw [hI₂.r36, h30, ← hlen₀, DownBase.rankF_length]; unfold transL; rw [List.length_map]
  · show c₂.nreg 9999 = _; rw [g₂ _ (by norm_num), v99]
  · refine chordListAt_memT (m₀ := c₁.nmem) (fun a => ?_)
    rw [hI₂.mem a, h30, hlen₀]
  · rw [hI₂.mem, h30]; unfold memT; rw [ite_eq_right (by omega), mm₁, ite_eq_right (by omega), ite_eq_left rfl]
  · rw [hI₂.mem, h30]; unfold memT; rw [ite_eq_right (by omega), mm₁, ite_eq_left rfl]
  · intro a ha
    rw [hI₂.mem, h30]; unfold memT; rw [ite_eq_right (by omega), hlow₁ a ha]
  · intro r hr hra
    rw [g₂ r (by omega), g₁ r hr hra]

end exec

end

end DrvT

end Chazelle.Core
