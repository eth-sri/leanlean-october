module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvTFiltL

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
      ram_simp)).2.2.2.2.1
    simp_all
  refine ⟨h1, fun i hi => ?_⟩
  by_contra hc
  push Not at hc
  set a := m (B + 3) + 5 * i + 4 with ha
  have hm : ∀ a', a' < A → Function.update m a ((N.chord i).dn + 1) a' = m a' := fun a' ha' => by
    ram_simp
  have hN := h _ hm
  have h3 : Function.update m a ((N.chord i).dn + 1) (B + 3) = m (B + 3) := hm _ (by omega)
  have := (hN.2.2.2.2.2.1 i hi).2.2.2.2
  simp_all

section exec

variable {P : Polygon} {W : ℕ}

set_option maxHeartbeats 8000000 in
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
  all_goals (try simp only [Machine.upd_apply])

/-- The records of a robust normal form, as triples. -/
theorem recsT_of_nfAt {A : ℕ} {m m' : ℕ → ℕ} {B : ℕ} {N : NF}
    (h : Robust A m (fun m'' => NFAt m'' B N)) (hm : ∀ a, a < A → m' a = m a) :
    RecsT m' (m (B + 3)) (triplesOf N) := by
  obtain ⟨-, hrec⟩ := nfAt_robust_bound h
  have hN := h.holds
  intro i hi
  have hi' : i < N.chords.length := by grind [triplesOf]
  obtain ⟨e1, e2, e3, -, -⟩ := hN.2.2.2.2.2.1 i hi'
  grind [triplesOf, NF.chord, List.getD_eq_getElem?_getD, List.getElem?_map, Option.map_some, Option.getD_some]

/-- The list of a full pass, in memory. -/
theorem chordListAt_memT {m₀ m : ℕ → ℕ} {li : Bool} {n c₀ : ℕ} {L₀ : List (ℕ × ℕ × ℕ)} {B' : ℕ}
    (hm : ∀ a, m a = memT m₀ li n c₀ L₀ B' L₀.length a) :
    ChordListAt m B' (transL li n c₀ L₀) := by
  have hlen : rankF (keepT li n c₀) L₀ L₀.length = (transL li n c₀ L₀).length := by
    core_grind
  intro j hj
  have hq : ∀ q, q < 3 → m (B' + 3 * j + q) = tw (transL li n c₀ L₀) (3 * j + q) := by
    grind [memT]
  refine ⟨?_, ?_, ?_⟩
  · have := hq 0 (by norm_num); rw [Nat.add_zero, Nat.add_zero] at this; grind [tw]
  · grind [tw]
  grind [tw]

set_option maxHeartbeats 4000000 in
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
  have hlen₀ : (triplesOf N).length = K₀ := by core_grind
  obtain ⟨c₁, k₁, e₁, hk₁, v21, v22, v23, v24, v17, v18, v99, v30, v31, v35, v36, g₁, mm₁,
    rr₁, rm₁, o₁⟩ := fSetup_exec (P := P) c hw (A := A) (Bn := Bn) (K₀ := K₀)
      (CB := c.nmem (Bn + 3)) (b := if li then 1 else 0) rfl rfl hBnA hNA.1 rfl h01 (by omega)
  have hlow₁ : ∀ a, a < A → c₁.nmem a = c.nmem a := fun a ha => by
    ram_grind
  have hR := recsT_of_nfAt hN hlow₁
  have hI₁ : FInv c₁.nmem li n c₀ (triplesOf N) (c.nmem (Bn + 3)) (A + 6) c₁ c₁ :=
    { i_le := by omega
      rK := by omega
      r31 := by omega
      r35 := by grind [rankF]
      r36 := by grind [rankF]
      r10 := by ram_grind
      r14 := by ram_grind
      r15 := by ram_grind
      r16 := by ram_grind
      r17 := v17
      r18 := v18
      fr := fun _ _ => rfl
      rr := rfl
      rm := rfl
      out := rfl
      mem := fun a => by grind [memT, rankF] }
  have hCB : (triplesOf N).length = 0 ∨
      c.nmem (Bn + 3) + 5 * (triplesOf N).length ≤ A + 6 := by
    rcases Nat.eq_zero_or_pos (triplesOf N).length with h0 | hpos
    · omega
    · right
      have := (nfAt_robust_bound hN).2 (K₀ - 1) (by omega)
      omega
  obtain ⟨c₂, k₂, e₂, hw₂, hI₂, h30, hk₂, hk₂'⟩ := fLoop_exec (P := P) hR hCB
    (by omega) e₁.wb_right hI₁ v30
  rw [hlen₀] at hk₂ hk₂' h30
  have g₂ : ∀ r, (r < 190030 ∨ 190039 < r) → c₂.nreg r = c₁.nreg r := hI₂.fr
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hI₂.rr.trans rr₁, hI₂.rm.trans rm₁, hI₂.out.trans o₁⟩
  · ram_grind
  · ram_grind
  · rw [hI₂.r36, h30, ← hlen₀, DownBase.rankF_length]; grind [transL, List.length_map]
  · ram_grind
  · refine chordListAt_memT (m₀ := c₁.nmem) (fun a => ?_)
    rw [hI₂.mem a, h30, hlen₀]
  · rw [hI₂.mem, h30]; grind [memT]
  · rw [hI₂.mem, h30]; grind [memT]
  · intro a ha
    rw [hI₂.mem, h30]; grind [memT]
  ram_grind

end exec

end

end DrvT

end Chazelle.Core
