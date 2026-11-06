module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildEvCmp
public import Chazelle.Core.SortRam

/-!
# WP-C (BuildNF), RAM part 4: the event records and the code list

For a chord list of length `K` at `B` (`ChordListAt`), `recLoop` writes the records of the `2K`
event codes at `T` (`RecsAt`: edge and height code of `wposOf`, parity, chord) and the code list
`0, 1, …, 2K - 1` at `S₀ = T + 8K` (the input of the sort).

Registers: `r43020` the chord counter, `r43021 … r43024` the running addresses and the next code,
`r43025 … r43028` scratch, `r43010 = 0`, `r43011 = 1`, `r43002 = K`.
-/

namespace Chazelle.Core

namespace BuildRam

open Machine Machine.Stmt Programs SignK
open BuildNF (wposOf)

@[expose] public section

/-- The word `q` of the record table. -/
def recWord (L : List (ℕ × ℕ × ℕ)) (q : ℕ) : ℕ :=
  if q % 4 = 0 then (wposOf L (q / 4)).edge else if q % 4 = 1 then (wposOf L (q / 4)).hgt
  else if q % 4 = 2 then q / 4 % 2 else q / 4 / 2

/-- One chord: its two records and its two codes. -/
def recBody : Stmt :=
  block [.loadN 43025 43021, .addN 43021 43021 43011, .loadN 43026 43021,
    .addN 43021 43021 43011, .loadN 43027 43021, .addN 43021 43021 43011,
    .addN 43028 43025 43011,
    .storeN 43022 43026, .addN 43022 43022 43011, .storeN 43022 43028, .addN 43022 43022 43011,
    .storeN 43022 43010, .addN 43022 43022 43011, .storeN 43022 43020, .addN 43022 43022 43011,
    .storeN 43022 43027, .addN 43022 43022 43011, .storeN 43022 43028, .addN 43022 43022 43011,
    .storeN 43022 43011, .addN 43022 43022 43011, .storeN 43022 43020, .addN 43022 43022 43011,
    .storeN 43023 43024, .addN 43023 43023 43011, .addN 43024 43024 43011,
    .storeN 43023 43024, .addN 43023 43023 43011, .addN 43024 43024 43011,
    .addN 43020 43020 43011]

/-- The record loop. -/
def recLoop : Stmt := .whileLtN 43020 43002 recBody

/-- The record words of chord `i`. -/
theorem recWord_eq (L : List (ℕ × ℕ × ℕ)) (i k : ℕ) (hk : k < 8) :
    recWord L (8 * i + k) =
      if k = 0 then (L.getD i (0, 0, 0)).2.1 else if k = 1 then (L.getD i (0, 0, 0)).1 + 1
      else if k = 2 then 0 else if k = 3 then i else if k = 4 then (L.getD i (0, 0, 0)).2.2
      else if k = 5 then (L.getD i (0, 0, 0)).1 + 1 else if k = 6 then 1 else i := by
  have e0 : (2 * i) % 2 = 0 := by omega
  have e1 : (2 * i + 1) % 2 = 1 := by omega
  have d0 : 2 * i / 2 = i := by omega
  have d1 : (2 * i + 1) / 2 = i := by omega
  unfold recWord
  interval_cases k
  · rw [show (8 * i + 0) % 4 = 0 by omega, show (8 * i + 0) / 4 = 2 * i by omega]
    grind [wposOf, BuildRegions.crec, CRec.lpos, recOf]
  · rw [show (8 * i + 1) % 4 = 1 by omega, show (8 * i + 1) / 4 = 2 * i by omega]
    grind [wposOf, BuildRegions.crec, CRec.lpos, recOf]
  · rw [show (8 * i + 2) % 4 = 2 by omega, show (8 * i + 2) / 4 = 2 * i by omega]
    simp [e0]
  · rw [show (8 * i + 3) % 4 = 3 by omega, show (8 * i + 3) / 4 = 2 * i by omega]
    simp [d0]
  · rw [show (8 * i + 4) % 4 = 0 by omega, show (8 * i + 4) / 4 = 2 * i + 1 by omega]
    grind [wposOf, BuildRegions.crec, CRec.rpos, recOf]
  · rw [show (8 * i + 5) % 4 = 1 by omega, show (8 * i + 5) / 4 = 2 * i + 1 by omega]
    grind [wposOf, BuildRegions.crec, CRec.rpos, recOf]
  · rw [show (8 * i + 6) % 4 = 2 by omega, show (8 * i + 6) / 4 = 2 * i + 1 by omega]
    simp [e1]
  · rw [show (8 * i + 7) % 4 = 3 by omega, show (8 * i + 7) / 4 = 2 * i + 1 by omega]
    simp [d1]

/-- The record table gives `RecsAt`. -/
theorem recsAt_of {m : ℕ → ℕ} {T : ℕ} {L : List (ℕ × ℕ × ℕ)}
    (h : ∀ q, q < 8 * L.length → m (T + q) = recWord L q) : RecsAt m T L := by
  intro c hc
  have w : ∀ k, k < 4 → m (T + 4 * c + k) = recWord L (4 * c + k) := fun k hk => by
    grind
  
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := w 0 (by norm_num); rw [Nat.add_zero] at this
    grind [recWord]
  · grind [recWord]
  · grind [recWord]
  grind [recWord]

section exec

variable {P : Polygon} {W : ℕ}

/-- The memory after `i` chords. -/
def recMem (m₀ : ℕ → ℕ) (L : List (ℕ × ℕ × ℕ)) (T S₀ i a : ℕ) : ℕ :=
  if T ≤ a ∧ a < T + 8 * i then recWord L (a - T)
  else if S₀ ≤ a ∧ a < S₀ + 2 * i then a - S₀ else m₀ a

/-- The memory step of the record loop. -/
theorem recStep_mem {m₀ m : ℕ → ℕ} {L : List (ℕ × ℕ × ℕ)} {T S₀ i : ℕ}
    (hm : ∀ a, m a = recMem m₀ L T S₀ i a) (hi : i < L.length)
    {a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 : ℕ}
    (e0 : a0 = T + 8 * i) (e1 : a1 = T + 8 * i + 1) (e2 : a2 = T + 8 * i + 2)
    (e3 : a3 = T + 8 * i + 3) (e4 : a4 = T + 8 * i + 4) (e5 : a5 = T + 8 * i + 5)
    (e6 : a6 = T + 8 * i + 6) (e7 : a7 = T + 8 * i + 7) (e8 : a8 = S₀ + 2 * i)
    (e9 : a9 = S₀ + 2 * i + 1)
    (w0 : v0 = (L.getD i (0, 0, 0)).2.1) (w1 : v1 = (L.getD i (0, 0, 0)).1 + 1) (w2 : v2 = 0)
    (w3 : v3 = i) (w4 : v4 = (L.getD i (0, 0, 0)).2.2) (w5 : v5 = (L.getD i (0, 0, 0)).1 + 1)
    (w6 : v6 = 1) (w7 : v7 = i) (w8 : v8 = 2 * i) (w9 : v9 = 2 * i + 1)
    (hS : S₀ = T + 8 * L.length) (a : ℕ) :
    upd (upd (upd (upd (upd (upd (upd (upd (upd (upd m a0 v0) a1 v1) a2 v2) a3 v3) a4 v4) a5 v5)
      a6 v6) a7 v7) a8 v8) a9 v9 a = recMem m₀ L T S₀ (i + 1) a := by
  subst a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 S₀
  simp only [upd_apply]
  rw [hm a]
  unfold recMem
  have hr : a < T ∨ (T ≤ a ∧ a < T + 8 * i) ∨ (∃ k, k < 8 ∧ a = T + 8 * i + k) ∨
      (T + 8 * i + 8 ≤ a ∧ a < T + 8 * L.length) ∨
      (T + 8 * L.length ≤ a ∧ a < T + 8 * L.length + 2 * i) ∨ a = T + 8 * L.length + 2 * i ∨
      a = T + 8 * L.length + 2 * i + 1 ∨ T + 8 * L.length + 2 * i + 2 ≤ a := by
    by_cases h : T + 8 * i ≤ a ∧ a < T + 8 * i + 8
    · exact Or.inr (Or.inr (Or.inl ⟨a - (T + 8 * i), by omega, by omega⟩))
    · omega
  rcases hr with h | h | ⟨k, hk, rfl⟩ | h | h | h | h | h
  · repeat' (first | rw [if_pos (by omega)] | rw [ite_eq_right (by omega)])
  · repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
  · interval_cases k <;>
    · repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
      first
        | (rw [show T + 8 * i + 0 - T = 8 * i + 0 by omega, recWord_eq L i 0 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 1 - T = 8 * i + 1 by omega, recWord_eq L i 1 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 2 - T = 8 * i + 2 by omega, recWord_eq L i 2 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 3 - T = 8 * i + 3 by omega, recWord_eq L i 3 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 4 - T = 8 * i + 4 by omega, recWord_eq L i 4 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 5 - T = 8 * i + 5 by omega, recWord_eq L i 5 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 6 - T = 8 * i + 6 by omega, recWord_eq L i 6 (by norm_num)]; rfl)
        | (rw [show T + 8 * i + 7 - T = 8 * i + 7 by omega, recWord_eq L i 7 (by norm_num)]; rfl)
  · repeat' (first | rw [if_pos (by omega)] | rw [ite_eq_right (by omega)])
  · repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
  · repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
    omega
  · repeat' (first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)])
    omega
  · repeat' (first | rw [if_pos (by omega)] | rw [ite_eq_right (by omega)])

/-- The invariant of the record loop. -/
structure RecInv (m₀ : ℕ → ℕ) (L : List (ℕ × ℕ × ℕ)) (B T S₀ : ℕ) (c₀ d : Config) : Prop where
  i_le : d.nreg 43020 ≤ L.length
  rK : d.nreg 43002 = L.length
  r0 : d.nreg 43010 = 0
  r1 : d.nreg 43011 = 1
  a21 : d.nreg 43021 = B + 3 * d.nreg 43020
  a22 : d.nreg 43022 = T + 8 * d.nreg 43020
  a23 : d.nreg 43023 = S₀ + 2 * d.nreg 43020
  a24 : d.nreg 43024 = 2 * d.nreg 43020
  fr : ∀ r, (r < 43020 ∨ 43028 < r) → d.nreg r = c₀.nreg r
  rr : d.rreg = c₀.rreg
  rm : d.rmem = c₀.rmem
  out : d.output = c₀.output
  mem : ∀ a, d.nmem a = recMem m₀ L T S₀ (d.nreg 43020) a

/-- **The record loop.** -/
theorem recLoop_exec {m₀ : ℕ → ℕ} {L : List (ℕ × ℕ × ℕ)} {B T S₀ : ℕ} (hL : ChordListAt m₀ B L)
    (hB : B + 3 * L.length ≤ T) (hS : S₀ = T + 8 * L.length) (hSW : S₀ + 2 * L.length ≤ W)
    (hhW : ∀ x ∈ L, x.1 + 1 ≤ W) {c₀ c : Config} (hw : WordsBounded W c)
    (hI : RecInv m₀ L B T S₀ c₀ c) (h0 : c.nreg 43020 = 0) :
    ∃ c' k, Exec P W recLoop c c' k ∧ k ≤ 32 * L.length + 2 ∧ 30 * L.length ≤ k ∧
      WordsBounded W c' ∧
      RecInv m₀ L B T S₀ c₀ c' ∧ c'.nreg 43020 = L.length := by
  obtain ⟨c', k, e, ⟨hw', hI'⟩, htest, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P) (W := W)
    (a := 43020) (b := 43002) (body := recBody)
    (fun d => WordsBounded W d ∧ RecInv m₀ L B T S₀ c₀ d)
    (fun d => 32 * (L.length - d.nreg 43020)) (fun d => 30 * d.nreg 43020) (fun d hd => hd.1)
    (fun d ⟨hwd, hId⟩ htest => by
      rw [hId.rK] at htest
      obtain ⟨i, hi⟩ : ∃ i, d.nreg 43020 = i := ⟨_, rfl⟩
      rw [hi] at htest
      have ha21 := hId.a21; have ha22 := hId.a22; have ha23 := hId.a23; have ha24 := hId.a24
      rw [hi] at ha21 ha22 ha23 ha24
      have o := hId.r1; have z := hId.r0
      obtain ⟨l1, l2, l3⟩ := hL i htest
      have hx : L.getD i (0, 0, 0) ∈ L := BuildOrder.getD_mem htest
      have hh := hhW _ hx
      have m21 : d.nmem (B + 3 * i) = (L.getD i (0, 0, 0)).1 := by
        rw [hId.mem, recMem, ite_eq_right (by omega), ite_eq_right (by omega), l1]
      have m22 : d.nmem (B + 3 * i + 1) = (L.getD i (0, 0, 0)).2.1 := by
        rw [hId.mem, recMem, ite_eq_right (by omega), ite_eq_right (by omega), l2]
      have m23 : d.nmem (B + 3 * i + 2) = (L.getD i (0, 0, 0)).2.2 := by
        rw [hId.mem, recMem, ite_eq_right (by omega), ite_eq_right (by omega), l3]
      unfold recBody
      exec_block
      all_goals first
        | (config_simp; simp (config := { failIfUnchanged := false }) only [hi, ha21, ha22, ha23,
            ha24, o, z, m21, m22, m23, hS]; omega)
        | skip
      have fr := hId.fr; have hm := hId.mem; simp only [hi] at hm
      refine ⟨⟨‹WordsBounded _ _›, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, hId.rr, hId.rm,
        hId.out, fun a => ?_⟩⟩, ?_, ?_⟩
      all_goals config_simp
      · omega_nf
      · exact hId.rK
      · exact z
      · exact o
      · omega_nf
      · omega_nf
      · omega_nf
      · omega_nf
      · simp (disch := omega) only [upd_other]; ram_simp
      · rw [hi, o]
        refine recStep_mem hm htest ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hS a <;>
          ram_simp
      · omega_nf
      · omega_nf)
    ⟨hw, hI⟩
  refine ⟨c', k, e, ?_, ?_, hw', hI', ?_⟩
  · rw [h0] at hk; omega
  · have := hI'.i_le; rw [hI'.rK] at htest; rw [h0] at hψ; omega
  · have := hI'.i_le; rw [hI'.rK] at htest; omega

end exec

end

end BuildRam

end Chazelle.Core
