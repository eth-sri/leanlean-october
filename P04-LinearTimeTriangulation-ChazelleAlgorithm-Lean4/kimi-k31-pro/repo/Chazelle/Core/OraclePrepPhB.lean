module

public import Chazelle.Core.OraclePrepPhA
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 2000000

/-!
# Lemma 3.6 (WP-H), preprocessing part 29: phase B (the chords of the book)

* `starStage := frS; iS`: the star chords in two fresh chord arrays (`starStage_exec`);
* `zipStage := zS; spS`: the raw zipper pairs in two fresh arrays (`zipStage_exec`);
* `dedupStage := dSort; 60008 := 60003; dEmit`: the raw pairs sorted and appended without
  repetitions to the chord arrays after the star chords (`dedupStage_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey

@[expose] public section

theorem RgMem.congr {m m' : ℕ → ℕ} {AB SB A : ℕ} {σ rg : ℕ → ℕ} (h : RgMem m AB SB A σ rg)
    {X : ℕ} (hX : ∀ a, a < X → m' a = m a) (hS : SB + A ≤ X) (hA : AB + 5 * A ≤ X) :
    RgMem m' AB SB A σ rg :=
  ⟨fun p hp => by rw [hX _ (by omega)]; exact h.seq p hp, h.σ_lt,
    fun j hj => by rw [hX _ (by omega)]; exact h.reg j hj⟩

/-! ## The star chords -/

/-- **The star chords.** -/
def starStage : Stmt := .seq frS iS

theorem starStage_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {NB AB SB A R A₁ : ℕ} {σ rg : ℕ → ℕ} (hM : RgMem c.nmem AB SB A σ rg)
    (hNB : c.nreg 120014 = NB) (h2 : c.nreg 120048 = 2) (hR : c.nmem (NB + 2) = R)
    (hAB : c.nreg 120044 = AB) (hSB : c.nreg 120046 = SB) (hA : c.nreg 120030 = A)
    (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₁) (hNBA : NB + 2 < A₁) (hSA : SB + A ≤ A₁)
    (hABA : AB + 5 * A ≤ A₁) (hρR : ∀ p, p < A → rg (σ p) < R)
    (hW : A₁ + R + A + 2 * chCap A ≤ W) :
    ∃ c' k, Exec P W starStage c c' k ∧ k ≤ 46 * A + 23 ∧
      PF (fun r => BFR r || BIS r) A₁ c c' ∧ c'.nreg 9999 = A₁ + R + 2 * chCap A ∧
      c'.nreg 110072 = A₁ + R ∧ c'.nreg 110073 = A₁ + R + chCap A ∧
      c'.nreg 110074 = (starList (fun q => rg (σ q)) A).length ∧
      PairsAt c'.nmem (A₁ + R) (A₁ + R + chCap A) (starList (fun q => rg (σ q)) A) := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9, a60, afr⟩ := frS_exec (P := P) hw hM hNB h2 hR hAB hSB hA h1 hAl
    hNBA hSA hABA hρR (by omega)
  have hM₁  := hM.congr (X := A₁) F₁.2.2.1 hSA hABA
  have K  := F₁.1
  obtain ⟨c₂, k₂, e₂, hk₂, F₂, b9, b72, b73, -, b74, pairs⟩ := iS_exec (P := P) e₁.wb_right hM₁
    (by rw [K _ (by decide), hAB]) (by rw [K _ (by decide), hSB]) (by rw [K _ (by decide), hA])
    (by rw [K _ (by decide), h1]) a60 a9 (by omega) (by omega) (by omega) hρR afr (by omega)
  refine ⟨c₂, _, .seq e₁ e₂, by omega,
    (F₁.mono (fun r hr => by simp [hr]) le_rfl).trans
      (F₂.mono (fun r hr => by simp [hr]) (by omega)), b9, b72, b73, b74, pairs⟩

/-! ## The raw zipper pairs -/

/-- **The raw zipper pairs.** -/
def zipStage : Stmt := .seq zS spS

theorem zipStage_exec {P : Polygon} {W lo : ℕ} {C : Chain} {N : NF} {V : QV} {c : Config}
    (hw : WordsBounded W c) (h : ZEnv P W lo C N V c) {A₃ : ℕ} (hAl : c.nreg 9999 = A₃)
    (hlo : lo ≤ A₃) (hW : A₃ + 2 * zCap V.A + 10 ≤ W) :
    ∃ c' k, Exec P W zipStage c c' k ∧
      k ≤ 2 * V.A * (5500 * (V.L + 1) + 410) + 3 * (5500 * (V.L + 1) + 262) + 220 ∧
      PF (fun r => BZS r || BSP r) A₃ c c' ∧ c'.nreg 9999 = A₃ + 2 * zCap V.A ∧
      c'.nreg 110293 = A₃ ∧ c'.nreg 110294 = A₃ + zCap V.A ∧
      c'.nreg 110295 = (OracleQ.zipRaw C (Qof P) N).length ∧
      PairsAt c'.nmem A₃ (A₃ + zCap V.A) (OracleQ.zipRaw C (Qof P) N) ∧ ZEnv P W lo C N V c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, a9, a93, a94, a97, a95, pairs₁, Z₁⟩ :=
    zS_exec (P := P) hw h hAl hlo (by omega)
  have hA : V.A = N.arcs.length := h.loc.holds.1.A
  have hlen : (emitted (OracleQ.zipSk C (Qof P) N) V.A ++ emitted (OracleQ.zipEk C (Qof P) N) V.A).length ≤
      2 * V.A := by
    rw [List.length_append]
    have := emitted_length_le (OracleQ.zipSk C (Qof P) N) V.A
    have := emitted_length_le (OracleQ.zipEk C (Qof P) N) V.A
    omega
  obtain ⟨c₂, k₂, e₂, hk₂, r₂, rr₂, rm₂, o₂, cnt, ⟨pairs₂, mem₂⟩, Z₂⟩ := spS_exec (P := P)
    e₁.wb_right Z₁ a93 a94 a95 hlo (by have hz : zCap V.A = 2 * V.A + 5 := rfl; omega)
    (by have hz : zCap V.A = 2 * V.A + 5 := rfl; omega)
  have hz : zCap V.A = 2 * V.A + 5 := rfl
  have hsplen : (OracleQ.zipSp C (Qof P) N).length ≤ 5 := by
    unfold OracleQ.zipSp OracleQ.zipSpO
    exact (List.length_filterMap_le _ _).trans (by simp)
  have hraw : OracleQ.zipRaw C (Qof P) N = (emitted (OracleQ.zipSk C (Qof P) N) V.A ++
      emitted (OracleQ.zipEk C (Qof P) N) V.A) ++ OracleQ.zipSp C (Qof P) N := by
    rwr [hA]
  refine ⟨c₂, _, .seq e₁ e₂, by omega, (F₁.mono (fun r hr => by simp [hr]) le_rfl).trans ?_, by rw [r₂ _ (by decide), a9],
    by rw [r₂ _ (by decide), a93], by rw [r₂ _ (by decide), a94], ?_, ?_, Z₂⟩
  · refine ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => mem₂ a (Or.inl (by omega)),
      fun a _ => by rw [rm₂], by rw [o₂]⟩
    · simp only [Bool.or_eq_false_iff] at hr; exact r₂ r hr.2
    · simp only [Bool.or_eq_false_iff] at hr; exact rr₂ r hr.2
  · rw [cnt, hraw]; simp only [List.length_append]
  · rw [hraw]
    refine PairsAt.append (fun t ht => ?_) pairs₂
    rw [mem₂ _ (Or.inl (by omega)), mem₂ _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact pairs₁ t ht

/-! ## The global frame -/

/-- **The frame of a phase** relative to a fixed bound `lo` (the allocator at the entry of the
preprocessing): registers outside the bands (and the allocator), real registers outside the
bands, memory below `lo`, output. -/
def GF (S : Finset ℕ) (lo : ℕ) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ S → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ S → c'.rreg r = c.rreg r) ∧ (∀ a, a < lo → c'.nmem a = c.nmem a) ∧
    (∀ a, a < lo → c'.rmem a = c.rmem a) ∧ c'.output = c.output

theorem GF.trans {S : Finset ℕ} {lo : ℕ} {c₁ c₂ c₃ : Config} (h₁ : GF S lo c₁ c₂)
    (h₂ : GF S lo c₂ c₃) : GF S lo c₁ c₃ :=
  ⟨fun r a b => (h₂.1 r a b).trans (h₁.1 r a b), fun r a => (h₂.2.1 r a).trans (h₁.2.1 r a),
    fun a ha => (h₂.2.2.1 a ha).trans (h₁.2.2.1 a ha),
    fun a ha => (h₂.2.2.2.1 a ha).trans (h₁.2.2.2.1 a ha), h₂.2.2.2.2.trans h₁.2.2.2.2⟩

theorem FrameN.gf {S : Finset ℕ} {lo : ℕ} {c c' : Config} (h : FrameN S c c')
    (hlo : lo ≤ c.nreg ALLOC) : GF S lo c c' :=
  ⟨h.1, h.2.1, fun a ha => h.2.2.1 a (by omega), fun a ha => h.2.2.2.1 a (by omega), h.2.2.2.2⟩

/-- A stage frame with the written registers in the bands (or the allocator), whose real registers
are preserved. -/
theorem PF.gf {B : ℕ → Bool} {S : Finset ℕ} {lo lo' : ℕ} {c c' : Config} (h : PF B lo' c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∨ r = ALLOC) (hrr : ∀ r, c'.rreg r = c.rreg r)
    (hlo : lo ≤ lo') : GF S lo c c' := by
  refine ⟨fun r hr hra => h.1 r ?_, fun r _ => hrr r, fun a ha => h.2.2.1 a (by omega),
    fun a ha => h.2.2.2.1 a (by omega), h.2.2.2.2⟩
  by_contra h'; simp only [Bool.not_eq_false] at h'
  rcases hB r h' with h'' | h''
  · exact hr h''
  · exact hra h''

/-! ## The deduplication -/

/-- **The sorted, deduplicated zipper pairs after the star chords.** -/
def dedupStage : Stmt := .seq dSort (.seq (.instr (.copyN 60008 60003)) dEmit)

theorem dedupStage_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {CH1 CH2 nI Z1 Z2 n A₄ : ℕ} (h72 : c.nreg 110072 = CH1) (h73 : c.nreg 110073 = CH2)
    (h74 : c.nreg 110074 = nI) (h93 : c.nreg 110293 = Z1) (h94 : c.nreg 110294 = Z2)
    (h95 : c.nreg 110295 = n) (h1 : c.nreg 120011 = 1) (h0 : c.nreg 120012 = 0)
    (hAl : c.nreg 9999 = A₄) (hZ1 : Z1 + n ≤ A₄) (hZ2 : Z2 + n ≤ A₄)
    (hC : CH1 + nI + n ≤ CH2) (hZ : CH2 + nI + n ≤ Z1) (hZ12 : Z1 ≤ Z2)
    (hroom : A₄ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W dedupStage c c' k ∧ k ≤ 47 * n + SortR.sortCost 20 n + 25 ∧
      (∀ r, bandOf r ∉ dBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ dBands → c'.rreg r = c.rreg r) ∧
      (∀ a, (a < CH1 + nI ∨ (CH1 + nI + n ≤ a ∧ a < CH2 + nI) ∨ (CH2 + nI + n ≤ a ∧ a < A₄)) →
        c'.nmem a = c.nmem a) ∧
      (∀ a, a < A₄ → c'.rmem a = c.rmem a) ∧ c'.output = c.output ∧
      A₄ + n ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A₄ + n + SortR.sortCost 20 n ∧
      c'.nreg 60001 = CH1 ∧ c'.nreg 60002 = CH2 ∧ c'.nreg 60008 = nI ∧
      ∃ D : List (ℕ × ℕ), c'.nreg 60003 = nI + D.length ∧ D.length ≤ n ∧
        PairsAt c'.nmem (CH1 + nI) (CH2 + nI) D ∧ D.Nodup ∧
        ∀ x, x ∈ D ↔ ∃ i, i < n ∧ (c.nmem (Z1 + i), c.nmem (Z2 + i)) = x := by
  have hAL : ALLOC = 9999 := rfl
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, al1a, al1b, v1, v2, v3, v4, v5, v6, sb1, sb2, hsort, hsurj, hlt⟩ :=
    dSort_exec (P := P) hw h72 h73 h74 h93 h94 h95 h1 hAl hZ1 hZ2 hroom
  have hA₄ : c.nreg ALLOC = A₄ := hAl
  have e₂ := Exec.copyN (P := P) e₁.wb_right 60008 60003
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 60008 (c₁.nreg 60003) } with hc₂
  have R₂ : ∀ r, r ≠ 60008 → c₂.nreg r = c₁.nreg r := fun r hr => by
    rw [hc₂]; config_simp; rw [upd_other _ _ _ hr]
  have g11 : c₁.nreg 120011 = 1 := by
    rw [F₁.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide), h1]
  have g12 : c₁.nreg 120012 = 0 := by
    rw [F₁.1 _ (by simp [dBands, bSort, bDecomp, bOPrep, bandOf]) (by decide), h0]
  have hW9 : c₁.nreg 9999 ≤ W := e₁.wb_right.1 9999
  have hDE : DEnv (c₁.nreg 60007) Z1 Z2 n (fun t => c₁.nmem (c₁.nreg 60007 + t))
      (fun i => c.nmem (Z1 + i)) (fun i => c.nmem (Z2 + i)) c₂ :=
    ⟨by rw [R₂ _ (by decide), v4], by rw [R₂ _ (by decide), v5], R₂ _ (by decide),
      by rw [R₂ _ (by decide), g11], by rw [R₂ _ (by decide), g12],
      ⟨fun t _ => rfl, hlt, fun i hi => F₁.2.2.1 _ (by rwo [hA₄]),
        fun i hi => F₁.2.2.1 _ (by rwo [hA₄])⟩⟩
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, cnt₃, pairs₃, mem₃, rm₃, o₃⟩ := dEmit_exec (P := P) e₂.wb_right
    hDE (by rw [R₂ _ (by decide), v1]) (by rw [R₂ _ (by decide), v2])
    (by rw [R₂ _ (by decide), v3]) (by rw [R₂ _ (by decide), v6]) hC hZ hZ12 (by omega)
    (by omega)
  set D := emitted (dedupF n (fun i => (c.nmem (Z1 + i), c.nmem (Z2 + i)))
    (fun t => c₁.nmem (c₁.nreg 60007 + t))) n with hD
  have hDl : D.length ≤ n := emitted_length_le _ _
  have K3 : ∀ r, BDB r = false → r ≠ 60010 → r ≠ 60003 → r ≠ 60014 → r ≠ 60008 →
      c₃.nreg r = c₁.nreg r := fun r a b d e f => by rw [r₃ r a b d e, R₂ r f]
  refine ⟨c₃, _, .seq e₁ (.seq e₂ e₃), by omega, fun r hr hra => ?_, fun r hr => ?_,
    fun a ha => ?_, fun a ha => by rw [rm₃, F₁.2.2.2.1 a (by rwx [hA₄])],
    by rw [o₃, F₁.2.2.2.2], ?_, ?_, ?_, ?_, ?_, D, ?_, hDl, pairs₃, dedup_nodup hsort,
    fun x => mem_dedup hsurj hlt⟩
  · have h6 : ¬ bandOf r = 6 := fun h => hr (by simp [dBands, bDecomp, h])
    unfold bandOf at h6
    rw [K3 r (by sio only [BDB, decide_eq_false_iff_not]) (by omega) (by omega)
      (by omega) (by omega), F₁.1 r hr hra]
  · have h6 : ¬ bandOf r = 6 := fun h => hr (by simp [dBands, bDecomp, h])
    unfold bandOf at h6
    rw [rr₃ r (by sio only [BDB, decide_eq_false_iff_not])]
    exact F₁.2.1 r hr
  · rw [mem₃ a (by omega)]
    exact F₁.2.2.1 a (by rwo [hA₄])
  · rw [hAL, K3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact al1a
  · rw [hAL, K3 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact al1b
  · rw [K3 _ (by decide) (by decide) (by decide) (by decide) (by decide), v1]
  · rw [K3 _ (by decide) (by decide) (by decide) (by decide) (by decide), v2]
  · rw [r₃ _ (by decide) (by decide) (by decide) (by decide)]; rw [hc₂]; config_simp; exact v3
  · rw [cnt₃]

end

end OracleR

end Chazelle.Core
