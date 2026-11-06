module

public import Chazelle.Core.FuseAsmCtx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
set_option maxHeartbeats 16000000

/-!
# WP-F fusion assembly, part 21: the query lists of the two sides

* `endPart S G`: the chord-end queries of the normal form whose handle is in register `G`,
  written at the allocator (base saved in `S`, count in `70128`) (`endPart_exec`).
* `sideQ₀`: the query list of side `0`: `endQL N₁.chords ++ (v₁ ++ v₀ ++ t₁ ++ t₀ ++ k₀)`;
  `sideQ₁`: the query list of side `1`: `endQL N₂.chords ++ (t'₁ ++ t'₀ ++ k₁)`.
-/

namespace Chazelle.Core

namespace FuseAsm

open Machine Machine.Stmt Programs SignK SweepPrim MergeAsm

@[expose] public section

/-- Initialisation of the chord-end queries. -/
def sqInit (S G : ℕ) : Stmt := block [.constN 70105 1, .constN 70106 5, .constN 70108 0,
  .copyN S ALLOC, .loadN 70100 G, .constN 70131 3, .addN 70132 G 70131, .loadN 70101 70132,
  .constN 70102 0]

/-- The query count after the chord-end queries. -/
def sqMid : Stmt := block [.addN 70128 70100 70100]

/-- The chord-end queries. -/
def endPart (S G : ℕ) : Stmt := .seq (sqInit S G) (.seq qlLoop sqMid)

/-- The registers written by `endPart S G`. -/
def Bend (S r : ℕ) : Bool := decide (70100 ≤ r ∧ r ≤ 70108) || r == 70128 || r == 70131 ||
  r == 70132 || r == S || r == ALLOC

theorem endPart_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c) {S G : ℕ}
    (hS : S = 70150 ∨ S = 70151) (hGr : G = 70003 ∨ G = 70004) {A : ℕ} {N : NF}
    {M : Model} (hN : NFWithin c.nmem (c.nreg G) A N) (hA : A ≤ c.nreg ALLOC)
    (hIs : IsNF M (Qof P) N) (hnW : P.n ≤ W)
    (hroom : c.nreg ALLOC + 22 * N.nChords + 20 ≤ W) :
    ∃ c' k, Exec P W (endPart S G) c c' k ∧ k ≤ 22 * N.nChords + 13 ∧
      6 * N.nChords ≤ k ∧
      c'.nreg S = c.nreg ALLOC ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (endQL N.chords).length ∧
      c'.nreg 70128 = (endQL N.chords).length ∧
      c'.nreg 70105 = 1 ∧ c'.nreg 70108 = 0 ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (endQL N.chords) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, Bend S r = false → c'.nreg r = c.nreg r) ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨A₀, hA₀⟩ : ∃ x, c.nreg ALLOC = x := ⟨_, rfl⟩
  have hA'  := hA₀
  obtain ⟨Hd, hHd⟩ : ∃ x, c.nreg G = x := ⟨_, rfl⟩
  rw [hHd] at hN
  have hat := hN.nfAt
  obtain ⟨hK, -, -, -, -, hch, -⟩ := hat
  obtain ⟨hB7, hch', -⟩ := Gran.nf_areas hN
  set K := N.nChords with hKdef
  have hKc  := hK
  obtain ⟨CB, hCB⟩ : ∃ x, c.nmem (Hd + 3) = x := ⟨_, rfl⟩
  rw [hCB] at hch hch'
  obtain ⟨c₁, k₁, e₁, hk₁, q⟩ : ∃ c₁ k₁, Exec P W (sqInit S G) c c₁ k₁ ∧ k₁ = 9 ∧
      (c₁.nreg 70105 = 1 ∧ c₁.nreg 70106 = 5 ∧ c₁.nreg 70108 = 0 ∧ c₁.nreg S = A₀ ∧
        c₁.nreg 70100 = K ∧ c₁.nreg 70101 = CB ∧ c₁.nreg 70102 = 0 ∧ c₁.nreg ALLOC = A₀ ∧
        (∀ r, (r < 70100 ∨ 70108 < r) → r ≠ S → r ≠ 70131 → r ≠ 70132 → c₁.nreg r = c.nreg r) ∧
        c₁.nmem = c.nmem ∧ c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output) := by
    unfold sqInit
    rcases hS with rfl | rfl <;> rcases hGr with rfl | rfl <;>
    · exec_block
      all_goals try omega
      all_goals try (simp (disch := omega) only [Machine.upd_same,
        Machine.upd_other, hHd]; omega)
      refine ⟨rfl, ?_⟩
      simp (disch := omega) only [Machine.upd_same, Machine.upd_other, hHd, hA', ALLOC]
      and_intros
      all_goals first | trivial | exact hKc | exact hCB |
        (intro r h1 h2 h3 h4; simp (disch := omega) only [Machine.upd_other])
  obtain ⟨q05, q06, q08, qS, q00, q01, q02, qA, qr, qm, qrr, qrm, qo⟩ := q
  have w₁ := e₁.wb_right
  -- the loop
  have hIs' := hIs
  obtain ⟨-, -, -, -, -, -, -, -, -, hhQ, -⟩ := hIs'
  have hn : (Qof P).n = P.n := shear_n _ _
  have I0 : QLI W K CB A₀ c₁ c₁ := ⟨w₁, by omega, by rwring [q01, q02], by rwring [qA, q02],
    fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl, fun i hi => by omega, rfl, rfl, rfl⟩
  obtain ⟨c₂, k₂, e₂, hk₂, hk₂', I₂, h₂⟩ := qlLoop_exec (P := P) q05 q06 q08 q00
    (fun i hi => by have := hch' i hi; omega)
    (fun i hi => by
      rw [qm, (hch i hi).1]
      have := hhQ i hi; rwo [hn] at this)
    (by omega) (by omega) K c₁ I0 (by omega)
  have w₂ := I₂.wb
  have g₂ : ∀ r, r ≠ 70101 → r ≠ 70102 → r ≠ 70103 → r ≠ 70104 → r ≠ 70107 → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := I₂.regs
  have r00 : c₂.nreg 70100 = K := by
    rw [g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), q00]
  obtain ⟨c₃, k₃, e₃, hk₃, t28, tr, tm, trr, trm, tou⟩ : ∃ c₃ k₃, Exec P W sqMid c₂ c₃ k₃ ∧
      k₃ = 1 ∧ c₃.nreg 70128 = 2 * K ∧ (∀ r, r ≠ 70128 → c₃.nreg r = c₂.nreg r) ∧
      c₃.nmem = c₂.nmem ∧ c₃.rreg = c₂.rreg ∧ c₃.rmem = c₂.rmem ∧ c₃.output = c₂.output := by
    unfold sqMid
    exec_block
    all_goals try (sio only [r00])
    refine ⟨rfl, ?_, fun r h => ?_, rfl, rfl, rfl, rfl⟩
    all_goals simp (disch := omega) only [Machine.upd_same, Machine.upd_other,
      r00]
    ring
  have ex : Exec P W (endPart S G) c c₃ (k₁ + (k₂ + k₃)) := .seq e₁ (.seq e₂ e₃)
  have hlen : (endQL N.chords).length = 2 * K := endQL_length _
  have hS' : S ≠ ALLOC := by rcases hS with rfl | rfl <;> decide
  refine ⟨c₃, _, ex, by omega, by omega, ?_, ?_, by rw [t28, hlen], ?_, ?_, ?_, fun a ha => ?_,
    fun r hr => ?_, by rw [trr, I₂.rr, qrr], by rw [trm, I₂.rm, qrm], by rw [tou, I₂.out, qo]⟩
  · rw [tr _ (by rcases hS with rfl | rfl <;> decide), g₂ _ (by rcases hS with rfl | rfl <;> decide)
      (by rcases hS with rfl | rfl <;> decide) (by rcases hS with rfl | rfl <;> decide)
      (by rcases hS with rfl | rfl <;> decide) (by rcases hS with rfl | rfl <;> decide) hS', qS,
      hA₀]
  · rwring [tr _ (by decide), I₂.alloc, h₂, hlen, hA₀]
  · rw [tr _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), q05]
  · rw [tr _ (by decide), g₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), q08]
  · rw [tm, hA₀]
    have hdone := I₂.done
    rw [h₂] at hdone
    refine chordList_endQL (m₀ := c₁.nmem) (CB := CB) (fun i hi => ?_) (hdone)
    rw [qm]
    obtain ⟨d0, d1, d2, -, -⟩ := hch i hi
    exact ⟨d0, d1, d2⟩
  · rw [tm, I₂.low a (by omega), qm]
  · have hr' := hr
    simp [Bend, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr'
    rw [tr r (by omega), g₂ r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      qr r (by omega) (by omega) (by omega) (by omega)]

end

end FuseAsm

end Chazelle.Core
