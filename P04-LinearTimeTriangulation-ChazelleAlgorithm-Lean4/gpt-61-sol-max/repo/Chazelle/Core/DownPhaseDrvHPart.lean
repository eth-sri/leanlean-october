module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvHEmit

/-!
# Down-phase driver, host RAM (D3a), part 5: the partner search

`partS_exec`: `partS` computes `partner N r x` (the other end of the first exit chord of region
`r` attached at `x`, or `x`) by a loop over the region's chord list with a found bit, as
`List.find?` (`partner_eq`, `find_take_succ`); one chord is tested by `chTest_exec`.
-/

namespace Chazelle.Core

namespace DrvH

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

section exec

variable {P : Polygon} {W : ℕ}

section
variable {c : CRec} {x : WPos}
theorem lpos_eq_iff : c.lpos = x ↔ c.lp = x.edge ∧ c.h + 1 = x.hgt := by
  cases x; simp [CRec.lpos]

theorem rpos_eq_iff : c.rpos = x ↔ c.rp = x.edge ∧ c.h + 1 = x.hgt := by
  cases x; simp [CRec.rpos]


end

theorem chTest_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n : ℕ} {N : NF} {x : WPos}
    {i v : ℕ} (hK : Kst n li d) (h46 : d.nreg 215046 = x.edge) (h47 : d.nreg 215047 = x.hgt)
    (h55 : d.nreg 215055 = v) (hi : d.nmem (d.nreg 215027 + (d.nreg 215029 + v)) = i)
    (hiW : d.nreg 215027 + (d.nreg 215029 + v) ≤ W)
    (hh : d.nmem (d.nreg 215025 + 5 * i) = (N.chord i).h)
    (hlp : d.nmem (d.nreg 215025 + 5 * i + 1) = (N.chord i).lp)
    (hrp : d.nmem (d.nreg 215025 + 5 * i + 2) = (N.chord i).rp)
    (hcW : d.nreg 215025 + 5 * i + 2 ≤ W) (hxe : x.edge < n) (hxh : x.hgt ≤ n)
    (hl : (N.chord i).lp < n) (hr : (N.chord i).rp < n) (hhn : (N.chord i).h + 1 ≤ n)
    (hW : 4 * n + 4 ≤ W) :
    ∃ d' k, Exec P W chTest d d' k ∧ k ≤ 30 ∧
      (if (N.chord i).lpos = x then
        d'.nreg 215052 = (N.chord i).rpos.edge ∧ d'.nreg 215053 = (N.chord i).rpos.hgt ∧
          d'.nreg 215054 = 1
      else if (N.chord i).rpos = x then
        d'.nreg 215052 = (N.chord i).lpos.edge ∧ d'.nreg 215053 = (N.chord i).lpos.hgt ∧
          d'.nreg 215054 = 1
      else d'.nreg 215052 = d.nreg 215052 ∧ d'.nreg 215053 = d.nreg 215053 ∧
        d'.nreg 215054 = d.nreg 215054) ∧
      d'.nmem = d.nmem ∧ FrameM (fun q => decide (q = 215045) || decide (215052 ≤ q ∧ q ≤ 215054) ||
        decide (215056 ≤ q ∧ q ≤ 215063)) d d' := by

  have e5 : ∀ a b : ℕ, a + (b + b + (b + b) + b) = a + 5 * b := fun a b => by ring
  obtain ⟨d', k, ex, hk, hpost, hm⟩ : ∃ d' k, Exec P W chTest d d' k ∧ k ≤ 30 ∧
      (if (N.chord i).lpos = x then
        d'.nreg 215052 = (N.chord i).rpos.edge ∧ d'.nreg 215053 = (N.chord i).rpos.hgt ∧
          d'.nreg 215054 = 1
      else if (N.chord i).rpos = x then
        d'.nreg 215052 = (N.chord i).lpos.edge ∧ d'.nreg 215053 = (N.chord i).lpos.hgt ∧
          d'.nreg 215054 = 1
      else d'.nreg 215052 = d.nreg 215052 ∧ d'.nreg 215053 = d.nreg 215053 ∧
        d'.nreg 215054 = d.nreg 215054) ∧ d'.nmem = d.nmem := by
    unfold chTest
    refine spec_seq ?_
    exec_block
    all_goals try (config_simp; (try simp only [h55, hi, hK.one, e5, hh, hlp, hrp, h46, h47]); omega)
    by_cases hL : (N.chord i).lpos = x
    · have hL' := lpos_eq_iff.1 hL
      refine spec_ifLtN_true (by config_simp; simp only [h55, hi, hK.one, e5, hh, hlp, h46, h47]; omega) ?_
      exec_block
      · omega
      refine ⟨by omega, ?_, rfl⟩
      simp only [hL, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩ <;> config_simp <;>
        (try simp only [h55, hi, hK.one, e5, hh, hrp]) <;> rfl
    · have hL' : ¬ ((N.chord i).lp = x.edge ∧ (N.chord i).h + 1 = x.hgt) := fun h => hL (lpos_eq_iff.2 h)
      refine spec_ifLtN_false (by config_simp; simp only [h55, hi, hK.one, e5, hh, hlp, h46, h47]; omega) ?_
      by_cases hR : (N.chord i).rpos = x
      · have hR' := rpos_eq_iff.1 hR
        refine spec_ifLtN_true (by config_simp; simp only [h55, hi, hK.one, e5, hh, hrp, h46, h47]; omega) ?_
        exec_block
        · omega
        refine ⟨by omega, ?_, rfl⟩
        simp only [hL, hR, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩ <;> config_simp <;>
          (try simp only [h55, hi, hK.one, e5, hh, hlp]) <;> rfl
      · have hR' : ¬ ((N.chord i).rp = x.edge ∧ (N.chord i).h + 1 = x.hgt) := fun h => hR (rpos_eq_iff.2 h)
        refine spec_ifLtN_false (by config_simp; simp only [h55, hi, hK.one, e5, hh, hrp, h46, h47]; omega) ?_
        refine spec_skip ‹_› ⟨by omega, ?_, rfl⟩
        simp only [hL, hR, ↓reduceIte]
        refine ⟨?_, ?_, ?_⟩ <;> config_simp
  exact ⟨d', k, ex, hk, hpost, hm, exec_frameM ex (by decide)⟩


section
variable (N : NF)
include N
/-- The search predicate of `partner`. -/
def pmatch (x : WPos) (i : ℕ) : Bool := decide ((N.chord i).lpos = x ∨ (N.chord i).rpos = x)

/-- The result of the partner search for a search outcome. -/
def resOf (x : WPos) : Option ℕ → WPos
  | some i => if (N.chord i).lpos = x then (N.chord i).rpos else (N.chord i).lpos
  | none => x

theorem partner_eq (r : ℕ) (x : WPos) :
    partner N r x = resOf N x ((N.region r).chords.find? (pmatch N x)) := by
  rfl


end

theorem find_take_succ {l : List ℕ} {p : ℕ → Bool} {v : ℕ} (hv : v < l.length) :
    (l.take (v + 1)).find? p =
      ((l.take v).find? p).or (if p (l.getD v 0) then some (l.getD v 0) else none) := by
  grind [List.take_add_one, List.find?_append, Option.toList_some, List.find?_singleton]

set_option maxHeartbeats 1000000 in
/-- **The partner search.** -/
theorem partS_exec (d : Config) (hw : WordsBounded W d) {li : Bool} {n : ℕ} {N : NF} {r : ℕ}
    {x : WPos} (hK : Kst n li d) (hF : HFacts n N r)
    (h46 : d.nreg 215046 = x.edge) (h47 : d.nreg 215047 = x.hgt) (hxe : x.edge < n)
    (hxh : x.hgt ≤ n) (h31 : d.nreg 215031 = (N.region r).chords.length)
    (hch : ∀ v, v < (N.region r).chords.length →
      d.nmem (d.nreg 215027 + (d.nreg 215029 + v)) = (N.region r).chords.getD v 0 ∧
      d.nreg 215027 + (d.nreg 215029 + v) ≤ W)
    (hrec : ∀ i, i < N.nChords → d.nmem (d.nreg 215025 + 5 * i) = (N.chord i).h ∧
      d.nmem (d.nreg 215025 + 5 * i + 1) = (N.chord i).lp ∧
      d.nmem (d.nreg 215025 + 5 * i + 2) = (N.chord i).rp ∧ d.nreg 215025 + 5 * i + 2 ≤ W)
    (hW : 4 * n + 4 ≤ W) :
    ∃ d' k, Exec P W partS d d' k ∧ k ≤ 150 ∧ d'.nreg 215052 = (partner N r x).edge ∧
      d'.nreg 215053 = (partner N r x).hgt ∧ d'.nmem = d.nmem ∧ FrameM Bpart d d' := by
  set cs := (N.region r).chords with hcs
  have hKc : cs.length ≤ 4 := hF.hK
  -- initialisation
  obtain ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀, f₀⟩ : ∃ d₀ k₀, Exec P W
      (block [.copyN 215052 215046, .copyN 215053 215047, .constN 215054 0, .constN 215055 0])
      d d₀ k₀ ∧ k₀ = 4 ∧ d₀.nreg 215052 = x.edge ∧ d₀.nreg 215053 = x.hgt ∧ d₀.nreg 215054 = 0 ∧
      d₀.nreg 215055 = 0 ∧ d₀.nmem = d.nmem ∧ FrameM Bpart d d₀ := by
    obtain ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀⟩ : ∃ d₀ k₀, Exec P W
        (block [.copyN 215052 215046, .copyN 215053 215047, .constN 215054 0, .constN 215055 0])
        d d₀ k₀ ∧ k₀ = 4 ∧ d₀.nreg 215052 = x.edge ∧ d₀.nreg 215053 = x.hgt ∧
        d₀.nreg 215054 = 0 ∧ d₀.nreg 215055 = 0 ∧ d₀.nmem = d.nmem := by
      exec_block
      · omega
      · omega
      simp_all
    exact ⟨d₀, k₀, e₀, hk₀, a52, a53, a54, a55, m₀, exec_frameM e₀ (by decide)⟩
  -- the loop
  let Inv : ℕ → Config → Prop := fun v e => WordsBounded W e ∧ e.nreg 215055 = v ∧
    e.nreg 215031 = cs.length ∧
    e.nreg 215052 = (resOf N x ((cs.take v).find? (pmatch N x))).edge ∧
    e.nreg 215053 = (resOf N x ((cs.take v).find? (pmatch N x))).hgt ∧
    e.nreg 215054 = (if ((cs.take v).find? (pmatch N x)).isSome then 1 else 0) ∧
    FrameM Bpart d e ∧ e.nmem = d.nmem
  obtain ⟨d', k, ex, ⟨w', -, -, v52, v53, -, f', m'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W)
    (ir := 215055) (nr := 215031) Inv 33 cs.length
    (fun v e ⟨hw, h1, h2, _⟩ => ⟨hw, h1, h2⟩)
    (fun v e hv ⟨hwe, e55, e31, e52, e53, e54, fe, me⟩ => by
      have g : ∀ q, Bpart q = false → e.nreg q = d.nreg q := fe.1
      have Ke : Kst n li e := hK.frame fe (by decide)
      have hfs := find_take_succ (p := pmatch N x) hv
      have hmem : cs.getD v 0 ∈ cs := by
        grind
      obtain ⟨hi1, hil, hir, hih⟩ := hF.hch _ hmem
      have Ke' : e.nreg 215020 = 1 := Ke.one
      obtain ⟨e', k, ex, hk, p55, p52, p53, p54, pm⟩ : ∃ e' k, Exec P W chBody e e' k ∧ k ≤ 33 ∧
          e'.nreg 215055 = v + 1 ∧
          e'.nreg 215052 = (resOf N x ((cs.take (v + 1)).find? (pmatch N x))).edge ∧
          e'.nreg 215053 = (resOf N x ((cs.take (v + 1)).find? (pmatch N x))).hgt ∧
          e'.nreg 215054 = (if ((cs.take (v + 1)).find? (pmatch N x)).isSome then 1 else 0) ∧
          e'.nmem = e.nmem := by
        unfold chBody
        refine spec_seq ?_
        cases hfound : (cs.take v).find? (pmatch N x) with
        | some i₀ =>
          rw [hfound] at e52 e53 e54
          simp only [Option.isSome_some, ↓reduceIte] at e54
          refine spec_ifLtN_false (by omega) ?_
          refine spec_skip hwe ?_
          exec_block
          · omega
          rw [hfs, hfound, Option.some_or]
          refine ⟨by omega, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp
          · omega
          · exact e52
          · exact e53
          ram_grind
        | none =>
          rw [hfound] at e52 e53 e54
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, resOf] at e52 e53 e54
          refine spec_ifLtN_true (by omega) ?_
          set i := cs.getD v 0 with hidef
          obtain ⟨r1, r2, r3, r4⟩ := hrec i hi1
          obtain ⟨c1, c2⟩ := hch v hv
          have t46 : e.nreg 215046 = x.edge := by rw [g _ (by decide), h46]
          have t47 : e.nreg 215047 = x.hgt := by rw [g _ (by decide), h47]
          have t27 : e.nreg 215027 = d.nreg 215027 := g _ (by decide)
          have t29 : e.nreg 215029 = d.nreg 215029 := g _ (by decide)
          have t25 : e.nreg 215025 = d.nreg 215025 := g _ (by decide)
          have ti : e.nmem (e.nreg 215027 + (e.nreg 215029 + v)) = i := by ram_grind
          have tiW : e.nreg 215027 + (e.nreg 215029 + v) ≤ W := by omega
          have th : e.nmem (e.nreg 215025 + 5 * i) = (N.chord i).h := by ram_grind
          have tl : e.nmem (e.nreg 215025 + 5 * i + 1) = (N.chord i).lp := by ram_grind
          have tr : e.nmem (e.nreg 215025 + 5 * i + 2) = (N.chord i).rp := by ram_grind
          have tW : e.nreg 215025 + 5 * i + 2 ≤ W := by omega
          refine spec_use (chTest_exec (P := P) e hwe Ke t46 t47 e55 ti tiW th tl tr tW hxe hxh
            hil hir hih hW) ?_
          intro c₁ k₁ hk₁ hw₁ ⟨hpost, hm₁, hf₁⟩
          have q55 : c₁.nreg 215055 = v := by rw [hf₁.1 _ (by decide), e55]
          have q20 : c₁.nreg 215020 = 1 := by rw [hf₁.1 _ (by decide), Ke']
          exec_block
          · omega
          rw [hfs, hfound, Option.none_or]
          refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩ <;> config_simp
          · omega
          all_goals by_cases hL : (N.chord i).lpos = x <;> by_cases hR : (N.chord i).rpos = x <;>
            simp only [hL, hR, ↓reduceIte] at hpost <;>
            simp only [pmatch, hL, hR, or_true, or_false, decide_true, decide_false,
              ↓reduceIte, resOf, Option.isSome_some, Option.isSome_none, Bool.false_eq_true,
              hpost.1, hpost.2.1, hpost.2.2, e52, e53, e54, hm₁]
      have fe' := exec_frameM ex wrM_chBody
      exact ⟨e', k, ex, ⟨ex.wb_right, p55, by rw [fe'.1 _ (by decide), e31], p52, p53, p54,
        fe.trans fe', pm.trans me⟩, hk⟩)
    (j := 0) ⟨e₀.wb_right, a55, by rw [f₀.1 _ (by decide), h31], by simp [resOf, a52],
      by simp [resOf, a53], by simp [a54], f₀, m₀⟩ (Nat.zero_le _)
  refine ⟨d', k₀ + k, .seq e₀ ex, by omega, ?_, ?_, m', f'⟩
  · rw [v52, List.take_length, partner_eq]
  · rw [v53, List.take_length, partner_eq]

end exec

end

end DrvH

end Chazelle.Core
