module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTValid2
public import Chazelle.Core.RestoreTCountMath

/-!
# WP-E, the candidate test on the RAM, part 13: the count test

`countS kc` scans the exit chords of the region and counts those with an end strictly inside the
key interval `(key x, key f)` (`83053`) and inside `(key f, key x)` (`83054`), for the candidate
`x` (`83005`, `83006`) and the arrival position `f` (`83012`, `83013`); the success bit `83014`
is `1` iff both counts are at least `2` (`count_rs`: `83014 = 1` iff `CountOK`, by
`sideExits_ncard`).

Scratch registers: `83030 … 83032`, `83047 … 83049` (the chord), `83055` (the constant `2`),
`83056`, `83057` (`x < f`, `f < x`), `83060 … 83067` (the comparisons of the two ends with `x`
and `f`), `83068`, `83069` (the side flags of the chord).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc)

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-- **Update of a side flag** `f`: set if the key `k` is strictly inside the arc `(a, b)` (bits
`bab`: `a < b`, `bak`: `a < k`, `bkb`: `k < b`). -/
def updArc (bab bak bkb f : ℕ) : Stmt :=
  .ifLtN bab 83023
    (.ifLtN bak 83023 (.ifLtN bkb 83023 .skip (setF f)) (setF f))
    (.ifLtN bak 83023 .skip (.ifLtN bkb 83023 .skip (setF f)))

theorem updArc_rs {bab bak bkb f : ℕ} {a b k : ℝ} (hf : Scr f) (hI : TInv W c₀ c)
    (h1 : BitIs c bab (a < b)) (h2 : BitIs c bak (a < k)) (h3 : BitIs c bkb (k < b)) :
    RS P W c₀ (updArc bab bak bkb f) c 7 (fun c' => FlagUpd c c' f (sideInArc a b k)) := by
  have e1 : c.nreg 83023 = 1 := hI.h23
  rw [← sideInArc_bits]
  unfold updArc
  rcases bit01 h1 with ⟨q1, n1⟩ | ⟨q1, n1⟩ <;>
  rcases bit01 h2 with ⟨q2, n2⟩ | ⟨q2, n2⟩ <;>
  rcases bit01 h3 with ⟨q3, n3⟩ | ⟨q3, n3⟩
  · refine RS.ifT (by omega) (RS.ifT (by omega) (RS.ifT (by omega) (leaf_skip hI ?_)))
    simp_all
  · refine RS.ifT (by omega) (RS.ifT (by omega) (RS.ifF (by omega) (leaf_set hI hf le_rfl ?_)))
    simp_all
  · refine RS.ifT (by omega) (RS.ifF (by omega) (leaf_set hI hf (by norm_num) ?_))
    simp_all
  · grind
  · grind
  · refine RS.ifF (by omega) (RS.ifT (by omega) (leaf_skip hI ?_))
    simp_all
  · refine RS.ifF (by omega) (RS.ifF (by omega) (RS.ifT (by omega) (leaf_skip hI ?_)))
    simp_all
  · refine RS.ifF (by omega) (RS.ifF (by omega) (RS.ifF (by omega) (leaf_set hI hf le_rfl ?_)))
    simp_all


/-! ## Reading an exit chord -/

/-- Read the exit chord at place `83030`: `83047 := h + 1`, `83048 := lp`, `83049 := rp`. -/
def cRead : Stmt :=
  .seq (tRegItem 3 83030) (.seq (.instr (.copyN 83032 50210))
    (.seq (chF 0 83047) (.seq (.instr (.addN 83047 83047 83023))
      (.seq (chF 1 83048) (chF 2 83049)))))

theorem cRead_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (ht : c.nreg 83030 < (N.region (c₀.nreg 83002)).chords.length)
    (hroom : c.nreg ALLOC + 70 ≤ W) :
    RS P W c₀ cRead c 70 (fun c' =>
      c'.nreg 83047 = (N.chord (chordAt N (c₀.nreg 83002) (c.nreg 83030))).h + 1 ∧
      c'.nreg 83048 = (N.chord (chordAt N (c₀.nreg 83002) (c.nreg 83030))).lp ∧
      c'.nreg 83049 = (N.chord (chordAt N (c₀.nreg 83002) (c.nreg 83030))).rp ∧
      Agr c c' [83032, 83047, 83048, 83049]) := by
  have hil := (chordAt_lt hE ht).1
  set i := chordAt N (c₀.nreg 83002) (c.nreg 83030) with hidef
  have h1 := tRegItem_exec (f := 3) (tr := 83030) (Or.inr rfl) (by omega_nf) hE hI
    (by simp_all) (by omega)
  rw [ite_eq_right (by decide)] at h1
  refine RS.mono (K := 20 + (1 + (14 + (1 + (14 + 14))))) ?_ (by norm_num) (fun _ h => h)
  refine RS.seq (RS.op h1) fun c₁ hI₁ hA₁ ⟨v₁, h8₁⟩ =>
    RS.seq (RS.copy hI₁ (r := 83032) (a := 50210) (by omega_nf))
    fun c₂ hI₂ hA₂ hc₂ => ?_
  have q2 : c₂.nreg 83032 = i := by rw [hc₂, upd_eq, v₁]; rfl
  have a2 : Agr c c₂ [83032] := (Agr.of_band h8₁ []).trans (Agr.of_upd hc₂)
  refine RS.seq (chF_rs (f := 0) (d := 83047) (by norm_num) (by omega_nf) hE hI₂
    (by omega) (by omega)) fun c₃ hI₃ hA₃ ⟨v₃, a₃⟩ => ?_
  have q3 : c₃.nreg 83032 = i := by rw [a₃ _ (by norm_num) (by norm_num) (by simp), q2]
  have e23 : c₃.nreg 83023 = 1 := hI₃.h23
  have hh : (N.chord i).h < P.n := by
    obtain ⟨-, -, -, reg, -, -, -, -, -, hh, -⟩ := hE.hNF
    have := hh _ hil
    rwa [show (Qof P).n = P.n from shear_n _ _] at this
  refine RS.seq (RS.add hI₃ (r := 83047) (a := 83047) (b := 83023) (by omega_nf)
    (by rw [v₃, e23, q2]; have := hE.hW; core_grind [hostWords]))
    fun c₄ hI₄ hA₄ h₄ => ?_
  have q4 : c₄.nreg 83032 = i := by rw [h₄, upd_ne (by norm_num), q3]
  have v4 : c₄.nreg 83047 = (N.chord i).h + 1 := by rw [h₄, upd_eq, v₃, e23, q2]; rfl
  refine RS.seq (chF_rs (f := 1) (d := 83048) (by norm_num) (by omega_nf) hE hI₄
    (by omega) (by omega)) fun c₅ hI₅ hA₅ ⟨v₅, a₅⟩ => ?_
  have q5 : c₅.nreg 83032 = i := by rw [a₅ _ (by norm_num) (by norm_num) (by simp), q4]
  refine (chF_rs (f := 2) (d := 83049) (by norm_num) (by omega_nf) hE hI₅
    (by omega) (by omega)).mono le_rfl fun c₆ ⟨v₆, a₆⟩ => ?_
  refine ⟨?_, ?_, ?_, ((((a2.trans a₃).trans (Agr.of_upd h₄)).trans a₅).trans a₆).mono
    (by simp)⟩
  · rw [a₆ _ (by norm_num) (by norm_num) (by simp), a₅ _ (by norm_num) (by norm_num) (by simp),
      v4]
  · rw [a₆ _ (by norm_num) (by norm_num) (by simp), v₅, q4]; rfl
  · rw [v₆, q5]; rfl

/-! ## The comparisons of the ends -/

/-- The four comparisons of the ends `L = (83048, 83047)`, `R = (83049, 83047)` of the chord
with `x` and `f`. -/
def cCmps (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq (kc 83048 83047 83005 83006) (cp2 83060 83061))
    (.seq (.seq (kc 83048 83047 83012 83013) (cp2 83062 83063))
      (.seq (.seq (kc 83049 83047 83005 83006) (cp2 83064 83065))
        (.seq (kc 83049 83047 83012 83013) (cp2 83066 83067))))

theorem cCmps_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hL : PosG M (Qof P) P.n ⟨c.nreg 83048, c.nreg 83047⟩)
    (hR : PosG M (Qof P) P.n ⟨c.nreg 83049, c.nreg 83047⟩)
    (hf : PosG M (Qof P) P.n ⟨c.nreg 83012, c.nreg 83013⟩)
    (hroom : c.nreg ALLOC + 4 * (Kk + 2) ≤ W) :
    RS P W c₀ (cCmps kc) c (4 * (Kk + 2)) (fun c' =>
      BitIs c' 83060 (keyAt M P c 83048 83047 < keyAt M P c 83005 83006) ∧
      BitIs c' 83061 (keyAt M P c 83005 83006 < keyAt M P c 83048 83047) ∧
      BitIs c' 83062 (keyAt M P c 83048 83047 < keyAt M P c 83012 83013) ∧
      BitIs c' 83063 (keyAt M P c 83012 83013 < keyAt M P c 83048 83047) ∧
      BitIs c' 83064 (keyAt M P c 83049 83047 < keyAt M P c 83005 83006) ∧
      BitIs c' 83065 (keyAt M P c 83005 83006 < keyAt M P c 83049 83047) ∧
      BitIs c' 83066 (keyAt M P c 83049 83047 < keyAt M P c 83012 83013) ∧
      BitIs c' 83067 (keyAt M P c 83012 83013 < keyAt M P c 83049 83047) ∧
      Agr c c' [83060, 83061, 83062, 83063, 83064, 83065, 83066, 83067]) := by
  have i5 := hI.hin 83005 (by norm_num) (by norm_num)
  have i6 := hI.hin 83006 (by norm_num) (by norm_num)
  have hx : PosG M (Qof P) P.n ⟨c.nreg 83005, c.nreg 83006⟩ := by
    rw [i5, i6]; exact hE.xPosG
  unfold cCmps
  refine RS.mono (K := (Kk + 2) + ((Kk + 2) + ((Kk + 2) + (Kk + 2)))) ?_ (by omega)
    (fun _ h => h)
  have g : ∀ {c₁ : Config} {S : List ℕ}, Agr c c₁ S → (∀ q ∈ [83005, 83006, 83012, 83013, 83047,
      83048, 83049], q ∉ S) → ∀ q ∈ [83005, 83006, 83012, 83013, 83047, 83048, 83049],
      c₁.nreg q = c.nreg q := fun ha hS q hq => by
    have := hS q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact ha q (by omega) (by omega) this
  refine RS.seq (kcmp_rs hK (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf) (by omega) hE hI hL hx
    (by omega)) fun c₁ hI₁ hA₁ ⟨b60, b61, a₁⟩ => ?_
  have g1 := g a₁ (by simp)
  refine RS.seq (kcmp_rs hK (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf) (by omega) hE hI₁
    (by grind)
    (by grind) (by omega))
    fun c₂ hI₂ hA₂ ⟨b62, b63, a₂⟩ => ?_
  have g2 := g (a₁.trans a₂) (by simp)
  refine RS.seq (kcmp_rs hK (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf) (by omega) hE hI₂
    (by grind)
    (by grind) (by omega))
    fun c₃ hI₃ hA₃ ⟨b64, b65, a₃⟩ => ?_
  have g3 := g ((a₁.trans a₂).trans a₃) (by simp)
  refine (kcmp_rs hK (by unfold InR; omega) (by unfold InR; omega) (by unfold InR; omega)
    (by unfold InR; omega) (by unfold Scr; omega) (by unfold Scr; omega) (by omega) hE hI₃
    (by grind)
    (by grind) (by omega)).mono le_rfl
    fun c₄ ⟨b66, b67, a₄⟩ => ?_
  unfold keyAt at *
  rw [g1 83048 (by simp), g1 83047 (by simp), g1 83012 (by simp), g1 83013 (by simp)] at b62 b63
  rw [g2 83049 (by simp), g2 83047 (by simp), g2 83005 (by simp), g2 83006 (by simp)] at b64 b65
  rw [g3 83049 (by simp), g3 83047 (by simp), g3 83012 (by simp), g3 83013 (by simp)] at b66 b67
  have t4 : ∀ q ∈ [83060, 83061, 83062, 83063, 83064, 83065], c₄.nreg q = c₃.nreg q := by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₄ q (by omega) (by omega) (by simp; omega)
  have t3 : ∀ q ∈ [83060, 83061, 83062, 83063], c₃.nreg q = c₂.nreg q := by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₃ q (by omega) (by omega) (by simp; omega)
  have t2 : ∀ q ∈ [83060, 83061], c₂.nreg q = c₁.nreg q := by
    intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₂ q (by omega) (by omega) (by simp; omega)
  refine ⟨b60.of_eq ?_, b61.of_eq ?_, b62.of_eq ?_, b63.of_eq ?_, b64.of_eq ?_, b65.of_eq ?_,
    b66, b67, (((a₁.trans a₂).trans a₃).trans a₄).mono (by simp)⟩
  · rw [t4 _ (by simp), t3 _ (by simp), t2 _ (by simp)]
  · rw [t4 _ (by simp), t3 _ (by simp), t2 _ (by simp)]
  · rw [t4 _ (by simp), t3 _ (by simp)]
  · rw [t4 _ (by simp), t3 _ (by simp)]
  · rw [t4 _ (by simp)]
  · rw [t4 _ (by simp)]


/-! ## The side flags -/

/-- The side flags `83068` (inside `(x, f)`) and `83069` (inside `(f, x)`) of the chord. -/
def cUpd : Stmt :=
  .seq (.instr (.constN 83068 0)) (.seq (.instr (.constN 83069 0))
    (.seq (updArc 83056 83061 83062 83068) (.seq (updArc 83056 83065 83066 83068)
      (.seq (updArc 83057 83063 83060 83069) (updArc 83057 83067 83064 83069)))))

theorem flag_val {c : Config} {r : ℕ} {p : Prop} (h1 : c.nreg r ≤ 1) (h2 : c.nreg r = 1 ↔ p) :
    c.nreg r = (open Classical in if p then 1 else 0) := by
  grind

theorem cUpd_rs {kx kf kL kR : ℝ} (hI : TInv W c₀ c) (b56 : BitIs c 83056 (kx < kf))
    (b57 : BitIs c 83057 (kf < kx)) (b60 : BitIs c 83060 (kL < kx))
    (b61 : BitIs c 83061 (kx < kL)) (b62 : BitIs c 83062 (kL < kf))
    (b63 : BitIs c 83063 (kf < kL)) (b64 : BitIs c 83064 (kR < kx))
    (b65 : BitIs c 83065 (kx < kR)) (b66 : BitIs c 83066 (kR < kf))
    (b67 : BitIs c 83067 (kf < kR)) :
    RS P W c₀ cUpd c 30 (fun c' =>
      c'.nreg 83068 ≤ 1 ∧ (c'.nreg 83068 = 1 ↔ sideInArc kx kf kL ∨ sideInArc kx kf kR) ∧
      c'.nreg 83069 ≤ 1 ∧ (c'.nreg 83069 = 1 ↔ sideInArc kf kx kL ∨ sideInArc kf kx kR) ∧
      Agr c c' [83068, 83069]) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rw [hI.h23] at this; exact this
  unfold cUpd
  refine RS.mono (K := 1 + (1 + (7 + (7 + (7 + 7))))) ?_ (by norm_num) (fun _ h => h)
  refine RS.seq (RS.const hI (r := 83068) (v := 0) (by omega_nf) (by omega))
    fun c₁ hI₁ _ h₁ => ?_
  refine RS.seq (RS.const hI₁ (r := 83069) (v := 0) (by omega_nf) (by omega))
    fun c₂ hI₂ _ h₂ => ?_
  have a2 : Agr c c₂ [83068, 83069] := ((Agr.of_upd h₁).trans (Agr.of_upd h₂)).mono (by simp)
  have tr : ∀ {c' : Config} {S : List ℕ}, Agr c c' S → ∀ r ∈ [83056, 83057, 83060, 83061, 83062,
      83063, 83064, 83065, 83066, 83067], r ∉ S → c'.nreg r = c.nreg r := fun ha r hr hS => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    exact ha r (by omega) (by omega) hS
  refine RS.seq (updArc_rs (by omega_nf) hI₂ (b56.of_eq (tr a2 _ (by simp) (by simp)))
    (b61.of_eq (tr a2 _ (by simp) (by simp))) (b62.of_eq (tr a2 _ (by simp) (by simp))))
    fun c₃ hI₃ _ ⟨u1, u2, a₃⟩ => ?_
  have a3 := a2.trans a₃
  refine RS.seq (updArc_rs (by omega_nf) hI₃ (b56.of_eq (tr a3 _ (by simp) (by simp)))
    (b65.of_eq (tr a3 _ (by simp) (by simp))) (b66.of_eq (tr a3 _ (by simp) (by simp))))
    fun c₄ hI₄ _ ⟨v1, v2, a₄⟩ => ?_
  have a4 := a3.trans a₄
  refine RS.seq (updArc_rs (by omega_nf) hI₄ (b57.of_eq (tr a4 _ (by simp) (by simp)))
    (b63.of_eq (tr a4 _ (by simp) (by simp))) (b60.of_eq (tr a4 _ (by simp) (by simp))))
    fun c₅ hI₅ _ ⟨w1, w2, a₅⟩ => ?_
  have a5 := a4.trans a₅
  refine (updArc_rs (by omega_nf) hI₅ (b57.of_eq (tr a5 _ (by simp) (by simp)))
    (b67.of_eq (tr a5 _ (by simp) (by simp))) (b64.of_eq (tr a5 _ (by simp) (by simp)))).mono
    le_rfl fun c₆ ⟨z1, z2, a₆⟩ => ?_
  have e68 : c₂.nreg 83068 = 0 := by rw [h₂, upd_ne (by norm_num), h₁, upd_eq]
  have e69 : c₂.nreg 83069 = 0 := by rw [h₂, upd_eq]
  have f68 : c₆.nreg 83068 = c₄.nreg 83068 := by
    rw [a₆ _ (by norm_num) (by norm_num) (by simp), a₅ _ (by norm_num) (by norm_num) (by simp)]
  have f69 : c₄.nreg 83069 = c₂.nreg 83069 := by
    rw [a₄ _ (by norm_num) (by norm_num) (by simp), a₃ _ (by norm_num) (by norm_num) (by simp)]
  refine ⟨by omega, ?_, z2 (w2 (by omega)), ?_,
    (((a2.trans a₃).trans a₄).trans a₅).trans a₆ |>.mono (by simp)⟩
  · grind
  grind

/-! ## The count loop -/

/-- The additions of the count loop. -/
def cAdd : Stmt :=
  .seq (.instr (.addN 83053 83053 83068)) (.seq (.instr (.addN 83054 83054 83069))
    (.instr (.addN 83030 83030 83023)))

/-- The body of the count loop. -/
def countBody (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt := .seq cRead (.seq (cCmps kc) (.seq cUpd cAdd))

/-- The cost bound of the body of the count loop. -/
def countKB (Kk : ℕ) : ℕ := 70 + (4 * (Kk + 2) + (30 + (1 + (1 + 1))))

/-- The registers the count loop writes. -/
def countScr : List ℕ := [83030, 83032, 83047, 83048, 83049, 83053, 83054, 83060, 83061, 83062,
  83063, 83064, 83065, 83066, 83067, 83068, 83069]

/-- **The invariant of the count loop** for the arrival position `f` (started in `cS`). -/
def CountI (M : Model) (P : Polygon) (N : NF) (c₀ : Config) (f : WPos) (cS c : Config) : Prop :=
  c.nreg 83031 = (N.region (c₀.nreg 83002)).chords.length ∧ c.nreg 83030 ≤ c.nreg 83031 ∧
    c.nreg 83053 = cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀)) (M.key (Qof P) f)
      (chordAt N (c₀.nreg 83002) t)) (c.nreg 83030) ∧
    c.nreg 83054 = cntP (fun t => SideHit M P N (M.key (Qof P) f) (M.key (Qof P) (xOf c₀))
      (chordAt N (c₀.nreg 83002) t)) (c.nreg 83030) ∧
    BitIs c 83056 (M.key (Qof P) (xOf c₀) < M.key (Qof P) f) ∧
    BitIs c 83057 (M.key (Qof P) f < M.key (Qof P) (xOf c₀)) ∧
    c.nreg 83012 = f.edge ∧ c.nreg 83013 = f.hgt ∧ Agr cS c countScr

/-- **One iteration of the count loop.** -/
theorem countBody_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {f : WPos} (hf : PosG M (Qof P) P.n f) {cS : Config}
    (hI : TInv W c₀ c) (hA : CountI M P N c₀ f cS c) (ht : c.nreg 83030 < c.nreg 83031)
    (hroom : c.nreg ALLOC + countKB Kk ≤ W) :
    RS P W c₀ (countBody kc) c (countKB Kk) (fun c' => CountI M P N c₀ f cS c' ∧
      c'.nreg 83030 = c.nreg 83030 + 1) := by
  obtain ⟨hL, htL, n53, n54, b56, b57, f12, f13, aS⟩ := hA
  have ht' : c.nreg 83030 < (N.region (c₀.nreg 83002)).chords.length := by omega
  obtain ⟨hil, -⟩ := chordAt_lt hE ht'
  have hpos := hE.chordPosG hil
  unfold countBody countKB
  refine RS.seq (cRead_rs hE hI ht' (by omega_nf))
    fun c₁ hI₁ hA₁ ⟨s1, s2, s3, a₁⟩ => ?_
  have g1 : ∀ q ∈ [83005, 83006, 83012, 83013, 83030, 83031, 83053, 83054, 83056, 83057],
      c₁.nreg q = c.nreg q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a₁ q (by omega) (by omega) (by simp; omega)
  have hLp : PosG M (Qof P) P.n ⟨c₁.nreg 83048, c₁.nreg 83047⟩ := by rw [s1, s2]; exact hpos.1
  have hRp : PosG M (Qof P) P.n ⟨c₁.nreg 83049, c₁.nreg 83047⟩ := by rw [s1, s3]; exact hpos.2
  have hfp : PosG M (Qof P) P.n ⟨c₁.nreg 83012, c₁.nreg 83013⟩ := by
    rw [g1 83012 (by simp), g1 83013 (by simp), f12, f13]; exact hf
  refine RS.seq (cCmps_rs hK hE hI₁ hLp hRp hfp (by omega_nf))
    fun c₂ hI₂ hA₂ ⟨b60, b61, b62, b63, b64, b65, b66, b67, a₂⟩ => ?_
  have i5 := hI₁.hin 83005 (by norm_num) (by norm_num)
  have i6 := hI₁.hin 83006 (by norm_num) (by norm_num)
  set i := chordAt N (c₀.nreg 83002) (c.nreg 83030)
  have kL : keyAt M P c₁ 83048 83047 = M.key (Qof P) (N.chord i).lpos := by
    unfold keyAt; rw [s1, s2]; rfl
  have kR : keyAt M P c₁ 83049 83047 = M.key (Qof P) (N.chord i).rpos := by
    unfold keyAt; rw [s1, s3]; rfl
  have kx : keyAt M P c₁ 83005 83006 = M.key (Qof P) (xOf c₀) := by
    unfold keyAt; rw [i5, i6]; rfl
  have kf : keyAt M P c₁ 83012 83013 = M.key (Qof P) f := by
    unfold keyAt; rw [g1 83012 (by simp), g1 83013 (by simp), f12, f13]
  rw [kL, kx] at b60 b61
  rw [kL, kf] at b62 b63
  rw [kR, kx] at b64 b65
  rw [kR, kf] at b66 b67
  have a12 := a₁.trans a₂
  have b56' := b56.of_eq (a12 83056 (by norm_num) (by norm_num) (by simp))
  have b57' := b57.of_eq (a12 83057 (by norm_num) (by norm_num) (by simp))
  refine RS.seq (cUpd_rs hI₂ b56' b57' b60 b61 b62 b63 b64 b65 b66 b67)
    fun c₃ hI₃ hA₃ ⟨u1, u2, v1, v2, a₃⟩ => ?_
  have a13 := a12.trans a₃
  have g3 : ∀ q ∈ [83030, 83031, 83053, 83054, 83056, 83057, 83012, 83013],
      c₃.nreg q = c.nreg q := fun q hq => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    exact a13 q (by omega) (by omega) (by simp; omega)
  have e23 : c₃.nreg 83023 = 1 := hI₃.h23
  have hcl : c.nreg 83053 ≤ c.nreg 83030 := by rw [n53]; exact cntP_le _ _
  have hcl' : c.nreg 83054 ≤ c.nreg 83030 := by rw [n54]; exact cntP_le _ _
  have hW31 := hI.hw.1 83031
  unfold cAdd
  refine RS.seq (RS.add hI₃ (r := 83053) (a := 83053) (b := 83068) (by unfold Scr; omega)
    (by rw [g3 83053 (by simp)]; omega)) fun c₄ hI₄ _ h₄ => ?_
  refine RS.seq (RS.add hI₄ (r := 83054) (a := 83054) (b := 83069) (by unfold Scr; omega)
    (by rw [h₄, upd_ne (by norm_num), upd_ne (by norm_num), g3 83054 (by simp)]; omega))
    fun c₅ hI₅ _ h₅ => ?_
  have e23' : c₅.nreg 83023 = 1 := hI₅.h23
  have e30 : c₅.nreg 83030 = c.nreg 83030 := by
    rw [h₅, upd_ne (by norm_num), h₄, upd_ne (by norm_num), g3 83030 (by simp)]
  refine (RS.add hI₅ (r := 83030) (a := 83030) (b := 83023) (by unfold Scr; omega)
    (by omega)).mono le_rfl fun c₆ h₆ => ?_
  have v53 : c₆.nreg 83053 = c.nreg 83053 + c₃.nreg 83068 := by
    rw [h₆, upd_ne (by norm_num), h₅, upd_ne (by norm_num), h₄, upd_eq, g3 83053 (by simp)]
  have v54 : c₆.nreg 83054 = c.nreg 83054 + c₃.nreg 83069 := by
    rw [h₆, upd_ne (by norm_num), h₅, upd_eq, h₄, upd_ne (by norm_num), upd_ne (by norm_num),
      g3 83054 (by simp)]
  have v30 : c₆.nreg 83030 = c.nreg 83030 + 1 := by rw [h₆, upd_eq, e30, e23']
  have a36 : Agr c₃ c₆ [83053, 83054, 83030] :=
    (((Agr.of_upd h₄).trans (Agr.of_upd h₅)).trans (Agr.of_upd h₆)).mono (by simp)
  have a16 := a13.trans a36
  have g6 : ∀ q, 80000 ≤ q → q < 90000 → q ∉ countScr → c₆.nreg q = c.nreg q :=
    fun q h1 h2 hq => a16 q h1 h2 (fun h => hq (by simp [countScr] at h ⊢; omega))
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, v30⟩
  · rw [g6 83031 (by norm_num) (by norm_num) (by simp [countScr])]; exact hL
  · rw [v30, g6 83031 (by norm_num) (by norm_num) (by simp [countScr])]; omega
  · rw [v53, v30, cntP_succ, ← n53, flag_val u1 u2]; rfl
  · rw [v54, v30, cntP_succ, ← n54, flag_val v1 v2]; rfl
  · exact b56.of_eq (g6 83056 (by norm_num) (by norm_num) (by simp [countScr]))
  · exact b57.of_eq (g6 83057 (by norm_num) (by norm_num) (by simp [countScr]))
  · rw [g6 83012 (by norm_num) (by norm_num) (by simp [countScr]), f12]
  · rw [g6 83013 (by norm_num) (by norm_num) (by simp [countScr]), f13]
  · intro q h1 h2 hq
    rw [g6 q h1 h2 hq, aS q h1 h2 hq]


/-- The success bit: both counts at least `2`. -/
def succS : Stmt :=
  .seq (.instr (.constN 83014 0)) (.ifLtN 83053 83055 .skip (.ifLtN 83054 83055 .skip (setF 83014)))

/-- **The count test.** -/
def countS (kc : ℕ → ℕ → ℕ → ℕ → Stmt) : Stmt :=
  .seq (.seq (kc 83005 83006 83012 83013) (cp2 83056 83057)) (.seq (.instr (.constN 83053 0))
    (.seq (.instr (.constN 83054 0)) (.seq (.instr (.constN 83055 2)) (.seq (tRegLen 2)
      (.seq (.instr (.copyN 83031 50210)) (.seq (.instr (.constN 83030 0))
        (.seq (.whileLtN 83030 83031 (countBody kc)) succS)))))))

/-- The cost bound of the count test for a region with `D` exit chords. -/
def countK (Kk D : ℕ) : ℕ :=
  (Kk + 2) + (1 + (1 + (1 + (13 + (1 + (1 + (((countKB Kk + 2) * D + 2) + (1 + 6))))))))

/-- The registers the count test writes. -/
def countW : List ℕ := [83014, 83030, 83031, 83032, 83047, 83048, 83049, 83053, 83054, 83055,
  83056, 83057, 83060, 83061, 83062, 83063, 83064, 83065, 83066, 83067, 83068, 83069]

/-- **Contract of the count test** for the arrival position `f` in `83012`, `83013`. -/
theorem count_rs {kc : ℕ → ℕ → ℕ → ℕ → Stmt} {Kk : ℕ} (hK : KeyOK kc Kk)
    (hE : TGood P W M N c₀) {f : WPos} (hf : PosG M (Qof P) P.n f) (hI : TInv W c₀ c)
    (hf12 : c.nreg 83012 = f.edge) (hf13 : c.nreg 83013 = f.hgt)
    (hroom : c.nreg ALLOC + countK Kk (N.region (c₀.nreg 83002)).chords.length ≤ W) :
    RS P W c₀ (countS kc) c (countK Kk (N.region (c₀.nreg 83002)).chords.length) (fun c' =>
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀)) (M.key (Qof P) f)
          (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) f) (M.key (Qof P) (xOf c₀))
          (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length) ∧
      Agr c c' countW) := by
  have hW1 : 1 ≤ W := by have := hI.hw.1 83023; rw [hI.h23] at this; exact this
  have hW2 : 2 ≤ W := by omega_nf
  have i5 := hI.hin 83005 (by norm_num) (by norm_num)
  have i6 := hI.hin 83006 (by norm_num) (by norm_num)
  have hx : PosG M (Qof P) P.n ⟨c.nreg 83005, c.nreg 83006⟩ := by rw [i5, i6]; exact hE.xPosG
  have hfp : PosG M (Qof P) P.n ⟨c.nreg 83012, c.nreg 83013⟩ := by simp_all
  unfold countS countK
  unfold countK at hroom
  refine RS.seq (kcmp_rs hK (by omega_nf) (by omega_nf) (by omega_nf)
    (by omega_nf) (by omega_nf) (by omega_nf) (by omega) hE hI hx hfp
    (by omega)) fun c₁ hI₁ hA₁ ⟨b56, b57, a₁⟩ => ?_
  have kx : M.key (Qof P) ⟨c.nreg 83005, c.nreg 83006⟩ = M.key (Qof P) (xOf c₀) := by
    rw [i5, i6]; rfl
  have kf : M.key (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩ = M.key (Qof P) f := by
    simp_all
  rw [kx, kf] at b56 b57
  refine RS.seq (RS.const hI₁ (r := 83053) (v := 0) (by omega_nf) (by omega))
    fun c₂ hI₂ hA₂ h₂ => ?_
  refine RS.seq (RS.const hI₂ (r := 83054) (v := 0) (by omega_nf) (by omega))
    fun c₃ hI₃ hA₃ h₃ => ?_
  refine RS.seq (RS.const hI₃ (r := 83055) (v := 2) (by omega_nf) hW2)
    fun c₄ hI₄ hA₄ h₄ => ?_
  refine RS.seq (RS.op (tRegLen_exec (f := 2) (Or.inr rfl) hE hI₄ (by omega)))
    fun c₅ hI₅ hA₅ ⟨v₅, h8₅⟩ => ?_
  refine RS.seq (RS.copy hI₅ (r := 83031) (a := 50210) (by omega_nf))
    fun c₆ hI₆ hA₆ h₆ => ?_
  refine RS.seq (RS.const hI₆ (r := 83030) (v := 0) (by unfold Scr; omega) (by omega))
    fun c₇ hI₇ hA₇ h₇ => ?_
  have a27 : Agr c₁ c₇ [83053, 83054, 83055, 83031, 83030] :=
    ((((((Agr.of_upd h₂).trans (Agr.of_upd h₃)).trans (Agr.of_upd h₄)).trans
      (Agr.of_band h8₅ [])).trans (Agr.of_upd h₆)).trans (Agr.of_upd h₇)).mono (by simp)
  have a17 := a₁.trans a27
  have e31 : c₇.nreg 83031 = (N.region (c₀.nreg 83002)).chords.length := by
    rw [h₇, upd_ne (by norm_num), h₆, upd_eq, v₅]; rfl
  have e30 : c₇.nreg 83030 = 0 := by rw [h₇, upd_eq]
  have e53 : c₇.nreg 83053 = 0 := by
    rw [h₇, upd_ne (by norm_num), h₆, upd_ne (by norm_num), h8₅ _ (by norm_num) (by norm_num),
      h₄, upd_ne (by norm_num), h₃, upd_ne (by norm_num), h₂, upd_eq]
  have e54 : c₇.nreg 83054 = 0 := by
    rw [h₇, upd_ne (by norm_num), h₆, upd_ne (by norm_num), h8₅ _ (by norm_num) (by norm_num),
      h₄, upd_ne (by norm_num), h₃, upd_eq]
  have e55 : c₇.nreg 83055 = 2 := by
    rw [h₇, upd_ne (by norm_num), h₆, upd_ne (by norm_num), h8₅ _ (by norm_num) (by norm_num),
      h₄, upd_eq]
  have hI0 : CountI M P N c₀ f c₇ c₇ := by
    refine ⟨e31, by omega, by grind [cntP_zero], by grind [cntP_zero],
      b56.of_eq (a27 _ (by norm_num) (by norm_num) (by simp)),
      b57.of_eq (a27 _ (by norm_num) (by norm_num) (by simp)), ?_, ?_, Agr.refl _ _⟩
    · rw [a17 _ (by norm_num) (by norm_num) (by simp), hf12]
    · rw [a17 _ (by norm_num) (by norm_num) (by simp), hf13]
  have hμ : (countKB Kk + 2) * (c₇.nreg 83031 - c₇.nreg 83030) =
      (countKB Kk + 2) * (N.region (c₀.nreg 83002)).chords.length := by
    grind
  refine RS.seq ((RS.while (CountI M P N c₀ f c₇) (fun c => c.nreg 83031 - c.nreg 83030)
    (countKB Kk) (fun c hA ht => by omega)
    (fun c hIc hA ht hr => (countBody_rs hK hE hf hIc hA ht hr).mono le_rfl
      fun c' ⟨hA', h30⟩ => ⟨hA', by rw [h30, hA'.1]; have := hA.1; omega⟩)
    hI₇ hI0 (by omega)).mono (by rw [hμ]) (fun c h => h))
    fun c₈ hI₈ hA₈ ⟨⟨hL, htL, n53, n54, _, _, _, _, a₈⟩, hnt⟩ => ?_
  have hT : c₈.nreg 83030 = (N.region (c₀.nreg 83002)).chords.length := by omega
  rw [hT] at n53 n54
  have e55' : c₈.nreg 83055 = 2 := by
    rw [a₈ _ (by norm_num) (by norm_num) (by simp [countScr]), e55]
  have a18 : Agr c c₈ countW := (a17.trans a₈).mono (by simp [countScr, countW])
  unfold succS
  refine RS.seq (RS.const hI₈ (r := 83014) (v := 0) (by unfold Scr; omega) (by omega))
    fun c₉ hI₉ hA₉ h₉ => ?_
  have q53 : c₉.nreg 83053 = c₈.nreg 83053 := by rw [h₉, upd_ne (by norm_num)]
  have q54 : c₉.nreg 83054 = c₈.nreg 83054 := by rw [h₉, upd_ne (by norm_num)]
  have q55 : c₉.nreg 83055 = 2 := by rw [h₉, upd_ne (by norm_num), e55']
  have q14 : c₉.nreg 83014 = 0 := by rw [h₉, upd_eq]
  have a19 : Agr c c₉ countW := (a18.trans (Agr.of_upd h₉)).mono (by simp [countW])
  by_cases t1 : c₉.nreg 83053 < c₉.nreg 83055
  · refine RS.ifT t1 (RS.skip hI₉ ⟨by omega, ?_, a19⟩)
    omega
  · by_cases t2 : c₉.nreg 83054 < c₉.nreg 83055
    · refine RS.ifF t1 (RS.ifT t2 (RS.skip hI₉ ⟨by omega, ?_, a19⟩))
      omega
    · refine RS.ifF t1 (RS.ifF t2 ((RS.const hI₉ (r := 83014) (v := 1) (by unfold Scr; omega)
        hW1).mono (by norm_num) fun c' h' => ⟨by rw [h', upd_eq], ?_,
          (a19.trans (Agr.of_upd h')).mono (by simp [countW])⟩))
      rw [h', upd_eq, ← n53, ← n54, ← q53, ← q54]; omega

end

end Restore

end Chazelle.Core
