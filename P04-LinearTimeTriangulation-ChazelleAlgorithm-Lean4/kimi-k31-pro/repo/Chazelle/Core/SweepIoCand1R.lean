module

public import Chazelle.Core.SweepIoCand1T
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `1`, the run

* `tourB_irs`: a tour position (`prepL`, `normS`, `midB`, the decision tree);
* `cand1P_irs`: the candidate step (the local hit in the model of `C₂`, then the classes), from
  the bodies of the contracts of the table step, the shared-vertex step and the brute-force
  shot.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

namespace Cand1

theorem prepL_val (m f : ℕ → ℕ) :
    regB m prepL f tE = f qE ∧ regB m prepL f tH = f qH ∧
      regB m prepL f y34 = f (sw 34) - f K1 ∧ regB m prepL f k2 = m (f (sw 4)) ∧
      regB m prepL f jx = f qJ - m (f (sw 4)) ∧
      (∀ q, (q < sw 4800 ∨ sw 4806 < q) → regB m prepL f q = f q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩ <;>
    simp [prepL, regB, regI, upd, tE, tH, y34, k2, jx, sw, qE, qH, qJ, K1]
  unfold sw at hq
  simp [show q ≠ 244800 by omega, show q ≠ 244801 by omega, show q ≠ 244804 by omega,
    show q ≠ 244805 by omega, show q ≠ 244806 by omega]

theorem prepL_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m prepL f := by
  have s : ∀ j, 4800 ≤ j → j ≤ 4806 → IScr (sw j) := fun j h1 h2 =>
    iscr_sw (by ufo sw) (by ufo sw)
  simp only [prepL, okB, okI]
  exact ⟨s 4800 le_rfl (by norm_num), s 4801 (by norm_num) (by norm_num),
    s 4804 (by norm_num) (by norm_num), s 4805 (by norm_num) (by norm_num),
    s 4806 (by norm_num) le_rfl, trivial⟩

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}
variable {tabB : Stmt} {shrB bruteS : Stmt → Stmt} {κT κS κB KB : ℕ}

/-- **A tour position.** -/
theorem tourB_irs (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hq : QState P J 1 z c)
    (hend : c.nreg qJ < 2 * N₂.nChords →
      (c.nreg qE, c.nreg qH, c.nreg qD) = (sweepEndQ N₂.chords).getD (c.nreg qJ) (0, 0, 0))
    (hKB : BruteQ J N₂ (c.nreg qJ) z →
      κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ KB)
    (hI₂ : IInv W c₀ c₂) (hM : Mid P J z c c₂ L) (hnb : ¬ (c.nreg qE = 1 ∨ c.nreg qE = 3))
    (hroom : c₂.nreg ALLOC + (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB + 11068) ≤ W) :
    IRS P W c₀ (tourB tabB shrB bruteS sh) c₂
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB + 11068)
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, hpc, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  obtain ⟨-, h6, -⟩ := tour_set J.right (Qof P) hpc hnb hpp.1 hpp.2.1
  simp only at h6
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -, -, -, -, -⟩ := hA.hst
  obtain ⟨KK, hKK⟩ : ∃ KK, KK = kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB := ⟨_, rfl⟩
  rw [← hKK] at hroom ⊢
  have fr := hM.2.2.2
  have eE := candFr_qE fr
  have eH := candFr_qH fr
  have eJ := candFr_qJ fr
  have hK₂ := hA.hK.fix hI₂
  obtain ⟨p1, p2, p3, p4, p5, po⟩ := prepL_val c₂.nmem c₂.nreg
  unfold tourB
  refine (IRS.seq (K₁ := 5) (K₂ := 11015 + (20 + (KK + 28)))
    ((IRS.block prepL hI₂ (prepL_ok c₂.nmem c₂.nreg)).mono (by simp [prepL]) (fun _ => id))
    ?_).mono (by omega) (fun _ => id)
  rintro c₃ hI₃ hA₃ hA₃' rfl
  simp only at hA₃ hA₃'
  have hA3 : regB c₂.nmem prepL c₂.nreg ALLOC = c₂.nreg ALLOC :=
    po _ (by ufo ALLOC sw)
  have hM₃ : Mid P J z c { c₂ with nreg := regB c₂.nmem prepL c₂.nreg } L :=
    mid_keep hM (fun r _ hr _ => po r (by ufo sw at hr ⊢)) (by simp [hA3])
      (fun _ _ => rfl)
  have hK₃ := hA.hK.fix hI₃
  have hns := normS_irs (dsc := sw 21) (pe := tE) (ph := tH) (o := nO) hI₃ hK₃
    (AEnv.ctxR hA hI₃) (by ufo tE tH sw) (by ufo nO tE tH sw)
    (by show regB _ _ _ tE < _; rwx [p1, eE])
    (by show ProperPos _ _ _ ⟨regB _ _ _ tE, regB _ _ _ tH⟩; rwx [p1, p2, eE, eH])
    (fun h => by
      exfalso
      have : regB c₂.nmem prepL c₂.nreg tE = c.nreg qE := by rw [p1, eE]
      simp only at h
      omega)
    (by simp only; rwo [hA3])
  refine IRS.seq hns ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨n1, n2, n3, n4, n5⟩
  simp only at n1 n2 n3 n4 n5 hA₄ hA₄'
  have hM₄ : Mid P J z c c₄ L := mid_keep hM₃
    (fun r a b d => n3 r a (by unfold sw at b; ufo tH sw)
      (by unfold sw at b; ufo nO sw) (by unfold sw at b; ufo nO sw) d) n4 n5
  have hK₄ := hA.hK.fix hI₄
  refine IRS.seq (midB_irs hI₄ hK₄ (AEnv.ctxR hA hI₄)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨t1, t2, t3⟩
  have tA : c₅.nreg ALLOC = c₄.nreg ALLOC := t2 _ (by ufo OutM ALLOC sw)
  have hM₅ : Mid P J z c c₅ L := mid_keep hM₄ (fun r _ hr _ => t2 r (by unfold OutM; ufo sw at hr ⊢))
    (by rw [tA]) (fun a _ => by rw [t3])
  -- the values at `c₅`
  have k3 : ∀ q, OutM q → q ≠ tH → q ≠ nO → q ≠ nO + 1 → q ≠ ALLOC → bandOf q ∉ oracleBands →
      c₅.nreg q = regB c₂.nmem prepL c₂.nreg q := fun q a b d e f g => by
    rw [t2 q a]; exact n3 q g b d e f
  have nb : ∀ q, 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands := fun q h1 h2 =>
    not_oracle_sw h1 h2
  have h34' : c₂.nreg (sw 34) = 2 * J.right.m + 7 := by
    rwx [hI₂.hin _ (by ufo IFix sw)]
  have k1 : c₂.nreg K1 = 1 := hK₂.2.1
  have hNF : c₂.nmem (c₂.nreg (sw 4)) = N₂.nChords := by
    rw [hI₂.hin _ (by ufo IFix sw)]
    exact (hA.hN₂ c₂.nmem (fun a ha => hI₂.hm a (by have := hA.hE; omega))).1
  have hm : J.right.m = J.m₂ := rfl
  have tree : TreeH P W X Ok J H N₁ N₂ E c₀ c c₅ z L F κB KB :=
    { hA := hA, hq := hq, hend := hend, hKB := hKB, hI₂ := hI₅, hM := hM₅, hnb := hnb
      vE := candFr_qE hM₅.2.2.2
      vy := by
        rw [k3 y34 (by ufo OutM y34 sw) (by ufo y34 tH sw)
          (by ufo y34 nO sw) (by ufo y34 nO sw)
          (by ufo y34 ALLOC sw) (nb _ (by ufo y34 sw)
          (by ufo y34 sw)), p3, h34', k1, hm]
        omega
      vk := by
        rw [k3 k2 (by ufo OutM k2 sw) (by ufo k2 tH sw)
          (by ufo k2 nO sw) (by ufo k2 nO sw)
          (by ufo k2 ALLOC sw) (nb _ (by ufo k2 sw)
          (by ufo k2 sw)), p4, hNF]
      vj := by
        rw [k3 jx (by ufo OutM jx sw) (by ufo jx tH sw)
          (by ufo jx nO sw) (by ufo jx nO sw)
          (by ufo jx ALLOC sw) (nb _ (by ufo jx sw)
          (by ufo jx sw)), p5, hNF, eJ]
      vt := t1
      v41 := by
        rw [hI₅.hin _ (by ufo IFix sw)]; exact h40 1 (by norm_num)
      hK := hA.hK.fix hI₅ }
  have vH : c₅.nreg tH = nhgt (chainModel J.right) (Qof P) ⟨c.nreg qE, c.nreg qH⟩ := by
    rw [t2 tH (by ufo OutM tH sw), n2, p1, p2, eE, eH]
  have hd := dec_irs hT hS hBr hsh hBs hXl tree vH (by rwo [← hKK])
  rw [← hKK] at hd
  exact hd

/-- **The candidate step of side `1`.** -/
theorem cand1P_irs (hT : TabBody tabB κT) (hS : ShrBody shrB κS) (hBr : BruteBody bruteS κB)
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) (hq : QState P J 1 z c)
    (hend : c.nreg qJ < 2 * N₂.nChords →
      (c.nreg qE, c.nreg qH, c.nreg qD) = (sweepEndQ N₂.chords).getD (c.nreg qJ) (0, 0, 0))
    (hKB : BruteQ J N₂ (c.nreg qJ) z →
      κB * (N₁.arcs.length + 1) * (F (c₀.nreg (sw 5)) + 1) ≤ KB)
    (hacc0 : c.nreg accA = 0)
    (hroom : c.nreg ALLOC + (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) +
      (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB + 11076)) ≤ W) :
    IRS P W c₀ (cand1P tabB shrB bruteS sh) c
      (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) +
        (kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) KB + 11076))
      (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
  obtain ⟨hzpos, hqE, hpp, habs, hz₂, hpc, hgeo, hσ, h1H, hHn, hht⟩ := q1_facts hq
  obtain ⟨LK, hLK⟩ : ∃ LK, LK = lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) :=
    ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ KK, KK = kD κT κS LK KB := ⟨_, rfl⟩
  have hKK' : KK = 16749 + κT + κS + LK + KB := by rwr [hKK]
  rw [← hLK, ← hKK] at hroom ⊢
  have hbr1  := (hq.hbR.2).2 hz₂
  have hMod : ModB J (c.nreg bL) (c.nreg bR) 1 = J.right := by
    unfold ModB; rw [ite_eq_right (by omega), ite_eq_left ⟨rfl, hbr1⟩]
  have hloc : (c.nreg qE = 1 ∨ c.nreg qE = 3) ∨ (6 ≤ c.nreg qE ∧ z ∈ J.right.set) := by
    by_cases hb : c.nreg qE = 1 ∨ c.nreg qE = 3
    · exact Or.inl hb
    · obtain ⟨hzC, h6, -⟩ := tour_set J.right (Qof P) hpc hb hpp.1 hpp.2.1
      rw [hzpos] at hzC
      exact Or.inr ⟨h6, hzC⟩
  have hlhs := lhsR_irs (e := qE) (t := 1) hsh hBs hXl hA (by ufo OutL qE sw) hI
    hqE hpp hzpos habs hloc (accOK_init accA _ _ _ _ hacc0) (by norm_num) hMod rfl
    (by rwo [← hLK])
  rw [← hLK] at hlhs
  unfold cand1P
  refine IRS.seq (K₁ := LK) (K₂ := KK + 11076) hlhs ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
  have hM : Mid P J z c c₁ L' := ⟨a', fun τ hτ => (g' τ hτ).elim (fun h => absurd h (by simp))
    (fun h => ⟨h.1, onCB_of_right J h.2⟩), geo' hgeo, candFr_lhw fr' hA' hm'⟩
  have hK₁ := hA.hK.fix hI₁
  have eE := candFr_qE hM.2.2.2
  have hbox : ∀ hb : c.nreg qE = 1 ∨ c.nreg qE = 3,
      IRS P W c₀ (boxB sh) c₁ (KK + 11068) (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
    intro hb
    have h := boxB_irs hsh hBs hXl hA hq hI₁ hM hb (by rwo [← hLK])
    rw [← hLK] at h
    exact h.mono (by omega) (fun _ => id)
  refine irs_ifEq' (K := KK + 11072) (by omega) (fun e => ?_) (fun e => ?_)
  · rw [eE, hK₁.2.1] at e
    exact (hbox (Or.inl e)).mono (by omega) (fun _ => id)
  · rw [eE, hK₁.2.1] at e
    refine irs_ifEq' (K := KK + 11068) (by omega) (fun e' => ?_) (fun e' => ?_)
    · rw [eE, hK₁.2.2.2.2.2.2] at e'
      exact hbox (Or.inr e')
    · rw [eE, hK₁.2.2.2.2.2.2] at e'
      have ht := tourB_irs hT hS hBr hsh hBs hXl hA hq hend hKB hI₁ hM
        (by rintro (h | h) <;> contradiction) (by rwo [← hLK, ← hKK])
      rw [← hLK, ← hKK] at ht
      exact ht

end Cand1

end

end SweepIo

end Chazelle.Core
