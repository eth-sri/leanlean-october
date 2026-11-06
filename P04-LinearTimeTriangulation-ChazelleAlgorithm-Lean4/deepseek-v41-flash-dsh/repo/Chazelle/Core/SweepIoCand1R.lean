module

public import Chazelle.Golf

public import Chazelle.Core.SweepIoCand1T

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
    iscr_sw (by unfold sw; omega) (by unfold sw; omega)
  ϴ prepL, okB, okI
  exact ⟨s 4800 le_rfl (⊛), s 4801 (⊛) (⊛),
    s 4804 (⊛) (⊛), s 4805 (⊛) (⊛),
    s 4806 (⊛) le_rfl, trivial⟩

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ c c₂ : Config} {J : Merge.Junction} {H : Host} {N₁ N₂ : NF}
  {E : ℕ} {z : Point} {L : Set ℝ}
variable {tabB : Stmt} {shrB bruteS : Stmt → Stmt} {κT κS κB KB : ℕ}

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
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
    ((IRS.block prepL hI₂ (prepL_ok c₂.nmem c₂.nreg)).mono (⊚ prepL) (fun _ h => h))
    ?_).mono (⋄) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' rfl
  simp only at hA₃ hA₃'
  have hA3 : regB c₂.nmem prepL c₂.nreg ALLOC = c₂.nreg ALLOC :=
    po _ (by unfold ALLOC sw; omega)
  have hM₃ : Mid P J z c { c₂ with nreg := regB c₂.nmem prepL c₂.nreg } L :=
    mid_keep hM (fun r _ hr _ => po r (by unfold sw at hr ⊢; omega)) (⊚ hA3)
      (fun _ _ => rfl)
  have hK₃ := hA.hK.fix hI₃
  have hns := normS_irs (dsc := sw 21) (pe := tE) (ph := tH) (o := nO) hI₃ hK₃
    (AEnv.ctxR hA hI₃) (by unfold tE tH sw; omega) (by unfold nO tE tH sw; omega)
    (by show regB _ _ _ tE < _; rw [p1, eE]; exact hqE)
    (by show ProperPos _ _ _ ⟨regB _ _ _ tE, regB _ _ _ tH⟩; rw [p1, p2, eE, eH]; exact hpp)
    (fun h => by
      exfalso
      have : regB c₂.nmem prepL c₂.nreg tE = c.nreg qE := Ρ p1, eE
      simp only at h
      omega)
    (by simp only; rw [hA3]; omega)
  refine IRS.seq hns ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨n1, n2, n3, n4, n5⟩
  simp only at n1 n2 n3 n4 n5 hA₄ hA₄'
  have hM₄ : Mid P J z c c₄ L := mid_keep hM₃
    (fun r a b d => n3 r a (by unfold sw at b; unfold tH sw; omega)
      (by unfold sw at b; unfold nO sw; omega) (by unfold sw at b; unfold nO sw; omega) d) n4 n5
  have hK₄ := hA.hK.fix hI₄
  refine IRS.seq (midB_irs hI₄ hK₄ (AEnv.ctxR hA hI₄)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨t1, t2, t3⟩
  have tA : c₅.nreg ALLOC = c₄.nreg ALLOC := t2 _ (by unfold OutM ALLOC sw; omega)
  have hM₅ : Mid P J z c c₅ L := mid_keep hM₄ (fun r _ hr _ => t2 r (by unfold OutM; unfold sw at hr ⊢; omega))
    (Ρ tA) (fun a _ => Ρ t3)
  -- the values at `c₅`
  have k3 : ∀ q, OutM q → q ≠ tH → q ≠ nO → q ≠ nO + 1 → q ≠ ALLOC → bandOf q ∉ oracleBands →
      c₅.nreg q = regB c₂.nmem prepL c₂.nreg q := fun q a b d e f g => by
    rw [t2 q a]; exact n3 q g b d e f
  have nb : ∀ q, 240000 ≤ q → q < 250000 → bandOf q ∉ oracleBands := fun q h1 h2 =>
    not_oracle_sw h1 h2
  have h34' : c₂.nreg (sw 34) = 2 * J.right.m + 7 := by
    rw [hI₂.hin _ (by unfold IFix sw; omega)]; exact h34
  have k1 : c₂.nreg K1 = 1 := hK₂.2.1
  have hNF : c₂.nmem (c₂.nreg (sw 4)) = N₂.nChords := by
    Ξ hI₂.hin _ (by unfold IFix sw; omega)
    exact (hA.hN₂ c₂.nmem (fun a ha => hI₂.hm a (by have := hA.hE; omega))).1
  have hm : J.right.m = J.m₂ := rfl
  have tree : TreeH P W X Ok J H N₁ N₂ E c₀ c c₅ z L F κB KB :=
    { hA := hA, hq := hq, hend := hend, hKB := hKB, hI₂ := hI₅, hM := hM₅, hnb := hnb
      vE := candFr_qE hM₅.2.2.2
      vy := by
        rw [k3 y34 (by unfold OutM y34 sw; omega) (by unfold y34 tH sw; omega)
          (by unfold y34 nO sw; omega) (by unfold y34 nO sw; omega)
          (by unfold y34 ALLOC sw; omega) (nb _ (by unfold y34 sw; omega)
          (by unfold y34 sw; omega)), p3, h34', k1, hm]
        omega
      vk := by
        rw [k3 k2 (by unfold OutM k2 sw; omega) (by unfold k2 tH sw; omega)
          (by unfold k2 nO sw; omega) (by unfold k2 nO sw; omega)
          (by unfold k2 ALLOC sw; omega) (nb _ (by unfold k2 sw; omega)
          (by unfold k2 sw; omega)), p4, hNF]
      vj := by
        rw [k3 jx (by unfold OutM jx sw; omega) (by unfold jx tH sw; omega)
          (by unfold jx nO sw; omega) (by unfold jx nO sw; omega)
          (by unfold jx ALLOC sw; omega) (nb _ (by unfold jx sw; omega)
          (by unfold jx sw; omega)), p5, hNF, eJ]
      vt := t1
      v41 := by
        rw [hI₅.hin _ (by unfold IFix sw; omega)]; exact h40 1 (⊛)
      hK := hA.hK.fix hI₅ }
  have vH : c₅.nreg tH = nhgt (chainModel J.right) (Qof P) ⟨c.nreg qE, c.nreg qH⟩ := by
    Ξ t2 tH (by unfold OutM tH sw; omega), n2, p1, p2, eE, eH
  have hd := dec_irs hT hS hBr hsh hBs hXl tree vH (by rw [← hKK]; omega)
  rw [← hKK] at hd
  exact hd

set_option maxRecDepth 200000 in
set_option maxHeartbeats 1000000 in
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
  have hKK' : KK = 16749 + κT + κS + LK + KB := by rw [hKK]; rfl
  rw [← hLK, ← hKK] at hroom ⊢
  have hbr1 : c.nreg bR = 1 := (hq.hbR.2).2 hz₂
  have hMod : ModB J (c.nreg bL) (c.nreg bR) 1 = J.right := by
    unfold ModB; rw [ite_eq_right (⋄), ite_eq_left ⟨rfl, hbr1⟩]
  have hloc : (c.nreg qE = 1 ∨ c.nreg qE = 3) ∨ (6 ≤ c.nreg qE ∧ z ∈ J.right.set) := by
    by_cases hb : c.nreg qE = 1 ∨ c.nreg qE = 3
    · exact Or.inl hb
    · obtain ⟨hzC, h6, -⟩ := tour_set J.right (Qof P) hpc hb hpp.1 hpp.2.1
      rw [hzpos] at hzC
      exact Or.inr ⟨h6, hzC⟩
  have hlhs := lhsR_irs (e := qE) (t := 1) hsh hBs hXl hA (by unfold OutL qE sw; omega) hI
    hqE hpp hzpos habs hloc (accOK_init accA _ _ _ _ hacc0) (⊛) hMod rfl
    (by rw [← hLK]; omega)
  rw [← hLK] at hlhs
  unfold cand1P
  refine IRS.seq (K₁ := LK) (K₂ := KK + 11076) hlhs ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
  have hM : Mid P J z c c₁ L' := ⟨a', fun τ hτ => (g' τ hτ).elim (fun h => absurd h (✓))
    (fun h => ⟨h.1, onCB_of_right J h.2⟩), geo' hgeo, candFr_lhw fr' hA' hm'⟩
  have hK₁ := hA.hK.fix hI₁
  have eE := candFr_qE hM.2.2.2
  have hbox : ∀ hb : c.nreg qE = 1 ∨ c.nreg qE = 3,
      IRS P W c₀ (boxB sh) c₁ (KK + 11068) (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
    intro hb
    have h := boxB_irs hsh hBs hXl hA hq hI₁ hM hb (by rw [← hLK]; omega)
    rw [← hLK] at h
    exact h.mono (⋄) (fun _ h => h)
  refine irs_ifEq' (K := KK + 11072) (⋄) (fun e => ?_) (fun e => ?_)
  · rw [eE, hK₁.2.1] at e
    exact (hbox (Or.inl e)).mono (⋄) (fun _ h => h)
  · rw [eE, hK₁.2.1] at e
    refine irs_ifEq' (K := KK + 11068) (⋄) (fun e' => ?_) (fun e' => ?_)
    · rw [eE, hK₁.2.2.2.2.2.2] at e'
      exact hbox (Or.inr e')
    · rw [eE, hK₁.2.2.2.2.2.2] at e'
      have ht := tourB_irs hT hS hBr hsh hBs hXl hA hq hend hKB hI₁ hM
        (by rintro (h | h) <;> contradiction) (by rw [← hLK, ← hKK]; omega)
      rw [← hLK, ← hKK] at ht
      exact ht

end Cand1

end

end SweepIo

end Chazelle.Core
