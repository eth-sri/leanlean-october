module
public import Chazelle.Core.ModelAccess
public import Chazelle.Programs.Address
public import Chazelle.Programs.Evidence
public import Chazelle.Programs.RegisterProof

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
  register_block

theorem prepL_ok {W : ℕ} (m f : ℕ → ℕ) : okB W m prepL f := by
  register_block

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
  obtain ⟨-, h6, -⟩ := from_facts tour_set
  simp at h6
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, -, -, h34, -, -, -, -, -⟩ := hA.hst
  obtain ⟨KK, hKK⟩ : ∃ KK, KK = kD κT κS (lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5)))
      (c₀.nreg (sw 6))) KB := ⟨_, rfl⟩
  rw [← hKK] at hroom ⊢
  have fr := hM.2.2.2
  have eE := candFr_qE fr
  have eH := candFr_qH fr
  have hK₂ := hA.hK.fix hI₂
  obtain ⟨p1, p2, p3, p4, p5, po⟩ := prepL_val c₂.nmem c₂.nreg
  unfold tourB
  refine (IRS.seq (K₁ := 5) (K₂ := 11015 + (20 + (KK + 28)))
    (from_facts (IRS.block prepL hI₂ (prepL_ok c₂.nmem c₂.nreg)).mono)
    ?_).mono (by omega) (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' rfl
  simp at hA₃ hA₃'
  have hA3 : regB c₂.nmem prepL c₂.nreg ALLOC = c₂.nreg ALLOC :=
    at_index po _
  have hM₃ : Mid P J z c { c₂ with nreg := regB c₂.nmem prepL c₂.nreg } L :=
    mid_keep hM (fun r _ hr _ => at_index po r) (by simp [hA3])
      (fun _ _ => rfl)
  have hns := normS_irs (dsc := sw 21) (pe := tE) (ph := tH) (o := nO) hI₃ (hA.hK.fix hI₃)
    (AEnv.ctxR hA hI₃) (by decide) (by decide)
    (by grind)
    (by grind)
    (fun h => by
      address_omega)
    (by grind)
  refine IRS.seq hns ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨n1, n2, n3, n4, n5⟩
  simp only at n1 n2 n3 n4 n5 hA₄ hA₄'
  have hM₄ : Mid P J z c c₄ L := mid_keep hM₃
    (fun r a b d => n3 r a (by address_omega)
      (by address_omega) (by address_omega) d) n4 n5
  refine IRS.seq (midB_irs hI₄ (hA.hK.fix hI₄) (AEnv.ctxR hA hI₄)) ?_
  rintro c₅ hI₅ hA₅ hA₅' ⟨t1, t2, t3⟩
  have hM₅ : Mid P J z c c₅ L := mid_keep hM₄ (fun r _ hr _ => at_index t2 r)
    (by address_omega) (fun a _ => by rw [t3])
  -- the values at `c₅`
  have k3 : ∀ q, OutM q → q ≠ tH → q ≠ nO → q ≠ nO + 1 → q ≠ ALLOC → bandOf q ∉ oracleBands →
      c₅.nreg q = regB c₂.nmem prepL c₂.nreg q := fun q a b d e f g => by
    grind
  have h34' : c₂.nreg (sw 34) = 2 * J.right.m + 7 := by
    rwa [at_index hI₂.hin _]
  have hNF : c₂.nmem (c₂.nreg (sw 4)) = N₂.nChords := by
    rw [at_index hI₂.hin _]
    exact (hA.hN₂ c₂.nmem (fun a ha => hI₂.hm a (by have := hA.hE; omega))).1
  have hm : J.right.m = J.m₂ := rfl
  have tree : TreeH P W X Ok J H N₁ N₂ E c₀ c c₅ z L F κB KB :=
    { hA := hA, hq := hq, hend := hend, hKB := hKB, hI₂ := hI₅, hM := hM₅, hnb := hnb
      vE := candFr_qE hM₅.2.2.2
      vy := by
        rw [at_index k3 y34, p3, h34', hK₂.2.1, hm]
        omega
      vk := by
        rw [at_index k3 k2, p4, hNF]
      vj := by
        rw [at_index k3 jx, p5, hNF, (candFr_qJ fr)]
      vt := t1
      v41 := by
        rw [at_index hI₅.hin _]; exact at_index h40 1
      hK := hA.hK.fix hI₅ }
  have vH : c₅.nreg tH = nhgt J.right.chainModel P.Qof ⟨c.nreg qE, c.nreg qH⟩ := by
    rw [at_index t2 tH, n2, p1, p2, eE, eH]
  have := guarded (dec_irs hT hS hBr hsh hBs hXl tree vH); grind

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
  have hMod : ModB J (c.nreg bL) (c.nreg bR) 1 = J.right := by
    unfold ModB; rw [guarded ite_eq_right, ite_eq_left ⟨rfl, ((hq.hbR.2).2 hz₂)⟩]
  have hloc : (c.nreg qE = 1 ∨ c.nreg qE = 3) ∨ (6 ≤ c.nreg qE ∧ z ∈ J.right.set) := by
    by_cases hb : c.nreg qE = 1 ∨ c.nreg qE = 3
    · exact Or.inl hb
    · obtain ⟨hzC, h6, -⟩ := from_facts tour_set <;> grind
  have hlhs := guarded (lhsR_irs (e := qE) (t := 1) hsh hBs hXl hA (by unfold OutL qE sw; omega) hI
    hqE hpp hzpos habs hloc (accOK_init accA _ _ _ _ hacc0))
  rw [← hLK] at hlhs
  unfold cand1P
  refine IRS.seq (K₁ := LK) (K₂ := KK + 11076) hlhs ?_
  rintro c₁ hI₁ hA₁ hA₁' ⟨⟨L', a', s', g', geo'⟩, fr', hA', hm'⟩
  have hM : Mid P J z c c₁ L' := ⟨a', fun τ hτ => (g' τ hτ).elim (fun h => absurd h (by simp))
    (fun h => ⟨h.1, onCB_of_right J h.2⟩), geo' hgeo, guarded candFr_lhw⟩
  have hK₁ := hA.hK.fix hI₁
  have eE := candFr_qE hM.2.2.2
  have hbox : ∀ hb : c.nreg qE = 1 ∨ c.nreg qE = 3,
      IRS P W c₀ (boxB sh) c₁ (KK + 11068) (fun c' => CandOut P J z c c' ∧ CandFr c c') := by
    intro hb
    have h := guarded (boxB_irs hsh hBs hXl hA hq hI₁ hM hb)
    rw [← hLK] at h
    exact from_facts h.mono
  refine irs_ifEq' (K := KK + 11072) (by omega) (fun e => ?_) (fun e => ?_)
  · rw [eE, hK₁.2.1] at e
    exact (hbox (Or.inl e)).mono (by omega) (fun _ h => h)
  · rw [eE, hK₁.2.1] at e
    refine irs_ifEq' (K := KK + 11068) (by omega) (fun e' => ?_) (fun e' => ?_)
    · grind [hK₁.2.2.2.2.2]
    · rw [eE, hK₁.2.2.2.2.2.2] at e'
      have ht := guarded (tourB_irs hT hS hBr hsh hBs hXl hA hq hend hKB hI₁ hM)
      grind

end Cand1

end

end SweepIo

end Chazelle.Core
