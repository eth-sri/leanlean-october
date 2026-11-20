module

public import Chazelle.Core.ShotListRun
public import Chazelle.Core.SpecMerge

/-!
# Shooting at a list of arcs with holes, part 7: the cutting recursion

`levF sh R f ℓ` cuts the arc of level `ℓ` by the hole `ℓ` (if present) and runs level `ℓ + 1` on
each piece; level `3` (`f = 0`) is the leaf.  The pieces reached are `levLeaves` (the program's
recursion, read in the registers), and `lev_exec` proves by induction on `f` that the running
minimum extends to their union (`pcSet`).
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)

@[expose] public section

/-! ## The program -/

/-- Move the second piece of level `ℓ` into the arc registers of level `ℓ + 1`. -/
def copy2List (R ℓ : ℕ) : List (ℕ × ℕ) := [(rL R ℓ + 10, rL R ℓ + 4), (rL R ℓ + 11, rL R ℓ + 5),
  (rL R ℓ + 12, rL R ℓ + 6), (rL R ℓ + 13, rL R ℓ + 7)]

/-- **The cutting recursion**: `f` levels from level `ℓ`. -/
def levF (sh : Stmt) (R : ℕ) : ℕ → ℕ → Stmt
  | 0, _ => leaf sh R
  | f + 1, ℓ => .seq (cutB R ℓ) (.ifLtN (R + 30) (rL R ℓ + 8)
      (.seq (levF sh R f (ℓ + 1)) (.ifLtN (R + 31) (rL R ℓ + 8)
        (.seq (block (copies (copy2List R ℓ))) (levF sh R f (ℓ + 1))) .skip)) .skip)

/-! ## The pieces -/

/-- The points of a list of pieces. -/
def pcSet (M : Model) (Q : Polygon) (L : List (WPos × WPos)) : Set Point :=
  ⋃ p ∈ L, M.arcSet (M.key Q p.1) (M.key Q p.2)

theorem pcSet_nil (M : Model) (Q : Polygon) : pcSet M Q [] = ∅ := by simp [pcSet]

theorem pcSet_single (M : Model) (Q : Polygon) (p : WPos × WPos) :
    pcSet M Q [p] = M.arcSet (M.key Q p.1) (M.key Q p.2) := by simp [pcSet]

theorem pcSet_append (M : Model) (Q : Polygon) (L L' : List (WPos × WPos)) :
    pcSet M Q (L ++ L') = pcSet M Q L ∪ pcSet M Q L' := by
  ext x; simp [pcSet, or_and_right, exists_or]

/-- **The pieces reached by the recursion** from level `ℓ` (`f` levels), with the holes read in
the registers of `c`. -/
noncomputable def levLeaves (M : Model) (Q : Polygon) (c : Config) (R : ℕ) :
    ℕ → ℕ → WPos × WPos → List (WPos × WPos)
  | 0, _, q => [q]
  | f + 1, ℓ, q => (levPieces M Q (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) q.1 q.2
      (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ))).flatMap (levLeaves M Q c R f (ℓ + 1))

/-- `levLeaves` reads only the hole registers and the level constants. -/
theorem levLeaves_congr (M : Model) (Q : Polygon) {c c' : Config} {R : ℕ}
    (h : ∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) → c'.nreg (R + i) = c.nreg (R + i)) :
    ∀ f ℓ, f + ℓ ≤ 3 → ∀ q, levLeaves M Q c' R f ℓ q = levLeaves M Q c R f ℓ q
  | 0, _, _, _ => rfl
  | f + 1, ℓ, hf, q => by
    simp only [levLeaves]
    have e1 : c'.nreg (R + 30 + ℓ) = c.nreg (R + 30 + ℓ) := by
      rw [show R + 30 + ℓ = R + (30 + ℓ) by omega]; exact h _ (Or.inr (by omega))
    have e2 : c'.nreg (R + 9) = c.nreg (R + 9) := h 9 (Or.inl (by omega))
    have e3 : c'.nreg (R + 10 + 2 * ℓ) = c.nreg (R + 10 + 2 * ℓ) :=
      by rw [show R + 10 + 2 * ℓ = R + (10 + 2 * ℓ) by omega]; exact h _ (Or.inl (by omega))
    have e4 : c'.nreg (R + 11 + 2 * ℓ) = c.nreg (R + 11 + 2 * ℓ) :=
      by rw [show R + 11 + 2 * ℓ = R + (11 + 2 * ℓ) by omega]; exact h _ (Or.inl (by omega))
    simp only [e1, e2, e3, e4]
    congr 1
    funext p
    exact levLeaves_congr M Q h f (ℓ + 1) (by omega) p

/-! ## Pieces with good ends -/

/-- **A piece with good ends**: normalised, in range, and each a vertex or an inner point. -/
def PieceOK (M : Model) (Q : Polygon) (n : ℕ) (p : WPos × WPos) : Prop :=
  NormPos M Q n p.1 ∧ NormPos M Q n p.2 ∧ p.1.edge < M.W.n ∧ p.2.edge < M.W.n ∧
    (p.1.hgt = 0 ∨ M.InnerPt (M.pos Q p.1)) ∧ (p.2.hgt = 0 ∨ M.InnerPt (M.pos Q p.2))

/-- The ends of a piece of `levPieces` are ends of the arc or hole vertices. -/
theorem levPieces_ends {M : Model} {Q : Polygon} {hp : Prop} [Decidable hp] {a b : WPos}
    {x y : ℕ} {p : WPos × WPos} (h : p ∈ levPieces M Q hp a b x y) :
    (p.1 = a ∨ p.1 = b ∨ p.1 = ⟨x, 0⟩ ∨ p.1 = ⟨y, 0⟩) ∧
      (p.2 = a ∨ p.2 = b ∨ p.2 = ⟨x, 0⟩ ∨ p.2 = ⟨y, 0⟩) := by
  unfold levPieces at h
  split_ifs at h
  · obtain ⟨u, v⟩ := p
    rcases cut1_cases (M.key Q) a b ⟨x, 0⟩ ⟨y, 0⟩ h with
      ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ |
      ⟨-, -, -, rfl, rfl⟩ | ⟨-, -, -, -, rfl, rfl⟩ | ⟨-, -, -, rfl, rfl⟩ <;> simp
  · simp only [List.mem_singleton] at h; subst h; simp

/-- **Good ends are preserved by cutting.** -/
theorem pieceOK_levPieces {M : Model} {Q : Polygon} {n : ℕ} {hp : Prop} [Decidable hp]
    {a b : WPos} {x y : ℕ} (hab : PieceOK M Q n (a, b)) (hx : x < M.W.n) (hy : y < M.W.n)
    {p : WPos × WPos} (h : p ∈ levPieces M Q hp a b x y) : PieceOK M Q n p := by
  obtain ⟨na, nb, ea, eb, ia, ib⟩ := hab
  have good : ∀ u : WPos, (u = a ∨ u = b ∨ u = ⟨x, 0⟩ ∨ u = ⟨y, 0⟩) →
      NormPos M Q n u ∧ u.edge < M.W.n ∧ (u.hgt = 0 ∨ M.InnerPt (M.pos Q u)) := by
    rintro u (rfl | rfl | rfl | rfl)
    · exact ⟨na, ea, ia⟩
    · exact ⟨nb, eb, ib⟩
    · exact ⟨normPos_vtx M Q n x, hx, Or.inl rfl⟩
    · exact ⟨normPos_vtx M Q n y, hy, Or.inl rfl⟩
  obtain ⟨h1, h2⟩ := levPieces_ends h
  obtain ⟨g1, g1e, g1i⟩ := good _ h1
  obtain ⟨g2, g2e, g2i⟩ := good _ h2
  exact ⟨g1, g2, g1e, g2e, g1i, g2i⟩

/-! ## The recursion on the RAM -/

/-- The registers of the caller's block written from level `ℓ` on. -/
def WrLev (R ℓ : ℕ) (r : ℕ) : Prop := (R + 20 ≤ r ∧ r < R + 28) ∨ (rL R ℓ + 4 ≤ r ∧ r < R + 300)

/-- The cost of `f` levels. -/
def levCost (Fg f : ℕ) : ℕ := (2 ^ (f + 1) - 1) * (Fg + 30000)

theorem levCost_succ (Fg f : ℕ) : levCost Fg (f + 1) = 2 * levCost Fg f + (Fg + 30000) := by
  unfold levCost
  have : 1 ≤ 2 ^ (f + 1) := Nat.one_le_two_pow
  rw [pow_succ]
  zify [this, show 1 ≤ 2 ^ (f + 1) * 2 by omega]
  ring

theorem levCost_zero (Fg : ℕ) : levCost Fg 0 = Fg + 30000 := by simp [levCost]

theorem rL_succ (R ℓ : ℕ) : rL R (ℓ + 1) = rL R ℓ + 10 := by unfold rL; ring

/-- A register of the caller's block outside the written ones survives a named frame. -/
theorem frameR_keep {R : ℕ} (hR : RegsOK R) {Wr : ℕ → Prop} {c c' : Config} {k : ℕ}
    (h : FrameR oracleBands Wr c c' k) {i : ℕ} (hi : i < 300) (hw : ¬ Wr (R + i)) :
    c'.nreg (R + i) = c.nreg (R + i) :=
  h.1 _ (band_R hR hi) (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw

/-- **The cutting recursion**: from level `ℓ` (`f + ℓ = 3`), the running minimum extends to the
pieces `levLeaves` of the arc of level `ℓ`. -/
theorem lev_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {R : ℕ} (hR : RegsOK R) {H : Host} {C : Chain}
    {o : Origin} (hol : o.Lt P.n (chainModel C))
    (hof : (∃ q, o = .walk ⟨q, 0⟩) ∨ ((chainModel C).InnerPt (o.eval (chainModel C) (Qof P)) ∧
      ∀ x, o = .walk x → ProperPos (chainModel C) (Qof P) P.n x))
    (hoy : |(o.eval (chainModel C) (Qof P)).2| < C.radius) :
    ∀ (f ℓ : ℕ) (c : Config) (S : Set Point), f + ℓ = 3 → WordsBounded W c →
      ShotCtx P W X Ok R c H C → OriginIn c (R + 3) o →
      PieceOK (chainModel C) (Qof P) P.n (pieceR c (rL R ℓ)) →
      (∀ j, ℓ ≤ j → j < 3 → c.nreg (R + 30 + j) < c.nreg (R + 9) →
        c.nreg (R + 10 + 2 * j) < (chainModel C).W.n ∧
          c.nreg (R + 11 + 2 * j) < (chainModel C).W.n) →
      (∀ p ∈ levLeaves (chainModel C) (Qof P) c R f ℓ (pieceR c (rL R ℓ)),
        (chainModel C).arcWt ((chainModel C).key (Qof P) p.1) ((chainModel C).key (Qof P) p.2) ≤
          c.nreg (R + 7) ∧
        o.eval (chainModel C) (Qof P) ∉ (chainModel C).arcSet ((chainModel C).key (Qof P) p.1)
          ((chainModel C).key (Qof P) p.2)) →
      BestOK P C R c S (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg (R + 6))) →
      c.nreg ALLOC + levCost (F (c.nreg (R + 7))) f ≤ W →
      ∃ c' k, Exec P W (levF sh R f ℓ) c c' k ∧ k ≤ levCost (F (c.nreg (R + 7))) f ∧
        BestOK P C R c' (S ∪ pcSet (chainModel C) (Qof P)
          (levLeaves (chainModel C) (Qof P) c R f ℓ (pieceR c (rL R ℓ))))
          (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg (R + 6))) ∧
        FrameR oracleBands (WrLev R ℓ) c c' k
  | 0, ℓ, c, S, hf, hw, hctx, ho, hpc, _, hleaf, hbest, hroom => by
    have hℓ : ℓ = 3 := by omega
    subst hℓ
    have hL3 : rL R 3 = R + 70 := by unfold rL; omega
    rw [hL3] at hpc hleaf ⊢
    obtain ⟨n1, n2, e1, e2, i1, i2⟩ := hpc
    obtain ⟨hwt, hon⟩ := hleaf (pieceR c (R + 70)) (by simp [levLeaves])
    rw [levCost_zero] at hroom ⊢
    have hroom' : c.nreg ALLOC + F (c.nreg (R + 7)) + 17500 ≤ W := by
      refine le_trans ?_ hroom
      rw [add_assoc]
      exact Nat.add_le_add_left (Nat.add_le_add_left (by norm_num) _) _
    obtain ⟨c', k, ex, hk, hb, fr⟩ := leaf_exec hsh hBs hXl hR c hw hctx n1.1 n2.1 e1 e2 i1 i2
      hwt ho hol hof hon hoy hbest hroom'
    refine ⟨c', k, ex, by omega, ?_, fr.mono le_rfl (fun r hr => ?_) le_rfl⟩
    · simp only [levLeaves, pcSet_single]; exact hb
    · rcases hr with hr | hr
      · exact Or.inl hr
      · right; unfold rL; unfold RegsOK at hR; omega
  | f + 1, ℓ, c, S, hf, hw, hctx, ho, hpc, hholes, hleaf, hbest, hroom => by
    have hℓ : ℓ ≤ 2 := by omega
    have hR' := hR; unfold RegsOK at hR'
    set M := chainModel C with hM
    set Q := Qof P
    set Fg := F (c.nreg (R + 7))
    set q := pieceR c (rL R ℓ) with hq
    have hLd : rL R ℓ = R + 40 + 10 * ℓ := rfl
    have hctx0 := hctx
    obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ := hctx0
    obtain ⟨na, nb, ea, eb, ia, ib⟩ := hpc
    have hlc := levCost_succ Fg f
    -- the cut
    obtain ⟨c₁, k₁, e₁, hk₁, pc₁, f₁⟩ := cutB_exec (P := P) hR hℓ c hw (by
      unfold hostWords at hHW; omega) hG hHW (H := H) (C := C) hctx.chainWF
      (by rw [h34]; exact hC) hm (by omega) h30 na nb ea eb
    set ps := levPieces M Q (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) q.1 q.2
      (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ)) with hps
    have k1 : ∀ r, R ≤ r → r < rL R ℓ + 4 → c₁.nreg r = c.nreg r := fun r h1 h2 => f₁.1 r (by
      have hb := bprim_R' hR h1 (by omega)
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, hb, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_false,
        Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
      omega)
    have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 _ (by
      unfold ALLOC
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, Bprim, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_false_iff,
        decide_eq_false_iff_not, beq_eq_false_iff_ne]
      omega)
    have F01 : FrameR oracleBands (WrLev R ℓ) c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, List.map_cons, List.map_nil,
        List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, Bool.or_eq_true,
        decide_eq_true_eq, beq_iff_eq] at hr
      rcases hr with ((hr | (hr | hr) | hr) | hr) | hr
      · left; right; unfold rL; omega
      · left; right; unfold rL; omega
      · exact Or.inr (band_prim hr)
      · exact Or.inr (band_locate (by omega))
      · left; right; unfold rL; omega
      · left; right; exact ⟨hr.1, by rw [hLd] at hr; omega⟩) (by
        unfold ALLOC
        simp only [Bcut, Bouts, cmpOuts, cmpList, Boff, Bform, Bprim, List.map_cons,
          List.map_nil, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false,
          Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
        omega) _
    have ctx₁ : ShotCtx P W X Ok R c₁ H C := ShotCtx.frame hXl hctx F01
      (fun i hi => k1 _ (by omega) (by unfold rL; omega))
    have ho₁ : OriginIn c₁ (R + 3) o := originIn_copy ho (k1 _ (by omega) (by unfold rL; omega))
      (k1 _ (by omega) (by unfold rL; omega)) (k1 _ (by omega) (by unfold rL; omega))
    have r6 : c₁.nreg (R + 6) = c.nreg (R + 6) := k1 _ (by omega) (by unfold rL; omega)
    have r7 : c₁.nreg (R + 7) = c.nreg (R + 7) := k1 _ (by omega) (by unfold rL; omega)
    have best₁ : BestOK P C R c₁ S (o.eval M Q) (dirOf (c₁.nreg (R + 6))) := by
      rw [r6]
      exact hbest.congr (k1 _ (by omega) (by unfold rL; omega))
        (k1 _ (by omega) (by unfold rL; omega)) (k1 _ (by omega) (by unfold rL; omega))
        (k1 _ (by omega) (by unfold rL; omega)) (k1 _ (by omega) (by unfold rL; omega))
        (k1 _ (by omega) (by unfold rL; omega)) (k1 _ (by omega) (by unfold rL; omega))
    have hlv : ∀ (c' : Config), (∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) →
        c'.nreg (R + i) = c.nreg (R + i)) → ∀ p, levLeaves M Q c' R f (ℓ + 1) p =
          levLeaves M Q c R f (ℓ + 1) p := fun c' h' =>
      levLeaves_congr M Q h' f (ℓ + 1) (by omega)
    have hleaves : levLeaves M Q c R (f + 1) ℓ q = ps.flatMap (levLeaves M Q c R f (ℓ + 1)) := rfl
    -- the pieces are good
    have hgood : ∀ p ∈ ps, PieceOK M Q P.n p := by
      intro p hp
      by_cases hpres : c.nreg (R + 30 + ℓ) < c.nreg (R + 9)
      · obtain ⟨hx, hy⟩ := hholes ℓ le_rfl (by omega) hpres
        exact pieceOK_levPieces ⟨na, nb, ea, eb, ia, ib⟩ hx hy hp
      · simp only [hps, levPieces, ite_no _ _ hpres, List.mem_singleton] at hp
        subst hp; exact ⟨na, nb, ea, eb, ia, ib⟩
    obtain ⟨hcnt, hlen, hp0, hp1⟩ := pc₁
    have w₁ := e₁.wb_right
    have z₁ : c₁.nreg (R + 30) = 0 := by rw [k1 _ (by omega) (by unfold rL; omega), h30]
    have o₁ : c₁.nreg (R + 31) = 1 := by rw [k1 _ (by omega) (by unfold rL; omega), h31]
    -- the recursive call on a piece in the registers of level `ℓ + 1`
    have call : ∀ (cc : Config) (S' : Set Point) (p : WPos × WPos), p ∈ ps → WordsBounded W cc →
        ShotCtx P W X Ok R cc H C → OriginIn cc (R + 3) o →
        (∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) ∨ i = 6 ∨ i = 7 →
          cc.nreg (R + i) = c.nreg (R + i)) →
        pieceR cc (rL R (ℓ + 1)) = p →
        BestOK P C R cc S' (o.eval M Q) (dirOf (c.nreg (R + 6))) →
        cc.nreg ALLOC + levCost Fg f ≤ W →
        ∃ c' k, Exec P W (levF sh R f (ℓ + 1)) cc c' k ∧ k ≤ levCost Fg f ∧
          BestOK P C R c' (S' ∪ pcSet M Q (levLeaves M Q c R f (ℓ + 1) p)) (o.eval M Q)
            (dirOf (c.nreg (R + 6))) ∧ FrameR oracleBands (WrLev R (ℓ + 1)) cc c' k := by
      intro cc S' p hp hwc hcc hoc hreg' hpc' hbc hrc
      have e6 := hreg' 6 (Or.inr (Or.inr (Or.inl rfl)))
      have e7 := hreg' 7 (Or.inr (Or.inr (Or.inr rfl)))
      have hl := hlv cc (fun i hi => hreg' i (by omega))
      obtain ⟨c', k, ex, hk, hb, fr⟩ := lev_exec hsh hBs hXl hR hol hof hoy f (ℓ + 1) cc S'
        (by omega) hwc hcc hoc (by rw [hpc']; exact hgood p hp)
        (fun j hj1 hj2 hj3 => by
          have e30 := hreg' (30 + j) (Or.inr (Or.inl (by omega)))
          have e9 := hreg' 9 (Or.inl (by omega))
          have ex1 := hreg' (10 + 2 * j) (Or.inl (by omega))
          have ex2 := hreg' (11 + 2 * j) (Or.inl (by omega))
          have a1 : R + 30 + j = R + (30 + j) := by omega
          have a2 : R + 10 + 2 * j = R + (10 + 2 * j) := by omega
          have a3 : R + 11 + 2 * j = R + (11 + 2 * j) := by omega
          rw [a1, e30, e9] at hj3
          have hh := hholes j (by omega) hj2 (by rw [a1]; exact hj3)
          rw [a2, a3] at hh ⊢
          rw [ex1, ex2]
          exact hh)
        (fun p' hp' => by
          rw [hpc', hl] at hp'
          have := hleaf p' (by rw [hleaves]; exact List.mem_flatMap.2 ⟨p, hp, hp'⟩)
          rw [e7]; exact this)
        (by rw [e6]; exact hbc) (by rw [e7]; exact hrc)
      rw [e7] at hk
      rw [hpc', hl, e6] at hb
      exact ⟨c', k, ex, hk, hb, fr⟩
    have hcnt' : c₁.nreg (rL R ℓ + 8) = ps.length := hcnt
    have hlen' : ps.length ≤ 2 := hlen
    have hp0' : ∀ p, ps[0]? = some p → pieceR c₁ (rL R (ℓ + 1)) = p := fun p hp => by
      rw [rL_succ]; exact hp0 p hp
    have hp1' : ∀ p, ps[1]? = some p → pieceR c₁ (rL R ℓ + 4) = p := hp1
    have regs1 : ∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) ∨ i = 6 ∨ i = 7 →
        c₁.nreg (R + i) = c.nreg (R + i) := fun i hi =>
      k1 _ (by omega) (by unfold rL; omega)
    have wr1 : ∀ r, WrLev R (ℓ + 1) r → WrLev R ℓ r := fun r hr => by
      rcases hr with hr | hr
      · exact Or.inl hr
      · right; unfold rL at hr ⊢; omega
    rw [hleaves]
    have best₁' : BestOK P C R c₁ S (o.eval M Q) (dirOf (c.nreg (R + 6))) := by rw [← r6]; exact best₁
    have hroom1 : c₁.nreg ALLOC + levCost Fg f ≤ W := by rw [hA1]; omega
    cases hcase : ps with
    | nil =>
      rw [hcase] at hcnt'
      have g : ¬ c₁.nreg (R + 30) < c₁.nreg (rL R ℓ + 8) := by rw [z₁, hcnt']; simp
      refine ⟨c₁, _, .seq e₁ (.ifLtN_false g (.skip w₁)), by omega, ?_, F01.mono le_rfl
        (fun _ h => h) (by omega)⟩
      simp only [List.flatMap_nil, pcSet_nil, Set.union_empty]
      exact best₁'
    | cons p₀ t =>
      have hp0m : p₀ ∈ ps := by rw [hcase]; exact List.mem_cons_self
      have g0 : c₁.nreg (R + 30) < c₁.nreg (rL R ℓ + 8) := by
        rw [z₁, hcnt', hcase]; simp
      obtain ⟨c₂, k₂, e₂, hk₂, b₂, fr₂⟩ := call c₁ S p₀ hp0m w₁ ctx₁ ho₁ regs1
        (hp0' p₀ (by rw [hcase]; rfl)) best₁' hroom1
      have kp2 : ∀ i, i < 300 → ¬ WrLev R (ℓ + 1) (R + i) → c₂.nreg (R + i) = c₁.nreg (R + i) :=
        fun i hi hw' => frameR_keep hR fr₂ hi hw'
      have o₂ : c₂.nreg (R + 31) = 1 := by
        rw [kp2 31 (by omega) (by unfold WrLev rL; omega), o₁]
      have cn₂ : c₂.nreg (rL R ℓ + 8) = c₁.nreg (rL R ℓ + 8) := by
        have := kp2 (40 + 10 * ℓ + 8) (by omega) (by unfold WrLev rL; omega)
        rw [show R + (40 + 10 * ℓ + 8) = rL R ℓ + 8 by unfold rL; omega] at this; exact this
      have w₂ := e₂.wb_right
      cases ht : t with
      | nil =>
        rw [hcase, ht] at hcnt'
        have g1 : ¬ c₂.nreg (R + 31) < c₂.nreg (rL R ℓ + 8) := by rw [o₂, cn₂, hcnt']; simp
        refine ⟨c₂, _, .seq e₁ (.ifLtN_true g0 (.seq e₂ (.ifLtN_false g1 (.skip w₂)))),
          by omega, ?_, (F01.trans (fr₂.mono le_rfl wr1 le_rfl)).mono le_rfl (fun _ h => h)
            (by omega)⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
        exact b₂
      | cons p₁ t' =>
        have ht' : t' = [] := by
          have := hlen'; rw [hcase, ht] at this; simp only [List.length_cons] at this
          exact List.length_eq_zero_iff.1 (by omega)
        subst ht'
        rw [hcase, ht] at hcnt'
        have hp1m : p₁ ∈ ps := by rw [hcase, ht]; simp
        have g1 : c₂.nreg (R + 31) < c₂.nreg (rL R ℓ + 8) := by rw [o₂, cn₂, hcnt']; simp
        -- the second piece into the registers of level `ℓ + 1`
        obtain ⟨c₃, e₃, v₃, f₃⟩ := copies_run (P := P) (copy2List R ℓ) c₂ w₂ (by
          simp only [copy2List, List.mem_cons, List.not_mem_nil, or_false]
          rintro p (rfl | rfl | rfl | rfl) q (rfl | rfl | rfl | rfl) <;> simp)
          (by simp [copy2List])
        simp only [copy2List, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at v₃
        obtain ⟨v0, v1, v2, v3⟩ := v₃
        have k3 : ∀ r, ¬ (rL R ℓ + 10 ≤ r ∧ r < rL R ℓ + 14) → c₃.nreg r = c₂.nreg r :=
          fun r hr => f₃.1 r (by simp [copy2List]; omega)
        have F23 : FrameR oracleBands (WrLev R ℓ) c₂ c₃ 4 := FrameR.of_frameB f₃ (fun r hr => by
          simp [copy2List] at hr; left; right; unfold rL at hr ⊢; omega)
          (by simp [copy2List, ALLOC]; unfold rL; omega) _
        have F13 : FrameR oracleBands (WrLev R ℓ) c₁ c₃ (k₂ + 4) :=
          (fr₂.mono le_rfl wr1 le_rfl).trans F23
        have regs3 : ∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) ∨ i = 6 ∨ i = 7 →
            c₃.nreg (R + i) = c.nreg (R + i) := fun i hi => by
          rw [k3 _ (by unfold rL; omega), kp2 i (by omega) (by unfold WrLev rL; omega),
            regs1 i hi]
        have ctx₃ : ShotCtx P W X Ok R c₃ H C := ShotCtx.frame hXl ctx₁ F13 (fun i hi => by
          rw [k3 _ (by unfold rL; omega), kp2 i (by omega) (by unfold WrLev rL; omega)])
        have kk : ∀ i, i < 10 → c₃.nreg (R + i) = c₁.nreg (R + i) := fun i hi => by
          rw [k3 _ (by unfold rL; omega)]; exact kp2 i (by omega) (by unfold WrLev rL; omega)
        have ho₃ : OriginIn c₃ (R + 3) o := by
          refine originIn_copy ho₁ (kk 3 (by omega)) ?_ ?_
          · rw [show R + 3 + 1 = R + 4 by omega]; exact kk 4 (by omega)
          · rw [show R + 3 + 2 = R + 5 by omega]; exact kk 5 (by omega)
        have hpc₃ : pieceR c₃ (rL R (ℓ + 1)) = p₁ := by
          rw [← hp1' p₁ (by rw [hcase, ht]; rfl), rL_succ]
          simp only [pieceR, posR, Prod.mk.injEq, WPos.mk.injEq]
          have s4 := kp2 (44 + 10 * ℓ) (by omega) (by unfold WrLev rL; omega)
          have s5 := kp2 (45 + 10 * ℓ) (by omega) (by unfold WrLev rL; omega)
          have s6 := kp2 (46 + 10 * ℓ) (by omega) (by unfold WrLev rL; omega)
          have s7 := kp2 (47 + 10 * ℓ) (by omega) (by unfold WrLev rL; omega)
          have a4 : R + (44 + 10 * ℓ) = rL R ℓ + 4 := by unfold rL; omega
          have a5 : R + (45 + 10 * ℓ) = rL R ℓ + 4 + 1 := by unfold rL; omega
          have a6 : R + (46 + 10 * ℓ) = rL R ℓ + 4 + 2 := by unfold rL; omega
          have a7 : R + (47 + 10 * ℓ) = rL R ℓ + 4 + 3 := by unfold rL; omega
          rw [a4] at s4; rw [a5] at s5; rw [a6] at s6; rw [a7] at s7
          have b0 : rL R ℓ + 10 + 1 = rL R ℓ + 11 := by omega
          have b1 : rL R ℓ + 10 + 2 = rL R ℓ + 12 := by omega
          have b2 : rL R ℓ + 10 + 3 = rL R ℓ + 13 := by omega
          have c1 : rL R ℓ + 4 + 1 = rL R ℓ + 5 := by omega
          have c2 : rL R ℓ + 4 + 2 = rL R ℓ + 6 := by omega
          have c3 : rL R ℓ + 4 + 3 = rL R ℓ + 7 := by omega
          rw [b0, b1, b2, c1, c2, c3]
          rw [c1] at s5; rw [c2] at s6; rw [c3] at s7
          exact ⟨⟨by rw [v0, s4], by rw [v1, s5]⟩, by rw [v2, s6], by rw [v3, s7]⟩
        have best₃ : BestOK P C R c₃ (S ∪ pcSet M Q (levLeaves M Q c R f (ℓ + 1) p₀))
            (o.eval M Q) (dirOf (c.nreg (R + 6))) := b₂.congr
          (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega))
          (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega))
          (k3 _ (by unfold rL; omega))
        have hA3 : c₃.nreg ALLOC ≤ c.nreg ALLOC + (k₂ + 4) := by
          have := F13.2.2.2.2.2.2; rw [hA1] at this; exact this
        obtain ⟨c₄, k₄, e₄, hk₄, b₄, fr₄⟩ := call c₃ _ p₁ hp1m e₃.wb_right ctx₃ ho₃ regs3 hpc₃
          best₃ (by omega)
        refine ⟨c₄, _, .seq e₁ (.ifLtN_true g0 (.seq e₂ (.ifLtN_true g1 (.seq e₃ e₄)))),
          by simp only [copy2List, List.length_cons, List.length_nil]; omega, ?_,
          ((F01.trans F13).trans (fr₄.mono le_rfl wr1 le_rfl)).mono le_rfl (fun _ h => h)
            (by simp only [copy2List, List.length_cons, List.length_nil]; omega)⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, pcSet_append]
        rw [← Set.union_assoc]
        exact b₄

end

end ShotList

end Chazelle.Core
