module

public import Chazelle.Core.ShotListGLeaf

/-!
# The model-generic shot list, part 4: the cutting recursion

`levFG kc xc sh R f ℓ` is the sweep's recursion `ShotList.levF` with the generic cutting block
(`cutBG`) and leaf (`leafG`).  `levG_exec` proves by induction on `f` that the running minimum
extends to the pieces `levLeaves` of the arc of level `ℓ` (the same pieces as the sweep's).
-/

namespace Chazelle.Core

namespace ShotListG

open Machine Machine.Stmt Programs SignK SweepPrim ShotList

@[expose] public section

/-- **The cutting recursion**: `f` levels from level `ℓ`. -/
def levFG (kc xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : ℕ → ℕ → Stmt
  | 0, _ => leafG xc sh R
  | f + 1, ℓ => .seq (cutBG kc R ℓ) (.ifLtN (R + 30) (rL R ℓ + 8)
      (.seq (levFG kc xc sh R f (ℓ + 1)) (.ifLtN (R + 31) (rL R ℓ + 8)
        (.seq (block (copies (copy2List R ℓ))) (levFG kc xc sh R f (ℓ + 1))) .skip)) .skip)

/-- The cost of one node of the recursion: a shot and two abscissa comparisons, or a cut. -/
def nodeG (Fg K : ℕ) : ℕ := Fg + 2 * K + 1000

/-- The cost of `f` levels. -/
def levCostG (G f : ℕ) : ℕ := (2 ^ (f + 1) - 1) * G

theorem levCostG_succ (G f : ℕ) : levCostG G (f + 1) = 2 * levCostG G f + G := by
  unfold levCostG
  have : 1 ≤ 2 ^ (f + 1) := Nat.one_le_two_pow
  rw [pow_succ]
  zify [this, show 1 ≤ 2 ^ (f + 1) * 2 by omega]
  ring

theorem levCostG_zero (G : ℕ) : levCostG G 0 = G := by simp [levCostG]

/-- **The cutting recursion**: from level `ℓ` (`f + ℓ = 3`), the running minimum extends to the
pieces `levLeaves` of the arc of level `ℓ`. -/
theorem levG_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ Bo)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    (hRB : bandOf R ∉ Bo) {E : Config → Prop} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E) {Y : ℝ → Prop} {kc xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bk Bx : ℕ → Bool} {K : ℕ} (hk : KeyG P W M R E kc Bk K) (hBk : OpW Bk)
    (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx)
    {o : Origin} (hol : o.Lt P.n M)
    (hof : (∃ q, o = .walk ⟨q, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
      ∀ x, o = .walk x → ProperPos M (Qof P) P.n x))
    (hoy : Y (o.eval M (Qof P)).2) :
    ∀ (f ℓ : ℕ) (c : Config) (S : Set Point), f + ℓ = 3 → WordsBounded W c →
      ShotCtxG P W X Ok R M E c → OriginIn c (R + 3) o →
      PieceOK M (Qof P) P.n (pieceR c (rL R ℓ)) →
      (∀ j, ℓ ≤ j → j < 3 → c.nreg (R + 30 + j) < c.nreg (R + 9) →
        c.nreg (R + 10 + 2 * j) < M.W.n ∧ c.nreg (R + 11 + 2 * j) < M.W.n) →
      (∀ p ∈ levLeaves M (Qof P) c R f ℓ (pieceR c (rL R ℓ)),
        M.arcWt (M.key (Qof P) p.1) (M.key (Qof P) p.2) ≤ c.nreg (R + 7) ∧
        o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) p.1) (M.key (Qof P) p.2)) →
      BestG P M R c S (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) →
      c.nreg ALLOC + levCostG (nodeG (F (c.nreg (R + 7))) K) f ≤ W →
      ∃ c' k, Exec P W (levFG kc xc sh R f ℓ) c c' k ∧
        k ≤ levCostG (nodeG (F (c.nreg (R + 7))) K) f ∧
        BestG P M R c' (S ∪ pcSet M (Qof P) (levLeaves M (Qof P) c R f ℓ (pieceR c (rL R ℓ))))
          (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) ∧
        FrameR Bo (WrLev R ℓ) c c' k
  | 0, ℓ, c, S, hf, hw, hctx, ho, hpc, _, hleaf, hbest, hroom => by
    have hℓ : ℓ = 3 := by omega
    subst hℓ
    have hL3 : rL R 3 = R + 70 := by unfold rL; omega
    rw [hL3] at hpc hleaf ⊢
    obtain ⟨n1, n2, e1, e2, i1, i2⟩ := hpc
    obtain ⟨hwt, hon⟩ := hleaf (pieceR c (R + 70)) (by simp [levLeaves])
    rw [levCostG_zero] at hroom ⊢
    unfold nodeG at hroom ⊢
    obtain ⟨c', k, ex, hk, hb, fr⟩ := leafG_exec hsh hBs hXl hR hRB hBo hS hx hBx c hw hctx n1.1 n2.1
      e1 e2 i1 i2 hwt ho hol hof hon hoy hbest (by omega)
    refine ⟨c', k, ex, by omega, ?_, fr.mono le_rfl (fun r hr => ?_) le_rfl⟩
    · simp only [levLeaves, pcSet_single]; exact hb
    · rcases hr with hr | hr
      · exact Or.inl ⟨hr.1, by omega⟩
      · right; unfold rL; unfold RegsOK at hR; omega
  | f + 1, ℓ, c, S, hf, hw, hctx, ho, hpc, hholes, hleaf, hbest, hroom => by
    have hℓ : ℓ ≤ 2 := by omega
    have hR' := hR; unfold RegsOK at hR'
    set Q := Qof P
    have hlc := levCostG_succ (nodeG (F (c.nreg (R + 7))) K) f
    have hKG : K + 900 ≤ nodeG (F (c.nreg (R + 7))) K := by unfold nodeG; omega
    set G := nodeG (F (c.nreg (R + 7))) K with hG
    set q := pieceR c (rL R ℓ) with hq
    have hLd : rL R ℓ = R + 40 + 10 * ℓ := rfl
    have hkctx := hctx.1
    have hHW := hkctx.2.2.1
    obtain ⟨na, nb, ea, eb, ia, ib⟩ := hpc
    -- the cut
    obtain ⟨c₁, k₁, e₁, hk₁, pc₁, f₁⟩ := cutBG_exec (P := P) hR hℓ hBo hS hk hBk c hw (by
      unfold hostWords at hHW; omega) hkctx (by omega) na nb ea eb
    set ps := levPieces M Q (c.nreg (R + 30 + ℓ) < c.nreg (R + 9)) q.1 q.2
      (c.nreg (R + 10 + 2 * ℓ)) (c.nreg (R + 11 + 2 * ℓ)) with hps
    have k1 : ∀ r, R ≤ r → r < rL R ℓ + 4 → c₁.nreg r = c.nreg r := fun r h1 h2 => f₁.1 r (by
      have hbk := opW_R hBk hR h1 (by unfold rL at h2; omega)
      unfold rL at h2
      cases hb : BcutG R ℓ Bk r
      · rfl
      · exfalso
        simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hb
        rcases hb with ((h' | h' | h') | h') | h'
        · have := bouts_range h'; omega
        · omega
        · rw [hbk] at h'; exact absurd h' (by simp)
        · simp only [Bform, decide_eq_true_eq] at h'; omega
        · simp only [decide_eq_true_eq] at h'; unfold rL at h'; omega)
    have wc := wrG_cut (R := R) hℓ hBk
    have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := f₁.1 _ (wc.alloc hR)
    have F01 : FrameR Bo (WrLev R ℓ) c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
      simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hr
      rcases hr with ((hr | hr | hr) | hr) | hr
      · have := bouts_range hr; left; right; unfold rL; omega
      · left; right; unfold rL; omega
      · exact Or.inr (hBo (hBk r hr).1)
      · simp only [Bform, decide_eq_true_eq] at hr; left; right; unfold rL; omega
      · simp only [decide_eq_true_eq] at hr; left; right; exact ⟨hr.1, by rw [hLd] at hr; omega⟩)
      (wc.alloc hR) _
    have toS : ∀ r, WrLev R ℓ r → R + 9 ≤ r ∧ r < R + 300 := fun r hr => by
      unfold WrLev rL at hr; omega
    have ctx₁ : ShotCtxG P W X Ok R M E c₁ := ShotCtxG.frame hXl hS hctx e₁.wb_right F01 toS
      (fun i hi => k1 _ (by omega) (by unfold rL; omega))
    have ho₁ : OriginIn c₁ (R + 3) o := originIn_copy ho (k1 _ (by omega) (by unfold rL; omega))
      (k1 _ (by omega) (by unfold rL; omega)) (k1 _ (by omega) (by unfold rL; omega))
    have r6 : c₁.nreg (R + 6) = c.nreg (R + 6) := k1 _ (by omega) (by unfold rL; omega)
    have r7 : c₁.nreg (R + 7) = c.nreg (R + 7) := k1 _ (by omega) (by unfold rL; omega)
    have best₁' : BestG P M R c₁ S (o.eval M Q) (dirOf (c.nreg (R + 6))) :=
      hbest.congr (k1 _ (by omega) (by unfold rL; omega))
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
    have z₁ : c₁.nreg (R + 30) = 0 := ctx₁.1.2.2.2.2.2.1
    have o₁ : c₁.nreg (R + 31) = 1 := ctx₁.1.2.2.2.2.2.2.1
    -- the recursive call on a piece in the registers of level `ℓ + 1`
    have call : ∀ (cc : Config) (S' : Set Point) (p : WPos × WPos), p ∈ ps → WordsBounded W cc →
        ShotCtxG P W X Ok R M E cc → OriginIn cc (R + 3) o →
        (∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) ∨ i = 6 ∨ i = 7 →
          cc.nreg (R + i) = c.nreg (R + i)) →
        pieceR cc (rL R (ℓ + 1)) = p →
        BestG P M R cc S' (o.eval M Q) (dirOf (c.nreg (R + 6))) →
        cc.nreg ALLOC + levCostG G f ≤ W →
        ∃ c' k, Exec P W (levFG kc xc sh R f (ℓ + 1)) cc c' k ∧ k ≤ levCostG G f ∧
          BestG P M R c' (S' ∪ pcSet M Q (levLeaves M Q c R f (ℓ + 1) p)) (o.eval M Q)
            (dirOf (c.nreg (R + 6))) ∧ FrameR Bo (WrLev R (ℓ + 1)) cc c' k := by
      intro cc S' p hp hwc hcc hoc hreg' hpc' hbc hrc
      have e6 := hreg' 6 (Or.inr (Or.inr (Or.inl rfl)))
      have e7 := hreg' 7 (Or.inr (Or.inr (Or.inr rfl)))
      have hl := hlv cc (fun i hi => hreg' i (by omega))
      obtain ⟨c', k, ex, hk', hb, fr⟩ := levG_exec hsh hBs hXl hR hRB hBo hS hk hBk hx hBx hol hof hoy
        f (ℓ + 1) cc S' (by omega) hwc hcc hoc (by rw [hpc']; exact hgood p hp)
        (fun j hj1 hj2 hj3 => by
          have e30 := hreg' (30 + j) (Or.inr (Or.inl (by omega)))
          have e9 := hreg' 9 (Or.inl (by omega))
          have ex1 := hreg' (10 + 2 * j) (Or.inl (by omega))
          have ex2 := hreg' (11 + 2 * j) (Or.inl (by omega))
          have a1 : R + 30 + j = R + (30 + j) := by omega
          have a2 : R + 10 + 2 * j = R + (10 + 2 * j) := by omega
          have a3 : R + 11 + 2 * j = R + (11 + 2 * j) := by omega
          rw [a1, e30, e9] at hj3
          have hh := hholes j (by omega) hj2 (by rwa [a1])
          rw [a2, a3] at hh ⊢
          rwa [ex1, ex2])
        (fun p' hp' => by
          rw [hpc', hl] at hp'
          have := hleaf p' (by rw [hleaves]; exact List.mem_flatMap.2 ⟨p, hp, hp'⟩)
          rw [e7]; exact this)
        (by rwa [e6]) (by rwa [e7])
      rw [e7] at hk'
      rw [hpc', hl, e6] at hb
      exact ⟨c', k, ex, hk', hb, fr⟩
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
    have hroom1 : c₁.nreg ALLOC + levCostG G f ≤ W := by rw [hA1]; omega
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
        fun i hi hw' => fr₂.1 _ (band_RB hR hRB hi) (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw'
      have o₂ : c₂.nreg (R + 31) = 1 := by
        rw [kp2 31 (by omega) (by unfold WrLev rL; omega), o₁]
      have cn₂ : c₂.nreg (rL R ℓ + 8) = c₁.nreg (rL R ℓ + 8) := by
        have := kp2 (40 + 10 * ℓ + 8) (by omega) (by unfold WrLev rL; omega)
        rwa [show R + (40 + 10 * ℓ + 8) = rL R ℓ + 8 by unfold rL; omega] at this
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
        have F23 : FrameR Bo (WrLev R ℓ) c₂ c₃ 4 := FrameR.of_frameB f₃ (fun r hr => by
          simp [copy2List] at hr; left; right; unfold rL at hr ⊢; omega)
          (by simp [copy2List, ALLOC]; unfold rL; omega) _
        have F13 : FrameR Bo (WrLev R ℓ) c₁ c₃ (k₂ + 4) :=
          (fr₂.mono le_rfl wr1 le_rfl).trans F23
        have regs3 : ∀ i, (9 ≤ i ∧ i ≤ 15) ∨ (30 ≤ i ∧ i ≤ 33) ∨ i = 6 ∨ i = 7 →
            c₃.nreg (R + i) = c.nreg (R + i) := fun i hi => by
          rw [k3 _ (by unfold rL; omega), kp2 i (by omega) (by unfold WrLev rL; omega),
            regs1 i hi]
        have ctx₃ : ShotCtxG P W X Ok R M E c₃ := ShotCtxG.frame hXl hS ctx₁ e₃.wb_right F13 toS
          (fun i hi => by
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
        have best₃ : BestG P M R c₃ (S ∪ pcSet M Q (levLeaves M Q c R f (ℓ + 1) p₀))
            (o.eval M Q) (dirOf (c.nreg (R + 6))) := b₂.congr
          (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega)) (k3 _ (by unfold rL; omega))
        have hA3 : c₃.nreg ALLOC ≤ c.nreg ALLOC + (k₂ + 4) := by
          have := F13.2.2.2.2.2.2; rwa [hA1] at this
        obtain ⟨c₄, k₄, e₄, hk₄, b₄, fr₄⟩ := call c₃ _ p₁ hp1m e₃.wb_right ctx₃ ho₃ regs3 hpc₃
          best₃ (by omega)
        refine ⟨c₄, _, .seq e₁ (.ifLtN_true g0 (.seq e₂ (.ifLtN_true g1 (.seq e₃ e₄)))),
          by simp only [copy2List, List.length_cons, List.length_nil]; omega, ?_,
          ((F01.trans F13).trans (fr₄.mono le_rfl wr1 le_rfl)).mono le_rfl (fun _ h => h)
            (by simp only [copy2List, List.length_cons, List.length_nil]; omega)⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, pcSet_append]
        rwa [← Set.union_assoc]

end

end ShotListG

end Chazelle.Core
