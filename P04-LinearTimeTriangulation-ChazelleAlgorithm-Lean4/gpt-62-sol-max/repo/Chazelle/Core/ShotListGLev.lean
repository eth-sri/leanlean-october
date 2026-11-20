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

/-- The cutting tree with the general model's operations. -/
abbrev levFG (kc xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) :=
  levCore (leafG xc sh R) (cutBG kc R) R

/-- The cost of one node of the recursion: a shot and two abscissa comparisons, or a cut. -/
def nodeG (Fg K : ℕ) : ℕ := Fg + 2 * K + 1000

abbrev levCostG := treeCost

set_option maxRecDepth 4096 in
/-- **The cutting recursion**: from level `ℓ` (`f + ℓ = 3`), the running minimum extends to the
pieces `levLeaves` of the arc of level `ℓ`. -/
theorem levG_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo)
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
        FrameR Bo (WrLev R ℓ) c c' k := by
  apply levCore_exec (o := o) (G₀ := fun n => nodeG (F n) K)
    (Ctx := ShotCtxG P W X Ok R M E)
    (Best := fun c S d => BestG P M R c S (o.eval M (Qof P)) (dirOf d))
    hR (fun _ hi => band_RB hR hRB hi)
  · intro c h
    exact ⟨h.1.2.2.2.2.2.1, h.1.2.2.2.2.2.2.1⟩
  · intro c c' k ℓ h hw hf hr
    exact ShotCtxG.frame hXl hS h hw hf (fun r hr => by unfold WrLev rL at hr; omega) hr
  · intro c c' S d hb hr
    exact hb.congr (hr 20 (by omega) (by omega)) (hr 21 (by omega) (by omega))
      (hr 22 (by omega) (by omega))
  · intro c S hw hctx ho hpc ⟨hwt, hon⟩ hbest hroom
    obtain ⟨n1, n2, e1, e2, i1, i2⟩ := hpc
    unfold nodeG at hroom ⊢
    obtain ⟨c', k, ex, hk, hb, fr⟩ := leafG_exec hsh hBs hXl hR hRB hBo hS hx hBx c hw hctx n1.1 n2.1
      e1 e2 i1 i2 hwt ho hol hof hon hoy hbest (by omega)
    refine ⟨c', k, ex, by omega, ?_, fr.mono le_rfl (fun r hr => ?_) le_rfl⟩
    · simpa only [pcSet_single, show rL R 3 = R + 70 by unfold rL; omega] using hb
    · rcases hr with hr | hr
      · exact Or.inl ⟨hr.1, by omega⟩
      · right; unfold rL; unfold RegsOK at hR; omega
  · intro ℓ c hℓ hw hctx hpc hroom
    have hR' := hR
    unfold RegsOK at hR'
    have hLd : rL R ℓ = R + 40 + 10 * ℓ := rfl
    have hHW := hctx.1.2.2.1
    obtain ⟨na, nb, ea, eb, -, -⟩ := hpc
    unfold nodeG at hroom ⊢
    obtain ⟨c₁, k₁, e₁, hk₁, pc₁, f₁⟩ := cutBG_exec (P := P) hR hℓ hBo hS hk hBk c hw (by
      unfold hostWords at hHW; omega) hctx.1 (by omega) na nb ea eb
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
    have hA1 := f₁.1 _ (wc.alloc hR)
    have F01 : FrameR Bo (WrLev R ℓ) c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
      simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hr
      rcases hr with ((hr | hr | hr) | hr) | hr
      · have := bouts_range hr; left; right; unfold rL; omega
      · left; right; unfold rL; omega
      · exact Or.inr (hBo (hBk r hr).1)
      · simp only [Bform, decide_eq_true_eq] at hr; left; right; unfold rL; omega
      · simp only [decide_eq_true_eq] at hr; left; right; exact ⟨hr.1, by rw [hLd] at hr; omega⟩)
      (wc.alloc hR) _
    exact ⟨c₁, k₁, e₁, by omega, pc₁, F01, hA1, k1⟩

end

end ShotListG

end Chazelle.Core
