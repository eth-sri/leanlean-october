module

public import Chazelle.Core.ShotListGCut

/-!
# The model-generic shot list, part 3: one shot and the running minimum

The leaf of the cutting recursion shoots at the piece of level `3` (`R + 70 … R + 73`) with the
ray shooter `sh`, as in the sweep's `ShotList.leaf`; a hit is compared with the running minimum
(`BestG`: flag `R + 20`, position `R + 21`, `R + 22`) by the abscissa comparison `xc` (`XG`),
twice, in the direction of the ray (`R + 35`).

* `leafHitG_exec`: a hit extends the running minimum;
* `leafG_exec`: one shot extends the running minimum by the piece.
-/

namespace Chazelle.Core

namespace ShotListG

open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

@[expose] public section

/-! ## The programs -/

/-- The candidate's position into `R + 244`, `R + 245`. -/
def candList (R : ℕ) : List (ℕ × ℕ) := [(R + 244, 140011), (R + 245, 140012)]

/-- Accept the candidate. -/
def leafAccG (R : ℕ) : Stmt :=
  .seq (.instr (.constN (R + 20) 1)) (block (copies [(R + 21, R + 244), (R + 22, R + 245)]))

/-- The bits `cand < best` (`R + 246`) and `best < cand` (`R + 247`) of the abscissae. -/
def leafCmpG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (R : ℕ) : Stmt :=
  .seq (xc (R + 244) (R + 245) (R + 21) (R + 22)) (.seq (.instr (.copyN (R + 246) 50210))
    (.seq (xc (R + 21) (R + 22) (R + 244) (R + 245)) (.instr (.copyN (R + 247) 50210))))

/-- Accept if the candidate comes first along the ray. -/
def leafDecG (R : ℕ) : Stmt :=
  .ifLtN (R + 30) (R + 35) (.ifLtN (R + 30) (R + 246) (leafAccG R) .skip)
    (.ifLtN (R + 30) (R + 247) (leafAccG R) .skip)

/-- A hit: accept it if there is no minimum yet, else compare. -/
def leafHitG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (R : ℕ) : Stmt :=
  .seq (block (copies (candList R)))
    (.ifLtN (R + 20) (R + 31) (leafAccG R) (.seq (leafCmpG xc R) (leafDecG R)))

/-- **The leaf**: one shot at the piece of level `3`, and the running minimum. -/
def leafG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : Stmt :=
  .seq (leafSet R) (.seq sh (.ifLtN (R + 31) 140010 .skip (.ifLtN 140010 (R + 31) .skip
    (leafHitG xc R))))

/-! ## Execution of the blocks -/

/-- **Accepting the candidate.** -/
theorem leafAccG_exec {P : Polygon} {W : ℕ} {R : ℕ} (c : Config) (hw : WordsBounded W c)
    (hW : 1 ≤ W) :
    ∃ c' k, Exec P W (leafAccG R) c c' k ∧ k = 3 ∧ c'.nreg (R + 20) = 1 ∧
      c'.nreg (R + 21) = c.nreg (R + 244) ∧ c'.nreg (R + 22) = c.nreg (R + 245) ∧
      FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 23)) c c' := by
  have e₁ := Exec.constN (P := P) hw (R + 20) 1 hW
  set c₁ : Config := { c with nreg := upd c.nreg (R + 20) 1 } with hc₁
  have r₁ : ∀ r, r ≠ R + 20 → c₁.nreg r = c.nreg r := fun r hr => by rw [hc₁]; simp [upd, hr]
  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) [(R + 21, R + 244), (R + 22, R + 245)] c₁
    e₁.wb_right (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) q (rfl | rfl) <;> simp)
    (by simp)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at v₂
  obtain ⟨a1, a2⟩ := v₂
  refine ⟨c₂, _, .seq e₁ e₂, rfl, ?_, by rw [a1, r₁ _ (by omega)], by rw [a2, r₁ _ (by omega)],
    ?_⟩
  · rw [f₂.1 _ (by simp), hc₁]; simp
  · have fa : FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 23)) c c₁ :=
      frameB_mono (exec_frameB e₁ (show wr (Bone (R + 20)) (.instr (.constN (R + 20) 1)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by simp only [Bone, beq_iff_eq] at hr; simp [hr])
    have fb : FrameB (fun r => decide (R + 20 ≤ r ∧ r < R + 23)) c₁ c₂ :=
      frameB_mono f₂ (fun r hr => by simp at hr; simp only [decide_eq_true_eq]; omega)
    exact fa.trans fb

/-- The write set of `leafCmpG`. -/
def BcmpG (R : ℕ) (Bx : ℕ → Bool) (r : ℕ) : Bool := decide (R + 246 ≤ r ∧ r < R + 248) || Bx r

/-- **Comparing the abscissae** of the candidate (`R + 244`, `R + 245`) and of the minimum
(`R + 21`, `R + 22`). -/
theorem leafCmpG_exec {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    (hpc : ProperPos M (Qof P) P.n ⟨c.nreg (R + 244), c.nreg (R + 245)⟩)
    (hec : c.nreg (R + 244) < M.W.n)
    (hpb : ProperPos M (Qof P) P.n ⟨c.nreg (R + 21), c.nreg (R + 22)⟩)
    (heb : c.nreg (R + 21) < M.W.n)
    (hy : (M.pos (Qof P) ⟨c.nreg (R + 244), c.nreg (R + 245)⟩).2 =
      (M.pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩).2)
    (hY : Y (M.pos (Qof P) ⟨c.nreg (R + 244), c.nreg (R + 245)⟩).2)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W (leafCmpG xc R) c c' k ∧ k ≤ 2 * K + 2 ∧
      BitIs c' (R + 246) ((M.pos (Qof P) ⟨c.nreg (R + 244), c.nreg (R + 245)⟩).1 <
        (M.pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩).1) ∧
      BitIs c' (R + 247) ((M.pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩).1 <
        (M.pos (Qof P) ⟨c.nreg (R + 244), c.nreg (R + 245)⟩).1) ∧
      FrameB (BcmpG R Bx) c c' := by
  have h := hR; unfold RegsOK at h
  have iB : ∀ i, i < 300 → InB R (R + i) := fun i hi => ⟨by omega, by omega⟩
  -- first comparison
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := hx (R + 244) (R + 245) (R + 21) (R + 22) (iB _ (by omega))
    (iB _ (by omega)) (iB _ (by omega)) (iB _ (by omega)) c hw hctx hpc hec hpb heb hy hY hroom
  have e₂ := Exec.copyN (P := P) e₁.wb_right (R + 246) 50210
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg (R + 246) (c₁.nreg 50210) } with hc₂
  have w₂ := e₂.wb_right
  have kR1 : ∀ r, R ≤ r → r < R + 300 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (opW_R hBx hR h1 h2)
  have keep2 : ∀ r, R ≤ r → r < R + 300 → r ≠ R + 246 → c₂.nreg r = c.nreg r :=
    fun r h1 h2 h3 => by
      rw [hc₂]; simp only [upd, h3, ↓reduceIte]; exact kR1 r h1 h2
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := by
    rw [hc₂]; simp only [upd, show ALLOC ≠ R + 246 by unfold ALLOC; omega, ↓reduceIte]
    exact f₁.1 _ (opW_alloc hBx)
  have F12 : FrameB (BcmpG R Bx) c c₂ := by
    have g1 : FrameB (BcmpG R Bx) c c₁ := frameB_mono f₁ (fun r hr => by simp [BcmpG, hr])
    have g2 : FrameB (BcmpG R Bx) c₁ c₂ := frameB_mono (exec_frameB e₂
      (show wr (Bone (R + 246)) (.instr (.copyN (R + 246) 50210)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [BcmpG])
    exact g1.trans g2
  have ctx₂ : KCtx P W M R E c₂ := KCtx.of_frameB hR hBo hS hctx w₂ F12 (fun r hr => by
    simp only [BcmpG, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with hr | hr
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inr (hBx r hr)))
  -- second comparison
  have q := fun i (hi : i < 300) (hne : i ≠ 246) => keep2 (R + i) (by omega) (by omega) (by omega)
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, f₃⟩ := hx (R + 21) (R + 22) (R + 244) (R + 245) (iB _ (by omega))
    (iB _ (by omega)) (iB _ (by omega)) (iB _ (by omega)) c₂ w₂ ctx₂
    (by rwa [q 21 (by omega) (by omega), q 22 (by omega) (by omega)])
    (by rwa [q 21 (by omega) (by omega)])
    (by rwa [q 244 (by omega) (by omega), q 245 (by omega) (by omega)])
    (by rwa [q 244 (by omega) (by omega)])
    (by rw [q 21 (by omega) (by omega), q 22 (by omega) (by omega), q 244 (by omega) (by omega),
      q 245 (by omega) (by omega)]; exact hy.symm)
    (by rwa [q 21 (by omega) (by omega), q 22 (by omega) (by omega), ← hy])
    (by rwa [hA2])
  rw [q 21 (by omega) (by omega), q 22 (by omega) (by omega), q 244 (by omega) (by omega),
    q 245 (by omega) (by omega)] at b₃
  have e₄ := Exec.copyN (P := P) e₃.wb_right (R + 247) 50210
  have ex : Exec P W (leafCmpG xc R) c _ _ := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨_, _, ex, by omega, ?_, ?_, ?_⟩
  · -- the first bit survives
    have b2 : BitIs c₂ (R + 246) ((M.pos (Qof P) ⟨c.nreg (R + 244), c.nreg (R + 245)⟩).1 <
        (M.pos (Qof P) ⟨c.nreg (R + 21), c.nreg (R + 22)⟩).1) :=
      ⟨by rw [hc₂]; simp only [upd_same]; exact b₁.1,
        by rw [hc₂]; simp only [upd_same]; exact b₁.2⟩
    refine b2.of_eq ?_
    simp only [upd, show R + 246 ≠ R + 247 by omega, ↓reduceIte]
    exact f₃.1 _ (opW_R hBx hR (by omega) (by omega))
  · exact ⟨by simp only [upd_same]; exact b₃.1, by simp only [upd_same]; exact b₃.2⟩
  · have g3 : FrameB (BcmpG R Bx) c₂ c₃ := frameB_mono f₃ (fun r hr => by simp [BcmpG, hr])
    have g4 : FrameB (BcmpG R Bx) c₃ _ := frameB_mono (exec_frameB e₄
      (show wr (Bone (R + 247)) (.instr (.copyN (R + 247) 50210)) = true by
        simp [wr, wrOK, Bone])) (fun r hr => by
          simp only [Bone, beq_iff_eq] at hr; subst hr; simp [BcmpG])
    exact F12.trans (g3.trans g4)

/-! ## The running minimum after one hit -/

/-- The write set of `leafHitG`. -/
def BhitG (R : ℕ) (Bx : ℕ → Bool) (r : ℕ) : Bool :=
  decide (R + 20 ≤ r ∧ r < R + 23) || decide (R + 244 ≤ r ∧ r < R + 248) || Bx r

theorem wrG_hit {R : ℕ} {Bx : ℕ → Bool} (hBx : OpW Bx) : WrG R (BhitG R Bx) := fun r hr => by
  simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with (hr | hr) | hr
  · exact Or.inl ⟨by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · exact Or.inr (Or.inr (hBx r hr))

/-- **A hit updates the running minimum.** -/
theorem leafHitG_exec {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    {S A : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (he : c.nreg 140011 < M.W.n)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg 140011, c.nreg 140012⟩)
    (hpos : M.pos (Qof P) ⟨c.nreg 140011, c.nreg 140012⟩ = rayPt z σ t)
    (hz : Y z.2) (hσb : BitIs c (R + 35) (c.nreg (R + 6) = 1)) (hσ : σ = dirOf (c.nreg (R + 6)))
    (hbest : BestG P M R c S z σ) (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W (leafHitG xc R) c c' k ∧ k ≤ 2 * K + 20 ∧ BestG P M R c' (S ∪ A) z σ ∧
      FrameB (BhitG R Bx) c c' := by
  have h := hR; unfold RegsOK at h
  obtain ⟨-, -, hHW, -, -, h30, h31, -⟩ := id hctx
  have hkc : (candList R).length = 2 := rfl
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) (candList R) c hw (by
    simp only [candList, List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl) q (rfl | rfl) <;> simp <;> omega)
    (by simp [candList])
  simp only [candList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  obtain ⟨p44, p45⟩ := v₁
  have k1 : ∀ r, r ≠ R + 244 → r ≠ R + 245 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp [candList, h1, h2])
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have best₁ : BestG P M R c₁ S z σ := hbest.congr (k1 _ (by omega) (by omega))
    (k1 _ (by omega) (by omega)) (k1 _ (by omega) (by omega))
  have w₁ := e₁.wb_right
  have fB : ∀ {B : ℕ → Bool} {c₀ c' : Config}, FrameB B c₀ c' → (∀ r, B r = true → BhitG R Bx r) →
      FrameB (BhitG R Bx) c₀ c' := fun h hB => frameB_mono h hB
  have f₁' : FrameB (BhitG R Bx) c c₁ := fB f₁ (fun r hr => by
    simp [candList] at hr; simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq]; left; right
    omega)
  have ctx₁ : KCtx P W M R E c₁ := KCtx.of_frameB hR hBo hS hctx w₁ f₁' (wrG_hit hBx)
  -- the acceptance
  have accept : ∀ (cc : Config), WordsBounded W cc → FrameB (BhitG R Bx) c cc →
      cc.nreg (R + 244) = c.nreg 140011 → cc.nreg (R + 245) = c.nreg 140012 →
      (NoHit S z σ ∨ ∃ tb, FirstHit S z σ tb ∧ t ≤ tb) →
      ∃ c' k, Exec P W (leafAccG R) cc c' k ∧ k = 3 ∧ BestG P M R c' (S ∪ A) z σ ∧
        FrameB (BhitG R Bx) c c' := by
    intro cc hcc fcc h44 h45 hS'
    obtain ⟨c', k, ex, hk, a0, a1, a2, fa⟩ := leafAccG_exec (P := P) (R := R) cc hcc (by
      unfold hostWords at hHW; omega)
    refine ⟨c', k, ex, hk, ⟨by rw [a0], fun _ => ⟨t, ?_, ?_, ?_, ?_⟩, fun h' => absurd a0 h'⟩,
      fcc.trans (fB fa (fun r hr => by
        simp only [decide_eq_true_eq] at hr
        simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq]; left; left; omega))⟩
    · rcases hS' with hS' | ⟨tb, htb, hle⟩
      · exact firstHit_union_right hS' hA
      · exact firstHit_union_le' htb hA hle
    · rwa [a1, a2, h44, h45]
    · rwa [a1, h44]
    · rwa [a1, a2, h44, h45]
  have c31 : c₁.nreg (R + 31) = 1 := by rw [k1 _ (by omega) (by omega), h31]
  by_cases hf : c₁.nreg (R + 20) < c₁.nreg (R + 31)
  · -- no minimum yet
    have hno : NoHit S z σ := best₁.2.2 (by omega)
    obtain ⟨c', k, ex, hk, hb, fr⟩ := accept c₁ w₁ f₁' p44 p45 (Or.inl hno)
    exact ⟨c', _, .seq e₁ (.ifLtN_true hf ex), by omega, hb, fr⟩
  -- compare with the minimum
  have hf1 : c₁.nreg (R + 20) = 1 := by have := best₁.1; omega
  obtain ⟨tb, htb, hpb, heb, hposb⟩ := best₁.2.1 hf1
  have hyc : (M.pos (Qof P) ⟨c₁.nreg (R + 244), c₁.nreg (R + 245)⟩).2 = z.2 := by
    rw [p44, p45, hpos]; simp
  have hyb : (M.pos (Qof P) ⟨c₁.nreg (R + 21), c₁.nreg (R + 22)⟩).2 = z.2 := by
    rw [hposb]; simp
  obtain ⟨c₂, k₂, e₂, hk₂, b46, b47, f₂⟩ := leafCmpG_exec (P := P) hR hBo hS hx hBx c₁ w₁ ctx₁
    (by rwa [p44, p45]) (by rwa [p44]) hpb heb (by rw [hyc, hyb])
    (by rwa [hyc]) (by rwa [hA1])
  rw [p44, p45, hpos, hposb] at b46 b47
  have k2 : ∀ r, R ≤ r → r < R + 246 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    f₂.1 r (by simp only [BcmpG, opW_R hBx hR h1 (by omega), Bool.or_false,
      decide_eq_false_iff_not]; omega)
  have f₂' : FrameB (BhitG R Bx) c c₂ := f₁'.trans (fB f₂ (fun r hr => by
    simp only [BcmpG, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with h | h
    · simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq]; left; right; omega
    · simp [BhitG, h]))
  -- keeping the minimum
  have keep : tb ≤ t → BestG P M R c₂ (S ∪ A) z σ := fun hle => by
    refine ⟨by rw [k2 _ (by omega) (by omega)]; exact best₁.1, fun _ => ⟨tb, ?_, ?_, ?_, ?_⟩,
      fun h' => absurd (by rwa [k2 _ (by omega) (by omega)]) h'⟩
    · exact firstHit_union_le htb hA hle
    · rwa [k2 _ (by omega) (by omega), k2 _ (by omega) (by omega)]
    · rwa [k2 _ (by omega) (by omega)]
    · rwa [k2 _ (by omega) (by omega), k2 _ (by omega) (by omega)]
  have r35 : c₂.nreg (R + 35) = c.nreg (R + 35) := by
    rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega)]
  have r30 : c₂.nreg (R + 30) = 0 := by
    rw [k2 _ (by omega) (by omega), k1 _ (by omega) (by omega), h30]
  have h44 : c₂.nreg (R + 244) = c.nreg 140011 := by rw [k2 _ (by omega) (by omega), p44]
  have h45 : c₂.nreg (R + 245) = c.nreg 140012 := by rw [k2 _ (by omega) (by omega), p45]
  have w₂ := e₂.wb_right
  have hσ1 : σ = 1 ∨ σ = -1 := by rw [hσ]; unfold dirOf; split_ifs <;> simp
  by_cases hs : c₂.nreg (R + 30) < c₂.nreg (R + 35)
  · -- `σ = 1`: accept iff `xc < xb`
    have hv : c.nreg (R + 6) = 1 := hσb.2.1 (by have := hσb.1; rw [← r35]; omega)
    have hσe : σ = 1 := by rw [hσ]; exact dirOf_eq_one hv
    have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1
    rw [ite_yes _ _ hσe] at ord
    by_cases hb : c₂.nreg (R + 30) < c₂.nreg (R + 246)
    · have hlt : t < tb := ord.2 (b46.2.1 (by have := b46.1; omega))
      obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' h44 h45 (Or.inr ⟨tb, htb, hlt.le⟩)
      exact ⟨c', _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_true hb ex)))),
        by omega, hbest', fr⟩
    · have hge : tb ≤ t := by
        by_contra hcon
        exact hb (by rw [r30]; have := b46.2.2 (ord.1 (not_le.1 hcon)); omega)
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_false hb
        (.skip w₂))))), by omega, keep hge, f₂'⟩
  · -- `σ = -1`: accept iff `xb < xc`
    have hv : c.nreg (R + 6) ≠ 1 := fun h' => hs (by rw [r30, r35]; have := hσb.2.2 h'; omega)
    have hσe : σ ≠ 1 := by rw [hσ, dirOf_ne_one hv]; norm_num
    have ord := ray_lt_iff (p := z) (t := t) (t' := tb) hσ1
    rw [ite_no _ _ hσe] at ord
    by_cases hb : c₂.nreg (R + 30) < c₂.nreg (R + 247)
    · have hlt : t < tb := ord.2 (b47.2.1 (by have := b47.1; omega))
      obtain ⟨c', k, ex, hk, hbest', fr⟩ := accept c₂ w₂ f₂' h44 h45 (Or.inr ⟨tb, htb, hlt.le⟩)
      exact ⟨c', _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_true hb ex)))),
        by omega, hbest', fr⟩
    · have hge : tb ≤ t := by
        by_contra hcon
        exact hb (by rw [r30]; have := b47.2.2 (ord.1 (not_le.1 hcon)); omega)
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_false hb
        (.skip w₂))))), by omega, keep hge, f₂'⟩

/-! ## The leaf with the shooter -/

/-- **One shot at the piece of level `3`**: the running minimum extends to the piece. -/
theorem leafG_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ Bo)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    (hRB : bandOf R ∉ Bo) {E : Config → Prop} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : ShotCtxG P W X Ok R M E c)
    (hp1 : ProperPos M (Qof P) P.n (pieceR c (R + 70)).1)
    (hp2 : ProperPos M (Qof P) P.n (pieceR c (R + 70)).2)
    (he1 : (pieceR c (R + 70)).1.edge < M.W.n) (he2 : (pieceR c (R + 70)).2.edge < M.W.n)
    (hi1 : (pieceR c (R + 70)).1.hgt = 0 ∨ M.InnerPt (M.pos (Qof P) (pieceR c (R + 70)).1))
    (hi2 : (pieceR c (R + 70)).2.hgt = 0 ∨ M.InnerPt (M.pos (Qof P) (pieceR c (R + 70)).2))
    (hwt : M.arcWt (M.key (Qof P) (pieceR c (R + 70)).1) (M.key (Qof P) (pieceR c (R + 70)).2) ≤
      c.nreg (R + 7))
    {o : Origin} (ho : OriginIn c (R + 3) o) (hol : o.Lt P.n M)
    (hof : (∃ q, o = .walk ⟨q, 0⟩) ∨ (M.InnerPt (o.eval M (Qof P)) ∧
      ∀ x, o = .walk x → ProperPos M (Qof P) P.n x))
    (hon : o.eval M (Qof P) ∉ M.arcSet (M.key (Qof P) (pieceR c (R + 70)).1)
      (M.key (Qof P) (pieceR c (R + 70)).2))
    (hoy : Y (o.eval M (Qof P)).2) {S : Set Point}
    (hbest : BestG P M R c S (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))))
    (hroom : c.nreg ALLOC + F (c.nreg (R + 7)) + (2 * K + 50) ≤ W) :
    ∃ c' k, Exec P W (leafG xc sh R) c c' k ∧ k ≤ F (c.nreg (R + 7)) + (2 * K + 50) ∧
      BestG P M R c' (S ∪ M.arcSet (M.key (Qof P) (pieceR c (R + 70)).1)
        (M.key (Qof P) (pieceR c (R + 70)).2)) (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) ∧
      FrameR Bo (fun r => (R + 20 ≤ r ∧ r < R + 23) ∨ (R + 244 ≤ r ∧ r < R + 248)) c c' k := by
  have h := hR; unfold RegsOK at h
  set Q := Qof P
  set z := o.eval M Q
  set σ := dirOf (c.nreg (R + 6))
  set A := M.arcSet (M.key Q (pieceR c (R + 70)).1) (M.key Q (pieceR c (R + 70)).2)
  -- the shooter's inputs
  obtain ⟨c₁, k₁, e₁, hk₁, v₁, f₁⟩ := leafSet_exec (P := P) hR c hw
  simp only [setList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s13⟩ := v₁
  have k1 : ∀ r, ¬ (140000 ≤ r ∧ r < 140014) → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r (by simp [setList]; omega)
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by unfold ALLOC; omega)
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
  have hR1 : ∀ i, i < 300 → c₁.nreg (R + i) = c.nreg (R + i) := fun i hi => k1 _ (by omega)
  have hctx0 := hctx
  obtain ⟨⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩, hX, hcap, hOk, hσb, hreg⟩ := hctx0
  have hO1 : OriginIn c₁ (bandReg bShoot 5) o := by
    refine originIn_copy ho ?_ ?_ ?_ <;> simp only [bandReg, bShoot] <;> norm_num
    · exact s5
    · exact s6
    · exact s7
  -- the shot
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, fr₂⟩ := hsh P W c₁ e₁.wb_right
    ⟨hG, hHW, by rw [rd_shoot, s13, hM1, hA1]; exact hX,
      by rw [rd_shoot, rd_shoot, s9, s13, hM1]; exact hcap,
      by rwa [rd_shoot, s0, hM1, hA1], by rw [rd_shoot, s0, hM1]; exact hreg, M,
      by rwa [rd_shoot, s0, hM1], hOk,
      by rwa [rd_shoot, rd_shoot, s1, s2], by rwa [rd_shoot, rd_shoot, s3, s4],
      by rwa [rd_shoot, s1], by rwa [rd_shoot, s3],
      by rwa [rd_shoot, rd_shoot, s1, s2], by rwa [rd_shoot, rd_shoot, s3, s4],
      by rwa [rd_shoot, rd_shoot, rd_shoot, rd_shoot, rd_shoot, s1, s2, s3, s4, s9],
      o, hol, hO1, hof, by rwa [rd_shoot, rd_shoot, rd_shoot, rd_shoot, s1, s2, s3, s4]⟩
    (by rw [hA1]; show _ + F (rd c₁ bShoot 9) ≤ W; rw [rd_shoot, s9]; omega)
  replace hk₂ : k₂ ≤ F (c.nreg (R + 7)) := by
    have h2 : k₂ ≤ F (rd c₁ bShoot 9) := hk₂
    rwa [rd_shoot, s9] at h2
  have post := post₂ M o (by rwa [rd_shoot, s0, hM1]) hO1
  simp only [rd_shoot, Nat.reduceAdd, s1, s2, s3, s4, s8] at post
  obtain ⟨hhit, hnoh⟩ := post
  -- registers of the caller's block survive the shot
  have hR2 : ∀ i, i < 300 → c₂.nreg (R + i) = c.nreg (R + i) := fun i hi => by
    rw [fr₂.1 _ (fun hb => band_RB hR hRB hi (hBs hb)) (by unfold ALLOC; omega), hR1 i hi]
  have F01 : FrameR Bo (fun _ => False) c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
    right; simp [setList] at hr; exact hBo (band_shoot (by omega))) (by simp [setList, ALLOC]) _
  have F12 : FrameR Bo (fun _ => False) c₁ c₂ k₂ :=
    (FrameR.of_frame fr₂).mono hBs (fun _ h => h) le_rfl
  have F02 := F01.trans F12
  have w₂ := e₂.wb_right
  have ctx₂ : ShotCtxG P W X Ok R M E c₂ :=
    ShotCtxG.frame hXl hS hctx w₂ F02 (fun _ h => h.elim) (fun i hi => hR2 i (by omega))
  have best₂ : BestG P M R c₂ S z σ := hbest.congr (hR2 20 (by omega)) (hR2 21 (by omega))
    (hR2 22 (by omega))
  have hA2 : c₂.nreg ALLOC ≤ c.nreg ALLOC + F (c.nreg (R + 7)) := by
    have := F12.2.2.2.2.2.2; rw [hA1] at this; omega
  have Fw : ∀ {cc cc' : Config} {kk : ℕ}, FrameR Bo (fun _ => False) cc cc' kk →
      FrameR Bo (fun r => (R + 20 ≤ r ∧ r < R + 23) ∨ (R + 244 ≤ r ∧ r < R + 248))
        cc cc' kk := fun hf => hf.mono le_rfl (fun _ h => h.elim) le_rfl
  have c31 : c₂.nreg (R + 31) = 1 := by rw [hR2 31 (by omega), h31]
  -- no hit
  have nohit : c₂.nreg 140010 ≠ 1 → BestG P M R c₂ (S ∪ A) z σ := fun hne => by
    have hNA : NoHit A z σ := hnoh hne
    refine ⟨best₂.1, fun hf => ?_, fun hf => noHit_union (best₂.2.2 hf) hNA⟩
    obtain ⟨t, ht, rest⟩ := best₂.2.1 hf
    exact ⟨t, firstHit_union_left ht hNA, rest⟩
  by_cases g1 : c₂.nreg (R + 31) < c₂.nreg 140010
  · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_true g1 (.skip w₂))), by omega,
      nohit (by omega), ?_⟩
    exact (Fw F02).mono le_rfl (fun _ h => h) (by omega)
  by_cases g2 : c₂.nreg 140010 < c₂.nreg (R + 31)
  · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_false g1 (.ifLtN_true g2 (.skip w₂)))), by omega,
      nohit (by omega), ?_⟩
    exact (Fw F02).mono le_rfl (fun _ h => h) (by omega)
  -- a hit
  have hflag : c₂.nreg 140010 = 1 := by omega
  obtain ⟨t, htA, hpp, hpe, hpos⟩ := hhit hflag
  obtain ⟨c₃, k₃, e₃, hk₃, best₃, f₃⟩ := leafHitG_exec (P := P) hR hBo hS hx hBx c₂ w₂ ctx₂.1 htA
    hpe hpp hpos hoy ctx₂.2.2.2.2.1 (by rw [hR2 6 (by omega)]) best₂ (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_false g1 (.ifLtN_false g2 e₃))), by omega, best₃, ?_⟩
  have F23 : FrameR Bo (fun r => (R + 20 ≤ r ∧ r < R + 23) ∨ (R + 244 ≤ r ∧ r < R + 248))
      c₂ c₃ k₃ := FrameR.of_frameB f₃ (fun r hr => by
    simp only [BhitG, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (h' | h') | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
    · exact Or.inr (hBo (hBx r h').1)) ((wrG_hit hBx).alloc hR) _
  exact ((Fw F02).trans F23).mono le_rfl (fun _ h => h) (by omega)

end

end ShotListG

end Chazelle.Core
