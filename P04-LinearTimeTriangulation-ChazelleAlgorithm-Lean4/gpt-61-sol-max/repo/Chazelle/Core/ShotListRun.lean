module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ShotListLeaf

/-!
# Shooting at a list of arcs with holes, part 6: the shooting context and the leaf

`ShotCtx`: the facts every shot of the wrapper needs (the context `X` in memory with room for the
weight bound, the model descriptor of the chain model at `R`, the chain descriptor at `R + 34`,
the constants).  It survives the frames of the wrapper's steps (`ShotCtx.frame`, using
`X.CapLocal`).  `leaf_exec`: one shot at the piece of level `3` with the shooter `sh`.
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## Descriptors survive memory changes above the allocator -/

/-- A well-formed model descriptor of a chain model below `E` survives a change of the memory at
or above `E` (and a larger bound). -/
theorem modelDesc_keep {P : Polygon} {m m' : ℕ → ℕ} {D E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ModelDescWF P E m D) (h0 : m D = 0) (hC : ChainDescAt m (D + 1) (Qof P) H C)
    (he : ∀ a, a < E → m' a = m a) (hE : E ≤ E') :
    ModelDescWF P E' m' D ∧ m' D = 0 ∧ ChainDescAt m' (D + 1) (Qof P) H C := by
  obtain ⟨hD6, hch⟩ := hwf
  have hcw := hch h0
  obtain ⟨-, -, hEb, -⟩ := hcw.2 H C hC
  have hc : ∀ j, j < 5 → m' (D + 1 + j) = m (D + 1 + j) := fun j hj => he _ (by omega)
  have hC' := chainDescAt_copy hC hEb he hc
  have h0' : m' D = 0 := by grind
  refine ⟨⟨by omega, fun _ => chainWF_copy hcw hC he hc (by omega) hE⟩, h0', hC'⟩

/-! ## The shooting context -/

/-- **The shooting context** at `R`: the facts the shots need, for the chain `C` on the host `H`. -/
def ShotCtx (P : Polygon) (W : ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ)
    (c : Config) (H : Host) (C : Chain) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem (c.nreg (R + 8)) (c.nreg ALLOC) ∧
    c.nreg (R + 7) ≤ X.cap P c.nmem (c.nreg (R + 8)) ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg R) ∧ c.nmem (c.nreg R) = 0 ∧
    ChainDescAt c.nmem (c.nreg R + 1) (Qof P) H C ∧ c.nreg (R + 34) = c.nreg R + 1 ∧
    (∀ H', HostAt c.nmem (c.nmem (c.nreg R + 1)) H' → HostRegular P.n H') ∧
    Ok P (chainModel C) ∧ 2 * C.m + 7 ≤ W ∧ c.nreg (R + 30) = 0 ∧ c.nreg (R + 31) = 1 ∧
    BitIs c (R + 35) (c.nreg (R + 6) = 1)

section
variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {R : ℕ} {c : Config} {H : Host} {C : Chain} (h : ShotCtx P W X Ok R c H C)
include W X Ok H C h
theorem ShotCtx.modelDesc :
    ModelDescAt c.nmem (c.nreg R) (Qof P) (chainModel C) :=
  Or.inl ⟨h.2.2.2.2.2.1, H, C, h.2.2.2.2.2.2.1, rfl⟩

theorem ShotCtx.chainWF :
    ChainWF P (c.nreg ALLOC) c.nmem (c.nreg (R + 34)) := by
  rw [h.2.2.2.2.2.2.2.1]; exact h.2.2.2.2.1.2 h.2.2.2.2.2.1


end

/-- **The shooting context survives** a frame of the oracle bands that keeps the registers
`R … R + 8` and `R + 30 … R + 35`. -/
theorem ShotCtx.frame {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hXl : X.CapLocal) {R : ℕ} {c c' : Config} {H : Host} {C : Chain} {Wr : ℕ → Prop} {k : ℕ}
    (h : ShotCtx P W X Ok R c H C) (hf : FrameR oracleBands Wr c c' k)
    (hr : ∀ i, (i ≤ 8 ∨ (30 ≤ i ∧ i ≤ 35)) → c'.nreg (R + i) = c.nreg (R + i)) :
    ShotCtx P W X Ok R c' H C := by
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσ⟩ := h
  obtain ⟨-, -, hmem, -, -, hA, -⟩ := hf
  have he : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a := hmem
  have r0 : c'.nreg R = c.nreg R := by simpa using hr 0 (Or.inl (by omega))
  obtain ⟨mw', h0', hC'⟩ := modelDesc_keep hmwf h0 hC he hA
  obtain ⟨-, -, hEb, -⟩ := (hmwf.2 h0).2 H C hC
  refine ⟨hG, hHW, ?_, ?_, by ram_simp, by omega_nf, by ram_simp,
    by ram_simp, ?_, hOk, hm, by ram_simp,
    by ram_simp, ⟨by rw [hr 35 (Or.inr (by omega))]; exact hσ.1,
      by rw [hr 35 (Or.inr (by omega)), hr 6 (Or.inl (by omega))]; exact hσ.2⟩⟩
  · rw [hr 8 (Or.inl (by omega))]
    exact X.mono P _ _ _ _ hA (X.local_ P _ _ _ _ (fun a ha => (he a ha).symm) hX)
  · rw [hr 8 (Or.inl (by omega)), hr 7 (Or.inl (by omega)), hXl P c.nmem c'.nmem _ _ he hX]; exact hcap
  · intro H' hH'
    rw [r0] at hH'
    have hb : c'.nmem (c.nreg R + 1) = c.nmem (c.nreg R + 1) := he _ (by
      have := hmwf.1; omega)
    rw [hb] at hH'
    have hH : HostAt c'.nmem (c.nmem (c.nreg R + 1)) H := hostAt_agree hC.1 hEb he
    rw [NFLoc.hostAt_unique hH' hH]
    exact hreg H hC.1


/-! ## Bands -/

theorem rd_shoot (c : Config) (i : ℕ) : rd c bShoot i = c.nreg (140000 + i) := by
  aesop

/-- The caller's registers are outside the oracle bands. -/
theorem band_R {R : ℕ} (hR : RegsOK R) {i : ℕ} (hi : i < 300) : bandOf (R + i) ∉ oracleBands := by
  unfold RegsOK at hR
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, bandOf]
  omega

section
variable {r : ℕ}
theorem band_prim (h : Bprim r = true) : bandOf r ∈ oracleBands := by
  have := (Bprim_band r h).1
  grind [primBands, oracleBands, kernelBands, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

theorem band_locate (h : 50000 ≤ r ∧ r < 60000) : bandOf r ∈ oracleBands := by
  grind [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot, bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, bandOf]

theorem band_shoot (h : 140000 ≤ r ∧ r < 150000) : bandOf r ∈ oracleBands := by
  core_grind [kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot, bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

/-! ## The leaf with the shooter -/


end

/-- The registers of the caller's block written by a leaf. -/
def WrLeaf (R r : ℕ) : Prop := (R + 20 ≤ r ∧ r < R + 28) ∨ (R + 240 ≤ r ∧ r < R + 250)

/-- **One shot at the piece of level `3`**: the running minimum extends to the piece. -/
theorem leaf_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {P : Polygon} {W R : ℕ} (hR : RegsOK R) (c : Config)
    (hw : WordsBounded W c) {H : Host} {C : Chain} (hctx : ShotCtx P W X Ok R c H C)
    (hp1 : ProperPos (chainModel C) (Qof P) P.n (pieceR c (R + 70)).1)
    (hp2 : ProperPos (chainModel C) (Qof P) P.n (pieceR c (R + 70)).2)
    (he1 : (pieceR c (R + 70)).1.edge < (chainModel C).W.n)
    (he2 : (pieceR c (R + 70)).2.edge < (chainModel C).W.n)
    (hi1 : (pieceR c (R + 70)).1.hgt = 0 ∨
      (chainModel C).InnerPt ((chainModel C).pos (Qof P) (pieceR c (R + 70)).1))
    (hi2 : (pieceR c (R + 70)).2.hgt = 0 ∨
      (chainModel C).InnerPt ((chainModel C).pos (Qof P) (pieceR c (R + 70)).2))
    (hwt : (chainModel C).arcWt ((chainModel C).key (Qof P) (pieceR c (R + 70)).1)
      ((chainModel C).key (Qof P) (pieceR c (R + 70)).2) ≤ c.nreg (R + 7))
    {o : Origin} (ho : OriginIn c (R + 3) o) (hol : o.Lt P.n (chainModel C))
    (hof : (∃ q, o = .walk ⟨q, 0⟩) ∨ ((chainModel C).InnerPt (o.eval (chainModel C) (Qof P)) ∧
      ∀ x, o = .walk x → ProperPos (chainModel C) (Qof P) P.n x))
    (hon : o.eval (chainModel C) (Qof P) ∉ (chainModel C).arcSet
      ((chainModel C).key (Qof P) (pieceR c (R + 70)).1)
      ((chainModel C).key (Qof P) (pieceR c (R + 70)).2))
    (hoy : |(o.eval (chainModel C) (Qof P)).2| < C.radius) {S : Set Point}
    (hbest : BestOK P C R c S (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg (R + 6))))
    (hroom : c.nreg ALLOC + F (c.nreg (R + 7)) + 17500 ≤ W) :
    ∃ c' k, Exec P W (leaf sh R) c c' k ∧ k ≤ F (c.nreg (R + 7)) + 17500 ∧
      BestOK P C R c' (S ∪ (chainModel C).arcSet
        ((chainModel C).key (Qof P) (pieceR c (R + 70)).1)
        ((chainModel C).key (Qof P) (pieceR c (R + 70)).2))
        (o.eval (chainModel C) (Qof P)) (dirOf (c.nreg (R + 6))) ∧
      FrameR oracleBands (WrLeaf R) c c' k := by
  have h := hR; unfold RegsOK at h
  set M := chainModel C with hM
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
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by omega_nf)
  have hM1 : c₁.nmem = c.nmem := f₁.2.2.1
  have hR1 : ∀ i, i < 300 → c₁.nreg (R + i) = c.nreg (R + i) := fun i hi => k1 _ (by omega)
  have hMD := hctx.modelDesc
  obtain ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ := hctx
  have hO1 : OriginIn c₁ (bandReg bShoot 5) o := by
    refine originIn_copy ho ?_ ?_ ?_ <;> omega_nf <;> norm_num
    all_goals omega
  
  -- the shot
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, fr₂⟩ := hsh P W c₁ e₁.wb_right
    ⟨hG, hHW, by rw [rd_shoot, s13, hM1, hA1]; exact hX,
      by rw [rd_shoot, rd_shoot, s9, s13, hM1]; exact hcap,
      by rw [rd_shoot, s0, hM1, hA1]; exact hmwf,
      fun _ H' C' hC' => by
        rw [rd_shoot, s0, hM1] at hC'
        rw [show (Qof P).n = P.n from shear_n _ _]; exact hreg H' hC'.1, M,
      by rw [rd_shoot, s0, hM1]; exact hMD, hOk,
      by rw [rd_shoot, rd_shoot, s1, s2]; exact hp1, by rw [rd_shoot, rd_shoot, s3, s4]; exact hp2,
      by rw [rd_shoot, s1]; exact he1, by rw [rd_shoot, s3]; exact he2,
      by rw [rd_shoot, rd_shoot, s1, s2]; exact hi1, by rw [rd_shoot, rd_shoot, s3, s4]; exact hi2,
      by rw [rd_shoot, rd_shoot, rd_shoot, rd_shoot, rd_shoot, s1, s2, s3, s4, s9]; exact hwt,
      o, hol, hO1, hof, by rw [rd_shoot, rd_shoot, rd_shoot, rd_shoot, s1, s2, s3, s4]; exact hon⟩
    (by rw [hA1]; show _ + F (rd c₁ bShoot 9) ≤ W; grind [rd_shoot])
  replace hk₂ : k₂ ≤ F (c.nreg (R + 7)) := by
    have h2 : k₂ ≤ F (rd c₁ bShoot 9) := hk₂
    rw [rd_shoot, s9] at h2; exact h2
  have post := post₂ M o (by rw [rd_shoot, s0, hM1]; exact hMD) hO1
  simp only [rd_shoot, Nat.reduceAdd, s1, s2, s3, s4, s8] at post
  obtain ⟨hhit, hnoh⟩ := post
  -- registers of the caller's block survive the shot
  have hR2 : ∀ i, i < 300 → c₂.nreg (R + i) = c.nreg (R + i) := fun i hi => by
    rw [fr₂.1 _ (fun hb => band_R hR hi (hBs hb)) (by unfold ALLOC; omega), hR1 i hi]
  have F01 : FrameR oracleBands (WrLeaf R) c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
    right; simp [setList] at hr; exact band_shoot (by omega)) (by simp [setList, ALLOC]) _
  have F12 : FrameR oracleBands (WrLeaf R) c₁ c₂ k₂ :=
    (FrameR.of_frame fr₂).mono hBs (fun _ h => h) le_rfl
  have F02 := F01.trans F12
  have ctx₂ : ShotCtx P W X Ok R c₂ H C :=
    ShotCtx.frame hXl ⟨hG, hHW, hX, hcap, hmwf, h0, hC, h34, hreg, hOk, hm, h30, h31, hσb⟩ F02
      (fun i hi => hR2 i (by omega))
  have best₂ : BestOK P C R c₂ S z σ := hbest.congr (hR2 20 (by omega)) (hR2 21 (by omega))
    (hR2 22 (by omega)) (hR2 24 (by omega)) (hR2 25 (by omega)) (hR2 26 (by omega))
    (hR2 27 (by omega))
  have w₂ := e₂.wb_right
  have c31 : c₂.nreg (R + 31) = 1 := by ram_simp
  have hA2 : c₂.nreg ALLOC ≤ c.nreg ALLOC + F (c.nreg (R + 7)) := by
    have := F12.2.2.2.2.2.2; omega
  -- no hit
  have nohit : c₂.nreg 140010 ≠ 1 → BestOK P C R c₂ (S ∪ A) z σ := fun hne => by
    have hNA : NoHit A z σ := hnoh hne
    refine ⟨best₂.1, fun hf => ?_, fun hf => noHit_union (best₂.2.2 hf) hNA⟩
    obtain ⟨t, ht, rest⟩ := best₂.2.1 hf
    exact ⟨t, firstHit_union_left ht hNA, rest⟩
  by_cases g1 : c₂.nreg (R + 31) < c₂.nreg 140010
  · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_true g1 (.skip w₂))), by omega,
      nohit (by omega), ?_⟩
    exact (F02.mono le_rfl (fun _ h => h) (by omega))
  by_cases g2 : c₂.nreg 140010 < c₂.nreg (R + 31)
  · refine ⟨c₂, _, .seq e₁ (.seq e₂ (.ifLtN_false g1 (.ifLtN_true g2 (.skip w₂)))), by omega,
      nohit (by omega), ?_⟩
    exact (F02.mono le_rfl (fun _ h => h) (by omega))
  -- a hit
  have hflag : c₂.nreg 140010 = 1 := by omega
  obtain ⟨t, htA, hpp, hpe, hpos⟩ := hhit hflag
  obtain ⟨-, hHW2, -, -, hmwf2, h02, hC2, h342, hreg2, -, -, h302, h312, hσb2⟩ := ctx₂
  obtain ⟨c₃, k₃, e₃, hk₃, best₃, f₃⟩ := leafHit_exec (P := P) hR c₂ w₂ hG hHW2
    (H := H) (C := C) (by rw [h342]; exact hmwf2.2 h02) (by grind)
    (by rw [h342]; exact hreg2) htA hpe hpp hpos hoy h302 h312 hσb2
    (by ram_simp) best₂ (by omega)
  refine ⟨c₃, _, .seq e₁ (.seq e₂ (.ifLtN_false g1 (.ifLtN_false g2 e₃))), by omega, best₃, ?_⟩
  have F23 : FrameR oracleBands (WrLeaf R) c₂ c₃ k₃ := FrameR.of_frameB f₃ (fun r hr => by
    simp only [Bhit, Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with ((h' | h') | h') | h'
    · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h')
    · exact Or.inr (band_prim h')
    · exact Or.inr (band_locate (by omega)))
    (by unfold ALLOC; simp only [Bhit, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega) _
  exact (F02.trans F23).mono le_rfl (fun _ h => h) (by omega)

end

end ShotList

end Chazelle.Core
