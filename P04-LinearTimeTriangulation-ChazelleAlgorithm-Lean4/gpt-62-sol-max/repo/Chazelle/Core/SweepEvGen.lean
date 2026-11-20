module

public import Chazelle.Core.SweepEvGenR

/-!
# The sweep (WP-D), stage 3: the genuineness check (task A)

`mkG sh`: from the arrival position `(eA + 1, eA + 2)` of the hit `w = rayPt a σ τ` of the model
of `C₁`:

1. the inputs of the answer stage's (`SweepIo`) local hit (`gSetL`): the model and chain descriptors of `C₁`, its
   normal form `N₁`, the position, the reverse direction code `1 - oD`, the walk length, an empty
   accumulator;
2. a positive height code naming the height of the position (`gHgt`: normalisation, and at a
   vertex the code of its symbolic point);
3. the local hit (`localHit sh`): the first hit `h` of the reverse ray from `w` (the least of its
   candidates, `lh_min`), with its abscissa record at `accA + 4`;
4. the comparison of the abscissas of `h` and `a` (`gCmp`): the hit is genuine iff `h` lies beyond
   `a` (`genuine_iff_abs`).

**`genTask : GenTask`**, cost `κGen D · (F γ + TLR + 1)`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

/-! ## The program -/

/-- The comparison of the abscissas of the reverse hit (`accA + 4`) and the origin (`oAbsA`):
direction code `0` (`σ = -1`): genuine iff `a.1 < h.1`; code `1`: iff `h.1 < a.1`. -/
def gCmp : Stmt :=
  .ifLtN oD K1 (callAbsCmp oAbsA (accA + 4) cG) (callAbsCmp (accA + 4) oAbsA cG)

/-- **The genuineness check.** -/
def mkG (sh : Stmt) : Stmt := .seq (block gSetL) (.seq gHgt (.seq (localHit sh) gCmp))

/-- The cost of the check. -/
def genK (Fg D T : ℕ) : ℕ := 9 + (42030 + (localK T Fg (D + 1) D + (269 + 2)))

/-- The constant of the cost bound. -/
def κGen (D : ℕ) : ℕ := localK 0 0 (D + 1) D + 16 * (3 * (D + 1) + 1) + 50000

theorem localK_lin (T Fg Da Dc : ℕ) :
    localK T Fg Da Dc = localK 0 0 Da Dc + 5500 * T + (3 * Da + 1) * (16 * Fg) := by
  unfold localK lh1K shotOfferK ShotList.shotCost
  ring

theorem genK_le (Fg D T : ℕ) : genK Fg D T ≤ κGen D * (Fg + T + 1) := by
  unfold genK κGen
  rw [localK_lin]
  set A := localK 0 0 (D + 1) D
  set B := 16 * (3 * (D + 1) + 1) with hB
  have e1 : (3 * (D + 1) + 1) * (16 * Fg) = B * Fg := by rw [hB]; ring
  have e2 : (A + B + 50000) * (Fg + T + 1) =
      A * Fg + A * T + A + B * Fg + B * T + B + 50000 * Fg + 50000 * T + 50000 := by ring
  rw [e1, e2]
  have := Nat.zero_le (A * Fg)
  have := Nat.zero_le (A * T)
  have := Nat.zero_le (B * T)
  omega

theorem dirOf_pm (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  unfold dirOf; split_ifs <;> simp

/-! ## The contract -/

section exec

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {P : Polygon} {W : ℕ} {c₀ : Config} {J : Merge.Junction} {N₁ N₂ : NF}

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 40000 in
/-- **The genuineness check meets its contract.** -/
theorem genOK_mkG (E : EvEnv sh Bs F X Ok P W c₀ J N₁ N₂) :
    GenOK P W c₀ J (mkG sh) (κGen (c₀.nreg (sw 6)) * (F (c₀.nreg (sw 5)) + c₀.nreg TLR + 1)) := by
  intro c₁ a σ τ hI₁ hroom hD hσ habs haR hav ha₁ hτ he hpp harr
  set Fg := F (c₀.nreg (sw 5)) with hFg
  set D := c₀.nreg (sw 6) with hDd
  set T := c₀.nreg TLR with hTd
  have hgk : 9 + (42030 + (localK T Fg (D + 1) D + (269 + 2))) ≤ κGen D * (Fg + T + 1) :=
    genK_le Fg D T
  have hσ' : σ = 1 ∨ σ = -1 := by rw [hσ]; exact dirOf_pm _
  have hW3 : P.n + 3 ≤ W := by have := E.hWh; unfold hostWords at this; omega
  -- the geometry of the hit
  have hR : J.left.radius = J.right.radius := rfl
  have hay : |a.2| < J.left.radius := by
    rw [hR]
    exact lt_of_le_of_lt (J.right.abs_le_coordBound_of_mem_set haR).2 J.right.coordBound_lt_radius
  set x : WPos := ⟨c₁.nreg (eA + 1), c₁.nreg (eA + 2)⟩ with hxd
  set w := rayPt a σ τ with hwd
  have hw2 : w.2 = a.2 := rfl
  obtain ⟨hposx, hcl, hloc, hwD⟩ := arr_facts (N := P.n) (x := x) he hpp harr
    (by rw [hw2]; exact hay) (by rw [hw2]; exact ha₁)
  have haD : a ∈ J.left.dom := origin_mem_left_dom E.hP haR hav ha₁
  have hrev : dirOf (1 - c₁.nreg oD) = -σ := by
    rw [hσ, ← dirOf_rev hD, neg_neg]
  -- 1. the inputs of the local hit
  refine (IRS.seq (K₁ := 9) (K₂ := 42030 + (localK T Fg (D + 1) D + (269 + 2)))
    ((IRS.block gSetL hI₁ (gSet_ok _ _ (Nat.zero_le _))).mono (by simp [gSetL])
      (fun _ h => h)) ?_).mono (by omega) (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' hc₂
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, vo⟩ := gSet_val c₁.nmem c₁.nreg
  have g2 : ∀ q, (q < 241100 ∨ 241107 < q) → q ≠ accA → c₂.nreg q = c₁.nreg q := fun q h h' => by
    rw [hc₂]; exact vo q h h'
  have m₂ : c₂.nmem = c₁.nmem := by rw [hc₂]
  have r2 : ∀ r, ∀ v, regB c₁.nmem gSetL c₁.nreg r = v → c₂.nreg r = v := fun r v h => by
    rw [hc₂]; exact h
  have hK₁ := E.hK.fix hI₁
  have s2E : c₂.nreg lE = x.edge := r2 _ _ v4
  have s2H : c₂.nreg lH = x.hgt := r2 _ _ v5
  have s2D : c₂.nreg lD = 1 - c₁.nreg oD := by rw [r2 _ _ v6, hK₁.2.1]
  have s2N : c₂.nreg lN = 2 * J.left.m + 7 := by
    rw [r2 _ _ v7, (E.hM.fix hI₁).n1, WalkEmbed.cm_n]
  have s2T : c₂.nreg lT = 0 := r2 _ _ v8
  have s2A : c₂.nreg accA = 0 := r2 _ _ v9
  have s2MD : c₂.nreg lMD = c₁.nreg MD₁ := r2 _ _ v1
  have s2CD : c₂.nreg lCD = c₁.nreg CD₁ := r2 _ _ v2
  have s2NF : c₂.nreg lNF = c₁.nreg (sw 3) := r2 _ _ v3
  -- 2. a positive height code
  have hctx₂ : ChainCtx P W c₂ CD₁ J.left := E.ctx1' hI₂
  have hn₂ : c₂.nreg cN1 = 2 * J.left.m + 7 := by
    rw [(E.hM.fix hI₂).n1, WalkEmbed.cm_n]
  refine IRS.seq (K₁ := 42030) (K₂ := localK T Fg (D + 1) D + (269 + 2))
    (gHgt_irs hI₂ E.hK hctx₂ hn₂ (x := x) s2E s2H he hpp hcl
      (by rw [hposx, hw2]; exact hay) (by omega) (by omega)) ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨k, s3E, s3H, hkl, hkh, hkpar, hkpos, hkpp, k3, hA₃'', m₃⟩
  set xs : WPos := ⟨x.edge, k + 1⟩ with hxs
  have k3' : ∀ r, r ≠ lH → 241000 ≤ r → r < 242200 → (r < sw 720 ∨ sw 726 < r) →
      c₃.nreg r = c₂.nreg r := fun r h1 h2 h3 h4 =>
    k3 r (not_oracle_sw (by omega) (by omega)) h1 h4 (by unfold ALLOC; omega)
  have s3D : c₃.nreg lD = 1 - c₁.nreg oD := by
    rw [k3' lD (by unfold lD lH sw; omega) (by unfold lD sw; omega) (by unfold lD sw; omega)
      (Or.inr (by unfold lD sw; omega))]; exact s2D
  have s3N : c₃.nreg lN = 2 * J.left.m + 7 := by
    rw [k3' lN (by unfold lN lH sw; omega) (by unfold lN sw; omega) (by unfold lN sw; omega)
      (Or.inr (by unfold lN sw; omega))]; exact s2N
  have s3T : c₃.nreg lT = 0 := by
    rw [k3' lT (by unfold lT lH sw; omega) (by unfold lT sw; omega) (by unfold lT sw; omega)
      (Or.inr (by unfold lT sw; omega))]; exact s2T
  have s3A : c₃.nreg accA = 0 := by
    rw [k3' accA (by unfold accA lH sw; omega) (by unfold accA sw; omega)
      (by unfold accA sw; omega) (Or.inr (by unfold accA sw; omega))]; exact s2A
  have s3MD : c₃.nreg lMD = c₃.nreg MD₁ := by
    rw [k3' lMD (by unfold lMD lH sw; omega) (by unfold lMD sw; omega) (by unfold lMD sw; omega)
      (Or.inr (by unfold lMD sw; omega)), s2MD, hI₁.hin _ (by unfold IFix MD₁ sw; omega),
      hI₃.hin _ (by unfold IFix MD₁ sw; omega)]
  have s3CD : c₃.nreg lCD = c₃.nreg CD₁ := by
    rw [k3' lCD (by unfold lCD lH sw; omega) (by unfold lCD sw; omega) (by unfold lCD sw; omega)
      (Or.inr (by unfold lCD sw; omega)), s2CD, hI₁.hin _ (by unfold IFix CD₁ sw; omega),
      hI₃.hin _ (by unfold IFix CD₁ sw; omega)]
  have s3NF : c₃.nreg lNF = c₀.nreg (sw 3) := by
    rw [k3' lNF (by unfold lNF lH sw; omega) (by unfold lNF sw; omega) (by unfold lNF sw; omega)
      (Or.inr (by unfold lNF sw; omega)), s2NF, hI₁.hin _ (by unfold IFix sw; omega)]
  -- 3. the local hit
  have hTBR₃ : c₃.nreg TBR = c₀.nreg TBR := hI₃.hin _ (by unfold IFix TBR sw; omega)
  have hTLR₃ : c₃.nreg TLR = c₀.nreg TLR := hI₃.hin _ (by unfold IFix TLR sw; omega)
  have hTA := E.hTBR
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI₃
  have hL₃ : LCtx P W J.left N₁ (c₀.nreg TBR) c₃ :=
    { hG := E.hG
      hWh := E.hWh
      hctx := (E.ctx1' hI₃).transport s3CD (fun _ _ => rfl) le_rfl
      hcd := by rw [s3CD, s3MD]; exact md4
      hmd := by rw [s3MD]; exact md1
      hmwf := by rw [s3MD]; exact md2
      hm0 := by rw [s3MD]; exact md3
      hP := E.hP
      hNW := by
        rw [s3NF]
        exact E.hNT₁.transport (fun b hb => hI₃.hm b (by omega))
      hE := by have := hI₃.hA; omega
      hNF := E.hNF₁
      htab := fun j hj => by
        rw [hTLR₃] at hj
        rw [hTBR₃, hI₃.hm _ (by omega)]
        exact E.htab j hj
      hbig := by rw [hTLR₃]; exact E.hbig₁
      hTB := by rw [hTBR₃]
      hTW := by rw [hTBR₃, hTLR₃]; have := hI₃.hA; omega }
  obtain ⟨hAr, hCh⟩ := region_bounds (C := J.left) E.hP E.hNF₁ E.hdeg₁
  have hposxs : (chainModel J.left).pos (Qof P) xs = w := hkpos.trans hposx
  have hlocs : (xs.edge = 1 ∨ xs.edge = 3) ∨
      (6 ≤ xs.edge ∧ (chainModel J.left).pos (Qof P) xs ∈ J.left.set) := by
    rw [hkpos]; exact hloc
  have hacc : AccOK P accA (fun _ => J.left) J.left.radius
      ((chainModel J.left).pos (Qof P) xs) (dirOf (1 - c₁.nreg oD)) ∅ c₃ :=
    accOK_init accA _ _ _ _ s3A
  refine IRS.seq (K₁ := localK T Fg (D + 1) D) (K₂ := 269 + 2)
    ((localHit_irs (C := J.left) (N := N₁) (Mod := fun _ => J.left) (R₀ := J.left.radius)
      (L := ∅) (Da := D + 1) (Dc := D) (x := xs) (d := 1 - c₁.nreg oD)
      E.hsh E.hBs E.hXl hI₃ E.hK hL₃ E.hX E.hcap E.hOk₁ E.hsg₁ hAr hCh s3E s3H s3D he hkpp
      (by rw [hposxs, hw2]; exact hay) hlocs hacc (by rw [s3T]; omega) rfl rfl s3N
      (by rw [hTLR₃]; show c₃.nreg ALLOC + localK T Fg (D + 1) D ≤ W; omega)).mono
        (by rw [hTLR₃]) (fun _ h => h)) ?_
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨L', hacc', -, hL', hgeo⟩, k4, hA₄'', m₄⟩
  -- the reverse hit
  have hgeo' : LHGeo P J.left xs (1 - c₁.nreg oD) := by
    refine ⟨k, rfl, hkl, by rw [hkpos]; exact hkh, ?_, by rw [hposxs, hw2]; exact ha₁⟩
    rw [hposxs, hrev]
    show sideLeft (chainModel J.left).W x.edge ((chainModel J.left).param (Qof P) xs) _
    rw [hkpar]
    exact harr.2.2.2.2
  obtain ⟨hfree, hmem⟩ := hgeo hgeo'
  rw [hposxs, hrev] at hfree hmem hacc' hL'
  obtain ⟨hf1, hf0, hf⟩ := hacc'
  have hflag : c₄.nreg accA = 1 := by
    by_contra hne
    have h0 : c₄.nreg accA = 0 := by omega
    rw [hf0 h0] at hmem
    exact hmem
  obtain ⟨τm, hτm, hmin, -, -, -, -, habsH⟩ := hf hflag
  have hσ'' : -σ = 1 ∨ -σ = -1 := by rcases hσ' with h | h <;> rw [h] <;> norm_num
  have hτeq : τm = J.left.hitParam w (-σ) :=
    lh_min hσ'' (by rw [hw2]; exact ha₁) (fun t ht => by
      rcases hL' t ht with h | h
      · exact absurd h (Set.notMem_empty t)
      · exact h) hfree hmem hτm hmin
  rw [hτeq] at habsH
  obtain ⟨gp, gn⟩ := genuine_iff_abs hσ' haD hwD hτ ha₁ hfree
  -- the registers of `c₁` at `c₄`
  have keep : ∀ r, bandOf r ∉ oracleBands → ¬ GR r → r ≠ ALLOC → c₄.nreg r = c₁.nreg r := by
    intro r h1 h2 h3
    have hGR : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ r = cG ∨ (sw 3000 ≤ r ∧ r < sw 4000)) := h2
    rw [k4 r h1 (fun h => hGR (by unfold LHW at h; unfold cG; unfold sw at h ⊢; omega)) h3,
      k3 r h1 (fun h => hGR (by subst h; unfold lH sw; omega))
        (by unfold sw at hGR ⊢; omega) h3,
      g2 r (by unfold sw at hGR; omega) (fun h => hGR (by subst h; unfold accA sw; omega))]
  have hD4 : c₄.nreg oD = c₁.nreg oD :=
    keep oD (not_oracle_sw (by unfold oD sw; omega) (by unfold oD sw; omega))
      (by unfold GR oD cG sw; omega) (by unfold oD ALLOC sw; omega)
  have kA : ∀ i, i < 4 → c₄.nreg (oAbsA + i) = c₁.nreg (oAbsA + i) := fun i hi =>
    keep _ (not_oracle_sw (by unfold oAbsA sw; omega) (by unfold oAbsA sw; omega))
      (by unfold GR oAbsA cG sw; omega) (by unfold oAbsA ALLOC sw; omega)
  have habs4 : AbsRec P c₄ oAbsA a.1 J.left.radius :=
    absRec_transport habs (kA 0 (by norm_num)) (kA 1 (by norm_num)) (kA 2 (by norm_num))
      (kA 3 (by norm_num))
  have hk1₄ : c₄.nreg K1 = 1 := (E.hK.fix hI₄).2.1
  -- the frame
  have hfin : ∀ c', (∀ r, bandOf r ∉ oracleBands → r ≠ cG → r ≠ ALLOC → c'.nreg r = c₄.nreg r) →
      c₄.nreg ALLOC ≤ c'.nreg ALLOC → (∀ b, b < c₄.nreg ALLOC → c'.nmem b = c₄.nmem b) →
      EFr GR c₁ c' := fun c' h1 h2 h3 => by
    refine ⟨fun r hr1 hr2 hr3 => ?_, by omega, fun b hb => ?_⟩
    · rw [h1 r hr1 (fun h => hr2 (Or.inr (Or.inl h))) hr3]; exact keep r hr1 hr2 hr3
    · rw [h3 b (by omega), m₄ b (by omega), m₃ b (by omega), m₂]
  unfold gCmp
  refine IRS.ite (K := 269) (fun hlt => ?_) (fun hlt => ?_)
  · -- code `0`: `σ = -1`
    have hd0 : c₁.nreg oD = 0 := by rw [hD4, hk1₄] at hlt; omega
    have hsn : σ = -1 := by rw [hσ, hd0]; rfl
    refine (callAbsCmp_irs (o := cG) hI₄ E.hG hW3
      ⟨by unfold oAbsA sw; omega, by unfold oAbsA sw; omega, by unfold accA sw; omega,
        by unfold accA sw; omega⟩ ⟨by unfold cG sw; omega, by unfold cG sw; omega⟩ habs4 habsH
      (by omega)).mono le_rfl ?_
    rintro c' ⟨hbit, h1, h2, h3⟩
    refine ⟨⟨hbit.1, by rw [hbit.2, gn hsn]⟩, hfin c' h1 h2 h3⟩
  · -- code `1`: `σ = 1`
    have hd1 : c₁.nreg oD = 1 := by rw [hD4, hk1₄] at hlt; omega
    have hsp : σ = 1 := by rw [hσ, hd1]; rfl
    refine (callAbsCmp_irs (o := cG) hI₄ E.hG hW3
      ⟨by unfold accA sw; omega, by unfold accA sw; omega, by unfold oAbsA sw; omega,
        by unfold oAbsA sw; omega⟩ ⟨by unfold cG sw; omega, by unfold cG sw; omega⟩ habsH habs4
      (by omega)).mono le_rfl ?_
    rintro c' ⟨hbit, h1, h2, h3⟩
    refine ⟨⟨hbit.1, by rw [hbit.2, gp hsp]⟩, hfin c' h1 h2 h3⟩

end exec

/-- **Task A: the genuineness check.** -/
theorem genTask : GenTask :=
  ⟨mkG, κGen, fun _ _ _ _ _ _ _ _ _ _ _ E => genOK_mkG E⟩

end

end SweepEv

end Chazelle.Core
