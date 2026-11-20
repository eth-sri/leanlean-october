module

meta import Chazelle.Programs.RamEval

public import Chazelle.Core.SweepEvStopH
public import Chazelle.Core.SweepEvStopM3

/-!
# The sweep (WP-D), stage 2: a local hit in a chain model (RAM)

`lhRun sh md cd nf nr`: the local hit (the answer stage's (`SweepIo`) `localHit`) of the model whose model descriptor,
chain descriptor, normal form and walk length are in the registers `md, cd, nf, nr`, from the
position in `(lE, lH)` (any code: it is fixed by `hHgt`) in the direction of code `lD`, into an
empty accumulator `accA` (constant model tag).  `lhRun_irs`: the candidates are points of the chain
or of the box on the ray, and under the geometric conditions (the ray in the left sector, the
point not above the top) the direction is free and the first hit is a candidate.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- The context of a model for the local hit, at registers `md, cd, nf` (`LCtx` with
these registers). -/
structure MCtx (P : Polygon) (W : ℕ) (C : Chain) (N : NF) (E : ℕ) (md cd nf : ℕ) (c : Config) :
    Prop where
  hctx : ChainCtx P W c cd C
  hcd : c.nreg cd = c.nreg md + 1
  hmd : ModelDescAt c.nmem (c.nreg md) (Qof P) (chainModel C)
  hmwf : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg md)
  hm0 : c.nmem (c.nreg md) = 0
  hNW : NFWithin c.nmem (c.nreg nf) E N
  hE : E ≤ c.nreg ALLOC
  htab : ∀ j, j < c.nreg TLR → c.nmem (c.nreg TBR + j) = 2 ^ j
  hbig : N.arcs.length < 2 ^ c.nreg TLR
  hTB : E ≤ c.nreg TBR
  hTW : c.nreg TBR + c.nreg TLR ≤ c.nreg ALLOC

/-- The setup of the local hit. -/
def lhSetL (md cd nf nr : ℕ) : List Instr :=
  [.copyN lMD md, .copyN lCD cd, .copyN lNF nf, .copyN lN nr, .constN lT 0, .constN accA 0]

/-- **A local hit** in the model of the registers `md, cd, nf, nr`. -/
def lhRun (sh : Stmt) (md cd nf nr : ℕ) : Stmt :=
  .seq (block (lhSetL md cd nf nr)) (.seq (hHgt cd nr) (localHit sh))

/-- The registers of the local-hit run (besides the oracle bands and the allocator). -/
def LHR (r : ℕ) : Prop := (sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 3200)

/-- The cost of the local-hit run. -/
def lhRunK (T Fg D : ℕ) : ℕ := 6 + (42030 + localK T Fg (D + 1) D)

theorem lhSet_val (m f : ℕ → ℕ) {md cd nf nr : ℕ} (_hd : DR md) (hc : DR cd) (hn : DR nf)
    (hr : DR nr) :
    regB m (lhSetL md cd nf nr) f lMD = f md ∧ regB m (lhSetL md cd nf nr) f lCD = f cd ∧
    regB m (lhSetL md cd nf nr) f lNF = f nf ∧ regB m (lhSetL md cd nf nr) f lN = f nr ∧
    regB m (lhSetL md cd nf nr) f lT = 0 ∧ regB m (lhSetL md cd nf nr) f accA = 0 ∧
    (∀ q, q ≠ lMD → q ≠ lCD → q ≠ lNF → q ≠ lN → q ≠ lT → q ≠ accA →
      regB m (lhSetL md cd nf nr) f q = f q) := by
  unfold DR at _hd hc hn hr
  have e1 : lMD = 241100 := rfl
  have e2 : lCD = 241101 := rfl
  have e3 : lNF = 241102 := rfl
  have e4 : lN = 241106 := rfl
  have e5 : lT = 241107 := rfl
  have e6 : accA = 242000 := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 => ?_⟩ <;>
    simp only [lhSetL, regB, regI, upd, e1, e2, e3, e4, e5, e6] at * <;>
    simp (disch := omega) only [ite_false, ite_eq_right, ite_eq_left, *]

/-- **The local-hit run.** -/
theorem lhRun_irs {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands)
    (hXl : X.CapLocal) {C : Chain} {N : NF} {E : ℕ} {md cd nf nr : ℕ}
    (hd : DR md) (hc : DR cd) (hn : DR nf) (hr : DR nr)
    (hI : IInv W c₀ c) (hK : Consts c₀) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hM : MCtx P W C N E md cd nf c) (hPs : C.P.Simple) (hNF : IsNF (chainModel C) (Qof P) N)
    (hX : X.holds P c₀.nmem (c₀.nreg (sw 10)) (c₀.nreg ALLOC))
    (hcap : c₀.nreg (sw 5) ≤ X.cap P c₀.nmem (c₀.nreg (sw 10)))
    (hOk : Ok P (chainModel C))
    (hsg : (chainModel C).Semigranular (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 5)))
    (hdeg : (chainModel C).DegLe (N.F (chainModel C) (Qof P)) (c₀.nreg (sw 6)))
    (hnr : c.nreg nr = 2 * C.m + 7) {x : WPos} (hxE : c.nreg lE = x.edge)
    (hxH : c.nreg lH = x.hgt) (_hxD : c.nreg lD ≤ 1) (he : x.edge < (chainModel C).W.n)
    (hpp : ProperPos (chainModel C) (Qof P) P.n x) (hcl : PosClass C (Qof P) x)
    (hy : |((chainModel C).pos (Qof P) x).2| < C.radius)
    (hon : (chainModel C).pos (Qof P) x ∈ C.set ∨
      |((chainModel C).pos (Qof P) x).1| = C.radius)
    (hroom : c.nreg ALLOC + lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6)) ≤ W) :
    IRS P W c₀ (lhRun sh md cd nf nr) c
      (lhRunK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))) (fun c' =>
      ∃ L', AccOK P accA (fun _ => C) C.radius ((chainModel C).pos (Qof P) x)
          (dirOf (c.nreg lD)) L' c' ∧
        (∀ τ ∈ L', 0 < τ ∧ OnCB C (rayPt ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) τ)) ∧
        ((sideLeft (chainModel C).W x.edge ((chainModel C).param (Qof P) x)
            (rayPt ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) 1) ∧
          ((chainModel C).pos (Qof P) x).2 ≤ C.top.2) →
          Merge.FreeAt C ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) ∧
            C.hitParam ((chainModel C).pos (Qof P) x) (dirOf (c.nreg lD)) ∈ L') ∧
      EFr LHR c c') := by
  set Fg := F (c₀.nreg (sw 5)) with hFg
  set D := c₀.nreg (sw 6) with hDd
  set T := c₀.nreg TLR with hTd
  unfold lhRun lhRunK at *
  
  -- 1. the setup
  have hok : okB W c.nmem (lhSetL md cd nf nr) c.nreg := by
    simp only [lhSetL, reg_check]
    exact ⟨iscr_sw (by reg_omega) (by reg_omega),
      iscr_sw (by reg_omega) (by reg_omega),
      iscr_sw (by reg_omega) (by reg_omega),
      iscr_sw (by reg_omega) (by reg_omega),
      ⟨iscr_sw (by reg_omega) (by reg_omega), Nat.zero_le _⟩,
      ⟨iscr_sw (by reg_omega) (by reg_omega), Nat.zero_le _⟩, trivial⟩
  refine IRS.seq (K₁ := 6) (K₂ := 42030 + localK T Fg (D + 1) D)
    ((IRS.block _ hI hok).budget (by simp [lhSetL])) ?_
  rintro c₁ hI₁ hA₁ hA₁' hc₁
  obtain ⟨v1, v2, v3, v4, v5, v6, vo⟩ := lhSet_val c.nmem c.nreg hd hc hn hr
  have r1 : ∀ r v, regB c.nmem (lhSetL md cd nf nr) c.nreg r = v → c₁.nreg r = v :=
    fun r v h => by rwa [hc₁]
  have m1 : c₁.nmem = c.nmem := by rw [hc₁]
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := r1 _ _ (ram_app% (vo _ ?_
    ?_ ?_ ?_
    ?_ ?_))
  have keep1 := fun q a b d e f g => r1 _ _ (vo q a b d e f g)
  have kD : ∀ r, DR r → c₁.nreg r = c.nreg r := fun r h => by
    unfold DR at h
    exact keep1 r (by reg_omega) (by reg_omega) (by reg_omega)
      (by reg_omega) (by reg_omega) (by reg_omega)
  have s1E : c₁.nreg lE = x.edge := by
    ram_simp [keep1] <;> reg_omega
  have s1H : c₁.nreg lH = x.hgt := by
    ram_simp [keep1] <;> reg_omega
  have s1D : c₁.nreg lD = c.nreg lD := keep1 lD (by reg_omega)
    (by reg_omega) (by reg_omega) (by reg_omega)
    (by reg_omega) (by reg_omega)
  have hctx₁ := hM.hctx.transport (kD cd hc) (fun a _ => by rw [m1])
    (by rw [hA1])
  have hnr₁ : c₁.nreg nr = 2 * C.m + 7 := by rwa [kD nr hr]
  have hPW : P.n + 1 ≤ W := by unfold hostWords at hWh; omega
  -- 2. the height code
  refine IRS.seq (K₁ := 42030) (K₂ := localK T Fg (D + 1) D)
    (hHgt_irs hc hr hI₁ hK hctx₁ hnr₁ s1E s1H he hpp hcl hy (by omega) hPW) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨k, s2E, s2H, hkl, hkh, hkpar, hkpos, hkpp, k2, hA₂'', m2⟩
  set xs : WPos := ⟨x.edge, k + 1⟩ with hxs
  have keep2 := k2
  have k2s := fun r h1 h2 h3 h4 =>
    keep2 r (not_oracle_sw h1 h2) h3 h4 (by reg_omega)
  have s2D : c₂.nreg lD = c.nreg lD := by
    ram_simp [k2s, s1D] 
  have s2N : c₂.nreg lN = 2 * C.m + 7 := by
    ram_simp [k2s, r1, hnr] 
  have s2T : c₂.nreg lT = 0 := by
    ram_simp [k2s, r1] 
  have s2A : c₂.nreg accA = 0 := by
    ram_simp [k2s, r1] 
  have s2MD : c₂.nreg lMD = c.nreg md := by
    ram_simp [k2s, r1] 
  have s2CD : c₂.nreg lCD = c.nreg cd := by
    ram_simp [k2s, r1] 
  have s2NF : c₂.nreg lNF = c.nreg nf := by
    ram_simp [k2s, r1] 
  have hTBR₂ : c₂.nreg TBR = c.nreg TBR := by
    ram_post
  have hTLR₂ : c₂.nreg TLR = c.nreg TLR := by
    ram_rw [hI₂.hin, hI.hin]
  have hTLRc : c.nreg TLR = T := hI.hin _ (by reg_omega)
  have mem2 : MemEqBelow (c.nreg ALLOC) c₂.nmem c.nmem := fun a ha => by
    rw [m2 a (by rwa [hA1]), m1]
  have hA2 : c.nreg ALLOC ≤ c₂.nreg ALLOC := by rwa [← hA1]
  have hL₂ : LCtx P W C N E c₂ :=
    { hG := hG
      hWh := hWh
      hctx := by
        refine hM.hctx.transport (by rw [s2CD]) mem2 hA2
      hcd := by rw [s2CD, s2MD]; exact hM.hcd
      hmd := by
        rw [s2MD]
        rcases hM.hmd with ⟨h0, H, C', hC', hMC⟩ | ⟨h1, -⟩
        · obtain ⟨w1, w2, w3⟩ := ShotList.modelDesc_keep hM.hmwf hM.hm0 hC' mem2 hA2
          exact Or.inl ⟨w2, H, C', w3, hMC⟩
        · have := hM.hm0; omega
      hmwf := by
        rw [s2MD]
        rcases hM.hmd with ⟨h0, H, C', hC', hMC⟩ | ⟨h1, -⟩
        · exact (ShotList.modelDesc_keep hM.hmwf hM.hm0 hC' mem2 hA2).1
        · have := hM.hm0; omega
      hm0 := by rw [s2MD, mem2 _ (by have := hM.hmwf.1; omega)]; exact hM.hm0
      hP := hPs
      hNW := by rw [s2NF]; exact (hM.hNW.transport fun b hb => mem2 b (by
        have := hM.hE; omega))
      hE := le_trans hM.hE hA2
      hNF := hNF
      htab := fun j hj => by
        rw [hTLR₂] at hj
        rw [hTBR₂, mem2 _ (by have := hM.hTW; omega)]
        exact hM.htab j hj
      hbig := by rw [hTLR₂]; exact hM.hbig
      hTB := by rw [hTBR₂]; exact hM.hTB
      hTW := by rw [hTBR₂, hTLR₂]; have := hM.hTW; omega }
  obtain ⟨hAr, hCh⟩ := region_bounds (C := C) hPs hNF hdeg
  have hposxs := hkpos
  have hlocs : (xs.edge = 1 ∨ xs.edge = 3) ∨
      (6 ≤ xs.edge ∧ (chainModel C).pos (Qof P) xs ∈ C.set) := by
    rw [hposxs]
    rcases hcl with h | ⟨h6, h6'⟩ | ⟨h6, hz⟩
    · exact Or.inl h
    · rcases hon with h | h
      · exact Or.inr ⟨h6, h⟩
      · exfalso
        have hm := C.sideWalk_tour_pt_mem C.sideBeta (i := x.edge - 6)
          (t := (chainModel C).param (Qof P) x) (by omega) (fun h'' => by omega) hpp.1 hpp.2.1
        rw [show x.edge - 6 + 6 = x.edge by omega] at hm
        exact SweepStop.not_mem_set_of_abs C h hm
    · rcases hon with h | h
      · exact Or.inr ⟨by have := C.one_le; show 6 ≤ x.edge; omega, h⟩
      · exfalso
        have hm := C.sideWalk_tour_pt_mem C.sideBeta (i := 2 * C.m) (t := 0)
          le_rfl (fun _ => rfl) le_rfl one_pos
        have : (chainModel C).pos (Qof P) x = sidePt (C.sideWalk C.sideBeta) (2 * C.m + 6) 0 := by
          show sidePt (chainModel C).W _ _ = _
          rw [cm_W, h6, hz]
        rw [this] at h
        exact SweepStop.not_mem_set_of_abs C h hm
  have hacc : AccOK P accA (fun _ => C) C.radius
      ((chainModel C).pos (Qof P) xs) (dirOf (c₂.nreg lD)) ∅ c₂ :=
    accOK_init accA _ _ _ _ s2A
  refine (localHit_irs (C := C) (N := N) (Mod := fun _ => C) (R₀ := C.radius)
      (L := ∅) (Da := c₀.nreg (sw 6) + 1) (Dc := c₀.nreg (sw 6)) (x := xs) (d := c₂.nreg lD)
      hsh hBs hXl hI₂ hK hL₂ hX hcap hOk hsg hAr hCh s2E s2H rfl he hkpp
      (by rwa [hposxs]) hlocs hacc (by rw [s2T]; omega) rfl rfl s2N
      (by rw [hTLR₂, hTLRc]; show c₂.nreg ALLOC + localK T Fg (D + 1) D ≤ W; omega)).mono
        (by rw [hTLR₂, hTLRc]) ?_
  rintro c' ⟨⟨L', hacc', -, hL', hgeo⟩, k3, hA₃, m3⟩
  rw [hposxs, s2D] at hacc' hL' hgeo
  refine ⟨L', hacc', fun τ hτ => ?_, fun ⟨hsl, htop⟩ => hgeo ?_, ?_⟩
  · rcases hL' τ hτ with h | h
    · exact absurd h (Set.notMem_empty τ)
    · exact h
  · refine ⟨k, rfl, hkl, by rwa [hkpos], ?_, by rwa [hposxs]⟩
    simp only [hposxs, hkpar] <;> omega
  · refine ⟨fun r h1 h2 h3 => ?_, le_trans hA2 hA₃, fun a ha => ?_⟩
    · have hr2 : ¬ ((sw 700 ≤ r ∧ r < sw 2200) ∨ (sw 3000 ≤ r ∧ r < sw 3200)) := h2
      rw [k3 r h1 (fun h => hr2 (by unfold LHW sw at h; unfold sw; omega)) h3,
        keep2 r h1 (fun h => hr2 (by subst h; unfold lH sw; omega)) (by unfold sw at hr2 ⊢; omega)
          h3, keep1 r (fun h => hr2 (by subst h; unfold lMD sw; omega))
          (fun h => hr2 (by subst h; unfold lCD sw; omega))
          (fun h => hr2 (by subst h; unfold lNF sw; omega))
          (fun h => hr2 (by subst h; unfold lN sw; omega))
          (fun h => hr2 (by subst h; unfold lT sw; omega))
          (fun h => hr2 (by subst h; unfold accA sw; omega))]
    · ram_rw [m3 a, mem2 a ha]

end

end SweepEv

end Chazelle.Core
