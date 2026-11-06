module

public import Chazelle.Core.SweepEvStopBrute

/-!
# The sweep (WP-D), stage 2: the brute-force shot at `N₁`, the run

**`bruteTask : BruteTask`** (program `stbProg`, see `SweepEvStopBrute`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 200000 in
/-- **Task B: the brute-force shot at `N₁`.** -/
theorem bruteTask : BruteTask := by
  refine ⟨stbProg, stbK, ?_⟩
  intro sh Bs F X Ok P W c₀ c J N₁ N₂ E hI s hs hsl hzC hz1 hz2 hzt hd hroom
  have hP : J.left.P.Simple := E.hP
  have hNF := E.hNF₁
  have hAr := arcsTask J.left (Qof P) N₁ hP hNF
  have hcost := stb_cost N₁.arcs.length N₁.nChords (F (c₀.nreg (sw 5))) hAr
  have nb : ∀ j, j < 10000 → bandOf (sw j) ∉ oracleBands := fun j hj => nob_sw hj
  obtain ⟨pv, p1, p2, p3, p4, p5, po⟩ := stbPre_val c.nmem c.nreg
  unfold stbProg
  refine (IRS.seq (K₁ := 10) (K₂ := bLoopK N₁.arcs.length +
      (symShotK (F (c₀.nreg (sw 5))) N₁.arcs.length + 12))
    ((IRS.block stbPre hI (stbPre_ok _ _)).mono (by simp [stbPre]) (fun _ h => h)) ?_).mono
    hcost (fun _ h => h)
  rintro c₁ hI₁ hA₁ hA₁' rfl
  simp only at hA₁ hA₁'
  have eA1 : regB c.nmem stbPre c.nreg ALLOC = c.nreg ALLOC :=
    po _ (by unfold StbPreW; simp [ALLOC, sw, qD, accA])
  -- the chain context of `C₁` at `sw 20`
  obtain ⟨H₀, hJ₀, hst⟩ := E.hst
  obtain ⟨-, -, -, -, -, -, d20, w20, -⟩ := hst
  have hctx20 : ChainCtx P W { c with nreg := regB c.nmem stbPre c.nreg } (sw 20) J.left :=
    (chainCtx_of E.hG E.hWh hP hJ₀ E.hJWF d20 w20).transport
      (hI₁.hin _ (by unfold IFix sw; omega)) (fun a ha => hI₁.hm a ha) hI₁.hA
  have hNW : NFWithin ({ c with nreg := regB c.nmem stbPre c.nreg } : Config).nmem
      (c₀.nreg (sw 3)) (c₀.nreg ALLOC) N₁ :=
    E.hNW₁.transport (fun a ha => hI₁.hm a ha)
  refine IRS.seq (bLoop_irs hI₁ E.hK hctx20 hP hNF hNW (hI₁.hin _ (by unfold IFix sw; omega))
    hI₁.hA (by simp only; rw [eA1]; omega)) ?_
  rintro c₂ hI₂ hA₂ hA₂' hBW
  obtain ⟨w1, w2, -, w4, -, w6, w7, w8, w9⟩ := hBW
  simp only at w1 w6 w7 w8 w9 hA₂ hA₂'
  rw [eA1] at w1 w6 w7 w8 hA₂ hA₂'
  have keep : ∀ j, j < 10000 → ¬ BSet (sw j) →
      c₂.nreg (sw j) = regB c.nmem stbPre c.nreg (sw j) := fun j hj hb =>
    w9 _ (nb j hj) hb (by unfold ALLOC sw; omega)
  have hs2 : SymPtIn c₂ sO s := by
    refine symPtIn_copy hs ?_ ?_ ?_
    · rw [show sO = sw 3231 from rfl, keep 3231 (by norm_num) (by unfold BSet sw; omega)]
      exact p1
    · rw [show sO + 1 = sw 3232 from rfl, keep 3232 (by norm_num) (by unfold BSet sw; omega)]
      exact p2
    · rw [show sO + 2 = sw 3233 from rfl, keep 3233 (by norm_num) (by unfold BSet sw; omega)]
      exact p3
  have d2 : c₂.nreg qD = c.nreg brOD := by
    rw [show qD = sw 3212 from rfl, keep 3212 (by norm_num) (by unfold BSet sw; omega)]
    exact p4
  have a2 : c₂.nreg accA = 0 := by
    rw [show accA = sw 2000 from rfl, keep 2000 (by norm_num) (by unfold BSet sw; omega)]
    exact p5
  have hacc : AccOK P accA (fun _ => J.left) J.left.radius (s.eval (Qof P))
      (dirOf (c₂.nreg qD)) ∅ c₂ := accOK_init _ _ _ _ _ a2
  have hK2 := E.hK.fix hI₂
  obtain ⟨md1, md2, md3, md4⟩ := E.md hI₂
  obtain ⟨-, -, -, ⟨H, hCD, hreg⟩, -, -⟩ := E.ctx1' hI₂
  have hmd : MdFacts P c₂ (c₂.nreg MD₁) H J.left := ⟨md3, by rw [← md4]; exact hCD, md2, md1⟩
  have hzD : s.eval (Qof P) ∈ J.left.dom := mem_dom_of J.left hzt hz1 hz2 hzC
  have hN1 : c₂.nreg SweepIo.bN = N₁.arcs.length := w4
  have harcs : ∀ j, j < c₂.nreg SweepIo.bN →
      ShotList.PieceOK (chainModel J.left) (Qof P) P.n (ShotList.arcAt c₂.nmem (c₂.nreg SweepIo.bBase) j) ∧
      (chainModel J.left).arcWt
        ((chainModel J.left).key (Qof P) (ShotList.arcAt c₂.nmem (c₂.nreg SweepIo.bBase) j).1)
        ((chainModel J.left).key (Qof P) (ShotList.arcAt c₂.nmem (c₂.nreg SweepIo.bBase) j).2) ≤
        c₀.nreg (sw 5) := by
    intro j hj
    rw [hN1] at hj
    rw [w1, w7 j hj]
    exact nArc_piece hP hNF E.hsg₁ hj
  have hss := symShot_irs (C := J.left) (H := H) (md := MD₁) (base := SweepIo.bBase)
    (cnt := SweepIo.bN) (dsc := CD₁) (tg := K0) (Mod := fun _ => J.left) (R₀ := J.left.radius)
    (L := ∅) (s := s) (z := s.eval (Qof P)) E.hsh E.hBs E.hXl hI₂ E.hK E.hG E.hWh E.hX E.hcap E.hOk₁
    hmd hreg (E.ctx1' hI₂) harcs (by rw [w1, hN1, w6]) hs2 hsl rfl hzD hz1 hz2 hzt
    hacc (by rw [hK2.1]; omega) rfl rfl
    ⟨sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num),
      sregOK_sw (by norm_num) (by norm_num) (by norm_num)⟩
    (by rw [hN1]; omega)
  rw [hN1] at hss
  refine IRS.seq (K₁ := symShotK (F (c₀.nreg (sw 5))) N₁.arcs.length) (K₂ := 12) hss ?_
  rintro c₃ hI₃ hA₃ hA₃' ⟨L', hacc', hL', hcomp, k3, hA3, hm3⟩
  rw [d2] at hacc' hL' hcomp
  refine (IRS.block stbPost hI₃ (stbPost_ok _ _)).mono (by simp [stbPost]) ?_
  rintro c' rfl
  obtain ⟨qv, q0, q1, q2, q3, qo⟩ := stbPost_val c₃.nmem c₃.nreg
  unfold BruteOut
  simp only
  set σ := dirOf (c.nreg brOD) with hσ
  set z := s.eval (Qof P) with hzd
  -- the exit point lies on the arcs
  have hexit : FreeAt J.left z σ → rayPt z σ (J.left.hitParam z σ) ∈
      ShotList.loSet (chainModel J.left) (Qof P) c₂.nmem (c₂.nreg SweepIo.bBase) N₁.arcs.length [] := by
    intro hf
    obtain ⟨p, t, hp, ht0, ht1, ⟨j, hj, hin⟩, hpt⟩ :=
      exit_in_arcs J.left hP hNF (Q := Qof P) (SweepPrim.dirOf_cases _) hzt hf
    refine ⟨p, t, hp, ht0, ht1, ⟨j, hj, ?_⟩, fun g hg => absurd hg
      (List.not_mem_nil), hpt.symm⟩
    rw [w1, w7 j hj]
    obtain ⟨⟨hps, -, -⟩, ⟨hpe, -, -⟩⟩ := arc_end_facts hP hNF hj
    unfold nArc
    rw [(Restore.normOf_facts hps).2.2.2.1, (Restore.normOf_facts hpe).2.2.2.1]
    exact hin
  have hmem : FreeAt J.left z σ → J.left.hitParam z σ ∈ L' := fun hf => hcomp hf (hexit hf)
  obtain ⟨f1, f0, fs⟩ := hacc'
  have hA3' : regB c₃.nmem stbPost c₃.nreg ALLOC = c₃.nreg ALLOC :=
    qo _ (by unfold StbPostW ALLOC brF sw; omega)
  refine ⟨by rw [q0]; exact f1, fun h1 => ?_, fun hf => ?_, fun a ha => ?_, ?_, ?_⟩
  · rw [q0] at h1
    obtain ⟨τ, hτ, hmin, -, hpp, he, hpos, hrec⟩ := fs h1
    rcases hL' with rfl | ⟨τ₀, rfl, hτ0, hon⟩
    · exact absurd hτ (Set.notMem_empty _)
    · have eτ : τ = τ₀ := by simpa using hτ
      subst eτ
      refine ⟨τ, hτ0, hon, by rw [q1]; exact he, by rw [q1, q2]; exact hpp,
        by rw [q1, q2]; exact hpos, ?_, fun hf => ?_⟩
      · refine absRec_transport hrec ?_ ?_ ?_ ?_
        · have := q3 0 (by norm_num); simpa using this
        · have := q3 1 (by norm_num); rw [show brF + 3 + 1 = brF + 3 + 1 from rfl] at this
          rw [show accA + 4 + 1 = accA + 4 + 1 from rfl]; omega
        · have := q3 2 (by norm_num); omega
        · have := q3 3 (by norm_num); omega
      · have := hmem hf
        simp only [Set.mem_insert_iff, Set.mem_empty_iff_false, or_false] at this
        exact this.symm
  · rw [q0]
    have hne : L' ≠ ∅ := fun h => by rw [h] at hmem; exact Set.notMem_empty _ (hmem hf)
    by_contra hc
    exact hne (f0 (by omega))
  · rw [hm3 a (by omega), w8 a (by rw [← eA1] at hA₁; omega)]
  · rw [hA3']; omega
  · intro r hr hb hra
    unfold BrR at hb
    by_cases hp : StbPostW r
    · have hr4 : 244001 ≤ r ∧ r ≤ 244005 := by
        unfold StbPostW brF at hp; unfold sw at hp hb; omega
      obtain ⟨i, hi, rfl⟩ : ∃ i, i < 5 ∧ r = sw 4001 + i :=
        ⟨r - 244001, by omega, by unfold sw; omega⟩
      have esv : stbSv + i = sw (3990 + i) := by unfold stbSv sw; omega
      rw [qv i hi, k3 _ (by rw [esv]; exact nb (3990 + i) (by omega))
        (by unfold RS stbSv sw; omega) (by unfold accA stbSv sw; omega)
        (by unfold ALLOC stbSv sw; omega)]
      rw [esv, keep (3990 + i) (by omega) (by unfold BSet sw; omega), ← esv]
      exact pv i hi
    · have hb' := hb
      unfold sw at hb'
      have e1 : ¬ (RS ≤ r ∧ r < RS + 300) := by unfold RS; omega
      have e2 : r < accA ∨ accA + 12 < r := by unfold accA sw; omega
      have e3 : ¬ BSet r := by unfold BSet; unfold StbPostW brF at hp; unfold sw at hb hp ⊢; omega
      rw [qo r hp, k3 r hr e1 e2 hra, w9 r hr e3 hra]
      exact po r (by unfold StbPreW qD accA; unfold sw at hb ⊢; omega)

end

end SweepEv

end Chazelle.Core
