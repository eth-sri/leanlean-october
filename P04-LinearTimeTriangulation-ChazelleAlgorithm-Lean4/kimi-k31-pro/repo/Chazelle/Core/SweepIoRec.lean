module

public import Chazelle.Core.SweepIoQPos
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

/-!
# The sweep RAM (WP-D), answers: the flag and the record of an answer

For a query point `z` with a position `(zE, qH)` in the model `M` of `C = J.whole` and the
direction code `qD`:

* `flagS`: `arrivalPos` at `z` for the direction; the flag is `1` iff the direction is free for
  `C` at `z` (`arrival_of_freeC`, `freeAt_of_leave`), and then the position `(zP, zPh)` has the
  ray in its left sector;
* `recS`: for the first hit `w = rayPt z σ T` of `C` with a position `(yE, yH)` in `M`,
  `arrivalPos` at `w` for the reversed direction, and the record `(lp, rp)` of the chord seen
  (`Sweep.recordData_of_arrival`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Mathematics -/

/-- **A free direction at a point of a chain or of a vertical side of the box has a departure
position** in the walk of the chain model. -/
theorem arrival_of_freeC (C : Chain) (hPC : C.P.Simple) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ C.set ∨ (|z.1| = C.radius ∧ |z.2| < C.radius))
    (hf : FreeAt C z σ) : ∃ p t, Sweep.Arrival (chainModel C).W z (-σ) p t := by
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hf
  have hu0 : (0 : ℝ) < u := hu
  set T := u / 2
  have hT : 0 < T := by positivity
  have hσ0 : σ ≠ 0 := by rcases hσ with h | h <;> rw [h] <;> norm_num
  have hee : z ≠ rayPt z σ T := by
    intro h
    have h' := congrArg Prod.fst h
    simp only [rayPt] at h'
    have hm0 : σ * T = 0 := by linarith
    rcases mul_eq_zero.1 hm0 with h1 | h1
    · exact hσ0 h1
    · linarith
  have hopen : ∀ s ∈ Set.Ioo (0 : ℝ) 1, Geometry.lerp z (rayPt z σ T) s ∈ C.dom := by
    intro s hs
    rw [show Geometry.lerp z (rayPt z σ T) s = rayPt z σ (s * T) by
      apply Geometry.point_ext <;> simp [Geometry.lerp, rayPt]; ring]
    have hTu : T = u / 2 := rfl
    exact hsub ⟨mul_pos hs.1 hT, by have := hs.2; rwnl [hTu]⟩
  obtain ⟨p, t, hp, ht0, ht1, hpt, hl⟩ :=
    C.sideSees_chordEnd hPC C.sideBeta hee (by simp [rayPt]) hopen hz
  have hpt' : sidePt (chainModel C).W p t = z := hpt
  have hl' : sideLeft (chainModel C).W p t (rayPt z σ T) := hl
  refine ⟨p, t, hp, ht0, ht1, hpt', ?_⟩
  rw [neg_neg]
  have h1 : sideLeft (chainModel C).W p t (rayPt (sidePt (chainModel C).W p t) σ T) := by
    rwx [hpt']
  have := (Sweep.sideLeft_rayPt_iff _ p t σ hT one_pos).1 h1
  rwa [hpt'] at this

/-- **The flag from `arrivalPos`**: free iff an arrival position exists. -/
theorem freeAt_iff_arr (C : Chain) (hPC : C.P.Simple) {z : Point} {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hz : z ∈ C.set ∨ (|z.1| = C.radius ∧ |z.2| < C.radius)) :
    FreeAt C z σ ↔ ∃ p t, Sweep.Arrival (chainModel C).W z (-σ) p t := by
  constructor
  · exact arrival_of_freeC C hPC hσ hz
  · rintro ⟨p, t, hp, ht0, ht1, hpt, hl⟩
    rw [neg_neg] at hl
    exact Sweep.freeAt_of_leave C hPC hσ hp ht0 ht1 hpt hl

/-! ## Registers of an answer -/

def qE : ℕ := sw 3210
def qH : ℕ := sw 3211
def qD : ℕ := sw 3212
def zE : ℕ := sw 3213
def zF : ℕ := sw 3214
def zP : ℕ := sw 3215
def zPh : ℕ := sw 3216
def yE : ℕ := sw 3217
def yH : ℕ := sw 3218
def wF : ℕ := sw 3219
def wP : ℕ := sw 3220
def wPh : ℕ := sw 3221
def rL : ℕ := sw 3222
def rR : ℕ := sw 3223
def rho : ℕ := sw 3224

/-! ## The flag -/

/-- `arrivalPos` at the query point (position `(zE, qH)` of `M`, direction code `qD`). -/
def flagS : Stmt := callArr (sw 2) zE qH qD zF

/-- **The flag.** -/
theorem flagS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hP : J.P.Simple)
    (hctx : ChainCtx P W c (sw 2) J.whole) {z : Point}
    (he : c.nreg zE < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg zE, c.nreg qH⟩)
    (hz : (chainModel J.whole).pos (Qof P) ⟨c.nreg zE, c.nreg qH⟩ = z)
    (hzR : |z.2| < J.whole.radius)
    (hzC : z ∈ J.whole.set ∨ (|z.1| = J.whole.radius ∧ |z.2| < J.whole.radius))
    (hroom : c.nreg ALLOC + 35007 ≤ W) :
    IRS P W c₀ flagS c 35007 (fun c' =>
      c'.nreg zF ≤ 1 ∧ (c'.nreg zF = 1 ↔ FreeAt J.whole z (dirOf (c.nreg qD))) ∧
      (c'.nreg zF = 1 → c'.nreg zP < (chainModel J.whole).W.n ∧
        ProperPos (chainModel J.whole) (Qof P) P.n ⟨c'.nreg zP, c'.nreg zPh⟩ ∧
        Sweep.Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c'.nreg zP)
          ((chainModel J.whole).param (Qof P) ⟨c'.nreg zP, c'.nreg zPh⟩)) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ zF → r ≠ zP → r ≠ zPh → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  have hσ := dirOf_cases (c.nreg qD)
  refine (callArr_irs hI hctx ⟨by ufn sw, by ufn sw, by ufn zE sw,
    by ufn zE sw, by ufn qH sw, by ufn qH sw,
    by ufn qD sw, by ufn qD sw⟩ ⟨by ufn zF sw,
    by ufn zF sw⟩ he hpp (by rwx [hz]) hroom).mono le_rfl ?_
  rintro c' ⟨⟨hf1, hf2, hf3⟩, hfr, hA, hm⟩
  rw [hz] at hf2 hf3
  have e1 : zF + 1 = zP := rfl
  have e2 : zF + 2 = zPh := rfl
  rw [e1, e2] at hf2 hfr
  refine ⟨hf1, ?_, hf2, hfr, hA, hm⟩
  rw [freeAt_iff_arr J.whole hP hσ hzC]
  constructor
  · intro h
    obtain ⟨-, -, hA'⟩ := hf2 h
    exact ⟨_, _, hA'⟩
  · rintro ⟨p, t, hA'⟩
    by_contra hne
    exact hf3 hne p t hA'

/-! ## The record -/

/-- `arrivalPos` at the hit point (position `(yE, yH)`, reversed direction), and the record. -/
def recS : Stmt :=
  .seq (block [.constN rho 1]) (.seq (eqT qD K1 (.instr (.constN rho 0)))
    (.seq (callArr (sw 2) yE yH rho wF)
      (.seq (block [.copyN rL wP, .copyN rR zP]) (eqT qD K1 (block [.copyN rL zP, .copyN rR wP])))))

/-- The cost of the record. -/
def recK : ℕ := 35030

/-- **The record of the answer.** -/
theorem recS_irs {J : Merge.Junction} (hI : IInv W c₀ c) (hK : Consts c₀) (hP : J.P.Simple)
    (hctx : ChainCtx P W c (sw 2) J.whole) {z : Point} {T : ℝ}
    (hzt : z.2 ≤ J.whole.top.2) (hfree : FreeAt J.whole z (dirOf (c.nreg qD)))
    (hT : J.whole.hitParam z (dirOf (c.nreg qD)) = T)
    (hAz : Sweep.Arrival (chainModel J.whole).W z (-dirOf (c.nreg qD)) (c.nreg zP)
      ((chainModel J.whole).param (Qof P) ⟨c.nreg zP, c.nreg zPh⟩))
    (he : c.nreg yE < (chainModel J.whole).W.n)
    (hpp : ProperPos (chainModel J.whole) (Qof P) P.n ⟨c.nreg yE, c.nreg yH⟩)
    (hw : (chainModel J.whole).pos (Qof P) ⟨c.nreg yE, c.nreg yH⟩ = rayPt z (dirOf (c.nreg qD)) T)
    (hzR : |z.2| < J.whole.radius) {h : ℕ} (hh : ((Qof P).vtx h).2 = z.2)
    (hroom : c.nreg ALLOC + recK ≤ W) :
    IRS P W c₀ recS c recK (fun c' =>
      Sweep.RecordData J (Qof P) z (dirOf (c.nreg qD)) T h (c.nreg zP) (c'.nreg wP) (c'.nreg rL)
        (c'.nreg rR) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ rL → r ≠ rR →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)) := by
  set σ := dirOf (c.nreg qD) with hσd
  have hσ : σ = 1 ∨ σ = -1 := dirOf_cases _
  have hk1 : c.nreg K1 = 1 := (hK.fix hI).2.1
  obtain ⟨hT0, -, -⟩ := Merge.hit_of_freeAt J.whole hzt hσ hfree
  rw [hT] at hT0
  have hgen : Sweep.Genuine J.whole z σ T :=
    (Sweep.genuine_iff J.whole hzt hσ).2 ⟨hfree, hT⟩
  have hsr : ∀ r, 240700 ≤ r → r < 250000 → IScr r := fun r h1 h2 => iscr_sw h1 h2
  have hW1 : 1 ≤ W := by have := hctx.2.1; ufo hostWords at this
  have hrho : IScr rho := hsr _ (by ufn rho sw) (by ufn rho sw)
  have hq1 : σ = 1 ↔ c.nreg qD = 1 := by
    rw [hσd]; unfold dirOf; split_ifs with h <;> norm_num [h]
  -- `rho := flip qD`
  refine (IRS.seq (K₂ := recK - 1) (IRS.block [.constN rho 1] hI ⟨⟨hrho, hW1⟩, trivial⟩) ?_).mono
    (by simp [recK]) (fun _ => id)
  rintro c₁ hI₁ - - hc1
  have r1 : c₁.nreg rho = 1 := by rw [hc1]; show upd c.nreg rho 1 rho = 1; rw [upd_same]
  have k1 : ∀ r, r ≠ rho → c₁.nreg r = c.nreg r := fun r hr => by
    rw [hc1]; show upd c.nreg rho 1 r = _; rw [upd_other _ _ _ hr]
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have hA1 : c₁.nreg ALLOC = c.nreg ALLOC := k1 _ (by ufo rho ALLOC sw)
  have q1 : c₁.nreg qD = c.nreg qD := k1 _ (by ufo rho qD sw)
  have kk1 : c₁.nreg K1 = 1 := by rw [k1 _ (by ufo rho K1 sw), hk1]
  have st2 : IRS P W c₀ (eqT qD K1 (.instr (.constN rho 0))) c₁ 5 (fun c' =>
      c'.nreg rho = (if c.nreg qD = 1 then 0 else 1) ∧ (∀ r, r ≠ rho → c'.nreg r = c₁.nreg r) ∧
      c'.nmem = c₁.nmem) := by
    unfold eqT
    by_cases h1 : c₁.nreg qD < c₁.nreg K1
    · refine (IRS.ifT h1 (IRS.skip (K := 0) hI₁ ?_)).mono (by norm_num) (fun _ => id)
      rw [q1, kk1] at h1
      exact ⟨by rw [r1, ite_eq_right (by omega)], fun _ _ => rfl, rfl⟩
    refine IRS.mono (K := 5) (IRS.ifF h1 ?_) (by norm_num) (fun _ => id)
    by_cases h2 : c₁.nreg K1 < c₁.nreg qD
    · refine (IRS.ifT h2 (IRS.skip (K := 0) hI₁ ?_)).mono (by norm_num) (fun _ => id)
      rw [q1, kk1] at h2
      exact ⟨by rw [r1, ite_eq_right (by omega)], fun _ _ => rfl, rfl⟩
    refine (IRS.ifF h2 (IRS.instr1 (i := .constN rho 0) hI₁ ⟨hrho, by omega⟩)).mono (by norm_num) ?_
    rintro c' rfl
    rw [q1, kk1] at h1 h2
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · show upd c₁.nreg rho 0 rho = _; rw [upd_same, ite_eq_left (by omega)]
    · show upd c₁.nreg rho 0 r = _; rw [upd_other _ _ _ hr]
  refine (IRS.seq (K₂ := 35024) st2 ?_).mono (by simp [recK]) (fun _ => id)
  rintro c₂ hI₂ hA₂ - ⟨r2, k2, hm2⟩
  have ff : ∀ r, r ≠ rho → c₂.nreg r = c.nreg r := fun r hr => by rw [k2 r hr, k1 r hr]
  have hA2 : c₂.nreg ALLOC = c.nreg ALLOC := ff _ (by ufo rho ALLOC sw)
  have y2 : c₂.nreg yE = c.nreg yE := ff _ (by ufo rho yE sw)
  have h2' : c₂.nreg yH = c.nreg yH := ff _ (by ufo rho yH sw)
  have hctx₂ : ChainCtx P W c₂ (sw 2) J.whole := hctx.transport
    (ff _ (by ufo rho sw)) (fun a _ => by rw [hm2, hm1]) (by rw [hA2])
  have hwR : |((chainModel J.whole).pos (Qof P) ⟨c₂.nreg yE, c₂.nreg yH⟩).2| < J.whole.radius := by
    rw [y2, h2', hw]; simpa [rayPt] using hzR
  refine (IRS.seq (K₂ := 17) (callArr_irs hI₂ hctx₂ ⟨by ufn sw, by ufn sw,
    by ufn yE sw, by ufn yE sw, by ufn yH sw,
    by ufn yH sw, by ufn rho sw, by ufn rho sw⟩
    ⟨by ufn wF sw, by ufn wF sw⟩ (by rwx [y2])
    (by rwx [y2, h2']) hwR (by ruo [hA2] recK at hroom)) ?_).mono le_rfl
    (fun _ => id)
  rintro c₃ hI₃ hA₃ hA₃' ⟨⟨hf1, hf2, hf3⟩, fr3, hA3, hm3⟩
  rw [y2, h2', hw, r2] at hf2 hf3
  have hflip : -dirOf (if c.nreg qD = 1 then 0 else 1) = σ := neg_dirOf_flip _
  rw [hflip] at hf2 hf3
  have e1 : wF + 1 = wP := rfl
  have e2 : wF + 2 = wPh := rfl
  rw [e1, e2] at hf2 fr3
  have hf : c₃.nreg wF = 1 := by
    by_contra hne
    obtain ⟨p, t, hA'⟩ := Sweep.arrival_exists J.whole hP hzt hσ hgen
    exact hf3 hne p t hA'
  obtain ⟨-, -, hAw⟩ := hf2 hf
  have hRD := Sweep.recordData_of_arrival J (Qof P) hσ hT0 hh hAz hAw
  have k3 : ∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ ALLOC →
      c₃.nreg r = c.nreg r := fun r h0 h1 h2 h3 h4 h5 => by rw [fr3 r h0 h2 h3 h4 h5, ff r h1]
  have zp3 : c₃.nreg zP = c.nreg zP := k3 _ (not_oracle_sw (by ufn zP sw)
    (by ufn zP sw)) (by ufo zP rho sw) (by ufo zP wF sw)
    (by ufo zP wP sw) (by ufo zP wPh sw) (by ufo zP ALLOC sw)
  have q3 : c₃.nreg qD = c.nreg qD := k3 _ (not_oracle_sw (by ufn qD sw)
    (by ufn qD sw)) (by ufo qD rho sw) (by ufo qD wF sw)
    (by ufo qD wP sw) (by ufo qD wPh sw) (by ufo qD ALLOC sw)
  have kk3 : c₃.nreg K1 = 1 := (hK.fix hI₃).2.1
  -- the default order, then the swap for `σ = 1`
  refine (IRS.seq (K₂ := 15) (IRS.block [.copyN rL wP, .copyN rR zP] hI₃
    ⟨hsr _ (by ufn rL sw) (by ufn rL sw),
      hsr _ (by ufn rR sw) (by ufn rR sw), trivial⟩) ?_).mono
    (by simp) (fun _ => id)
  rintro c₄ hI₄ - - hc4
  have v4L : c₄.nreg rL = c₃.nreg wP := by
    rw [hc4]; show regB c₃.nmem [.copyN rL wP, .copyN rR zP] c₃.nreg rL = _
    simp only [regB, regI]
    rw [upd_other _ _ _ (by ufo rL rR sw), upd_same]
  have v4R : c₄.nreg rR = c.nreg zP := by
    rw [hc4]; show regB c₃.nmem [.copyN rL wP, .copyN rR zP] c₃.nreg rR = _
    simp only [regB, regI]
    rw [upd_same, upd_other _ _ _ (by ufo zP rL sw), zp3]
  have k4 : ∀ r, r ≠ rL → r ≠ rR → c₄.nreg r = c₃.nreg r := fun r h1 h2 => by
    rw [hc4]; show regB c₃.nmem [.copyN rL wP, .copyN rR zP] c₃.nreg r = _
    simp only [regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have hm4 : c₄.nmem = c₃.nmem := by rw [hc4]
  have q4 : c₄.nreg qD = c.nreg qD := by rw [k4 _ (by ufo qD rL sw)
    (by ufo qD rR sw), q3]
  have kk4 : c₄.nreg K1 = 1 := (hK.fix hI₄).2.1
  have w4 : c₄.nreg wP = c₃.nreg wP := k4 _ (by ufo wP rL sw) (by ufo wP rR sw)
  have zp4 : c₄.nreg zP = c.nreg zP := by
    rw [k4 _ (by ufo zP rL sw) (by ufo zP rR sw), zp3]
  have hfin : ∀ c' : Config, c'.nreg rL = (if σ = 1 then c.nreg zP else c₃.nreg wP) →
      c'.nreg rR = (if σ = 1 then c₃.nreg wP else c.nreg zP) → c'.nreg wP = c₃.nreg wP →
      (∀ r, r ≠ rL → r ≠ rR → c'.nreg r = c₄.nreg r) → c'.nmem = c₄.nmem →
      c'.nreg ALLOC = c₄.nreg ALLOC →
      Sweep.RecordData J (Qof P) z σ T h (c.nreg zP) (c'.nreg wP) (c'.nreg rL) (c'.nreg rR) ∧
      (∀ r, bandOf r ∉ oracleBands → r ≠ rho → r ≠ wF → r ≠ wP → r ≠ wPh → r ≠ rL → r ≠ rR →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) := by
    intro c' hl hr hwp hk hm hA
    refine ⟨by rwx [hl, hr, hwp], fun r h0 h1 h2 h3 h4 h5 h6 h7 => ?_, ?_, fun a ha => ?_⟩
    · rw [hk r h5 h6, k4 r h5 h6]; exact k3 r h0 h1 h2 h3 h4 h7
    · rw [hA, k4 _ (by ufo rL ALLOC sw) (by ufo rR ALLOC sw)]
      rwx [← hA2]
    · rw [hm, hm4, hm3 a (by omega), hm2, hm1]
  have hA4 : c₄.nreg ALLOC = c₃.nreg ALLOC := k4 _ (by ufo rL ALLOC sw)
    (by ufo rR ALLOC sw)
  unfold eqT
  by_cases h1 : c₄.nreg qD < c₄.nreg K1
  · refine (IRS.ifT h1 (IRS.skip (K := 0) hI₄ ?_)).mono (by norm_num) (fun _ => id)
    rw [q4, kk4] at h1
    have hs : ¬ σ = 1 := fun h => by have := hq1.1 h; omega
    exact hfin c₄ (by rw [v4L, ite_eq_right hs]) (by rw [v4R, ite_eq_right hs]) w4 (fun _ _ _ => rfl) rfl rfl
  refine IRS.mono (K := 15) (IRS.ifF h1 ?_) (by norm_num) (fun _ => id)
  by_cases h2 : c₄.nreg K1 < c₄.nreg qD
  · refine (IRS.ifT h2 (IRS.skip (K := 0) hI₄ ?_)).mono (by norm_num) (fun _ => id)
    rw [q4, kk4] at h2
    have hs : ¬ σ = 1 := fun h => by have := hq1.1 h; omega
    exact hfin c₄ (by rw [v4L, ite_eq_right hs]) (by rw [v4R, ite_eq_right hs]) w4 (fun _ _ _ => rfl) rfl rfl
  rw [q4, kk4] at h1 h2
  have hs : σ = 1 := hq1.2 (by omega)
  refine (IRS.ifF (show ¬ c₄.nreg K1 < c₄.nreg qD by rwo [q4, kk4])
    (IRS.block [.copyN rL zP, .copyN rR wP] hI₄
      ⟨hsr _ (by ufn rL sw) (by ufn rL sw),
        hsr _ (by ufn rR sw) (by ufn rR sw), trivial⟩)).mono
    (by simp) ?_
  rintro c' rfl
  refine hfin _ ?_ ?_ ?_ (fun r h1 h2 => ?_) rfl ?_
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg rL = _
    simp only [regB, regI]
    rw [upd_other _ _ _ (by ufo rL rR sw), upd_same, zp4, ite_eq_left hs]
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg rR = _
    simp only [regB, regI]
    rw [upd_same, upd_other _ _ _ (by ufo wP rL sw), w4, ite_eq_left hs]
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg wP = _
    simp only [regB, regI]
    rw [upd_other _ _ _ (by ufo wP rR sw), upd_other _ _ _ (by ufo wP rL sw), w4]
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg r = _
    simp only [regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  · show regB c₄.nmem [.copyN rL zP, .copyN rR wP] c₄.nreg ALLOC = _
    simp only [regB, regI]
    rw [upd_other _ _ _ (by ufo rR ALLOC sw), upd_other _ _ _ (by ufo rL ALLOC sw)]

end

end SweepIo

end Chazelle.Core
