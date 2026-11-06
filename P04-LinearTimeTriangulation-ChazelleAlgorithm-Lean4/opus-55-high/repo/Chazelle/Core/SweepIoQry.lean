module

public import Chazelle.MacT
public import Chazelle.Core.SweepIoCand1B
public import Chazelle.Core.SweepIoLoop
public import Chazelle.Core.SweepIoBruteLoop
public import Chazelle.Existence.Diagonal
public import Chazelle.Core.TopIdx
public import Chazelle.Final.Wedge
public import Chazelle.Core.FactsAttach
public import Chazelle.Mountain.PieceSteps

section
set_option hygiene false
local macro "zqber" : tactic => `(tactic| (zuogr; unfold mem4'; simp))
local macro "zqbes" : tactic => `(tactic| (zuogr; unfold mem4'
                                           zvmwf
                                           zunjd))
local macro "zqbet" : tactic => `(tactic| rcases hcls with (h | h) | ⟨-, h⟩ | ⟨h, -⟩ <;> simp only at h <;> omega)
local macro "zqbeu" : tactic => `(tactic| (exact ⟨a1, ⟨by zungr; exact hpp.1, by zungr; exact hpp.2.1, hpp.2.2⟩, by_simp_all⟩))
local macro "zqbev" : tactic => `(tactic| (have t1 := tpos_lt J.left J.m₁
                                           have t2 := tpos_lt J.whole ztbv))
set_option hygiene true

/-!
# The sweep RAM (WP-D), answers: the per-query program

`qry_run`: the per-query program `qryP c0 c1` from the loop registers: read the query, convert
its position to the walk of `C` (`convQ_sem`), the flag (`flagS`); for a direction that is not
free the zero record; otherwise the bits, the cleared accumulator, the candidate step of the side
(an `IRS` contract `hc` with the cost `Kc`), the winner in the walk of `C` (`winVal_sem`), the
record (`recS`) and the result `(1, h, lp, rp)` in the slot (`QryPost`).
-/
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Merge (FreeAt)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- Register (in)equalities of the pipeline. -/
macro "rne" : tactic => `(tactic| (simp only [qE, qH, qD, qJ, zE, zF, zP, zPh, yE, yH, wF, wP,
  wPh, rL, rR, rho, bL, bR, cX, cT, cDd, ALLOC, accA, tAq, tH, sZ, sTq, kO, pJ, pA, pR, sSide, K0,
  K1, K2, K3, K4, K5, K6, sO, sw] at *; omega))

/-- The stage-0 registers at a configuration of the answer phase. -/
theorem st0_reg (hI : IInv W c₀ c) {j : ℕ} (hj : j < 700) : c.nreg ztgc = c₀.nreg ztgc :=
  hI.hin _ ztze
variable {J : Merge.Junction} {H : Host}
set_option maxHeartbeats 4000000 in
/-- **The query position in the walk of `C`.** -/
theorem convQ_sem (hI : IInv W c₀ c) (hK : Consts c₀)
    (hst : SweepEv.St0S P c₀ H J) (hP : J.P.Simple) (hWm : 2 * J.whole.m + 7 ≤ W) {i : ℕ}
    (hi : i ≤ 1) (hs : c.nreg sSide = i)
    (hcls : PosClass ztgi zta zthz) :
    IRS P W c₀ convQ c 24 (fun c' => c'.nreg zE < (chainModel J.whole).W.n ∧
      (chainModel J.whole).param zta ztrbc =
        (chainModel ztgi).param zta zthz ∧
      (chainModel J.whole).pos zta ztrbc =
        (chainModel ztgi).pos zta zthz ∧
      (∀ r, ¬ CvSet zE r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  zuhx
  zucww
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := id hst
  have rr : zthpu := fun x h1 h2 =>
    hI.hin _ ztwo
  have r : ∀ j, j < 700 → c.nreg _ = c₀.nreg _ := fun j hj => st0_reg hI hj
  have hm1 : ztpkj := by_simp_all
  have hm2 : ztmti := by_simp_all
  have hpe : qE ≠ cX ∧ qE ≠ cT ∧ qE ≠ cDd := by_decide
  have hpo : IScr zE ∧ zE ≠ cX ∧ zE ≠ cT ∧ zE ≠ cDd :=
    ⟨iscr_sw by_decide by_decide, by_decide,
      by decide, by_decide⟩
  have v35 : c.nreg zthg = 2 * J.whole.m + 7 := by_simp_all
  have hnC := cm_n
  rcases sideChain_cases J hi with ⟨rfl, hC⟩ | ⟨rfl, hC⟩
  · zujie
    zukgb
    have hqE : c.nreg qE < 2 * J.left.m + 6 + 1 := by
      zqbet
    have v33 : c.nreg ztna = 2 * J.left.m + 7 := by_simp_all
    have v45 : ztxbs := by
      rw [r 45 by_norm_num, show (45 : ℕ) = 45 + 0 from rfl, h45 0 by_norm_num]; rfl
    have v46 : ztxps := by
      rw [show sw 45 + 1 = sw 46 from rfl, r 46 by_norm_num, show (46 : ℕ) = 45 + 1 from rfl,
        h45 1 by_norm_num]; rfl
    zqbev
    refine (IRS.ifT ht (convS_irs ztbt ztp hpe hpo hI hK by_omega
      by_omega by_omega by_omega
      by_omega)).mono by_norm_num ?_
    zuhjk
    zuetp
    simp only [rr ztbca by_decide by_decide,
      rr ztbwh by_decide by_decide,
      rr ztdaj by_decide by_decide,
      rr ztdak by_decide by_decide,
      rr ztna by_decide by_decide,
      rr zthg by_decide by_decide] at h1
    grind
  · zujie
    zukga
    have hqE : c.nreg qE < 2 * J.right.m + 6 + 1 := by
      zqbet
    have v34 : ztyug := by_simp_all
    have v40 : ztxbt := by
      rw [r 40 by_norm_num, show (40 : ℕ) = 40 + 0 from rfl, h40 0 by_norm_num]; rfl
    have v41 : ztxpr := by
      rw [show sw 40 + 1 = sw 41 from rfl, r 41 by_norm_num, show (41 : ℕ) = 40 + 1 from rfl,
        h40 1 by_norm_num]; rfl
    zufht

    refine (IRS.ifF ht (convS_irs ztp ztbt hpe hpo hI hK by_omega
      by_omega by_omega by_omega
      by_omega)).mono by_norm_num ?_
    zuhjk
    zuetq
    simp only [rr ztfg by_decide by_decide,
      rr ztbwf by_decide by_decide,
      rr ztdah by_decide by_decide,
      rr ztdai by_decide by_decide,
      rr zthy by_decide by_decide,
      rr zthg by_decide by_decide] at h1
    grind
set_option maxHeartbeats 4000000 in
/-- **The winner in the walk of `C`.** -/
theorem winVal_sem (hI : IInv W c₀ c)
    (hst : SweepEv.St0S P c₀ H J) (hP : J.P.Simple) {z : Point} {σ T : ℝ}
    (hzR : |z.2| < J.whole.radius)
    (hbL : c.nreg bL = 1 → z.2 ≤ J.left.top.2) (hbR : c.nreg bR = 1 → z.2 ≤ J.right.top.2)
    (hpp : ProperPos (chainModel ztxgg) zta
      P.n ⟨c.nreg ztbef, c.nreg ztcma⟩)
    (he : c.nreg ztbef < (chainModel ztxgg).W.n)
    (hpos : (chainModel ztxgg).pos zta
      ⟨c.nreg ztbef, c.nreg ztcma⟩ = rayPt z σ T) :
    winVal c < (chainModel J.whole).W.n ∧
      ProperPos ztbm zta P.n ztzip ∧
      (chainModel J.whole).pos zta ztzip = rayPt z σ T := by
  have rr : zthpu := fun x h1 h2 =>
    hI.hin _ ztwo
  have hy : ∀ C : Chain, C.P = J.P → |((chainModel C).pos zta
      ⟨c.nreg ztbef, c.nreg ztcma⟩).2| < C.radius → True := by_simp_all
  unfold winVal
  zupi
  · have hM : ModB J ztcpq ztcpr ztzdy = J.left := by
      zujpw
    zuijg
    have hcls : PosClass J.left _ zteyb :=
      posClass_of he hpp.1 hpp.2.1
        (by zunuh;
            omega)
        by_simp_all
    zuetp
    simp only [rr ztbca by_decide by_decide,
      rr ztbwh by_decide by_decide,
      rr ztdaj by_decide by_decide,
      rr ztdak by_decide by_decide,
      rr ztna by_decide by_decide,
      rr zthg by_decide by_decide]
    zqbeu
  · have hM : ModB J ztcpq ztcpr ztzdy = J.right := by
      zujpw
    zuijg
    have hcls : PosClass J.right _ zteyb :=
      posClass_of he hpp.1 hpp.2.1
        (by zunuh;
            omega)
        by_simp_all
    zuetq
    simp only [rr ztfg by_decide by_decide,
      rr ztbwf by_decide by_decide,
      rr ztdah by_decide by_decide,
      rr ztdai by_decide by_decide,
      rr zthy by_decide by_decide,
      rr zthg by_decide by_decide]
    zqbeu
  · have hM : ModB J ztcpq ztcpr ztzdy = J.whole := by
      unfold ModB; grind
    simp_all

/-- The postcondition of a query. -/
def QryPost (J : Merge.Junction) (P : Polygon) (i : ℕ) (L : List zte) (j : ℕ)
    (c c' : Config) : Prop :=
  (∃ r : ℕ × ℕ × ℕ × ℕ, c'.nmem ztqix = r.1 ∧ c'.nmem ztrml = r.2.1 ∧
    c'.nmem ztrmm = r.2.2.1 ∧ c'.nmem ztrmn = r.2.2.2 ∧
    SeesInWhole J zta i ztwzi r) ∧
  ztdws ∧
  ztfyx ∧
  c.nreg ALLOC ≤ c'.nreg ALLOC

/-- A frame: registers outside the oracle bands and outside `S` (other than the allocator)
kept, the allocator not lowered, memory below it kept. -/
def PFr (S : ℕ → Prop) (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth
theorem PFr.trans {S S' : ℕ → Prop} {c₁ c₂ c₃ : Config} (h₁ : PFr S c₁ c₂) (h₂ : PFr S' c₂ c₃)
    (hS : ∀ r, S r → S' r) : PFr S' c₁ c₃ :=
  ⟨fun r h0 h1 h2 => (h₂.1 r h0 h1 h2).trans (h₁.1 r h0 by_grind h2),
    h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a ztkan).trans ztdux⟩

/-- The registers a query writes (besides the slot, the oracle bands and the allocator). -/
def QW (r : ℕ) : Prop := (sw 1000 ≤ r ∧ r < sw 3400) ∨ ztbwg
set_option maxHeartbeats 16000000 in
set_option maxRecDepth 40000 in
/-- **The per-query program.** -/
theorem qry_run {c0 c1 : Stmt} {X : MemCtx} {Ok : Polygon → Model → Prop}
    {Aux : Polygon → Merge.Junction → NF → Config → Prop} {J : Merge.Junction} {H : Host}
    {N₁ N₂ : NF} {E : ℕ} {L : List zte} {i j Kc : ℕ}
    (hB : ABase P W X Ok Aux J H N₁ N₂ E L i c₀) (hI : IInv W c₀ c)
    (hpJ : c.nreg pJ = j) (hj : j < L.length) (hpA : c.nreg pA = c₀.nreg ztfiw + 3 * j)
    (hpR : c.nreg pR = c₀.nreg ztbor + 4 * j) (hslot : c.nreg pR + 4 ≤ c.nreg ALLOC)
    (hc : ∀ c', IInv W c₀ c' → QState P J i ztdvu c' → c'.nreg qJ = j →
      (i = 1 → c'.nreg qJ < 2 * N₂.nChords →
        (c'.nreg qE, c'.nreg qH, c'.nreg qD) = (sweepEndQ N₂.chords).getD ztvgw ztt) →
      c'.nreg accA = 0 → c'.nreg ALLOC + Kc ≤ W →
      IRS P W c₀ (if i = 0 then c0 else c1) c' Kc
        (fun c'' => CandOut P J ztdvu c' c'' ∧ CandFr c' c''))
    (hroom : c.nreg ALLOC + ztsur ≤ W) :
    IRS P W c₀ (qryP c0 c1) c ztsur (QryPost J P i L j c) := by
  have hA := hB.hA
  zudnn
  zuhx
  zuc
  set q := L.getD j ztt with hq_def
  have hqL : q ∈ L := by_grind
  have hqOK := hB.hq q hqL
  have hqht := hB.hht q hqL
  set z := qPt J P i L j with hz_def
  have hzq : (chainModel _).pos _ ztpo = z := rfl
  obtain ⟨hcls, hzR, hzts, hzt, hzC⟩ := query_facts J hqOK
  rw [hzq] at hzR hzts hzt hzC
  zullu
  zumby
  zudni
  obtain ⟨g1, g2, g3⟩ := hB.hLat j hj
  zugmr
  -- 1. read the query
  refine (IRS.seq (K₂ := 87094 + Kc) (loadQ_irs hI hK by_omega) ?_).mono
    by_omega ztb
  rintro c₁ hI₁ hA₁ hA₁' ⟨l1, l2, l3, l4, l5, l6⟩
  have e1 : c₁.nreg qE = q.1 := by
    grind
  have e2 : c₁.nreg qH = q.2.1 := by_grind
  have e3 : c₁.nreg qD = q.2.2 := by_grind
  have e0 : c₁.nreg qJ = j := by_omega
  have hside : ∀ c', IInv W c₀ c' → c'.nreg sSide = i := fun c' h' =>
    (h'.hin _ by_trivial).trans hB.hside
  have hA1 : ztdc := l5 _ by_decide
    by_decide by_decide by_decide
    by_decide
  -- 2. the position in the walk of `C`
  refine (IRS.seq (K₂ := 87070 + Kc) (convQ_sem hI₁ hK hA.hst hA.hP hA.hWm hB.hi by_grind
    by_grind) ?_).mono by_omega (fun _ h => h)
  rintro c₂ hI₂ hA₂ hA₂' ⟨v1, v2, v3, v4, v5⟩
  zvmws at v2 v3
  rw [hzq] at v3
  have k2 : ∀ r, r ≠ zE → r ≠ cX → r ≠ cT → r ≠ cDd → c₂.nreg r = c₁.nreg r := fun r a b d e =>
    v4 r ztqfu
  have e1' : c₂.nreg qE = q.1 := by rw [k2 qE (by rne) (by rne) (by rne) (by rne), e1]
  have e2' : c₂.nreg qH = q.2.1 := by rw [k2 qH (by rne) (by rne) (by rne) (by rne), e2]
  have e3' : c₂.nreg qD = q.2.2 := by rw [k2 qD (by rne) (by rne) (by rne) (by rne), e3]
  have e0' : c₂.nreg qJ = j := by rw [k2 qJ (by rne) (by rne) (by rne) (by rne), e0]
  have hA2 : ztbae := by
    rw [k2 ALLOC (by rne) (by rne) (by rne) (by rne), hA1]
  -- 3. the flag
  obtain ⟨-, hq1, hqn, hp0, hp1, -, -⟩ := hqOK
  have hpp2 : ProperPos ztbm zta P.n ⟨c₂.nreg zE, c₂.nreg qH⟩ := by
    rw [e2']; exact ⟨by_grind, by_grind, by_grind⟩
  refine (IRS.seq (K₂ := 52063 + Kc) (flagS_irs hI₂ hA.hP (hA.ctxW hI₂) v1 hpp2
    by_grind hzR hzC by_omega) ?_).mono by_omega (fun _ h => h)
  rintro c₃ hI₃ hA₃ hA₃' ⟨u1, u2, u3, u4, u5, u6⟩
  rw [e3'] at u2 u3
  have k3 := u4
  have s3 := fun r h1 h2 a b d =>
    k3 r (not_oracle_sw h1 h2) a b d (by rne)
  have hKc3 := hK.fix hI₃
  -- the slot
  have hR3 : c₃.nreg pR = c.nreg pR := by
    rw [s3 pR (by rne) (by rne) (by rne) (by rne) (by rne), k2 pR (by rne) (by rne) (by rne) (by rne),
      l5 pR (by rne) (by rne) (by rne) (by rne) (by rne)]
  have hslotA : c₀.nreg ALLOC ≤ c.nreg pR := by
    rw [hpR, hB.hres]; omega
  -- the frame so far
  have fr3 : PFr QW c c₃ := by
    refine ⟨fun r h0 h1 h2 => ?_, by_omega, fun a ha => ?_⟩
    · have : ¬ (sw 3200 ≤ r ∧ r < sw 3400) := fun h => h1 ztiqb
      rw [k3 r h0 (by rne) (by rne) (by rne) h2, k2 r (by rne) (by rne) (by rne) (by rne),
        l5 r (by rne) (by rne) (by rne) (by rne) (by rne)]
    · rw [u6 a by_omega, v5, l6]
  by_cases hf : c₃.nreg zF < c₃.nreg K1
  · -- not free: the zero record
    have hz0 : ¬ FreeAt J.whole z _ := fun h => by
      have := u2.2 h; rw [hKc3.2.1] at hf; omega
    refine (IRS.ifT hf (store4_irs hI₃ hK (by rne) (by rne) (by rne) by_omega
      by_omega)).mono by_omega ?_
    zuewf
    have k0 := hKc3.1
    rw [hR3, k0] at w1
    refine ⟨⟨ztlt, ?_, ?_, ?_, ?_, seesInWhole_notFree' J _ i q hzq rfl hz0 _
      by_norm_num⟩, fun a ha hout => ?_, fun r h1 h2 => ?_, ?_⟩
    · zqber
    · zqber
    · zqber
    · zqber
    · zqbes
      exact fr3.2.2 a ha
    · rw [w2 r (by rne)]
      exact fr3.1 r ztftm
        (by unfold QW; unfold sw at *; omega) (by rne)
    · rw [w2 ALLOC (by rne)]; grind
  -- free: the candidates
  have hf1 : c₃.nreg zF = 1 := by rw [hKc3.2.1] at hf; omega
  have hfree : FreeAt J.whole z _ := u2.1 hf1
  obtain ⟨a1, a2, a3⟩ := u3 hf1
  have q3E : c₃.nreg qE = q.1 := by rw [s3 qE (by rne) (by rne) (by rne) (by rne) (by rne), e1']
  have q3H : c₃.nreg qH = q.2.1 := by rw [s3 qH (by rne) (by rne) (by rne) (by rne) (by rne), e2']
  have q3D : c₃.nreg qD = q.2.2 := by rw [s3 qD (by rne) (by rne) (by rne) (by rne) (by rne), e3']
  have q3J : c₃.nreg qJ = j := by rw [s3 qJ (by rne) (by rne) (by rne) (by rne) (by rne), e0']
  have q3zE := s3 zE (by rne) (by rne) (by rne) (by rne) (by rne)
  have hvz : ((Qof P).vtx zteut).2 = z.2 := by_grind
  refine (IRS.ifF hf (K := 52061 + Kc) ?_).mono by_omega ztb
  -- 5. the bits
  refine (IRS.seq (K₂ := 35095 + Kc) (bitsQ_irs hI₃ hK hB.hi (hside c₃ hI₃) (hA.ctxL hI₃)
    (hA.ctxR hI₃) by_omega
    (fun h0 => by
      rw [q3H, hvz]; have := hzts; subst h0; tauto)
    (fun h1 => by
      rw [q3H, hvz]; have := hzts; subst h1; tauto)
    by_omega) ?_).mono by_omega (fun _ h => h)
  rintro c₄ hI₄ hA₄ hA₄' ⟨⟨b1, b2⟩, ⟨b3, b4⟩, b5, b6, b7⟩
  rw [q3H, hvz] at b2 b4
  have s4 := fun r h1 h2 a b d =>
    b5 r (not_oracle_sw h1 h2) a b d (by rne)
  -- 6. clear the accumulator
  have okA : okB W c₄.nmem [.constN accA 0] c₄.nreg :=
    ⟨⟨iscr_sw (by rne) (by rne), Nat.zero_le _⟩, trivial⟩
  refine (IRS.seq (K₂ := 35094 + Kc) (IRS.block _ hI₄ okA) ?_).mono ztbaw ztb
  zukod
  have v5 : ∀ r, r ≠ accA → c₅.nreg r = c₄.nreg r := fun r hr => by
    rw [hc5]; zumxi; exact upd_other _ _ _ hr
  have acc5 : c₅.nreg accA = 0 := by rw [hc5]; rfl
  have m5 : ztpnw := by rw [hc5]
  have s5 : ∀ r, 240000 ≤ r → r < 250000 → r ≠ bL → r ≠ bR → ¬ ztdpp →
      r ≠ accA → c₅.nreg r = c₃.nreg r := fun r h1 h2 a b d e => by
    rw [v5 r e, s4 r h1 h2 a b d]
  have hA5 : c₅.nreg ALLOC = c₄.nreg ALLOC := v5 _ (by rne)
  have q5E : c₅.nreg qE = q.1 := by
    rw [s5 qE (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q3E]
  have q5H : c₅.nreg qH = q.2.1 := by
    rw [s5 qH (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q3H]
  have q5D : c₅.nreg qD = q.2.2 := by
    rw [s5 qD (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q3D]
  have q5J : c₅.nreg qJ = j := by
    rw [s5 qJ (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q3J]
  have q5zE : c₅.nreg zE = c₂.nreg zE := by
    rw [s5 zE (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q3zE]
  have q5P := s5 zP (by rne) (by rne) (by rne) (by rne) (by rne) (by rne)
  have q5Ph :=
    s5 zPh (by rne) (by rne) (by rne) (by rne) (by rne) (by rne)
  have q5bL : c₅.nreg bL = c₄.nreg bL := v5 _ (by rne)
  have q5bR : c₅.nreg bR = c₄.nreg bR := v5 _ (by rne)
  have hQS : QState P J i z c₅ := by
    refine ⟨by rw [q5E, q5H, q5D]; exact hB.hq q hqL, by_grind,
      by grind, by_omega, by_grind,
      by grind, by_grind,
      by omega, by_grind, by_grind,
      by grind, by_grind⟩
  have hend5 : i = 1 → c₅.nreg qJ < 2 * N₂.nChords →
      (c₅.nreg qE, c₅.nreg qH, c₅.nreg qD) =
        (sweepEndQ N₂.chords).getD (c₅.nreg qJ) ztt := by
    intro hi1 hlt
    obtain ⟨L₁, hL, -⟩ := hB.hend hi1
    rw [q5E, q5H, q5D, q5J]
    rw [q5J] at hlt
    have hlen : ztmsd := by
      zugge
    show q = _
    rw [hq_def, hL, List.getD_append _ _ _ _ by_omega]
  -- 7. the candidate step
  have hKc5 := hK.fix hI₅
  have hdisp : IRS P W c₀ ztprx c₅ (Kc + 2)
      (fun c'' => CandOut P J z c₅ c'' ∧ CandFr c₅ c'') := by
    have hcand := hc c₅ hI₅ hQS q5J hend5 acc5 by_omega
    zujdf
    · rw [ite_eq_left h0] at hcand
      exact IRS.ifT ztiik hcand
    · zvmyd at hcand
      exact IRS.ifF ztiik hcand
  refine (IRS.seq (K₂ := 35068) hdisp ?_).mono by_omega ztb
  rintro c₆ hI₆ hA₆ hA₆' ⟨⟨Lc, hacc, hgood, hhit⟩, cf1, cf2, cf3⟩
  rw [q5D] at hacc hgood hhit
  obtain ⟨wf, wt, wpp, we, wpos⟩ := winner_eq hacc hgood hhit
  have s6 :=
    fun r h1 h2 a b d => cf1 r (not_oracle_sw h1 h2) a b d (by rne)
  have q6bL := s6 bL (by rne) (by rne) (by rne) (by rne) (by rne)
  have q6bR := s6 bR (by rne) (by rne) (by rne) (by rne) (by rne)
  rw [← q6bL, ← q6bR] at wpp we wpos
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h40, h45, h33, h34, h35, -⟩ := id hA.hst
  have rr6 : ∀ x, 240000 ≤ x → x < 240700 → c₆.nreg x = c₀.nreg x := fun x h1 h2 =>
    hI₆.hin _ ztwo
  have hmL : ztpkj := sideChain_m_le J 0
  have hmR : ztmti := sideChain_m_le J 1
  have hWm := hA.hWm
  -- 8. the winner in the walk of `C`
  refine (IRS.seq (K₂ := 35038) (winQ_irs hI₆ hK by_omega (fun t0 l1 => ?_) (fun t1 r1 => ?_)) ?_).mono by_omega
    ztb
  · have hM : ModB J ztvod ztvoe ztbahf = J.left := by
      unfold ModB; zunab
    zuijc
    zqbev
    rw [rr6 (sw 33) (by rne) (by rne), rr6 (sw 45 + 1) (by rne) (by rne),
      rr6 (sw 45) (by rne) (by rne), rr6 (sw 35) (by rne) (by rne), h33, h35, show sw 45 = sw _ from rfl, h45 0 by_norm_num,
      show sw _ + 1 = sw ztngs from rfl, h45 1 by_norm_num]
    simp only [cstL, List.getD_cons_zero, List.getD_cons_succ]
    omega
  · have hM : ModB J ztvod ztvoe ztbahf = J.right := by
      unfold ModB; rw [ite_eq_right by_omega, ite_eq_left by_omega]
    zuijc
    zufht

    rw [rr6 (sw 34) (by rne) (by rne), rr6 (sw 40 + 1) (by rne) (by rne),
      rr6 (sw 40) (by rne) (by rne), rr6 (sw 35) (by rne) (by rne), h34, h35, show sw 40 = sw _ from rfl, h40 0 by_norm_num,
      show sw _ + 1 = sw ztngi from rfl, h40 1 by_norm_num]
    simp only [cstR, List.getD_cons_zero, List.getD_cons_succ]
    omega
  rintro c₇ hI₇ hA₇ hA₇' ⟨y1, y2, y3, y4⟩
  obtain ⟨w1, w2, w3⟩ := winVal_sem hI₆ hA.hst hA.hP hzR
    (fun h => by rw [q6bL, q5bL] at h; exact b2.1 h) (fun h => by rw [q6bR, q5bR] at h; exact b4.1 h)
    wpp we wpos
  rw [← y1] at w1
  rw [← y1, ← y2] at w2 w3
  have s7 : ∀ r, 240000 ≤ r → r < 250000 → ¬ ztdpo →
      ¬ ztdpq → ¬ ztbwg → r ≠ yE → r ≠ yH →
      c₇.nreg r = c₅.nreg r := fun r h1 h2 a b d e f => by
    rw [y3 r e f (by rne) (by rne) (by rne), s6 r h1 h2 a b d]
  have q7D : c₇.nreg qD = q.2.2 := by
    rw [s7 qD (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q5D]
  have q7H : c₇.nreg qH = q.2.1 := by
    rw [s7 qH (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q5H]
  have q7P : c₇.nreg zP = c₃.nreg zP := by
    rw [s7 zP (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q5P]
  have q7Ph : c₇.nreg zPh = c₃.nreg zPh := by
    rw [s7 zPh (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q5Ph]
  have hA7 : c₇.nreg ALLOC = c₆.nreg ALLOC := y3 _ (by rne) (by rne) (by rne) (by rne) (by rne)
  -- 9. the record
  refine (IRS.seq (K₂ := 8) (recS_irs hI₇ hK hA.hP (hA.ctxW hI₇) hzt (by zupdk; omega)
    rfl (by rw [q7D, q7P, q7Ph]; exact a3) w1 w2 (by zupdk; exact w3) hzR hvz (by unfold recK; omega)) ?_).mono by_rfl (fun _ h => h)
  rintro c₈ hI₈ hA₈ hA₈' ⟨hRD, x1, x2, x3⟩
  rw [q7D, q7P] at hRD
  have hSee := seesInWhole_hit J _ i q hzq rfl hzt ⟨hfree, rfl⟩ hRD
  have k8 := fun r h1 h2 a b d e f g =>
    x1 r (not_oracle_sw h1 h2) a b d e f g (by rne)
  have q8H : c₈.nreg qH = q.2.1 := by
    rw [k8 qH (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne) (by rne), q7H]
  -- 10. the height code minus one
  have hKc8 := hK.fix hI₈
  have okH : okB W c₈.nmem [.subN tH qH K1] c₈.nreg := ⟨iscr_sw (by rne) (by rne), trivial⟩
  refine IRS.seq (K₂ := 7) (IRS.block _ hI₈ okH) ?_
  rintro c₉ hI₉ - - hc9
  have v9 : ∀ r, r ≠ tH → c₉.nreg r = c₈.nreg r := fun r hr => by
    zuogw; zumxi; exact upd_other _ _ _ hr
  have t9 : c₉.nreg tH = q.2.1 - 1 := by
    zuogw; zvmzj; rw [q8H, hKc8.2.1]
  have m9 : c₉.nmem = c₈.nmem := by zuogw
  -- the frame up to the store
  have fr4 : PFr QW c₃ c₄ := ⟨fun r h0 h1 h2 => b5 r h0
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (fun h => h1 ztfxv) h2, b6, b7⟩
  have fr5 : PFr QW c₄ c₅ := ⟨fun r _ h1 _ => v5 r (by intro h; apply h1; subst h; left; rne),
      by omega, fun a _ => by rw [m5]⟩
  have fr6 : PFr QW c₅ c₆ := ⟨fun r h0 h1 h2 => cf1 r h0
      (fun h => h1 (Or.inl ⟨h.1, by unfold sw at *; omega⟩))
      (fun h => h1 ztiqb) (fun h => h1 ztbho) h2, cf2, cf3⟩
  have fr7 : PFr QW c₆ c₇ := ⟨fun r _ h1 _ => y3 r (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne),
      by omega, fun a _ => by rw [y4]⟩
  have fr8 : PFr QW c₇ c₈ := ⟨fun r h0 h1 h2 => x1 r h0
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne)
      (by intro h; apply h1; subst h; left; rne) (by intro h; apply h1; subst h; left; rne) h2,
      x2, x3⟩
  have fr9 : PFr QW c₈ c₉ := ⟨fun r _ h1 _ => v9 r (by intro h; apply h1; subst h; left; rne),
      by rw [v9 ALLOC (by rne)], fun a _ => by rw [m9]⟩
  have fr := ((((((fr3.trans fr4 ztb).trans fr5 ztb).trans
    fr6 ztb).trans fr7 (fun _ h => h)).trans fr8 (fun _ h => h)).trans fr9
    ztb)
  have hR9 := fr.1 pR (not_oracle_sw (by rne) (by rne))
    (by unfold QW; rne) (by rne)
  -- 11. the store
  refine (store4_irs hI₉ hK (by rne) (by rne) (by rne) by_omega
    by_omega).mono le_rfl ?_
  zuewf
  rw [hR9, (hK.fix hI₉).2.1, t9, v9 rL (by rne), v9 rR (by rne)] at w1
  refine ⟨⟨(1, q.2.1 - 1, c₈.nreg rL, c₈.nreg rR), ?_, ?_, ?_, ?_, hSee⟩,
    fun a ha hout => ?_, fun r h1 h2 => ?_, ?_⟩
  · zqber
  · zqber
  · zqber
  · zqber
  · zqbes
    exact fr.2.2 a ha
  · rw [w2 r (by rne)]
    exact fr.1 r ztftm
      (by unfold QW; unfold sw at *; omega) (by rne)
  · rw [w2 ALLOC (by rne)]; exact fr.2.1
open Classical in
/-- The cost of the candidate step of a query. -/
noncomputable def candK (κ0 κ1 F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List zte) (i j : ℕ) : ℕ :=
  if i = 0 then κ0 zto * ztwit
  else κ1 zto * ztwit +
    (if BruteQ J N₂ j ztdvu then
      κ1 zto * ztyz * ztwju else 0)
theorem candK_le (κ0 κ1 F : ℕ → ℕ) (c₀ : Config) (J : Merge.Junction) (P : Polygon)
    (N₁ N₂ : NF) (L : List zte) {i : ℕ} (hi : i ≤ 1) (j : ℕ) :
    87100 + candK κ0 κ1 F c₀ J P N₁ N₂ L i j ≤
      qCost (fun D => κ0 D + κ1 D + 87100) F c₀ J P N₁ N₂ L i j := by
  unfold candK qCost
  grind
open Classical in
/-- **The per-query procedure from the candidate steps.** -/
theorem qry_of_cands (h0 : Cand0Spec) (h1 : Cand1Spec) :
    ∃ (init0 : Stmt) (Aux : Polygon → Merge.Junction → NF → Config → Prop) (κ0 : ℕ → ℕ),
      InitSpec init0 Aux κ0 ∧ QrySpec Aux := by
  obtain ⟨init0, cand0, Aux, κ0, hInit, hRob, hC0⟩ := h0
  obtain ⟨cand1, κ1, hC1⟩ := h1
  refine ⟨init0, Aux, κ0, hInit, fun sh => qryP ztvky ztvkz,
    fun D => κ0 D + κ1 D + 87100, ?_⟩
  intro sh Bs F X Ok hsh hBs hXl P W c₀ c J H N₁ N₂ E L i j hB hI hpJ hj hpA hpR hslot hroom
  have hle := candK_le κ0 κ1 F c₀ J P N₁ N₂ L hB.hi j
  refine (qry_run hB
    hI hpJ hj hpA hpR hslot ?_ by_omega).mono hle (fun c' h => h)
  intro c' hI' hQS hqJ hend hacc hroom'
  zujdf
  · zubvi
    zubyt
    have hk : candK κ0 κ1 F c₀ J P N₁ N₂ L 0 j =
        κ0 zto * ztwit := by
      rfl
    zujjc
    exact hC0 sh Bs F X Ok hsh hBs hXl P W c₀ c' J H N₁ N₂ E _ hB.hA (hB.hAux rfl) hI' hQS hacc
      hroom'
  · zubvi
    rw [ite_eq_right by_norm_num]
    have hk : candK κ0 κ1 F c₀ J P N₁ N₂ L 1 j =
        κ1 zto * ztwit +
          (if BruteQ J N₂ ztvgw (qPt J P 1 L j) then
            κ1 zto * ztyz * ztwju else 0) := by
      unfold candK; grind
    zujjc
    exact hC1 sh Bs F X Ok hsh hBs hXl P W c₀ c' J H N₁ N₂ E _ hB.hA hI' hQS (hend rfl) hacc
      hroom'
end
end SweepIo
end Chazelle.Core
end
namespace Chazelle.Core
namespace SweepIo
@[expose] public section
theorem sweepSpecH_of (hE : SweepEvSpec) (h0 : Cand0Spec) (h1 : Cand1Spec) : SweepSpecH := by
  obtain ⟨init0, Aux, κ0, hInit, hQ⟩ := qry_of_cands h0 h1
  exact asmGoal hE init0 Aux κ0 hInit (loopSpec_of hQ topCount)
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Split
@[expose] public section
open Set
open Chazelle.Existence (WeakTriangulates relabel IsDiagonal triangulates_of_weak)
open Chazelle.EarClip (subPoly n_subPoly relabelList subPoly_range getD_range relabelList_range)
open Chazelle.Mountain (allDiagonals diagSeg allDiagonals_isDiagonal allDiagonals_inter
  allDiagonals_lt allDiagonals_finite IsPiece IsPieceEdge)
variable {P : Polygon}

/-! ### Elementary facts -/

/-- `Chazelle.Mountain.diagSeg` is `pairSeg`. -/
theorem diagSeg_eq_pairSeg (P : Polygon) (d : ℕ × ℕ) : diagSeg P d = pairSeg P d := rfl

/-- A diagonal with its endpoints swapped. -/
theorem IsDiag.swap {l : List ℕ} {d : ℕ × ℕ} (hd : IsDiag P l d) : IsDiag P l d.swap := by
  obtain ⟨h1, h2, hne, hch, hf⟩ := hd
  refine ⟨h2, h1, Ne.symm hne, ?_, ?_⟩
  · zuhgu
    zukyf
    simp_all
  · rw [pairSeg_swap]; exact hf
variable {d d' : ℕ × ℕ}
/-- Non-crossing is invariant under swapping the first pair. -/
theorem NonCross.swap_left (h : NonCross P d d') : NonCross P d.swap d' := by
  zuda
  zukyf
  have := h hp
  grind

/-- Non-crossing is symmetric. -/
theorem NonCross.symm (h : NonCross P d d') : NonCross P d' d := by
  zuda
  have := h ztuhv
  simp_all

/-- Non-crossing is invariant under swapping the second pair. -/
theorem NonCross.swap_right (h : NonCross P d d') : NonCross P d d'.swap :=
  h.symm.swap_left.symm

/-- **An inserted diagonal is an `IsDiag` of the whole polygon.** -/
theorem isDiag_range_of_mem_allDiagonals (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ allDiagonals P) : IsDiag P ztbyp d := by
  obtain ⟨h1, h2, hne⟩ := allDiagonals_lt hP hd
  obtain ⟨s, L, hdiag, hs, hsL, hsub⟩ := allDiagonals_isDiagonal hP hd
  unfold IsDiag
  zumoz
  refine ⟨List.mem_range.2 h1, List.mem_range.2 h2, hne, ?_, hsub⟩
  have hch := hdiag.2.2
  rw [hs, hsL] at hch
  tauto

/-- A member of `allDiagonals P` up to orientation is an `IsDiag` of the whole polygon. -/
theorem isDiag_range_of_mem_or_swap (hP : P.Simple) {d : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P) : IsDiag P ztbyp d := by
  rcases hd with h | h
  · exact isDiag_range_of_mem_allDiagonals hP h
  · have := (isDiag_range_of_mem_allDiagonals hP h).swap
    simp_all

/-- **Two inserted diagonals (up to orientation) with the same segment are the same pair up to
orientation.** -/
theorem eq_or_eq_swap_of_pairSeg_eq (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P ∨ d'.swap ∈ allDiagonals P) (h : pairSeg P d = pairSeg P d') :
    d' = d ∨ d' = d.swap := by
  have hD := isDiag_range_of_mem_or_swap hP hd
  have hD' := isDiag_range_of_mem_or_swap hP hd'
  have hQ : (subPoly P ztbyp).Simple := by rw [subPoly_range]; exact hP
  -- each endpoint of `d'` is an endpoint of `d`
  have key : ∀ x, x ∈ List.range P.n → P.vtx x ∈ pairSeg P d → x = d.1 ∨ x = d.2 := by
    intro x hxl hxs
    zubqk
    zudva
    apply hD.2.2.2.1 _ hxs (fun e => hcon.1 (eq_of_vtx_eq P hQ hxl hD.1 e))
      (fun e => hcon.2 (eq_of_vtx_eq P hQ hxl hD.2.1 e))
    zumoz
    exact Chazelle.Existence.vtx_mem_boundary P (List.mem_range.1 hxl)
  have e1 := key d'.1 hD'.1 (by zvmwc; exact Chazelle.Geometry.left_mem_segment _ _)
  have e2 := key d'.2 hD'.2.1 (by zvmwc; exact Chazelle.Geometry.right_mem_segment _ _)
  have hne := hD.2.2.1
  have hne' := hD'.2.2.1
  grind

/-- **Two inserted diagonals (up to orientation) that are distinct pairs up to orientation do not
cross.** -/
theorem nonCross_of_mem_or_swap (hP : P.Simple) {d d' : ℕ × ℕ}
    (hd : d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P)
    (hd' : d' ∈ allDiagonals P ∨ d'.swap ∈ allDiagonals P) (hne : d ≠ d' ∧ d ≠ d'.swap) :
    NonCross P d d' := by
  have hseg : pairSeg P d ≠ pairSeg P d' := by
    zuq
    rcases eq_or_eq_swap_of_pairSeg_eq hP hd hd' h with e | e
    · simp_all
    simp_all
  have key : ∀ e e', e ∈ allDiagonals P → e' ∈ allDiagonals P →
      pairSeg P e = pairSeg P d → pairSeg P e' = pairSeg P d' → NonCross P e e' := by
    intro e e' he he' h1 h2
    apply allDiagonals_inter hP he he'
    rw [diagSeg_eq_pairSeg, diagSeg_eq_pairSeg, h1, h2]
    omega
  rcases hd with h | h <;> rcases hd' with h' | h'
  · simp_all
  · have := (key _ _ h h' rfl zttvp).swap_right
    simp_all
  · have := (key _ _ h h' zttvq rfl).swap_left
    simp_all
  · have := (key _ _ h h' zttvq zttvp).swap_left.swap_right
    simp_all

/-! ### Enumerations of the inserted diagonals -/

/-- **`D` enumerates the inserted diagonals of `P` up to orientation**: every member or its swap
is in `allDiagonals P`, every member of `allDiagonals P` or its swap is in `D`, and no pair occurs
twice in `D`, in either orientation. -/
structure EnumDiags (P : Polygon) (D : List ztw) : Prop where
  sound : ∀ d ∈ D, d ∈ allDiagonals P ∨ d.swap ∈ allDiagonals P
  complete : ∀ d ∈ allDiagonals P, d ∈ D ∨ d.swap ∈ D
  distinct : D.Pairwise (fun d d' => d ≠ d' ∧ d ≠ d'.swap)

/-- **An enumeration of the inserted diagonals is a diagonal system for the whole polygon.** -/
theorem EnumDiags.diagSystem (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D) :
    DiagSystem P ztbyp D where
  simple := by rw [subPoly_range]; exact hP
  diag d hd := isDiag_range_of_mem_or_swap hP (hD.sound d hd)
  noncross := hD.distinct.imp_of_mem fun hd hd' hne =>
    nonCross_of_mem_or_swap hP (hD.sound _ hd) (hD.sound _ hd') hne

/-- A cyclic edge of `List.range n` is an edge `x → x + 1 (mod n)`. -/
theorem cycEdge_range {n x y : ℕ} (h : CycEdge ztpzu x y) : y = zthf % n := by
  obtain ⟨k, hk, rfl, rfl⟩ := h
  rw [List.length_range] at hk ⊢
  rw [getD_range hk, getD_range ztcv]

/-- **Every output piece is a piece of the subdivision of `P` by `allDiagonals P`.** -/
theorem EnumDiags.isPiece (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D) {m : List ℕ}
    (hm : m ∈ splitAll ztbyp D) : IsPiece P m := by
  obtain ⟨hs, hsub, hedges, hbd, hdiag, hfill⟩ := pieceOf_splitAll ztqpe m hm
  rw [subPoly_range] at hbd hfill
  refine ⟨nodup_of_simple P hs, fun x hx => List.mem_range.1 (hsub x hx),
    three_le_of_simple P hs, ?_, hs, hbd, ?_, hfill⟩
  · zugf
    rcases hedges k hk with h | h | h
    · exact Or.inl (cycEdge_range h)
    · zuidy
      · tauto
      tauto
    · zuidy
      · tauto
      tauto
  · intro d hd p hp
    rw [diagSeg_eq_pairSeg]
    rcases hD.complete d hd with h' | h'
    · simp_all
    · rw [← pairSeg_swap]; grind

/-- The triangles of a weak triangulation of `P` are unchanged by `relabelList (List.range P.n)`. -/
theorem map_relabelList_range {T : List Polygon.Triangle} (h : WeakTriangulates P T) :
    T.map ztbaip = T := by
  conv_rhs => rw [← List.map_id T]
  zucfh
  zucj
  exact relabelList_range (index_lt_of_weak h ht)

/-- **Combination on the whole polygon.**  If `T m` weakly triangulates `subPoly P m` (in
positions of `m`) for every piece `m` of `splitAll (List.range P.n) D`, then the concatenation of
the `T m` relabelled to original indices weakly triangulates `P`. -/
theorem EnumDiags.weakTriangulates (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D)
    {T : List ℕ → List Polygon.Triangle}
    (hT : ∀ m ∈ splitAll ztbyp D, WeakTriangulates ztevt ztjng) :
    WeakTriangulates P
      ((splitAll ztbyp D).flatMap zteci) := by
  have hsys := hD.diagSystem hP
  have hw := weakTriangulates_combineTri hsys hT
  rw [subPoly_range] at hw
  rw [← map_relabelList_combineTri hsys hT, map_relabelList_range hw]
  zulzb

/-! ### A canonical enumeration -/

/-! ### The final composition -/
end
end Chazelle.Split
section
set_option hygiene false
local macro "zqox" : tactic => `(tactic| simp only [hS', surgery, upd])
local macro "zqoy" : tactic => `(tactic| obtain ⟨m, hm, (⟨hd, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm')
local macro "zqoz" : tactic => `(tactic| (zvmwf; have hz' : ztjaw := hz; split_ifs))
local macro "zqpa" : tactic => `(tactic| rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right h1])
local macro "zqpb" : tactic => `(tactic| rw [hlen2, show len - L + 1 - 1 = len - L by omega, hg2_last, hg2_0])
local macro "zqpc" : tactic => `(tactic| (set m := c.map S.vtx with hm; have hmem : m ∈ (c :: rest).map _ := List.mem_map_of_mem List.mem_cons_self))
local macro "zqpd" : tactic => `(tactic| (rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega]; simp))
set_option hygiene true

/-!
# Splitting a simple polygon along its diagonal list with a linked structure

This file gives the abstract (list-level) version of the linear-time splitting of a simple
polygon `P` along a list `D` of non-crossing diagonals, and proves it correct against
`Chazelle.Split.splitAll`.

## Sequential splitting (`seqSplit`)

`cut P pcs d` replaces every piece `m` of the list `pcs` in which `d` is an interior diagonal
(`IsDiag P m d`) by its two pieces `splitFst m d`, `splitSnd m d`; `seqSplit P pcs D` cuts
along the members of `D` in order.  `seqSplit_eq_splitAll`: for a diagonal system,
`seqSplit P [l] D = splitAll l D` (the recursion of `splitAll` distributes the remaining
diagonals exactly as sequential cutting does).  `Good P σ pcs E` is the invariant of sequential
cutting: simple pieces of orientation `σ` with pairwise disjoint interiors, every remaining
diagonal an interior diagonal of some piece, the remaining diagonals pairwise non-crossing.

## The linked structure (`LState`)

Pieces are cycles of *nodes*; a node is a copy of a vertex: `vtx z` is its vertex, `nxt z`,
`prv z` its neighbours in its cycle, `cnt` the number of nodes (`0 … cnt - 1`), `cop v` the list
of the copies of the vertex `v`.  Initially node `i` is vertex `i` (`init n`).

`step P σ S (a, b)`: the copy `x` of `a` whose corner passes the wedge test towards `b`
(`nodeWedge`, `Chazelle.Final.wedgeTest` with the corner `vtx (prv x) → a → vtx (nxt x)`), the
copy `y` of `b` whose corner passes the wedge test towards `a`, two new nodes `x' = cnt` (a copy of
`a`) and `y' = cnt + 1` (a copy of `b`), and the surgery

```
nxt y := x, prv x := y                       -- first cycle  x → … → y → x
nxt y' := nxt y, prv (nxt y) := y',          -- second cycle y' → nxt y → … → prv x → x' → y'
nxt (prv x) := x', prv x' := prv x, nxt x' := y', prv y' := x'
```

`Repr S cs`: the node lists `cs` partition `0 … cnt - 1` into cycles of `S`, and `cop` lists the
copies.  **Main theorem** (`runState_spec`): for an enumeration `D` of the inserted diagonals,
after processing `D` from `init P.n` with `σ = orient P`, the cycles read as vertex lists are a
permutation of the pieces `splitAll (List.range P.n) D` (exactly, each cycle read from the right
node).  Consequences: every cycle read from any of its nodes is a piece (`IsPiece`), and the
triangulations of the cycles assemble into a triangulation of `P` (`triangulates_of_cycles`).

## Cost

Processing `(a, b)` performs at most `(cop a).length + (cop b).length` wedge tests; the copies of
a vertex `v` number `1 +` (the processed diagonals incident to `v`), at most `11` for
`diagList P T C` (`countP_diagList_le`), so the total number of wedge tests is at most
`22 * D.length` (`runCost_le`).
-/
namespace Chazelle.Final
@[expose] public section
open Set
open Chazelle.Split (IsDiag NonCross splitFst splitSnd splitAll splitAll_nil splitAll_cons
  diagsFst diagsSnd sideTest sideTest_eq_true DiagSystem mem_of_mem_arcList EnumDiags
  splitPair_split SplitPair)
open Chazelle.EarClip (subPoly n_subPoly subPoly_range)
open Chazelle.Mountain (orient orient_eq IsPiece)
variable {P : Polygon}

/-! ### Sequential cutting -/
open Classical in
/-- Cut every piece of `pcs` in which `d` is an interior diagonal into its two pieces. -/
noncomputable def cut (P : Polygon) (pcs : List ztul) (d : ℕ × ℕ) : List ztul :=
  pcs.flatMap fun m => if IsDiag P m d then [splitFst m d, splitSnd m d] else [m]

/-- Cut along the members of `D` in order. -/
noncomputable def seqSplit (P : Polygon) : List ztul → List ztw → List ztul
  | pcs, [] => pcs
  | pcs, d :: D => seqSplit P ztfqs D
theorem seqSplit_cons (pcs : List ztul) (d : ℕ × ℕ) (D : List ztw) :
    seqSplit P pcs (d :: D) = seqSplit P ztfqs D := rfl
variable (A B : List (List ℕ)) {m : List ℕ} {pcs : List (List ℕ)} {d : ℕ × ℕ} {l' : List ℕ}
theorem cut_append (d : ℕ × ℕ) :
    cut P ztldt d = cut P A d ++ cut P B d := by
  unfold cut; simp
theorem cut_cons_of_isDiag {rest : List ztul} {d : ℕ × ℕ} (h : IsDiag P m d) :
    cut P (m :: rest) d = splitFst m d :: splitSnd m d :: cut P rest d := by
  zumsf
theorem cut_cons_of_not_isDiag {rest : List ztul} {d : ℕ × ℕ}
    (h : ¬ IsDiag P m d) : cut P (m :: rest) d = m :: cut P rest d := by
  zumsf

/-- Cutting along a diagonal of no piece changes nothing. -/
theorem cut_eq_self (h : ∀ m ∈ pcs, ¬ IsDiag P m d) :
    cut P pcs d = pcs := by
  induction pcs with
  | nil => rfl
  | cons m rest ih =>
    rw [cut_cons_of_not_isDiag by_simp_all,
      ih by_simp_all]

/-- Cutting respects permutations of the piece list. -/
theorem cut_perm {pcs pcs' : List ztul} (h : List.Perm pcs pcs') (d : ℕ × ℕ) :
    List.Perm ztfqs (cut P pcs' d) :=
  List.Perm.flatMap_right _ h

/-- A member of a cut is a piece of the list or one of its two pieces along `d`. -/
theorem mem_cut {m' : List ℕ} (h : m' ∈ cut P pcs d) :
    ∃ m ∈ pcs, (IsDiag P m d ∧ (m' = splitFst m d ∨ m' = splitSnd m d)) ∨
      (¬ IsDiag P m d ∧ m' = m) := by
  unfold cut at h
  grind
theorem seqSplit_append (D : List ztw) :
    seqSplit P ztldt D = seqSplit P A D ++ seqSplit P B D := by
  induction D generalizing A B with
  | nil => rfl
  | cons d D ih => rw [seqSplit_cons, cut_append, ih]; rfl

/-- The entries of the pieces of a cut are entries of the pieces cut. -/
theorem sub_of_mem_cut (h : ∀ m ∈ pcs, ∀ x ∈ m, x ∈ l')
    {d : ℕ × ℕ} : ∀ m ∈ cut P pcs d, ∀ x ∈ m, x ∈ l' := by
  intro m' hm' x hx
  obtain ⟨m, hm, (⟨-, rfl | rfl⟩ | ⟨-, rfl⟩)⟩ := mem_cut hm'
  · zujuu
  · zujuu
  grind

/-- **Irrelevant diagonals.**  When all entries of the pieces are entries of `l'`, the
diagonals without both endpoints in `l'` cut nothing. -/
theorem seqSplit_filter (h : ∀ m ∈ pcs, ∀ x ∈ m, x ∈ l')
    (D : List ztw) : seqSplit P pcs D = seqSplit P pcs (D.filter (sideTest l')) := by
  induction D generalizing pcs with
  | nil => rfl
  | cons d D ih =>
    by_cases hd : sideTest l' d = true
    · rw [List.filter_cons_of_pos hd, seqSplit_cons, seqSplit_cons, ih ztwft]
    · rw [List.filter_cons_of_neg hd, seqSplit_cons, ih ztwft]
      zucr
      apply cut_eq_self
      intro m hm hdiag
      exact hd (sideTest_eq_true.2 ⟨h m hm _ hdiag.1, h m hm _ hdiag.2.1⟩)

/-- **Sequential cutting is `splitAll`.**  For a diagonal system `D` of `(P, l)`, cutting `[l]`
along the members of `D` in order gives exactly `splitAll l D`. -/
theorem seqSplit_eq_splitAll {l : List ℕ} {D : List ztw} (h : DiagSystem P l D) :
    seqSplit P [l] D = splitAll l D := by
  revert h
  refine Chazelle.Split.splitAll_induction (motive := fun l D => DiagSystem P l D →
    seqSplit P [l] D = splitAll l D) ?_ ?_ l D
  · intro l _; rw [splitAll_nil]; rfl
  · intro l d D ih₁ ih₂ h
    zukbq
    rw [seqSplit_cons, show cut P [l] d = [splitFst l d] ++ [splitSnd l d] from
      cut_cons_of_isDiag hd, seqSplit_append, splitAll_cons, ← ih₁ h.fst, ← ih₂ h.snd]
    have hsub₁ : ∀ m ∈ [splitFst l d], ∀ x ∈ m, x ∈ splitFst l d := by
      simp
    have hsub₂ : ∀ m ∈ [splitSnd l d], ∀ x ∈ m, x ∈ splitSnd l d := by
      simp
    zucr
    · rw [seqSplit_filter hsub₁]; rfl
    · rw [seqSplit_filter hsub₂, seqSplit_filter hsub₂ ztczf]
      zucr
      unfold diagsSnd
      rw [List.filter_filter]
      apply List.filter_congr
      zubre
      by_cases h2 : sideTest ztbno e = true
      · have h1 : sideTest ztbhc e = false := by
          by_contra h1
          rw [Bool.not_eq_false] at h1
          exact h.splitPair.not_mem_both h.simple (h.tail_isDiag he) (h.tail_nonCross he)
            (sideTest_eq_true.1 h1) (sideTest_eq_true.1 h2)
        simp_all
      simp_all

/-! ### The invariant of sequential cutting -/

/-- **The invariant of sequential cutting**: the pieces are simple with orientation `σ` and
pairwise disjoint interiors; every remaining diagonal is an interior diagonal of some piece; the
remaining diagonals are pairwise non-crossing. -/
structure Good (P : Polygon) (σ : ℝ) (pcs : List ztul) (E : List ztw) : Prop where
  simple : ∀ m ∈ pcs, (subPoly P m).Simple
  orient : ∀ m ∈ pcs, orient ztevt = σ
  disj : pcs.Pairwise fun m m' =>
    Disjoint zthia zthhz
  diag : ∀ e ∈ E, ∃ m ∈ pcs, IsDiag P m e
  noncross : E.Pairwise ztvbs

/-- The invariant is insensitive to the order of the pieces. -/
theorem Good.perm {σ : ℝ} {pcs pcs' : List ztul} {E : List ztw} (h : Good P σ pcs E)
    (hp : List.Perm pcs pcs') : Good P σ pcs' E where
  simple m hm := h.simple m ztqqk
  orient m hm := h.orient m ztqqk
  disj := hp.pairwise h.disj fun hd => hd.symm
  diag e he := by
    obtain ⟨m, hm, hd⟩ := h.diag e he
    grind
  noncross := h.noncross

/-- The interior of a filled piece lies in the interior of the piece it was cut from. -/
theorem interior_subset_of_mem_cut
    (hs : ∀ m ∈ pcs, (subPoly P m).Simple) {m' : List ℕ} (hm' : m' ∈ cut P pcs d) :
    ∃ m ∈ pcs, interior (subPoly P m').filled ⊆ interior (subPoly P m).filled := by
  zqoy
  · exact ⟨m, hm, interior_mono (splitPair_split by_simp_all hd).filled_subset⟩
  · exact ⟨m, hm, interior_mono (splitPair_split by_simp_all hd).symm.filled_subset⟩
  grind

/-- **The invariant passes through a cut.** -/
theorem Good.cut {σ : ℝ} {pcs : List ztul} {d : ℕ × ℕ} {E : List ztw}
    (h : Good P σ pcs (d :: E)) : Good P σ ztfqs E where
  simple m' hm' := by
    zqoy
    · exact (splitPair_split ztfsf hd).simple₁
    · exact (splitPair_split ztfsf hd).simple₂
    · exact h.simple _ hm
  orient m' hm' := by
    zqoy
    · rw [orient_splitFst ztfsf hd]; exact h.orient m hm
    · rw [orient_splitSnd ztfsf hd]; exact h.orient m hm
    · exact h.orient _ hm
  disj := by
    unfold Final.cut
    zumln
    refine ⟨fun m hm => ?_, ?_⟩
    · split_ifs with hd
      · exact List.pairwise_pair.2 (splitPair_split ztfsf hd).interior_disjoint
      simp
    · refine h.disj.imp_of_mem fun {m₁ m₂} hm₁ hm₂ hdisj => ?_
      zulnq
      have hx' : x ∈ Final.cut P [m₁] d := by
        zumqv
      have hy' : y ∈ Final.cut P [m₂] d := by
        zumqv
      obtain ⟨m₁', hm₁', hsub₁⟩ := interior_subset_of_mem_cut
        (fun m hm => by zvojs at hm; zvmwi; exact h.simple _ hm₁) hx'
      obtain ⟨m₂', hm₂', hsub₂⟩ := interior_subset_of_mem_cut
        (fun m hm => by zvojs at hm; zvmwi; exact h.simple _ hm₂) hy'
      grind
  diag e he := by
    classical
    obtain ⟨m, hm, hde⟩ := h.diag e by_simp_all
    have hmem : ∀ m', m' ∈ (if IsDiag P m d then [splitFst m d, splitSnd m d] else [m]) →
        m' ∈ Final.cut P pcs d := fun m' hm' => by
      unfold Final.cut; grind
    by_cases hd : IsDiag P m d
    · have hnc := (List.pairwise_cons.1 h.noncross).1 e he
      rcases Chazelle.Split.isDiag_split_cases ztfsf hd hde hnc with
        ⟨-, -, h1⟩ | ⟨-, -, -, h2⟩
      · grind
      grind
    · grind
  noncross := (List.pairwise_cons.1 h.noncross).2

/-- The invariant passes through sequential cutting. -/
theorem Good.seqSplit {σ : ℝ} {pcs : List ztul} {E : List ztw} (h : Good P σ pcs E) :
    Good P σ (Final.seqSplit P pcs E) [] := by
  induction E generalizing pcs with
  | nil => exact h
  | cons d E ih => exact ih h.cut

/-- A simple polygon has a nonempty interior. -/
theorem interior_filled_nonempty {Q : Polygon} (hQ : Q.Simple) : (interior Q.filled).Nonempty := by
  zuhfh
  obtain ⟨δ, hδ⟩ := (Chazelle.Mountain.eventually_offset_orient hQ (i := 0) by_omega
    (t := 1 / 2) by_grind).exists
  exact ⟨_, by rw [Chazelle.Jordan.interior_filled hQ]; tauto⟩

/-- **Uniqueness of the piece of a diagonal**: in a list of pieces with pairwise disjoint
interiors, a diagonal of the head piece is a diagonal of no other piece. -/
theorem not_isDiag_of_disj {rest : List ztul} {d : ℕ × ℕ}
    (hs : (subPoly P m).Simple) (hd : IsDiag P m d)
    (hdisj : ∀ m' ∈ rest, Disjoint zthia zthhz)
    (hs' : ∀ m' ∈ rest, (subPoly P m').Simple) : ∀ m' ∈ rest, ¬ IsDiag P m' d := by
  intro m' hm' hd'
  have h1 := isDiag_lerp_mem_interior hs hd (ε := 1 / 2) by_grind
  have h2 := isDiag_lerp_mem_interior by_simp_all hd' (ε := 1 / 2) by_grind
  rw [← Chazelle.Jordan.interior_filled hs] at h1
  rw [← Chazelle.Jordan.interior_filled (hs' m' hm')] at h2
  grind

/-- **The initial invariant**: for an enumeration of the inserted diagonals, the whole polygon
`[List.range P.n]` with orientation `orient P`. -/
theorem good_init (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D) :
    Good P ztqui [List.range P.n] D where
  simple m hm := by
    zvojs at hm; zuopu; exact hP
  orient m hm := by zvojs at hm; zuopu
  disj := List.pairwise_singleton _ _
  diag e he := ⟨_, List.mem_singleton_self _, (hD.diagSystem hP).diag e he⟩
  noncross := (hD.diagSystem hP).noncross

/-! ### Index lists -/
section ListFacts
theorem getD_mem_of_lt {c : List ℕ} {t : ℕ} (ht : t < c.length) : c.getD t 0 ∈ c := by
  simp_all
theorem getD_inj_of_nodup {c : List ℕ} (hnd : c.Nodup) {t t' : ℕ} (ht : t < c.length)
    (ht' : t' < c.length) (h : c.getD t 0 = c.getD t' 0) : t = t' := by
  simp_all
theorem exists_getD_of_mem {c : List ℕ} {z : ℕ} (h : z ∈ c) : ∃ t < c.length, c.getD t 0 = z := by
  obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 h
  exact ⟨t, ht, by_simp_all⟩
theorem getD_map_of_lt (f : ℕ → ℕ) {c : List ℕ} {t : ℕ} (ht : t < c.length) :
    (c.map f).getD t 0 = f ztnwk := by
  simp_all
theorem getD_rotate_of_lt {c : List ℕ} (r : ℕ) {t : ℕ} (ht : t < c.length) :
    (c.rotate r).getD t 0 = c.getD ((t + r) % c.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_rotate ht]
theorem getD_take_of_lt {c : List ℕ} {k t : ℕ} (ht : t < k) : (c.take k).getD t 0 = c.getD t 0 := by
  simp_all
theorem getD_drop' (c : List ℕ) (k t : ℕ) : (c.drop k).getD t 0 = c.getD (k + t) 0 := by
  simp
variable {A B : List ℕ} {t : ℕ} (p : ℕ → Bool)
theorem getD_append_lt (ht : t < A.length) :
    (A ++ B).getD t 0 = A.getD t 0 := by
  grind
theorem getD_append_ge (ht : A.length ≤ t) :
    (A ++ B).getD t 0 = B.getD (t - A.length) 0 := by
  grind

/-- The last member of `l` satisfying `p` (or `r` if there is none): a left fold. -/
def selectLast (p : ℕ → Bool) (l : List ℕ) (r : ℕ) : ℕ :=
  l.foldl (fun r z => if p z then z else r) r
theorem selectLast_nil (r : ℕ) : selectLast p [] r = r := rfl
theorem selectLast_cons (z : ℕ) (l : List ℕ) (r : ℕ) :
    selectLast p (z :: l) r = selectLast p l (if p z then z else r) := rfl
theorem selectLast_append (l l' : List ℕ) (r : ℕ) :
    selectLast p ztrsu r = selectLast p l' (selectLast p l r) := by
  unfold selectLast; simp

/-- If every member satisfying `p` is `x`, selecting from `x` gives `x`. -/
theorem selectLast_self {p : ℕ → Bool} {x : ℕ} :
    ∀ {l : List ℕ}, (∀ z ∈ l, p z = true → z = x) → selectLast p l x = x
  | [], _ => rfl
  | z :: l, h => by
    zujlk
    by_cases hz : p z = true
    · rw [ite_eq_left hz, h z List.mem_cons_self hz]
      zulft
    · rw [ite_eq_right hz]
      zulft

/-- **Selection of the unique passing member**: if `x ∈ l` is the only member satisfying `p`,
the selection returns it, from any start. -/
theorem selectLast_eq_of_unique {l : List ℕ} {p : ℕ → Bool} {x : ℕ} (hx : x ∈ l)
    (hpx : p x = true) (huniq : ∀ z ∈ l, p z = true → z = x) (r : ℕ) : selectLast p l r = x := by
  induction l generalizing r with
  | nil => exact absurd hx List.not_mem_nil
  | cons a l ih =>
    zujlk
    by_cases ha : p a = true
    · rw [ite_eq_left ha, huniq a List.mem_cons_self ha]
      zulft
    · grind
end ListFacts

/-! ### The linked structure -/

/-- **The linked structure of the pieces.**  Nodes `0 … cnt - 1`; node `z` is a copy of the
vertex `vtx z`, with neighbours `nxt z`, `prv z` in its cycle; `cop v` lists the copies of the
vertex `v`. -/
structure LState where
  vtx : ℕ → ℕ
  nxt : ℕ → ℕ
  prv : ℕ → ℕ
  cnt : ℕ
  cop : ℕ → List ℕ

/-- The initial structure of an `n`-gon: node `i` is vertex `i`, one cycle `0 → 1 → ⋯ → n-1`. -/
def initState (n : ℕ) : LState where
  vtx z := z
  nxt z := ztokj % n
  prv z := ztqzh % n
  cnt := n
  cop v := if v < n then [v] else []

/-- **The wedge test at a node**: the vertex `w` passes the `σ`-side wedge test at the corner
`vtx (prv z) → vtx z → vtx (nxt z)` of node `z`. -/
def nodeWedge (P : Polygon) (σ : ℝ) (S : LState) (z w : ℕ) : Prop :=
  wedgeTest σ (P.vtx (S.vtx (S.prv z))) (P.vtx (S.vtx z)) (P.vtx (S.vtx ztvdc)) ztbup
open Classical in
/-- The (last) copy of the vertex `v` whose corner passes the wedge test towards `w` (or `0`);
the copies are scanned in the order of `cop v`. -/
noncomputable def findCopy (P : Polygon) (σ : ℝ) (S : LState) (v w : ℕ) : ℕ :=
  selectLast (fun z => decide ztpcu) ztqcm 0

/-- **The surgery** splitting the cycle through the nodes `x` (a copy of `a`) and `y` (a copy of
`b`) into `x → ⋯ → y → x` and `y' → nxt y → ⋯ → prv x → x' → y'`, with the new nodes
`x' = cnt` (a copy of `a`) and `y' = cnt + 1` (a copy of `b`). -/
def surgery (S : LState) (a b x y : ℕ) : LState where
  vtx := upd (upd S.vtx S.cnt a) ztdge b
  nxt := upd (upd (upd (upd S.nxt y x) ztdge ztmch) ztmci S.cnt) S.cnt ztdge
  prv := upd (upd (upd (upd S.prv x y) ztmch ztdge) S.cnt ztmci) ztdge S.cnt
  cnt := S.cnt + 2
  cop := upd (upd S.cop a (S.cnt :: S.cop a)) b (ztdge :: S.cop b)

/-- **One step**: split along the diagonal `(a, b)` at the copies chosen by the wedge test. -/
noncomputable def step (P : Polygon) (σ : ℝ) (S : LState) (d : ℕ × ℕ) : LState :=
  surgery S d.1 d.2 (findCopy P σ S d.1 d.2) (findCopy P σ S d.2 d.1)

/-- **The whole run**: process the diagonals in order. -/
noncomputable def runState (P : Polygon) (σ : ℝ) : LState → List ztw → LState
  | S, [] => S
  | S, d :: D => runState P σ ztcbd D

/-! ### Cycles -/

/-- `c` is a cycle of the structure: nonempty, and consecutive entries (cyclically) are linked by
`nxt` and `prv`. -/
def IsCyc (S : LState) (c : List ℕ) : Prop :=
  c ≠ [] ∧ ∀ i < c.length, S.nxt ztcus = c.getD ztzzx 0 ∧
    S.prv (c.getD ztzzx 0) = c.getD i 0

/-- The chain description of a cycle. -/
theorem isCyc_of_chain {S : LState} {c : List ℕ} (hne : c ≠ [])
    (hch : ∀ t, t + 1 < c.length → S.nxt ztnwk = c.getD ztbx 0 ∧
      S.prv ztzvg = c.getD t 0)
    (hn : S.nxt (c.getD ztthn 0) = c.getD 0 0)
    (hp : S.prv ztnwi = c.getD ztthn 0) : IsCyc S c := by
  refine ⟨hne, fun i hi => ?_⟩
  by_cases h : i + 1 < c.length
  · zvnnm; grind
  · have hi' : i = c.length - 1 := by_omega
    have e : ztg % c.length = 0 := by
      rw [show i + 1 = c.length by omega, Nat.mod_self]
    grind

/-- The chain relations of a cycle. -/
theorem IsCyc.chain {S : LState} {c : List ℕ} (h : IsCyc S c) {t : ℕ} (ht : t + 1 < c.length) :
    S.nxt ztnwk = c.getD ztbx 0 ∧ S.prv ztzvg = c.getD t 0 := by
  have := h.2 t by_omega
  rwa [Nat.mod_eq_of_lt ht] at this

/-- The predecessor in a cycle. -/
theorem IsCyc.prv_getD {S : LState} {c : List ℕ} (h : IsCyc S c) {i : ℕ} (hi : i < c.length) :
    S.prv ztcus = c.getD ztbaan 0 := by
  zufve
  have := (h.2 ztbaan ztbpn).2
  have e : (ztjyk % c.length + 1) % c.length = i := by
    rw [Nat.mod_add_mod, show i + c.length - 1 + 1 = i + c.length by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt hi]
  simp_all

/-- Rotating a cycle gives a cycle. -/
theorem IsCyc.rotate {S : LState} {c : List ℕ} (h : IsCyc S c) (r : ℕ) : IsCyc S (c.rotate r) := by
  have hl := List.length_pos_iff.2 h.1
  refine ⟨fun h' => by_simp_all, fun i hi => ?_⟩
  rw [List.length_rotate] at hi ⊢
  rw [getD_rotate_of_lt r hi, getD_rotate_of_lt r ztbpn]
  have e : (ztg % c.length + r) % c.length = ((i + r) % c.length + 1) % c.length := by
    grind
  zui
  exact h.2 _ ztbpn

/-- **The representation invariant**: the node lists `cs` partition the nodes `0 … cnt - 1`
into cycles of `S`, and `cop v` lists (without repetition) the copies of `v`. -/
structure Repr (S : LState) (cs : List ztul) : Prop where
  nodup : cs.flatten.Nodup
  mem : ∀ z, z ∈ cs.flatten ↔ z < S.cnt
  cyc : ∀ c ∈ cs, IsCyc S c
  cop : ∀ v z, z ∈ S.cop v ↔ z < S.cnt ∧ S.vtx z = v
  copNodup : ∀ v, (S.cop v).Nodup
theorem Repr.perm {S : LState} {cs cs' : List ztul} (h : Repr S cs) (hp : List.Perm cs cs') :
    Repr S cs' where
  nodup := hp.flatten.nodup_iff.1 h.nodup
  mem z := by rw [← hp.flatten.mem_iff]; exact h.mem z
  cyc c hc := h.cyc c (hp.mem_iff.2 hc)
  cop := h.cop
  copNodup := h.copNodup

/-- Replacing the head cycle by a rotation keeps the representation. -/
theorem Repr.rotate_head {S : LState} {c : List ℕ} {rest : List ztul} (h : Repr S (c :: rest))
    (r : ℕ) : Repr S (c.rotate r :: rest) where
  nodup := by
    have h1 := h.nodup
    rw [List.flatten_cons] at h1 ⊢
    exact ((List.rotate_perm c r).append_right _).nodup_iff.2 h1
  mem z := by
    rw [← h.mem z, List.flatten_cons, List.flatten_cons, List.mem_append, List.mem_append,
      List.mem_rotate]
  cyc c' hc' := by
    zujcn
    · exact (h.cyc c List.mem_cons_self).rotate r
    · exact h.cyc c' by_simp_all
  cop := h.cop
  copNodup := h.copNodup

/-- **The wedge test at a node of a cycle is the wedge test of the piece.**  For a cycle `c` and
a position `i`, the node wedge test at `c[i]` is the wedge test at vertex `i` of the sub-polygon
of the vertex list `c.map vtx`. -/
theorem nodeWedge_iff {S : LState} {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length)
    (σ : ℝ) (w : ℕ) :
    nodeWedge P σ S ztcus w ↔
      wedgeTest σ ((subPoly P zteqt).vtx (Chazelle.Jordan.prevIdx (subPoly P zteqt) i))
        ((subPoly P zteqt).vtx i)
        ((subPoly P zteqt).vtx (ztg % (subPoly P zteqt).n)) ztbup := by
  zufve
  have hn : (subPoly P zteqt).n = c.length := by_simp
  have hv : ∀ j < c.length, (subPoly P zteqt).vtx j = P.vtx (S.vtx ztnwj) := by
    zun
    rw [Chazelle.EarClip.vtx_subPoly_getD P _ by_simp_all,
      getD_map_of_lt _ hj]
  unfold nodeWedge Chazelle.Jordan.prevIdx
  rw [hn, hv _ ztbpn, hv _ hi, hv _ ztbpn, (hc.2 i hi).1,
    hc.prv_getD hi]

/-! ### The surgery -/
section Surgery
variable {S : LState} {a b x y : ℕ}
theorem surgery_vtx_old {z : ℕ} (hz : z < S.cnt) : (surgery S a b x y).vtx z = S.vtx z := by
  simp only [surgery, upd]
  grind
theorem surgery_vtx_x' : (surgery S a b x y).vtx S.cnt = a := by
  zuhqa
theorem surgery_vtx_y' : (surgery S a b x y).vtx ztdge = b := by
  zuhqa

/-- **Correctness of the surgery.**  Let `c` be a cycle of a represented structure, with the
copy `x = c[0]` of `a` and the copy `y = c[L]` of `b ≠ a`, `2 ≤ L ≤ c.length - 2`.  After the
surgery the structure represents the cycles `c[0 … L]` and `y', c[L+1 …], x'` together with the
other cycles. -/
theorem surgery_spec {c : List ℕ} {rest : List ztul} (hR : Repr S (c :: rest)) {L : ℕ}
    (hL2 : 2 ≤ L) (hLn : L + 2 ≤ c.length) (hab : a ≠ b) (hva : S.vtx ztnwi = a)
    (hvb : S.vtx ztthm = b) :
    Repr (surgery S a b ztnwi ztthm)
      (c.take ztgt :: (ztdge :: (c.drop ztgt ++ [S.cnt])) :: rest) := by
  set N := S.cnt with hN
  set len := c.length with hlen
  set x := c.getD 0 0 with hx
  set y := c.getD L 0 with hy
  set S' := surgery S a b x y with hS'
  have hflat := hR.nodup
  rw [List.flatten_cons, List.nodup_append] at hflat
  obtain ⟨hnd, hrnd, hdisj⟩ := hflat
  have hltc : ∀ z ∈ c, z < N := fun z hz =>
    (hR.mem z).1 by_simp_all
  have hltr : ∀ z ∈ rest.flatten, z < N := fun z hz =>
    (hR.mem z).1 by_simp_all
  zukbo
  have hg_lt : ∀ t < len, c.getD t 0 < N := fun t ht => hltc _ (getD_mem_of_lt ht)
  have hg_ne : ∀ t t', t < len → t' < len → t ≠ t' → c.getD t 0 ≠ c.getD t' 0 :=
    by grind
  have hpx : S.prv x = c.getD ztetx 0 := by
    rw [hx, hcyc.prv_getD by_omega, show 0 + len - 1 = len - 1 by omega,
      Nat.mod_eq_of_lt by_omega]
  have hny : S.nxt y = c.getD _ 0 := (hcyc.chain by_omega).1
  -- evaluation of the new links
  have nxt_old : ∀ z, z ≠ y → z ≠ c.getD ztetx 0 → z < N → S'.nxt z = S.nxt z := by
    intro z h1 h2 h3
    zqox
    zqpa
  have nxt_y : S'.nxt y = x := by
    have h1 := hg_ne L ztetx by_omega by_omega by_omega
    have h2 := hg_lt L by_omega
    zqox
    zqpd
  have nxt_px : S'.nxt (c.getD ztetx 0) = N := by
    have h2 := hg_lt ztetx by_omega
    zqox
    rw [ite_eq_right by_omega, ite_eq_left hpx.symm]
  have nxt_N : S'.nxt N = N + 1 := by
    zughq
  have nxt_N1 : S'.nxt zttg = c.getD ztgt 0 := by
    have h2 := hg_lt ztetx by_omega
    zqox
    rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_left rfl, hny]
  have prv_old : ∀ z, z ≠ x → z ≠ c.getD ztgt 0 → z < N → S'.prv z = S.prv z := by
    intro z h1 h2 h3
    zqox
    zqpa
  have prv_x : S'.prv x = y := by
    have h1 := hg_ne 0 ztgt by_omega by_omega by_omega
    have h2 := hg_lt 0 by_omega
    zqox
    zqpd
  have prv_ny : S'.prv (c.getD ztgt 0) = N + 1 := by
    have h2 := hg_lt ztgt by_omega
    zqox
    rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_left hny.symm]
  have prv_N : S'.prv N = c.getD ztetx 0 := by
    zqox
    grind
  have prv_N1 : S'.prv zttg = N := by
    zughq
  -- the first new cycle
  have hlen1 : (c.take ztgt).length = L + 1 := by_grind
  have hcyc1 : IsCyc S' (c.take ztgt) := by
    refine isCyc_of_chain by_grind ?_ ?_ ?_
    · zucj
      rw [hlen1] at ht
      rw [getD_take_of_lt by_omega, getD_take_of_lt by_omega]
      have hc := hcyc.chain (t := t) by_omega
      zujx
      · rw [nxt_old _ by_grind
          by_grind by_grind]
        omega
      grind
    · rw [hlen1, show L + 1 - 1 = L by omega, getD_take_of_lt by_omega,
        getD_take_of_lt by_omega]
      omega
    · rw [hlen1, show L + 1 - 1 = L by omega, getD_take_of_lt by_omega,
        getD_take_of_lt by_omega]
      omega
  -- the second new cycle
  set c2 := zttg :: (c.drop _ ++ [N]) with hc2
  have hlenA : (c.drop ztgt).length = len - L - 1 := by_grind
  have hlen2 : c2.length = len - L + 1 := by
    rw [hc2, List.length_cons, List.length_append, hlenA, List.length_singleton]; omega
  have hg2_0 : c2.getD 0 0 = N + 1 := rfl
  have hg2_mid : ∀ u, u < len - L - 1 → c2.getD ztcol 0 = c.getD (L + 1 + u) 0 := by
    zubgt
    rw [hc2, List.getD_cons_succ, getD_append_lt by_omega, getD_drop']
  have hg2_last : c2.getD (len - L) 0 = N := by
    rw [hc2, show len - L = (len - L - 1) + 1 by omega, List.getD_cons_succ,
      getD_append_ge by_omega, hlenA, Nat.sub_self]
    rfl
  have hcyc2 : IsCyc S' c2 := by
    refine isCyc_of_chain by_simp ?_ ?_ ?_
    · zucj
      rw [hlen2] at ht
      rcases Nat.eq_zero_or_pos t with rfl | htpos
      · rw [hg2_0, show 0 + 1 = 0 + 1 from rfl, hg2_mid 0 by_omega, Nat.add_zero]
        grind
      · zucyb
        rw [hg2_mid u by_omega]
        by_cases hu : u + 1 < len - L - 1
        · rw [hg2_mid _ hu]
          have hc := hcyc.chain (t := L + 1 + u) by_omega
          rw [show L + 1 + ztcol = L + 1 + u + 1 by omega]
          zujx
          · rw [nxt_old _ by_grind
              (hg_ne _ _ by_omega by_omega by_omega) by_grind]
            omega
          · rw [prv_old _ by_grind
              by_grind by_grind]
            omega
        · have hu' : u + 1 = len - L - 1 := by_omega
          rw [show u + 1 + 1 = len - L by omega, hg2_last,
            show L + 1 + u = len - 1 by omega]
          omega
    · zqpb
      omega
    · zqpb
      omega
  -- the other cycles are untouched
  have hcycr : ∀ c'' ∈ rest, IsCyc S' c'' := by
    intro c'' hc''
    have hold := hR.cyc c'' by_grind
    have hin : ∀ z ∈ c'', z ∈ rest.flatten := fun z hz => List.mem_flatten.2 by_grind
    have hnotc : ∀ z ∈ c'', z ∉ c := by_grind
    refine ⟨hold.1, fun i hi => ?_⟩
    have hl : 0 < c''.length := by_omega
    have hz1 := getD_mem_of_lt hi
    have hz2 := getD_mem_of_lt ztzuo
    rw [nxt_old _ ztyql
      ztyql zttnw,
      prv_old _ ztyqm
      ztyqm zttnw]
    exact hold.2 i hi
  -- the flattening
  have hperm : List.Perm (c.take ztgt :: c2 :: rest).flatten
      (c ++ rest.flatten ++ [N + 1, N]) := by
    rw [List.flatten_cons, List.flatten_cons, hc2]
    conv_rhs => rw [← List.take_append_drop ztgt c]
    rw [List.perm_iff_count]
    zujbq
    simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append]
    omega
  zuflw
  · rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨?_, by_simp, ?_⟩
    · grind
    · intro z hz w hw
      have : z < N := by_grind
      zvmxh at hw
      omega
  · intro z
    rw [hperm.mem_iff, List.mem_append, ← List.flatten_cons, hR.mem z]
    zvmxh
    show _ ↔ z < N + 2
    omega
  · zufxk
    zujcn
    · omega
    grind
  · intro v z
    have hcop := hR.cop
    have hnc : ∀ w u, N ≤ u → u ∉ S.cop w := by_grind
    show z ∈ upd _ b _ v ↔
      z < N + 2 ∧ upd _ _ b z = v
    have hvz : upd (upd S.vtx N a) _ b z =
        if z = N + 1 then b else if z = N then a else S.vtx z := rfl
    have hcz : upd (upd S.cop a _) b _ v =
        if v = b then zttg :: S.cop b else if v = a then N :: S.cop a else S.cop v := rfl
    rw [hvz, hcz]
    rcases lt_trichotomy z N with hz | hz | hz
    · rw [ite_eq_right (show ¬ z = N + 1 by omega), ite_eq_right ztoht]
      zupi
      · zucuj
        zujgu

        · grind
        omega
      · zuhqi
        zujgu

        · grind
        omega
      grind
    · subst hz
      rw [ite_eq_right (show ¬ N = N + 1 by omega), ite_eq_left rfl]
      zupi
      · zucuj
        grind
      · grind
      grind
    · by_cases hz1 : z = N + 1
      · subst hz1
        zubyt
        zupi
        · grind
        · zuhqi
          grind
        grind
      · rw [ite_eq_right hz1, ite_eq_right ztoht]
        have hzN : ¬ z < N + 2 := by_omega
        simp only [hzN, false_and, iff_false]
        zupi
        · zuenn
        · zuenn
        grind
  · zujbq
    show (upd _ b (zttg :: S.cop b) v).Nodup
    have hnc : ∀ w, N ∉ S.cop w ∧ N + 1 ∉ S.cop w := fun w =>
      ⟨fun h => by have := ((hR.cop w N).1 h).1; omega,
       fun h => by have := ((hR.cop w _).1 h).1; omega⟩
    zuby
    zupi
    · exact List.nodup_cons.2 ⟨by_grind, hR.copNodup b⟩
    · exact List.nodup_cons.2 ⟨by_grind, hR.copNodup a⟩
    · exact hR.copNodup v
end Surgery

/-! ### One step -/
section Step
open Chazelle.Split (diagLen diagLen_spec getD_idxOf isDiagonal_of_isDiag nodup_of_simple arcList)

/-- The second piece of a split, as the part of the rotation to `d.1` after `d.2`, closed by
`d.1`: `splitSnd m d = d.2 :: (m.rotate i).drop (L + 1) ++ [d.1]` with `i` the position of `d.1`
and `L = diagLen m d`. -/
theorem splitSnd_eq_cons {m : List ℕ} {d : ℕ × ℕ} (h1 : d.1 ∈ m) (h2 : d.2 ∈ m) (hne : d.1 ≠ d.2) :
    splitSnd m d = d.2 :: ((m.rotate (m.idxOf d.1)).drop (diagLen m d + 1) ++ [d.1]) := by
  obtain ⟨hL1, hLn, hsL⟩ := diagLen_spec h1 h2 hne
  set i := m.idxOf d.1 with hi
  set L := diagLen m d with hL
  have hlen : (m.rotate i).length = m.length := by_simp_all
  have e1 : m.rotate (m.idxOf d.2) = (m.rotate i).rotate L := by
    rw [List.rotate_rotate, ← List.rotate_mod m (i + L), hsL]
  unfold splitSnd arcList
  rw [e1, List.rotate_eq_drop_append_take by_omega, List.take_append,
    List.take_of_length_le by_simp_all, List.length_drop, hlen,
    show m.length - L + 1 - (m.length - L) = 1 by omega, List.take_take,
    show min 1 L = 1 by omega, List.drop_eq_getElem_cons by_omega, List.take_one]
  have hM0 : (m.rotate i).head? = some d.1 := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate by_omega, Nat.zero_add,
      Nat.mod_eq_of_lt ztuzn, List.getElem?_eq_getElem
      ztuzn, List.getElem_idxOf]
  have hML : (m.rotate i)[L]' by_omega = d.2 := by
    rw [List.getElem_rotate]
    grind
  simp_all
variable {σ : ℝ} {S : LState} {c : List ℕ} {rest : List (List ℕ)}

/-- **The wedge test finds the right copy.**  Let `c :: rest` be the cycles of a represented
structure whose vertex lists satisfy the invariant, `e` an interior diagonal of the head piece
`c.map vtx`, and `c[t₀]` the node of `e.1` in `c`.  Then the first copy of `e.1` passing the wedge
test towards `e.2` is `c[t₀]`: it passes (`wedge_of_isDiag`), and a copy in another cycle fails
(its piece has an interior disjoint from the head piece, `not_wedge_of_disjoint`). -/
theorem findCopy_eq {E : List ztw} (hR : Repr S (c :: rest))
    (hG : Good P σ ztfas E) {e : ℕ × ℕ}
    (he : IsDiag P zteqt e) {t₀ : ℕ} (ht₀ : t₀ < c.length)
    (hv : S.vtx (c.getD t₀ 0) = e.1) : findCopy P σ S e.1 e.2 = c.getD t₀ 0 := by
  classical
  zqpc
  have hs : (subPoly P m).Simple := hG.simple m hmem
  have hor : orient _ = σ := hG.orient m hmem
  have hmnd : m.Nodup := nodup_of_simple P hs
  zufgo

  zukbo
  have hlt : ∀ z, z ∈ c ++ rest.flatten ↔ z < S.cnt := by
    intro z; rw [← List.flatten_cons]; exact hR.mem z
  unfold findCopy
  refine selectLast_eq_of_unique ?_ ?_ ?_ 0
  · exact (hR.cop _ _).2 ⟨(hlt _).1 by_simp_all, hv⟩
  · rw [decide_eq_true_iff, nodeWedge_iff hcyc ht₀, ← hor]
    exact wedge_of_isDiag hs he by_simp_all
      by_simp_all
  · intro z hz hpz
    rw [decide_eq_true_iff] at hpz
    obtain ⟨hzlt, hzv⟩ := (hR.cop _ _).1 hz
    rcases List.mem_append.1 ((hlt z).2 hzlt) with hzc | hzr
    · obtain ⟨t, ht, rfl⟩ := exists_getD_of_mem hzc
      have hmt : m.getD t 0 = m.getD t₀ 0 := by
        simp_all
      grind
    · exfalso
      obtain ⟨c'', hc'', hzc''⟩ := List.mem_flatten.1 hzr
      obtain ⟨t, ht, rfl⟩ := exists_getD_of_mem hzc''
      have hcyc'' := hR.cyc c'' by_simp_all
      have hmem'' : c''.map S.vtx ∈ (c :: rest).map _ :=
        List.mem_map_of_mem by_simp_all
      have hs'' := hG.simple _ hmem''
      rw [nodeWedge_iff hcyc'' ht, ← hG.orient _ hmem''] at hpz
      have hvt : (subPoly P (c''.map S.vtx)).vtx t = P.vtx e.1 := by
        rw [Chazelle.EarClip.vtx_subPoly_getD P _ by_simp_all,
          getD_map_of_lt _ ht, hzv]
      refine not_wedge_of_disjoint hs'' by_simp_all
        (U := (subPoly P m).filled \ (subPoly P m).boundary) ?_ ?_ hpz
      · zudik
        rw [hvt]
        exact isDiag_lerp_mem_interior hs he hε
      · rw [← Chazelle.Jordan.interior_filled hs, ← Chazelle.Jordan.interior_filled hs'']
        simp_all

/-- **One step on the head cycle.**  If the head piece `c.map vtx` has `d` as an interior
diagonal, processing `d` gives a represented structure whose vertex lists are exactly the cut
of the vertex lists. -/
theorem step_spec_head {d : ℕ × ℕ} {E : List ztw} (hR : Repr S (c :: rest))
    (hG : Good P σ ztfas (d :: E)) (hd : IsDiag P zteqt d) :
    ∃ cs', Repr ztcbd cs' ∧
      cs'.map ztlff = cut P ztfas d := by
  zqpc
  have hs := hG.simple m hmem
  have hmnd := nodup_of_simple P hs
  have hlenm : m.length = c.length := List.length_map _
  zufgo

  have hnot : ∀ m' ∈ rest.map _, ¬ IsDiag P m' d :=
    not_isDiag_of_disj hs hd hdisj.1 fun m' hm' =>
      hG.simple m' by_simp_all
  zubxn
  set i := m.idxOf d.1 with hi_def
  set j := m.idxOf d.2 with hj_def
  set L := diagLen m d with hL_def
  have hi := List.idxOf_lt_length_of_mem hd.1
  have hj := List.idxOf_lt_length_of_mem hd.2.1
  have hmi := getD_idxOf hd.1
  have hmj := getD_idxOf hd.2.1
  have hdiag := isDiagonal_of_isDiag hs hd hi hmi hL1 hLn by_grind
  have hL2 := hdiag.1
  have hL2' : L + 2 ≤ m.length := by have := hdiag.2.1; rwa [n_subPoly] at this
  have hi' : i < c.length := by_omega
  have hj' : j < c.length := by_omega
  have hvx : S.vtx ztcus = d.1 := by rw [← getD_map_of_lt S.vtx hi', ← hm, hmi]
  have hvy : S.vtx ztnwj = d.2 := by rw [← getD_map_of_lt S.vtx hj', ← hm, hmj]
  have hfx := findCopy_eq hR hG hd hi' hvx
  have hfy :=
    findCopy_eq hR hG (Chazelle.Split.IsDiag.swap hd) hj' hvy
  have hstep : step P σ S d = surgery S d.1 d.2 ztcus ztnwj := by
    unfold step; grind
  set c' := c.rotate i with hc'
  have hlenc' : c'.length = c.length := List.length_rotate _ _
  have hc'0 : c'.getD 0 0 = c.getD i 0 := by
    rw [getD_rotate_of_lt i by_omega, Nat.zero_add, Nat.mod_eq_of_lt hi']
  have hc'L : c'.getD L 0 = c.getD j 0 := by
    rw [getD_rotate_of_lt i by_omega, Nat.add_comm, ← hlenm, hsL]
  have hsur := surgery_spec (hR.rotate_head i) hL2 by_grind hd.2.2.1
    by_grind by_grind
  rw [← hc', hc'0, hc'L, ← hstep] at hsur
  refine ⟨_, hsur, ?_⟩
  have hvold : ∀ l : List ℕ, (∀ z ∈ l, z < S.cnt) →
      l.map (step P σ S d).vtx = l.map S.vtx := by
    intro l hl
    zucfh
    zugh
    rw [hstep]; exact surgery_vtx_old by_grind
  have hltc : ∀ z ∈ c, z < S.cnt := fun z hz =>
    (hR.mem z).1 (by rw [List.flatten_cons]; grind)
  have hltc' : ∀ z ∈ c', z < S.cnt := fun z hz => hltc z (List.mem_rotate.1 hz)
  show _ = cut P (m :: rest.map _) d
  rw [cut_cons_of_isDiag hd, cut_eq_self hnot, List.map_cons, List.map_cons]
  zucr
  · rw [hvold _ fun z hz => hltc' z (List.mem_of_mem_take hz), List.map_take, hc',
      List.map_rotate]
    rfl
  zucr
  · rw [splitSnd_eq_cons hd.1 hd.2.1 hd.2.2.1, List.map_cons, List.map_append, List.map_singleton,
      hstep, surgery_vtx_y', surgery_vtx_x', ← hstep,
      hvold _ fun z hz => hltc' z (List.mem_of_mem_drop hz), List.map_drop, hc', List.map_rotate]
  · zucfh
    intro c'' hc''
    apply hvold
    zugh
    exact (hR.mem z).1 (by
      rw [List.flatten_cons]
      exact List.mem_append_right _ (List.mem_flatten.2 ⟨c'', hc'', hz⟩))

/-- **One step.**  If the cycles `cs` of a represented structure read, up to order, as a list of
pieces `pcs` satisfying the invariant for `d :: E`, then after processing `d` the new cycles read,
up to order, as `cut P pcs d`. -/
theorem step_spec {cs pcs : List ztul} {d : ℕ × ℕ} {E : List ztw} (hR : Repr S cs)
    (hp : List.Perm ztghv pcs) (hG : Good P σ pcs (d :: E)) :
    ∃ cs', Repr ztcbd cs' ∧
      List.Perm (cs'.map ztlff) ztfqs := by
  classical
  obtain ⟨m, hm, hd⟩ := hG.diag d List.mem_cons_self
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ztqqk
  have hcs : List.Perm cs _ := List.perm_cons_erase hc
  have hp' : List.Perm _ pcs :=
    (hcs.map _).symm.trans hp
  obtain ⟨cs', h1, h2⟩ := step_spec_head (hR.perm hcs) (hG.perm hp'.symm) hd
  exact ⟨cs', h1, by zvmxx; exact cut_perm hp' d⟩
end Step

/-! ### The whole run -/
section Run
variable {σ : ℝ}
@[simp] theorem runState_nil (S : LState) : runState P σ S [] = S := rfl
theorem runState_cons (S : LState) (d : ℕ × ℕ) (D : List ztw) :
    runState P σ S (d :: D) = runState P σ ztcbd D := rfl

/-- **The run simulates sequential cutting** (general form). -/
theorem runState_spec_gen (E : List ztw) :
    ∀ (S : LState) (cs pcs : List ztul), Repr S cs →
      List.Perm ztghv pcs → Good P σ pcs E →
      ∃ cs', Repr (runState P σ S E) cs' ∧
        List.Perm (cs'.map (List.map (runState P σ S E).vtx)) (seqSplit P pcs E) := by
  induction E with
  | nil => intro S cs pcs hR hp _; exact ⟨cs, hR, hp⟩
  | cons d E ih =>
    intro S cs pcs hR hp hG
    obtain ⟨cs', hR', hp'⟩ := step_spec hR hp hG
    exact ih _ cs' _ hR' hp' hG.cut

/-- The initial structure represents the single cycle `0 → 1 → ⋯ → n - 1`. -/
theorem repr_init {n : ℕ} (hn : 0 < n) : Repr ztqrr [List.range n] where
  nodup := by rw [List.flatten_singleton]; grind
  mem z := by rw [List.flatten_singleton, List.mem_range]; rfl
  cyc c hc := by
    zvojs at hc
    subst hc
    refine ztexr
    rw [List.length_range] at hi ⊢
    rw [Chazelle.EarClip.getD_range hi, Chazelle.EarClip.getD_range zthp]
    zubee
    show (ztg % n + n - 1) % n = i
    by_cases h : i + 1 < n
    · rw [Nat.mod_eq_of_lt h, show i + 1 + n - 1 = i + n by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    · rw [show i + 1 = n by omega, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt by_omega]
      omega
  cop v z := by
    show z ∈ ztetp ↔ z < n ∧ z = v
    simp_all
  copNodup v := by
    show (if v < n then [v] else []).Nodup
    grind

/-- **Main theorem of the linked splitting.**  For a simple polygon `P` and an enumeration `D`
of its inserted diagonals, the structure obtained by processing `D` from `initState P.n` with
`σ = orient P` represents cycles `cs` whose vertex lists are, up to order, exactly the pieces
`splitAll (List.range P.n) D`. -/
theorem runState_spec (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D) :
    ∃ cs, Repr (runState P ztqui zteag D) cs ∧
      List.Perm (cs.map (List.map (runState P ztqui zteag D).vtx))
        ztyrt := by
  have hn : ztbof := by have := Chazelle.Jordan.simple_three_le hP; omega
  have hmap : [List.range P.n].map (List.map (initState P.n).vtx) = [List.range P.n] := by
    simp only [List.map_cons, List.map_nil]
    zucr
    exact List.map_id' _
  obtain ⟨cs, hR, hp⟩ := runState_spec_gen (σ := orient P) D zteag _ _ (repr_init hn)
    by_simp_all (good_init hP hD)
  exact ⟨cs, hR, by rw [← seqSplit_eq_splitAll ztqpe]; exact hp⟩
end Run

/-! ### Reading the cycles -/
section Read

/-- Walk `k` steps along `nxt` from the node `z`. -/
def walk (S : LState) (z : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => z :: walk S ztvdc k
theorem walk_eq_map {S : LState} {c : List ℕ} (hc : IsCyc S c) (k : ℕ) :
    ∀ i < c.length, walk S ztcus k =
      (List.range k).map fun t => c.getD ((i + t) % c.length) 0 := by
  have hl := List.length_pos_iff.2 hc.1
  induction k with
  | zero => intro i _; rfl
  | succ k ih =>
    zug
    rw [walk, (hc.2 i hi).1, ih _ ztbpn, List.range_succ_eq_map, List.map_cons,
      List.map_map]
    zucr
    · simp only [Nat.add_zero, Nat.mod_eq_of_lt hi]
    zucfh
    intro t _
    simp only [Function.comp]
    rw [Nat.mod_add_mod, show i + 1 + t = i + ztbx by omega]

/-- **Walking a cycle from any of its nodes reads a rotation of it.** -/
theorem walk_eq_rotate {S : LState} {c : List ℕ} (hc : IsCyc S c) {i : ℕ} (hi : i < c.length) :
    walk S ztcus c.length = c.rotate i := by
  rw [walk_eq_map hc _ i hi]
  zuhrr
  · simp
  · zumhl
    zufay
    rw [List.getElem_rotate, ← Chazelle.EarClip.getD_eq_getElem_of_lt _ 0 _,
      Nat.add_comm]
end Read

/-! ### Rotations of pieces and the triangulation of the cycles -/
section Assemble
open Chazelle.Existence (WeakTriangulates relabel filled_rotate simple_rotate triangulates_of_weak)
open Chazelle.EarClip (relabelList subPoly_rotate weakTriangulates_rotate)
open Chazelle.Mountain (IsPieceEdge)

/-- **Pieces are closed under rotation.** -/
theorem isPiece_rotate {l : List ℕ} (h : IsPiece P l) (r : ℕ) : IsPiece P zteaj where
  nodup := List.nodup_rotate.2 h.nodup
  lt x hx := h.lt x (List.mem_rotate.1 hx)
  three_le := by rw [List.length_rotate]; exact h.three_le
  edges k hk := by
    rw [List.length_rotate] at hk ⊢
    have hl : ztmso := by_omega
    rw [getD_rotate_of_lt r hk, getD_rotate_of_lt r ztbpn]
    have e : (zts % l.length + r) % l.length = (zttqd % l.length + 1) % l.length := by
      grind
    zui
    exact h.edges _ ztbpn
  simple := by rw [subPoly_rotate]; exact simple_rotate _ _ h.simple
  not_boundary p hp := by
    rw [subPoly_rotate, filled_rotate] at hp; exact h.not_boundary p hp
  not_diag d hd p hp := by
    rw [subPoly_rotate, filled_rotate] at hp; exact h.not_diag d hd p hp
  filled_subset := by rw [subPoly_rotate, filled_rotate]; exact h.filled_subset

/-- **Triangulations are insensitive to the order of the triangles.** -/
theorem triangulates_perm {Q : Polygon} {T T' : List Polygon.Triangle} (h : Q.Triangulates T)
    (hp : List.Perm T T') : Q.Triangulates T' := by
  zubrk
  refine ⟨by_grind, by rw [← hp.length_eq]; exact h2, ?_,
    hp.pairwise h4 fun hd => hd.symm, hp.pairwise h5 by_grind⟩
  grind

/-- A list with pairwise disjoint nonempty "interiors" has no two rotation-equivalent members. -/
theorem pairwise_not_rotate_of_disj {pcs : List ztul}
    (hs : ∀ m ∈ pcs, (subPoly P m).Simple)
    (hd : pcs.Pairwise fun m m' =>
      Disjoint zthia zthhz) :
    pcs.Pairwise fun m m' => ∀ r, m' ≠ m.rotate r := by
  refine hd.imp_of_mem fun {m m'} hm _ hdisj r he => ?_
  obtain ⟨p, hp⟩ := interior_filled_nonempty (hs m hm)
  rw [he, subPoly_rotate, filled_rotate] at hdisj
  simp_all
end Assemble

/-! ### Cost -/
section Cost
variable {σ : ℝ}

/-- The number of wedge tests performed by the run, counted pessimistically as all the copies
of both endpoints at each step. -/
noncomputable def runCost (P : Polygon) (σ : ℝ) : LState → List ztw → ℕ
  | _, [] => 0
  | S, d :: D => (S.cop d.1).length + (S.cop d.2).length + runCost P σ ztcbd D

/-- One step adds one copy of each endpoint. -/
theorem length_cop_step (S : LState) {d : ℕ × ℕ} (_hd : d.1 ≠ d.2) (v : ℕ) :
    ((step P σ S d).cop v).length =
      (S.cop v).length + (if d.1 = v ∨ d.2 = v then 1 else 0) := by
  show (upd _ d.2 (ztdge :: S.cop d.2) v).length = _
  zuby
  grind

/-- **Cost bound.**  If every vertex has, together with its future incident diagonals, at most
`B` copies, then the run performs at most `2 B` wedge tests per diagonal. -/
theorem runCost_le {B : ℕ} : ∀ (D : List ztw) (S : LState), (∀ d ∈ D, d.1 ≠ d.2) →
    (∀ v, (S.cop v).length + D.countP (fun e => decide (e.1 = v ∨ e.2 = v)) ≤ B) →
    runCost P σ S D ≤ 2 * B * D.length := by
  intro D
  induction D with
  | nil => intro S _ _; simp [runCost]
  | cons d D ih =>
    intro S hne hB
    have hd := hne d List.mem_cons_self
    have h1 := hB d.1
    have h2 := hB d.2
    rw [List.countP_cons] at h1 h2
    have hrest := ih ztcbd by_grind (by
      zujbq
      rw [length_cop_step S hd v]
      grind)
    show (S.cop d.1).length + (S.cop d.2).length + runCost P σ _ D ≤ _
    simp only [true_or, or_true, decide_true, ite_true] at h1 h2
    rw [List.length_cons, show 2 * B * (D.length + 1) = 2 * B * D.length + 2 * B by ring]
    omega

/-- The copies in the initial structure: one per vertex `< n`. -/
theorem length_cop_init (n v : ℕ) : ((initState n).cop v).length ≤ 1 := by
  show (if v < n then [v] else []).length ≤ 1
  grind

/-- **The final-stage input enumerates the inserted diagonals.** -/
theorem enumDiags_diagList {T : TrapTable} {C : List ChordRec} (hP : P.Simple)
    (hT : IsTrapTable P T) (hC : IsVtxChordTable P C) : EnumDiags P (diagList P T C) where
  sound d hd := ((diagList_mem_iff hP hT hC d).1 hd).2
  complete d hd := by
    obtain ⟨h1, h2, hne⟩ := Chazelle.Mountain.allDiagonals_lt hP hd
    zubxx
    · exact Or.inl ((diagList_mem_iff hP hT hC d).2 by_simp_all)
    · exact Or.inr ((diagList_mem_iff hP hT hC d.swap).2
        by_simp_all)
  distinct := (diagList_nodup P T C).imp_of_mem fun {d d'} hd hd' hne => by
    refine ⟨hne, fun e => ?_⟩
    have h1 := (diagList_lt hP hT hC hd).1
    have h2 := (diagList_lt hP hT hC hd').1
    grind
end Cost

/-! ### The output: walking the final cycles -/
section Output
open Chazelle.Existence (WeakTriangulates)
open Chazelle.EarClip (relabelList)

/-- **Every cycle, walked from any of its nodes, is a piece.** -/
theorem isPiece_walk (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D) {S : LState}
    {cs : List ztul} (hR : Repr S cs)
    (hp : List.Perm ztghv ztyrt) {c : List ℕ}
    (hc : c ∈ cs) {i : ℕ} (hi : i < c.length) :
    IsPiece P ((walk S ztcus c.length).map S.vtx) := by
  rw [walk_eq_rotate (hR.cyc c hc) hi, List.map_rotate]
  exact isPiece_rotate (hD.isPiece hP by_grind) i
end Output

/-! ### Prefixes of the run and elementary invariants (used by the RAM simulation) -/
section Prefix
variable {σ : ℝ}
theorem runState_append (S : LState) (D D' : List ztw) :
    runState P σ S (D ++ D') = runState P σ (runState P σ S D) D' := by
  induction D generalizing S with
  | nil => rfl
  | cons d D ih => exact ih _
theorem cnt_step (S : LState) (d : ℕ × ℕ) : (step P σ S d).cnt = S.cnt + 2 := rfl
theorem cnt_runState (S : LState) (D : List ztw) :
    (runState P σ S D).cnt = S.cnt + 2 * D.length := by
  induction D generalizing S with
  | nil => simp
  | cons d D ih => rw [runState_cons, ih, cnt_step, List.length_cons]; ring
theorem runCost_cons (S : LState) (d : ℕ × ℕ) (D : List ztw) :
    runCost P σ S (d :: D) = (S.cop d.1).length + (S.cop d.2).length +
      runCost P σ ztcbd D := rfl

/-- **Closure**: the links of the nodes stay among the nodes, the copies are nodes, the vertices
are `< n`, and there is at least one node. -/
structure Closed (S : LState) (n : ℕ) : Prop where
  pos : 0 < S.cnt
  nxt : ∀ z < S.cnt, S.nxt z < S.cnt
  prv : ∀ z < S.cnt, S.prv z < S.cnt
  vtx : ∀ z < S.cnt, S.vtx z < n
  cop : ∀ v, ∀ z ∈ S.cop v, z < S.cnt
theorem closed_init {n : ℕ} (hn : 0 < n) : Closed ztqrr n where
  pos := hn
  nxt z _ := Nat.mod_lt _ hn
  prv z _ := Nat.mod_lt _ hn
  vtx z hz := hz
  cop v z hz := by
    show z < n
    have : z ∈ ztetp := hz
    simp_all
theorem selectLast_lt {p : ℕ → Bool} {l : List ℕ} {r N : ℕ} (hr : r < N) (hl : ∀ z ∈ l, z < N) :
    selectLast p l r < N := by
  induction l generalizing r with
  | nil => exact hr
  | cons a l ih =>
    zujlk
    zubfo
theorem findCopy_lt {S : LState} {n : ℕ} (hS : Closed S n) (v w : ℕ) :
    findCopy P σ S v w < S.cnt :=
  selectLast_lt hS.pos (hS.cop v)

/-- Closure passes through a step along a pair of vertices `< n`. -/
theorem Closed.step {S : LState} {n : ℕ} (hS : Closed S n) {d : ℕ × ℕ} (h1 : d.1 < n)
    (h2 : d.2 < n) : Closed ztcbd n := by
  zubcp

  have hpx := hS.prv _ hx
  have hny := hS.nxt _ hy
  refine ⟨by show 0 < S.cnt + 2; omega, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_,
    fun v z hz => ?_⟩
  · show upd _ _ _ z < S.cnt + 2
    zqoz
    · omega
    · omega
    · omega
    · omega
    · have := hS.nxt z by_omega; omega
  · show upd _ _ _ z < S.cnt + 2
    zqoz
    · omega
    · omega
    · omega
    · omega
    · have := hS.prv z by_omega; omega
  · show upd _ _ _ z < n
    zqoz
    · zucvi
    · zubvv
    · exact hS.vtx z by_omega
  · show z < S.cnt + 2
    have hz' : z ∈ upd _ d.2 _ v := hz
    zvmwf at hz'
    split_ifs at hz'
    · zujcp
      · omega
      · have := hS.cop _ z h; omega
    · zujcp
      · omega
      · have := hS.cop _ z h; omega
    · have := hS.cop _ z hz'; omega
end Prefix
end
end Chazelle.Final
end
namespace Chazelle.Final
@[expose] public section
open Set
open Chazelle.Split (splitAll EnumDiags)
open Chazelle.EarClip (subPoly n_subPoly relabelList subPoly_rotate weakTriangulates_rotate)
open Chazelle.Existence (WeakTriangulates relabel triangulates_of_weak)
open Chazelle.Mountain (IsPiece)
variable {P : Polygon}

/-- **Assembling a list of triangulated rotated pieces.**  Let `D` enumerate the inserted
diagonals, `M'` a permutation of the pieces `splitAll (List.range P.n) D`, and `acc` a list of
pairs `(m, T)` whose vertex lists `m` are, member by member, rotations of the members of `M'`
and with `T` a weak triangulation of `subPoly P m`.  Then the triangles, relabelled to original
indices, triangulate `P`. -/
theorem triangulates_of_pairs (hP : P.Simple) {D : List ztw} (hD : EnumDiags P D)
    {M' : List ztul} (hperm : List.Perm M' ztyrt)
    {acc : List ztpzo}
    (hrot : List.Forall₂ ztjwc M' acc)
    (hT : ∀ p ∈ acc, WeakTriangulates (subPoly P p.1) p.2) :
    P.Triangulates (acc.flatMap fun p => p.2.map (relabelList p.1)) := by
  classical
  have hG := (good_init hP hD).seqSplit
  rw [seqSplit_eq_splitAll ztqpe] at hG
  have hG' := hG.perm hperm.symm
  have hnd : M'.Nodup := (pairwise_not_rotate_of_disj hG'.simple hG'.disj).imp fun h e =>
    h 0 by_simp_all
  have hpiece : ∀ m' ∈ M', IsPiece P m' := fun m' hm' => hD.isPiece hP (hperm.mem_iff.1 hm')
  set g : List ℕ → List ℕ × List Polygon.Triangle := fun m' => acc.getD (M'.idxOf m') ([], [])
    with hg
  have hlen : M'.length = acc.length := hrot.length_eq
  have hMg : acc = M'.map g := by
    zuhrr
    · simp_all
    simp_all
  have hgmem : ∀ m' ∈ M', g m' ∈ acc := by
    grind
  have hgrot : ∀ m' ∈ M', ∃ r, (g m').1 = m'.rotate r := by
    zubxa
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hm'
    have := List.forall₂_iff_get.1 hrot
    grind
  set T' : List ℕ → List Polygon.Triangle := fun m' =>
    if h : ∃ r, (g m').1 = m'.rotate r then (g m').2.map (relabel (Classical.choose h) m'.length)
    else [] with hT'
  have hwT : ∀ m' ∈ M', WeakTriangulates (subPoly P m') (T' m') ∧
      (T' m').map ztwcr = (g m').2.map (relabelList (g m').1) := by
    zubxa
    have h := hgrot m' hm'
    have hr := Classical.choose_spec h
    set r := Classical.choose h
    have hw0 : WeakTriangulates (subPoly P (g m').1) (g m').2 := hT _ (hgmem m' hm')
    have hw : WeakTriangulates ((subPoly P m').rotate r) (g m').2 := by
      rw [← subPoly_rotate, ← hr]; omega
    have hw' := weakTriangulates_rotate _ r hw
    zvnnk at hw'
    have e : T' m' = (g m').2.map (relabel r m'.length) := by
      grind
    zuevy
    rw [e, List.map_map]
    zucfh
    zucj
    have hb := Chazelle.Split.index_lt_of_weak hw ht
    rw [Chazelle.Existence.n_rotate, n_subPoly] at hb
    zubpk
    simp only [Function.comp, relabelList, Chazelle.Existence.relabel_fst,
      Chazelle.Existence.relabel_snd_fst, Chazelle.Existence.relabel_snd_snd]
    rw [hr, getD_rotate_of_lt r hb.1, getD_rotate_of_lt r hb.2.1, getD_rotate_of_lt r hb.2.2,
      Nat.add_comm r t1, Nat.add_comm r t2, Nat.add_comm r t3]
  have heq : acc.flatMap ztmjv =
      M'.flatMap (fun m' => (T' m').map ztwcr) := by
    rw [hMg, List.flatMap_map]
    apply List.flatMap_congr
    grind
  zudab
  have hsplit : ∀ m ∈ splitAll ztbyp D, WeakTriangulates ztevt (T' m) :=
    fun m hm => (hwT m (hperm.mem_iff.2 hm)).1
  exact triangulates_perm (triangulates_of_weak (hD.weakTriangulates hP hsplit))
    (List.Perm.flatMap_right _ hperm.symm)
end
end Chazelle.Final
namespace Chazelle.Final
@[expose] public section
open Chazelle.Mountain
open Chazelle.EarClip (subPoly n_subPoly vtx_subPoly_getD relabelList subPoly_rotate
  getD_eq_getElem_of_lt getD_rotate)
open Chazelle.Existence (WeakTriangulates)

/-! ### Definitions -/

/-- The point at position `i` of the index list `l`. -/
noncomputable def ptAt (P : Polygon) (l : List ℕ) (i : ℕ) : Point := P.vtx (l.getD i 0)

/-- Position `i0` holds a `ylexLT`-minimal vertex of `l` (no vertex is strictly below it). -/
def IsMinPos (P : Polygon) (l : List ℕ) (i0 : ℕ) : Prop :=
  i0 < l.length ∧ ∀ j, j < l.length → ¬ ylexLT ztruq (ptAt P l i0)

/-- The list read forward from position `i0`: entry `j` is `l[(i0 + j) % m]`. -/
def fwdList (l : List ℕ) (i0 : ℕ) : List ℕ :=
  (List.range l.length).map (fun j => l.getD ztzzg 0)

/-- The list read backward from position `i0`: entry `j` is `l[(i0 + m - j) % m]`. -/
def bwdList (l : List ℕ) (i0 : ℕ) : List ℕ :=
  (List.range l.length).map (fun j => l.getD ztlcr 0)

/-- The direction test: the successor of position `i0` is `ylexLT`-below its predecessor. -/
def DirFwd (P : Polygon) (l : List ℕ) (i0 : ℕ) : Prop :=
  ylexLT (ptAt P l ((i0 + 1) % l.length)) (ptAt P l ((i0 + l.length - 1) % l.length))
open Classical in
/-- **The reoriented list**: forward from `i0` if `DirFwd`, backward otherwise. -/
noncomputable def reorient (P : Polygon) (l : List ℕ) (i0 : ℕ) : List ℕ :=
  if DirFwd P l i0 then fwdList l i0 else bwdList l i0

/-! ### Elementary list and index facts -/
theorem length_fwdList (l : List ℕ) (i0 : ℕ) : (fwdList l i0).length = l.length := by
  simp [fwdList]
theorem length_bwdList (l : List ℕ) (i0 : ℕ) : (bwdList l i0).length = l.length := by
  simp [bwdList]
theorem getD_fwdList (l : List ℕ) (i0 : ℕ) {j : ℕ} (hj : j < l.length) :
    (fwdList l i0).getD j 0 = l.getD ztzzg 0 := by
  simp [fwdList, List.getD_eq_getElem?_getD, hj]
theorem getD_bwdList (l : List ℕ) (i0 : ℕ) {j : ℕ} (hj : j < l.length) :
    (bwdList l i0).getD j 0 = l.getD ztlcr 0 := by
  simp [bwdList, List.getD_eq_getElem?_getD, hj]
theorem length_reorient (P : Polygon) (l : List ℕ) (i0 : ℕ) :
    (reorient P l i0).length = l.length := by
  unfold reorient; split_ifs
  · exact length_fwdList l i0
  · exact length_bwdList l i0

/-- Two lists of the same length with the same `getD` entries are equal. -/
theorem list_eq_of_getD {l₁ l₂ : List ℕ} (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  simp_all

/-- Reduction of `a % m` for `a < 2 m`. -/
theorem mod_of_lt_two_mul {a m : ℕ} (h : a < 2 * m) : a % m = if a < m then a else a - m := by
  zulsr
  · exact Nat.mod_eq_of_lt h'
  · zul

/-- Every residue `x < m` is `(j + r) % m` for some `j < m`, with `j = 0` iff `x = r`. -/
theorem exists_add_mod_eq {m r x : ℕ} (hr : r < m) (hx : x < m) :
    ∃ j, j < m ∧ ztobz % m = x ∧ (j = 0 ↔ x = r) := by
  by_cases h : r ≤ x
  · refine ⟨x - r, by_omega, ?_, by_omega⟩
    zupd
  · refine ⟨x + m - r, by_omega, ?_, by_omega⟩
    rw [mod_of_lt_two_mul by_omega, ite_eq_right by_omega]; omega

/-- The forward list from `i0` is the rotation by `i0`. -/
theorem fwdList_eq_rotate (l : List ℕ) (i0 : ℕ) : fwdList l i0 = l.rotate i0 := by
  apply list_eq_of_getD (by rw [length_fwdList, List.length_rotate])
  zun
  rw [length_fwdList] at hj
  rw [getD_fwdList l i0 hj, getD_rotate l i0 j hj, Nat.add_comm]

/-- The backward list from `i0 < m` is the reversal rotated by `m - 1 - i0`. -/
theorem bwdList_eq_reverse_rotate {l : List ℕ} {i0 : ℕ} (hi0 : i0 < l.length) :
    bwdList l i0 = l.reverse.rotate (l.length - 1 - i0) := by
  apply list_eq_of_getD (by rw [length_bwdList, List.length_rotate, List.length_reverse])
  zun
  rw [length_bwdList] at hj
  rw [getD_bwdList l i0 hj,
    getD_rotate l.reverse _ j by_simp_all, List.length_reverse,
    getD_reverse l ztcv]
  zucr
  rw [mod_of_lt_two_mul by_omega,
    mod_of_lt_two_mul by_omega]
  grind

/-! ### Transfer of weak triangulations -/

/-- Reversing the positions of a triangle in a list of length `m`. -/
def revTri (m : ℕ) (t : Polygon.Triangle) : Polygon.Triangle :=
  (m - 1 - t.1, m - 1 - t.2.1, m - 1 - t.2.2)
section transfer
variable (P : Polygon)

/-- The triangle `revTri m t` of `subPoly P l` has the vertices of `t` in `subPoly P l.reverse`. -/
theorem triVertices_revTri {l : List ℕ} {t : Polygon.Triangle}
    (h : t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length) :
    (subPoly P l).triVertices zttyw = (subPoly P l.reverse).triVertices t := by
  unfold Polygon.triVertices revTri
  rw [vtx_subPoly_reverse P l h.1, vtx_subPoly_reverse P l h.2.1, vtx_subPoly_reverse P l h.2.2]
theorem triSet_revTri {l : List ℕ} {t : Polygon.Triangle}
    (h : t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length) :
    (subPoly P l).triSet zttyw = (subPoly P l.reverse).triSet t := by
  unfold Polygon.triSet
  rw [triVertices_revTri P h]

/-- **Weak triangulations transfer along reversal**: a weak triangulation of
`subPoly P l.reverse` gives one of `subPoly P l` by reversing positions (`revTri`). -/
theorem weakTriangulates_subPoly_reverse {l : List ℕ} {T : List Polygon.Triangle}
    (hT : WeakTriangulates ztubh T) :
    WeakTriangulates ztdi (T.map (revTri l.length)) := by
  zueiy
  have hidx : ∀ t ∈ T, t.1 < l.length ∧ t.2.1 < l.length ∧ t.2.2 < l.length := by
    zucj
    zueil
    zugwo
    omega
  zuflw
  · zucj
    zurg

    obtain ⟨h1, h2, h3⟩ := hidx t' ht'
    obtain ⟨-, -, -, hdet⟩ := hvalid t' ht'
    refine ⟨by zvnnk; zunxd; omega,
      by zvnnk; zunxd; omega,
      by zvnnk; zunxd; omega, ?_⟩
    unfold revTri
    rw [← vtx_subPoly_reverse P l h1, ← vtx_subPoly_reverse P l h2,
      ← vtx_subPoly_reverse P l h3]
    omega
  · rw [n_subPoly, List.length_reverse] at hcount
    rw [List.length_map, n_subPoly]
    omega
  · rw [← filled_subPoly_reverse P l, ← hunion]
    zufj
    zuipb

    · zuekq
      exact ⟨t, ht, by rw [← triSet_revTri P by_grind]; exact hp⟩
    · zucjf
      exact ⟨_, ztbik, by rw [triSet_revTri P by_grind]; exact hp⟩
  · zuczn
    zuloj
    zubto
    rw [triSet_revTri P by_grind, triSet_revTri P by_grind]
    zubh
  · zukju
    zurg

    zvnnk at hi
    have e : (subPoly P l).vtx i = (subPoly P l.reverse).vtx (l.length - 1 - i) := by
      rw [vtx_subPoly_reverse P l by_omega]; congr 1; omega
    rw [e, triSet_revTri P by_grind] at hmem
    rw [e, triVertices_revTri P by_grind]
    exact hvert t' ht' _ (by rw [n_subPoly, List.length_reverse]; omega) hmem

/-- **Relabelled weak triangulations transfer along reversal of the index list.** -/
theorem goodTri_of_reverse {l : List ℕ} {T : List Polygon.Triangle}
    (h : GoodTri P l.reverse T) : GoodTri P l T := by
  obtain ⟨T', hT', rfl⟩ := h
  refine ⟨_, weakTriangulates_subPoly_reverse P hT', ?_⟩
  zuczm
  zucfh
  zucj
  obtain ⟨h1, h2, h3, -⟩ := hT'.1 t ht
  zugwo
  obtain ⟨a, b, d⟩ := t
  simp only [Function.comp, relabelList, revTri]
  grind

/-- **Relabelled weak triangulations transfer back along rotation of the index list.** -/
theorem goodTri_of_rotate {l : List ℕ} {r : ℕ} {T : List Polygon.Triangle}
    (h : GoodTri P zteaj T) : GoodTri P l T := by
  have := goodTri_rotate P h ztgkr
  rwa [rotate_rotate_cancel] at this

/-- **Transfer for the reoriented list**: a relabelled weak triangulation of
`reorient P l i0` (`i0 < m`) is a relabelled weak triangulation of `l`. -/
theorem goodTri_of_reorient {l : List ℕ} {i0 : ℕ} (hi0 : i0 < l.length)
    {T : List Polygon.Triangle} (h : GoodTri P ztlsu T) : GoodTri P l T := by
  unfold reorient at h
  zulsn
  · rw [fwdList_eq_rotate] at h
    exact goodTri_of_rotate P h
  · rw [bwdList_eq_reverse_rotate hi0] at h
    exact goodTri_of_reverse P (goodTri_of_rotate P h)
end transfer

/-! ### The minimum -/
section minimum
variable {P : Polygon} {l : List ℕ}
variable {r i0 : ℕ}
/-- **Case 1 of the mountain theorem** (the list rotated by `r` is a mountain): the minimum
position is `r`, the direction test is positive, and the forward list is that mountain list. -/
theorem mountain_case_rotate (hr : r < l.length)
    (hM : IsMountain ztzyc) (hmin : IsMinPos P l i0) :
    i0 = r ∧ DirFwd P l i0 ∧ fwdList l i0 = l.rotate r := by
  zukzs
  have hn : (subPoly P zteaj).n = m := by_simp_all
  zueqf
  have hv : ∀ j, j < m → (subPoly P zteaj).vtx j = ptAt P l (ztobz % m) := by
    zun
    rw [vtx_subPoly_getD P _ by_simp_all, getD_rotate l r j hj]
    rfl
  have hi0 : i0 = r := by
    zuct
    obtain ⟨j, hj, hjr, hj0⟩ := exists_add_mod_eq hr hmin.1
    have hjpos : ztpht := by
      omega
    have := ylexLT_of_lt _ hM hjpos by_omega
    rw [hv 0 by_omega, hv j hj, hjr, Nat.zero_add, Nat.mod_eq_of_lt hr] at this
    exact hmin.2 r hr this
  zufpy
  refine ⟨rfl, ?_, fwdList_eq_rotate l _⟩
  have := ylexLT_of_lt _ hM (i := 1) (j := m - 1) by_omega by_omega
  rw [hv 1 by_omega, hv ztfte by_omega] at this
  unfold DirFwd
  grind

/-- **Case 2 of the mountain theorem** (the reversed list rotated by `r` is a mountain): the
minimum position is `m - 1 - r`, the direction test is negative, and the backward list is that
mountain list. -/
theorem mountain_case_reverse (hr : r < l.length)
    (hM : IsMountain ztzyd) (hmin : IsMinPos P l i0) :
    i0 = l.length - 1 - r ∧ ¬ DirFwd P l i0 ∧ bwdList l i0 = l.reverse.rotate r := by
  zukzs
  have hn : (subPoly P ztmma).n = m := by
    simp_all
  zueqf
  have hv : ∀ j, j < m →
      (subPoly P ztmma).vtx j = ptAt P l (m - 1 - ztobz % m) := by
    zun
    rw [vtx_subPoly_getD P _ by_simp_all,
      getD_rotate l.reverse r j by_simp_all, List.length_reverse,
      getD_reverse l ztcv]
    rfl
  have hi0m := hmin.1
  have hi0 : i0 = m - 1 - r := by
    zuct
    obtain ⟨j, hj, hjr, hj0⟩ := exists_add_mod_eq (x := m - 1 - i0) hr by_omega
    have hjpos : ztpht := by
      omega
    have := ylexLT_of_lt _ hM hjpos by_omega
    rw [hv 0 by_omega, hv j hj, hjr, Nat.zero_add, Nat.mod_eq_of_lt hr,
      show m - 1 - (m - 1 - i0) = i0 by have := hmin.1; omega] at this
    exact hmin.2 _ by_omega this
  zufpy
  zuknv
  · have := ylexLT_of_lt _ hM (i := 1) (j := m - 1) by_omega by_omega
    rw [hv 1 by_omega, hv _ by_omega] at this
    zudqe
    unfold DirFwd at hd
    rw [← hm] at hd
    have e1 : (m - 1 - r + 1) % m = m - 1 - (m - 1 + r) % m := by
      rw [mod_of_lt_two_mul by_omega,
        mod_of_lt_two_mul by_omega]
      zuwd
    have e2 : (m - 1 - r + m - 1) % m = m - 1 - (1 + r) % m := by
      rw [mod_of_lt_two_mul by_omega,
        mod_of_lt_two_mul by_omega]
      zuwd
    zvmws at hd
    exact ylexLT_asymm this hd
  · rw [bwdList_eq_reverse_rotate by_omega, ← hm]
    grind

/-- The two cases of the mountain theorem, with the rotation reduced below `m`. -/
theorem mountain_cases (hmount : ∃ s, IsMountain ztden ∨
      IsMountain ztdeo) (h0 : 0 < l.length) :
    ∃ r, r < l.length ∧
      (IsMountain ztzyc ∨ IsMountain ztzyd) := by
  zugqs
  · refine ⟨s % l.length, Nat.mod_lt _ h0, Or.inl ?_⟩
    rw [List.rotate_mod, subPoly_rotate]; exact h
  · refine ⟨s % l.length, Nat.mod_lt _ h0, Or.inr ?_⟩
    have e : l.reverse.rotate zttza = l.reverse.rotate s := by
      rw [← List.length_reverse, List.rotate_mod]
    rw [e, subPoly_rotate]; exact h

/-- **The reoriented list is a monotone mountain**: from any minimum position `i0` of a piece
whose vertex list is a rotated (possibly reversed) mountain, `reorient P l i0` lists the piece
in strictly increasing `ylexLT` order. -/
theorem isMountain_reorient (hmount : ∃ s, IsMountain ztden ∨
      IsMountain ztdeo) {i0 : ℕ} (hmin : IsMinPos P l i0) :
    IsMountain (subPoly P ztlsu) := by
  obtain ⟨r, hr, hM | hM⟩ := mountain_cases hmount (by have := hmin.1; omega)
  · obtain ⟨-, hd, he⟩ := mountain_case_rotate hr hM hmin
    zumue
    simp_all
  · obtain ⟨-, hd, he⟩ := mountain_case_reverse hr hM hmin
    zumue
    simp_all

/-- **The abstract piece triangulator**: on a piece given as a rotated (possibly reversed)
mountain, with `i0` a minimum position, any relabelled weak triangulation of the reoriented
mountain `reorient P l i0` is a relabelled weak triangulation of the piece. -/
theorem goodTri_piece_of_mountain {i0 : ℕ} (hmin : IsMinPos P l i0)
    {T : List Polygon.Triangle} (h : GoodTri P ztlsu T) : GoodTri P l T :=
  goodTri_of_reorient P hmin.1 h
