module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvXRamH
public import Chazelle.Core.RestoreTPos
public import Chazelle.Core.ShotListCut
public import Chazelle.Core.SweepChainT

namespace Chazelle.Core
namespace ShotListG
open Machine Machine.Stmt Programs SignK SweepPrim ShotList
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
@[expose] public section
def candList (R : ℕ) : List ztw := [ztqbw, ztqbx]

/-- Accept the candidate. -/
def leafAccG (R : ℕ) : Stmt :=
  .seq ztyva (block (copies [zthcc, zthcd]))

/-- The bits `cand < best` (`R + 246`) and `best < cand` (`R + 247`) of the abscissae. -/
def leafCmpG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (R : ℕ) : Stmt :=
  .seq (xc ztbme ztbpp ztbjl ztbyz) (.seq (.instr (.copyN ztbtr 50210))
    (.seq (xc ztbjl ztbyz ztbme ztbpp) (.instr (.copyN ztces 50210))))

/-- Accept if the candidate comes first along the ray. -/
def leafDecG (R : ℕ) : Stmt :=
  .ifLtN ztgx ztbgt (.ifLtN ztgx ztbtr ztkae .skip)
    (.ifLtN ztgx ztces ztkae .skip)

/-- A hit: accept it if there is no minimum yet, else compare. -/
def leafHitG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (R : ℕ) : Stmt :=
  .seq (block (copies ztvla))
    (.ifLtN ztpa zthl ztkae (.seq ztocu (leafDecG R)))

/-- **The leaf**: one shot at the piece of level `3`, and the running minimum. -/
def leafG (xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : Stmt :=
  .seq ztqsw (.seq sh (.ifLtN zthl 140010 .skip (.ifLtN 140010 zthl .skip
    zttry)))

/-! ## Execution of the blocks -/
variable {P : Polygon} {W : ℕ} {R : ℕ} {M : Model}
/-- **Accepting the candidate.** -/
theorem leafAccG_exec (c : Config) (hw : WordsBounded W c)
    (hW : 1 ≤ W) :
    ∃ c' k, Exec P W ztkae c c' k ∧ k = 3 ∧ c'.nreg ztpa = 1 ∧
      c'.nreg ztbjl = c.nreg ztbme ∧ c'.nreg ztbyz = c.nreg ztbpp ∧
      FrameB ztxxa c c' := by
  zuban

  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) [zthcc, zthcd] c₁
    e₁.wb_right (by
      simp)
    by_simp
  zvmwt at v₂
  obtain ⟨a1, a2⟩ := v₂
  refine ⟨c₂, _, .seq e₁ e₂, rfl, ?_, by_simp_all, by_simp_all,
    ?_⟩
  · rw [f₂.1 _ by_simp, hc₁]; simp
  · have fa : FrameB ztxxa c c₁ :=
      frameB_mono (exec_frameB e₁ (show wr ztbadw _ = true by
        zumym)) (fun r hr => by zvnih at hr; simp_all)
    have fb : FrameB ztxxa c₁ c₂ :=
      frameB_mono f₂ by_simp_all
    exact fa.trans fb

/-- The write set of `leafCmpG`. -/
def BcmpG (R : ℕ) (Bx : ℕ → Bool) (r : ℕ) : Bool := decide ztjlv || Bx r

/-- **Comparing the abscissae** of the candidate (`R + 244`, `R + 245`) and of the minimum
(`R + 21`, `R + 22`). -/
theorem leafCmpG_exec {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    (hpc : ProperPos M zta P.n ztxat)
    (hec : c.nreg ztbme < M.W.n)
    (hpb : ProperPos M zta P.n ztuw)
    (heb : c.nreg ztbjl < M.W.n)
    (hy : (M.pos zta ztxat).2 =
      (M.pos zta ztuw).2)
    (hY : Y (M.pos zta ztxat).2)
    (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W ztocu c c' k ∧ k ≤ 2 * K + 2 ∧
      BitIs c' ztbtr ((M.pos zta ztxat).1 <
        (M.pos zta ztuw).1) ∧
      BitIs c' ztces ((M.pos zta ztuw).1 <
        (M.pos zta ztxat).1) ∧
      FrameB ztfnd c c' := by
  zubwa
  have iB : ∀ i, i < 300 → InB R ztly := fun i hi => ztgy
  -- first comparison
  obtain ⟨c₁, k₁, e₁, hk₁, b₁, f₁⟩ := hx ztbme ztbpp ztbjl ztbyz ztduz
    ztduz ztduz ztduz c hw hctx hpc hec hpb heb hy hY hroom
  have e₂ := Exec.copyN (P := P) e₁.wb_right ztbtr 50210
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg _ _ } with hc₂
  zue
  have kR1 := fun r h1 h2 =>
    f₁.1 r (opW_R hBx hR h1 h2)
  have keep2 : ∀ r, R ≤ r → r < R + 300 → r ≠ R + 246 → c₂.nreg r = c.nreg r :=
    by simp_all
  have hA2 : ztbae := by
    zumxp; zundi
    exact f₁.1 _ (opW_alloc hBx)
  have F12 : FrameB ztfnd c c₂ := by
    have g1 : FrameB ztfnd c c₁ := frameB_mono f₁ ztjwg
    have g2 : FrameB ztfnd c₁ c₂ := frameB_mono (exec_frameB e₂
      (show wr ztbadu _ = true by
        zumym)) (fun r hr => by
          zvnih at hr; subst hr; zupbn)
    exact g1.trans g2
  have ctx₂ := KCtx.of_frameB hR hBo hS hctx w₂ F12 (fun r hr => by
    zuggo
    zubbc
    · omega
    · exact Or.inr ztoxl)
  -- second comparison
  have q := fun i (hi : i < 300) (hne : i ≠ 246) => keep2 ztly by_omega by_omega by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, b₃, f₃⟩ := hx ztbjl ztbyz ztbme ztbpp ztduz
    ztduz ztduz ztduz c₂ w₂ ctx₂
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    by_simp_all
    by_omega
  rw [q 21 by_omega by_omega, q 22 by_omega by_omega, q 244 by_omega by_omega,
    q 245 by_omega by_omega] at b₃
  have e₄ := Exec.copyN (P := P) e₃.wb_right ztces 50210
  have ex : Exec P W ztocu c _ _ := .seq e₁ ztcb
  refine ztink
  · -- the first bit survives
    have b2 : BitIs c₂ ztbtr ((M.pos _ zteyb).1 <
        (M.pos _ zteyb).1) :=
      ⟨by zumxp; zumwv; exact b₁.1,
        by zumxp; zumwv; exact b₁.2⟩
    refine b2.of_eq ?_
    zudcj
    exact f₃.1 _ (opW_R hBx hR by_omega by_omega)
  · exact ⟨by zumwv; exact b₃.1, by zumwv; exact b₃.2⟩
  · have g3 : FrameB ztfnd c₂ c₃ := frameB_mono f₃ ztjwg
    have g4 : FrameB ztfnd c₃ _ := frameB_mono (exec_frameB e₄
      (show wr ztbadv _ = true by
        zumym)) (fun r hr => by
          zvnih at hr; subst hr; zupbn)
    exact F12.trans (g3.trans g4)

/-! ## The running minimum after one hit -/

/-- The write set of `leafHitG`. -/
def BhitG (R : ℕ) (Bx : ℕ → Bool) (r : ℕ) : Bool :=
  decide ztbea || decide ztctn || Bx r
theorem wrG_hit {Bx : ℕ → Bool} (hBx : OpW Bx) : WrG R ztjgw := fun r hr => by
  zuggq
  zugrv
  · omega
  · omega
  · exact Or.inr ztoxl

/-- **A hit updates the running minimum.** -/
theorem leafHitG_exec {R : ℕ} (hR : RegsOK R)
    {E : Config → Prop} {Bo : Finset ℕ} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : KCtx P W M R E c)
    {S A : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (he : c.nreg 140011 < M.W.n)
    (hp : ProperPos M zta P.n ztdqm)
    (hpos : M.pos zta ztdqm = rayPt z σ t)
    (hz : Y z.2) (hσb : BitIs c ztbgt ztwyb) (hσ : σ = dirOf ztxnk)
    (hbest : BestG P M R c S z σ) (hroom : c.nreg ALLOC + K ≤ W) :
    ∃ c' k, Exec P W zttry c c' k ∧ k ≤ 2 * K + 20 ∧ BestG P M R c' ztjmc z σ ∧
      FrameB ztjgw c c' := by
  zubwa
  obtain ⟨-, -, hHW, -, -, h30, h31, -⟩ := id hctx
  have hkc : (candList R).length = 2 := rfl
  obtain ⟨c₁, e₁, v₁, f₁⟩ := copies_run (P := P) ztvla c hw (by
    simp only [candList, List.mem_cons, List.not_mem_nil, or_false]
    grind)
    (by simp [candList])
  simp only [candList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  obtain ⟨p44, p45⟩ := v₁
  have k1 : ∀ r, r ≠ R + 244 → r ≠ R + 245 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    f₁.1 r (by simp [candList, h1, h2])
  have hA1 : ztdc := k1 _ ztu ztu
  have best₁ : BestG P M R c₁ S z σ := hbest.congr by_simp_all
    by_simp_all by_simp_all
  zud
  have fB : ∀ {B : ℕ → Bool} {c₀ c' : Config}, FrameB B c₀ c' → (∀ r, B r = true → BhitG R Bx r) →
      FrameB _ c₀ c' := frameB_mono
  have f₁' : ztukw := fB f₁ (fun r hr => by
    simp [candList] at hr; zunfn; omega)
  have ctx₁ := KCtx.of_frameB hR hBo hS hctx w₁ f₁' (wrG_hit hBx)
  -- the acceptance
  have accept : ∀ (cc : Config), WordsBounded W cc → FrameB ztjgw c cc →
      cc.nreg ztbme = c.nreg 140011 → cc.nreg ztbpp = c.nreg 140012 →
      ztgeh →
      ∃ c' k, Exec P W ztkae cc c' k ∧ k = 3 ∧ BestG P M R c' ztjmc z σ ∧
        FrameB ztjgw c c' := by
    intro cc hcc fcc h44 h45 hS'
    obtain ⟨c', k, ex, hk, a0, a1, a2, fa⟩ := leafAccG_exec (P := P) (R := R) cc hcc (by
      unfold hostWords at hHW; omega)
    refine ⟨c', k, ex, hk, ⟨by rw [a0], fun _ => ⟨t, ?_, ?_, ?_, ?_⟩, fun h' => absurd a0 h'⟩,
      fcc.trans (fB fa (fun r hr => by
        zucy
        zunfn; omega))⟩
    · rcases hS' with hS' | ⟨tb, htb, hle⟩
      · exact firstHit_union_right hS' hA
      · zulfc
    · grind
    · omega
    grind
  zuefz

  · -- no minimum yet
    zulkw
    obtain ⟨c', k, ex, hk, hb, fr⟩ := accept c₁ w₁ f₁' p44 p45 ztvcb
    exact ztgoi
  -- compare with the minimum
  zufur
  obtain ⟨tb, htb, hpb, heb, hposb⟩ := best₁.2.1 hf1
  have hyc : (M.pos zta ⟨c₁.nreg ztbme, c₁.nreg ztbpp⟩).2 = z.2 := by
    rw [p44, p45, hpos]; simp
  have hyb : (M.pos zta ⟨c₁.nreg ztbjl, c₁.nreg ztbyz⟩).2 = z.2 := by
    rw [hposb]; simp
  obtain ⟨c₂, k₂, e₂, hk₂, b46, b47, f₂⟩ := leafCmpG_exec (P := P) hR hBo hS hx hBx c₁ w₁ ctx₁
    by_grind by_omega hpb heb by_grind
    by_grind by_omega
  rw [p44, p45, hpos, hposb] at b46 b47
  have k2 : ztgqd := fun r h1 h2 =>
    f₂.1 r (by simp only [BcmpG, opW_R hBx hR h1 by_omega, Bool.or_false,
      decide_eq_false_iff_not]; omega)
  have f₂' : ztukx := f₁'.trans (fB f₂ (fun r hr => by
    zuggo
    zubuj
    · zunfn; omega
    · simp [BhitG, h]))
  -- keeping the minimum
  have keep : tb ≤ t → BestG P M R c₂ _ z σ := fun hle => by
    refine ⟨by zuogg; omega, fun _ => ⟨tb, ?_, ?_, ?_, ?_⟩,
      fun h' => absurd ztkua h'⟩
    · zulfb
    · zuemj
    · zuhmt
    · zuemj
  have r35 : ztzpw := by
    zufnv
  have r30 : ztbacr := by
    zuemi
  have h44 : c₂.nreg ztbme = c.nreg 140011 := by rw [k2 _ by_omega by_omega, p44]
  have h45 : c₂.nreg ztbpp = c.nreg 140012 := by rw [k2 _ by_omega by_omega, p45]
  zue
  zubws

  · -- `σ = 1`: accept iff `xc < xb`
    zubob

    zucry
    zudkf

    · zudze
      zuchr
      exact ⟨c', _, .seq e₁ ztgws,
        by omega, hbest', fr⟩
    · have hge : ztpqd := by
        zubqk
        zudmn
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_true hs (.ifLtN_false hb
        ztbun)))), by_omega, keep hge, f₂'⟩
  · -- `σ = -1`: accept iff `xb < xc`
    zuuf

    zucry
    zudke

    · zudzf
      zuchr
      exact ⟨c', _, .seq e₁ ztgwr,
        by omega, hbest', fr⟩
    · have hge : ztpqd := by
        zubqk
        zudmo
      exact ⟨c₂, _, .seq e₁ (.ifLtN_false hf (.seq e₂ (.ifLtN_false hs (.ifLtN_false hb
        ztbun)))), by_omega, keep hge, f₂'⟩

/-! ## The leaf with the shooter -/

/-- **One shot at the piece of level `3`**: the running minimum extends to the piece. -/
theorem leafG_exec {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh : ShooterOKE sh Bs F X Ok) (hBs : Bs ⊆ Bo)
    (hXl : X.CapLocal) {P : Polygon} {W : ℕ} {M : Model} {R : ℕ} (hR : RegsOK R)
    (hRB : bandOf R ∉ Bo) {E : Config → Prop} (hBo : oracleBands ⊆ Bo) (hS : Stable Bo W R E)
    {Y : ℝ → Prop} {xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bx : ℕ → Bool} {K : ℕ} (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config)
    (hw : WordsBounded W c) (hctx : ShotCtxG P W X Ok R M E c)
    (hp1 : ProperPos M zta P.n (pieceR c ztmp).1)
    (hp2 : ProperPos M zta P.n (pieceR c ztmp).2)
    (he1 : (pieceR c ztmp).1.edge < M.W.n) (he2 : (pieceR c ztmp).2.edge < M.W.n)
    (hi1 : (pieceR c ztmp).1.hgt = 0 ∨ M.InnerPt (M.pos zta (pieceR c ztmp).1))
    (hi2 : (pieceR c ztmp).2.hgt = 0 ∨ M.InnerPt (M.pos zta (pieceR c ztmp).2))
    (hwt : M.arcWt ztxge ztxgf ≤
      c.nreg ztbmf)
    {o : Origin} (ho : OriginIn c ztbza o) (hol : o.Lt P.n M)
    (hof : ztbnw ∨ (M.InnerPt ztwle ∧
      ∀ x, o = .walk x → ProperPos M zta P.n x))
    (hon : o.eval M zta ∉ M.arcSet ztxge
      ztxgf)
    (hoy : Y (o.eval M zta).2) {S : Set Point}
    (hbest : BestG P M R c S ztwle ztwkv)
    (hroom : c.nreg ALLOC + F ztkx + ztptr ≤ W) :
    ∃ c' k, Exec P W (leafG xc sh R) c c' k ∧ k ≤ F ztkx + ztptr ∧
      BestG P M R c' (S ∪ M.arcSet ztxge
        ztxgf) (o.eval M (Qof P)) (dirOf (c.nreg (R + 6))) ∧
      FrameR Bo ztxqx c c' k := by
  zubwa
  zurm

  -- the shooter's inputs

  simp only [setList, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₁
  zubuc
  have k1 := fun r hr =>
    f₁.1 r ztnuz
  zucao

  zumdg
  obtain ⟨⟨hE, hG, hHW, hMD, hmwf, h30, h31, h34⟩, hX, hcap, hOk, hσb, hreg⟩ := hctx0
  have hO1 : ztyyi := by
    zudss
    · exact s5
    · exact s6
    omega
  -- the shot
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, fr₂⟩ := hsh P W c₁ e₁.wb_right
    ⟨hG, hHW, by zuntt; exact hX,
      by zunnb; omega,
      by zuntu; omega, by rw [rd_shoot, s0, hM1]; exact hreg, M,
      by rw [rd_shoot, s0, hM1]; omega, hOk,
      by zunah; exact hp1, by zunai; exact hp2,
      by zuoob; exact he1, by zuooc; exact he2,
      by zunah; exact hi1, by zunai; exact hi2,
      by zunch; exact hwt,
      o, hol, hO1, hof, by zuneq; exact hon⟩
    ztezq
  replace hk₂ : k₂ ≤ F ztkx := by
    zudhc

  zubbp

  -- registers of the caller's block survive the shot
  have hR2 : ztkog := fun i hi => by
    rw [fr₂.1 _ (fun hb => band_RB hR hRB hi ztvsp) ztu, hR1 i hi]
  have F01 : FrameR Bo ztbvx c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
    right; simp [setList] at hr; exact hBo (band_shoot by_omega)) by_rfl _
  have F12 : FrameR Bo ztbvx c₁ c₂ k₂ :=
    (FrameR.of_frame fr₂).mono hBs ztb le_rfl
  zulgy
  zue
  have ctx₂ :=
    ShotCtxG.frame hXl hS hctx w₂ F02 by_grind ztnyx
  have best₂ := hbest.congr zttmt zttmu
    zttmv
  have hA2 : ztyui := by
    have := F12.2.2.2.2.2.2; omega
  have Fw : ∀ {cc cc' : Config} {kk : ℕ}, FrameR Bo ztbvx cc cc' kk →
      FrameR Bo ztxqx
        cc cc' kk := fun hf => hf.mono le_rfl by_grind le_rfl
  zuefy
  -- no hit
  have nohit : c₂.nreg 140010 ≠ 1 → BestG P M R c₂ _ z σ := fun hne => by
    zucru

  zuhsd
  · refine ⟨c₂, _, .seq e₁ ztyog, by_omega,
      nohit by_omega, ?_⟩
    zuhcl
  zuhsf
  · refine ⟨c₂, _, .seq e₁ ztxuf, by_omega,
      nohit by_omega, ?_⟩
    zuhcl
  -- a hit
  zucmd

  obtain ⟨c₃, k₃, e₃, hk₃, best₃, f₃⟩ := leafHitG_exec (P := P) hR hBo hS hx hBx c₂ w₂ ctx₂.1 htA
    hpe hpp hpos hoy ctx₂.2.2.2.2.1 ztntn best₂ by_omega
  refine ztedq
  have F23 : FrameR Bo ztxqx
      c₂ c₃ k₃ := FrameR.of_frameB f₃ (fun r hr => by
    zuggq
    rcases hr with (h' | h') | h'
    · omega
    · omega
    · exact Or.inr (hBo (hBx r h').1)) ((wrG_hit hBx).alloc hR) _
  exact ((Fw F02).trans F23).mono le_rfl by_omega by_omega
end
end ShotListG
end Chazelle.Core
namespace Chazelle.Core
namespace ShotListG
open Machine Machine.Stmt Programs SignK SweepPrim ShotList
@[expose] public section
def levFG (kc xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : ℕ → ℕ → Stmt
  | 0, _ => leafG xc sh R
  | f + 1, ℓ => .seq ztlmk (.ifLtN ztgx ztsj
      (.seq ztxkx (.ifLtN zthl ztsj
        (.seq ztzdm ztxkx) .skip)) .skip)

/-- The cost of one node of the recursion: a shot and two abscissa comparisons, or a cut. -/
def nodeG (Fg K : ℕ) : ℕ := Fg + 2 * K + 1000

/-- The cost of `f` levels. -/
def levCostG (G f : ℕ) : ℕ := ztzba * G
theorem levCostG_succ (G f : ℕ) : levCostG G ztbax = 2 * levCostG G f + G := by
  unfold levCostG
  zubvy
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
    (hof : ztbnw ∨ (M.InnerPt ztwle ∧
      ∀ x, o = .walk x → ProperPos M zta P.n x))
    (hoy : Y (o.eval M zta).2) :
    ∀ (f ℓ : ℕ) (c : Config) (S : Set Point), f + ℓ = 3 → WordsBounded W c →
      ShotCtxG P W X Ok R M E c → OriginIn c ztbza o →
      PieceOK M zta P.n ztxeg →
      (∀ j, ℓ ≤ j → j < 3 → c.nreg ztqbz < c.nreg ztnx →
        c.nreg ztbyx < M.W.n ∧ c.nreg ztbyy < M.W.n) →
      (∀ p ∈ levLeaves M zta c R f ℓ ztxeg,
        M.arcWt ztzty ztztz ≤ c.nreg ztbmf ∧
        o.eval M zta ∉ M.arcSet ztzty ztztz) →
      BestG P M R c S ztwle ztwkv →
      c.nreg ALLOC + levCostG ztbaoa f ≤ W →
      ∃ c' k, Exec P W (levFG kc xc sh R f ℓ) c c' k ∧
        k ≤ levCostG ztbaoa f ∧
        BestG P M R c' (S ∪ pcSet M zta (levLeaves M zta c R f ℓ ztxeg))
          ztwle ztwkv ∧
        FrameR Bo ztfov c c' k
  | 0, ℓ, c, S, hf, hw, hctx, ho, hpc, _, hleaf, hbest, hroom => by
    zunz

    rw [levCostG_zero] at hroom ⊢
    unfold nodeG at hroom ⊢
    obtain ⟨c', k, ex, hk, hb, fr⟩ := leafG_exec hsh hBs hXl hR hRB hBo hS hx hBx c hw hctx n1.1 n2.1
      e1 e2 i1 i2 hwt ho hol hof hon hoy hbest by_omega
    refine ztxpg
    · zugzl
    · zubbc
      · zuleg
      · right; omega
  | f + 1, ℓ, c, S, hf, hw, hctx, ho, hpc, hholes, hleaf, hbest, hroom => by
    zuiay
    zubdp
    zubep
    have hlc := levCostG_succ ztbaoa f
    have hKG : K + 900 ≤ nodeG ztwui K := by unfold nodeG; omega
    set G := nodeG ztwui K with hG
    zuenc

    have hkctx := hctx.1
    have hHW := hkctx.2.2.1
    zudro
    -- the cut
    obtain ⟨c₁, k₁, e₁, hk₁, pc₁, f₁⟩ := cutBG_exec (P := P) hR hℓ hBo hS hk hBk c hw (by
      omega) hkctx by_omega na nb ea eb
    set ps := levPieces M Q ztwrw q.1 q.2
      ztxwe ztxwf with hps
    have k1 : ztfxj := fun r h1 h2 => f₁.1 r (by
      have hbk := opW_R hBk hR h1 by_omega
      unfold rL at h2
      cases hb : BcutG R ℓ Bk r
      · rfl
      · exfalso
        simp only [BcutG, BoffG, Bool.or_eq_true, beq_iff_eq] at hb
        rcases hb with ((h' | h' | h') | h') | h'
        · have := bouts_range h'; omega
        · omega
        · grind
        · simp only [Bform, decide_eq_true_eq] at h'; omega
        grind)
    have wc := wrG_cut (R := R) hℓ hBk
    have hA1 := f₁.1 _ ztwhu
    have F01 : FrameR Bo ztfov c c₁ k₁ := FrameR.of_frameB f₁ (fun r hr => by
      zufap
      rcases hr with ((hr | hr | hr) | hr) | hr
      · have := bouts_range hr; left; right; omega
      · zuetn
      · exact Or.inr (hBo (hBk r hr).1)
      · simp only [Bform, decide_eq_true_eq] at hr; left; right; omega
      · zvmwo at hr; left; right; omega)
      ztwhu _
    have toS : ∀ r, WrLev R ℓ r → R + 9 ≤ r ∧ r < R + 300 := fun r hr => by
      unfold WrLev rL at hr; omega
    have ctx₁ := ShotCtxG.frame hXl hS hctx e₁.wb_right F01 toS
      ztmjs
    have ho₁ : ztulv := originIn_copy ho ztbdg
      ztbdg ztbdg
    zuddn

    have best₁' : BestG P M R c₁ S _ _ :=
      hbest.congr ztbdg
        ztbdg ztbdg
    have hlv : ∀ (c' : Config), (∀ i, ztbje ∨ ztbjd →
        c'.nreg _ = c.nreg _) → ∀ p, levLeaves M Q c' R f _ p =
          levLeaves M Q c R f _ p := fun c' h' =>
      levLeaves_congr M Q h' f ztmv by_omega
    zukdb
    -- the pieces are good
    have hgood : ztlzb := by
      zuda
      zuhti
      · zuden

      · zucqz

    zufjr
    zud
    have z₁ : c₁.nreg _ = 0 := ctx₁.1.2.2.2.2.2.1
    have o₁ : c₁.nreg _ = 1 := ctx₁.1.2.2.2.2.2.2.1
    -- the recursive call on a piece in the registers of level `ℓ + 1`
    have call : ∀ (cc : Config) (S' : Set Point) (p : WPos × WPos), p ∈ ps → WordsBounded W cc →
        ShotCtxG P W X Ok R M E cc → OriginIn cc ztbza o →
        (∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
          cc.nreg ztly = c.nreg ztly) →
        pieceR cc ztxxv = p →
        BestG P M R cc S' ztfto ztwkv →
        cc.nreg ALLOC + levCostG G f ≤ W →
        ∃ c' k, Exec P W ztxkx cc c' k ∧ k ≤ levCostG G f ∧
          BestG P M R c' ztxkk ztfto
            ztwkv ∧ FrameR Bo ztzuy cc c' k := by
      zubjf

      obtain ⟨c', k, ex, hk', hb, fr⟩ := levG_exec hsh hBs hXl hR hRB hBo hS hk hBk hx hBx hol hof hoy
        f ztmv cc S' by_omega hwc hcc hoc ztktr
        (fun j hj1 hj2 hj3 => by
          zujxk
          zume

          grind)
        (fun p' hp' => by
          zuikj
          have := hleaf p' ztheu
          grind)
        by_grind by_grind
      rw [e7] at hk'
      zugvi
      exact ⟨c', k, ex, hk', hb, fr⟩
    zuegu

    have hp0' : ztfld := fun p hp => by
      zuhni
    zukeo
    have regs1 : ∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
        c₁.nreg _ = c.nreg ztly := fun i hi =>
      k1 _ by_omega by_omega
    have wr1 : ztyad := fun r hr => by
      zubbc
      · zulei
      · zuhjh
    zumnm
    have hroom1 : c₁.nreg ALLOC + levCostG G f ≤ W := by_omega
    cases hcase : ps with
    | nil =>
      zuctq

      refine ⟨c₁, _, .seq e₁ ztzrn, by_omega, ?_, F01.mono le_rfl
        ztb by_omega⟩
      zuggz

    | cons p₀ t =>
      zuehd
      have g0 : ztzpu := by
        zugxl
      obtain ⟨c₂, k₂, e₂, hk₂, b₂, fr₂⟩ := call c₁ S p₀ hp0m w₁ ctx₁ ho₁ regs1
        ztjyb best₁' hroom1
      have kp2 : ztgqb :=
        fun i hi hw' => fr₂.1 _ ztrku (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw'
      have o₂ : ztygq := by
        zuhmy
      have cn₂ : ztzpz := by
        have := kp2 ztelj by_omega ztpq
        zucka
      zue
      cases ht : t with
      | nil =>
        zuccc

        refine ⟨c₂, _, .seq e₁ ztxud,
          by omega, ?_, (F01.trans ztrpn).mono le_rfl ztb
            by_omega⟩
        zuggy

      | cons p₁ t' =>
        have ht' : ztuuz := by
          have := hlen'; rw [hcase, ht] at this; simp only [List.length_cons] at this
          exact List.length_eq_zero_iff.1 by_omega
        zuuk

        -- the second piece into the registers of level `ℓ + 1`
        obtain ⟨c₃, e₃, v₃, f₃⟩ := copies_run (P := P) ztjsw c₂ w₂ (by
          zughm
          simp)
          ztqfk
        simp only [copy2List, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] at v₃
        zufla
        have k3 : ztebk :=
          fun r hr => f₃.1 r ztnur
        have F23 : FrameR Bo ztfov c₂ c₃ 4 := FrameR.of_frameB f₃ (fun r hr => by
          simp [copy2List] at hr; left; right; omega)
          ztljp _
        have F13 : FrameR Bo _ c₁ c₃ _ :=
          (fr₂.mono le_rfl wr1 le_rfl).trans F23
        have regs3 : ∀ i, ztbje ∨ ztbjd ∨ i = 6 ∨ i = 7 →
            c₃.nreg ztly = c.nreg _ := fun i hi => by
          rw [k3 _ by_omega, kp2 i by_omega ztpq,
            regs1 i hi]
        have ctx₃ : ShotCtxG P W X Ok R M E c₃ := ShotCtxG.frame hXl hS ctx₁ e₃.wb_right F13 toS
          (fun i hi => by
            zunql)
        have kk : ztxzz := fun i hi => by
          zufnw
        have ho₃ : ztbacc := by
          zuknn
          · zucty
          · zuctz
        have hpc₃ : ztbaqw := by
          zujy

          zufex

          zuez

          zucpn

        have best₃ : BestG P M R c₃ _
            _ _ := b₂.congr
          ztcvx ztcvx ztcvx
        have hA3 : ztlap := by
          have := F13.2.2.2.2.2.2; omega
        obtain ⟨c₄, k₄, e₄, hk₄, b₄, fr₄⟩ := call c₃ _ p₁ hp1m e₃.wb_right ctx₃ ho₃ regs3 hpc₃
          best₃ by_omega
        refine ⟨c₄, _, .seq e₁ ztxue,
          by zunww; omega, ?_,
          ((F01.trans F13).trans ztrpo).mono le_rfl ztb
            ztisc⟩
        zudgl
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)
def shotListG (kc xc : ℕ → ℕ → ℕ → ℕ → Stmt) (sh : Stmt) (R : ℕ) : Stmt :=
  .seq ztqwe (.whileLtN ztnw ztbgs
    ztzse)

/-- **The precondition of the wrapper** for the model `M`, the environment `E` and the
admissible heights `Y`. -/
def ShotPreG (X : MemCtx) (Ok : Polygon → Model → Prop) (R : ℕ) (P : Polygon) (W : ℕ)
    (M : Model) (E : Config → Prop) (Y : ℝ → Prop) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztbwu ztm ∧
    c.nreg ztbmf ≤ X.cap P c.nmem ztbwu ∧
    ModelDescWF P ztm c.nmem ztdct ∧ ModelDescAt c.nmem ztdct zta M ∧
    HReg P c.nmem ztdct ∧ E c ∧ Ok P M ∧
    c.nreg ztza + 4 * c.nreg ztbgs ≤ c.nreg ALLOC ∧ c.nreg ztnx ≤ 3 ∧
    (∀ j < c.nreg ztbgs, PieceOK M zta P.n ztbapz ∧
      M.arcWt (M.key zta (arcAt c.nmem ztwxd j).1)
        (M.key zta (arcAt c.nmem ztwxd j).2) ≤ c.nreg ztbmf) ∧
    (∀ j < c.nreg ztnx, c.nreg ztbyx < M.W.n ∧ c.nreg ztbyy < M.W.n ∧
      c.nreg ztbyx ≠ c.nreg ztbyy) ∧
    ∃ o : Origin, OriginIn c ztbza o ∧ o.Lt P.n M ∧
      (ztbnw ∨ (M.InnerPt ztwle ∧
        ∀ x, o = .walk x → ProperPos M zta P.n x)) ∧
      Y (o.eval M zta).2 ∧
      Avoid M zta c.nmem ztwxd ztxci ztobb ztwle

/-- The cost of the wrapper: `A + 1` rounds of `16` nodes. -/
def shotCostG (Fg K A : ℕ) : ℕ := ztbo * (16 * nodeG Fg K)

/-- **The contract of the model-generic wrapper**, with the register frame: besides the oracle
bands, only the block `R … R + 299` changes. -/
theorem shotListG_execR {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {Bo : Finset ℕ} (hsh' : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo)
    (hXl : X.CapLocal) {R : ℕ} (hR : RegsOK R) {P : Polygon} {W : ℕ} {M : Model}
    (hRB : bandOf R ∉ Bo) (hBo : oracleBands ⊆ Bo) {E : Config → Prop} (hS : Stable Bo W R E) {Y : ℝ → Prop} {kc xc : ℕ → ℕ → ℕ → ℕ → Stmt}
    {Bk Bx : ℕ → Bool} {K : ℕ} (hk : KeyG P W M R E kc Bk K) (hBk : OpW Bk)
    (hx : XG P W M R E Y xc Bx K) (hBx : OpW Bx) (c : Config) (hw : WordsBounded W c)
    (pre : ShotPreG X Ok R P W M E Y c)
    (hroom : c.nreg ALLOC + shotCostG ztwui K ztxci ≤ W) :
    ∃ c' k, Exec P W (shotListG kc xc sh R) c c' k ∧
      k ≤ shotCostG ztwui K ztxci ∧ ShotPost R P c c' ∧
      FrameR Bo ztbio c c' k := by
  zullg
  obtain ⟨hG, hHW, hX, hcap, hmwf, hMD, hreg, hE, hOk, hAB, hH3, harcs, hholes, o, ho,
    hol, hof, hoy, havoid⟩ := pre
  zubdp
  zubep
  zugyc

  set A := c.nreg ztbgs
  zuhob
  set G := nodeG Fg K with hG'
  zudbm

  set Bi := levCostG G 3 + 20 with hBi
  have hlc : levCostG G 3 = 15 * G := by_rfl
  have hG1 : 1000 ≤ G := by rw [hG']; unfold nodeG; omega
  zudcz

  have hroom' : c.nreg ALLOC + ztbo * ztnen ≤ W := hroom
  have hA0 : c.nreg ALLOC + 16 * G ≤ W := by
    grind
  -- initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, i30, i31, i32, i33, i34, i20, i28, i36, i37, i35, f₁⟩ :=
    shInit_exec (P := P) (R := R) c hw by_omega by_omega
  have k1 := fun r hr =>
    f₁.1 r ztkuw
  zuffv

  have F01 : FrameR Bo ztdob c c₁ k₁ :=
    FrameR.of_frameB f₁ (fun r hr => by
      simp only [Bmid, decide_eq_true_eq] at hr; omega)
      ztiir k₁
  -- the holes of the recursion
  have holes_ok : HolesOK ztbmb hl := by
    zubjn

  -- the invariant
  let I : Config → Prop := fun cc =>
    WordsBounded W cc ∧ ztxsk ∧
    cc.nreg ztgx = 0 ∧ cc.nreg zthl = 1 ∧ cc.nreg ztjlw = 2 ∧ cc.nreg ztjlx = 3 ∧
    cc.nreg ztdgc = 4 ∧ cc.nreg ztnw ≤ A ∧ cc.nreg ztbas = AB + 4 * cc.nreg ztnw ∧
    ztimm ∧ c.nreg ALLOC ≤ cc.nreg ALLOC ∧
    cc.nreg ALLOC + (A - cc.nreg ztnw) * Bi ≤ W ∧ ShotCtxG P W X Ok R M E cc ∧
    OriginIn cc ztbza o ∧ BestG P M R cc ztybg z σ
  zucnm
  have I₁ : ztkzz := by
    refine ⟨e₁.wb_right, fun i hi => k1 _ by_omega, i30, i31, i32, i33, i37, by_omega,
      by omega, by_grind, by zvnhf, ?_, ?_, ?_, ?_⟩
    · zuksc
      have : (A - 0) * Bi ≤ ztbo * ztnen := by
        zuiiq
        exact Nat.mul_le_mul by_omega by_omega
      omega
    · refine ⟨⟨hS c c₁ k₁ hE e₁.wb_right F01, hG, hHW, ?_, ?_, i30, i31, ?_⟩, ?_, ?_, hOk, ?_, ?_⟩
      · zudaa
      · zufne
      · zuikv
      · zuexs
      · zuelr
      · zuilg
      · zudaa
    · zujvf
    · zuiku

      zubh
  -- one iteration
  have body : ∀ cc, I cc → cc.nreg ztnw < cc.nreg ztbgs →
      ∃ c' k, Exec P W ztzse cc c' k ∧
        I c' ∧ k ≤ Bi ∧ A - c'.nreg ztnw < A - cc.nreg ztnw ∧
        FrameR Bo Wr cc c' k := by
    zuva

    have hK2 : cc.nreg _ = A := hin 2 by_omega
    zukss
    -- load the arc
    obtain ⟨c₂, k₂, e₂, hk₂, pc₂, f₂⟩ := loadArc_exec (P := P) (R := R) cc hwc c31 (by
      omega)
    have k2 : ∀ r, ¬ ztjly → c₂.nreg r = cc.nreg r := fun r hr =>
      f₂.1 r by_grind
    have harc : ztyus := by
      zuben

    have F02 : FrameR Bo Wr cc c₂ k₂ := FrameR.of_frameB f₂ (fun r hr => by
      zvmwo at hr; omega)
      ztjqn _
    have ctx₂ := ShotCtxG.frame hXl hS hctx e₂.wb_right F02
      by_omega ztnyz
    have ho₂ : ztulw := originIn_copy hoc ztbna ztbna
      ztbna
    zubew

    have hkl : ztyda := by
      zulnr
      interval_cases ℓ
      · zuoe
      · zuoe
      · zuoe
      · zuoe
    have hhl2 : ztsix := by
      zuyh

      zujx
      · zubyv
      · zubyw
    have hlv : levLeaves M Q c₂ R 3 0 ztzxs =
        leaves ztbmb hl ztrkr := by
      rw [levLeaves_eq M Q c₂ R hkl 3 0 by_omega, holesFrom_eq c₂ R hkl, hhl2, harc]
    zumdr
    have best₂ : BestG P M R c₂ ztevr z ztzej := by
      zummk
      exact hbest.congr ztbna ztbna
        ztbna
    zucic

    have hKj : Bi ≤ ztsuu * Bi := Nat.le_mul_of_pos_left _ by_omega
    obtain ⟨c₃, k₃, e₃, hk₃, b₃, fr₃⟩ := levG_exec hsh hBs hXl hR hRB hBo hS hk hBk hx hBx hol hof hoy
      3 0 c₂ ztevr by_omega e₂.wb_right ctx₂ ho₂
      ztntp
      (fun j' _ hj' hj'' => by
        rw [hkl j' by_omega, k2 _ by_omega, hin 9 by_omega] at hj''
        have := hholes j' by_omega
        rw [k2 _ by_omega, k2 _ by_omega,
          show R + 10 + 2 * j' = R + ztgbv by omega, hin _ by_omega,
          show R + 11 + 2 * j' = R + ztgbx by omega, hin _ by_omega]
        rw [show R + 10 + 2 * j' = R + ztgbv by omega,
          show R + 11 + 2 * j' = R + ztgbx by omega] at this
        omega)
      (fun p hp => by
        zugvb

        exact ⟨le_trans ztqsx hwt,
          leaf_avoid M Q holes_ok hp ztfrs⟩)
      best₂ (by zuood; show _ + levCostG G 3 ≤ W; omega)
    zuemd

    replace hk₃ : k₃ ≤ levCostG G 3 := hk₃
    have k3 : ztgqa :=
      fun i hi hw' => fr₃.1 _ ztrku (by have := hR; unfold RegsOK at this; unfold ALLOC; omega) hw'
    have nw : ztygx := fun i hi => by
      zultz
    -- advance
    have d31 : ztyyr := by
      zunla
    have d37 : ztbact := by
      zunlb
    zudgz
    have d36 : ztyuj := by
      zueyu
    have hAc : AB + 4 * A ≤ W := by_omega
    obtain ⟨c₄, k₄, e₄, hk₄, s28, s36, f₄⟩ := stepArc_exec (P := P) (R := R) c₃ e₃.wb_right d31 d37
      by_omega by_omega
    have k4 : ztfxl := fun r h1 h2 =>
      f₄.1 r zthfj
    have F34 : FrameR Bo Wr c₃ c₄ k₄ := FrameR.of_frameB f₄ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq] at hr; omega) (by simp; unfold ALLOC; omega) _
    have F24 : FrameR Bo Wr c₂ c₄ _ :=
      (fr₃.mono le_rfl ztisu le_rfl).trans F34
    zulgz
    have ex : Exec P W _ cc c₄
      _ := .seq e₂ ztfml
    have reg4 : ztygw :=
      fun i hi => by
        zuduu
    refine ⟨c₄, _, ex, ⟨e₄.wb_right, fun i hi => by zuntv,
      by zuobf, by zuobg,
      by zuobh, by zuobi,
      by zuobj, by_omega,
      by omega, fun a ha => ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by omega, by_omega, F04⟩
    · zugtr
    · have := F04.2.2.2.2.2.1; omega
    · have := F04.2.2.2.2.2.2; zuooe
      have hsub : (A - ztl) * Bi + Bi = ztsuu * Bi := by
        zugxn
      omega
    · exact ShotCtxG.frame hXl hS hctx e₄.wb_right F04 by_omega
        ztnza
    · zujvg
    · zuiml
      exact b₃.congr ztcdi ztcdi
        ztcdi
  -- the loop
  obtain ⟨c', kL, eL, hIc, hnt, hkL, frL⟩ := whileLtN_rel (P := P) (W := W) (a := R + 28)
    (b := R + 2) (body := .seq ztfic ztdkg) I
    (FrameR Bo Wr) (fun cc => A - cc.nreg ztnw) Bi ztqnk
    ztsxp ztjvk
    ztxsd body _ c₁ rfl I₁
  obtain ⟨-, hin, -, -, -, -, -, hjK, -, -, -, -, -, -, hbest⟩ := hIc
  have hK2 : c'.nreg _ = A := hin 2 by_omega
  have hjE : c'.nreg ztnw = A := by_omega
  zuema

  -- the frame
  have f₁' : FrameR Bo ztbio c c₁ k₁ :=
    F01.mono le_rfl by_omega le_rfl
  have fL : FrameR Bo ztbio c₁ c' kL :=
    frL.mono le_rfl ztqoc le_rfl
  zulhe
  -- the cost
  have hcost : k₁ + kL ≤ shotCostG Fg K A := by
    unfold shotCostG
    have h1 : ztsvm * A ≤ ztnen * A := Nat.mul_le_mul_right _ by_omega
    rw [Nat.add_one_mul, Nat.mul_comm A]
    rw [← hG']
    omega
  refine zthmq
  -- the postcondition
  intro M' o' hMD' ho'
  have hM' := NFLoc.modelDesc_unique hMD' hMD
  zukei
  rw [hM', ho'']
  refine ⟨hbest.1, sofJ M Q hl c.nmem AB A, ?_, ?_, fun h => ?_, hbest.2.2⟩
  · zubbg

  · zuh
    zubvg

  · exact hbest.2.1 h
end
end ShotListG
namespace Restore
@[expose] public section
open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

/-- The register block of the candidate test's shots. -/
def RS0 : ℕ := 84000
theorem regsOK_RS0 : RegsOK RS0 := by_trivial
theorem band8_not_oracle {q : ℕ} (h1 : 80000 ≤ q) (h2 : q < 90000) : bandOf q ∉ oracleBands := by
  rw [band8 h1 h2]; decide

/-- **The run invariant survives the wrapper's frames.** -/
theorem stable_tinv {W : ℕ} {c₀ : Config} {Bo : Finset ℕ} (hB8 : bRestore ∉ Bo) :
    Stable Bo W RS0 zthcy := by
  intro c c' k hI hw' hf
  obtain ⟨r₁, -, m₁, -, -, a₁, -⟩ := hf
  have keep : zthoz := fun q h1 h2 =>
    r₁ q ztlgv ztu
      ztqgg
  refine ⟨hw', fun q h1 h2 => by zuogb; exact hI.hin q h1 h2,
    le_trans hI.hA a₁, fun a ha => by zunkw; exact hI.hm a ha,
    by zumyo; exact hI.h20,
    by zumyo; exact hI.h21,
    by zumyo; exact hI.h22,
    by zumyo; exact hI.h23⟩

/-- The registers written by `gKey`. -/
def BgK (r : ℕ) : Bool := Bprim r || decide ztqt
theorem opW_BgK : OpW BgK := fun r hr => by
  simp only [BgK, Bool.or_eq_true, decide_eq_true_eq] at hr
  zubbc
  · have := Bprim_band r hr
    refine ztoma
    have h1 := this.1
    simp only [primBands, Finset.mem_insert, Finset.mem_singleton] at h1
    simp only [oracleBands, kernelBands, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  · zumkh
    zucvl
    zuvs
theorem wr_gKey (a b d e : ℕ) : wr BgK ztjxb = true := by
  rfl

/-- **The key comparison of the test is a key comparison of the wrapper.** -/
theorem gKey_keyG {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ : Config}
    (hE : TGood P W M N c₀) : KeyG P W M RS0 zthcy gKey BgK 11010 := by
  zucxc
  zubth

  obtain ⟨c', k, ex, hk, b1, -, -⟩ := gKey_ok a b d e zttpe zttpf zttpg zttph
    P W M N c₀ c hE hI ⟨hxe, hx, fun C _ h0 => by_simp_all⟩
    ⟨hye, hy, fun C _ h0 => by_simp_all⟩ hroom
  exact ⟨c', k, ex, hk, b1, exec_frameB ex ztqyr⟩
variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## The programs -/

/-- The inputs of `absKey`. -/
def cRecL (a b : ℕ) : List ztw := [ztgzg, ztdsp, ztfmv]

/-- The abscissa record of a chain position. -/
def cRec (a b : ℕ) : Stmt := .seq (block (copies ztthu)) absKey

/-- The abscissa record of a position, in either model. -/
def gRec (a b : ℕ) : Stmt := .ifLtN 83021 83023 (cRec a b) ztjyq

/-- Saving the first record. -/
def recSave : List ztw := [(10700, 50210), (10701, 50211), (10702, 50212), (10703, 50213)]

/-- The two records into the inputs of `absCmp`. -/
def recLoad : List ztw := [(50201, 10700), (50202, 10701), (50203, 10702), (50204, 10703),
  (50205, 50210), (50206, 50211), (50207, 50212), (50208, 50213)]

/-- **The abscissa comparison of the test.** -/
def xcR (a b d e : ℕ) : Stmt :=
  .seq zthhl (.seq (block (copies recSave)) (.seq (gRec d e)
    (.seq (block (copies recLoad)) absCmp)))

/-- The registers written by `xcR`. -/
def BxR (r : ℕ) : Bool :=
  Bprim r || decide ztqt || decide ztndw
theorem wr_gRec (a b : ℕ) : wr BgK zthhl = true := by
  rfl
theorem wr_xcR (a b d e : ℕ) : wr BxR ztqze = true := by
  rfl
theorem opW_BxR : OpW BxR := fun r hr => by
  simp only [BxR, Bool.or_eq_true, decide_eq_true_eq] at hr
  zugrv
  · exact ztkbq
  · exact ztkbq
  · zumkh
    zucvk
    zuvs

/-! ## The radius of the model -/

/-- The radius of the abscissa records of the model of a run: the box radius of the chain of the
descriptor, or `coordBound Q + 1` in the interior model. -/
def KindRad (P : Polygon) (M : Model) (c : Config) (Rd : ℝ) : Prop :=
  (c.nreg 83021 = 0 ∧ ∃ H C, ChainDescAt c.nmem ztdms zta H C ∧ M = chainModel C ∧
    ChainWF P ztm c.nmem ztdms ∧ HostRegular (Qof P).n H ∧
    Rd = C.radius) ∨
  (c.nreg 83021 = 1 ∧ M = interiorModel zta ∧
    (c.nmem ztdms = 1 ↔ Mountain.LeftInside zta) ∧
    Rd = Jordan.coordBound zta + 1)

/-- **The radius of a run.** -/
theorem kindRad_run (hE : TGood P W M N c₀) (hI : TInv W c₀ c) : ∃ Rd, KindRad P M c Rd := by
  zuivj
  have h20 := hI.h20
  zuizz
  have hD := hE.hwfMD.1
  zubbz
  · zuqq
    refine ⟨C'.radius, Or.inl ⟨by_omega, H, C', hC, hM', hwf, ?_, rfl⟩⟩
    have hr : HReg P c.nmem ztchn :=
      hreg_keep hE.hwfMD hE.hMD hE.hreg zttj
    exact hr (by zunqh; exact h0) H C' by_simp_all
  · refine ⟨_, Or.inr ⟨by_omega, hMi, ?_, rfl⟩⟩
    rw [h20, hI.hm _ by_omega]; omega

/-- The radius survives a frame that keeps the memory and the registers `83020`, `83021` and the
allocator. -/
theorem KindRad.frame {Rd : ℝ} {c' : Config} (h : KindRad P M c Rd) (hm : c'.nmem = c.nmem)
    (h20 : c'.nreg 83020 = c.nreg 83020) (h21 : c'.nreg 83021 = c.nreg 83021)
    (hA : c'.nreg ALLOC = c.nreg ALLOC) : KindRad P M c' Rd := by
  unfold KindRad; rw [hm, h20, h21, hA]; exact h

/-! ## One record -/

/-- **The abscissa record of one position.** -/
theorem gRec_exec (hE : TGood P W M N c₀) (hI : TInv W c₀ c) {Rd : ℝ} (hK : KindRad P M c Rd)
    {a b : ℕ} (ha : InR a) (hb : InR b)
    (hp : ProperPos M zta P.n ztel) (he : c.nreg a < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C → |(M.pos zta ⟨c.nreg a, c.nreg b⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16800 ≤ W) :
    ∃ c' k, Exec P W zthhl c c' k ∧ k ≤ 16800 ∧
      AbsRec P c' 50210 (M.pos zta ztel).1 Rd ∧ FrameB BgK c c' := by
  unfold InR at ha hb
  zueqd
  zucvu
  have hHW := hE.hW
  rcases hK with ⟨h21, H, C, hC, hMC, hwf, hreg, rfl⟩ | ⟨h21, hMi, hbit, rfl⟩
  · -- a chain model: `absKey`
    obtain ⟨c₁, c', k, h1, -, -, ex, hk, hout, -⟩ := callPrim absKey_meets ztthu
      (by simp only [cRecL, List.mem_cons, List.not_mem_nil, or_false]
          grind)
      ztggf ztggf (src := 83020) by_tauto hI.hw hG hHW hwf hC
      (fun c₁ h1 _ hm => by
        have q0 := h1 ztgzg by_tauto
        have q1 := h1 ztdsp by_tauto
        have q2 := h1 ztfmv by_tauto
        simp only at q0 q1 q2
        refine ⟨⟨by_grind, by_grind,
          by grind⟩, fun H' hH' => ?_⟩
        rw [hm, q0] at hH'
        have := NFLoc.hostAt_unique hH' hC.1
        zumo
        zubp
        grind)
      by_omega
    have q1 := h1 ztdsp ztggf
    have q2 := h1 ztfmv ztggf
    zuhqe
    have hr : AbsRec P c' 50210 ((chainModel C).pos zta ztrbr).1
      C.radius := hout
    rw [q1, q2, ← hMC] at hr
    have ex' : Exec P W zthhl c c' zts := .ifLtN_true by_omega ex
    exact ⟨c', _, ex', by simp [cRecL] at hk; omega, hr, exec_frameB ex' ztudi⟩
  · -- the interior model: `iRec`
    zugih

    obtain ⟨c', k, ex, hk, hr, -⟩ := iRec_exec (P := P) (W := W) hG
      (by unfold hostWords at hHW; omega) hI.hw (a := a) (b := b) hbit rfl hI.h22 ha hb hp
      by_omega
    have ex' : Exec P W zthhl c c' ztcnq := .ifLtN_false by_omega ex
    exact ⟨c', _, ex', by_omega, hr, exec_frameB ex' ztudi⟩

/-! ## The comparison -/

/-- The admissible heights of the test's shots: inside the box of a chain model. -/
def YR (M : Model) (y : ℝ) : Prop := ∀ C : Chain, M = chainModel C → |y| < C.radius

/-- **`xcR` is an abscissa comparison of the wrapper.** -/
theorem xcR_xG (hE : TGood P W M N c₀) :
    XG P W M RS0 zthcy ztqdh xcR BxR 34000 := by
  zucxb
  zubth

  have ha' := inR a ha
  have hb' := inR b hb
  have hd' := inR d hd
  have he' := inR e he
  unfold InR at ha' hb' hd' he'
  obtain ⟨Rd, hK⟩ := kindRad_run hE hI
  -- the first record
  obtain ⟨c₁, k₁, e₁, hk₁, r₁, f₁⟩ := gRec_exec hE hI hK zttpe zttpf hp1 he1 hY
    by_omega
  have g₁ : zthpl := fun r h1 h2 => f₁.1 r (by
    simp only [BgK, Bprim, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  zuhwg
  -- save it
  obtain ⟨c₂, e₂, v₂, f₂⟩ := copies_run (P := P) recSave c₁ e₁.wb_right
    by_decide
    by_decide
  simp only [recSave, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₂
  obtain ⟨s0, s1, s2, s3⟩ := v₂
  have k2 : ∀ r, ¬ ztndw → c₂.nreg r = c₁.nreg r := fun r hr =>
    f₂.1 r (by simp [recSave]; omega)
  have r₂ : AbsRec P c₂ 10700 (M.pos zta ztel).1 Rd :=
    absRec_copy r₁ s0 (by zunsu) (by rw [s2]) (by rw [s3])
  have f₁' : FrameB BxR c c₁ := frameB_mono f₁ (fun r h => by
    simp only [BgK, Bool.or_eq_true] at h; simp only [BxR, Bool.or_eq_true]; tauto)
  have F02 : FrameB BxR c c₂ := f₁'.trans (frameB_mono f₂ (fun r hr => by
    simp [recSave] at hr; simp only [BxR, Bool.or_eq_true, decide_eq_true_eq]; omega))
  have g₂ : ∀ r, 80000 ≤ r → r < 90000 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    grind
  have hA2 : ztbae := by rw [k2 _ by_decide, hA1]
  have hI2 : TInv W c₀ c₂ := stable_tinv (Bo := oracleBands) by_decide c c₂ 0 hI e₂.wb_right
    (FrameR.of_frameB F02 (fun r hr => Or.inr (opW_BxR r hr).1) (opW_alloc opW_BxR) 0)
  have hK2 : KindRad P M c₂ Rd := hK.frame F02.2.2.1 ztrrc
    ztrrc hA2
  -- the second record
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, f₃⟩ := gRec_exec hE hI2 hK2 zttpg zttph
    by_grind
    by_grind
    (fun C hC => by rw [g₂ d hd'.1 hd'.2, g₂ e he'.1 he'.2, ← hyy]; exact hY C hC)
    by_omega
  rw [g₂ d hd'.1 hd'.2, g₂ e he'.1 he'.2] at r₃
  have r₂' : AbsRec P c₃ 10700 (M.pos zta ztel).1 Rd :=
    absRec_copy r₂ ztjwu ztjwu ztjwu
      ztjwu
  -- load both
  obtain ⟨c₄, e₄, v₄, f₄⟩ := copies_run (P := P) recLoad c₃ e₃.wb_right
    by_decide
    by_decide
  simp only [recLoad, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at v₄
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := v₄
  have x1 : AbsRec P c₄ 50201 (M.pos zta ztel).1 Rd :=
    absRec_copy r₂' l1 (by rw [l2]) (by rw [l3]) (by rw [l4])
  have x2 : AbsRec P c₄ 50205 (M.pos zta ztge).1 Rd :=
    absRec_copy r₃ l5 (by rw [l6]) (by rw [l7]) (by rw [l8])
  have hA4 : ztgul := by
    rw [f₄.1 _ by_rfl, f₃.1 _ by_rfl, hA2]
  have hP3 : ztmd := by have := hE.hW; unfold hostWords at this; omega
  obtain ⟨c₅, k₅, e₅, hk₅, post₅, -⟩ := absCmp_meets P W c₄ e₄.wb_right
    ⟨hE.hG, hP3, _, _, Rd, x1, x2⟩ by_grind
  zuifh
  have bit := post₅ _ _ Rd x1 x2
  have ex : Exec P W ztqze c c₅ _ := .seq e₁ ztbq
  refine ⟨c₅, _, ex, by simp only [recSave, recLoad, List.length_cons, List.length_nil]; omega,
    bit, exec_frameB ex (wr_xcR a b d e)⟩
end
end Restore
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
variable {M : Model}
/-- **The side of a chord confines the positions facing it** (the core of `chord_bound`): if `G`
is on the side `ρ` of `f`, attached at `N` and `Fr`, with orientation `θ`, then no position
facing `G` lies in the cyclic interval from `Fr` to `N` (`θ = 1`) or from `N` to `Fr`
(`θ = -1`). -/
theorem side_arc (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {f : Set Point} (hf : f ∈ F) {pn pf : ℕ} {tn tf : ℝ} (hN : SideAttach M.W f pn tn)
    (hFr : SideAttach M.W f pf tf) (hNF : sidePt M.W pn tn ≠ sidePt M.W pf tf) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ M.regions F) (hS : SideOf M ρ f G)
    {θ : ℝ} (hori : 0 < θ * ρ * ztgwh) {p : ℕ}
    (hp : p < M.W.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hfG : M.Faces p t G) :
    (θ = 1 → ¬ sideInArc ztbbc ztbue ztk) ∧
      (θ = -1 → ¬ sideInArc ztbue ztbbc ztk) := by
  zudel
  have hmid : ztzjj := by
    zugdw
  zufvn
  have hsym : lerp ztegb ztegc ztcn =
      lerp ztegc ztegb ztcn := by
    zubvj
  constructor
  · zumgu

    have hleft := left_of_side hρ hS hy.symm
      by_simp_all by_grind by_linarith
    exact fun hin => hM.not_left_of_after hF hf hFr hN ztqax hG hp ht hin hfG hleft
  · zumgu

    have hleft := left_of_side hρ hS hy hmid
      hmidD by_linarith
    exact fun hin => hM.not_left_of_after hF hf hN hFr hNF hG hp ht hin hfG hleft

/-- **A third chord at a tie** is one of the two chords of the tie. -/
theorem tie_third (hM : WalkAx M) {F : Set ztf} (hF : F ⊆ M.Adm)
    {c c' e : Set Point} (hc : c ∈ F) (hc' : c' ∈ F) (he : e ∈ F) (hne : c ≠ c') {p : ℕ}
    {t : ℝ} (hA : SideAttach M.W c p t) (hA' : SideAttach M.W c' p t)
    (hE : SideAttach M.W e p t) : e = c ∨ e = c' := by
  zuxr
  · obtain ⟨-, -, h⟩ := hM.tie_shape hF hc hc' hA hA' h1 h2
    simp_all
  · obtain ⟨-, -, h⟩ := hM.tie_shape hF hc' hc hA' hA h2 h1
    grind

/-- A key of a chord is one of two given keys of it with distinct points. -/
theorem key_of_two (hM : WalkAx M) {c : Set Point} (hc : c ∈ M.Adm)
    {pa pb p : ℕ} {ta tb t : ℝ} (hA : SideAttach M.W c pa ta) (hB : SideAttach M.W c pb tb)
    (hAB : sidePt M.W pa ta ≠ sidePt M.W pb tb) (hP : SideAttach M.W c p t) :
    (p = pa ∧ t = ta) ∨ (p = pb ∧ t = tb) := by
  obtain ⟨hseg, -, hopen, -, -⟩ := hM.attach_seg hc hA hB hAB
  rw [hseg] at hP
  have hP' := hP
  rw [← hseg] at hP'
  rcases hM.attach_endpoint hopen hP with h | h
  · exact Or.inl (hM.attach_unique hc hP' hA h)
  · exact Or.inr (hM.attach_unique hc hP' hB h)

/-! ## Walking along a chain with an invariant -/
section ChainWalk
variable (J : Merge.Junction)

/-- **An invariant propagated across ties** of the right stretch: if `Φ` holds for a chord `f`
at its near attachment, and `f'` is the other chord of the tie at the far attachment of `f`
(both in the right stretch), then `Φ` holds for `f'` at that attachment. -/
def Propag (S₂ : Set ztf) (Φ : Set Point → ℝ → Prop) : Prop :=
  ∀ (f f' : Set Point) (pn : ℕ) (tn : ℝ) (pf pb : ℕ) (tb : ℝ), f ∈ F₂plus J S₂ →
    f' ∈ F₂plus J S₂ → f' ≠ f → SideAttach (chainModel J.whole).W f pn tn →
    SideAttach (chainModel J.whole).W f pf 0 →
    sidePt (chainModel J.whole).W pn tn ≠ sidePt (chainModel J.whole).W pf 0 →
    SideAttach (chainModel J.whole).W f' pf 0 → SideAttach (chainModel J.whole).W f' pb tb →
    sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W pf 0 →
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    Φ f ztxcr →
    Φ f' (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu)

/-! ## The two invariants -/

/-- **The forward invariant**: chords of `F₂⁺` (other than `f`) with an attachment beyond `lo`
and one inside the right stretch have the latter before `o`. -/
def PhiI (S₂ : Set ztf) (lo : ℝ) (f : Set Point) (o : ℝ) : Prop :=
  ∀ e ∈ F₂plus J S₂, e ≠ f → ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
    SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
    sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
    lo < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd < o

/-- **The backward invariant**: chords of `F₂⁺` (other than `f`) with an attachment in the `C₁`
part and one inside the right stretch before `o` have the latter before `oA` (weakly). -/
def PhiK (S₂ : Set ztf) (oA : ℝ) (f : Set Point) (o : ℝ) : Prop :=
  ∀ e ∈ F₂plus J S₂, e ≠ f → ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
    SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
    sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
    ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
      ((rL1 J + rL2 J : ℕ) : ℝ) →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ≤ o →
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ≤ oA

/-! ## The ends of a chain -/

/-- **The backward end** of a chain (orientation `-1`) lies in the `C₁` part before every
non-cut position facing `G` there. -/
theorem back_end (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {ph pz : ℕ} {th tz : ℝ}
    (hPa : SideAttach (chainModel J.whole).W h ph th)
    (hZa : SideAttach (chainModel J.whole).W h pz tz)
    (hne : sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz)
    (hS : SideOf ztbm ρ h G)
    (hori : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw := by
  zucf
  zued
  have hgn : ztcx := by
    zucfu
  zucmq
  zuxn

  zujzv
  have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
    zube

    zudsa
    · grind
    · zuhrv

      · exact (sideInArc_rev_iff_off hg0 hgn kZ0 kZ1 kP0 kP1 kx0 kx1 by_linarith).2
          by_grind
      · zubev

  zumku
  have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by_linarith
  have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw := by
    zux

    exact hsa zthqa
  zudsg
  · zuito
  · zulxs

/-- **The forward end** of a chain (orientation `1`) is the shared vertex copy at offset `0`, or
lies in the `C₁` part after every non-cut position facing `G` there. -/
theorem fwd_end (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {ph pz : ℕ} {th tz : ℝ}
    (hPa : SideAttach (chainModel J.whole).W h ph th)
    (hZa : SideAttach (chainModel J.whole).W h pz tz)
    (hne : sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz)
    (hS : SideOf ztbm ρ h G)
    (hori : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (_ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe) := by
  zucf
  zued
  have hgn : ztcx := by
    zucfu
  zucmp
  zuxn

  zudsa
  · right
    have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
      grind
    zumku
    have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by_linarith
    have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
      zux

      exact hsa ztxmr
    zudsg
    · zuito
    · zulxt
  grind
end ChainWalk
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
section Walk2
variable (J : Merge.Junction)

/-- **A pair of gap labels**: `V` is a gap label and some label of `G` is a gap label. -/
def GapPair (S₂ : Set ztf) (G V : Set Point) : Prop :=
  GapLab J S₂ V ∧ ∃ Vg, GapLab J S₂ Vg ∧ RLabel J S₂ G Vg

/-- **Walking along a chain** without `TopStrict`.  As `half_walk`, with the chord of the model
of `C₂` in `S₂x`; the tracked region may switch sides of the slit at the split vertex, and the
walk ends with a label, a bound, or a pair of gap labels. -/
theorem half_walk2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) :
    ∀ (N d : ℕ) (t : ℝ) (f : Set Point) (pf : ℕ) (tf : ℝ) (V : Set Point),
      V ∈ (chainModel J.right).regions S₂ →
      (beyond ztbi ztbuj ztmok).ncard ≤ N →
      d < rL1 J + rL2 J → 0 ≤ t → t < 1 → ztevv → f ∈ F₂plus J S₂ →
      SideAttach (chainModel J.whole).W f
        ztbn t →
      SideAttach (chainModel J.whole).W f pf tf →
      sidePt (chainModel J.whole).W ztbn t ≠
        sidePt (chainModel J.whole).W pf tf →
      SideOf ztbm ρ f G →
      0 < θ * ρ * ((sidePt (chainModel J.whole).W
        ztbn t).1 -
          (sidePt (chainModel J.whole).W pf tf).1) →
      ztwst →
      RLabel J S₂ G V ∨ Bound ztbm ztbi G
        ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
        (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ztwlh) ∨
        GapPair J S₂ G V := by
  zucf
  zust
  zudnl
  zued
  have hgn : ztcx := by
    zucfu
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro d t f pf tf V hV hN hd ht0 ht1 hd0 hf hfA hfF hNF hS hori htrack
  zurn
  zugyp
  zugye
  have hoN : off W.n (g : ℝ) ztwmq = d + t := hC.off_M hd ht0 ht1
  have hN0 : 0 < off W.n (g : ℝ) ztwmq := by
    zumnu
    zubbd
    · grind
    · have := hd0 h.symm
      positivity
  have hNL : off W.n (g : ℝ) ztwmq < ((L : ℕ) : ℝ) := by
    zumnu
    have : (d : ℝ) + 1 ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  -- the bound through `f`, given a bound (or nothing) at the far end
  have hthrough : (∀ (p : ℕ) (t' : ℝ), p < W.n → t' ∈ Ioo (0 : ℝ) 1 →
      ¬ (chainModel J.whole).IsCut ztbi ztdvo → (chainModel J.whole).Faces p t' G →
      0 < off W.n (g : ℝ) ztdvo → off W.n (g : ℝ) ztdvo < ((L : ℕ) : ℝ) →
      0 < θ * (off W.n (g : ℝ) ztdvo - off W.n (g : ℝ) ztbbc) ∨
        ((L : ℕ) : ℝ) ≤ off W.n (g : ℝ) ztbbc ∨ off W.n (g : ℝ) ztbbc ≤ 0) →
      Bound ztbm ztbi G (g : ℝ) ((L : ℕ) : ℝ) θ
        ztbani :=
    fun hpre => chord_bound hM hFs hf hfA hfF hNF hρ hG hS hθ hori hg0 hgn hN0 hNL hpre
  zubdh

  · zuhl
    refine hthrough fun _ _ _ _ _ _ _ _ => Or.inr ?_
    grind
  -- the far end is in the right stretch
  zucsv

  have hd' : d' < L := by
    zucvn

    zufc
  zuegw

  obtain ⟨c, hc, hfc, hVs⟩ := htrack
  -- the partner step: from a partner at the far end, a label, a bound or a gap pair there
  have hstep : ∀ (f' : Set Point) (V' : Set Point), tf = 0 → d' ≠ 0 → f' ∈ F₂plus J S₂ →
      f' ≠ f → SideAttach W f' ztxap 0 → SideOf ztbm ρ f' G →
      V' ∈ (chainModel J.right).regions S₂ →
      (ztxim ∨
        ztbaod) →
      RLabel J S₂ G V' ∨ Bound ztbm ztbi G (g : ℝ) ((L : ℕ) : ℝ) θ
        ztxaz ∨ GapPair J S₂ G V' := by
    intro f' V' htf0 hd'0 hf' hne hA' hS' hV' hpart
    zucae

    set Pn := sidePt W ztwnv t with hPndef
    zuhc

    have hθρ : ztmxn := by
      zugl
    have hori' : ztkzn := by
      zugld

    rcases hpart with ⟨c', hc', hfc', hVs'⟩ | ⟨-, hoff⟩
    · -- recursion along the partner
      have hlt : (beyond ztbi ztbuj Bp).ncard <
          (beyond ztbi ztbuj Pf).ncard := by
        zuknj

        · grind
        · zuzg

          zuje
          zujnq
          have : θ * ρ * ztigx =
              zteb * ztluq := by_ring
          nlinarith
      exact ih _ zttst d' 0 f' pb tb V' hV' le_rfl hd' le_rfl zero_lt_one
        by_omega hf' hA' hB ztbsb hS' hori' ztexw
    · -- the partner leaves the stretch
      zuhl
      zuhwo
      have hoF0 := by_omega
      refine chord_bound hM hFs hf' hA' hB ztbsb hρ hG hS' hθ hori' hg0 hgn ?_ ?_
        fun _ _ _ _ _ _ _ _ => Or.inr ?_
      · grind
      · grind
      · zux

        grind
  -- combining a result at the far end
  have hcomb : ∀ V' : Set Point, ztzde → tf = 0 →
      (RLabel J S₂ G V' ∨ Bound ztbm ztbi G (g : ℝ) ((L : ℕ) : ℝ) θ
        ztxaz ∨ GapPair J S₂ G V') →
      RLabel J S₂ G V ∨ Bound ztbm ztbi G (g : ℝ) ((L : ℕ) : ℝ) θ
        ztbani ∨ GapPair J S₂ G V := by
    intro V' hVV htf0 h
    subst htf0
    rcases h with hRL | hbd | ⟨hg', hgp⟩
    · rcases hVV with rfl | ⟨hgV, hgV'⟩
      · zuleh
      · exact Or.inr (Or.inr ⟨hgV, V', hgV', hRL⟩)
    · zuhl
      exact hthrough fun p t' hp ht' hnc hfG h0 hL => Or.inl (hbd p t' hp ht' hnc hfG h0 hL)
    · rcases hVV with rfl | ⟨hgV, -⟩
      · exact Or.inr (Or.inr ⟨hg', hgp⟩)
      · exact Or.inr (Or.inr ⟨hgV, hgp⟩)
  zufrm
  · zufka

    have hδ : ztixu := by
      zuccr
      have := hC.hδ by_omega
      omega
    have hd'0 : ztuuu := by
      intro h; zvmwc at hin1; grind
    rcases split_step J hP hS₂ hF hδ hf hc hfc hfF hρ hG hV hS hVs with
      hRL | hgp | ⟨hgV, f', hf', hne, hA', hS', hpart⟩
    · zuleh
    · exact Or.inr (Or.inr hgp)
    · zucti
      · exact hcomb V' (Or.inr ⟨hgV, hgV'⟩) rfl
          (hstep f' V' rfl hd'0 hf' hne hA' hS' hV' ztzcm)
      · exact hcomb V ztp rfl (hstep f' V rfl hd'0 hf' hne hA' hS' hV ztvci)
  · have hsec' : ztknq := by
      intro htf
      refine ⟨fun h => ?_, fun h => hsplit ⟨htf, h⟩⟩
      zuhqk

    rcases local_step2 J hP hS₂ hF hd' hfF.2.1 hfF.2.2.1 hsec' hf hc hfc hfF hρ hG hV hS hVs
      with hRL | ⟨htf0, f', hf', hne, hA', hS', hpart⟩
    · zuleh
    · subst htf0
      exact hcomb V ztp rfl
        (hstep f' V rfl (hsec' rfl).1 hf' hne hA' hS' hV hpart)

/-- **The bound from one chord of a tie** without `TopStrict` (as `end_bound`). -/
theorem end_bound2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G V : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) {d : ℕ} (hd : d < rL1 J + rL2 J) (hd0 : d ≠ 0)
    {f : Set Point} (hf : f ∈ F₂plus J S₂)
    (hfA : SideAttach (chainModel J.whole).W f
      ztbn 0)
    {pb : ℕ} {tb : ℝ} (hB : SideAttach (chainModel J.whole).W f pb tb)
    (hBne : sidePt (chainModel J.whole).W pb tb ≠ sidePt (chainModel J.whole).W
      ztbn 0)
    (hS : SideOf ztbm ρ f G)
    (hori : 0 < θ * ρ * ((sidePt (chainModel J.whole).W
      ztbn 0).1 -
        (sidePt (chainModel J.whole).W pb tb).1))
    (htr : ztwst ∨
      (ztnlx ∧
        OffOut J f ztbn 0)) :
    RLabel J S₂ G V ∨ Bound ztbm ztbi G
      ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ((rL1 J + rL2 J : ℕ) : ℝ) θ
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
        ztwrh) ∨
      GapPair J S₂ G V := by
  rcases htr with htr | ⟨-, hoff⟩
  · exact half_walk2 J hP hS₂ hF hρ hθ hG _ d 0 f pb tb V hV le_rfl hd le_rfl zero_lt_one
      by_omega hf hfA hB ztbsb hS hori htr
  zuhl
  zucf
  zued
  have hgn : ztcx := by
    zucfu
  zuhwo
  have hoF0 := hC.off_M hd le_rfl zero_lt_one
  refine chord_bound hC.hM hC.hF hf hfA hB ztbsb hρ hG hS hθ hori hg0 hgn ?_ ?_
    fun _ _ _ _ _ _ _ _ => Or.inr ?_
  · zumnt
    positivity
  · zumnt
    zubfq
    linarith
  grind

/-- A gap pair of `G` and a label of `G` make the (K3) alternative. -/
theorem gapPair_label (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV' : V' ∈ (chainModel J.right).regions S₂) (hL : RLabel J S₂ G V')
    (hgp : GapPair J S₂ G V) : V' = V ∨ ztfno := by
  obtain ⟨hgV, Vg, hgVg, hRLg⟩ := hgp
  right
  refine ⟨?_, hgV⟩
  rcases label_right3 J hP hS₂ hS₂f hG hV' hgVg.2.1 hL hRLg with rfl | ⟨h, -⟩
  · omega
  omega

/-- **Lemma (E) without `TopStrict`** (the weakened form of (K3)): let `e ∈ F₂⁺`, contained in
`c ∈ S₂`, be attached at a position of the right stretch (not the base or the split vertex),
`G` on the side `ρ` of `e` and `V` on the side `ρ` of `c`.  Then every label of `G` is `V`, or
it and `V` are gap labels. -/
theorem label_side_gen2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {d : ℕ} (hd : d < rL1 J + rL2 J)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c)
    (heA : SideAttach (chainModel J.whole).W e
      ztbn t)
    {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1) {G V V' : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hV' : V' ∈ (chainModel J.right).regions S₂)
    (hGs : SideOf ztbm ρ e G) (hVs : SideOf ztj ρ c V)
    (hL : RLabel J S₂ G V') : V' = V ∨ ztfno := by
  zucf
  zust
  zudnl
  zuixs
  rcases local_step2 J hP hS₂ hF hd ht0 ht1 hsec he hcx hec heA hρ hG hV hGs hVs with
    hRL | ⟨rfl, f', hf', hne, hA', hS', hpart⟩
  · zucli
  zukbr
  zurn
  zuinr
  zukw

  set Pa := sidePt W A 0 with hPadef
  set Bp := sidePt W pb tb with hBpdef
  set Bq := sidePt W pb' tb' with hBqdef
  have h1 : Bp.1 ≠ Pa.1 := by_grind
  have h1' : Bq.1 ≠ Pa.1 := by_grind
  zubqv

  have hθρ : ztxfm := by
    zugl
  have hori' : 0 < -θ * ρ * zttbj := by
    have e1 : -θ * ρ * zttbj = θ * ρ * ztjha := by_ring
    zukd
    have hprod : 0 < ztlur * ztzhx := by
      have e2 : ztlur * ztzhx =
          ztxho * (-((Bp.1 - Pa.1) * ztjha)) := by_ring
      zubyo

    zugkj
  zuehl
  rcases end_bound2 J hP hS₂ hF hρ hθ hG hV hd hd0 he heA hB hBne hGs hori
      ztfbd with hRL | hb1 | hgp
  · zucli
  · rcases end_bound2 J hP hS₂ hF hρ hθ' hG hV hd hd0 hf' hA' hB' hBne' hS' hori' hpart with
      hRL | hb2 | hgp
    · zucli
    · exfalso
      obtain ⟨d'', hd'', t'', ht'', hnc, hfG, -⟩ := hL
      zuiyr
      have hpos : 0 < off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ztfaq := by
        zuduj
      have hlt : off W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ)
          ztfaq <
            ((rL1 J + rL2 J : ℕ) : ℝ) := by
        zudui

      zubwv

    · zugkf
  · zugkf
end Walk2
end Sweep
end
end Chazelle.Core
section
set_option hygiene false
local macro "zqbbu" : tactic => `(tactic| have hg0 : ztee := Nat.cast_nonneg _)
local macro "zqbbv" : tactic => `(tactic| have hC := corr_right0 J hP hS₂.2.1 hS₂.1)
local macro "zqbbw" : tactic => `(tactic| (obtain ⟨kP0, kP1⟩ := Corr.key_mem hPa.1 hPa.2.1 hPa.2.2.1
                                           obtain ⟨kZ0, kZ1⟩ := Corr.key_mem hZa.1 hZa.2.1 hZa.2.2.1
                                           obtain ⟨kx0, kx1⟩ := Corr.key_mem hp₀ ht₀.1.le ht₀.2
                                           have hZ0 := off_nonneg kZ0 hgn))
local macro "zqbbx" : tactic => `(tactic| (have hM := hC.hM
                                           have hFs := hC.hF))
local macro "zqbby" : tactic => `(tactic| (set W := (chainModel J.whole).W with hWdef
                                           set g := 6 + tpos J.whole J.m₁ with hgdef))
set_option hygiene true

/-!
# The sweep (WP-D), part 9b: chain brackets without `TopStrict` (F2)

The bracket lemma of `SweepBracket` for a region without a label, with the walk of
`SweepChainT` (the enlarged family `S₂x`, the split step).  The tracked region of `S₂` may switch
to the other side of the slit of `C₂` at the split vertex, so the last chord of the chain lies in
a chord of `S₂` whose side is the region `V` of the start or (with `V`) a gap label
(`ChainKind`), or is a shared chord or a top chord.

* `kind_of_S₂x`: a chord of `F₂⁺` inside a chord of `S₂x` is inside a chord of `S₂`, or is that
  chord, a shared or top chord.
* `chain_gen2`, `bracket_core2`, `bracket2`: as `chain_gen`, `bracket_core`, `bracket`.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sideInArc sidePt sideLeft sideKey_inj)
open Chazelle.Jordan (offset)
open Chazelle.Geometry (lerp)
open WalkEmbed
namespace Sweep
section ChainWalk2
variable (J : Merge.Junction)

/-- The facts at a tie step: a chord with an attachment in the `C₁` part is not the chord `f`
arriving at the tie, is not attached at the tie unless it is `f'`, and the two attachments of
`f` have distinct offsets. -/
theorem tie_step_facts2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    {f f' : Set Point} {pn : ℕ} {tn : ℝ} {pf : ℕ} (hf : f ∈ F₂plus J S₂)
    (hf' : f' ∈ F₂plus J S₂) (hne : f' ≠ f) (hfA : SideAttach (chainModel J.whole).W f pn tn)
    (hfF : SideAttach (chainModel J.whole).W f pf 0)
    (hNF : sidePt (chainModel J.whole).W pn tn ≠ sidePt (chainModel J.whole).W pf 0)
    (hA' : SideAttach (chainModel J.whole).W f' pf 0)
    (hnL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hfL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    {e : Set Point} (he : e ∈ F₂plus J S₂) (hne' : e ≠ f') {pw : ℕ} {tw : ℝ} {pb : ℕ} {tb : ℝ}
    (hW : SideAttach (chainModel J.whole).W e pw tw)
    (hB : SideAttach (chainModel J.whole).W e pb tb)
    (hoW : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs) :
    e ≠ f ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ≠
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue ≠
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztftu := by
  zqbbv
  zqbbx
  zqbbu
  have hgn : ztcx := by
    zucfu
  obtain ⟨n0, n1⟩ := Corr.key_mem hfA.1 hfA.2.1 hfA.2.2.1
  obtain ⟨f0, f1⟩ := Corr.key_mem hfF.1 hfF.2.1 hfF.2.2.1
  obtain ⟨b0, b1⟩ := Corr.key_mem hB.1 hB.2.1 hB.2.2.1
  have hef : e ≠ f := by
    zunq
    rcases key_of_two hM ztcik hfA hfF hNF hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  refine ⟨hef, fun heq => ?_, fun heq => ?_⟩
  · have hk := off_inj hg0 hgn b0 b1 f0 f1 heq
    obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hfF.2.1 hfF.2.2.1 hk
    rcases tie_third hM hFs hf hf' he ztnr hfF hA' hB with h | h
    · simp_all
    simp_all
  · exact WalkAx.key_ne_of_pt_ne hfA hfF hNF (off_inj hg0 hgn n0 n1 f0 f1 heq)

/-- The forward invariant propagates across ties. -/
theorem propag_I2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {lo : ℝ}
    (hlo : ((rL1 J + rL2 J : ℕ) : ℝ) ≤ lo) : Propag J S₂ (PhiI J S₂ lo) := by
  intro f f' pn tn pf pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0 hnL hf0 hfL hΦ e he hne'
    pw tw pb' tb' hW hB' hWB hoW hoB
  zqbbv
  zqbbu
  have hgn : ztcx := by
    zucfu
  obtain ⟨hef, hBF, hNFo⟩ := tie_step_facts2 J hP hS₂ hf hf' hne hfA hfF hNF hA' hnL hfL he
    hne' hW hB' (lt_of_le_of_lt hlo hoW)
  have h1 := hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB
  zujeb
  · linarith
  · zux

    have := no_cross_off hC.hM hC.hF hF.1 hf he ztmbu hfF hfA ztqax hB' hW hg0
      hgn h by_grind h1
    grind

/-- The backward invariant propagates across ties. -/
theorem propag_K2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) (oA : ℝ) :
    Propag J S₂ ztrkb := by
  intro f f' pn tn pf pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0 hnL hf0 hfL hΦ e he hne'
    pw tw pb' tb' hW hB' hWB hoW hoB hle
  zqbbv
  zqbbu
  have hgn : ztcx := by
    zucfu
  obtain ⟨hef, hBF, hNFo⟩ := tie_step_facts2 J hP hS₂ hf hf' hne hfA hfF hNF hA' hnL hfL he
    hne' hW hB' hoW
  have hlt := lt_of_le_of_ne hle hBF
  zujeb
  · by_cases hb : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteun ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue
    · exact hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB hb
    · zumij
      exfalso
      have := no_cross_off hC.hM hC.hF hF.1 hf he ztmbu hfA hfF hNF hB' hW hg0 hgn h
        hb hlt
      grind
  · exact hΦ e he hef pw tw pb' tb' hW hB' hWB hoW hoB by_linarith

/-! ## The ends of a chain -/

/-- **The backward end** of a chain (orientation `-1`) lies in the `C₁` part before every
non-cut position facing `G` there. -/
theorem back_end2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {ph pz : ℕ} {th tz : ℝ}
    (hPa : SideAttach (chainModel J.whole).W h ph th)
    (hZa : SideAttach (chainModel J.whole).W h pz tz)
    (hne : sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz)
    (hS : SideOf ztbm ρ h G)
    (hori : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw := by
  zqbbv
  zqbbu
  have hgn : ztcx := by
    zucfu
  zucmq
  zqbbw
  zujzv
  have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
    zube

    zudsa
    · grind
    · zuhrv

      · exact (sideInArc_rev_iff_off hg0 hgn kZ0 kZ1 kP0 kP1 kx0 kx1 by_linarith).2
          by_grind
      · zubev

  zumku
  have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by_linarith
  have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ≤
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw := by
    zux

    exact hsa zthqa
  zudsg
  · zuito
  · zulxs

/-- **The forward end** of a chain (orientation `1`) is the shared vertex copy at offset `0`, or
lies in the `C₁` part after every non-cut position facing `G` there. -/
theorem fwd_end2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂) {ρ : ℝ}
    (hρ : ρ = 1 ∨ ρ = -1) {G : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    {h : Set Point} (hh : h ∈ F₂plus J S₂) {ph pz : ℕ} {th tz : ℝ}
    (hPa : SideAttach (chainModel J.whole).W h ph th)
    (hZa : SideAttach (chainModel J.whole).W h pz tz)
    (hne : sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz)
    (hS : SideOf ztbm ρ h G)
    (hori : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1))
    (hPL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hZout : ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        ((rL1 J + rL2 J : ℕ) : ℝ)))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (_ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe) := by
  zqbbv
  zqbbu
  have hgn : ztcx := by
    zucfu
  zucmp
  zqbbw
  zudsa
  · right
    have hLZ : ((rL1 J + rL2 J : ℕ) : ℝ) ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
      grind
    zumku
    have hPZ : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by_linarith
    have hle : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw ≤
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe := by
      zux

      exact hsa ztxmr
    zudsg
    · zuito
    · zulxt
  grind

/-- **The kind of the last chord of a chain**: inside a chord of `S₂` whose side `ρ` is the region
`V` of the start, or (with `V`) a gap label; or a shared chord; or a top chord. -/
def ChainKind (S₂ : Set ztf) (ρ : ℝ) (V h : Set Point) : Prop :=
  (∃ c ∈ S₂, h ⊆ c ∧ ∃ V' ∈ (chainModel J.right).regions S₂,
      ztzde ∧ SideOf ztj ρ c V') ∨
    J.shared ∈ h ∨ J.right.top ∈ h

/-- **A chord of `F₂⁺` inside a chord of `S₂x`** is inside a chord of `S₂` (that chord), or is
the chord itself, a shared or a top chord. -/
theorem kind_of_S₂x (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {f c : Set Point}
    (hf : f ∈ F₂plus J S₂) (hc : c ∈ S₂x J S₂) (hfc : f ⊆ c) :
    c ∈ S₂ ∨ J.shared ∈ f ∨ J.right.top ∈ f := by
  rcases hc with hc | ⟨hcF, hcA⟩
  · simp_all
  zuv
  have hfe := hC.nest f hf c hcF hfc
  subst hfe
  rcases F₂plus_kind J hS₂ hf with ⟨c₀, hc₀, hfc₀⟩ | h
  · left
    have := s2_eq_of_sub J subset_rfl hcA (hS₂ hc₀)
      ztleo subset_rfl hfc₀
    simp_all
  simp_all

/-- The kind of the last chord from the tracked data. -/
theorem chainKind_of (hP : J.P.Simple) {S₂ : Set ztf}
    (hS₂ : S₂ ⊆ Merge.augChords J.right) (hS₂f : S₂.Finite) {ρ : ℝ} {V₀ V h : Set Point}
    (hh : h ∈ F₂plus J S₂) (hV : V ∈ (chainModel J.right).regions S₂)
    (hrel : V = V₀ ∨ ztlet)
    (htr : (∃ c ∈ S₂x J S₂, h ⊆ c ∧ SideOf ztj ρ c V) ∨
      (J.shared ∈ h ∨ J.right.top ∈ h)) :
    ChainKind J S₂ ρ V₀ h := by
  rcases htr with ⟨c, hc, hhc, hVs⟩ | hk
  · rcases kind_of_S₂x J hP hS₂ hS₂f hh hc hhc with hc' | hk
    · zulef
    tauto
  tauto

/-- **The end of a chain** (without `TopStrict`): as `ChainEnd`, with the kind of the last chord
(`ChainKind`). -/
def ChainEnd2 (S₂ : Set ztf) (ρ θ : ℝ) (G V : Set Point)
    (Φ : Set Point → ℝ → Prop) : Prop :=
  ∃ h ∈ F₂plus J S₂, ∃ (ph : ℕ) (th : ℝ) (pz : ℕ) (tz : ℝ),
    SideAttach (chainModel J.whole).W h ph th ∧ SideAttach (chainModel J.whole).W h pz tz ∧
    sidePt (chainModel J.whole).W ph th ≠ sidePt (chainModel J.whole).W pz tz ∧
    SideOf ztbm ρ h G ∧
    0 < θ * ρ * ((sidePt (chainModel J.whole).W ph th).1 -
      (sidePt (chainModel J.whole).W pz tz).1) ∧
    ChainKind J S₂ ρ V h ∧
    0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob ∧
    off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob <
      ((rL1 J + rL2 J : ℕ) : ℝ) ∧
    ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe <
        ((rL1 J + rL2 J : ℕ) : ℝ)) ∧
    Φ h (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztcob)

/-- **Walking along a chain of an unlabelled region** without `TopStrict`: as `chain_gen`; the
tracked region `V` of `S₂` is `V₀` or (with `V₀`) a gap label. -/
theorem chain_gen2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ θ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    (hθ : θ = 1 ∨ θ = -1) {G V₀ : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) (hU : ∀ V', ¬ RLabel J S₂ G V')
    (Φ : Set Point → ℝ → Prop) (hΦ : Propag J S₂ Φ) :
    ∀ (N : ℕ) (f : Set Point) (pn : ℕ) (tn : ℝ) (pf : ℕ) (tf : ℝ) (V : Set Point),
      V ∈ (chainModel J.right).regions S₂ → (V = V₀ ∨ ztlet) →
      (beyond ztbi ztbuj ztmok).ncard ≤ N →
      f ∈ F₂plus J S₂ → SideAttach (chainModel J.whole).W f pn tn →
      SideAttach (chainModel J.whole).W f pf tf →
      sidePt (chainModel J.whole).W pn tn ≠ sidePt (chainModel J.whole).W pf tf →
      SideOf ztbm ρ f G →
      0 < θ * ρ * ((sidePt (chainModel J.whole).W pn tn).1 -
        (sidePt (chainModel J.whole).W pf tf).1) →
      (ztwst ∨
        (ztnlx ∧
          ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbbc ∧
            off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbbc <
              ((rL1 J + rL2 J : ℕ) : ℝ)))) →
      0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbue <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      Φ f ztxcr →
      ChainEnd2 J S₂ ρ θ G V₀ Φ := by
  zqbbv
  zqbbx
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro f pn tn pf tf V hV hrel hN hf hfA hfF hNF hS hori htrack hn0 hnL hΦf
  zqbby
  zugye
  zubdh

  · refine ⟨f, hf, pn, tn, pf, tf, hfA, hfF, hNF, hS, hori, ?_, hn0, hnL, hin, hΦf⟩
    exact chainKind_of J hP hS₂.2.1 hS₂.1 hf hV hrel by_grind
  -- the far end is in the right stretch
  obtain ⟨c, hc, hfc, hVs⟩ := htrack.resolve_right by_grind
  zucsv

  have hd' : d' < L := by
    zucvn

    zufc
  zuegw

  -- the step to a partner at the far end
  have hstep : ∀ (f' V' : Set Point), tf = 0 → f' ∈ F₂plus J S₂ → f' ≠ f →
      SideAttach W f' ztxap 0 → SideOf ztbm ρ f' G →
      V' ∈ (chainModel J.right).regions S₂ → (V' = V₀ ∨ ztles) →
      (ztxim ∨
        ztbaod) →
      ChainEnd2 J S₂ ρ θ G V₀ Φ := by
    intro f' V' htf0 hf' hne hA' hS' hV' hrel' hpart
    zucae

    set Pn := sidePt W pn tn with hPndef
    zuhc

    have hθρ : ztmxn := by
      zugl
    have hori' : ztkzn := by
      zugld

    have hΦ' := hΦ f f' pn tn ztxap pb tb hf hf' hne hfA hfF hNF hA' hB hBne hn0
      hnL hin.1 hin.2 hΦf
    rcases hpart with ⟨c', hc', hfc', hVs'⟩ | ⟨hk, hoff⟩
    · -- recursion along the partner
      have hlt : (beyond ztbi ztbuj Bp).ncard <
          (beyond ztbi ztbuj Pf).ncard := by
        zuknj

        · grind
        · zuzg

          zuje
          zujnq
          have : θ * ρ * ztigx =
              zteb * ztluq := by_ring
          nlinarith
      exact ih _ zttst f' _ 0 pb tb V' hV' hrel' le_rfl hf'
        hA' hB ztbsb hS' hori' ztzcm hin.1 hin.2 hΦ'
    · -- the partner leaves the stretch
      exact ⟨f', hf', ztsb % W.n, 0, pb, tb, hA', hB, Ne.symm hBne, hS', hori',
        Or.inr hk, hin.1, hin.2, hoff pb tb hB hBne, hΦ'⟩
  zufrm
  · zufka

    have hδ : ztixu := by
      zuccr
      have := hC.hδ by_omega
      omega
    rcases split_step J hP hS₂ hF hδ hf hc hfc hfF hρ hG hV hS hVs with
      hRL | ⟨-, Vg, -, hRLg⟩ | ⟨hgV, f', hf', hne, hA', hS', hpart⟩
    · grind
    · grind
    · have hgV₀ : GapLab J S₂ V₀ := by
        grind
      zucti
      · exact hstep f' V' rfl hf' hne hA' hS' hV' by_grind
          ztzcm
      · exact hstep f' V rfl hf' hne hA' hS' hV hrel ztvci
  · have hsec' : ztknq := by
      intro htf
      refine ⟨fun h => ?_, by_grind⟩
      zuhqk

    rcases local_step2 J hP hS₂ hF hd' hfF.2.1 hfF.2.2.1 hsec' hf hc hfc hfF hρ hG hV hS hVs
      with hRL | ⟨htf0, f', hf', hne, hA', hS', hpart⟩
    · grind
    · subst htf0
      exact hstep f' V rfl hf' hne hA' hS' hV hrel hpart

/-- **The conclusion of the bracket lemma** for a non-cut position with offset `o₀` in the `C₁`
part facing a region without a label: a chord `h` of `F₂⁺` (in a chord of `S₂` with `V` on the
side of the region, or ending at the shared vertex) is attached at a key `Z` after `o₀` (or at
offset `0`), and no chord of `F₂⁺` with an attachment inside the right stretch (not at offset
`0`) has an attachment between `o₀` and `Z`. -/
def BracketConcl2 (S₂ : Set ztf) (ρ : ℝ) (V : Set Point) (o₀ : ℝ) : Prop :=
  ∃ h ∈ F₂plus J S₂, ∃ (pz : ℕ) (tz : ℝ), SideAttach (chainModel J.whole).W h pz tz ∧
    ChainKind J S₂ ρ V h ∧
    (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe = 0 ∨
      (((rL1 J + rL2 J : ℕ) : ℝ) ≤
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe ∧
        o₀ < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe)) ∧
    ∀ e ∈ F₂plus J S₂, ∀ (pw : ℕ) (tw : ℝ) (pb : ℕ) (tb : ℝ),
      SideAttach (chainModel J.whole).W e pw tw → SideAttach (chainModel J.whole).W e pb tb →
      sidePt (chainModel J.whole).W pw tw ≠ sidePt (chainModel J.whole).W pb tb →
      o₀ < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs →
      (off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe = 0 ∨
        off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbjs <
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthe) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd <
        ((rL1 J + rL2 J : ℕ) : ℝ) →
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztbd ≠ 0 → False

/-- **The bracket lemma, from a tie.**  Let `fb`, `ff` be the two chords of `F₂⁺` of a tie at a
position `A` inside the right stretch, with the region `G` (without a label) on their side `ρ`,
`fb` oriented by `-1` and `ff` by `1`, each contained in a chord of `S₂` with `V` on its side `ρ`
(or ending at the shared vertex).  Then for every non-cut position of the `C₁` part facing `G`,
the conclusion `BracketConcl2` holds. -/
theorem bracket_core2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G V : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hU : ∀ V', ¬ RLabel J S₂ G V')
    {fb ff : Set Point} (hfb : fb ∈ F₂plus J S₂) (hff : ff ∈ F₂plus J S₂) (hbf : fb ≠ ff)
    {pa : ℕ}
    (hA0 : 0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteuk)
    (hAL : off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zteuk <
      ((rL1 J + rL2 J : ℕ) : ℝ))
    (hbA : SideAttach (chainModel J.whole).W fb pa 0)
    (hfA : SideAttach (chainModel J.whole).W ff pa 0) {pbb pff : ℕ} {tbb tff : ℝ}
    (hbB : SideAttach (chainModel J.whole).W fb pbb tbb)
    (hfF : SideAttach (chainModel J.whole).W ff pff tff)
    (hbne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pbb tbb)
    (hfne : sidePt (chainModel J.whole).W pa 0 ≠ sidePt (chainModel J.whole).W pff tff)
    (hbS : SideOf ztbm ρ fb G) (hfS : SideOf ztbm ρ ff G)
    (hbo : 0 < -1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pbb tbb).1))
    (hfo : 0 < 1 * ρ * ((sidePt (chainModel J.whole).W pa 0).1 -
      (sidePt (chainModel J.whole).W pff tff).1))
    {Vb Vf : Set Point} (hVb : Vb ∈ (chainModel J.right).regions S₂)
    (hVf : Vf ∈ (chainModel J.right).regions S₂)
    (hrel : Vf = V ∨ (GapLab J S₂ V ∧ GapLab J S₂ Vf))
    (hbT : (∃ c ∈ S₂x J S₂, fb ⊆ c ∧ SideOf ztj ρ c Vb) ∨
      ((J.shared ∈ fb ∨ J.right.top ∈ fb) ∧
        ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkcf ∧
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztkcf <
            ((rL1 J + rL2 J : ℕ) : ℝ))))
    (hfT : (∃ c ∈ S₂x J S₂, ff ⊆ c ∧ SideOf ztj ρ c Vf) ∨
      ((J.shared ∈ ff ∨ J.right.top ∈ ff) ∧
        ¬ (0 < off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx ∧
          off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) ztdhx <
            ((rL1 J + rL2 J : ℕ) : ℝ))))
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    BracketConcl2 J S₂ ρ V
      ztwmg := by
  zqbbv
  zqbbx
  zqbbu
  have hgn : ztcx := by
    zucfu
  zupz
  set L : ℝ := ((rL1 J + rL2 J : ℕ) : ℝ) with hLdef
  set o₀ := o _ with ho₀def
  set oA := o zteuk with hoAdef
  -- the backward run
  obtain ⟨hb, hhb, pP, tP, pZ, tZ, hPa, hZa, hPZ, hSb, horib, -, hP0, hPL, hZout, hΦb⟩ :=
    chain_gen2 J hP hS₂ hF hρ ztbt hG hU ztrkb
      (propag_K2 J hP hS₂ hF oA) _ fb pa 0 pbb tbb Vb hVb ztp le_rfl hfb hbA hbB hbne
      hbS hbo hbT hA0 hAL (fun _ _ _ _ _ _ _ _ _ _ _ _ hle => hle)
  obtain ⟨hLZb, hZb0⟩ := back_end2 J hP hS₂ hρ hG hhb hPa hZa hPZ hSb horib hPL hZout hp₀ ht₀
    hnc₀ hfG₀ ho₀
  obtain ⟨kP0, kP1⟩ := Corr.key_mem hPa.1 hPa.2.1 hPa.2.2.1
  zufyu
  -- the far attachment of `fb` is before `o₀`
  have hfbfar : ∀ (pw : ℕ) (tw : ℝ), SideAttach (chainModel J.whole).W fb pw tw →
      o₀ < o ztbjs → False := by
    intro pw tw hW hoW
    rcases key_of_two hM (hFs hfb) hbA hbB hbne hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    · have hout : ¬ (0 < o ztbjs ∧ o ztbjs < L) := by_grind
      have := back_end2 J hP hS₂ hρ hG hfb hbA hbB hbne hbS hbo hAL hout hp₀ ht₀ hnc₀ hfG₀ ho₀
      grind
  -- the base of the forward run
  have hbase : PhiI J S₂ o₀ ff oA := by
    intro e he hne pw tw pb tb hW hB hWB hoW hoB
    have heb : e ≠ fb := by_grind
    have hehb : e ≠ hb := by
      zunq
      rcases key_of_two hM ztcik hPa hZa hPZ hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
    zucoa
    have hBP : o ztbd ≤ o (pP + tP) := by
      zux

      have := no_cross_off hM hFs hF.1 hhb he (Ne.symm hehb) hPa hZa hPZ hB hW hg0 hgn
        by_linarith hc by_linarith
      grind
    have hle := hΦb e he hehb pw tw pb tb hW hB hWB by_linarith hoB hBP
    zubug
    · zubh
    · zubvx

      rcases tie_third hM hFs hff hfb he (Ne.symm hbf) hfA hbA hB with h' | h'
      · grind
      grind
  -- the forward run
  obtain ⟨hf, hhf, qP, sP, qZ, sZ, hQa, hZa', hQZ, hSf, horif, hTf, hQ0, hQL, hZout', hΦf⟩ :=
    chain_gen2 J hP hS₂ hF hρ ztp hG hU (PhiI J S₂ o₀)
      (propag_I2 J hP hS₂ hF ho₀.le) _ ff pa 0 pff tff Vf hVf hrel le_rfl hff hfA hfF hfne hfS
      hfo hfT hA0 hAL hbase
  have hfe := fwd_end2 J hP hS₂ hρ hG hhf hQa hZa' hQZ hSf horif hQL hZout' hp₀ ht₀ hnc₀ hfG₀
    ho₀
  refine ⟨hf, hhf, qZ, sZ, hZa', hTf, hfe, ?_⟩
  intro e he pw tw pb tb hW hB hWB hoW hoZ hoB hB0
  zucoa
  have hehf : e ≠ hf := by
    zunq
    rcases key_of_two hM ztcik hQa hZa' hQZ hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · linarith
    grind
  have h1 := hΦf e he hehf pw tw pb tb hW hB hWB hoW hoB
  zugrt
  · zuhwn
    have := no_cross_off hM hFs hF.1 hhf he ztvbd hZa' hQa (Ne.symm hQZ) hB hW hg0 hgn
      by_grind by_grind h1
    grind
  · zuklu
    · linarith
    · have := no_cross_off hM hFs hF.1 hhf he ztvbd hQa hZa' hQZ hW hB hg0 hgn
        by_linarith by_linarith h
      grind

/-- **The bracket lemma.**  Let `G` be a region of `F₂⁺` without a label, on the side `ρ` of a
chord `e ⊆ c ∈ S₂` of `F₂⁺` attached at a position of the right stretch (not the base or the
split vertex), with `V` on the side `ρ` of `c`.  Then for every non-cut position of the `C₁` part
facing `G`, the next chord of `F₂⁺` with an attachment in the right stretch is a chord in a
chord of `S₂` with `V` on the side of `G` (or ends at the shared vertex) — `BracketConcl2`. -/
theorem bracket2 (hP : J.P.Simple) {Q : Polygon}
    {S₂ : Set ztf} (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {ρ : ℝ} (hρ : ρ = 1 ∨ ρ = -1)
    {G V : Set Point} (hG : G ∈ (chainModel J.whole).regions ztbi)
    (hV : V ∈ (chainModel J.right).regions S₂) (hU : ∀ V', ¬ RLabel J S₂ G V')
    {e c : Set Point} (he : e ∈ F₂plus J S₂) (hc : c ∈ S₂) (hec : e ⊆ c) {d : ℕ}
    (hd : d < rL1 J + rL2 J) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hsec : t = 0 → d ≠ 0 ∧ d ≠ rL1 J)
    (heA : SideAttach (chainModel J.whole).W e
      ztbn t)
    (hGs : SideOf ztbm ρ e G) (hVs : SideOf ztj ρ c V)
    {p₀ : ℕ} {t₀ : ℝ} (hp₀ : p₀ < (chainModel J.whole).W.n) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (hnc₀ : ¬ (chainModel J.whole).IsCut ztbi zthw)
    (hfG₀ : (chainModel J.whole).Faces p₀ t₀ G)
    (ho₀ : ((rL1 J + rL2 J : ℕ) : ℝ) <
      off (chainModel J.whole).W.n ((6 + tpos J.whole J.m₁ : ℕ) : ℝ) zthw) :
    BracketConcl2 J S₂ ρ V
      ztwmg := by
  zqbbv
  zqbbx
  zuixs
  rcases local_step2 J hP hS₂ hF hd ht0 ht1 hsec he hcx hec heA hρ hG hV hGs hVs with
    hRL | ⟨rfl, f', hf', hne, hA', hS', hpart⟩
  · simp_all
  zukbr
  zqbby
  zuinq
  zukw

  have h1 : ztdrh :=
    by grind
  have h1' : ztdri :=
    by grind
  zubqv

  have hθρ : ztxfm := by
    zugl
  have hori' : ztxpm := by
    have e1 : -θ * ρ * ztbak =
        θ * ρ * ztix := by_ring
    zukd
    have hprod : 0 < ztrm *
        ztwvg := by
      have e2 : ztrm *
          ztwvg =
          ztxho * (-(ztdem *
            ztix)) := by_ring
      zubyo

    zugkj
  zuiys
  have hA0 : ztygk := by
    zueyd
    positivity
  have hAL : ztxbw := by
    zueyd
    zubfq
    linarith
  have hTf' : (∃ c ∈ S₂x J S₂, f' ⊆ c ∧ SideOf ztj ρ c V) ∨
      (ztbym ∧
        ¬ (0 < off W.n (g : ℝ) zteun ∧ off W.n (g : ℝ) zteun <
          ((rL1 J + rL2 J : ℕ) : ℝ))) := by
    rcases hpart with h | ⟨hk, h⟩
    · zueou
    · exact Or.inr ⟨hk, h pb' tb' hB' hBne'⟩
  zugaf
  · exact bracket_core2 J hP hS₂ hF hρ hG hU hf' he hne hA0 hAL hA' heA hB' hB
      zthrn ztbsb hS' hGs by_linarith hori hV hV ztp hTf'
      ztfbd hp₀ ht₀ hnc₀ hfG₀ ho₀
  · exact bracket_core2 J hP hS₂ hF hρ hG hU he hf' ztnr hA0 hAL heA hA' hB hB'
      ztbsb zthrn hGs hS' hori by_linarith hV hV ztp
      ztfbd hTf' hp₀ ht₀ hnc₀ hfG₀ ho₀
end ChainWalk2
end Sweep
end
end Chazelle.Core
end
section
set_option hygiene false
local macro "zqblx" : tactic => `(tactic| refine spec_skip ‹_› ⟨by_omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩)
local macro "zqbly" : tactic => `(tactic| (refine spec_seq ?_
                                           exec_block
                                           zujl
                                           obtain ⟨c₁, k₁, e₁, hk₁, rfl⟩ := ivF_exec (P := P) _ ‹_› (by config_simp; exact hS.r11)
                                           refine zthmi
                                           zud
                                           zujl
                                           exec_block))
local macro "zqblz" : tactic => `(tactic| have hQ : ztx := shear_n _ _)
local macro "zqbma" : tactic => `(tactic| refine ⟨by_omega, ?_, fun r h1 h2 => ?_⟩)
local macro "zqbmb" : tactic => `(tactic| (intro hc
                                           rcases ztta with h3 | h3))
local macro "zqbmc" : tactic => `(tactic| (exec_block
                                           all_goals first | omega | skip))
local macro "zqbmd" : tactic => `(tactic| (zumyp; rw [ite_eq_right h1]; exact F₁.1 r h2))
set_option hygiene true

/-!
# WP-M (E7-B, RAM part 3): the normalized query

`normI` computes, from the saved subarc ends `⟨e₁, h₁⟩`, `⟨e₂, h₂⟩`:

* `170030`: the normalized end code `h₂' = nh e₂ h₂` (`normA`);
* `170031`: the offset `ee = eeOf e₁ h₁ e₂ h₂'` of the end edge (`normB`, `normC`; on one edge,
  the key order by two sign tests, `ltS`);
* `170032`: the number `L = spanL ee h₂'` of walk edges met (`normD`).

Scratch: `170092 … 170129` and the sign kernel.
-/
namespace Chazelle.Core
namespace IOrc
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
variable {Q : Polygon}

/-! ## Mathematics -/

/-- The height vertex of a position of the interior walk (the start vertex for the code `0`). -/
noncomputable def hI (Q : Polygon) (e h : ℕ) : ℕ := if h = 0 then iv Q e else h - 1
theorem mi_hgtY {e h : ℕ} (he : e < Q.n) :
    (interiorModel Q).hgtY Q ztcq = (Q.vtx ztlpm).2 := by
  unfold hI Model.hgtY
  cases h with
  | zero => zuohl; rw [mi_wa he]
  | succ h => simp

/-- **Parameters on one edge of the interior walk** compare like the heights of their height
vertices, in the direction of the edge. -/
theorem param_lt_iff_iw (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {e h h' : ℕ} (he : e < Q.n) :
    (interiorModel Q).param Q ztcq < (interiorModel Q).param Q ztkkv ↔
      ((Q.vtx ztfss).2 < (Q.vtx ztbame).2 ∧
          (Q.vtx ztlpm).2 < (Q.vtx ztrrm).2) ∨
        (¬ (Q.vtx ztfss).2 < (Q.vtx ztbame).2 ∧
          (Q.vtx ztrrm).2 < (Q.vtx ztlpm).2) := by
  have hnh : ztcrb := by
    zudfx

    · zqbmb
      · zubym
      · zubpy
    · zqbmb
      · zubym
      · zubpy
  have hk := Model.key_lt_key_iff_of_same_edge (Q := Q)
    (x := ztcq) (y := ztkkv) rfl hnh
  zuckv
  simp only [add_lt_add_iff_left] at hk
  rw [hk, mi_hgtY he, mi_hgtY he, mi_wa he, mi_wb he]
  have hnh' := hnh
  rw [mi_wa he, mi_wb he] at hnh'
  grind
theorem dOf_eq {n e₁ e₂ : ℕ} (h1 : e₁ < n) (h2 : e₂ < n) :
    WalkEmbed.dOf n e₁ e₂ = if e₂ + n - e₁ < n then e₂ + n - e₁ else e₂ + n - e₁ - n := by
  unfold WalkEmbed.dOf
  zus
  · zubql
  · zul

/-! ## The programs -/

/-- The normalized end code into `170030`. -/
def normA : Stmt :=
  .seq (block [.copyN 170095 170003]) (.seq ivF
    (.seq (block [.copyN 170100 170096, .copyN 170030 170004, .subN 170101 170004 170011])
      (.ifLtN 170012 170004
        (.ifLtN 170101 170100 .skip (.ifLtN 170100 170101 .skip (block [.constN 170030 0])))
        .skip)))

/-- `170102 := dOf n e₁ e₂`. -/
def normB : Stmt :=
  .seq (block [.addN 170102 170003 170010, .subN 170102 170102 170001])
    (.ifLtN 170102 170010 .skip (block [.subN 170102 170102 170010]))

/-- The kernel slots of the key comparison on one edge. -/
def ltSlots : Stmt :=
  block [.constN 170110 0, .copyN 170111 170106, .constN 170113 0, .copyN 170114 170107,
    .constN 170116 0, .copyN 170117 170104, .constN 170119 0, .copyN 170120 170105]

/-- The preparation of the key comparison: the four height vertices into the kernel slots. -/
def ltPrep : Stmt :=
  .seq (block [.copyN 170095 170001]) (.seq ivF
    (.seq (block [.copyN 170106 170096, .addN 170095 170001 170011])
      (.seq (.ifLtN 170095 170010 .skip (block [.constN 170095 0]))
        (.seq ivF
          (.seq (block [.copyN 170107 170096, .copyN 170104 170106, .subN 170105 170030 170011])
            (.seq (.ifLtN 170012 170002 (block [.subN 170104 170002 170011]) .skip)
              ltSlots))))))

/-- The two sign tests of the key comparison. -/
def ltKer : Stmt :=
  .seq (SweepPrim.kbit 170110 170113 170110 1 170108)
    (.ifLtN 170012 170108 (SweepPrim.kbit 170116 170119 170116 1 170103)
      (SweepPrim.kbit 170119 170116 170119 1 170103))

/-- **The key order on the start edge** (`170103`), for a nonzero end code. -/
def ltK : Stmt := .seq ltPrep ltKer

/-- The key order on the start edge: false for the end code `0`. -/
def ltS : Stmt := .ifLtN 170030 170011 (block [.constN 170103 0]) ltK

/-- The offset of the end edge into `170031`. -/
def normC : Stmt :=
  .ifLtN 170012 170102 (block [.copyN 170031 170102])
    (.seq ltS (.ifLtN 170012 170103 (block [.constN 170031 0]) (block [.copyN 170031 170010])))

/-- The number of edges met into `170032`. -/
def normD : Stmt :=
  .seq (block [.copyN 170032 170031])
    (.ifLtN 170012 170030 (block [.addN 170032 170032 170011]) .skip)

/-- **The normalized query.** -/
def normI : Stmt := .seq normA (.seq normB (.seq normC normD))

/-- The registers `normI` writes: `170030 … 170032`, the scratch `170090 … 170129`, the
kernel. -/
def Bnorm (r : ℕ) : Bool :=
  decide (170030 ≤ r ∧ r < 170033) || decide (170090 ≤ r ∧ r < 170130) || Bk r
theorem wr_normI : wr Bnorm normI = true := by
  rfl

/-! ## Execution -/
section exec
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **The normalized end code.** -/
theorem normA_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) :
    ∃ c' k, Exec P W normA c c' k ∧ k ≤ 14 ∧ c'.nreg 170030 = nh zta s.e₂ s.h₂ ∧
      (∀ r, r ≠ 170030 → r ≠ 170095 → r ≠ 170096 → r ≠ 170100 → r ≠ 170101 →
        c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  unfold normA
  zqbly
  have hσ : ivV ztjrv ztmft (c.nreg 170003) = iv zta s.e₂ := by
    rw [hS.ivv, hS.r3]
  by_cases h0 : c.nreg 170012 < c.nreg 170004
  · zuek
    by_cases h1 : c.nreg 170004 - 1 < iv zta s.e₂
    · refine spec_ifLtN_true (by config_simp; rw [hS.r11, hσ]; exact h1) ?_
      zqblx
      · config_simp; unfold nh; rw [hS.r4, ite_eq_right (by rw [hS.r4] at h1; omega)]
      simp_all
    by_cases h2 : iv zta s.e₂ < c.nreg 170004 - 1
    · refine spec_ifLtN_false (by config_simp; rw [hS.r11, hσ]; exact h1)
        (spec_ifLtN_true (by config_simp; rw [hS.r11, hσ]; exact h2) ?_)
      zqblx
      · config_simp; unfold nh; rw [hS.r4, ite_eq_right (by rw [hS.r4] at h2; omega)]
      simp_all
    · refine spec_ifLtN_false (by config_simp; rw [hS.r11, hσ]; exact h1)
        (spec_ifLtN_false (by config_simp; rw [hS.r11, hσ]; exact h2) ?_)
      zqbmc
      refine ⟨by_omega, ?_, fun r a b d e f => ?_, rfl, rfl, rfl, rfl⟩
      · config_simp; unfold nh
        rw [hS.r12, hS.r4] at h0; rw [hS.r4] at h1 h2
        grind
      simp_all
  · zudx
    zqblx
    · config_simp; unfold nh; rw [hS.r12, hS.r4] at h0; rw [hS.r4, ite_eq_right by_omega]
    simp_all

/-- **The offset of the end edge** (`dOf`). -/
theorem normB_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (h1 : s.e₁ < P.n) (h2 : s.e₂ < P.n) :
    ∃ c' k, Exec P W normB c c' k ∧ k ≤ 5 ∧ c'.nreg 170102 = WalkEmbed.dOf P.n s.e₁ s.e₂ ∧
      c' = { c with nreg := upd c.nreg 170102 (c'.nreg 170102) } := by
  zucg

  unfold normB
  refine spec_seq ?_
  exec_block
  · config_simp; rw [hS.r3, hS.r10]; omega
  by_cases hc : s.e₂ + P.n - s.e₁ < P.n
  · refine spec_ifLtN_true (by config_simp; rw [hS.r3, hS.r10, hS.r1]; exact hc) ?_
    zuknr
    · config_simp; rw [hS.r3, hS.r10, hS.r1, dOf_eq h1 h2, ite_eq_left hc]
    simp
  · refine spec_ifLtN_false (by config_simp; rw [hS.r3, hS.r10, hS.r1]; exact hc) ?_
    exec_block
    zujfy
    · config_simp; rw [hS.r3, hS.r10, hS.r1, dOf_eq h1 h2, ite_eq_right hc]
    simp
end exec

/-- The registers `ltS` writes. -/
def BltS (r : ℕ) : Bool :=
  decide (r = 170092 ∨ r = 170095 ∨ r = 170096 ∨ (170103 ≤ r ∧ r < 170122)) || Bk r
theorem wr_ltS : wr BltS ltS = true := by
  rfl
section exec2
variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- The registers `ltPrep` writes. -/
def Bprep (r : ℕ) : Bool :=
  decide (r = 170092 ∨ r = 170095 ∨ r = 170096 ∨ (170104 ≤ r ∧ r < 170122))
theorem wr_ltPrep : wr Bprep ltPrep = true := by_decide

/-- **The preparation**: the kernel slots hold the vertices `iv e₁`, `iv (e₁ + 1)` (the ends of
the start edge) and the height vertices of the two positions. -/
theorem ltPrep_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) {h₂ : ℕ} (h30 : c.nreg 170030 = h₂) :
    ∃ c' k, Exec P W ltPrep c c' k ∧ k ≤ 40 ∧
      SymPtIn c' 170110 ztyvb ∧
      SymPtIn c' 170113 ztyvc ∧
      SymPtIn c' 170116 ztyoj ∧
      SymPtIn c' 170119 ztzao ∧ FrameB Bprep c c' := by
  zucwc
  obtain ⟨c', k, ex, hk, post⟩ : ∃ c' k, Exec P W ltPrep c c' k ∧ k ≤ 40 ∧
      (SymPtIn c' 170110 ztyvb ∧
      SymPtIn c' 170113 ztyvc ∧
      SymPtIn c' 170116 ztyoj ∧
      SymPtIn c' 170119 ztzao) := by
    unfold ltPrep
    zqbly
    · config_simp; rw [hS.r1, hS.r11]; omega
    zujl
    -- `(e₁ + 1) mod n` in `170095`
    obtain ⟨k₂, e₂, hk₂⟩ := exec_ite_upd (P := P) (W := W) (a := 170095) (b := 170010)
      (r := 170095) (s₁ := .skip) (s₂ := block [.constN 170095 0]) (v₂ := 0) (K := 1) _
      (fun _ => ⟨0, exec_skip_upd ‹_› 170095, by_omega⟩)
      (fun _ => ⟨1, exec_constN_upd ‹_› 170095 0 by_omega, le_rfl⟩)
    refine ⟨_, _, e₂, ?_⟩
    zue
    zujl
    obtain ⟨c₃, k₃, e₃, hk₃, rfl⟩ := ivF_exec (P := P) _ w₂ (by config_simp; exact hS.r11)
    refine ⟨_, _, e₃, ?_⟩
    zubj
    refine spec_seq ?_
    exec_block
    zujl
    obtain ⟨k₄, e₄, hk₄⟩ := exec_ite_upd (P := P) (W := W) (a := 170012) (b := 170002)
      (r := 170104) (s₁ := block [.subN 170104 170002 170011]) (s₂ := .skip) (K := 1) _
      (fun _ => ⟨1, exec_subN_upd ‹_› 170104 170002 170011, le_rfl⟩)
      (fun _ => ⟨0, exec_skip_upd ‹_› 170104, by_omega⟩)
    refine ⟨_, _, e₄, ?_⟩
    zucc
    unfold ltSlots
    zqbmc
    have hlb := hS.lb
    have hlb1 := hS.lb1
    zqblz
    refine ⟨by_omega, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩, ⟨by config_simp, ?_⟩,
      ⟨by config_simp, ?_⟩⟩
    · config_simp; rw [hS.ivv, hS.r1]
    · config_simp
      rw [hS.r1, hS.r11, hS.r10, hS.ivv]
      zucr
      zugif
      · zulpi
      · rw [show s.e₁ + 1 = P.n by omega, Nat.mod_self]
    · config_simp
      rw [hS.r12, hS.r2, hS.r11, hS.ivv, hS.r1]
      unfold hI
      grind
    · config_simp; rw [h30, hS.r11]
  exact ⟨c', k, ex, hk, post.1, post.2.1, post.2.2.1, post.2.2.2, exec_frameB ex wr_ltPrep⟩

/-- **The two sign tests**: the bit `170103` is the key order of the two positions. -/
theorem ltKer_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (h12 : c.nreg 170012 = 0) {a b x y : ℕ} (ha : a < P.n) (hb : b < P.n) (hx : x < P.n)
    (hy : y < P.n) (s1 : SymPtIn c 170110 ztpsg) (s2 : SymPtIn c 170113 (.vtx b))
    (s3 : SymPtIn c 170116 (.vtx x)) (s4 : SymPtIn c 170119 (.vtx y)) :
    ∃ c' k, Exec P W ltKer c c' k ∧ k ≤ 490 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 ∧ ((Qof P).vtx x).2 < ((Qof P).vtx y).2 ∨
        ¬ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 ∧ ((Qof P).vtx y).2 < ((Qof P).vtx x).2) := by
  unfold ltKer
  obtain ⟨c₁, k₁, e₁, hk₁, F₁, b₁, t₁⟩ := SweepPrim.kbit_exec (P := P) hG hW c hw
    (a := 170110) (b := 170113) (d := 170110) (op := 1) (dst := 170108) by_norm_num
    by_norm_num by_norm_num by_norm_num by_norm_num (sa := .vtx a) (sb := .vtx b)
    (sd := .vtx a) ha hb ha s1 s2 s1
  have kp : ∀ r, 10500 ≤ r → r ≠ 170108 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    F₁.1 r (by simp only [SweepPrim.Bkb, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne]; omega)
  have s3' : SymPtIn c₁ 170116 _ := NFLoc.symPtIn_copy s3 by_simp_all
    by_simp_all by_simp_all
  have s4' : SymPtIn c₁ 170119 _ := NFLoc.symPtIn_copy s4 by_simp_all
    by_simp_all by_simp_all
  simp only [SignTest, SymPt.eval] at t₁
  have h12' : ztpmu := by_simp_all
  by_cases hup : c₁.nreg 170012 < c₁.nreg 170108
  · obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec hG hW c₁ e₁.wb_right (op := 1) (dst := 170103) by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num (sa := .vtx x) (sb := .vtx y)
      (sd := .vtx x) hx hy hx s3' s4' s3'
    zubzp
    have hu : ((Qof P).vtx a).2 < ((Qof P).vtx b).2 := by_grind
    refine ⟨c₂, _, .seq e₁ (.ifLtN_true hup e₂), by_omega, b₂, ?_⟩
    simp_all
  · obtain ⟨c₂, k₂, e₂, hk₂, F₂, b₂, t₂⟩ := SweepPrim.kbit_exec hG hW c₁ e₁.wb_right (op := 1) (dst := 170103) by_norm_num
      by_norm_num by_norm_num by_norm_num by_norm_num (sa := .vtx y) (sb := .vtx x)
      (sd := .vtx y) hy hx hy s4' s3' s4'
    zubzp
    have hu : ¬ ((Qof P).vtx a).2 < ((Qof P).vtx b).2 := by_simp_all
    refine ⟨c₂, _, .seq e₁ (.ifLtN_false hup e₂), by_omega, b₂, ?_⟩
    simp_all

/-- **The key order on the start edge** (`170103`, for the end code in `170030`). -/
theorem ltS_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (hh1 : s.h₁ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel zta).param zta ztbra) {h₂ : ℕ}
    (h30 : c.nreg 170030 = h₂) (h2n : h₂ ≤ P.n) :
    ∃ c' k, Exec P W ltS c c' k ∧ k ≤ 840 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ (interiorModel zta).param zta ztbra <
        (interiorModel zta).param zta ztujl) ∧ FrameB BltS c c' := by
  zqblz
  have hD : DistinctHeights _ := ShootCut.goodEnv_distinct hS.good
  zucgt
  zucwc
  obtain ⟨c', k, ex, hk, b, t⟩ : ∃ c' k, Exec P W ltS c c' k ∧ k ≤ 840 ∧ c'.nreg 170103 ≤ 1 ∧
      (c'.nreg 170103 = 1 ↔ (interiorModel zta).param zta ztbra <
        (interiorModel zta).param zta ztujl) := by
    unfold ltS
    by_cases h0 : c.nreg 170030 < c.nreg 170011
    · have hz : h₂ = 0 := by zuorq; zvnem at h0; omega
      zujfh
      zqbmc
      simp_all
    · refine spec_ifLtN_false h0 ?_
      have h21 : 1 ≤ h₂ := by zuorq; zvnem at h0; omega
      obtain ⟨c₁, k₁, e₁, hk₁, s1, s2, s3, s4, F₁⟩ := ltPrep_exec c hw hS he1 h30
      have k12 : ztpmu := by
        zuhjv
      have hl := by_omega
      obtain ⟨c₂, k₂, e₂, hk₂, b₂, t₂⟩ := ltKer_exec c₁ e₁.wb_right hS.good hW k12
        (by have := iv_lt (Q := Qof P) (p := s.e₁) by_omega; omega) (by
          have := iv_lt (p := (s.e₁ + 1) % P.n) (by zvnao; exact Nat.mod_lt _ by_omega)
          omega)
        (by unfold hI; split_ifs
            · have := iv_lt (Q := Qof P) (p := s.e₁) by_omega; omega
            · omega)
        by_omega s1 s2 s3 s4
      refine ⟨c₂, _, .seq e₁ e₂, by_omega, b₂, ?_⟩
      rw [t₂, param_lt_iff_iw hD by_omega by_omega, hQ]
      have : hI zta s.e₁ h₂ = h₂ - 1 := by unfold hI; grind
      simp_all
  exact ⟨c', k, ex, hk, b, t, exec_frameB ex wr_ltS⟩
theorem wr_normC : wr (fun r => BltS r || decide (r = 170031)) normC = true := by
  rfl

/-- **The offset of the end edge** into `170031`. -/
theorem normC_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (he2 : s.e₂ < P.n) (hh1 : s.h₁ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel zta).param zta ztbra) {h₂ : ℕ}
    (h30 : c.nreg 170030 = h₂) (h2n : h₂ ≤ P.n)
    (h102 : c.nreg 170102 = WalkEmbed.dOf P.n s.e₁ s.e₂) :
    ∃ c' k, Exec P W normC c c' k ∧ k ≤ 850 ∧ c'.nreg 170031 = eeOf zta s.e₁ s.h₁ s.e₂ h₂ ∧
      (∀ r, r ≠ 170031 → BltS r = false → c'.nreg r = c.nreg r) := by
  zqblz
  zucwc
  unfold normC eeOf
  zuext
  by_cases hd : c.nreg 170012 < c.nreg 170102
  · refine spec_ifLtN_true hd ?_
    exec_block
    zqbma
    · config_simp; grind
    simp_all
  · refine spec_ifLtN_false hd ?_
    have hd0 : WalkEmbed.dOf P.n s.e₁ s.e₂ = 0 := by rw [hS.r12, h102] at hd; omega
    have he : s.e₂ = s.e₁ := by
      have := WalkEmbed.add_dOf he1 he2
      rw [hd0, Nat.add_zero, Nat.mod_eq_of_lt he1] at this; omega
    obtain ⟨c₁, k₁, e₁, hk₁, b₁, t₁, F₁⟩ := ltS_exec c hw hS he1 hh1 hx0 h30 h2n
    have k12 : ztpmu := by
      zuhjv
    have k10 : c₁.nreg 170010 = P.n := by
      rw [F₁.1 _ by_rfl]; exact hS.r10
    zud
    zugar
    rw [ite_eq_left hd0, he]
    by_cases hb : c₁.nreg 170012 < c₁.nreg 170103
    · zugst
      zqbmc
      zqbma
      · config_simp; grind
      · zqbmd
    · zugsq
      exec_block
      zqbma
      · simp_all
      · zqbmd

/-- **The number of edges met** into `170032`. -/
theorem normD_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c) {h₂ ee : ℕ}
    (h30 : c.nreg 170030 = h₂) (h31 : c.nreg 170031 = ee) (hee : ee + 1 ≤ W) :
    ∃ c' k, Exec P W normD c c' k ∧ k ≤ 4 ∧ c'.nreg 170032 = spanL ee h₂ ∧
      c' = { c with nreg := upd c.nreg 170032 (c'.nreg 170032) } := by
  unfold normD spanL
  refine spec_seq ?_
  exec_block
  by_cases h : c.nreg 170012 < c.nreg 170030
  · zuek
    exec_block
    · config_simp; rw [h31, hS.r11]; omega
    zujfy
    · config_simp; rw [h31, hS.r11, ite_eq_right by_omega]
    simp
  · zudx
    zuknr
    · config_simp; rw [h31, ite_eq_left (by rw [hS.r12, h30] at h; omega), Nat.add_zero]
    simp
theorem eeOf_le {Q : Polygon} {e₁ h₁ e₂ h₂ : ℕ} (hn : 0 < Q.n) : eeOf Q e₁ h₁ e₂ h₂ ≤ Q.n := by
  unfold eeOf
  have := WalkEmbed.dOf_lt hn e₁ e₂
  grind

/-- **The normalized query.** -/
theorem normI_exec (c : Config) (hw : WordsBounded W c) (hS : SEnv P W O s c)
    (he1 : s.e₁ < P.n) (he2 : s.e₂ < P.n) (hh1 : s.h₁ ≤ P.n) (hh2 : s.h₂ ≤ P.n)
    (hx0 : 0 ≤ (interiorModel zta).param zta ztbra) :
    ∃ c' k, Exec P W normI c c' k ∧ k ≤ 900 ∧
      c'.nreg 170030 = nh zta s.e₂ s.h₂ ∧
      c'.nreg 170031 = eeOf zta s.e₁ s.h₁ s.e₂ ztwla ∧
      c'.nreg 170032 = spanL ztbakl
        ztwla ∧ FrameB Bnorm c c' := by
  zqblz
  zucg

  obtain ⟨c₁, k₁, e₁, hk₁, a30, ka, ma, -, -, -⟩ := normA_exec c hw hS
  have S₁ : zteeb := hS.keep by_grind by_simp_all (by rw [ka _ by_decide by_decide
      by_decide by_decide by_decide])
  obtain ⟨c₂, k₂, e₂, hk₂, b102, hc₂⟩ := normB_exec c₁ e₁.wb_right S₁ he1 he2
  have kb : ∀ r, r ≠ 170102 → c₂.nreg r = c₁.nreg r := fun r hr => by
    zumxp; zunaw
  have S₂ : zthoi := S₁.keep by_grind
    (fun a _ => by zumxp) (by zuokh)
  have h2n : nh zta s.e₂ s.h₂ ≤ P.n := le_trans nh_le hh2
  obtain ⟨c₃, k₃, e₃, hk₃, c31, kc⟩ := normC_exec c₂ e₂.wb_right S₂ he1 he2 hh1 hx0
    (h₂ := nh zta s.e₂ s.h₂) by_grind h2n b102
  have S₃ := S₂.keep (fun r h1 h2 => kc r by_omega
      (by unfold BltS Bk; grind))
    (fun a _ => by rw [(exec_frameB e₃ (wr_normC)).2.2.1]) (by
      rw [kc _ by_decide by_decide])
  have hee := eeOf_le (Q := Qof P) (e₁ := s.e₁) (h₁ := s.h₁) (e₂ := s.e₂)
    (h₂ := nh zta s.e₂ s.h₂) by_omega
  zvnao at hee
  obtain ⟨c₄, k₄, e₄, hk₄, d32, hc₄⟩ := normD_exec c₃ e₃.wb_right S₃
    (h₂ := nh zta s.e₂ s.h₂) (by zunou; omega)
    c31 by_omega
  have ex : Exec P W normI c c₄ _ := .seq e₁ ztcb
  refine ⟨c₄, _, ex, by_omega, ?_, ?_, d32, exec_frameB ex wr_normI⟩
  · zunbf; zumyp
    zunou; grind
  · zunbf; zumyp; grind
