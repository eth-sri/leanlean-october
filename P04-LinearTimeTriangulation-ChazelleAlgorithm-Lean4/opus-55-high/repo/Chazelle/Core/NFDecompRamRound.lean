module

public import Chazelle.MacT
public import Chazelle.Core.NFDecompRamInit
public import Chazelle.Core.ClusterStepMain
public import Chazelle.Core.ClusterEulerRam

section
set_option hygiene false
local macro "zqbjb" : tactic => `(tactic| simp only [next, rsOf, ite_eq_left hr])
local macro "zqbjc" : tactic => `(tactic| (unfold rpv
                                           rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, hN]
                                           by_cases ht : tv m2 A R 8 r = r))
local macro "zqbjd" : tactic => `(tactic| (rw [hN]; simp only [next, rsOf, ite_eq_right (show ¬ r < R by omega), tv]))
local macro "zqbje" : tactic => `(tactic| rw [a4 r hr, a5 r hr, a12 _ (hp' r hr ht), hN])
local macro "zqbjf" : tactic => `(tactic| (have hbr := hb' r hr ht ha
                                           rw [a4 _ hbr, a5 _ hbr]))
local macro "zqbjg" : tactic => `(tactic| by_cases ha : tv m0 A R 13 r = 1)
local macro "zqbjh" : tactic => `(tactic| (have hKR : ztmtk := by have := h.hR; omega
                                           have hR0 : ztgac := by_omega))
set_option hygiene true

/-!
# Tree decomposition (WP-C), part 19: one round on the RAM realises `next`

* `round_mem`: the memory after the four passes of a round holds `next` of the memory before it
  (read through `rsOf`), with `top`, `best` the fields written by the top pass.
-/
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs Chazelle.Core.Dec
@[expose] public section
section nowr
def ndst : Instr → Option ℕ
  | .inputSize r => some r
  | .constN r _ => some r
  | .copyN r _ => some r
  | .addN r _ _ => some r
  | .subN r _ _ => some r
  | .loadN r _ => some r
  | _ => none

/-- The statement never writes the numeric register `x`. -/
def NoWr (x : ℕ) : Stmt → Bool
  | .skip => true
  | .instr i => ndst i != some x
  | .seq s t => NoWr x s && NoWr x t
  | .ifLtN _ _ t e => NoWr x t && NoWr x e
  | .ifLtR _ _ t e => NoWr x t && NoWr x e
  | .whileLtN _ _ b => NoWr x b
  | .whileLtR _ _ b => NoWr x b
variable {P : Polygon} {W : ℕ}
variable {x : ℕ}
/-- An instruction not writing the numeric register `x` keeps it. -/
theorem nreg_effect {ins : Instr} {c c' : Config} (he : ins.effect P c = some c')
    (hx : ndst ins ≠ some x) : c'.nreg x = c.nreg x := by
  cases ins <;> simp only [ndst, ne_eq, Option.some.injEq] at hx <;> simp [Instr.effect] at he
  all_goals first
    | (subst he; rfl)
    | (subst he; exact Machine.upd_other _ _ _ (Ne.symm hx))
    | (obtain ⟨-, rfl⟩ := he; rfl)

/-- A register a statement never writes keeps its value. -/
theorem nreg_of_noWr {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : NoWr x s = true) : c'.nreg x = c.nreg x := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ =>
    exact nreg_effect he (by simpa [NoWr] using hs)
  | seq _ _ ih1 ih2 =>
    simp only [NoWr, Bool.and_eq_true] at hs
    rw [ih2 hs.2, ih1 hs.1]
  | ifLtN_true _ _ ih => simp only [NoWr, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtN_false _ _ ih => simp only [NoWr, Bool.and_eq_true] at hs; exact ih hs.2
  | ifLtR_true _ _ ih => simp only [NoWr, Bool.and_eq_true] at hs; exact ih hs.1
  | ifLtR_false _ _ ih => simp only [NoWr, Bool.and_eq_true] at hs; exact ih hs.2
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih1 ih2 => zunzm
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih1 ih2 => zunzm

/-- The round counters are written only where intended. -/
theorem noWr_passes : NoWr 60022 p1S = true ∧ NoWr 60023 p1S = true ∧ NoWr 60024 p1S = true ∧
    NoWr 60022 p2S = true ∧ NoWr 60023 p2S = true ∧ NoWr 60024 p2S = true ∧
    NoWr 60022 cpS = true ∧ NoWr 60023 cpS = true ∧ NoWr 60024 cpS = true ∧
    NoWr 60022 rootS = true ∧ NoWr 60023 rootS = true ∧
    NoWr 60022 rpS = true ∧ NoWr 60024 rpS = true := by_decide
end nowr
section facts
variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ} {σ : RS} {top best bestv : ℕ → ℕ}
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}

/-- The facts on the top pass the chord and region passes rely on. -/
theorem round_facts (h : Rooted R K up dn ord pos prg pch)
    (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch ztjk = e)
    (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem ztkfw ∧ AncX R prg pch σ.rem ztkfw u)
    (hB : ∀ t, t < R → IsTop pch σ.rem t →
      ztpm ∧
      (ztvl ∨
        (best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t ztmy)))
    (hI : RInv R K D prg pch isdn chOf j σ gc cr) :
    (∀ u, u < R → top ztkfw = top u) ∧
    (∀ x, x < R → top x = x → best x < R ∧ (best x ≠ x → pch ztvex < R)) ∧
    (∀ t, t < R → top t = t → σ.act t = 1 → σ.side t ≠ 2 → σ.cpar t < R) ∧
    (∀ e, e < K → σ.pend e = 1 → top ztjk = chOf e) ∧
    (∀ r, r < R → top r ≠ r → pch r < R) ∧ top 0 = 0 := by
  zqbjh
  have top0 := top_self h hch hT hB hI hR0 ztp
  refine ⟨fun u hu => top_self h hch hT hB hI by_simp_all by_simp_all, fun x hx htx => ?_,
    fun t ht htt ha hs => ?_, fun e he hp => ?_, fun r hr htr => ?_, top0⟩
  · have htop := (top_iff h hch hT hB hI hx).1 htx
    rcases (hB x hx htop).2 with ⟨b1, -⟩ | ⟨b1, b2, b3, -⟩
    · omega
    · refine ⟨b1, fun _ => ?_⟩
      have hnt : ¬ IsTop pch σ.rem _ := AncX.not_top b2 ztvak
      have hb0 : best x ≠ 0 := by_grind
      have := h.pch_lt _ b1 hb0
      omega
  · zuehe
    rcases hI.i4 t ht htop ha with ⟨h2, -⟩ | ⟨-, h2, -⟩
    · omega
    · omega
  · zuizd
    obtain ⟨c1, -, c3⟩ := hch e he
    exact top_self h hch hT hB hI c1 ztcgy
  · have hr0 : r ≠ 0 := by_grind
    have := h.pch_lt r hr hr0
    omega
end facts
section roundmem
variable {A R K : ℕ}

/-- The chord-pass and region-pass fields are disjoint. -/
theorem cpf_not_rpf {f : ℕ} (h : CPF f) : ¬ RPF f := by unfold CPF at h; unfold RPF; omega

/-- **The memory of a round.** -/
theorem round_mem {m0 m2 m3 m4 : ℕ → ℕ} {root fin root' fin' : ℕ} (hK : K < R)
    (h02 : ∀ f u, f < 19 → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R →
      fv m2 A R f u = fv m0 A R f u)
    (h23 : ∀ f u, f < 19 → u < R → fv m3 A R f u =
      if u < K ∧ CPF f then cpv m2 A R K f u else fv m2 A R f u)
    (h34 : ∀ f u, f < 19 → u < R → fv m4 A R f u =
      if RPF f then rpv m3 A R f u else fv m3 A R f u)
    (hb : ∀ r, r < R → fv m2 A R 8 r = r → fv m2 A R 13 r = 1 → fv m2 A R 9 r < R)
    (hp : ∀ r, r < R → fv m2 A R 8 r ≠ r → fv m2 A R 4 r < R)
    (hroot : root' = if fv m0 A R 13 0 = 1 then (if fv m0 A R 15 0 = 2 then
      code ztkge (tv m2 A R 4) 0 else root) else root)
    (hfin : fin' = fin + ((Finset.range R).filter (fun r => SingAt m3 A R r)).card) :
    rsOf m4 A R root' fin' = next R K ztqxn ztqxo ztqxp ztqxq
      ztqxr ztkge (rsOf m0 A R root fin) := by
  have t02 : ∀ f, f < 19 → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → tv m2 A R f = tv m0 A R f :=
    fun f hf h7 h8 h9 h10 => tv_congr by_grind
  have hnxt : nxt m2 A R K = next R K ztqxn ztqxo ztqxp ztqxq
      ztqxr ztkge (rsOf m0 A R 0 0) := by
    unfold nxt rsOf
    grind
  set N := next R K _ _ _ _
      _ _ _ with hN
  -- the chord fields
  have chord : ∀ f, CPF f → ∀ F : ℕ → ℕ, (∀ e, e < K → cpv m2 A R K f e = F e) →
      (∀ e, K ≤ e → F e = tv m0 A R f e) → tv m4 A R f = F := by
    intro f hc F hF1 hF2
    zufgp
    funext e
    unfold tv
    by_cases he : e < R
    · rw [ite_eq_left he, h34 f e hf he, ite_eq_right (cpf_not_rpf hc), h23 f e hf he]
      zujth
      · grind
      · rw [ite_eq_right by_omega, hF2 e by_omega, tv_lt he,
          h02 f e hf zteqh zteqh
            zteqh zteqh he]
    · rw [ite_eq_right he, hF2 e by_omega]
      unfold tv; grind
  -- the facts read by the region pass
  have r2 : ∀ f x, f < 19 → ¬ CPF f → x < R → fv m3 A R f x = fv m2 A R f x :=
    fun f x hf hc hx => by_grind
  have r0 : ∀ f x, f < 19 → ¬ CPF f → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → x < R →
      fv m3 A R f x = tv m0 A R f x :=
    fun f x hf hc h7 h8 h9 h10 hx => by rw [r2 f x hf hc hx, h02 f x hf h7 h8 h9 h10 hx, tv_lt hx]
  have a8 : ∀ x, x < R → fv m3 A R 8 x = tv m2 A R 8 x := fun x hx => by
    rw [r2 8 x by_norm_num by_decide hx, tv_lt hx]
  have a9 : ∀ x, x < R → fv m3 A R 9 x = tv m2 A R 9 x := fun x hx => by
    rw [r2 9 x by_norm_num by_decide hx, tv_lt hx]
  have a4 := fun x hx =>
    r0 4 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a5 := fun x hx =>
    r0 5 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a13 := fun x hx =>
    r0 13 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a14 := fun x hx =>
    r0 14 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a15 := fun x hx =>
    r0 15 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a0 := fun x hx =>
    r0 0 x by_norm_num by_decide by_norm_num by_norm_num by_norm_num
      by_norm_num hx
  have a12 : ∀ e, e < R → fv m3 A R 12 e = N.pend e := fun e he => by
    rw [h23 12 e by_norm_num he]
    zujth
    · rw [ite_eq_left ⟨heK, by_decide⟩]
      unfold cpv; rw [hnxt]; rfl
    · rw [ite_eq_right by_omega, h02 12 e by_norm_num by_norm_num by_norm_num
        by_norm_num by_norm_num he, hN]
      simp only [next, nPend, ite_eq_right heK, rsOf, tv_lt he]
  have hb' : ∀ r, r < R → tv m2 A R 8 r = r → tv m0 A R 13 r = 1 → tv m2 A R 9 r < R :=
    fun r hr h8 h13 => by
      zuimt
      rw [tv_lt hr, ← h02 13 r by_norm_num by_norm_num by_norm_num by_norm_num
        by_norm_num hr] at h13
      grind
  have hp' : ∀ r, r < R → tv m2 A R 8 r ≠ r → tv m0 A R 4 r < R := fun r hr h8 => by
    zuimt
    grind
  -- the region fields
  have region : ∀ f, RPF f → f ≠ 7 → ∀ F : ℕ → ℕ, (∀ r, r < R → rpv m3 A R f r = F r) →
      (∀ r, R ≤ r → F r = 0) → tv m4 A R f = F := by
    intro f hc hf7 F hF1 hF2
    zufgq
    funext r
    unfold tv
    zufrk
    · rw [ite_eq_left hr, h34 f r hf hr, ite_eq_left hc, hF1 r hr]
    · rw [ite_eq_right hr, hF2 r by_omega]
  have eta : N = ⟨N.rem, N.pend, N.act, N.cpar, N.side, N.dpar, N.dlo, N.dhi, N.lpar, N.root,
      N.fin⟩ := rfl
  rw [eta]
  unfold rsOf
  zucr
  · exact chord 11 by_decide _ ztbmt
      ztyj
  · exact chord 12 by_decide _ ztbmt
      (fun e he => by rw [hN]; simp only [next, nPend, ite_eq_right (show ¬ e < K by omega), rsOf])
  · refine region 13 by_decide by_norm_num _ ztez ztez
    · zqbjc
      · zqbjg
        · zqbjf
          zqbjb
          grind
        · zqbjb
          grind
      · zqbje
        zqbjb
        rfl
    · zqbjd
  · refine region 14 by_decide by_norm_num _ ztez ztez
    · zqbjc
      · zqbjg
        · zqbjf
          zqbjb
          grind
        · zqbjb
          grind
      · zqbje
        zqbjb
        clear * - ht
        grind
    · zqbjd
  · refine region 15 by_decide by_norm_num _ ztez ztez
    · zqbjc
      · zqbjg
        · zqbjf
          zqbjb
          grind
        · zqbjb
          grind
      · zqbje
        zqbjb
        clear * - ht
        grind
    · zqbjd
  · exact chord 16 by_decide _ ztbmt
      ztyj
  · exact chord 17 by_decide _ ztbmt
      ztyj
  · exact chord 18 by_decide _ ztbmt
      ztyj
  · refine region 0 by_decide by_norm_num _ ztez ztez
    · unfold rpv
      rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, a0 r hr, hN]
      by_cases ht : tv m2 A R 8 r = r
      · zqbjg
        · zqbjf
          zqbjb
          clear * - ht ha
          grind
        · zqbjb
          grind
      · zqbje
        zqbjb
        clear * - ht
        simp_all
    · zqbjd
  · rw [hroot, hN]
    zudny
    simp only [next, rsOf, tv_lt hR0]
    rw [t02 4 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num]
  · rw [hfin, hN]
    simp only [next, rsOf]
    zucr
    apply congrArg Finset.card
    apply Finset.filter_congr
    zuz
    zudtk
    unfold SingAt
    rw [a8 r hr, a13 r hr, a9 r hr]
end roundmem
section roundram
variable {P : Polygon} {W : ℕ} {A R K D CB RB LB : ℕ}

/-- `CPFacts` only reads fields outside the chord pass. -/
theorem CPFacts.congr {m m' : ℕ → ℕ} (hF : CPFacts m A R K)
    (hs : ∀ f u, f < 19 → ¬ CPF f → u < R → fv m' A R f u = fv m A R f u) : CPFacts m' A R K := by
  zumbw
  have h6 := fun u => hs 6 u by_norm_num by_decide
  have h3 := fun u => hs 3 u by_norm_num by_decide
  have h8 := fun u => hs 8 u by_norm_num by_decide
  have h9 := fun u => hs 9 u by_norm_num by_decide
  have h4 := fun u => hs 4 u by_norm_num by_decide
  have h13 := fun u => hs 13 u by_norm_num by_decide
  have h14 := fun u => hs 14 u by_norm_num by_decide
  have h15 := fun u => hs 15 u by_norm_num by_decide
  refine ⟨hKR, fun e' he' => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
    fun t ht htt ha hs2 => ?_⟩
  · zuetr

  · zugcy
  · zuecy
  · zuiil
    zucnp
    simp_all
  · zuww

/-- The static fields (order, parent, parent chord, low flag, child endpoint) are those of `mB`. -/
def Stat (mB m : ℕ → ℕ) (A R : ℕ) : Prop :=
  ∀ f u, ztcnc → u < R → fv m A R f u = fv mB A R f u

/-- **One round on the RAM** preserves the round invariant, one round further. -/
theorem roundBody_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn pos : ℕ → ℕ} {mB : ℕ → ℕ}
    (h : Rooted R K up dn ztqxs pos ztcbg ztbta)
    (hch : ∀ e, e < K → tv mB A R 6 e < R ∧ tv mB A R 6 e ≠ 0 ∧ tv mB A R 4 ztpem = e)
    (hdeg : ∀ v, v < R →
      (kids R ztcbg ztbta rem0 v).card + ztbst ≤ D)
    (hst : Stat mB c.nmem A R) (h7 : ∀ u, u < R → fv c.nmem A R 7 u = 1)
    {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
    (hI : RInv R K D ztcbg ztbta ztevz ztcws j
      (rsOf c.nmem A R (c.nreg 60024) (c.nreg 60023)) gc cr)
    (hj : c.nreg 60022 = j) (hjW : j + 1 ≤ W) (hfin : c.nreg 60023 < R) :
    ∃ c' k, Exec P W roundBody c c' k ∧ k ≤ 175 * R + 43 ∧ WordsBounded W c' ∧
      DFr ztiq zten c c' ∧ Stat mB c'.nmem A R ∧
      (∀ u, u < R → fv c'.nmem A R 7 u = 1) ∧ c'.nreg 60022 = j + 1 ∧
      ∃ gc' cr', RInv R K D ztcbg ztbta ztevz ztcws ztl
        ztitf gc' cr' := by
  zqbjh
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ := noWr_passes
  have sv : ∀ f u, ztcnc → u < R →
      fv c.nmem A R f u = tv mB A R f u := fun f u hf hu => by rw [hst f u hf hu, tv_lt hu]
  -- pass 1
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, hv1⟩ := p1S_exec (P := P) hw hR hAW h
    (rem := tv c.nmem A R 11) (fun u hu => sv 1 u by_simp hu) (fun u hu => sv 3 u by_simp hu)
    (fun u hu => sv 4 u by_simp hu) (fun u hu => (tv_lt hu).symm) h7
  have hR1 := hR.frame hf1
  have f01 : ∀ f u, f < 19 → f ≠ 7 → u < R → fv c1.nmem A R f u = fv c.nmem A R f u :=
    by simp_all
  -- pass 2
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hag, hv2⟩ := p2S_exec (P := P) hw1 hR1 hAW h
    (rem := tv c.nmem A R 11)
    ztcid
    ztcid
    ztcid
    (fun u hu => by rw [f01 11 u by_norm_num by_norm_num hu, tv_lt hu])
    ztcid
  have hR2 := hR1.frame hf2
  have f02 : ∀ f u, f < 19 → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R →
      fv c2.nmem A R f u = fv c.nmem A R f u :=
    by grind
  -- the top pass, characterised
  set σ := rsOf c.nmem A R _ _ with hσ
  set prg := tv mB A R 3 with hprg
  set pch := tv mB A R 4 with hpch
  set top := tv c2.nmem A R 8 with htop
  set best := tv c2.nmem A R 9 with hbest
  set bestv := tv c2.nmem A R 10 with hbestv
  obtain ⟨hT', hB'⟩ := p2_full h (S := sz R prg pch σ.rem) (fun u hu => rfl) (t3Of c1.nmem A R)
  have hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem ztkfw ∧ AncX R prg pch σ.rem ztkfw u :=
    fun u hu => by
      have := (hag u hu).1
      zujpa
      rw [htop, tv_lt hu, this]; exact hT' u hu
  have hB : ∀ t, t < R → IsTop pch σ.rem t →
      ztpm ∧
      (ztvl ∨
        (best t < R ∧ AncX R prg pch σ.rem t ztmy ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t ztmy)) := fun t ht htt => by
    have a2 := (hag t ht).2.1
    have a3 := (hag t ht).2.2
    simp only [t3Of] at a2 a3
    rw [hbest, hbestv, tv_lt ht, tv_lt ht, a2, a3]; exact hB' t ht htt
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := round_facts h hch hT hB hI
  -- conversions at `c2`
  have T8 : ∀ u, u < R → fv c2.nmem A R 8 u = top u := fun u hu => by rw [htop, tv_lt hu]
  have T9 : ∀ u, u < R → fv c2.nmem A R 9 u = best u := fun u hu => by rw [hbest, tv_lt hu]
  have S2 : ∀ f u, ztcnc → u < R →
      fv c2.nmem A R f u = tv mB A R f u := fun f u hf hu => by
    rw [f02 f u by_omega by_omega by_omega by_omega by_omega hu]; exact sv f u hf hu
  have Q2 : ∀ f u, f < 19 → 11 ≤ f ∨ f = 0 → u < R → fv c2.nmem A R f u = tv c.nmem A R f u :=
    fun f u hf hf' hu => by
      rw [f02 f u hf by_omega by_omega by_omega by_omega hu, tv_lt hu]
  have hF2 : ztsbb := by
    refine ⟨hKR, fun e he => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
      fun t ht htt ha hs => ?_⟩
    · obtain ⟨a1, a2, -⟩ := hch e he
      rw [S2 6 e by_simp by_omega, S2 3 _ by_simp a1]
      exact ⟨a1, a2, h.prg_lt _ a1 a2⟩
    · rw [T8 u hu]; exact (hT u hu).1
    · rw [T8 u hu, T8 _ (hT u hu).1]; exact F1 u hu
    · rw [T8 x hx] at htx
      obtain ⟨b1, b2⟩ := F2 x hx htx
      rw [T9 x hx]; refine ⟨b1, fun hb => ?_⟩; rw [S2 4 _ by_simp b1]; exact b2 hb
    · rw [T8 t ht] at htt; rw [Q2 13 t by_norm_num by_omega ht] at ha
      rw [Q2 15 t by_norm_num by_omega ht] at hs
      rw [Q2 14 t by_norm_num by_omega ht]; exact F3 t ht htt ha hs
  -- the chord pass
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hv3⟩ := cpS_exec (P := P) hw2 hR2 hAW hF2
    (fun e he hp => by
      have he' : ztsid := by_omega
      rw [Q2 12 e by_norm_num by_omega he'] at hp
      obtain ⟨a1, -, -⟩ := hch e he
      rw [S2 6 e by_simp he', T8 _ a1]; exact F4 e he hp)
  zulja
  have f23 : ∀ f u, f < 19 → ¬ CPF f → u < R → fv c3.nmem A R f u = fv c2.nmem A R f u :=
    fun f u hf hc hu => by rw [hv3 f u hf hu, ite_eq_right (fun hh => hc hh.2)]
  have hF3 := hF2.congr f23
  -- the root step
  obtain ⟨c4, k4, e4, hk4, m4, s4, r24⟩ := rootS_exec (P := P) hw3 hR3 hAW hF3
    (by rw [f23 8 0 by_norm_num by_decide hR0, T8 0 hR0]; exact F6)
  zujzz
  -- the region pass
  have n23 : c3.nreg 60023 = c.nreg 60023 := by
    rw [nreg_of_noWr e3 w8, nreg_of_noWr e2 w5, nreg_of_noWr e1 w2]
  have n24 : c3.nreg 60024 = c.nreg 60024 := by
    rw [nreg_of_noWr e3 w9, nreg_of_noWr e2 w6, nreg_of_noWr e1 w3]
  have n22 : c4.nreg 60022 = c.nreg 60022 := by
    rw [nreg_of_noWr e4 w10, nreg_of_noWr e3 w7, nreg_of_noWr e2 w4, nreg_of_noWr e1 w1]
  have n23' : ztsfh := by rw [nreg_of_noWr e4 w11, n23]
  have g8 : ∀ u, u < R → fv c4.nmem A R 8 u = top u := fun u hu => by
    rw [m4, f23 8 u by_norm_num by_decide hu, T8 u hu]
  have g9 : ∀ u, u < R → fv c4.nmem A R 9 u = best u := fun u hu => by
    rw [m4, f23 9 u by_norm_num by_decide hu, T9 u hu]
  have gQ : ∀ f u, f < 19 → ¬ CPF f → 11 ≤ f → u < R → fv c4.nmem A R f u = tv c.nmem A R f u :=
    fun f u hf hc hf' hu => by rw [m4, f23 f u hf hc hu, Q2 f u hf by_omega hu]
  have g4 : ∀ u, u < R → fv c4.nmem A R 4 u = pch u := fun u hu => by
    rw [m4, f23 4 u by_norm_num by_decide hu, S2 4 u by_simp hu]
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, r23, hv5⟩ := rpS_exec (P := P) e4.wb_right hR4 hAW
    (fun r hr htr ha => by
      rw [g8 r hr] at htr; rw [g9 r hr]; exact (F2 r hr htr).1)
    (fun r hr htr ha hbr hs => by
      rw [g8 r hr] at htr
      rw [gQ 13 r by_norm_num by_decide by_norm_num hr] at ha
      rw [gQ 15 r by_norm_num by_decide by_norm_num hr] at hs
      rw [gQ 14 r by_norm_num by_decide by_norm_num hr]
      exact F3 r hr htr ha hs)
    (fun r hr htr => by rw [g8 r hr] at htr; rw [g4 r hr]; exact F5 r hr htr)
    by_omega
  zuljc
  -- the round counter
  have n22' : c5.nreg 60022 = j := by rw [nreg_of_noWr e5 w12, n22, hj]
  have e6 := Exec.addN (P := P) e5.wb_right 60022 60022 60011 (by zuolx; omega)
  set c6 := { c5 with nreg := upd c5.nreg 60022 _ } with hc6
  have hf6 : DFr ztiq zten c5 c6 :=
    DFr.nreg _ fun r hr _ => by unfold Prot at hr; zumyl
  -- memory relations
  have m56 : c6.nmem = c5.nmem := rfl
  have h45 : ∀ f u, f < 19 → u < R → fv c6.nmem A R f u =
      if RPF f then rpv c3.nmem A R f u else fv c3.nmem A R f u := fun f u hf hu => by
    rw [m56, hv5 f u hf hu, m4]
  have hmem := round_mem (root' := c6.nreg 60024)
    (fin' := c6.nreg 60023) hKR f02 hv3 h45
    (fun r hr htr ha => by
      rw [T8 r hr] at htr; rw [T9 r hr]; exact (F2 r hr htr).1)
    (fun r hr htr => by rw [T8 r hr] at htr; rw [S2 4 r by_simp hr]; exact F5 r hr htr)
    (by
      have e24 : c6.nreg 60024 = c4.nreg 60024 := by
        zunsx; config_simp; rw [nreg_of_noWr e5 w13]
      rw [e24, r24, n24, f23 13 0 by_norm_num by_decide hR0,
        f23 15 0 by_norm_num by_decide hR0,
        f02 13 0 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hR0,
        f02 15 0 by_norm_num by_norm_num by_norm_num by_norm_num by_norm_num hR0,
        tv_congr (fun u hu => f23 9 u by_norm_num by_decide hu),
        tv_congr (fun u hu => f23 4 u by_norm_num by_decide hu)])
    (by
      have e23 : c6.nreg 60023 = c5.nreg 60023 := by_rfl
      rw [e23, r23, n23', m4])
  have tS :=
    fun f hf => tv_congr (fun u hu => hst f u hf hu)
  rw [tS 3 by_simp, tS 4 by_simp, tS 5 by_simp, tS 6 by_simp] at hmem
  -- conclusion
  have hS6 : ∀ f u, f < 19 → ¬ RPF f → ¬ CPF f → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R →
      fv c6.nmem A R f u = fv c.nmem A R f u := fun f u hf hr hc h7 h8 h9 h10 hu => by
    rw [h45 f u hf hu, ite_eq_right hr, f23 f u hf hc hu, f02 f u hf h7 h8 h9 h10 hu]
  refine ⟨c6, k1 + zthii, .seq e1 ztvb,
    by omega, e6.wb_right, ?_, fun f u hf hu => ?_, fun u hu => ?_, ?_,
    gcNext R K prg pch ztcws top best σ gc,
    crNext K ztcws top best σ j cr, ?_⟩
  · refine ((((hf1.trans hf2).trans hf3).trans ?_).trans hf5).trans hf6
    exact DFr.of_same s4 ztfl (fun a _ => by rw [m4])
  · have hf' : ztmvq := by_omega
    rw [hS6 f u hf' (by unfold RPF; omega) ztqft by_omega by_omega by_omega
      by_omega hu]
    exact hst f u hf hu
  · rw [h45 7 u by_norm_num hu, ite_eq_left by_decide]; rfl
  · zunsx; config_simp; zuolx
  · zujjj
    exact rinv_next h hch hT hB hI hdeg
end roundram
end
end Chazelle.Core.DecR
end
namespace Chazelle.Core.DecR
open Machine Machine.Stmt Programs Chazelle.Core.Dec
@[expose] public section
section start
variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ}

/-- With nothing removed, the root is the only top. -/
theorem istop_start (h : Rooted R K up dn ord pos prg pch) {rem : ℕ → ℕ}
    (hrem : ∀ e, e < K → rem e = 0) {t : ℕ} (ht : t < R) : IsTop pch rem t ↔ t = 0 := by
  constructor
  · zugax
    · zulyi
    · zuccr
      have := hrem _ (h.pch_lt t ht h0)
      omega
  tauto

/-- **The invariant at the start**, for any state agreeing with `rs0` where it matters. -/
theorem rinv_start (h : Rooted R K up dn ord pos prg pch) {σ : RS}
    (hrem : ∀ e, e < K → σ.rem e = 0) (hpend : ∀ e, e < K → σ.pend e = 0)
    (hact : σ.act 0 = 1) (hside : σ.side 0 = 2) (hfin : σ.fin = 0)
    (gc : ℕ → Finset ℕ) (cr : ℕ → ℕ) :
    RInv R K D prg pch isdn chOf 0 σ gc cr where
  i0 e he hp := by simp_all
  i1 e he hr := by simp_all
  i2 e he hr := by simp_all
  i3 e he hp := by simp_all
  i4 t ht htop _ := by
    rw [istop_start h hrem ht] at htop
    simp_all
  i5 t ht htop hact' := by
    rw [istop_start h hrem ht] at htop
    simp_all
  i6 t _ _ _ := by
    refine ⟨?_, Or.inl rfl⟩
    have : sz R prg pch σ.rem t ≤ R := by
      classical
      unfold sz sub
      exact (Finset.card_filter_le _ _).trans (by simp)
    have := h.hR
    simp_all
  i7 _ := ⟨fun e he => by simp_all, hact, hside⟩
  i8 hj := absurd hj (by norm_num)
  i9 := by
    rw [hfin]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro t ht ⟨htop, hact'⟩
    rw [Finset.mem_range] at ht
    rw [istop_start h hrem ht] at htop
    simp_all

/-- At most `K` rounds. -/
theorem rounds_le_self (D K : ℕ) : rounds D K ≤ K := by
  have key : ztxbz := by
    zuibw
    induction i with
    | zero => left; simp
    | succ i ih =>
      zudtl
      rcases Nat.eq_zero_or_pos ztyxq with h0 | hpos
      · right; zvmzn; have := hstep_le D 0; omega
      · rcases ih with ih | ih
        · left; have := hstep_lt D _ hpos; omega
        · omega
  have hK : ztyk^[K] K = 0 := by
    grind
  exact Nat.find_min' _ hK
end start
section loopram
variable {P : Polygon} {W : ℕ} {A R K D CB RB LB : ℕ}

/-- **The loop of rounds.** -/
theorem roundsS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn pos : ℕ → ℕ} {mB : ℕ → ℕ}
    (h : Rooted R K up dn ztqxs pos ztcbg ztbta)
    (hch : ∀ e, e < K → tv mB A R 6 e < R ∧ tv mB A R 6 e ≠ 0 ∧ tv mB A R 4 ztpem = e)
    (hdeg : ∀ v, v < R →
      (kids R ztcbg ztbta rem0 v).card + ztbst ≤ D)
    (hst : Stat mB c.nmem A R) (h7 : ∀ u, u < R → fv c.nmem A R 7 u = 1)
    (h11 : ∀ u, u < R → fv c.nmem A R 11 u = 0) (h12 : ∀ u, u < R → fv c.nmem A R 12 u = 0)
    (h13 : fv c.nmem A R 13 0 = 1) (h15 : fv c.nmem A R 15 0 = 2) :
    ∃ c' k, Exec P W roundsS c c' k ∧ k ≤ ztptk * ztglt + 5 ∧
      WordsBounded W c' ∧ DFr ztiq zten c c' ∧ Stat mB c'.nmem A R ∧
      ∃ j gc cr, RInv R K D ztcbg ztbta ztevz ztcws j
        ztitf gc cr ∧
      ∀ t, t < R → IsTop ztbta (rsOf c'.nmem A R ztvgn ztvgm).rem t →
        (rsOf c'.nmem A R ztvgn ztvgm).act t ≠ 1 := by
  zuclt
  zudny
  have hrK := rounds_le_self D K
  unfold roundsS
  -- the three counters
  have e1 := Exec.constN (P := P) hw 60022 0 ztbg
  set c1 := { c with nreg := upd c.nreg 60022 0 } with hc1
  have e2 := Exec.constN (P := P) e1.wb_right 60023 0 ztbg
  set c2 := { c1 with nreg := upd c1.nreg 60023 0 } with hc2
  have e3 := Exec.constN (P := P) e2.wb_right 60024 0 ztbg
  set c3 := { c2 with nreg := upd c2.nreg 60024 0 } with hc3
  have eB : Exec P W zthsm c c3 3 :=
    .seq e1 (.seq e2 (.seq e3 (.skip e3.wb_right)))
  have hf3 : DFr ztiq zten c c3 :=
    DFr.nreg _ fun r hr _ => by
      zuhae
      simp only [hc2, hc1]
      rw [Machine.upd_other _ _ _ by_omega, Machine.upd_other _ _ _ by_omega,
        Machine.upd_other _ _ _ by_omega]
  have m3 : ztmut := rfl
  have r22 : c3.nreg 60022 = 0 := by_rfl
  have r23 : c3.nreg 60023 = 0 := by_rfl
  have r24 : c3.nreg 60024 = 0 := by_rfl
  have hI0 : RInv R K D ztcbg ztbta ztevz ztcws 0
      (rsOf c3.nmem A R (c3.nreg 60024) (c3.nreg 60023)) (fun _ => ∅) ztczh :=
    rinv_start h (fun e he => by
        show tv c3.nmem A R 11 e = 0
        zuofn; grind)
      (fun e he => by
        show tv c3.nmem A R 12 e = 0
        zuofn; grind)
      (by show tv c3.nmem A R 13 0 = 1; zuofo; omega)
      (by show tv c3.nmem A R 15 0 = 2; zuofo; omega)
      by_rfl _ _
  -- the loop
  obtain ⟨c', k, e, ⟨hw', hf', hst', h7', hjr, j, hjd, gc, cr, hI'⟩, htest, hk⟩ :=
    Exec.whileLtN_potential (P := P) (W := W) (a := 60023) (b := 60013) (body := roundBody)
    (fun d => WordsBounded W d ∧ DFr ztiq zten c d ∧ Stat mB d.nmem A R ∧
      (∀ u, u < R → fv d.nmem A R 7 u = 1) ∧ d.nreg 60022 ≤ rounds D K + 1 ∧
      ∃ j, d.nreg 60022 = j ∧ ∃ gc cr, RInv R K D ztcbg ztbta ztevz
        ztcws j (rsOf d.nmem A R (d.nreg 60024) (d.nreg 60023)) gc cr)
    (fun d => ztptk * (rounds D K + 1 - d.nreg 60022)) ztoe
    (fun d ⟨hwd, hfd, hstd, h7d, hjd, j, hjdef, gc, cr, hId⟩ ht => by
      zubdq
      zuktd
      obtain ⟨t, ht1, ht2, ht3⟩ := (fin_lt_iff h hId).1 ht
      have hjr := le_rounds_of_active h hId ht1 ht2 ht3
      obtain ⟨d', k', e', hk', hw'', hf'', hst'', h7'', hj'', gc', cr', hI''⟩ :=
        roundBody_exec (P := P) hwd hRd hAW h hch hdeg hstd h7d hId hjdef by_omega ht
      refine ⟨d', k', e', ⟨hw'', hfd.trans hf'', hst'', h7'', by_omega, j + 1, hj'', gc', cr',
        hI''⟩, ?_⟩
      rw [hj'', hjdef]
      have : rounds D K + 1 - j = (rounds D K + 1 - ztl) + 1 := by_omega
      rw [this, Nat.mul_add]
      omega)
    ⟨e3.wb_right, hf3, by_omega, by_omega, by_omega, 0, r22, _, _, hI0⟩
  zuut

  subst hjd
  refine ⟨c', 3 + k, .seq eB e, ?_, hw', hf', hst', _, gc, cr, hI', fun t ht htop hact => ?_⟩
  · grind
  · exact htest ((fin_lt_iff h hI').2 ⟨t, ht, htop, hact⟩)
end loopram
open Relation
section kids
variable {R K : ℕ} {up dn ord pos prg pch : ℕ → ℕ}

/-- **Degrees**: the children of `v` and its parent chord are distinct chords of `v`. -/
theorem kids_deg (h : Rooted R K up dn ord pos prg pch) {lst : ℕ → List ℕ}
    (hlists : ∀ r, r < R → ∀ i, i ∈ lst r ↔ i < K ∧ ztfvb)
    (hnd : ∀ r, r < R → (lst r).Nodup) {v : ℕ} (hv : v < R) :
    (kids R prg pch rem0 v).card + ztbst ≤ (lst v).length := by
  classical
  have hinj : Set.InjOn pch (kids R prg pch rem0 v : Set ℕ) := by
    intro a ha b hb he
    rw [Finset.mem_coe, mem_kids] at ha hb
    exact h.pch_inj ha.1 hb.1 ha.2.1 hb.2.1 he
  have himg : (kids R prg pch rem0 v).image pch ⊆ (lst v).toFinset := by
    zug
    zugby
    obtain ⟨c, hc, rfl⟩ := hi
    zubbi
    zufiv
    zuign
    refine ⟨h.pch_lt c c1 c2, ?_⟩
    rcases h.ends c c1 c2 with ⟨a1, -⟩ | ⟨-, a2⟩
    · omega
    omega
  have hcard1 : ((kids R prg pch rem0 v).image pch).card = (kids R prg pch rem0 v).card :=
    Finset.card_image_of_injOn hinj
  have hlen : (lst v).toFinset.card = (lst v).length := List.toFinset_card_of_nodup (hnd v hv)
  by_cases hv0 : v = 0
  · rw [ite_eq_left hv0, Nat.add_zero, ← hcard1, ← hlen]
    exact Finset.card_le_card himg
  · rw [ite_eq_right hv0]
    have hpv : pch v ∈ (lst v).toFinset := by
      zuign
      refine ⟨h.pch_lt v hv hv0, ?_⟩
      rcases h.ends v hv hv0 with ⟨-, a2⟩ | ⟨a1, -⟩
      · omega
      omega
    have hnot : pch v ∉ (kids R prg pch rem0 v).image pch := by
      zulmu
      zugby
      obtain ⟨c, hc, he⟩ := hi
      zubbi
      zufiv
      have := h.pch_inj c1 hv c2 hv0 he
      zumo
      have := h.pos_prg c c1 c2
      simp_all
    have hsub : insert (pch v) ((kids R prg pch rem0 v).image pch) ⊆ (lst v).toFinset :=
      Finset.insert_subset hpv himg
    have := Finset.card_le_card hsub
    simp_all

/-- `Rooted` only reads its functions below `R`. -/
theorem Rooted.congr (h : Rooted R K up dn ord pos prg pch) {ord' prg' pch' : ℕ → ℕ}
    (ho : ∀ j, j < R → ord' j = ord j) (hp : ∀ j, j < R → prg' j = prg j)
    (hc : ∀ j, j < R → pch' j = pch j) : Rooted R K up dn ord' pos prg' pch' where
  hR := h.hR
  ord_lt i hi := by zuols; exact h.ord_lt i hi
  pos_lt := h.pos_lt
  ord_pos r hr := by rw [ho _ (h.pos_lt r hr)]; exact h.ord_pos r hr
  pos_ord i hi := by zuols; exact h.pos_ord i hi
  root := by rw [ho 0 (by have := h.hR; omega)]; exact h.root
  prg_lt s hs hs0 := by zuolt; exact h.prg_lt s hs hs0
  pos_prg s hs hs0 := by zuolt; exact h.pos_prg s hs hs0
  pch_lt s hs hs0 := by rw [hc s hs]; exact h.pch_lt s hs hs0
  ends s hs hs0 := by rw [hc s hs, hp s hs]; exact h.ends s hs hs0
  pch_surj i hi := by
    obtain ⟨s, s1, s2, s3⟩ := h.pch_surj i hi
    grind
  ends_lt := h.ends_lt
end kids
section robust
variable {E : ℕ} {m : ℕ → ℕ}
/-- A robust fact at a fixed address reads below the bound. -/
theorem rb_addr {a v : ℕ} (h : Robust E m fun m' => m' a = v) : a < E := by
  zucux
  have := h ztzjx (fun b hb => by
    grind)
  simp_all

/-- A word reached through a pointer: the pointer and the word lie below the bound. -/
theorem rb_addr2 {b o v : ℕ}
    (h : Robust E m fun m' => m' ztrtu = v) : b < E ∧ m b + o < E := by
  have hb : ztsdn := by
    zucux
    zukat
    have := h ztzka
      (fun a ha => by
        grind)
    simp_all
  refine ztonz
  zucux
  have := h ztzjz (fun a ha => by
    grind)
  grind

/-- A robust fact with an inner offset read at a fixed address below the bound. -/
theorem rb_fix {c : ℕ} (hc : c < E) {Φ : ℕ → ztjx → Prop}
    (h : Robust E m fun m' => Φ (m' c) m') : Robust E m fun m' => Φ (m c) m' :=
  fun m' hm' => by
    have := h m' hm'
    simp_all
end robust
section env
variable {m : ℕ → ℕ} {B : ℕ} {N N' : NF}
/-- **The search environment** from a normal form readable below `A`. -/
theorem inEnv_of {B A : ℕ} {N : NF} (h : NFWithin m B A N) :
    InEnv m A N.nRegions N.nChords ztbaid (m zter) (m ztlw)
      ztmjq ztmjp (fun r => (N.region r).chords) := by
  have hN := h.nfAt
  refine ztfwh
  · obtain ⟨-, -, -, a1, a2⟩ := hN.2.2.2.2.2.1 i hi
    have r4 : Robust A m fun m' => m' (m' ztkh + ztjfv) = (N.chord i).dn :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.1 i hi).2.2.2.2
        omega
    have := (rb_addr2 r4).2
    omega
  · obtain ⟨-, a2, -, -, -⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have r4 : Robust A m fun m' => m' ztzmx = (N.region r).wt :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        omega
    have := (rb_addr2 r4).2
    omega
  · obtain ⟨-, -, -, -, a5⟩ := hN.2.2.2.2.2.2.2.1 r hr
    have r4 : Robust A m fun m' => m' ztzmx = (N.region r).wt :=
      fun m' hm' => by
        have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.1
        omega
    obtain ⟨hB5, hw⟩ := rb_addr2 r4
    have hc : m zter + 5 * r + 3 < A := by_omega
    have r5 : Robust A m fun m' => m' (m' ztlw + m' ztwnp + t) =
        (N.region r).chords.getD t 0 := fun m' hm' => by
      have := ((h m' hm').2.2.2.2.2.2.2.1 r hr).2.2.2.2 t ht
      simp_all
    have r6 := rb_fix (Φ := fun x m' => m' (m' ztlw + x + t) = (N.region r).chords.getD t 0)
      hc r5
    have r7 : Robust A m fun m' => m' (m' ztlw + (m ztwnp + t)) =
        (N.region r).chords.getD t 0 := fun m' hm' => by
      have := r6 m' hm'
      grind
    have := (rb_addr2 r7).2
    grind

/-- Region records are determined by their fields. -/
theorem rRec_ext' {a b : RRec} (h1 : a.arcs = b.arcs) (h2 : a.chords = b.chords)
    (h3 : a.wt = b.wt) : a = b := by
  obtain ⟨_, _, _⟩ := a
  simp_all

/-- Chord records are determined by their fields. -/
theorem cRec_ext' {a b : CRec} (h1 : a.h = b.h) (h2 : a.lp = b.lp) (h3 : a.rp = b.rp)
    (h4 : a.up = b.up) (h5 : a.dn = b.dn) : a = b := by
  zueak

/-- Arc records are determined by their fields. -/
theorem aRec_ext' {a b : ARec} (h1 : a.reg = b.reg) (h2 : a.s.edge = b.s.edge)
    (h3 : a.s.hgt = b.s.hgt) (h4 : a.e.edge = b.e.edge) (h5 : a.e.hgt = b.e.hgt) : a = b := by
  zucxj

/-- Lists of naturals with equal lengths and entries are equal. -/
theorem list_ext_getD {l l' : List ℕ} (hl : l'.length = l.length)
    (h : ∀ t, t < l.length → l'.getD t 0 = l.getD t 0) : l' = l := by
  zuiqu
  simp_all

/-- The layout determines the chord records. -/
theorem nfAt_chords_eq' (h : NFAt m B N) (h' : NFAt m B N') :
    N'.chords = N.chords := by
  zubnv

  have a1 : ztpkt := getD_of_lt hj' _
  have a2 : ztpkq := getD_of_lt hj _
  zubmi
  exact cRec_ext' ztjui ztjuj ztjuk
    ztmiw ztmix

/-- The layout determines the arc records. -/
theorem nfAt_arcs_eq' (h : NFAt m B N) (h' : NFAt m B N') :
    N'.arcs = N.arcs := by
  zubnu

  have a1 : ztpkr := getD_of_lt hj' _
  have a2 : ztpkp := getD_of_lt hj _
  zubmi
  exact aRec_ext' ztjui ztjuj ztjuk
    ztmiw ztmix

/-- The layout determines the region records. -/
theorem nfAt_regions_eq' (h : NFAt m B N) (h' : NFAt m B N') :
    N'.regions = N.regions := by
  have hl : N'.regions.length = N.regions.length := h'.2.2.1.symm.trans h.2.2.1
  zuiqu
  zumgz
  have e := h.2.2.2.2.2.2.2.1 j hj'
  have e' := h'.2.2.2.2.2.2.2.1 j hj
  have a1 : N.region j = N.regions[j] := getD_of_lt hj' _
  have a2 : N'.region j = N'.regions[j] := getD_of_lt hj _
  zubmi
  refine rRec_ext' ?_ ?_ ztjuk
  · exact list_ext_getD ztjui fun t ht => by
      simp_all
  · exact list_ext_getD ztjuj fun t ht => by
      simp_all
end env
macro "seq_store" : tactic =>
  `(tactic| (refine spec_seq (spec_instr (Machine.Exec.storeN ‹WordsBounded _ _› _ _)
    fun _hw => ?_); config_flatten_at _hw; spec_flatten))

/-- An addition followed by more code (side condition moved last). -/
macro "seq_addN" : tactic =>
  `(tactic| (refine spec_seq (spec_instr ztkqd
    fun _hw => ?_); rotate_left; config_flatten_at _hw; spec_flatten))

/-- Discharge the arithmetic side conditions left by the block steps. -/
macro "side_tac" : tactic =>
  `(tactic| all_goals first
    | (config_simp; simp (config := { failIfUnchanged := false }) only [*]; omega)
    | skip)
section fc
variable {P : Polygon} {W : ℕ} {A R K CB RB LB : ℕ}
variable {c : Config}
/-- One step of the node-table copy. -/
theorem fcBody_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R + 3 * K ≤ W) {j : ℕ} (h20 : c.nreg 60020 = j) (hj : j < K)
    (hKR : K < R) :
    ∃ c' k, Exec P W fcBody c c' k ∧ k = 15 ∧ DFr ztiq ztcsq c c' ∧
      c'.nreg 60020 = j + 1 ∧
      c'.nmem = upd (upd (upd c.nmem (A + 12 + 19 * R + 3 * j) (fv c.nmem A R 16 j))
        (A + 12 + 19 * R + 3 * j + 1) (fv c.nmem A R 17 j))
        (A + 12 + 19 * R + 3 * j + 2) (fv c.nmem A R 18 j) := by
  have b16 := hR.b 16 by_norm_num; have b17 := hR.b 17 by_norm_num
  have b18 := hR.b 18 by_norm_num; have b19 := hR.b 19 by_norm_num
  zvmxv at b16 b17 b18 b19
  zujaf
  have h16 : 16 * R + j < 19 * R := by_omega
  have hjR : 3 * j + 3 ≤ 3 * K := by_omega
  unfold fcBody ldF fb
  zulrv
  refine spec_seq ?_
  exec_block
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  seq_addN
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  seq_addN
  side_tac
  refine spec_seq ?_
  exec_block
  side_tac
  seq_store
  refine spec_instr ztkqd fun _hw => ?_
  rotate_left
  side_tac
  refine ⟨by_norm_num, ztcqy, ?_, ?_⟩
  · zuhae
    config_simp
    zup
  · config_simp
    simp only [b16, b17, b18, b19, h20, o]
    zup
  · config_simp; omega
  · config_simp
    simp only [b16, b17, b18, b19, h20, o]
    zup
    zumsr
    grind

/-- The node table value at address `a` (relative to `DB = A + 12 + 19 R`). -/
def ntv (m : ℕ → ℕ) (A R a : ℕ) : ℕ :=
  fv m A R (16 + ztzvb % 3) (ztzvb / 3)

/-- **The node-table copy.** -/
theorem fcS_exec (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R + 3 * K ≤ W) (hKR : K < R) :
    ∃ c' k, Exec P W fcS c c' k ∧ k ≤ 17 * K + 3 ∧ WordsBounded W c' ∧
      DFr ztiq ztcsq c c' ∧
      ∀ a, c'.nmem a = if A + 12 + 19 * R ≤ a ∧ a < A + 12 + 19 * R + 3 * K then
        ntv c.nmem A R a else c.nmem a := by
  unfold fcS
  zugx

  have hf1 : DFr ztiq ztcsq c c1 :=
    DFr.nreg _ fun r hr _ => by
      zupj
  obtain ⟨c', k, e, ⟨hw', hf', hj', hv'⟩, htest, hk⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 60020) (b := 60014) (body := fcBody)
    (fun d => WordsBounded W d ∧ DFr ztiq ztcsq c d ∧ d.nreg 60020 ≤ K ∧
      ∀ a, d.nmem a = if A + 12 + 19 * R ≤ a ∧ a < A + 12 + 19 * R + 3 * d.nreg 60020 then
        ntv c.nmem A R a else c.nmem a)
    (fun d => 17 * ztrjt) ztoe
    (fun d ⟨hwd, hfd, hjd, hvd⟩ htest => by
      zubdq
      zuktc
      obtain ⟨j, hjdef⟩ : ztjbr := zths
      rw [hjdef] at htest hjd hvd
      obtain ⟨d', k', e', rfl, hf'', h20', hm'⟩ := fcBody_exec (P := P) hwd hRd hAW hjdef htest hKR
      have hfv : ∀ f, f < 19 → fv d.nmem A R f j = fv c.nmem A R f j := fun f hf => by
        have : ztizt := Nat.mul_le_mul_right _ by_omega
        unfold fv; grind
      refine ⟨d', 15, e', ⟨e'.wb_right, hfd.trans hf'', by_omega, fun a => ?_⟩, by_omega⟩
      rw [hm', h20', hfv 16 by_norm_num, hfv 17 by_norm_num, hfv 18 by_norm_num]
      zudi
      rw [hvd a]
      unfold ntv
      split_ifs <;> first
        | rfl
        | omega
        | (· grind)
        | (· grind)
        | (· grind))
    ⟨hw1, hf1, by_simp_all, fun a => by
      simp_all⟩
  zuftv

  grind
end fc
section hdr
variable {P : Polygon} {W : ℕ} {A R K CB RB LB : ℕ}

/-- **The header** of the output at `A`. -/
theorem hdrS_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c) {B : ℕ}
    (hB : c.nreg 60001 = B) (hBA : B + 9 < A) (hAW : A + 12 + 20 * R ≤ W) :
    ∃ c' k, Exec P W hdrS c c' k ∧ k ≤ 40 ∧ c'.nreg 60003 = A ∧
      (∀ r, r ≠ 60030 → r ≠ 60031 → r ≠ 60085 → r ≠ 60003 → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nmem A = K ∧ c'.nmem ztbo = c.nmem ztvf ∧ c'.nmem ztbcl = R ∧
      c'.nmem zttf = c.nmem ztkh ∧ c'.nmem ztckz = c.nmem ztow ∧
      c'.nmem ztgzp = c.nmem zter ∧ c'.nmem ztjgk = c.nmem ztcsw ∧
      c'.nmem ztgzq = c.nmem ztlw ∧ c'.nmem ztcla = A + 12 + 19 * R ∧
      c'.nmem ztnir = c.nreg 60024 ∧ c'.nmem ztjgi = A + 12 ∧ c'.nmem ztnic = K ∧
      ∀ a, (a < A ∨ A + 12 ≤ a) → c'.nmem a = c.nmem a := by
  have b0 := hR.b 0 by_norm_num; have b19 := hR.b 19 by_norm_num
  simp only [Nat.reduceAdd, Nat.zero_mul, Nat.add_zero] at b0 b19
  have o := hR.one; have t := hR.two; have rA := hR.rA; have rK := hR.rK; have rR := hR.rR
  unfold hdrS
  exec_block
  side_tac
  refine ⟨by_omega, ?_, fun r h1 h2 h3 h4 => ?_, rfl, rfl, rfl, ?_⟩
  · tauto
  · config_simp; simp (disch := omega) only [Machine.upd_other]
  · config_simp
    simp only [b0, b19, o, t, rA, rK, rR, hB]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩ <;>
      simp (disch := omega) only [Machine.upd_other, Machine.upd_same]
end hdr
section helpers
variable {P : Polygon} {W : ℕ}

/-- **The allocation loop**, with the growth of the allocator bounded by the cost. -/
theorem allocS_exec' {c : Config} (hw : WordsBounded W c) (h1 : c.nreg 60011 = 1)
    (hle : c.nreg ALLOC ≤ c.nreg 60086) :
    ∃ c' k, Exec P W allocS c c' k ∧ k ≤ 3 * (c.nreg 60086 - c.nreg ALLOC) + 2 ∧
      c'.nreg ALLOC = c.nreg 60086 ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k ∧
      ztjn ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  have hT := WordsBounded.nreg hw 60086
  obtain ⟨c', k, e, ⟨hw', hle', hr, hm, hrr, hrm, ho⟩, htest, hk, hlb⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 9999) (b := 60086)
    (body := .instr ztrht)
    (fun d => WordsBounded W d ∧ d.nreg 9999 ≤ c.nreg 60086 ∧
      (∀ r, r ≠ 9999 → d.nreg r = c.nreg r) ∧ d.nmem = c.nmem ∧ d.rreg = c.rreg ∧
      d.rmem = c.rmem ∧ d.output = c.output)
    (fun d => 3 * (c.nreg 60086 - d.nreg 9999)) ztqno ztesk
    (fun d ⟨hwd, hled, hrd, hmd, hrrd, hrmd, hod⟩ ht => by
      have h1d : d.nreg 60011 = 1 := by_simp_all
      have h86 : d.nreg 60086 = c.nreg 60086 := by_simp_all
      rw [h86] at ht
      zujfj
      refine ⟨⟨hw2, by_simp_all, fun r hr => ?_, hmd, hrrd, hrmd, hod⟩, ?_, ?_⟩
      · simp_all
      · config_simp; omega
      simp_all)
    ⟨hw, hle, fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have h86 : c'.nreg 60086 = c.nreg 60086 := by_simp_all
  rw [h86] at htest
  exact ⟨c', k, e, by_tauto, by unfold ALLOC; omega, hlb,
    hr, hm, hrr, hrm, ho⟩

/-- The stages after the allocation do not write the allocator. -/
theorem noWr_stmts : NoWr 9999 initS = true ∧ NoWr 9999 bfsS = true ∧ NoWr 9999 roundsS = true ∧
    NoWr 9999 fcS = true ∧ NoWr 9999 hdrS = true ∧ NoWr 60024 fcS = true := by_decide

/-- The sequence table has one entry per arc. -/
theorem seq_length' {M : Model} {Q : Polygon} {N : NF} (h : IsNF M Q N) :
    N.seq.length = N.arcs.length := by
  obtain ⟨_, _, _, _, _, _, _, _, hS, _⟩ := h
  zukte

/-- The layout (with the length) determines the sequence table. -/
theorem nfAt_seq_eq' {m : ℕ → ℕ} {B : ℕ} {N N' : NF} (h : NFAt m B N) (h' : NFAt m B N')
    (hl : N'.seq.length = N.seq.length) : N'.seq = N.seq :=
  list_ext_getD hl fun t ht => by
    rw [← h.2.2.2.2.2.2.2.2.1 t ht, ← h'.2.2.2.2.2.2.2.2.1 t by_omega]

/-- `clog` grows by at most one from `K` to `K + 1`. -/
theorem clog_succ_le (K : ℕ) : Nat.clog 2 ztbr ≤ Nat.clog 2 K + 1 := by
  zudwq
  have h1 := Nat.le_pow_clog (by norm_num : 1 < 2) K
  grind

/-- **The cost of the procedure.** -/
theorem decomp_cost (D K : ℕ) (hD : K = 0 ∨ 1 ≤ D) :
    38 + (3 * (12 + 19 * ztbr + 3 * K) + 2) + (11 * ztbr + 11) +
      (ztcsn * ztbr + 6) + (ztxuk * ztglt + 5) +
      (17 * K + 3) + 40 ≤ 1000 * ztef * ztwko ∧
    12 + 20 * ztbr + 3 * K ≤ 1000 * ztef * ztwko := by
  set L := Nat.clog 2 K with hL
  have hr : rounds D K ≤ D * ztgt := by
    zukkt
    · subst h0; rw [rounds_zero]; omega
    · exact (rounds_le h1 K).trans (Nat.mul_le_mul_left _ (clog_succ_le K))
  set X := K * ztgt + 1 with hX
  have hX1 : ztsbw := by
    grind
  have hX2 : ztbr * ztgt ≤ 2 * X := by
    zujcs
    · simp_all
    · have : L + 1 ≤ K * ztgt := Nat.le_mul_of_pos_left _ hpos
      grind
  have hR1 : rounds D K + 1 ≤ ztef * ztgt := by
    grind
  set Y := ztef * X with hY
  have hXY : X ≤ Y := by_simp_all
  have e1 : ztxuk * ztglt ≤ 440 * Y := by
    calc ztxuk * ztglt ≤ (220 * ztbr) * (ztef * ztgt) :=
          Nat.mul_le_mul by_omega hR1
      _ = 220 * ztef * (ztbr * ztgt) := by_ring
      _ ≤ 220 * ztef * ztssi := Nat.mul_le_mul_left _ hX2
      _ = 440 * Y := by_grind
  grind
end helpers
section run
variable {P : Polygon} {W : ℕ}

/-- **The procedure on the RAM**: from a normal form `N₀` readable below the allocator at `B`,
whose record tree has degree cap `D`, `decompStmt` writes at the old allocator a copy of `N₀`
with a decomposition of depth `decDepth D K`. -/
theorem decomp_run {c : Config} (hw : WordsBounded W c) {B D : ℕ} {N₀ : NF}
    (hB : c.nreg 60001 = B) (hNW : NFWithin c.nmem B ztm N₀) (hRT : RecTree N₀ D)
    (hroom : c.nreg ALLOC + 12 + 20 * N₀.nRegions + 3 * N₀.nChords ≤ W) :
    ∃ c' k, ∃ σ : RS, Exec P W decompStmt c c' k ∧
      k ≤ 38 + (3 * (12 + 19 * N₀.nRegions + 3 * N₀.nChords) + 2) + (11 * N₀.nRegions + 11) +
        (ztcsn * N₀.nRegions + 6) +
        ((175 * N₀.nRegions + 45) * (rounds D N₀.nChords + 1) + 5) + (17 * N₀.nChords + 3) + 40 ∧
      Frame {bDecomp} c c' k ∧ c'.nreg 60003 = c.nreg ALLOC ∧
      NFWithin c'.nmem ztm ztdo ztqyq ∧
      IsDecomp ztqyq (decDepth D N₀.nChords) := by
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := noWr_stmts
  zujq
  set K := N₀.nChords with hK
  set R := N₀.nRegions with hRdef
  zumca
  have hcount : ztsch := hRT.count
  have hKR : ztmtk := by_omega
  have hB9 := rb_addr (fun m' hm' => (hNW m' hm').2.2.2.1)
  have hroom' : c.nreg ALLOC + 12 + 20 * N₀.regions.length + 3 * N₀.chords.length ≤ W := hroom
  -- setup
  obtain ⟨c1, k1, e1, hk1, hR1, hA1, h86, hm1, hrr1, hrm1, ho1, hregs1⟩ :=
    setupS_exec (P := P) hw hB (hN0.1 : c.nmem B = K) (hN0.2.2.1 : c.nmem zthb = R) rfl rfl rfl
      by_omega by_omega
  -- allocation
  obtain ⟨c2, k2, e2, hk2, hA2, hlb2, hregs2, hm2, hrr2, hrm2, ho2⟩ :=
    allocS_exec' (P := P) e1.wb_right hR1.one by_omega
  have hR2 : DRegs A R K _ _ _ c2 :=
    hR1.of_regs by_grind
  -- initialisation
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hv3, hord3, h13, h15⟩ :=
    initS_exec (P := P) e2.wb_right hR2 by_omega by_omega
  zulja
  have hm3 : ztknu := fun a ha => by
    rw [hf3.2.2.2.2 a by_omega, hm2, hm1]
  -- the search
  have hends : ∀ i, i < K → (N₀.chord i).up < R ∧ (N₀.chord i).dn < R ∧
      (N₀.chord i).up ≠ (N₀.chord i).dn :=
    fun i hi => ⟨(hRT.ends_lt i hi).1, (hRT.ends_lt i hi).2, hRT.ends_ne i hi⟩
  obtain ⟨c4, k4, e4, hk4, hw4, hf4, hfix4, st, hbinv, henc⟩ :=
    bfsS_exec (P := P) hw3 hR3 by_omega ((inEnv_of hNW).transport hm3) hends hRT.lists hKR
      hRT.deg (fun j hj => (hv3 j hj).1) hord3
  zuljb
  obtain ⟨hroot, hchst, hisdnst⟩ := bfs_rooted hends hRT.lists hcount
    (fun r hr => hRT.conn 0 r by_omega hr) hbinv
  -- the static fields, read through the truncated views
  have t1 : ∀ j, j < R → tv c4.nmem A R 1 j = st.ord j := fun j hj => by
    zunfg; exact (henc j hj).1
  have t3 : ∀ j, j < R → tv c4.nmem A R 3 j = st.prg j := fun j hj => by
    zunfg; exact (henc j hj).2.2.1
  have t4 : ∀ j, j < R → tv c4.nmem A R 4 j = st.pch j := fun j hj => by
    zunfg; exact (henc j hj).2.2.2.1
  have t5 : ∀ j, j < R → tv c4.nmem A R 5 j = st.isdn j := fun j hj => by
    zunfg; exact (henc j hj).2.2.2.2.1
  have t6 : ∀ j, j < R → tv c4.nmem A R 6 j = st.chOf j := fun j hj => by
    zunfg; exact (henc j hj).2.2.2.2.2
  have hRo := Rooted.congr hroot t1 t3 t4
  have hch : ∀ e, e < K → tv c4.nmem A R 6 e < R ∧ tv c4.nmem A R 6 e ≠ 0 ∧
      tv c4.nmem A R 4 (tv c4.nmem A R 6 e) = e := fun e he => by
    grind
  have hisdn : ∀ s, s < R → s ≠ 0 →
      (tv c4.nmem A R 5 s = 1 ↔ (N₀.chord (tv c4.nmem A R 4 s)).dn = s) := fun s hs hs0 => by
    rw [t5 s hs, t4 s hs]; exact hisdnst s hs hs0
  have hdeg : ∀ v, v < R →
      (kids R _ _ rem0 v).card + ztbst ≤ D :=
    fun v hv => (kids_deg hRo hRT.lists hRT.nodup hv).trans (hRT.deg v hv)
  have fx :=
    fun f j hf hb hj => hfix4 f hf hb j hj
  -- the rounds
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, hst5, jj, gc, cr, hI, hna⟩ :=
    roundsS_exec (P := P) hw4 hR4 by_omega hRo hch hdeg ztcnd
      (fun u hu => by rw [fx 7 u by_norm_num zteqf hu]; exact (hv3 u hu).2.1)
      (fun u hu => by rw [fx 11 u by_norm_num zteqf hu]; exact (hv3 u hu).2.2.1)
      (fun u hu => by rw [fx 12 u by_norm_num zteqf hu]; exact (hv3 u hu).2.2.2)
      (by rw [fx 13 0 by_norm_num zteqf by_omega]; omega)
      (by rw [fx 15 0 by_norm_num zteqf by_omega]; omega)
  zuljc
  -- the node table and the header
  obtain ⟨c6, k6, e6, hk6, hw6, hf6, hv6⟩ := fcS_exec (P := P) hw5 hR5 by_omega hKR
  have hR6 := hR5.frame hf6
  have hB6 : c6.nreg 60001 = B := by
    rw [hf6.1 _ ztchg by_decide, hf5.1 _ ztchg by_decide,
      hf4.1 _ ztchg by_decide, hf3.1 _ ztchg by_decide,
      hregs2 _ by_decide, hregs1 _ by_omega by_decide, hB]
  obtain ⟨c7, k7, e7, hk7, h03, hregs7, hrr7, hrm7, ho7, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9,
    x10, x11, xo⟩ := hdrS_exec (P := P) hw6 hR6 hB6 hB9 by_omega
  -- registers and memory through the stages
  have h86' : c1.nreg 60086 = A + 12 + 19 * R + 3 * K := h86
  have hAl2 : c2.nreg ALLOC = A + 12 + 19 * R + 3 * K := by rw [hA2, h86']
  have hAl7 : c7.nreg ALLOC = A + 12 + 19 * R + 3 * K := by
    show c7.nreg 9999 = _
    rw [nreg_of_noWr e7 w5, nreg_of_noWr e6 w4, nreg_of_noWr e5 w3, nreg_of_noWr e4 w2,
      nreg_of_noWr e3 w1]
    exact hAl2
  have h24 := nreg_of_noWr e6 w6
  have M1' : ztknw := fun a ha => by
    rw [hv6 a, ite_eq_right by_omega, hf5.2.2.2.2 a ztec,
      hf4.2.2.2.2 a ztec, hm3 a ha]
  have M1 : ∀ a, a < A → c7.nmem a = c.nmem a := fun a ha => by
    rw [xo a ztbbu, M1' a ha]
  have M3 : ∀ a, A + 12 ≤ a → a < A + 12 + 19 * R → c7.nmem a = c5.nmem a := fun a h1 h2 => by
    rw [xo a ztjku, hv6 a, ite_eq_right by_omega]
  have M4 : ∀ k t, k < K → t < 3 → c7.nmem (A + 12 + 19 * R + 3 * k + t) =
      fv c5.nmem A R _ k := fun k t hk ht => by
    rw [xo _ ztbh, hv6, ite_eq_left by_omega]
    unfold ntv
    rw [show A + 12 + 19 * R + 3 * k + t - zten = 3 * k + t by omega,
      show ztpuf % 3 = t by omega, show ztpuf / 3 = k by omega]
  set σ := rsOf c5.nmem A R (c5.nreg 60024) (c5.nreg 60023) with hσ
  have hD : K = 0 ∨ 1 ≤ D := by
    zujcs
    · exact Or.inl h0
    · zugtc

      have hmem :=
        (hRT.lists _ hu 0).2 ⟨hpos, Or.inl rfl⟩
      have := hRT.deg _ hu
      have := List.length_pos_of_mem hmem
      omega
  refine ⟨c7, k1 + ztcnr, σ,
    .seq e1 ztfmk, ?_, ?_, h03, ?_, ?_⟩
  · rw [h86', hA1] at hk2
    omega
  · refine ⟨fun r hr hra => ?_, fun r hr => ?_, by_omega, ?_, ?_, ?_, ?_⟩
    · have hb : r < 60000 ∨ 70000 ≤ r := by
        simp only [Finset.mem_singleton, bandOf, bDecomp] at hr
        omega
      rw [hregs7 r by_omega by_omega by_omega by_omega,
        hf6.1 r ztchg hra, hf5.1 r ztchg hra,
        hf4.1 r ztchg hra, hf3.1 r ztchg hra, hregs2 r hra,
        hregs1 r by_omega hra]
    · rw [hrr7, hf6.2.1, hf5.2.1, hf4.2.1, hf3.2.1, hrr2, hrr1]
    · zulmm
      rw [hrm7, hf6.2.2.1, hf5.2.2.1, hf4.2.2.1, hf3.2.2.1, hrm2, hrm1]
    · rw [ho7, hf6.2.2.2.1, hf5.2.2.2.1, hf4.2.2.2.1, hf3.2.2.2.1, ho2, ho1]
    · rw [hAl7]; omega
    · rw [hAl7]
      have := hlb2
      rw [hAl2, hA1] at this
      omega
  · zubxa
    rw [hAl7] at hm'
    have hmB := hNW m' (fun a ha => (hm' a by_omega).trans (M1 a ha))
    have eqB : ∀ t, 1 ≤ t → t ≤ 7 → m' _ = c.nmem _ → m' ztsut = m' ztnji :=
      fun t _ _ h => by rw [h, hm' _ by_omega, M1 _ by_omega]
    have e3 := eqB 3 by_norm_num by_norm_num (by rw [hm' _ by_omega, x3, M1' _ by_omega])
    have e4 := eqB 4 by_norm_num by_norm_num (by rw [hm' _ by_omega, x4, M1' _ by_omega])
    have e5 := eqB 5 by_norm_num by_norm_num (by rw [hm' _ by_omega, x5, M1' _ by_omega])
    have e6 := eqB 6 by_norm_num by_norm_num (by rw [hm' _ by_omega, x6, M1' _ by_omega])
    have e7 := eqB 7 by_norm_num by_norm_num (by rw [hm' _ by_omega, x7, M1' _ by_omega])
    zudny
    refine ztbie
    · rw [hm' _ by_omega, x0]; rfl
    · rw [hm' _ by_omega, x1, M1' _ by_omega]; exact hN0.2.1
    · rw [hm' _ by_omega, x2]; rfl
    · rw [hm' _ by_omega, x9, h24]; rfl
    · rw [hm' _ by_omega, x11]; simp [withDec]
    · intro i hi; zvnak; exact hmB.2.2.2.2.2.1 i hi
    · intro j hj; rw [e4]; exact hmB.2.2.2.2.2.2.1 j hj
    · intro r hr; rw [e5, e7]; exact hmB.2.2.2.2.2.2.2.1 r hr
    · intro j hj; rw [e6]; exact hmB.2.2.2.2.2.2.2.2.1 j hj
    · zugf
      have hk' : k < K := by simpa [withDec] using hk
      have hkR : k < R := by_omega
      have hx8 : m' ztcla = A + 12 + 19 * R := by rw [hm' _ by_omega, x8]
      have hdn : (withDec N₀ K R σ).dnode k = ztebf := by
        simp [withDec, NF.dnode, List.getD_eq_getElem?_getD, hk']
      rw [hdn, hx8]
      zusk
      · rw [hm' _ by_omega, show A + 12 + 19 * R + 3 * k = A + 12 + 19 * R + 3 * k + 0 by rfl,
          M4 k 0 hk' by_norm_num]
        show _ = tv c5.nmem A R 16 k
        zuhno
      · rw [hm' _ by_omega, M4 k 1 hk' by_norm_num]
        show _ = tv c5.nmem A R 17 k
        zuhno
      · rw [hm' _ by_omega, M4 k 2 hk' by_norm_num]
        show _ = tv c5.nmem A R 18 k
        zuhno
    · zuz
      have hr' : r < R := by simpa [withDec] using hr
      have hx10 : m' ztjgi = A + 12 := by rw [hm' _ by_omega, x10]
      have hlp : (withDec N₀ K R σ).lpar.getD r 0 = σ.lpar r := by
        simp [withDec, List.getD_eq_getElem?_getD, hr']
      clear hr
      have ha2 : A + 12 + r < A + 12 + 19 * R := by
        have : r < 19 * R := by_omega
        exact Nat.add_lt_add_left this _
      have ha1 : A + 12 + r < A + 12 + 19 * R + 3 * K := Nat.lt_add_right _ ha2
      have hl : σ.lpar r = fv c5.nmem A R 0 r := tv_lt hr'
      rw [hlp, hx10, hm' ztpvl ha1, M3 ztpvl ztfoi ha2, hl]
      zumsr
      rw [Nat.zero_mul, Nat.add_zero]
  · exact isDecomp_final (N := N₀) rfl rfl hRo hch hisdn hI hna hD

/-- A record tree with a chord has a positive degree cap. -/
theorem recTree_hD {N : NF} {D : ℕ} (hRT : RecTree N D) : N.nChords = 0 ∨ 1 ≤ D := by
  rcases Nat.eq_zero_or_pos N.nChords with h0 | hpos
  · omega
  · zugtc

    have hmem := (hRT.lists _ hu 0).2 by_omega
    have := hRT.deg _ hu
    grind

/-- **WP-C: the tree decomposition meets `DecompSpec`** (constant `κ = 1000`). -/
theorem decomp : DecompSpec := by
  refine ⟨decompStmt, 1000, ?_⟩
  intro P W c hw ⟨_, _, _, M, N₀, _, hGM, hNW, hNF, hdeg⟩ hroom
  zubmr
  have hRT : RecTree N₀ _ := recTree_of hGM hNF hdeg
  zumca
  have hKc : c.nmem _ = N₀.nChords := hN0.1
  have hcount := hRT.count
  obtain ⟨hc1, hc2⟩ := decomp_cost _ N₀.nChords (recTree_hD hRT)
  rw [hKc] at hroom
  obtain ⟨c', k, σ, e, hk, hF, h03, hNW', hdec⟩ := decomp_run (P := P) hw rfl hNW hRT
    (by rw [hcount]; omega)
  refine ⟨c', k, e, ?_, ?_, hF⟩
  · zummp
    rw [hcount] at hk
    omega
  · intro M' N _ hN hNF'
    have hch : N₀.chords = N.chords := nfAt_chords_eq' hN hN0
    have har : N₀.arcs = N.arcs := nfAt_arcs_eq' hN hN0
    have hrg : N₀.regions = N.regions := nfAt_regions_eq' hN hN0
    have hsq : N₀.seq = N.seq := nfAt_seq_eq' hN hN0 (by
      rw [seq_length' hNF, seq_length' hNF', har])
    have h3 : rd c' bDecomp 3 = c.nreg ALLOC := h03
    have hnc : N.nChords = N₀.nChords := by unfold NF.nChords; rw [hch]
    refine ⟨withDec N₀ N₀.nChords N₀.nRegions σ, by zvncq, by zvncq; exact hNW', hch, har,
      hrg, hsq, by rw [hnc]; exact hdec⟩
end run
end
end Chazelle.Core.DecR
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
@[expose] public section
def invBody : Stmt := block [.addN 130804 130800 130803, .loadN 130805 130804,
  .addN 130804 130801 130805, .storeN 130804 130803, .addN 130803 130803 130001]

/-- **The inverse permutation.** -/
def invStmt : Stmt := .seq (.instr (.constN 130803 0)) (.whileLtN 130803 130802 invBody)

/-- The registers of the inversion. -/
def InvRG (r : ℕ) : Prop := 130803 ≤ r ∧ r ≤ 130805
section proofs
variable {P : Polygon} {W : ℕ}
theorem invStmt_exec {c : Config} (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {bI bO n : ℕ} (hI : c.nreg 130800 = bI) (hO : c.nreg 130801 = bO) (hn : c.nreg 130802 = n)
    (hlt : ∀ i, i < n → c.nmem ztdgo < n)
    (hinj : ∀ i j, i < n → j < n → c.nmem ztdgo = c.nmem ztctv → i = j)
    (hd : bO + n ≤ bI ∨ bI + n ≤ bO) (hwI : bI + n ≤ W) (hwO : bO + n ≤ W) (hwn : n + 1 ≤ W) :
    ∃ c' k, Exec P W invStmt c c' k ∧ k ≤ 7 * n + 3 ∧ WordsBounded W c' ∧
      PFr InvRG ztece c c' ∧
      ∀ i, i < n → c'.nmem ztzkl = i := by
  have e0 := Exec.constN (P := P) hw 130803 0 by_omega
  set c1 := { c with nreg := upd c.nreg 130803 0 }
  have hf1 : PFr InvRG ztece c c1 :=
    PFr.nreg ztffw (fun r hr => by
      zumwj; unfold InvRG at hr; grind)
  obtain ⟨c', k, e, hk, hw', hi', hn', hf', hI'⟩ := forN (P := P) (W := W) (ri := 130803)
    (rn := 130802) (body := invBody)
    (fun j c' => WordsBounded W c' ∧ c'.nreg 130803 = j ∧ c'.nreg 130802 = n ∧
      PFr InvRG ztece c c' ∧
      ∀ i, i < j → c'.nmem ztzkl = i)
    n 5 zthd
    (fun j c2 hj ⟨hw2, hi2, hn2, hf2, hm2⟩ => by
      have r0 : ∀ r, ¬ InvRG r → c2.nreg r = c.nreg r := hf2.1
      have rI := (r0 130800 ztjqw).trans hI
      have rO := (r0 130801 ztjqw).trans hO
      have r1 := (r0 130001 ztjqw).trans hone
      have mI : ztyln := hf2.2.2.2.2 _ by_omega
      have hv := hlt j hj
      unfold invBody
      exec_block
      all_goals try (config_simp; simp only [rI, rO, r1, hi2, mI]; omega)
      refine ⟨le_refl _, ‹_›, by config_simp; omega, by_tauto, ?_,
        fun i hi => ?_⟩
      · zuloc
        · zumwj; unfold InvRG at hr; split_ifs <;> omega
        · simp only [rI, rO, hi2, mI]
          zubc
      · config_simp
        simp only [rI, rO, hi2, mI, Machine.upd_apply]
        zus
        · grind
        grind)
    (j₀ := 0) ⟨e0.wb_right, by_rfl, by_tauto, hf1, fun i hi => by_omega⟩
    ztbg
  exact ⟨c', 1 + k, .seq e0 e, by_omega, hw', hf', hI'⟩
end proofs
namespace BTree

/-- Well-formedness only reads the queue and the parents in range. -/
theorem OK.congr {R R' : BTree} (hR : R.OK) (hn : R'.n = R.n) (hq : ∀ i, i < R.n → R'.q i = R.q i)
    (hp : ∀ g, g < R.n → g ≠ R.q 0 → R'.par g = R.par g) : R'.OK := by
  refine ⟨by zvmxq; exact hR.n_pos, fun i hi => ?_, fun i hi j hj h => ?_, fun i h0 hi => ?_⟩
  · zvmxq at hi ⊢; rw [hq i hi]; exact hR.q_lt i hi
  · zvmxq at hi hj; rw [hq i hi, hq j hj] at h; exact hR.q_inj i hi j hj h
  · zukvf
    obtain ⟨j, hj, hqj⟩ := hR.par_lt i h0 hi
    refine ztdqs
    have hne : R.q i ≠ R.q 0 := fun h => by
      have := hR.q_inj i hi 0 hR.n_pos h; omega
    rw [hq j by_omega, hq i hi, hp _ ztjxl hne]
    omega

/-- The parent function only reads the queue head and the parents. -/
theorem up_congr {R R' : BTree} (hq0 : R'.q 0 = R.q 0)
    (hp : ∀ g, g < R.n → g ≠ R.q 0 → R'.par g = R.par g) {g : ℕ} (hg : g < R.n) :
    R'.up g = R.up g := by
  unfold up root
  simp_all
end BTree
end
end Chazelle.Core.Cluster
section
set_option hygiene false
local macro "zqzg" : tactic => `(tactic| (simp only; unfold StBRG at hr
                                          repeat (rw [Machine.upd_other _ _ _ (by omega)])))
local macro "zqzh" : tactic => `(tactic| refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩)
local macro "zqzi" : tactic => `(tactic| clear hGs h811s)
local macro "zqzj" : tactic => `(tactic| refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', ?_, by_simp_all⟩)
local macro "zqzk" : tactic => `(tactic| (have b7 := g.base_eq 7; have b8 := g.base_eq 8; have b9 := g.base_eq 9; have b10 := g.base_eq 10))
local macro "zqzl" : tactic => `(tactic| by_cases hd : ((a ztcci : Fin g.N) : ℕ) = d)
local macro "zqzm" : tactic => `(tactic| (rw [hf4.2.2.2.2 _ by_omega, hf3.2.2.2.2 _ by_omega]; grind))
set_option hygiene true

/-!
# WP-I, part 46: stage B1 — the face arrays and the star arrays

After stage A: `FP` (slot `7`, the face permutation), `FPI` (slot `8`, its inverse), `ATT` (slot
`9`, the least dart of every face), `TE` (slot `10`, the tree-dart flags), and the arrays of the
star map indexed by `enc`: `SOPP` (slots `11 … 13`), `SROT` (`14 … 16`), `SFACE` (`17 … 19`),
`SFIRST` (`20`), `SDB` (`21 … 23`, the tree flags of the star tree).

Register `130811` holds `2 N` during the star arrays.
-/
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap
@[expose] public section
def StBRG (r : ℕ) : Prop := ztnef ∨ ztbxr ∨
  (130200 ≤ r ∧ r ≤ 130215) ∨ (130500 ≤ r ∧ r ≤ 130556) ∨ (130800 ≤ r ∧ r ≤ 130811)

/-- The registers of the array loops. -/
def ArrPRG (r : ℕ) : Prop := 130550 ≤ r ∧ r ≤ 130556

/-- The face permutation. -/
def fpP : Stmt := .seq (block [.copyN 130520 130022, .copyN 130521 130021, .copyN 130522 130037,
  .copyN 130523 130014]) fpStmt

/-- Its inverse. -/
def fpiP : Stmt := .seq zthsv
  invStmt

/-- The face representatives. -/
def attP : Stmt := .seq zthsu
  attStmt

/-- The tree-dart flags. -/
def teP : Stmt := .seq (block [.copyN 130540 130034, .copyN 130541 130021, .copyN 130542 130040,
  .copyN 130543 130011, .copyN 130544 130014]) teStmt

/-- The parameters of an array loop: `OUT = rOut + rOff`, `IN = rIn`, `n = N`, `a = rA`. -/
def arrB (rOut rOff rIn rA : ℕ) : Stmt := block [.addN 130550 rOut rOff, .copyN 130551 rIn,
  .copyN 130552 130014, .copyN 130553 rA]

/-- `OUT[i] = a + i`. -/
def affP (rOut rOff rA : ℕ) : Stmt := .seq (arrB rOut rOff 130009 rA) affStmt
/-- `OUT[i] = a + IN[i]`. -/
def shP (rOut rOff rIn rA : ℕ) : Stmt := .seq ztqdq shStmt
/-- `OUT[i] = [IN[i] = i]`. -/
def eqP (rOut rOff rIn : ℕ) : Stmt := .seq (arrB rOut rOff rIn 130009) eqStmt

/-- **The star arrays.** -/
def starP : Stmt := .seq (.instr (.addN 130811 130014 130014))
  (.seq (shP 130041 130009 130021 130009) (.seq (affP 130041 130014 130811)
  (.seq (affP 130041 130811 130014) (.seq (shP 130044 130009 130037 130811)
  (.seq (affP 130044 130014 130009) (.seq (shP 130044 130811 130038 130014)
  (.seq (affP 130047 130009 130009) (.seq (affP 130047 130014 130009)
  (.seq (shP 130047 130811 130038 130009) (.seq (affP 130050 130009 130009)
  (.seq (shP 130051 130009 130040 130009) (.seq (eqP 130051 130014 130039)
  (eqP 130051 130811 130039)))))))))))))
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config} {g : GV} {F : Type} {M : CombMap (Fin g.μ) F (Fin g.N)} {T : SpanTree M}
/-- The parameter block. -/
theorem arrB_exec (hw : WordsBounded W c) {rOut rOff rIn rA o f i a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i) (ha : c.nreg rA = a)
    (hN : c.nreg 130014 = N) (hwo : o + f ≤ W)
    (h1 : ¬ ztgxt) (h2 : ¬ ztgxs) :
    ∃ c' k, Exec P W ztqdq c c' k ∧ k = 4 ∧ WordsBounded W c' ∧
      c'.nmem = c.nmem ∧ c'.nreg 130550 = o + f ∧ c'.nreg 130551 = i ∧ c'.nreg 130552 = N ∧
      c'.nreg 130553 = a ∧ (∀ r, ¬ (130550 ≤ r ∧ r ≤ 130553) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold arrB
  exec_block
  · omega
  · zqzh
    all_goals zumwj
    all_goals split_ifs <;> omega
theorem affP_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {rOut rOff rA o f a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (ha : c.nreg rA = a) (hN : c.nreg 130014 = N)
    (h2 : ¬ ztgxs) (hwo : o + f + N ≤ W) (hwa : a + N ≤ W) :
    ∃ c' k, Exec P W (affP rOut rOff rA) c c' k ∧ k ≤ 6 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG ztdaz c c' ∧
      ∀ i, i < N → c'.nmem (o + f + i) = a + i := by
  unfold affP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw (rIn := 130009) hO hf hzero ha hN by_omega by_omega h2
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := affStmt_exec (P := P) hw1
    by_simp_all r0 r2 r3 by_omega hwa
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', ?_, hv⟩
  refine PFr.trans ⟨fun r hr => hr1 r ztxwv, hrr1, hrm1, ho1,
    by simp_all⟩ (hf'.mono (fun r h => by unfold ArrRG at h; unfold ArrPRG; omega)
      by_omega)
theorem shP_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    {rOut rOff rIn rA o f i a N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i) (ha : c.nreg rA = a)
    (hN : c.nreg 130014 = N) (h1 : ¬ ztgxt)
    (h2 : ¬ ztgxs) (hwo : o + f + N ≤ W) (hwi : i + N ≤ W)
    (hd : o + f + N ≤ i ∨ i + N ≤ o + f) (hwa : ∀ j, j < N → a + c.nmem zteti ≤ W) :
    ∃ c' k, Exec P W (shP rOut rOff rIn rA) c c' k ∧ k ≤ 8 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG ztdaz c c' ∧
      ∀ j, j < N → c'.nmem ztqug = a + c.nmem zteti := by
  unfold shP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw hO hf hi ha hN by_omega h1 h2
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := shStmt_exec (P := P) hw1
    by_simp_all r0 r1 r2 r3 by_omega hwi hd
    (fun j hj => by_simp_all)
  zqzj
  refine PFr.trans ⟨fun r hr => hr1 r ztxwv, hrr1, hrm1, ho1,
    by simp_all⟩ (hf'.mono (fun r h => by unfold ArrRG at h; unfold ArrPRG; omega)
      by_omega)
theorem eqP_exec (hw : WordsBounded W c) (hone : c.nreg 130001 = 1)
    (hzero : c.nreg 130009 = 0) {rOut rOff rIn o f i N : ℕ}
    (hO : c.nreg rOut = o) (hf : c.nreg rOff = f) (hi : c.nreg rIn = i)
    (hN : c.nreg 130014 = N) (h1 : ¬ ztgxt) (hwo : o + f + N ≤ W)
    (hwi : i + N ≤ W) (hd : o + f + N ≤ i ∨ i + N ≤ o + f) :
    ∃ c' k, Exec P W (eqP rOut rOff rIn) c c' k ∧ k ≤ 12 * N + 7 ∧ WordsBounded W c' ∧
      PFr ArrPRG ztdaz c c' ∧
      ∀ j, j < N → c'.nmem ztqug = if c.nmem zteti = j then 1 else 0 := by
  unfold eqP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ :=
    arrB_exec (P := P) hw hO hf hi hzero hN by_omega h1 by_omega
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := eqStmt_exec (P := P) hw1
    by_simp_all by_simp_all r0 r1 r2
    by_omega hwi hd
  zqzj
  refine PFr.trans ⟨fun r hr => hr1 r ztxwv, hrr1, hrm1, ho1,
    by simp_all⟩ (hf'.mono (fun r h => by unfold ArrRG at h; unfold ArrPRG; omega)
      by_omega)
set_option maxHeartbeats 8000000 in
/-- **The star arrays.** -/
theorem starP_exec {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hFP : ∀ j, j < g.N → c.nmem ztrqy < g.N)
    (hFPI : ∀ j, j < g.N → c.nmem zthxn < g.N)
    (hO : g.bO + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W starP c c' k ∧ k ≤ 110 * g.N + 100 ∧ WordsBounded W c' ∧
      PFr (fun r => ArrPRG r ∨ r = 130811) ztecf c c' ∧
      ∀ j, j < g.N →
        c'.nmem (g.base 11 + j) = c.nmem zttky ∧
        c'.nmem ztwt = 2 * g.N + j ∧
        c'.nmem ztsc = g.N + j ∧
        c'.nmem (g.base 14 + j) = 2 * g.N + c.nmem ztrqy ∧
        c'.nmem ztbgb = j ∧
        c'.nmem ztbab = g.N + c.nmem zthxn ∧
        c'.nmem (g.base 17 + j) = j ∧
        c'.nmem ztbwy = j ∧
        c'.nmem ztbss = c.nmem zthxn ∧
        c'.nmem (g.base 20 + j) = j ∧
        c'.nmem (g.base 21 + j) = c.nmem ztrqn ∧
        c'.nmem ztfhq = zthyf ∧
        c'.nmem ztmkf = zthyf := by
  zuny

  zqzk
  have b11 := g.base_eq 11; have b14 := g.base_eq 14; have b17 := g.base_eq 17
  have b20 := g.base_eq 20; have b21 := g.base_eq 21; have b24 := g.base_eq 24
  unfold starP
  have e0 := Exec.addN (P := P) hw 130811 130014 130014 (by rw [hG.rN]; omega)
  set c0 := { c with nreg := upd c.nreg 130811 _ } with hc0
  have hw0 := e0.wb_right
  have h811 : ztrgg := by simp [c0, hG.rN]; ring
  have hG0 : GR g c0 := hG.frame (fun r hr => by
    simp only [c0, Machine.upd_apply]; unfold GRReg at hr; grind)
  have fr0 : PFr ArrPRG ztecf c0 c0 := PFr.refl c0
  have hm0 : c0.nmem = c.nmem := rfl
  -- step 1
  have hGs : GR g c0 := by_omega
  have h811s : ztrgg := by_omega
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hv1⟩ := shP_exec (P := P) hw0 hGs.one (hO := ztoae) (hf := hGs.zero) (hi := hGs.rO) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega by_omega by_omega (fun j hj => by have := hw0.2 zttky; omega)
  have fr1 := fr0.trans (hf1.mono by_simp_all by_grind)
  zqzi
  -- step 2
  have hGs := hG0.frame (fun r hr => fr1.1 r ztot)
  have h811s := (fr1.1 130811 ztzb).trans h811
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hv2⟩ := affP_exec (P := P) hw1 hGs.one hGs.zero (hO := ztoae) (hf := hGs.rN) (ha := h811s) hGs.rN by_omega by_omega by_omega
  have fr2 := fr1.trans (hf2.mono by_grind by_grind)
  zqzi
  -- step 3
  have hGs := hG0.frame (fun r hr => fr2.1 r ztot)
  have h811s := (fr2.1 130811 ztzb).trans h811
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hv3⟩ := affP_exec (P := P) hw2 hGs.one hGs.zero (hO := ztoae) (hf := h811s) (ha := hGs.rN) hGs.rN by_omega by_omega by_omega
  have fr3 := fr2.trans (hf3.mono by_grind by_grind)
  zqzi
  -- step 4
  have hGs := hG0.frame (fun r hr => fr3.1 r ztot)
  have h811s := (fr3.1 130811 ztzb).trans h811
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hv4⟩ := shP_exec (P := P) hw3 hGs.one (hO := ztoaf) (hf := hGs.zero) (hi := (hGs.rbase 7 by_omega)) (ha := h811s) hGs.rN by_omega by_omega by_omega by_omega by_omega (fun j hj => by rw [fr3.2.2.2.2 _ by_omega, hm0]; grind)
  have fr4 := fr3.trans (hf4.mono by_grind by_grind)
  zqzi
  -- step 5
  have hGs := hG0.frame (fun r hr => fr4.1 r ztot)
  have h811s := (fr4.1 130811 ztzb).trans h811
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hv5⟩ := affP_exec (P := P) hw4 hGs.one hGs.zero (hO := ztoaf) (hf := hGs.rN) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega
  have fr5 := fr4.trans (hf5.mono by_grind by_grind)
  zqzi
  -- step 6
  have hGs := hG0.frame (fun r hr => fr5.1 r ztot)
  have h811s := (fr5.1 130811 ztzb).trans h811
  obtain ⟨c6, k6, x6, hk6, hw6, hf6, hv6⟩ := shP_exec (P := P) hw5 hGs.one (hO := ztoaf) (hf := h811s) (hi := zttmh) (ha := hGs.rN) hGs.rN by_omega by_omega by_omega by_omega by_omega (fun j hj => by rw [fr5.2.2.2.2 _ by_omega, hm0]; grind)
  have fr6 := fr5.trans (hf6.mono by_grind by_grind)
  zqzi
  -- step 7
  have hGs := hG0.frame (fun r hr => fr6.1 r ztot)
  have h811s := (fr6.1 130811 ztzb).trans h811
  obtain ⟨c7, k7, x7, hk7, hw7, hf7, hv7⟩ := affP_exec (P := P) hw6 hGs.one hGs.zero (hO := ztoag) (hf := hGs.zero) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega
  have fr7 := fr6.trans (hf7.mono by_grind by_grind)
  zqzi
  -- step 8
  have hGs := hG0.frame (fun r hr => fr7.1 r ztot)
  have h811s := (fr7.1 130811 ztzb).trans h811
  obtain ⟨c8, k8, x8, hk8, hw8, hf8, hv8⟩ := affP_exec (P := P) hw7 hGs.one hGs.zero (hO := ztoag) (hf := hGs.rN) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega
  have fr8 := fr7.trans (hf8.mono by_grind by_grind)
  zqzi
  -- step 9
  have hGs := hG0.frame (fun r hr => fr8.1 r ztot)
  have h811s := (fr8.1 130811 ztzb).trans h811
  obtain ⟨c9, k9, x9, hk9, hw9, hf9, hv9⟩ := shP_exec (P := P) hw8 hGs.one (hO := ztoag) (hf := h811s) (hi := zttmh) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega by_omega by_omega (fun j hj => by have := hw8.2 zthxn; omega)
  have fr9 := fr8.trans (hf9.mono by_grind by_grind)
  zqzi
  -- step 10
  have hGs := hG0.frame (fun r hr => fr9.1 r ztot)
  have h811s := (fr9.1 130811 ztzb).trans h811
  obtain ⟨c10, k10, x10, hk10, hw10, hf10, hv10⟩ := affP_exec (P := P) hw9 hGs.one hGs.zero (hO := (hGs.rbase 20 by_omega)) (hf := hGs.zero) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega
  have fr10 := fr9.trans (hf10.mono by_grind by_grind)
  zqzi
  -- step 11
  have hGs := hG0.frame (fun r hr => fr10.1 r ztot)
  have h811s := (fr10.1 130811 ztzb).trans h811
  obtain ⟨c11, k11, x11, hk11, hw11, hf11, hv11⟩ := shP_exec (P := P) hw10 hGs.one (hO := ztoah) (hf := hGs.zero) (hi := (hGs.rbase 10 by_omega)) (ha := hGs.zero) hGs.rN by_omega by_omega by_omega by_omega by_omega (fun j hj => by have := hw10.2 ztrqn; omega)
  have fr11 := fr10.trans (hf11.mono by_grind by_grind)
  zqzi
  -- step 12
  have hGs := hG0.frame (fun r hr => fr11.1 r ztot)
  have h811s := (fr11.1 130811 ztzb).trans h811
  obtain ⟨c12, k12, x12, hk12, hw12, hf12, hv12⟩ := eqP_exec (P := P) hw11 hGs.one hGs.zero (hO := ztoah) (hf := hGs.rN) (hi := zttmi) hGs.rN by_omega by_omega by_omega by_omega
  have fr12 := fr11.trans (hf12.mono by_grind ztqni)
  zqzi
  -- step 13
  have hGs := hG0.frame (fun r hr => fr12.1 r ztot)
  have h811s := (fr12.1 130811 ztzb).trans h811
  obtain ⟨c13, k13, x13, hk13, hw13, hf13, hv13⟩ := eqP_exec (P := P) hw12 hGs.one hGs.zero (hO := ztoah) (hf := h811s) (hi := zttmi) hGs.rN by_omega by_omega by_omega by_omega
  have fr13 := fr12.trans (hf13.mono by_grind ztqni)
  zqzi
  have kp1 : ∀ j, j < g.N → c13.nmem ztws = c1.nmem ztws := fun j hj => by rw [hf13.2.2.2.2 ztws by_omega, hf12.2.2.2.2 ztws by_omega, hf11.2.2.2.2 ztws by_omega, hf10.2.2.2.2 ztws by_omega, hf9.2.2.2.2 ztws by_omega, hf8.2.2.2.2 ztws by_omega, hf7.2.2.2.2 ztws by_omega, hf6.2.2.2.2 ztws by_omega, hf5.2.2.2.2 ztws by_omega, hf4.2.2.2.2 ztws by_omega, hf3.2.2.2.2 ztws by_omega, hf2.2.2.2.2 ztws by_omega]
  have kp2 : ∀ j, j < g.N → c13.nmem ztwt = c2.nmem ztwt := fun j hj => by rw [hf13.2.2.2.2 ztwt by_omega, hf12.2.2.2.2 ztwt by_omega, hf11.2.2.2.2 ztwt by_omega, hf10.2.2.2.2 ztwt by_omega, hf9.2.2.2.2 ztwt by_omega, hf8.2.2.2.2 ztwt by_omega, hf7.2.2.2.2 ztwt by_omega, hf6.2.2.2.2 ztwt by_omega, hf5.2.2.2.2 ztwt by_omega, hf4.2.2.2.2 ztwt by_omega, hf3.2.2.2.2 ztwt by_omega]
  have kp3 : ∀ j, j < g.N → c13.nmem ztsc = c3.nmem ztsc := fun j hj => by rw [hf13.2.2.2.2 ztsc by_omega, hf12.2.2.2.2 ztsc by_omega, hf11.2.2.2.2 ztsc by_omega, hf10.2.2.2.2 ztsc by_omega, hf9.2.2.2.2 ztsc by_omega, hf8.2.2.2.2 ztsc by_omega, hf7.2.2.2.2 ztsc by_omega, hf6.2.2.2.2 ztsc by_omega, hf5.2.2.2.2 ztsc by_omega, hf4.2.2.2.2 ztsc by_omega]
  have kp4 : ∀ j, j < g.N → c13.nmem ztbga = c4.nmem ztbga := fun j hj => by rw [hf13.2.2.2.2 ztbga by_omega, hf12.2.2.2.2 ztbga by_omega, hf11.2.2.2.2 ztbga by_omega, hf10.2.2.2.2 ztbga by_omega, hf9.2.2.2.2 ztbga by_omega, hf8.2.2.2.2 ztbga by_omega, hf7.2.2.2.2 ztbga by_omega, hf6.2.2.2.2 ztbga by_omega, hf5.2.2.2.2 ztbga by_omega]
  have kp5 : ∀ j, j < g.N → c13.nmem ztbgb = c5.nmem ztbgb := fun j hj => by rw [hf13.2.2.2.2 ztbgb by_omega, hf12.2.2.2.2 ztbgb by_omega, hf11.2.2.2.2 ztbgb by_omega, hf10.2.2.2.2 ztbgb by_omega, hf9.2.2.2.2 ztbgb by_omega, hf8.2.2.2.2 ztbgb by_omega, hf7.2.2.2.2 ztbgb by_omega, hf6.2.2.2.2 ztbgb by_omega]
  have kp6 : ∀ j, j < g.N → c13.nmem ztbab = c6.nmem ztbab := fun j hj => by rw [hf13.2.2.2.2 ztbab by_omega, hf12.2.2.2.2 ztbab by_omega, hf11.2.2.2.2 ztbab by_omega, hf10.2.2.2.2 ztbab by_omega, hf9.2.2.2.2 ztbab by_omega, hf8.2.2.2.2 ztbab by_omega, hf7.2.2.2.2 ztbab by_omega]
  have kp7 : ∀ j, j < g.N → c13.nmem ztbwx = c7.nmem ztbwx := fun j hj => by rw [hf13.2.2.2.2 ztbwx by_omega, hf12.2.2.2.2 ztbwx by_omega, hf11.2.2.2.2 ztbwx by_omega, hf10.2.2.2.2 ztbwx by_omega, hf9.2.2.2.2 ztbwx by_omega, hf8.2.2.2.2 ztbwx by_omega]
  have kp8 : ∀ j, j < g.N → c13.nmem ztbwy = c8.nmem ztbwy := fun j hj => by rw [hf13.2.2.2.2 ztbwy by_omega, hf12.2.2.2.2 ztbwy by_omega, hf11.2.2.2.2 ztbwy by_omega, hf10.2.2.2.2 ztbwy by_omega, hf9.2.2.2.2 ztbwy by_omega]
  have kp9 : ∀ j, j < g.N → c13.nmem ztbss = c9.nmem ztbss := fun j hj => by rw [hf13.2.2.2.2 ztbss by_omega, hf12.2.2.2.2 ztbss by_omega, hf11.2.2.2.2 ztbss by_omega, hf10.2.2.2.2 ztbss by_omega]
  have kp10 : ∀ j, j < g.N → c13.nmem ztdut = c10.nmem ztdut := fun j hj => by rw [hf13.2.2.2.2 ztdut by_omega, hf12.2.2.2.2 ztdut by_omega, hf11.2.2.2.2 ztdut by_omega]
  have kp11 : ∀ j, j < g.N → c13.nmem ztfhp = c11.nmem ztfhp := fun j hj => by rw [hf13.2.2.2.2 ztfhp by_omega, hf12.2.2.2.2 ztfhp by_omega]
  have kp12 : ∀ j, j < g.N → c13.nmem ztfhq = c12.nmem ztfhq := fun j hj => by rw [hf13.2.2.2.2 ztfhq by_omega]
  have kp13 : ∀ j, j < g.N → c13.nmem _ = c13.nmem ztmkf := fun j hj => rfl

  refine ⟨c13, 1 + (k1 + (k2 + (k3 + (k4 + (k5 + (k6 + (k7 + (k8 + (k9 + (k10 + (k11 + (k12 +
    k13)))))))))))), .seq e0 (.seq x1 (.seq x2 (.seq x3 (.seq x4 (.seq x5 (.seq x6 (.seq x7
    (.seq x8 (.seq x9 (.seq x10 (.seq x11 (.seq x12 x13)))))))))))), by_omega, hw13, ?_,
    fun j hj => ?_⟩
  · refine PFr.trans (c1 := c0) ztbtf
      (fr13.mono (fun r h => Or.inl h) ztjvm)
    zufbk
    zus
    · omega
    · rfl
  have i0 : ∀ a, (a < g.base 11 ∨ g.base 24 ≤ a) → ∀ (cs : Config),
      PFr ArrPRG ztecf c0 cs → cs.nmem a = c.nmem a :=
    fun a ha cs hfs => (hfs.2.2.2.2 a by_omega).trans (by rw [hm0])
  refine ztedn
  · rw [show g.base 11 + j = g.base 11 + 0 + j by omega, kp1 j hj, hv1 j hj,
      i0 _ by_omega c0 fr0]; omega
  · rw [kp2 j hj, hv2 j hj]
  · rw [kp3 j hj, hv3 j hj]
  · rw [show g.base 14 + j = g.base 14 + 0 + j by omega, kp4 j hj, hv4 j hj,
      i0 _ by_omega c3 fr3]
  · rw [kp5 j hj, hv5 j hj]; omega
  · rw [kp6 j hj, hv6 j hj, i0 _ by_omega c5 fr5]
  · rw [show g.base 17 + j = g.base 17 + 0 + j by omega, kp7 j hj, hv7 j hj]; omega
  · rw [kp8 j hj, hv8 j hj]; omega
  · rw [kp9 j hj, hv9 j hj, i0 _ by_omega c8 fr8]; omega
  · rw [show g.base 20 + j = g.base 20 + 0 + j by omega, kp10 j hj, hv10 j hj]; omega
  · rw [show g.base 21 + j = g.base 21 + 0 + j by omega, kp11 j hj, hv11 j hj,
      i0 _ by_omega c10 fr10]; omega
  · rw [kp12 j hj, hv12 j hj, i0 _ by_omega c11 fr11]
  · rw [hv13 j hj, i0 _ by_omega c12 fr12]

/-- A copy block of the stage B phases. -/
theorem copyBlockFP (hw : WordsBounded W c) {g : GV} (hG : GR g c) :
    ∃ c' k, Exec P W (block [.copyN 130520 130022, .copyN 130521 130021, .copyN 130522 130037,
      .copyN 130523 130014]) c c' k ∧ k = 4 ∧ WordsBounded W c' ∧ c'.nmem = c.nmem ∧
      c'.nreg 130520 = g.bR ∧ c'.nreg 130521 = g.bO ∧ c'.nreg 130522 = g.base 7 ∧
      c'.nreg 130523 = g.N ∧ (∀ r, ¬ (130520 ≤ r ∧ r ≤ 130523) → c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  exec_block
  zqzh
  · config_simp; exact hG.rR
  · config_simp; exact hG.rO
  · config_simp; exact hG.rbase 7 by_omega
  · config_simp; exact hG.rN
  · simp only; repeat (rw [Machine.upd_other _ _ _ (by omega)])
theorem fpP_exec {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hmap : MapArrays c.nmem g.bO g.bR g.bV g.μ g.N M)
    (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W fpP c c' k ∧ k ≤ 9 * g.N + 7 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.base 7 ≤ a ∧ a < g.base 7 + g.N) c c' ∧
      ∀ d : Fin g.N, c'.nmem zteff = M.fperm d := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7
  unfold fpP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hr1, hrr1, hrm1, ho1⟩ := copyBlockFP (P := P) hw hG
  have hone1 : ztpmk := by rw [hr1 _ by_omega]; exact hG.one
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := fpStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 by_omega
    by_omega by_omega (fun d hd => by
      rw [hm1, hmap.opp hd]; omega)
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', PFr.trans ⟨fun r hr => hr1 r (fun h => hr (by
    unfold StBRG; omega)), hrr1, hrm1, ho1, by_simp_all⟩
    (hf'.mono (fun r h => by unfold FpRG at h; unfold StBRG; omega) by_omega),
    fun d => ?_⟩
  rw [hv d d.2, hm1, hmap.opp d.2, hmap.rot (M.opp ⟨d, d.2⟩).2]
  rfl
theorem fpiP_exec {M : CombMap ztbry F ztbrx} {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hfp : ∀ d : Fin g.N, c.nmem zteff = M.fperm d)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W fpiP c c' k ∧ k ≤ 7 * g.N + 6 ∧ WordsBounded W c' ∧
      PFr StBRG zthxa c c' ∧
      ∀ d : Fin g.N, c'.nmem ztlph = (M.fperm⁻¹ d : Fin g.N) := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7; have b8 := g.base_eq 8
  unfold fpiP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, hone1, hr1⟩ : ∃ c1 k1, Exec P W
      zthsv c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130800 = g.base 7 ∧
      c1.nreg 130801 = g.base 8 ∧ c1.nreg 130802 = g.N ∧ c1.nreg 130001 = 1 ∧
      PFr StBRG zthxa c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ztrg⟩
    · config_simp; exact hG.rbase 7 by_omega
    · config_simp; exact hG.rbase 8 by_omega
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · zqzg
  have hfp1 : ∀ i (hi : i < g.N), c1.nmem (g.base 7 + i) = M.fperm ztoot := fun i hi => by
    grind
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := invStmt_exec (P := P) hw1 hone1 r0 r1 r2
    ztgjg
    (fun i j hi hj h => by
      rw [hfp1 i hi, hfp1 j hj] at h
      exact congrArg Fin.val (M.fperm.injective ztmay))
    by_omega by_omega by_omega by_omega
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold InvRG at h; unfold StBRG; omega) by_omega), fun d => ?_⟩
  have := hv ztfnz ztpys
  simp_all
theorem attP_exec {M : CombMap ztbry F ztbrx} {c : Config}
    (hw : WordsBounded W c) (hG : GR g c) (hfp : ∀ d : Fin g.N, c.nmem zteff = M.fperm d)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W attP c c' k ∧ k ≤ 40 * g.N + 15 ∧ WordsBounded W c' ∧
      PFr StBRG zthxb c c' ∧
      ∀ x, x < g.N → c'.nmem (g.base 9 + x) = minOrb (fun y => c.nmem (g.base 7 + y)) x := by
  have hU := g.U_ge; have hE := g.END_eq; have b7 := g.base_eq 7; have b9 := g.base_eq 9
  unfold attP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, hone1, hzero1, hr1⟩ : ∃ c1 k1, Exec P W
      zthsu c c1 k1 ∧
      k1 = 3 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130530 = g.base 7 ∧
      c1.nreg 130531 = g.base 9 ∧ c1.nreg 130532 = g.N ∧ c1.nreg 130001 = 1 ∧
      c1.nreg 130009 = 0 ∧ PFr StBRG zthxb c c1 := by
    exec_block
    refine ztxhz
    · config_simp; exact hG.rbase 7 by_omega
    · config_simp; exact hG.rbase 9 by_omega
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · config_simp; exact hG.zero
    · zqzg
  have hinj : InjOn (fun y => c.nmem _) g.N := fp_injOn by_omega
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := attStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 hinj
    (fun x hx => by zvmxz) by_omega by_omega by_omega by_omega
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold AttRG at h; unfold StBRG; omega) by_omega), hv⟩

/-- The tree darts from the parent darts in memory. -/
theorem teSet_iff
    {m : ℕ → ℕ} (hA : AF g M T m) (d : Fin g.N) :
    TeSet m ztvqz g.bO g.μ d ↔ T.IsTreeDart d := by
  have hr : ∀ v : Fin g.μ, v ≠ T.root ↔ 1 ≤ (v : ℕ) := by
    zujbq
    constructor
    · intro h; by_contra h0; exact h (Fin.ext (by rw [hA.root]; omega))
    · intro h e; have := congrArg Fin.val e; rw [hA.root] at this; omega
  have hopp : ∀ v : Fin g.μ, v ≠ T.root →
      (M.opp zteoj : ℕ) = m ztbvy := by
    zuml
    have h1 := hA.par_eq v hv
    have h2 := hA.map.opp (hA.par_lt v hv)
    have : T.par v = M.opp ⟨m _, hA.par_lt v hv⟩ := by_omega
    rw [this, M.opp_opp]
  constructor
  · rintro ⟨v, h1, h2, h3⟩
    have hv : (ztknc : Fin g.μ) ≠ T.root := by_simp_all
    refine ⟨ztknc, hv, ?_⟩
    zujh
    · grind
    · left; apply Fin.ext; rw [hA.par_eq _ hv]; exact h3
  · rintro ⟨v, hv, h3⟩
    refine ⟨v, by_simp_all, v.2, ?_⟩
    zujh
    · right; rw [h3, hA.par_eq v hv]
    simp_all
theorem teP_exec
    {c : Config} (hw : WordsBounded W c) (hG : GR g c) (hA : AF g M T c.nmem) (hμ : 0 < g.μ)
    (hO : g.bO + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W teP c c' k ∧ k ≤ 5 * g.N + 11 * g.μ + 15 ∧ WordsBounded W c' ∧
      PFr StBRG zthwx c c' ∧
      ∀ d : Fin g.N, (c'.nmem ztrqm = 1 ∧ T.IsTreeDart d) ∨
        (c'.nmem ztrqm = 0 ∧ ¬ T.IsTreeDart d) := by
  have hU := g.U_ge; have hE := g.END_eq; have b4 := g.base_eq 4; have b10 := g.base_eq 10
  unfold teP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, r4, hone1, hzero1, hr1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130540 130034, .copyN 130541 130021, .copyN 130542 130040,
        .copyN 130543 130011, .copyN 130544 130014]) c c1 k1 ∧
      k1 = 5 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ c1.nreg 130540 = g.base 4 ∧
      c1.nreg 130541 = g.bO ∧ c1.nreg 130542 = g.base 10 ∧ c1.nreg 130543 = g.μ ∧
      c1.nreg 130544 = g.N ∧ c1.nreg 130001 = 1 ∧
      c1.nreg 130009 = 0 ∧ PFr StBRG zthwx c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?_, rfl, rfl, rfl,
      by simp_all⟩⟩
    · config_simp; exact hG.rbase 4 by_omega
    · config_simp; exact hG.rO
    · config_simp; exact hG.rbase 10 by_omega
    · config_simp; exact hG.rμ
    · config_simp; exact hG.rN
    · config_simp; exact hG.one
    · config_simp; exact hG.zero
    · zqzg
  have hvr : ∀ v (_ : 1 ≤ v) (h2 : v < g.μ), (ztknc : Fin g.μ) ≠ T.root := by
    intro v h1 h2 e; have := congrArg Fin.val e; rw [hA.root] at this; simp_all
  obtain ⟨c', k, e, hk, hw', hf', hv⟩ := teStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3 r4 hμ
    by_omega by_omega by_omega by_omega by_omega (fun v h1 h2 => by
      zumno
      have hp : c.nmem ztbvy < g.N := hA.par_lt ztknc by_simp_all
      refine ⟨hp, by_omega, ?_⟩
      rw [hA.map.opp hp]; omega)
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw', hr1.trans (hf'.mono (fun r h => by
    unfold TeRG at h; unfold StBRG; omega) by_omega), fun d => ?_⟩
  zvmxz at hv
  rcases hv d d.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, (teSet_iff hA d).mp h2⟩
  · exact Or.inr ⟨h1, fun h => h2 ((teSet_iff hA d).mpr h)⟩

/-- **Stage B1.** -/
def stageB1 : Stmt := .seq fpP (.seq fpiP (.seq attP (.seq teP starP)))

/-- **The facts of stage B1.** -/
structure B1F (g : GV) {F : Type} [Fintype F] [DecidableEq F] (M : CombMap ztbry F ztbrx)
    (T : SpanTree M) (a : F → Fin g.N) (ha : ∀ f, M.face ztdbz = f) (m : ℕ → ℕ) : Prop where
  fp : ∀ d : Fin g.N, m zteff = M.fperm d
  fpi : ∀ d : Fin g.N, m ztlph = (M.fperm⁻¹ d : Fin g.N)
  att : ∀ d : Fin g.N, m ztlpi = a ztcci
  so : ∀ d : Fin g.N, m ztrqo = M.opp d ∧ m (g.base 11 + g.N + d) = 2 * g.N + d ∧
    m (g.base 11 + 2 * g.N + d) = g.N + d
  sr : ∀ d : Fin g.N, m (g.base 14 + d) = 2 * g.N + M.fperm d ∧ m (g.base 14 + g.N + d) = d ∧
    m (g.base 14 + 2 * g.N + d) = g.N + (M.fperm⁻¹ d : Fin g.N)
  sf : ∀ d : Fin g.N, m ztrqp = d ∧ m (g.base 17 + g.N + d) = d ∧
    m (g.base 17 + 2 * g.N + d) = (M.fperm⁻¹ d : Fin g.N)
  sfirst : ∀ d : Fin g.N, m (g.base 20 + d) = d
  sdb : ∀ x, (m (g.base 21 + enc g.N x) = 1 ↔ (starTree T a ha).IsTreeDart x)
theorem B1F.congr [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {m m' : ℕ → ℕ} (h : B1F g M T a ha m)
    (he : ∀ x, g.base 7 ≤ x → x < g.base 24 → m' x = m x) : B1F g M T a ha m' := by
  zueqs
  have b7 := g.base_eq 7; have b8 := g.base_eq 8; have b9 := g.base_eq 9; have b11 := g.base_eq 11
  have b14 := g.base_eq 14; have b17 := g.base_eq 17; have b20 := g.base_eq 20
  have b21 := g.base_eq 21; have b24 := g.base_eq 24
  refine ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun x => ?_⟩
  · have := d.2; zunbc; exact h.fp d
  · have := d.2; zunbc; exact h.fpi d
  · have := d.2; zunbc; exact h.att d
  · have := d.2
    rw [he _ by_omega by_omega, he _ by_omega by_omega,
      he _ by_omega by_omega]; exact h.so d
  · have := d.2
    rw [he _ by_omega by_omega, he _ by_omega by_omega,
      he _ by_omega by_omega]; exact h.sr d
  · have := d.2
    rw [he _ by_omega by_omega, he _ by_omega by_omega,
      he _ by_omega by_omega]; exact h.sf d
  · have := d.2; zunbc; exact h.sfirst d
  · have := enc_lt x; zunbc; exact h.sdb x
open Classical in
theorem stageB1_exec [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {c : Config} (hw : WordsBounded W c)
    (hG : GR g c) (hA : AF g M T c.nmem) (hμ : 0 < g.μ) (hO : g.bO + g.N ≤ g.A0)
    (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageB1 c c' k ∧ k ≤ 172 * g.N + 11 * g.μ + 150 ∧ WordsBounded W c' ∧
      PFr StBRG ztiso c c' ∧
      ∃ (a : F → Fin g.N) (ha : ∀ f, M.face ztdbz = f), B1F g M T a ha c'.nmem := by
  zuuv
  zqzk
  have b11 := g.base_eq 11; have b24 := g.base_eq 24
  have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6
  have hGR : ztfao := fun hf =>
    hG.frame ztyqt
  have hmono : ∀ {c0 c1 : Config} {Am : ℕ → Prop}, PFr StBRG Am c0 c1 →
      (∀ a, Am a → g.base 7 ≤ a ∧ a < g.base 24) →
      PFr StBRG ztiso c0 c1 :=
    fun hf hAm => hf.mono by_simp_all hAm
  -- FP
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hfp1⟩ := fpP_exec (P := P) hw hG hA.map hO hR hW
  have f1 := hmono hf1 by_grind
  -- FPI
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, hfpi2⟩ := fpiP_exec (P := P) hw1 ztvte hfp1 hW
  have f2 := f1.trans (hmono hf2 by_grind)
  have hfp2 : ∀ d : Fin g.N, c2.nmem zteff = M.fperm d := fun d => by
    zuede
  -- ATT
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hatt3⟩ := attP_exec (P := P) hw2 ztvtf hfp2 hW
  have f3 := f2.trans (hmono hf3 by_grind)
  -- the representatives
  set fpf : ℕ → ℕ := fun y => c2.nmem _ with hfpf
  have hinj : InjOn fpf g.N := fp_injOn by_omega
  obtain ⟨a, ha, hatt⟩ := att_fun (M := M) (att := fun d => c3.nmem ztlpi)
    (fun d => by
      show c3.nmem _ < g.N
      rw [hatt3 d d.2]; exact lt_of_le_of_lt (minOrb_le _) d.2)
    (fun d h => by
      have e1 : c3.nmem _ = minOrb fpf d := hatt3 d d.2
      have ho := minOrb_orb (f := fpf) (d : ℕ)
      obtain ⟨i, hi⟩ := ho
      have hm : minOrb fpf d < g.N := by_omega
      obtain ⟨j, hj, hij⟩ := exists_lt_per_of_iterate hinj hm i
      have := (face_orbit by_omega ⟨_, hm⟩ d).mpr
        ⟨j, hj, by_grind⟩
      grind)
    (fun d e h => by
      show c3.nmem _ = c3.nmem _
      rw [hatt3 d d.2, hatt3 e e.2]
      obtain ⟨i, -, hi⟩ := (face_orbit (M := M) (fp := fpf) (fun e => hfp2 e) d e).mp h.symm
      exact (minOrb_eq hinj d.2 ztoot).symm)
  -- TE
  have hA3 := hA.congr by_grind
    (fun a ha' => f3.2.2.2.2 a (by unfold KeepA at ha'; omega))
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hte4⟩ := teP_exec (P := P) hw3 ztvtg hA3 hμ hO hW
  have f4 := f3.trans (hmono hf4 by_grind)
  have hfp4 : ∀ d : Fin g.N, c4.nmem zteff = M.fperm d := fun d => by
    have := d.2
    zqzm
  have hfpi4 : ∀ d : Fin g.N, c4.nmem ztlph = (M.fperm⁻¹ d : Fin g.N) := fun d => by
    have := d.2
    zqzm
  have hatt4 : ∀ d : Fin g.N, c4.nmem ztlpi = a ztcci := fun d => by
    have := d.2
    rw [hf4.2.2.2.2 _ by_omega]; grind
  -- the star arrays
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, hst⟩ := starP_exec (P := P) hw4 ztvth
    (fun j hj => by rw [hfp4 ztuiw]; omega)
    (fun j hj => by rw [hfpi4 ztuiw]; omega) hO hW
  have f5 :=
    f4.trans (hf5.mono (fun r h => by unfold ArrPRG at h; unfold StBRG; omega) (fun a h => by
      omega))
  have m4 := fun a ha' => f4.2.2.2.2 a by_omega
  refine ⟨c5, k1 + ztvs, .seq x1 ztekb,
    by omega, hw5, f5, a, ha, ⟨fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_, fun d => ?_,
    fun d => ?_, fun d => ?_, fun x => ?_⟩⟩
  · have := d.2; zunnw; exact hfp4 d
  · have := d.2; zunnw; exact hfpi4 d
  · have := d.2; zunnw; exact hatt4 d
  · obtain ⟨h1, h2, h3, -⟩ := hst d d.2
    refine ztexl
    rw [h1, m4 _ by_omega]; exact hA.map.opp d.2
  · obtain ⟨-, -, -, h4, h5, h6, -⟩ := hst d d.2
    exact ⟨by rw [h4, hfp4 d], h5, by rw [h6, hfpi4 d]⟩
  · obtain ⟨-, -, -, -, -, -, h7, h8, h9, -⟩ := hst d d.2
    exact ⟨h7, h8, by rw [h9, hfpi4 d]⟩
  · exact (hst d d.2).2.2.2.2.2.2.2.2.2.1
  · zuim
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.1
      rw [show enc g.N _ = d from rfl, e, starTree_isTreeDart_inl]
      rcases hte4 d with ⟨t1, t2⟩ | ⟨t1, t2⟩
      · rw [t1]; exact ⟨fun _ => t2, by_omega⟩
      · rw [t1]
        constructor
        · simp
        · intro h; exact absurd h t2
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.2.1
      rw [show enc g.N _ = g.N + d from rfl,
        show g.base 21 + ztnzv = g.base 21 + g.N + d by omega, e, hatt4 d,
        starTree_isTreeDart_inl_inr]
      zqzl
      · zujkd
      · zuhmn
        omega
    · have e := (hst d d.2).2.2.2.2.2.2.2.2.2.2.2.2
      rw [show enc g.N _ = 2 * g.N + d from rfl,
        show g.base 21 + ztjfg = g.base 21 + 2 * g.N + d by omega, e, hatt4 d,
        starTree_isTreeDart_inr_inr]
      zqzl
      · zujkd
      · zuhmn
        omega
end proofs
end
end Chazelle.Core.Cluster
end
namespace Chazelle.Core.Cluster
open Machine Machine.Stmt Programs
open Chazelle.Separator Chazelle.Separator.CombMap
@[expose] public section
def dbfsP : Stmt := .seq (block [.copyN 130100 130041, .copyN 130101 130044,
  .copyN 130102 130047, .copyN 130103 130050, .copyN 130104 130051, .copyN 130105 130031,
  .copyN 130106 130054, .copyN 130107 130055, .copyN 130108 130056, .copyN 130109 130057,
  .copyN 130110 130014, .constN 130111 0, .constN 130112 0])
  (.seq bfsStmt (.instr (.storeN 130056 130009)))

/-- The preorder intervals. -/
def eulerP : Stmt := .seq (block [.copyN 130200 130057, .copyN 130201 130056,
  .copyN 130202 130047, .copyN 130203 130058, .copyN 130204 130059, .copyN 130205 130060,
  .copyN 130206 130014]) eulerStmt

/-- The dual parent array `PF`. -/
def pfP : Stmt := .seq (block [.copyN 130500 130047, .copyN 130501 130056, .copyN 130502 130061,
  .copyN 130503 130014]) parStmt

/-- The dual table `UP`. -/
def updP : Stmt := .seq (block [.copyN 130510 130061, .copyN 130511 130085, .copyN 130512 130014,
  .copyN 130513 130017]) upStmt

/-- **Stage B2.** -/
def stageB2 : Stmt := .seq (fillWith 130054 130014 130014) (.seq dbfsP (.seq eulerP
  (.seq pfP updP)))

/-- The layout of the dual search. -/
def dualLay (g : GV) : Lay := ⟨g.base 11, g.base 14, g.base 17, g.base 20, g.base 21, g.base 1,
  g.base 24, g.base 25, g.base 26, g.base 27, g.N, 3 * g.N⟩

/-- The tree of the dual search read from memory. -/
def dtree (g : GV) (m : ℕ → ℕ) : BTree :=
  ⟨g.N, fun i => m ztrqr, fun x => m (g.base 17 + m ztbdf)⟩
section proofs
variable {P : Polygon} {W : ℕ}
variable {g : GV} {c : Config}
theorem dualLay_good (hW : g.END ≤ W) : (dualLay g).Good W := by
  zuny

  have b1 := g.base_eq 1; have b11 := g.base_eq 11; have b14 := g.base_eq 14
  zubck

  have b27 := g.base_eq 27
  refine ztbij
  all_goals simp only [dualLay, Disj] at *
  · grind
  zuiqs
set_option maxHeartbeats 4000000 in
open Classical in
theorem dbfsP_exec {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hA : AF g M T c.nmem) (hB : B1F g M T a ha c.nmem) (hM : M.Connected) (hN : 0 < g.N)
    (hdl : ∀ x, x < g.N → c.nmem (g.base 24 + x) = g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W dbfsP c c' k ∧ k ≤ 220 * g.N + 30 ∧ WordsBounded W c' ∧
      PFr StBRG ztism c c' ∧
      ∃ C : CoTree ztqc, (C.r0 : ℕ) = 0 ∧
        (∀ x : Fin g.N, x ≠ C.r0 → c'.nmem ztbdf = enc g.N ztpwm) ∧
        (∀ x, x < g.N → c'.nmem ztbdf < 3 * g.N) ∧ (dtree g c'.nmem).OK ∧
        (dtree g c'.nmem).q 0 = 0 ∧ ∀ x : Fin g.N, (dtree g c'.nmem).up x = C.parent x := by
  zuny

  have b1 := g.base_eq 1; have b7 := g.base_eq 7; have b8 := g.base_eq 8
  have b11 := g.base_eq 11; have b14 := g.base_eq 14
  zubck

  have b27 := g.base_eq 27; have b28 := g.base_eq 28
  set Y := dualLay g with hY
  have hYg := dualLay_good hW
  unfold dbfsP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130100 130041,
      .copyN 130101 130044, .copyN 130102 130047, .copyN 130103 130050, .copyN 130104 130051,
      .copyN 130105 130031, .copyN 130106 130054, .copyN 130107 130055, .copyN 130108 130056,
      .copyN 130109 130057, .copyN 130110 130014, .constN 130111 0, .constN 130112 0]) c c1 k1 ∧
      k1 = 13 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ Regs Y 0 0 c1 ∧
      PFr StBRG ztism c c1 := by
    exec_block
    all_goals try omega
    refine ⟨rfl, by_omega, rfl, ztzv,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, by_simp_all⟩⟩
    case fr =>
      zubi
      zuhag
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    all_goals try (config_simp <;>
                   first
                   | exact hG.one
                   | exact hG.rN
                   | exact hG.rbase 1 by_omega
                   | exact hG.rbase 11 by_omega
                   | exact hG.rbase 14 by_omega
                   | exact hG.rbase 17 by_omega
                   | exact hG.rbase 20 by_omega
                   | exact hG.rbase 21 by_omega
                   | exact hG.rbase 24 by_omega
                   | exact hG.rbase 25 by_omega
                   | exact hG.rbase 26 by_omega
                   | exact hG.rbase 27 by_omega)
  -- the rotation system
  set G := Y.env c1.nmem with hGdef
  have hview : ∀ b n i, i < n → view c1.nmem b n i = c.nmem _ := fun b n i hi => by
    rw [view_lt hi, hm1]
  have hGenc : EnvEnc G (star M).dual (fun f => (f : ℕ)) (enc g.N) := by
    refine star_dual_enc (opp := fun x => c.nmem _)
      (fp := fun x => c.nmem _) (fpi := fun x => c.nmem _)
      (fun d => (hB.so d).1) hB.fp hB.fpi rfl rfl ztbzy ztbzy
      ztbzy ztbzy
    · obtain ⟨h1, h2, h3⟩ := hB.so ztpw
      refine ⟨hview _ ztckv d by_omega, ?_, ?_⟩
      · show view c1.nmem ztvqx ztckv _ = _
        grind
      · show view c1.nmem ztvqx ztckv _ = _
        grind
    · obtain ⟨h1, h2, h3⟩ := hB.sr ztpw
      zusk
      · show view c1.nmem ztqom ztckv d = _
        rw [hview _ _ _ by_omega, h1, ← hB.fp ztpw]
      · show view c1.nmem ztqom ztckv _ = _
        grind
      · show view c1.nmem ztqom ztckv _ = _
        zudkc
    · obtain ⟨h1, h2, h3⟩ := hB.sf ztpw
      zusk
      · show view c1.nmem ztmke ztckv d = _
        grind
      · show view c1.nmem ztmke ztckv _ = _
        grind
      · show view c1.nmem ztmke ztckv _ = _
        zudkc
    · show view c1.nmem _ g.N d = d
      rw [hview _ _ _ hd]; exact hB.sfirst ztpw
  have hok := hGenc.ok
  have hpre : G.Pre 0 0 ztocr := by
    refine ⟨hok, hN, ?_, hN, fun w hw' _ => ?_⟩
    · show view c1.nmem zteac g.N 0 ≠ 1
      rw [hview _ _ _ hN, hA.zero 0 hN]; omega
    · show view c1.nmem _ g.N w = g.N
      rw [hview _ _ _ (show w < g.N from hw')]; exact hdl w hw'
  obtain ⟨c2, k2, e2, hk2, ⟨hw2, hfr2, hI⟩, hht⟩ := bfs_exec (P := P) hYg hR1 hpre hw1
  zukuh
  have hdb : ∀ x, G.db (enc g.N x) = 1 ↔ (starTree T a ha).IsTreeDart x := by
    zugop
    show view c1.nmem (g.base 21) ztckv _ = 1 ↔ _
    rw [hview _ _ _ (enc_lt x)]; exact hB.sdb x
  have hvb : ∀ f, f < g.N → G.vb f ≠ 1 := by
    zuhgh
    show view c1.nmem zteac g.N f ≠ 1
    rw [hview _ _ _ hf, hA.zero f hf]; omega
  obtain ⟨ht, C, hr0, hpar, hROK, hRup⟩ := dual_cotree (T := T) (ha := ha) hM hN rfl rfl hGenc
    hdb hvb hI
  -- the store `FPAR[0] := 0`
  have r56 : c2.nreg 130056 = g.base 26 := by
    zunrm
    exact hG.rbase 26 by_omega
  have r09 : c2.nreg 130009 = 0 := by
    zunrm; exact hG.zero
  have e3 := Exec.storeN (P := P) hw2 130056 130009
  set c3 := { c2 with nmem := upd c2.nmem _ _ } with hc3
  have hm3 : ∀ x, c3.nmem x = if x = g.base 26 then 0 else c2.nmem x := by
    intro x; simp only [c3, Machine.upd_apply, r56, r09]
  have hkeep2 : ∀ x, ¬ Y.Written x → c2.nmem x = c.nmem x := fun x hx => by
    rw [hfr2.2.2.2.2 x hx, hm1]
  have hq : ∀ i, i < g.N → c3.nmem ztrqr = qV Y c2.nmem i := by
    zug
    zuexy
    show _ = view c2.nmem (g.base 27) g.N i
    rw [view_lt hi]
  have hq0 := hI.q0
  have hpv : ∀ x, x < g.N → parV Y c2.nmem x = c2.nmem _ := fun x hx => by
    show view c2.nmem (g.base 26) g.N x = _; zuoqw
  have hr0' : ∀ x : Fin g.N, x ≠ C.r0 ↔ (x : ℕ) ≠ 0 := by
    omega
  have hpar' : ∀ x, x < g.N → x ≠ 0 → c2.nmem ztbdf < 3 * g.N ∧
      ∃ h : x < g.N, enc g.N (C.fpar zthnu) = c2.nmem ztbdf := by
    grind
  set R0 : BTree := ⟨g.N, qV Y c2.nmem, fun x => G.vert (parV Y c2.nmem x)⟩ with hR0
  have hRq := hq
  have hRp : ∀ x, x < R0.n → x ≠ R0.q 0 → (dtree g c3.nmem).par x = R0.par x := by
    intro x hx hx0
    have hx0' : x ≠ 0 := by_grind
    obtain ⟨hlt, -⟩ := hpar' x hx hx0'
    show c3.nmem _ = G.vert _
    rw [hm3 ztbdf, ite_eq_right by_omega, hm3, ite_eq_right by_omega, hpv x hx]
    show _ = view c1.nmem ztmke ztckv _
    rw [hview _ _ _ hlt, hkeep2 _ (by unfold Lay.Written; simp only [hY, dualLay]; omega)]
  refine ⟨c3, k1 + ztcvw, .seq e1 ztbpc, ?_, e3.wb_right, ?_, C, hr0, fun x hx => ?_,
    fun x hx => ?_, hROK.congr rfl hRq hRp, ?_, fun x => ?_⟩
  · zugnd

    have hGN3 : G.N = 3 * g.N := rfl
    have hGnv : G.nv = g.N := rfl
    rw [hGN3] at hsum
    zuksl
    omega
  · refine hf1.trans ⟨fun r hr => hfr2.1 r (fun h => hr (by unfold Scr at h; unfold StBRG; omega)),
      hfr2.2.1, hfr2.2.2.1, hfr2.2.2.2.1, fun a ha' => ?_⟩
    zuexy
    exact hfr2.2.2.2.2 a (fun h => ha' (by
      unfold Lay.Written at h; simp only [hY, dualLay] at h; omega))
  · have h0 := (hr0' x).mp hx
    obtain ⟨-, hx', he⟩ := hpar' x x.2 h0
    zuexy
    exact he.symm
  · by_cases h0 : x = 0
    · subst h0; rw [hm3, ite_eq_left by_omega]; omega
    · rw [hm3, ite_eq_right by_omega]; exact (hpar' x hx h0).1
  · show c3.nmem _ = 0
    rw [hq 0 hN]; omega
  · have hq0' := hq 0 hN
    rw [BTree.up_congr hq0' hRp x.2]
    exact hRup x

/-- The layout of the preorder intervals. -/
def eulerLay (g : GV) : ELay := ⟨g.base 27, g.base 26, g.base 17, g.base 28, g.base 29,
  g.base 30, g.N⟩
set_option maxHeartbeats 4000000 in
theorem eulerP_exec (hw : WordsBounded W c) (hG : GR g c)
    (hR : (dtree g c.nmem).OK) (hlt : ∀ x, x < g.N → c.nmem ztbdf < 3 * g.N)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W eulerP c c' k ∧ k ≤ 45 * g.N + 27 ∧ WordsBounded W c' ∧
      PFr StBRG ztisn c c' ∧
      (∀ x, x < g.N → c'.nmem ztfsa = ((dtree g c.nmem).sub x).card) ∧
      (dtree g c.nmem).PreInv (view c'.nmem ztqon g.N) (view c'.nmem ztvqy g.N)
        g.N := by
  zuny

  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b26 := g.base_eq 26
  have b27 := g.base_eq 27; have b28 := g.base_eq 28; have b29 := g.base_eq 29
  have b30 := g.base_eq 30; have b31 := g.base_eq 31
  set L := eulerLay g with hL
  unfold eulerP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, hR1, hf1⟩ : ∃ c1 k1, Exec P W (block [.copyN 130200 130057,
      .copyN 130201 130056, .copyN 130202 130047, .copyN 130203 130058, .copyN 130204 130059,
      .copyN 130205 130060, .copyN 130206 130014]) c c1 k1 ∧
      k1 = 7 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧ L.Regs c1 ∧
      PFr StBRG ztisn c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ztdiu,
      ⟨fun r hr => ?fr, rfl, rfl, rfl, by_simp_all⟩⟩
    case fr =>
      zubi
      zuhag
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rN
                   | exact hG.rbase 17 by_omega
                   | exact hG.rbase 26 by_omega
                   | exact hG.rbase 27 by_omega
                   | exact hG.rbase 28 by_omega
                   | exact hG.rbase 29 by_omega
                   | exact hG.rbase 30 by_omega)
  have hLG : L.Good c1.nmem W := by
    zumno
    refine ⟨?_, ?_, ?_, fun i hi => ?_, fun x hx _ => ?_, fun x hx _ => ?_, ?_, ?_, ?_, ?_, ?_,
      ?_⟩
    all_goals simp only [hL, eulerLay, Disj, ELay.WR] at *
    zubqj
    grind
  obtain ⟨c', k, e, hk, hw', hf', hsz, hpre⟩ := eulerStmt_exec (P := P) hLG hR1
    (by zvmxz; exact hR) hw1
  zvmxz at hsz hpre
  refine ⟨c', k1 + k, .seq e1 e, by simp only [hL, eulerLay] at hk; omega, hw', hf1.trans
    (hf'.mono (fun r h => by unfold ERG at h; unfold StBRG; omega) (fun a h => by
      simp only [hL, eulerLay, ELay.WR] at h; omega)), hsz, hpre⟩
theorem pfP_exec (hw : WordsBounded W c) (hG : GR g c) (hN : 0 < g.N)
    (hlt : ∀ x, x < g.N → c.nmem ztbdf < 3 * g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W pfP c c' k ∧ k ≤ 9 * g.N + 8 ∧ WordsBounded W c' ∧
      PFr StBRG zthwy c c' ∧ c'.nmem (g.base 31) = 0 ∧
      ∀ x, 1 ≤ x → x < g.N →
        c'.nmem ztrqt = c.nmem (g.base 17 + c.nmem ztbdf) := by
  zuny

  have b17 := g.base_eq 17; have b26 := g.base_eq 26; have b31 := g.base_eq 31
  unfold pfP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hzero1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130500 130047, .copyN 130501 130056, .copyN 130502 130061,
        .copyN 130503 130014]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130500 = g.base 17 ∧ c1.nreg 130501 = g.base 26 ∧ c1.nreg 130502 = g.base 31 ∧
      c1.nreg 130503 = g.N ∧ c1.nreg 130001 = 1 ∧ c1.nreg 130009 = 0 ∧
      PFr StBRG zthwy c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?fr, rfl, rfl, rfl,
      by simp_all⟩⟩
    case fr =>
      zubi
      zuhag
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.zero
                   | exact hG.rN
                   | exact hG.rbase 17 by_omega
                   | exact hG.rbase 26 by_omega
                   | exact hG.rbase 31 by_omega)
  obtain ⟨c', k, e, hk, hw', hf', h0, hx⟩ := parStmt_exec (P := P) hw1 hone1 hzero1 r0 r1 r2 r3
    hN by_omega by_omega by_omega (fun x h1 h2 => by
      grind)
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold ParRG at h; unfold StBRG; omega) by_omega),
    by omega, by_simp_all⟩
theorem updP_exec (hw : WordsBounded W c) (hG : GR g c) (hN : 0 < g.N)
    (hL : 0 < g.L) (hpf : ∀ x, x < g.N → c.nmem ztrqt < g.N) (hW : g.END ≤ W) :
    ∃ c' k, Exec P W updP c c' k ∧ k ≤ 12 * g.N * g.L + 7 * g.L + 16 ∧ WordsBounded W c' ∧
      PFr StBRG (fun a => g.A0 + 54 * g.U + g.L * g.U ≤ a ∧
        a < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) c c' ∧
      ∀ j, j < g.L → ∀ x, x < g.N → c'.nmem ztdhj =
        (fun y => c.nmem ztrqu)^[2 ^ j] x := by
  zuny

  have b31 := g.base_eq 31
  zuiwk
  zudyj
  unfold updP
  obtain ⟨c1, k1, e1, hk1, hw1, hm1, r0, r1, r2, r3, hone1, hf1⟩ : ∃ c1 k1, Exec P W
      (block [.copyN 130510 130061, .copyN 130511 130085, .copyN 130512 130014,
        .copyN 130513 130017]) c c1 k1 ∧ k1 = 4 ∧ WordsBounded W c1 ∧ c1.nmem = c.nmem ∧
      c1.nreg 130510 = g.base 31 ∧ c1.nreg 130511 = g.A0 + 54 * g.U + g.L * g.U ∧
      c1.nreg 130512 = g.N ∧ c1.nreg 130513 = g.L ∧ c1.nreg 130001 = 1 ∧
      PFr StBRG (fun a => g.A0 + 54 * g.U + g.L * g.U ≤ a ∧
        a < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) c c1 := by
    exec_block
    refine ⟨rfl, by_omega, rfl, ?_, ?_, ?_, ?_, ?_, ⟨fun r hr => ?fr, rfl, rfl, rfl,
      by simp_all⟩⟩
    case fr =>
      zubi
      zuhag
      repeat (rw [Machine.upd_other _ _ _ by_omega])
    all_goals try (config_simp;
                   first
                   | exact hG.one
                   | exact hG.rL
                   | exact hG.rN
                   | exact hG.rUP
                   | exact hG.rbase 31 by_omega)
  obtain ⟨c', k, e, hk, hw', hf', htab⟩ := upStmt_exec (P := P) hw1 hone1 r0 r1 r2 r3 hL
    ztqoj by_omega by_omega by_omega by_omega hN
  refine ⟨c', k1 + k, .seq e1 e, by_omega, hw',
    hf1.trans (hf'.mono (fun r h => by unfold UpRG at h; unfold StBRG; omega) by_omega),
    by simp_all⟩
structure B2F (g : GV) {F : Type} [Fintype F] [DecidableEq F] {M : CombMap ztbry F ztbrx}
    {T : SpanTree M} {a : F → Fin g.N} {ha : ∀ f, M.face ztdbz = f}
    (C : CoTree ztqc) (R : BTree) (preE slot : ℕ → ℕ) (m : ℕ → ℕ) : Prop where
  fpar : ∀ x : Fin g.N, x ≠ C.r0 → m ztbdf = enc g.N ztpwm
  fpar_lt : ∀ x, x < g.N → m ztbdf < 3 * g.N
  r0 : (C.r0 : ℕ) = 0
  pre : ∀ x, x < g.N → m zthxk = preE x
  sz : ∀ x, x < g.N → m ztfsa = (R.sub x).card
  R_ok : R.OK
  R_n : R.n = g.N
  R_up : ∀ x : Fin g.N, R.up x = C.parent x
  R_root : R.root = 0
  R_pre : R.PreInv preE slot R.n
  up_tab : ∀ j, j < g.L → ∀ x, x < g.N →
    m ztdhj = R.up^[2 ^ j] x
set_option maxHeartbeats 4000000 in
open Classical in
theorem stageB2_exec {g : GV} {F : Type} [Fintype F] [DecidableEq F]
    {M : CombMap ztbry F ztbrx} {T : SpanTree M} {a : F → Fin g.N}
    {ha : ∀ f, M.face ztdbz = f} {c : Config} (hw : WordsBounded W c) (hG : GR g c)
    (hA : AF g M T c.nmem) (hB : B1F g M T a ha c.nmem) (hM : M.Connected) (hN : 0 < g.N)
    (hL : 0 < g.L) (hO : g.bO + g.N ≤ g.A0) (hR : g.bR + g.N ≤ g.A0) (hV : g.bV + g.N ≤ g.A0)
    (hW : g.END ≤ W) :
    ∃ c' k, Exec P W stageB2 c c' k ∧ k ≤ 280 * g.N + 12 * g.N * g.L + 7 * g.L + 120 ∧
      WordsBounded W c' ∧ PFr StBRG (fun a => g.base 24 ≤ a ∧ a < g.base 32 ∨
        g.A0 + 54 * g.U + g.L * g.U ≤ a ∧ a < g.A0 + 54 * g.U + 2 * ztesx) c c' ∧
      ∃ (C : CoTree ztqc) (R : BTree) (preE slot : ℕ → ℕ),
        B2F g C R preE slot c'.nmem := by
  zuny

  zuiwk
  zudyj
  have b17 := g.base_eq 17; have b20 := g.base_eq 20; have b24 := g.base_eq 24
  have b26 := g.base_eq 26; have b27 := g.base_eq 27; have b28 := g.base_eq 28
  have b29 := g.base_eq 29; have b30 := g.base_eq 30; have b31 := g.base_eq 31
  have b32 := g.base_eq 32
  have hGR : ztfao := fun hf =>
    hG.frame ztyqt
  set Wr : ℕ → Prop := fun a => g.base 24 ≤ a ∧ a < g.base 32 ∨
    g.A0 + 54 * g.U + g.L * g.U ≤ a ∧ a < g.A0 + 54 * g.U + 2 * ztesx with hWr
  unfold stageB2
  -- `DLAB := N`
  obtain ⟨c1, k1, x1, hk1, hw1, hf1, hl1⟩ := fillWith_exec (P := P) hw hG.one
    (hG.rbase 24 by_omega) hG.rN hG.rN ztpc ztpc
    ztpc by_omega by_omega
  have f1 : PFr StBRG Wr c c1 := hf1.mono (fun r h => by unfold FillRG at h; unfold StBRG; omega)
    (fun a h => by_grind)
  have b3 := g.base_eq 3; have b5 := g.base_eq 5; have b6 := g.base_eq 6; have b7 := g.base_eq 7
  have hA1 : AF g M T c1.nmem := hA.congr zteyj
    (fun x hx => hf1.2.2.2.2 x (by unfold KeepA at hx; omega))
  have hB1 : B1F g M T a ha c1.nmem := hB.congr (fun x h1 h2 => hf1.2.2.2.2 x by_omega)
  -- the dual search
  obtain ⟨c2, k2, x2, hk2, hw2, hf2, C, hr0, hfpar2, hlt2, hROK, hq0, hRup⟩ :=
    dbfsP_exec (P := P) hw1 ztvte hA1 hB1 hM hN hl1 hW
  have f2 : PFr StBRG Wr c c2 := f1.trans (hf2.mono ztng (fun a h => by
    grind))
  -- the preorder intervals
  obtain ⟨c3, k3, x3, hk3, hw3, hf3, hsz3, hpre3⟩ := eulerP_exec (P := P) hw2 ztvtf hROK hlt2 hW
  have f3 : PFr StBRG Wr c c3 := f2.trans (hf3.mono ztng (fun a h => by
    zuoqx; omega))
  have hlt3 : ∀ x, x < g.N → c3.nmem ztbdf < 3 * g.N := fun x hx => by
    zubbh
  -- the dual parent array
  obtain ⟨c4, k4, x4, hk4, hw4, hf4, hp0, hp4⟩ := pfP_exec (P := P) hw3 ztvtg hN hlt3 hW
  have f4 : PFr StBRG Wr c c4 := f3.trans (hf4.mono ztng (fun a h => by
    zuoqx; omega))
  set R := dtree g c2.nmem with hRdef
  have hRn : R.n = g.N := rfl
  have hRroot : R.root = 0 := hq0
  have hupN : ∀ y, y < g.N → R.up y < g.N := fun y hy => by
    rw [hRup zthnw]; omega
  have hpf : ∀ y, y < g.N → c4.nmem ztrqu = R.up y := by
    zusy
    by_cases h0 : y = 0
    · zubvi
      zvnhg; rw [hp0]
      unfold BTree.up; grind
    · rw [hp4 y by_omega hy]
      unfold BTree.up
      zufa
      show _ = c2.nmem (g.base 17 + c2.nmem ztrqq)
      have := hlt2 y hy
      rw [hf3.2.2.2.2 ztrqq by_omega, hf3.2.2.2.2 _ by_omega]
  -- the dual table
  obtain ⟨c5, k5, x5, hk5, hw5, hf5, htab⟩ := updP_exec (P := P) hw4 ztvth hN hL
    ztqol hW
  have f5 : PFr StBRG Wr c c5 := f4.trans (hf5.mono ztng (fun a h => by
    grind))
  refine ⟨c5, k1 + ztvs, .seq x1 ztekb, ?_,
    hw5, f5, C, R, view c3.nmem ztqon g.N, view c3.nmem ztvqy g.N, ?_⟩
  · grind
  · have e5 := hf5.2.2.2.2
    have e4 := hf4.2.2.2.2
    have e3 := hf3.2.2.2.2
    clear f1 f2 f3 f4 f5 hf1 hf2 hf3 hf4 hf5
    have k29 : ∀ x, x < g.N → c5.nmem zthxk = c3.nmem zthxk := by
      zuh
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 29 + x ∧
          g.base 29 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        grind
      have h2 : ¬ (g.base 31 ≤ g.base 29 + x ∧ g.base 29 + x < g.base 31 + g.N) := by
        grind
      zuhty
    have k28 : ∀ x, x < g.N → c5.nmem ztfsa = c3.nmem ztfsa := by
      zuh
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 28 + x ∧
          g.base 28 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        grind
      have h2 : ¬ (g.base 31 ≤ g.base 28 + x ∧ g.base 28 + x < g.base 31 + g.N) := by
        grind
      zuhty
    have k26 : ∀ x, x < g.N → c5.nmem ztbdf = c2.nmem ztbdf := by
      zuh
      have h1 : ¬ (g.A0 + 54 * g.U + g.L * g.U ≤ g.base 26 + x ∧
          g.base 26 + x < g.A0 + 54 * g.U + g.L * g.U + g.L * g.N) := by
        grind
      have h2 : ¬ (g.base 31 ≤ g.base 26 + x ∧ g.base 26 + x < g.base 31 + g.N) := by
        grind
      have h3 : ¬ (g.base 28 ≤ g.base 26 + x ∧ g.base 26 + x < g.base 31) := by
        grind
      exact (e5 _ h1).trans ((e4 _ h2).trans (e3 _ h3))
    have hpreF : ∀ x, x < g.N → c5.nmem zthxk = view c3.nmem ztqon g.N x := by
      zuh
      zuoqw; exact k29 x hx
    have hfparF : ∀ x : Fin g.N, x ≠ C.r0 → c5.nmem ztbdf = enc g.N ztpwm := by
      zuh
      rw [k26 x x.2]; exact hfpar2 x hx
    have hltF : ∀ x, x < g.N → c5.nmem ztbdf < 3 * g.N := by
      zuh
      rw [k26 x hx]; exact hlt2 x hx
    have hszF : ∀ x, x < g.N → c5.nmem ztfsa = (R.sub x).card := by
      zuh
      rw [k28 x hx]; exact hsz3 x hx
    have htabF : ∀ j, j < g.L → ∀ x, x < g.N →
        c5.nmem ztdhj = R.up^[2 ^ j] x := by
      intro j hj x hx
      rw [htab j hj x hx]
      exact (iterate_congr_lt (n := g.N) hpf hupN ztssr x hx).1
    clear * - hfparF hltF hr0 hpreF hszF hROK hRn hRup hRroot hpre3 htabF
    exact ⟨hfparF, hltF, hr0, hpreF, hszF, hROK, hRn, hRup, hRroot, hpre3, htabF⟩
