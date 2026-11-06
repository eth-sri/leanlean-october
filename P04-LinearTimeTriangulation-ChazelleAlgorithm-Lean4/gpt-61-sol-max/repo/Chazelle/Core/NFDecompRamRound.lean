module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFDecompRamRP

/-!
# Tree decomposition (WP-C), part 19: one round on the RAM realises `next`

* `round_mem`: the memory after the four passes of a round holds `next` of the memory before it
  (read through `rsOf`), with `top`, `best` the fields written by the top pass.
-/

namespace Chazelle.Core.DecR

open Machine Machine.Stmt Programs Chazelle.Core.Dec

@[expose] public section

section nowr

/-- The numeric register written by an instruction, if any. -/
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

/-- An instruction not writing the numeric register `x` keeps it. -/
theorem nreg_effect {x : ℕ} {ins : Instr} {c c' : Config} (he : ins.effect P c = some c')
    (hx : ndst ins ≠ some x) : c'.nreg x = c.nreg x := by
  cases ins <;> simp only [ndst, ne_eq, Option.some.injEq] at hx <;> simp [Instr.effect] at he
  all_goals first
    | (subst he; rfl)
    | (subst he; exact Machine.upd_other _ _ _ (Ne.symm hx))
    | (obtain ⟨-, rfl⟩ := he; rfl)

/-- A register a statement never writes keeps its value. -/
theorem nreg_of_noWr {x : ℕ} {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k)
    (hs : NoWr x s = true) : c'.nreg x = c.nreg x := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ =>
    exact nreg_effect he (by core_grind)
  | seq _ _ ih1 ih2 =>
    simp_all [NoWr, Bool.and_eq_true]
  | ifLtN_true _ _ ih => simp_all [NoWr, Bool.and_eq_true]
  | ifLtN_false _ _ ih => simp_all [NoWr, Bool.and_eq_true]
  | ifLtR_true _ _ ih => simp_all [NoWr, Bool.and_eq_true]
  | ifLtR_false _ _ ih => simp_all [NoWr, Bool.and_eq_true]
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih1 ih2 => aesop
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih1 ih2 => aesop

/-- The round counters are written only where intended. -/
theorem noWr_passes : NoWr 60022 p1S = true ∧ NoWr 60023 p1S = true ∧ NoWr 60024 p1S = true ∧
    NoWr 60022 p2S = true ∧ NoWr 60023 p2S = true ∧ NoWr 60024 p2S = true ∧
    NoWr 60022 cpS = true ∧ NoWr 60023 cpS = true ∧ NoWr 60024 cpS = true ∧
    NoWr 60022 rootS = true ∧ NoWr 60023 rootS = true ∧
    NoWr 60022 rpS = true ∧ NoWr 60024 rpS = true := by decide

end nowr


section facts

variable {R K D : ℕ} {up dn ord pos prg pch isdn chOf : ℕ → ℕ} {σ : RS} {top best bestv : ℕ → ℕ}
variable {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}

/-- The facts on the top pass the chord and region passes rely on. -/
theorem round_facts (h : Rooted R K up dn ord pos prg pch)
    (hch : ∀ e, e < K → chOf e < R ∧ chOf e ≠ 0 ∧ pch (chOf e) = e)
    (hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u)
    (hB : ∀ t, t < R → IsTop pch σ.rem t →
      (∀ c, c < R → AncX R prg pch σ.rem t c → c ≠ t → cval R prg pch σ.rem t c ≤ bestv t) ∧
      ((best t = t ∧ ∀ c, c < R → AncX R prg pch σ.rem t c → c = t) ∨
        (best t < R ∧ AncX R prg pch σ.rem t (best t) ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t (best t))))
    (hI : RInv R K D prg pch isdn chOf j σ gc cr) :
    (∀ u, u < R → top (top u) = top u) ∧
    (∀ x, x < R → top x = x → best x < R ∧ (best x ≠ x → pch (best x) < R)) ∧
    (∀ t, t < R → top t = t → σ.act t = 1 → σ.side t ≠ 2 → σ.cpar t < R) ∧
    (∀ e, e < K → σ.pend e = 1 → top (chOf e) = chOf e) ∧
    (∀ r, r < R → top r ≠ r → pch r < R) ∧ top 0 = 0 := by
  have hKR : K < R := by have := h.hR; omega
  have hR0 : 0 < R := by omega
  have top0 : top 0 = 0 := top_self h hch hT hB hI hR0 (Or.inl rfl)
  refine ⟨fun u hu => top_self h hch hT hB hI (hT u hu).1 (hT u hu).2.1, fun x hx htx => ?_,
    fun t ht htt ha hs => ?_, fun e he hp => ?_, fun r hr htr => ?_, top0⟩
  · have htop := (top_iff h hch hT hB hI hx).1 htx
    rcases (hB x hx htop).2 with ⟨b1, -⟩ | ⟨b1, b2, b3, -⟩
    · omega
    · refine ⟨b1, fun _ => ?_⟩
      have hnt : ¬ IsTop pch σ.rem (best x) := AncX.not_top b2 (Ne.symm b3)
      have hb0 : best x ≠ 0 := fun h0 => hnt (Or.inl h0)
      have := h.pch_lt _ b1 hb0
      omega
  · have htop := (top_iff h hch hT hB hI ht).1 htt
    rcases hI.i4 t ht htop ha with ⟨h2, -⟩ | ⟨-, h2, -⟩
    all_goals omega
  · have hr := hI.i0 e he hp
    obtain ⟨c1, -, c3⟩ := hch e he
    exact top_self h hch hT hB hI c1 (Or.inr (by grind))
  · have hr0 : r ≠ 0 := fun h0 => htr (by grind)
    have := h.pch_lt r hr hr0
    omega

end facts

section roundmem

variable {A R K : ℕ}

/-- The chord-pass and region-pass fields are disjoint. -/
theorem cpf_not_rpf {f : ℕ} (h : CPF f) : ¬ RPF f := by omega_nf

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
      code (tv m2 A R 9) (tv m2 A R 4) 0 else root) else root)
    (hfin : fin' = fin + ((Finset.range R).filter (fun r => SingAt m3 A R r)).card) :
    rsOf m4 A R root' fin' = next R K (tv m0 A R 3) (tv m0 A R 4) (tv m0 A R 5) (tv m0 A R 6)
      (tv m2 A R 8) (tv m2 A R 9) (rsOf m0 A R root fin) := by
  have t02 : ∀ f, f < 19 → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → tv m2 A R f = tv m0 A R f :=
    fun f hf h7 h8 h9 h10 => tv_congr (fun u hu => h02 f u hf h7 h8 h9 h10 hu)
  have hnxt : nxt m2 A R K = next R K (tv m0 A R 3) (tv m0 A R 4) (tv m0 A R 5) (tv m0 A R 6)
      (tv m2 A R 8) (tv m2 A R 9) (rsOf m0 A R 0 0) := by
    grind [nxt, rsOf]
  set N := next R K (tv m0 A R 3) (tv m0 A R 4) (tv m0 A R 5) (tv m0 A R 6)
      (tv m2 A R 8) (tv m2 A R 9) (rsOf m0 A R root fin) with hN
  -- the chord fields
  have chord : ∀ f, CPF f → ∀ F : ℕ → ℕ, (∀ e, e < K → cpv m2 A R K f e = F e) →
      (∀ e, K ≤ e → F e = tv m0 A R f e) → tv m4 A R f = F := by
    intro f hc F hF1 hF2
    have hf : f < 19 := by unfold CPF at hc; omega
    funext e
    unfold tv
    by_cases he : e < R
    · rw [ite_eq_left he, h34 f e hf he, ite_eq_right (cpf_not_rpf hc), h23 f e hf he]
      by_cases heK : e < K
      · grind
      · rw [ite_eq_right (fun hh => heK hh.1), hF2 e (by omega), tv_lt he,
          h02 f e hf (by unfold CPF at hc; omega) (by unfold CPF at hc; omega)
            (by unfold CPF at hc; omega) (by unfold CPF at hc; omega) he]
    core_grind
  -- the facts read by the region pass
  have r2 : ∀ f x, f < 19 → ¬ CPF f → x < R → fv m3 A R f x = fv m2 A R f x :=
    fun f x hf hc hx => by grind
  have r0 : ∀ f x, f < 19 → ¬ CPF f → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → x < R →
      fv m3 A R f x = tv m0 A R f x :=
    fun f x hf hc h7 h8 h9 h10 hx => by rw [r2 f x hf hc hx, h02 f x hf h7 h8 h9 h10 hx, tv_lt hx]
  have a8 : ∀ x, x < R → fv m3 A R 8 x = tv m2 A R 8 x := fun x hx => by
    rw [r2 8 x (by norm_num) (by omega_nf) hx, tv_lt hx]
  have a9 : ∀ x, x < R → fv m3 A R 9 x = tv m2 A R 9 x := fun x hx => by
    rw [r2 9 x (by norm_num) (by omega_nf) hx, tv_lt hx]
  have a4 : ∀ x, x < R → fv m3 A R 4 x = tv m0 A R 4 x := fun x hx =>
    r0 4 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a5 : ∀ x, x < R → fv m3 A R 5 x = tv m0 A R 5 x := fun x hx =>
    r0 5 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a13 : ∀ x, x < R → fv m3 A R 13 x = tv m0 A R 13 x := fun x hx =>
    r0 13 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a14 : ∀ x, x < R → fv m3 A R 14 x = tv m0 A R 14 x := fun x hx =>
    r0 14 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a15 : ∀ x, x < R → fv m3 A R 15 x = tv m0 A R 15 x := fun x hx =>
    r0 15 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a0 : ∀ x, x < R → fv m3 A R 0 x = tv m0 A R 0 x := fun x hx =>
    r0 0 x (by norm_num) (by omega_nf) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hx
  have a12 : ∀ e, e < R → fv m3 A R 12 e = N.pend e := fun e he => by
    rw [h23 12 e (by norm_num) he]
    by_cases heK : e < K
    · rw [ite_eq_left ⟨heK, by omega_nf⟩]
      unfold cpv; rw [hnxt]; rfl
    · rw [ite_eq_right (fun hh => heK hh.1), h02 12 e (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) he, hN]
      simp only [next, nPend, ite_eq_right heK, rsOf, tv_lt he]
  have hb' : ∀ r, r < R → tv m2 A R 8 r = r → tv m0 A R 13 r = 1 → tv m2 A R 9 r < R :=
    fun r hr h8 h13 => by
      rw [tv_lt hr] at h8 ⊢
      rw [tv_lt hr, ← h02 13 r (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) hr] at h13
      grind
  have hp' : ∀ r, r < R → tv m2 A R 8 r ≠ r → tv m0 A R 4 r < R := fun r hr h8 => by
    rw [tv_lt hr] at h8 ⊢
    grind
  -- the region fields
  have region : ∀ f, RPF f → f ≠ 7 → ∀ F : ℕ → ℕ, (∀ r, r < R → rpv m3 A R f r = F r) →
      (∀ r, R ≤ r → F r = 0) → tv m4 A R f = F := by
    intro f hc hf7 F hF1 hF2
    have hf : f < 19 := by unfold RPF at hc; omega
    funext r
    unfold tv
    by_cases hr : r < R
    · rw [ite_eq_left hr, h34 f r hf hr, ite_eq_left hc, hF1 r hr]
    grind
  have eta : N = ⟨N.rem, N.pend, N.act, N.cpar, N.side, N.dpar, N.dlo, N.dhi, N.lpar, N.root,
      N.fin⟩ := rfl
  rw [eta]
  unfold rsOf
  congr 1
  · exact chord 11 (by omega_nf) _ (fun e he => by unfold cpv; rw [hnxt]; rfl)
      (fun e he => by rw [hN]; simp only [next, ite_eq_right (show ¬ e < K by omega), rsOf])
  · exact chord 12 (by omega_nf) _ (fun e he => by unfold cpv; rw [hnxt]; rfl)
      (fun e he => by rw [hN]; simp only [next, nPend, ite_eq_right (show ¬ e < K by omega), rsOf])
  · refine region 13 (by omega_nf) (by norm_num) _ (fun r hr => ?_) (fun r hr => ?_)
    · unfold rpv
      rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, hN]
      by_cases ht : tv m2 A R 8 r = r
      · by_cases ha : tv m0 A R 13 r = 1
        · have hbr := hb' r hr ht ha
          rw [a4 _ hbr, a5 _ hbr]
          simp only [next, rsOf, ite_eq_left hr]
          grind
        · simp only [next, rsOf, ite_eq_left hr]
          grind
      · rw [a4 r hr, a5 r hr, a12 _ (hp' r hr ht), hN]
        simp only [next, rsOf, ite_eq_left hr]
        clear * - ht
        grind
    · rw [hN]; simp only [next, rsOf, ite_eq_right (show ¬ r < R by omega), tv]
  · refine region 14 (by omega_nf) (by norm_num) _ (fun r hr => ?_) (fun r hr => ?_)
    · unfold rpv
      rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, hN]
      by_cases ht : tv m2 A R 8 r = r
      · by_cases ha : tv m0 A R 13 r = 1
        · have hbr := hb' r hr ht ha
          rw [a4 _ hbr, a5 _ hbr]
          simp only [next, rsOf, ite_eq_left hr]
          grind
        · simp only [next, rsOf, ite_eq_left hr]
          grind
      · rw [a4 r hr, a5 r hr, a12 _ (hp' r hr ht), hN]
        simp only [next, rsOf, ite_eq_left hr]
        clear * - ht
        grind
    · rw [hN]; simp only [next, rsOf, ite_eq_right (show ¬ r < R by omega), tv]
  · refine region 15 (by omega_nf) (by norm_num) _ (fun r hr => ?_) (fun r hr => ?_)
    · unfold rpv
      rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, hN]
      by_cases ht : tv m2 A R 8 r = r
      · by_cases ha : tv m0 A R 13 r = 1
        · have hbr := hb' r hr ht ha
          rw [a4 _ hbr, a5 _ hbr]
          simp only [next, rsOf, ite_eq_left hr]
          grind
        · simp only [next, rsOf, ite_eq_left hr]
          grind
      · rw [a4 r hr, a5 r hr, a12 _ (hp' r hr ht), hN]
        simp only [next, rsOf, ite_eq_left hr]
        clear * - ht
        grind
    · rw [hN]; simp only [next, rsOf, ite_eq_right (show ¬ r < R by omega), tv]
  · exact chord 16 (by omega_nf) _ (fun e he => by unfold cpv; rw [hnxt]; rfl)
      (fun e he => by rw [hN]; simp only [next, ite_eq_right (show ¬ e < K by omega), rsOf])
  · exact chord 17 (by omega_nf) _ (fun e he => by unfold cpv; rw [hnxt]; rfl)
      (fun e he => by rw [hN]; simp only [next, ite_eq_right (show ¬ e < K by omega), rsOf])
  · exact chord 18 (by omega_nf) _ (fun e he => by unfold cpv; rw [hnxt]; rfl)
      (fun e he => by rw [hN]; simp only [next, ite_eq_right (show ¬ e < K by omega), rsOf])
  · refine region 0 (by omega_nf) (by norm_num) _ (fun r hr => ?_) (fun r hr => ?_)
    · unfold rpv
      rw [a8 r hr, a13 r hr, a9 r hr, a14 r hr, a15 r hr, a0 r hr, hN]
      by_cases ht : tv m2 A R 8 r = r
      · by_cases ha : tv m0 A R 13 r = 1
        · have hbr := hb' r hr ht ha
          rw [a4 _ hbr, a5 _ hbr]
          simp only [next, rsOf, ite_eq_left hr]
          clear * - ht ha
          grind
        · simp only [next, rsOf, ite_eq_left hr]
          grind
      · rw [a4 r hr, a5 r hr, a12 _ (hp' r hr ht), hN]
        simp only [next, rsOf, ite_eq_left hr]
        clear * - ht
        simp_all
    · rw [hN]; simp only [next, rsOf, ite_eq_right (show ¬ r < R by omega), tv]
  · rw [hroot, hN]
    have hR0 : 0 < R := by omega
    simp only [next, rsOf, tv_lt hR0]
    rw [t02 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  · rw [hfin, hN]
    simp only [next, rsOf]
    congr 1
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro r hr
    rw [Finset.mem_range] at hr
    unfold SingAt
    rw [a8 r hr, a13 r hr, a9 r hr]

end roundmem

section roundram

variable {P : Polygon} {W A R K D CB RB LB : ℕ}

/-- `CPFacts` only reads fields outside the chord pass. -/
theorem CPFacts.congr {m m' : ℕ → ℕ} (hF : CPFacts m A R K)
    (hs : ∀ f u, f < 19 → ¬ CPF f → u < R → fv m' A R f u = fv m A R f u) : CPFacts m' A R K := by
  have hKR := hF.hKR
  have h6 := fun u => hs 6 u (by norm_num) (by omega_nf)
  have h3 := fun u => hs 3 u (by norm_num) (by omega_nf)
  have h8 := fun u => hs 8 u (by norm_num) (by omega_nf)
  have h9 := fun u => hs 9 u (by norm_num) (by omega_nf)
  have h4 := fun u => hs 4 u (by norm_num) (by omega_nf)
  have h13 := fun u => hs 13 u (by norm_num) (by omega_nf)
  have h14 := fun u => hs 14 u (by norm_num) (by omega_nf)
  have h15 := fun u => hs 15 u (by norm_num) (by omega_nf)
  refine ⟨hKR, fun e' he' => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
    fun t ht htt ha hs2 => ?_⟩
  all_goals (grind [Chazelle.Core.DecR.CPFacts, Chazelle.Core.DecR.CPF])

/-- The static fields (order, parent, parent chord, low flag, child endpoint) are those of `mB`. -/
def Stat (mB m : ℕ → ℕ) (A R : ℕ) : Prop :=
  ∀ f u, (f = 1 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6) → u < R → fv m A R f u = fv mB A R f u

/-- **One round on the RAM** preserves the round invariant, one round further. -/
theorem roundBody_exec {c : Config} (hw : WordsBounded W c) (hR : DRegs A R K CB RB LB c)
    (hAW : A + 12 + 20 * R ≤ W) {up dn pos mB : ℕ → ℕ}
    (h : Rooted R K up dn (tv mB A R 1) pos (tv mB A R 3) (tv mB A R 4))
    (hch : ∀ e, e < K → tv mB A R 6 e < R ∧ tv mB A R 6 e ≠ 0 ∧ tv mB A R 4 (tv mB A R 6 e) = e)
    (hdeg : ∀ v, v < R →
      (kids R (tv mB A R 3) (tv mB A R 4) rem0 v).card + (if v = 0 then 0 else 1) ≤ D)
    (hst : Stat mB c.nmem A R) (h7 : ∀ u, u < R → fv c.nmem A R 7 u = 1)
    {j : ℕ} {gc : ℕ → Finset ℕ} {cr : ℕ → ℕ}
    (hI : RInv R K D (tv mB A R 3) (tv mB A R 4) (tv mB A R 5) (tv mB A R 6) j
      (rsOf c.nmem A R (c.nreg 60024) (c.nreg 60023)) gc cr)
    (hj : c.nreg 60022 = j) (hjW : j + 1 ≤ W) (hfin : c.nreg 60023 < R) :
    ∃ c' k, Exec P W roundBody c c' k ∧ k ≤ 175 * R + 43 ∧ WordsBounded W c' ∧
      DFr (A + 12) (A + 12 + 19 * R) c c' ∧ Stat mB c'.nmem A R ∧
      (∀ u, u < R → fv c'.nmem A R 7 u = 1) ∧ c'.nreg 60022 = j + 1 ∧
      ∃ gc' cr', RInv R K D (tv mB A R 3) (tv mB A R 4) (tv mB A R 5) (tv mB A R 6) (j + 1)
        (rsOf c'.nmem A R (c'.nreg 60024) (c'.nreg 60023)) gc' cr' := by
  have hKR : K < R := by have := h.hR; omega
  have hR0 : 0 < R := by omega
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13⟩ := noWr_passes
  have sv : ∀ f u, (f = 1 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6) → u < R →
      fv c.nmem A R f u = tv mB A R f u := fun f u hf hu => by rw [hst f u hf hu, tv_lt hu]
  -- pass 1
  obtain ⟨c1, k1, e1, hk1, hw1, hf1, hv1⟩ := p1S_exec (P := P) hw hR hAW h
    (rem := tv c.nmem A R 11) (fun u hu => sv 1 u (by simp) hu) (fun u hu => sv 3 u (by simp) hu)
    (fun u hu => sv 4 u (by simp) hu) (fun u hu => (tv_lt hu).symm) h7
  have hR1 := hR.frame hf1
  have f01 : ∀ f u, f < 19 → f ≠ 7 → u < R → fv c1.nmem A R f u = fv c.nmem A R f u :=
    fun f u hf h7 hu => by grind
  -- pass 2
  obtain ⟨c2, k2, e2, hk2, hw2, hf2, hag, hv2⟩ := p2S_exec (P := P) hw1 hR1 hAW h
    (rem := tv c.nmem A R 11)
    (fun u hu => by grind)
    (fun u hu => by grind)
    (fun u hu => by grind)
    (fun u hu => by rw [f01 11 u (by norm_num) (by norm_num) hu, tv_lt hu])
    (fun u hu => by grind)
  have hR2 := hR1.frame hf2
  have f02 : ∀ f u, f < 19 → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R →
      fv c2.nmem A R f u = fv c.nmem A R f u :=
    fun f u hf h7 h8 h9 h10 hu => by grind
  -- the top pass, characterised
  set σ := rsOf c.nmem A R (c.nreg 60024) (c.nreg 60023) with hσ
  set prg := tv mB A R 3 with hprg
  set pch := tv mB A R 4 with hpch
  set top := tv c2.nmem A R 8 with htop
  set best := tv c2.nmem A R 9 with hbest
  set bestv := tv c2.nmem A R 10 with hbestv
  obtain ⟨hT', hB'⟩ := p2_full h (S := sz R prg pch σ.rem) (fun u hu => rfl) (t3Of c1.nmem A R)
  have hT : ∀ u, u < R → top u < R ∧ IsTop pch σ.rem (top u) ∧ AncX R prg pch σ.rem (top u) u :=
    fun u hu => by
      have := (hag u hu).1
      simp only [t3Of] at this
      rw [htop, tv_lt hu, this]; exact hT' u hu
  have hB : ∀ t, t < R → IsTop pch σ.rem t →
      (∀ c, c < R → AncX R prg pch σ.rem t c → c ≠ t → cval R prg pch σ.rem t c ≤ bestv t) ∧
      ((best t = t ∧ ∀ c, c < R → AncX R prg pch σ.rem t c → c = t) ∨
        (best t < R ∧ AncX R prg pch σ.rem t (best t) ∧ best t ≠ t ∧
          bestv t = cval R prg pch σ.rem t (best t))) := fun t ht htt => by
    have a2 := (hag t ht).2.1
    have a3 := (hag t ht).2.2
    simp only [t3Of] at a2 a3
    rw [hbest, hbestv, tv_lt ht, tv_lt ht, a2, a3]; exact hB' t ht htt
  obtain ⟨F1, F2, F3, F4, F5, F6⟩ := round_facts h hch hT hB hI
  -- conversions at `c2`
  have T8 : ∀ u, u < R → fv c2.nmem A R 8 u = top u := fun u hu => by rw [htop, tv_lt hu]
  have T9 : ∀ u, u < R → fv c2.nmem A R 9 u = best u := fun u hu => by rw [hbest, tv_lt hu]
  have S2 : ∀ f u, (f = 1 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6) → u < R →
      fv c2.nmem A R f u = tv mB A R f u := fun f u hf hu => by
    rw [f02 f u (by omega) (by omega) (by omega) (by omega) (by omega) hu]; exact sv f u hf hu
  have Q2 : ∀ f u, f < 19 → 11 ≤ f ∨ f = 0 → u < R → fv c2.nmem A R f u = tv c.nmem A R f u :=
    fun f u hf hf' hu => by
      rw [f02 f u hf (by omega) (by omega) (by omega) (by omega) hu, tv_lt hu]
  have hF2 : CPFacts c2.nmem A R K := by
    refine ⟨hKR, fun e he => ?_, fun u hu => ?_, fun u hu => ?_, fun x hx htx => ?_,
      fun t ht htt ha hs => ?_⟩
    · obtain ⟨a1, a2, -⟩ := hch e he
      rw [S2 6 e (by simp) (by omega), S2 3 _ (by simp) a1]
      exact ⟨a1, a2, h.prg_lt _ a1 a2⟩
    · rw [T8 u hu]; exact (hT u hu).1
    · rw [T8 u hu, T8 _ (hT u hu).1]; exact F1 u hu
    · rw [T8 x hx] at htx
      obtain ⟨b1, b2⟩ := F2 x hx htx
      rw [T9 x hx]; refine ⟨b1, fun hb => ?_⟩; rw [S2 4 _ (by simp) b1]; exact b2 hb
    · rw [T8 t ht] at htt; rw [Q2 13 t (by norm_num) (by omega) ht] at ha
      rw [Q2 15 t (by norm_num) (by omega) ht] at hs
      rw [Q2 14 t (by norm_num) (by omega) ht]; exact F3 t ht htt ha hs
  -- the chord pass
  obtain ⟨c3, k3, e3, hk3, hw3, hf3, hv3⟩ := cpS_exec (P := P) hw2 hR2 hAW hF2
    (fun e he hp => by
      have he' : e < R := by omega
      rw [Q2 12 e (by norm_num) (by omega) he'] at hp
      obtain ⟨a1, -, -⟩ := hch e he
      rw [S2 6 e (by simp) he', T8 _ a1]; exact F4 e he hp)
  have hR3 := hR2.frame hf3
  have f23 : ∀ f u, f < 19 → ¬ CPF f → u < R → fv c3.nmem A R f u = fv c2.nmem A R f u :=
    fun f u hf hc hu => by rw [hv3 f u hf hu, ite_eq_right (fun hh => hc hh.2)]
  have hF3 := hF2.congr f23
  -- the root step
  obtain ⟨c4, k4, e4, hk4, m4, s4, r24⟩ := rootS_exec (P := P) hw3 hR3 hAW hF3
    (by rw [f23 8 0 (by norm_num) (by omega_nf) hR0, T8 0 hR0]; exact F6)
  have hR4 := hR3.of_same s4 (by simp [Prot])
  -- the region pass
  have n23 : c3.nreg 60023 = c.nreg 60023 := by
    rw [nreg_of_noWr e3 w8, nreg_of_noWr e2 w5, nreg_of_noWr e1 w2]
  have n24 : c3.nreg 60024 = c.nreg 60024 := by
    rw [nreg_of_noWr e3 w9, nreg_of_noWr e2 w6, nreg_of_noWr e1 w3]
  have n22 : c4.nreg 60022 = c.nreg 60022 := by
    rw [nreg_of_noWr e4 w10, nreg_of_noWr e3 w7, nreg_of_noWr e2 w4, nreg_of_noWr e1 w1]
  have n23' : c4.nreg 60023 = c.nreg 60023 := by rw [nreg_of_noWr e4 w11, n23]
  have g8 : ∀ u, u < R → fv c4.nmem A R 8 u = top u := fun u hu => by
    rw [m4, f23 8 u (by norm_num) (by omega_nf) hu, T8 u hu]
  have g9 : ∀ u, u < R → fv c4.nmem A R 9 u = best u := fun u hu => by
    rw [m4, f23 9 u (by norm_num) (by omega_nf) hu, T9 u hu]
  have gQ : ∀ f u, f < 19 → ¬ CPF f → 11 ≤ f → u < R → fv c4.nmem A R f u = tv c.nmem A R f u :=
    fun f u hf hc hf' hu => by rw [m4, f23 f u hf hc hu, Q2 f u hf (by omega) hu]
  have g4 : ∀ u, u < R → fv c4.nmem A R 4 u = pch u := fun u hu => by
    rw [m4, f23 4 u (by norm_num) (by omega_nf) hu, S2 4 u (by simp) hu]
  obtain ⟨c5, k5, e5, hk5, hw5, hf5, r23, hv5⟩ := rpS_exec (P := P) e4.wb_right hR4 hAW
    (fun r hr htr ha => by
      rw [g8 r hr] at htr; rw [g9 r hr]; exact (F2 r hr htr).1)
    (fun r hr htr ha hbr hs => by
      rw [g8 r hr] at htr
      rw [gQ 13 r (by norm_num) (by omega_nf) (by norm_num) hr] at ha
      rw [gQ 15 r (by norm_num) (by omega_nf) (by norm_num) hr] at hs
      rw [gQ 14 r (by norm_num) (by omega_nf) (by norm_num) hr]
      exact F3 r hr htr ha hs)
    (fun r hr htr => by rw [g8 r hr] at htr; rw [g4 r hr]; exact F5 r hr htr)
    (by omega)
  have hR5 := hR4.frame hf5
  -- the round counter
  have n22' : c5.nreg 60022 = j := by rw [nreg_of_noWr e5 w12, n22, hj]
  have e6 := Exec.addN (P := P) e5.wb_right 60022 60022 60011 (by rw [n22', hR5.one]; exact hjW)
  set c6 := { c5 with nreg := upd c5.nreg 60022 (c5.nreg 60022 + c5.nreg 60011) } with hc6
  have hf6 : DFr (A + 12) (A + 12 + 19 * R) c5 c6 :=
    DFr.nreg _ fun r hr _ => by unfold Prot at hr; ram_simp
  -- memory relations
  have m56 : c6.nmem = c5.nmem := rfl
  have h45 : ∀ f u, f < 19 → u < R → fv c6.nmem A R f u =
      if RPF f then rpv c3.nmem A R f u else fv c3.nmem A R f u := fun f u hf hu => by
    rw [m56, hv5 f u hf hu, m4]
  have hmem := round_mem (m0 := c.nmem) (m2 := c2.nmem) (m3 := c3.nmem) (m4 := c6.nmem)
    (root := c.nreg 60024) (fin := c.nreg 60023) (root' := c6.nreg 60024)
    (fin' := c6.nreg 60023) hKR f02 hv3 h45
    (fun r hr htr ha => by
      rw [T8 r hr] at htr; rw [T9 r hr]; exact (F2 r hr htr).1)
    (fun r hr htr => by rw [T8 r hr] at htr; rw [S2 4 r (by simp) hr]; exact F5 r hr htr)
    (by
      have e24 : c6.nreg 60024 = c4.nreg 60024 := by
        rw [hc6]; config_simp; rw [nreg_of_noWr e5 w13]
      rw [e24, r24, n24, f23 13 0 (by norm_num) (by omega_nf) hR0,
        f23 15 0 (by norm_num) (by omega_nf) hR0,
        f02 13 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR0,
        f02 15 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR0,
        tv_congr (fun u hu => f23 9 u (by norm_num) (by omega_nf) hu),
        tv_congr (fun u hu => f23 4 u (by norm_num) (by omega_nf) hu)])
    (by
      ram_simp)
  have tS : ∀ f, (f = 1 ∨ f = 3 ∨ f = 4 ∨ f = 5 ∨ f = 6) → tv c.nmem A R f = tv mB A R f :=
    fun f hf => tv_congr (fun u hu => hst f u hf hu)
  rw [tS 3 (by simp), tS 4 (by simp), tS 5 (by simp), tS 6 (by simp)] at hmem
  -- conclusion
  have hS6 : ∀ f u, f < 19 → ¬ RPF f → ¬ CPF f → f ≠ 7 → f ≠ 8 → f ≠ 9 → f ≠ 10 → u < R →
      fv c6.nmem A R f u = fv c.nmem A R f u := fun f u hf hr hc h7 h8 h9 h10 hu => by
    rw [h45 f u hf hu, ite_eq_right hr, f23 f u hf hc hu, f02 f u hf h7 h8 h9 h10 hu]
  refine ⟨c6, k1 + (k2 + (k3 + (k4 + (k5 + 1)))), .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 e6)))),
    by omega, e6.wb_right, ?_, fun f u hf hu => ?_, fun u hu => ?_, ?_,
    gcNext R K prg pch (tv mB A R 6) top best σ gc,
    crNext K (tv mB A R 6) top best σ j cr, ?_⟩
  · refine ((((hf1.trans hf2).trans hf3).trans ?_).trans hf5).trans hf6
    exact DFr.of_same s4 (by simp [Prot]) (fun a _ => by rw [m4])
  · have hf' : f < 19 := by omega
    rw [hS6 f u hf' (by omega_nf) (by omega_nf) (by omega) (by omega) (by omega)
      (by omega) hu]
    exact hst f u hf hu
  · rw [h45 7 u (by norm_num) hu, ite_eq_left (by omega_nf)]; simp [rpv]
  · rw [hc6]; config_simp; rw [n22', hR5.one]
  · rw [hmem]
    exact rinv_next h hch hT hB hI hdeg

end roundram

end

end Chazelle.Core.DecR
