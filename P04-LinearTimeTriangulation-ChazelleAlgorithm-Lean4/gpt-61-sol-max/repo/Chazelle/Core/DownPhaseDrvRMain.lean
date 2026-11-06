module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseDrvRProg
public import Chazelle.Core.Output

/-!
# Down-phase driver (RAM side), D1 part 4: the down phase from its three components

**`downPhaseH_of_parts`**: for a memory context with a local capacity, the transition
(`TransSpec`), one level (`LevelSpec`) and the base case (`BaseSpec`), with a bounded count
function `cnt`, give `DownPhaseSpecH X`.  The program is `downS sT sL sB n₀`
(`DownPhaseDrvRProg`):

```
transition ; λ := p ; g := guard ; while 15 < g do (level ; λ := ⌈λ/5⌉ + 11 ; g := guard) ;
base ; coreReg 3 := handle
```

The level loop is verified with the potential `pot f λ` (`DownPhaseDrvRCost`), `f` the budget of
one level and its bookkeeping, which is at most `potConst · 2^p ≤ 2 potConst · n`
(`pot_lvlBudget_le`).
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs

@[expose] public section

/-! ## A loop rule with a potential and a frame -/

/-- **`whileLtN` with a potential, keeping a frame.** -/
theorem whileLtN_potential_frame {P : Polygon} {W a b : ℕ} {body : Stmt} {B : Finset ℕ}
    (I : Config → Prop) (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Frame B c c' k ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      Frame B c c' k ∧ k ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨c₁, k₁, hb, hI₁, hF₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hF₂, hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht',
        (hF₁.trans hF₂).mono (by simp) (by omega), by omega⟩
    · exact ⟨c, 2, .whileLtN_false ht (hI c hc), hc, ht,
        ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl,
          by omega⟩, by omega⟩

/-! ## The loop invariant -/

/-- **The invariant of the level loop**: the word bound, the environment, the level `λ ≤ p` in
register `0` of `bDownDrv` with `Inv(λ)`, the guard `g` and the constant `15`, and room for the
remaining budget `pot f λ` plus `Bb` (the base and the final copy). -/
def LoopI (X : MemCtx) (cnt : ℕ → ℕ) (n₀ : ℕ) (f : ℕ → ℕ) (Bb : ℕ) (P : Polygon) (W : ℕ)
    (c : Config) : Prop :=
  WordsBounded W c ∧ EnvD X P W c ∧ rd c bDownDrv 0 ≤ topGrade P.n ∧
    InvAt cnt P c (rd c bDownDrv 0) ∧
    c.nreg 210007 = (if n₀ ≤ P.n then c.nreg 210000 else 0) ∧ c.nreg 210008 = 15 ∧
    c.nreg ALLOC + pot f (rd c bDownDrv 0) + Bb ≤ W

theorem topGrade_le (n : ℕ) : topGrade n ≤ n := by
  unfold topGrade
  exact Nat.clog_le_of_le_pow ((Nat.sub_le n 1).trans (Nat.lt_two_pow_self).le)

/-- The setup record gives `λ ↦ ⌈λ/5⌉ + 11` for `λ ≤ p`. -/
theorem setup_next {m : ℕ → ℕ} {S n E lam : ℕ} (h : SetupAt m S n E) (hl : lam ≤ topGrade n) :
    m (S + topGrade n + 4 + lam) = Cost.ceilBeta lam := (h.2.2.1 lam (by omega)).2

/-- `EnvD` in terms of the raw registers of `coreReg 0`. -/
theorem EnvD.setup {X : MemCtx} {P : Polygon} {W : ℕ} {c : Config} (h : EnvD X P W c) :
    SetupAt c.nmem (c.nreg 230000) P.n (c.nreg ALLOC) := h.2.2.2.1.holds

/-- **One iteration of the level loop.** -/
theorem levelBody_step {X : MemCtx} (hX : X.CapLocal) {cnt : ℕ → ℕ} {n₀ : ℕ} {sL : Stmt}
    {κL : ℕ}
    (hL : Meets sL drvBands
      (fun P W c => EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧
        rd c bDownDrv 0 ≤ topGrade P.n ∧ InvAt cnt P c (rd c bDownDrv 0))
      (fun P c c' => rd c' bDownDrv 0 = rd c bDownDrv 0 ∧
        InvAt cnt P c' (nextLvl (rd c bDownDrv 0)))
      (fun _ c => κL * ((rd c bDownDrv 3 + 1) * (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1))))
    {Bb : ℕ} {P : Polygon} {W : ℕ} (hn₀ : n₀ + 15 ≤ W) {c : Config}
    (hI : LoopI X cnt n₀ (lvlBudget (κL + 20) cnt (topGrade P.n)) Bb P W c)
    (ht : c.nreg 210008 < c.nreg 210007) :
    ∃ c' k, Exec P W (levelBody sL n₀) c c' k ∧
      LoopI X cnt n₀ (lvlBudget (κL + 20) cnt (topGrade P.n)) Bb P W c' ∧
      Frame drvBands c c' k ∧
      pot (lvlBudget (κL + 20) cnt (topGrade P.n)) (rd c' bDownDrv 0) + k + 2 ≤
        pot (lvlBudget (κL + 20) cnt (topGrade P.n)) (rd c bDownDrv 0) := by
  obtain ⟨hw, hE, hlp, hInv, hg, h15, hroom⟩ := hI
  have hn₀n : n₀ ≤ P.n := by
    grind
  have h16 : 16 ≤ rd c bDownDrv 0 := by
    aesop
  have hpot := pot_of_le (f := lvlBudget (κL + 20) cnt (topGrade P.n)) h16
  -- the level
  have hK := InvAt.len_le hInv
  have hcost : κL * ((rd c bDownDrv 3 + 1) * (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1)) + 20 ≤
      lvlBudget (κL + 20) cnt (topGrade P.n) (rd c bDownDrv 0) := by
    unfold lvlBudget kBound
    have h1 : (rd c bDownDrv 3 + 1) * (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1) ≤
        (cnt (rd c bDownDrv 0) * (2 ^ topGrade P.n + 2 ^ Cost.ceilBeta (rd c bDownDrv 0)) /
            2 ^ Cost.ceilBeta (rd c bDownDrv 0) + 1) *
          (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1) := Nat.mul_le_mul_right _ (by omega)
    have h2 : 1 ≤ (rd c bDownDrv 3 + 1) * (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1) :=
      Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hpre : EnvD X P W c ∧ n₀ ≤ P.n ∧ 16 ≤ rd c bDownDrv 0 ∧ rd c bDownDrv 0 ≤ topGrade P.n ∧
      InvAt cnt P c (rd c bDownDrv 0) := ⟨hE, hn₀n, h16, hlp, hInv⟩
  obtain ⟨c₁, k₁, e₁, hk₁, ⟨h0₁, hInv₁⟩, hF₁⟩ := hL P W c hw hpre (by
    grind)
  replace hk₁ : k₁ ≤ κL * ((rd c bDownDrv 3 + 1) *
      (lemma41Nat (nextLvl (rd c bDownDrv 0)) + 1)) := hk₁
  have hw₁ := e₁.wb_right
  have hE₁ := hE.frame hX hF₁ bCore_notin_drvBands
  have hS₁ := hE₁.setup
  have hA₁ := hF₁.2.2.2.2.2.2
  -- `λ := ⌈λ/5⌉ + 11`
  have hl₁ : c₁.nreg 210000 = rd c bDownDrv 0 := h0₁
  have hp₁ : c₁.nmem (c₁.nreg 230000 + 1) = topGrade P.n := hS₁.2.1
  have hnext := setup_next hS₁ hlp
  have hpn := topGrade_le P.n
  have hSA := hS₁.2.2.2
  have hS₁W : c₁.nreg 230000 + topGrade P.n + 4 + rd c bDownDrv 0 ≤ W := by omega
  have hlt := Cost.ceilBeta_add_eleven_lt h16
  have hnW := hE.2.1
  obtain ⟨c₂, k₂, e₂, hk₂, hl₂, hr₂, hr₂', hm₂, hrr₂, hrm₂, ho₂⟩ :=
    lamNext_exec (P := P) c₁ hw₁ rfl hp₁ hl₁ hS₁W (by omega)
  rw [hnext] at hl₂
  have hw₂ := e₂.wb_right
  -- the guard
  obtain ⟨c₃, k₃, e₃, hk₃, hg₃, h15₃, hr₃, hr₃', hl₃, hm₃, hrr₃, hrm₃, ho₃⟩ :=
    guardS_exec (P := P) n₀ c₂ hw₂ hn₀ (by omega)
  have hw₃ := e₃.wb_right
  -- frames
  have hF₂ : Frame {bDownDrv} c₁ c₂ k₂ := frame_drv hr₂ hm₂ hrr₂ hrm₂ ho₂
  have hF₃ : Frame {bDownDrv} c₂ c₃ k₃ := frame_drv hr₃ hm₃ hrr₃ hrm₃ ho₃
  have hsub : drvBands ∪ {bDownDrv} ∪ {bDownDrv} ⊆ drvBands := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_singleton] at hx
    rcases hx with (hx | hx) | hx
    · exact hx
    · rw [hx]; exact bDownDrv_mem_drvBands
    · rw [hx]; exact bDownDrv_mem_drvBands
  have hF : Frame drvBands c c₃ (k₁ + k₂ + k₃) := ((hF₁.trans hF₂).trans hF₃).mono hsub le_rfl
  have hlam₃ : rd c₃ bDownDrv 0 = nextLvl (rd c bDownDrv 0) := by
    rw [rd_drv, Nat.add_zero, hl₃, hl₂]; rfl
  have hr13 : ∀ i, 1 ≤ i → i ≤ 5 → rd c₃ bDownDrv i = rd c₁ bDownDrv i := by
    grind [rd_drv]
  have hA2 : c₂.nreg ALLOC = c₁.nreg ALLOC := hr₂ ALLOC (by omega_nf)
  have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := hr₃ ALLOC (by omega_nf)
  have hInv₃ : InvAt cnt P c₃ (nextLvl (rd c bDownDrv 0)) :=
    hInv₁.transport hr13 (by omega) (fun a _ => by grind)
  have hE₃ : EnvD X P W c₃ :=
    hE₁.frame hX (hF₂.trans hF₃) (by decide)
  have hpotn := nextLvl_lt h16
  refine ⟨c₃, k₁ + (k₂ + k₃), Exec.seq e₁ (Exec.seq e₂ e₃),
    ⟨hw₃, hE₃, ?_, ?_, ?_, h15₃, ?_⟩, hF.mono subset_rfl (by omega), ?_⟩
  · omega
  · grind
  · grind
  all_goals grind

/-- `2^p ≤ 2 n + 2` for `p = topGrade n`. -/
theorem two_pow_topGrade_le (n : ℕ) : 2 ^ topGrade n ≤ 2 * n + 2 := by
  unfold topGrade
  rcases Nat.lt_or_ge (n - 1) 2 with h | h
  · rw [Nat.clog_of_right_le_one (show n - 1 ≤ 1 by omega), pow_zero]; omega
  · have h1 := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n - 1 by omega)
    have h2 : 1 ≤ Nat.clog 2 (n - 1) := Nat.clog_pos (by norm_num) (by omega)
    obtain ⟨q, hq⟩ : ∃ q, Nat.clog 2 (n - 1) = q + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h2).symm⟩
    grind [pow_succ, Nat.pred_succ]

/-- The word bound of the host procedures from the budget. -/
theorem hostWords_le {n κ : ℕ} (hκ : 272 ≤ κ) : hostWords n ≤ κ * (n + 1) := by
  unfold hostWords
  have := Nat.mul_le_mul_right (n + 1) hκ
  omega

/-- **The down phase from its components** (D1): the transition, one level and the base case,
with a bounded count function, give `DownPhaseSpecH X` for a context with a local capacity. -/
theorem downPhaseH_of_parts {X : MemCtx} (hX : X.CapLocal) {cnt : ℕ → ℕ} {C n₀ : ℕ}
    (hc : ∀ l, cnt l ≤ C) (hT : TransSpec X cnt) (hL : LevelSpec X cnt n₀)
    (hB : BaseSpec X cnt n₀) : DownPhaseSpecH X := by
  obtain ⟨sT, κT, hT⟩ := hT
  obtain ⟨sL, κL, hL⟩ := hL
  obtain ⟨sB, κB, hB⟩ := hB
  refine ⟨downS sT sL sB n₀, κT + κB + 2 * potConst C (κL + 20) + n₀ + 300, ?_⟩
  intro P W c hw hpre hroom
  obtain ⟨hG, hn3, hSet, hXh, hcap, hTop⟩ := hpre
  replace hroom : c.nreg ALLOC + (κT + κB + 2 * potConst C (κL + 20) + n₀ + 300) * (P.n + 1) ≤ W :=
    hroom
  obtain ⟨κ, hκ⟩ : ∃ κ, κT + κB + 2 * potConst C (κL + 20) + n₀ + 300 = κ := ⟨_, rfl⟩
  rw [hκ] at hroom
  obtain ⟨f, hf⟩ : ∃ f, lvlBudget (κL + 20) cnt (topGrade P.n) = f := ⟨_, rfl⟩
  have hn1 : n₀ + 300 ≤ κ * (P.n + 1) := by
    grind
  have hWh : hostWords P.n ≤ W := by
    have := hostWords_le (n := P.n) (show 272 ≤ κ by omega); omega
  have hE : EnvD X P W c := ⟨hG, hn3, hWh, hSet, hXh, hcap⟩
  have hpot : pot f (topGrade P.n) ≤ potConst C (κL + 20) * (2 * P.n + 2) := hf ▸
    (pot_lvlBudget_le hc (κL + 20) (topGrade P.n) _ le_rfl).trans
      (Nat.mul_le_mul_left _ (two_pow_topGrade_le P.n))
  have hbud : κT * (P.n + 1) + κB * (P.n + 1) + 1 + pot f (topGrade P.n) + 13 ≤ κ * (P.n + 1) := by
    
    rw [← hκ]; nlinarith
  -- the transition
  obtain ⟨c₁, k₁, e₁, hk₁, hInv₁, hF₁⟩ := hT P W c hw ⟨hE, hTop⟩ (by
    grind)
  replace hk₁ : k₁ ≤ κT * (P.n + 1) := hk₁
  have hw₁ := e₁.wb_right
  have hE₁ := hE.frame hX hF₁ bCore_notin_drvBands
  have hA₁ := hF₁.2.2.2.2.2.2
  -- `λ := p` and the guard
  have hS₁ := hE₁.setup
  have hSA := hS₁.2.2.2
  obtain ⟨c₂, k₂, e₂, hk₂, hl₂, hr₂, hr₂', hm₂, hrr₂, hrm₂, ho₂⟩ :=
    lamP_exec (P := P) c₁ hw₁ rfl (by omega)
  have hw₂ := e₂.wb_right
  rw [hS₁.2.1] at hl₂
  obtain ⟨c₃, k₃, e₃, hk₃, hg₃, h15₃, hr₃, hr₃', hl₃, hm₃, hrr₃, hrm₃, ho₃⟩ :=
    guardS_exec (P := P) n₀ c₂ hw₂ (by omega) (by omega)
  have hw₃ := e₃.wb_right
  have hF₂ : Frame {bDownDrv} c₁ c₂ k₂ := frame_drv hr₂ hm₂ hrr₂ hrm₂ ho₂
  have hF₃ : Frame {bDownDrv} c₂ c₃ k₃ := frame_drv hr₃ hm₃ hrr₃ hrm₃ ho₃
  have hA2 : c₂.nreg ALLOC = c₁.nreg ALLOC := hr₂ ALLOC (by omega_nf)
  have hA3 : c₃.nreg ALLOC = c₂.nreg ALLOC := hr₃ ALLOC (by omega_nf)
  have hl3 : rd c₃ bDownDrv 0 = topGrade P.n := by rw [rd_drv, Nat.add_zero, hl₃, hl₂]
  have hInv₃ : InvAt cnt P c₃ (topGrade P.n) :=
    hInv₁.transport (fun i h1 h5 => by
      grind [rd_drv])
      (by omega) (fun a _ => by grind)
  have hE₃ : EnvD X P W c₃ := hE₁.frame hX (hF₂.trans hF₃) (by simp [bCore, bDownDrv])
  have hI₃ : LoopI X cnt n₀ f (κB * (P.n + 1) + 1) P W c₃ := by
    grind [Chazelle.Core.DrvR.LoopI]
  -- the level loop
  obtain ⟨c₄, k₄, e₄, hI₄, hx₄, hF₄, hk₄⟩ := whileLtN_potential_frame (P := P) (W := W)
    (a := 210008) (b := 210007) (body := levelBody sL n₀) (B := drvBands)
    (LoopI X cnt n₀ f (κB * (P.n + 1) + 1) P W) (fun c => pot f (rd c bDownDrv 0))
    (fun c h => h.1)
    (fun c h ht => hf ▸ levelBody_step hX hL (P := P) (W := W) (by omega) (hf ▸ h) ht) hI₃
  rw [hl3] at hk₄
  obtain ⟨hw₄, hE₄, hlp₄, hInv₄, hg₄, h15₄, hroom₄⟩ := hI₄
  -- the base
  have hbase : 16 > rd c₄ bDownDrv 0 ∨ P.n < n₀ := by
    by_cases h : n₀ ≤ P.n
    · rw [ite_eq_left h] at hg₄; ram_simp <;> omega_nf
    omega
  obtain ⟨c₅, k₅, e₅, hk₅, ⟨N, hN, hNF, hFull⟩, hF₅⟩ := hB P W c₄ hw₄
    ⟨hE₄, rd c₄ bDownDrv 0, hlp₄, by omega, hInv₄⟩ (by
      grind)
  replace hk₅ : k₅ ≤ κB * (P.n + 1) := hk₅
  have hw₅ := e₅.wb_right
  -- the final copy
  have e₆ := Exec.copyN (P := P) hw₅ 230003 210006
  refine ⟨_, k₁ + ((k₂ + k₃) + (k₄ + (k₅ + 1))),
    Exec.seq e₁ (Exec.seq (Exec.seq e₂ e₃) (Exec.seq e₄ (Exec.seq e₅ e₆))), ?_, ?_, ?_⟩
  · show _ ≤ (κT + κB + 2 * potConst C (κL + 20) + n₀ + 300) * (P.n + 1)
    rw [hκ]; omega
  · refine ⟨N, ?_, hNF, hFull, fun k hk => ?_⟩
    · show Robust _ _ fun m => NFAt m ((upd c₅.nreg 230003 (c₅.nreg 210006)) 230003) N
      rw [Machine.upd_same]
      have hA : (upd c₅.nreg 230003 (c₅.nreg 210006)) ALLOC = c₅.nreg ALLOC := by
        omega_nf
      show Robust ((upd c₅.nreg 230003 (c₅.nreg 210006)) ALLOC) c₅.nmem _
      rw [hA]; exact hN
    · have := hNF.2.2.2.choose_spec.2.2.2.2.2.1 k hk
      rwa [show (Qof P).n = P.n from shear_n _ _] at this
  · have hF₆ : Frame {bCore} c₅ { c₅ with nreg := upd c₅.nreg 230003 (c₅.nreg 210006) } 1 :=
      frame_core (fun r hr => by ram_simp) rfl rfl rfl rfl
    have h23 : (drvBands ∪ (({bDownDrv} : Finset ℕ) ∪ {bDownDrv} ∪ (drvBands ∪ (drvBands ∪ {bCore}))))
        ⊆ phaseBands := by
      intro x hx
      simp only [Finset.mem_union, Finset.mem_singleton] at hx
      rcases hx with hx | ((hx | hx) | hx | hx | hx)
      · exact drvBands_subset hx
      · rw [hx]; decide
      · rw [hx]; decide
      · exact drvBands_subset hx
      · exact drvBands_subset hx
      · rw [hx]; decide
    exact (hF₁.trans ((hF₂.trans hF₃).trans (hF₄.trans (hF₅.trans hF₆)))).mono h23 le_rfl

end

end DrvR

end Chazelle.Core
