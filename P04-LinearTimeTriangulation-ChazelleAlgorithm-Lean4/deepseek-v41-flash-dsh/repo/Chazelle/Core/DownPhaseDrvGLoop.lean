module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvGLeaf

/-!
# Down-phase driver, region procedure (D5), part 8: the leaf loop

`LInv i e`: after `i` leaves, `pos = r219221` is the end of leaf `i - 1` (`0` if `i = 0`), the
remaining leaves have gaps of at most `64` edges from `pos` on (`GapsLe`), and (for `i > 0`) the
accumulated chain `⟨H.poly Q, 0, pos⟩` has granularity `γ ≤ γ₀ + 2 i - 1`, its end `pos` being a
junction.  `lfBody_exec`: one iteration (the connector before the leaf if `pos < s`, the leaf);
`lfLoop_exec`: the loop.
-/

namespace Chazelle.Core

namespace DrvG

open Machine Machine.Stmt Programs BuildRam DrvR

@[expose] public section

/-- **The invariant of the leaf loop** (`Lb` the budget of one iteration, `Rb` of the rest). -/
structure LInv (P : Polygon) (W : ℕ) (R : RData) (V : ℕ → ℕ) (Lb Rb i : ℕ) (e : Config) :
    Prop where
  wb : WordsBounded W e
  keep : ∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → e.nreg q = V q
  r20 : e.nreg 219220 = i
  r04 : e.nreg 219004 = (R.leaves P).length
  env : REnv R e
  r24 : e.nreg 219224 = R.T + 3 * i
  il : i ≤ (R.leaves P).length
  room : e.nreg ALLOC + ((R.leaves P).length - i) * Lb + Rb ≤ W
  st : ∃ pos γ, e.nreg 219221 = pos ∧ GapsLe 64 ((R.leaves P).drop i) pos (R.NP - 1) ∧
    ((i = 0 ∧ pos = 0 ∧ e.nreg 219222 = 0) ∨
      (0 < i ∧ 0 < pos ∧ AccOK P R e pos γ ∧ R.γ₀ ≤ γ ∧ γ + 1 ≤ R.γ₀ + 2 * i ∧
        JunOK (Qof P).n R.H pos))

/-- The budget of one iteration. -/
def lfB (pc : ℕ) : ℕ := 2 * pc + 30

theorem leaves_length_le {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}
    (hF : RFacts O P W R) : (R.leaves P).length ≤ 60 := by
  have := hostLeaves_length_le (n := (Qof P).n) (C := 2 ^ R.μ) Nat.one_le_two_pow R.H 0 hF.hruns
  have := hF.hHl
  unfold RData.leaves; omega

section exec

variable {O : OracleIface} {P : Polygon} {W : ℕ} {R : RData}


/-- **One iteration of the leaf loop.** -/
theorem lfBody_exec {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ} (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Rb i : ℕ} (e : Config) (hi : i < (R.leaves P).length)
    (hI : LInv P W R V (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) Rb i e) :
    ∃ e' k, Exec P W (lfBody sp sM) e e' k ∧
      LInv P W R V (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) Rb (i + 1) e' ∧
      k ≤ lfB (pcB κP (κ 130) κs (lemma41Nat R.μ)) ∧ Frame drvBands e e' k := by
  set pc := pcB κP (κ 130) κs (lemma41Nat R.μ) with hpc
  set x := (R.leaves P).getD i (0, 0, 0) with hx
  have hxL : x ∈ R.leaves P := by rw [hx, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hn3 := hF.hG.1.1
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8⟩ := leaf_facts (n := (Qof P).n) (C := 2 ^ R.μ)
    Nat.one_le_two_pow (by omega) hF.hwf hxL
  have hNP := hF.hNP
  have hK60 := leaves_length_le hF
  have hroom := hI.room
  have hpcL : ((R.leaves P).length - i) * lfB pc ≥ lfB pc := by
    have : 1 ≤ (R.leaves P).length - i := by omega
    nlinarith
  obtain ⟨pos, γ, hpos, hgap, hst⟩ := hI.st
  have hdrop : (R.leaves P).drop i = x :: (R.leaves P).drop (i + 1) := by
    rw [hx, List.getD_eq_getElem _ _ hi]; exact List.drop_eq_getElem_cons hi
  rw [hdrop] at hgap
  obtain ⟨g1, g2, g3⟩ := hgap
  have E := hI.env
  have hT := E.table hF
  obtain ⟨t1, t2, t3⟩ := hT i hi
  rw [← hx] at t1 t2 t3
  have t3' : e.nmem (R.T + 3 * i + 1 + 1) = x.2.2 := t3
  have hTA := hF.hTA
  have hAW : e.nreg ALLOC ≤ W := by omega
  have hTW : R.T + 3 * (R.leaves P).length ≤ W := by have := E.alloc; omega
  -- load the leaf
  obtain ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁, f₁⟩ : ∃ e₁ k₁, Exec P W lfLoad e e₁ k₁ ∧ k₁ = 5 ∧
      e₁.nreg 219226 = x.1 ∧ e₁.nreg 219227 = x.2.1 ∧ e₁.nreg 219228 = x.2.2 ∧ e₁.nmem = e.nmem ∧
      FrameM (fun q => decide (219226 ≤ q ∧ q ≤ 219229)) e e₁ := by
    obtain ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁⟩ : ∃ e₁ k₁, Exec P W lfLoad e e₁ k₁ ∧ k₁ = 5 ∧
        e₁.nreg 219226 = x.1 ∧ e₁.nreg 219227 = x.2.1 ∧ e₁.nreg 219228 = x.2.2 ∧
        e₁.nmem = e.nmem := by
      have hw := hI.wb
      unfold lfLoad
      exec_block
      all_goals try (config_simp; (try simp only [hI.r24, E.r230]); omega)
    exact ⟨e₁, k₁, ex₁, hk₁, v26, v27, v28, m₁, exec_frameM ex₁ (by decide)⟩
  have fr₁ : Frame drvBands e e₁ k₁ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₁ m₁ k₁
  have hA₁ : e₁.nreg ALLOC = e.nreg ALLOC := f₁.1 ALLOC (by decide)
  have E₁ : REnv R e₁ := E.keep (fun q hq => f₁.1 q (by
    obtain ⟨-, -, -, b4, -⟩ := envRegs_band2 q hq
    simp only [decide_eq_false_iff_not]; omega)) (fun a _ => by rw [m₁]) (by omega)
  have u₁ : ∀ q, (q < 219226 ∨ 219229 < q) → e₁.nreg q = e.nreg q := fun q hq => f₁.1 q (by
    simp only [decide_eq_false_iff_not]; omega)
  have hw₁ := ex₁.wb_right
  have p₁ : e₁.nreg 219221 = pos := by rw [u₁ _ (by omega), hpos]
  -- the connector
  obtain ⟨e₃, k₃, γ₁, ex₃, hk₃, hw₃, E₃, A₃, hγ₁, hγ₁', u₃, o₃, fr₃⟩ : ∃ e₃ k₃ γ₁,
      Exec P W (conS sp sM) e₁ e₃ k₃ ∧ k₃ ≤ pc + 10 ∧ WordsBounded W e₃ ∧ REnv R e₃ ∧
      AccOK P R e₃ x.1 γ₁ ∧ R.γ₀ ≤ γ₁ ∧ γ₁ ≤ R.γ₀ + 2 * i ∧
      (∀ q, q = 219004 ∨ q = 219220 ∨ q = 219221 ∨ q = 219224 ∨ q = 219226 ∨ q = 219227 ∨
        q = 219228 → e₃.nreg q = e₁.nreg q) ∧
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → e₃.nreg q = e₁.nreg q) ∧
      Frame drvBands e₁ e₃ k₃ := by
    by_cases hlt : pos < x.1
    · obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, f₂⟩ : ∃ e₂ k₂, Exec P W
          (block [.copyN 219240 219221, .subN 219241 219226 219221, .constN 219242 0,
            .constN 219243 0]) e₁ e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
          e₂.nreg 219241 = x.1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
          e₂.nmem = e₁.nmem ∧ FrameM (fun q => decide (219240 ≤ q ∧ q ≤ 219243)) e₁ e₂ := by
        obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂⟩ : ∃ e₂ k₂, Exec P W
            (block [.copyN 219240 219221, .subN 219241 219226 219221, .constN 219242 0,
              .constN 219243 0]) e₁ e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
            e₂.nreg 219241 = x.1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
            e₂.nmem = e₁.nmem := by
          exec_block
          all_goals try (config_simp; (try simp only [p₁, v26]); omega)
          refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> simp only [p₁, v26]
        exact ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, exec_frameM ex₂ (by decide)⟩
      have fr₂ : Frame drvBands e₁ e₂ k₂ := frame_band (fun q hq => by
        simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₂ m₂ k₂
      have hA₂ : e₂.nreg ALLOC = e₁.nreg ALLOC := f₂.1 ALLOC (by decide)
      have E₂ : REnv R e₂ := E₁.keep (fun q hq => f₂.1 q (by
        obtain ⟨-, -, -, -, b5⟩ := envRegs_band2 q hq
        simp only [decide_eq_false_iff_not]; omega)) (fun a _ => by rw [m₂]) (by omega)
      have u₂ : ∀ q, (q < 219240 ∨ 219243 < q) → e₂.nreg q = e₁.nreg q := fun q hq => f₂.1 q (by
        simp only [decide_eq_false_iff_not]; omega)
      have hacc : (e₂.nreg 219222 = 0 ∧ pos = 0 ∧ (if pos = 0 then R.γ₀ else γ) = R.γ₀) ∨
          (0 < pos ∧ AccOK P R e₂ pos (if pos = 0 then R.γ₀ else γ)) := by
        rcases hst with ⟨-, hp0, h22⟩ | ⟨-, hp0, A, -⟩
        · left; refine ⟨?_, hp0, by rw [ite_eq_left hp0]⟩
          rw [u₂ _ (by omega), u₁ _ (by omega), h22]
        · right; refine ⟨hp0, ?_⟩
          rw [ite_eq_right (by omega)]
          exact (A.keep fr₁ fun q hq => u₁ q (by omega)).keep fr₂ fun q hq => u₂ q (by omega)
      have hγb : R.γ₀ ≤ (if pos = 0 then R.γ₀ else γ) ∧
          (if pos = 0 then R.γ₀ else γ) + 1 ≤ R.γ₀ + 2 * i + 1 := by
        rcases hst with ⟨-, hp0, -⟩ | ⟨hi0, hp0, -, h1, h2, -⟩
        · rw [ite_eq_left hp0]; omega
        · rw [ite_eq_right (by omega)]; omega
      obtain ⟨e₃, k₃, ex₃, hk₃, E₃, A₃, u₃, fr₃⟩ := pcS_exec (P := P) (W := W) hsp hM hF e₂
        ex₂.wb_right E₂ w40 w41 w42 w43 hacc hγb.1 (by omega) (by omega)
        (by rw [hNP]; omega) (by omega) (fun h => absurd h (by norm_num))
        (fun _ => by omega)
        (fun hp => by
          rcases hst with ⟨-, hp0, -⟩ | ⟨-, -, -, -, -, hj⟩
          · omega
          · exact hj)
        (by have h1 : lfB pc = 2 * pc + 30 := rfl; rw [hA₂, hA₁]; omega)
      refine ⟨e₃, k₂ + k₃ + 1, if pos = 0 then R.γ₀ else γ + 1, .ifLtN_true (by
        rw [p₁, v26]; exact hlt) (.seq ex₂ ex₃), by omega, ex₃.wb_right, E₃,
        by rw [show pos + (x.1 - pos) = x.1 by omega] at A₃; split_ifs at A₃ ⊢ <;> exact A₃,
        ?_, ?_, fun q hq => ?_, fun q hq hq' => ?_, ?_⟩
      · split_ifs <;> omega
      · rcases hst with ⟨hi0, hp0, -⟩ | ⟨-, hp0, -, -, h2, -⟩
        · rw [ite_eq_left hp0]; omega
        · rw [ite_eq_right (by omega)]; omega
      · rw [u₃ q (by simp only [bandOf, bDownDrv]; omega) (by omega), u₂ q (by omega)]
      · rw [u₃ q hq (by omega), u₂ q (by omega)]
      · have := fr₂.trans fr₃
        rw [Finset.union_self] at this
        exact this.mono (le_refl _) (by omega)
    · have heq : pos = x.1 := by omega
      rcases hst with ⟨-, hp0, -⟩ | ⟨hi0, hp0, A, h1, h2, -⟩
      · omega
      refine ⟨e₁, 0 + 2, γ, .ifLtN_false (by rw [p₁, v26]; exact hlt) (.skip hw₁), by omega, hw₁,
        E₁, by rw [← heq]; exact A.keep fr₁ fun q hq => u₁ q (by omega), h1, by omega,
        fun q _ => rfl, fun q _ _ => rfl, ?_⟩
      exact frame_refl _ _ _
  have hA₃ := fr₃.2.2.2.2.2.2
  have p26 : e₃.nreg 219226 = x.1 := by rw [u₃ _ (by simp), v26]
  have p27 : e₃.nreg 219227 = x.2.1 := by rw [u₃ _ (by simp), v27]
  have p28 : e₃.nreg 219228 = x.2.2 := by rw [u₃ _ (by simp), v28]
  -- the leaf
  obtain ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄, f₄⟩ : ∃ e₄ k₄, Exec P W
      (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1, .copyN 219243 219228])
      e₃ e₄ k₄ ∧ k₄ = 4 ∧ e₄.nreg 219240 = x.1 ∧ e₄.nreg 219241 = x.2.1 ∧ e₄.nreg 219242 = 1 ∧
      e₄.nreg 219243 = x.2.2 ∧ e₄.nmem = e₃.nmem ∧
      FrameM (fun q => decide (219240 ≤ q ∧ q ≤ 219243)) e₃ e₄ := by
    obtain ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄⟩ : ∃ e₄ k₄, Exec P W
        (block [.copyN 219240 219226, .copyN 219241 219227, .constN 219242 1,
          .copyN 219243 219228]) e₃ e₄ k₄ ∧ k₄ = 4 ∧ e₄.nreg 219240 = x.1 ∧
        e₄.nreg 219241 = x.2.1 ∧ e₄.nreg 219242 = 1 ∧ e₄.nreg 219243 = x.2.2 ∧
        e₄.nmem = e₃.nmem := by
      have hw := hw₃
      exec_block
      all_goals try (config_simp; (try simp only [p26, p27, p28]); omega)
      refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> simp only [p26, p27, p28]
    exact ⟨e₄, k₄, ex₄, hk₄, w40, w41, w42, w43, m₄, exec_frameM ex₄ (by decide)⟩
  have fr₄ : Frame drvBands e₃ e₄ k₄ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₄ m₄ k₄
  have hA₄ : e₄.nreg ALLOC = e₃.nreg ALLOC := f₄.1 ALLOC (by decide)
  have E₄ : REnv R e₄ := E₃.keep (fun q hq => f₄.1 q (by
    obtain ⟨-, -, -, -, b5⟩ := envRegs_band2 q hq
    simp only [decide_eq_false_iff_not]; omega)) (fun a _ => by rw [m₄]) (by omega)
  have u₄ : ∀ q, (q < 219240 ∨ 219243 < q) → e₄.nreg q = e₃.nreg q := fun q hq => f₄.1 q (by
    simp only [decide_eq_false_iff_not]; omega)
  have A₄ : AccOK P R e₄ x.1 γ₁ := A₃.keep fr₄ fun q hq => u₄ q (by omega)
  obtain ⟨e₅, k₅, ex₅, hk₅, E₅, A₅, u₅, fr₅⟩ := pcS_exec (P := P) (W := W) hsp hM hF e₄
    ex₄.wb_right E₄ w40 w41 w42 w43 (Or.inr ⟨by omega, A₄⟩) hγ₁ (by omega) x2
    (by rw [hNP]; omega) (by omega) (fun _ => ⟨x3, x4, x6⟩) (fun h => absurd h (by norm_num))
    (fun _ => x7)
    (by have h1 : lfB pc = 2 * pc + 30 := rfl; rw [hA₄]; omega)
  rw [ite_eq_right (by omega)] at A₅
  have hA₅ := fr₅.2.2.2.2.2.2
  have hw₅ := ex₅.wb_right
  have s26 : e₅.nreg 219226 = x.1 := by
    rw [u₅ _ (by simp [bandOf, bDownDrv]) (by omega), u₄ _ (by omega), p26]
  have s27 : e₅.nreg 219227 = x.2.1 := by
    rw [u₅ _ (by simp [bandOf, bDownDrv]) (by omega), u₄ _ (by omega), p27]
  have s20 : e₅.nreg 219220 = i := by
    rw [u₅ _ (by simp [bandOf, bDownDrv]) (by omega), u₄ _ (by omega), u₃ _ (by simp),
      u₁ _ (by omega), hI.r20]
  have s24 : e₅.nreg 219224 = R.T + 3 * i := by
    rw [u₅ _ (by simp [bandOf, bDownDrv]) (by omega), u₄ _ (by omega), u₃ _ (by simp),
      u₁ _ (by omega), hI.r24]
  have s04 : e₅.nreg 219004 = (R.leaves P).length := by
    rw [u₅ _ (by simp [bandOf, bDownDrv]) (by omega), u₄ _ (by omega), u₃ _ (by simp),
      u₁ _ (by omega), hI.r04]
  have hNPW : R.NP ≤ W := by have := hw₅.1 219201; rw [E₅.r201] at this; exact this
  -- advance
  obtain ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆, f₆⟩ : ∃ e₆ k₆, Exec P W lfAdv e₅ e₆ k₆ ∧ k₆ = 3 ∧
      e₆.nreg 219221 = x.1 + x.2.1 ∧ e₆.nreg 219220 = i + 1 ∧ e₆.nreg 219224 = R.T + 3 * (i + 1) ∧
      e₆.nmem = e₅.nmem ∧
      FrameM (fun q => decide (q = 219220 ∨ q = 219221 ∨ q = 219224)) e₅ e₆ := by
    obtain ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆⟩ : ∃ e₆ k₆, Exec P W lfAdv e₅ e₆ k₆ ∧ k₆ = 3 ∧
        e₆.nreg 219221 = x.1 + x.2.1 ∧ e₆.nreg 219220 = i + 1 ∧
        e₆.nreg 219224 = R.T + 3 * (i + 1) ∧ e₆.nmem = e₅.nmem := by
      have hw := hw₅
      unfold lfAdv
      exec_block
      all_goals try (config_simp; (try simp only [s26, s27, s20, s24, E₅.r230, E₅.r231]); omega)
      refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;>
        simp only [s26, s27, s20, s24, E₅.r230, E₅.r231]; ring
    exact ⟨e₆, k₆, ex₆, hk₆, y21, y20, y24, m₆, exec_frameM ex₆ (by decide)⟩
  have fr₆ : Frame drvBands e₅ e₆ k₆ := frame_band (fun q hq => by
    simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₆ m₆ k₆
  have hA₆ : e₆.nreg ALLOC = e₅.nreg ALLOC := f₆.1 ALLOC (by decide)
  have E₆ : REnv R e₆ := E₅.keep (fun q hq => f₆.1 q (by
    obtain ⟨b1, b2, -, b4, -⟩ := envRegs_band2 q hq
    simp only [decide_eq_false_iff_not]; omega)) (fun a _ => by rw [m₆]) (by omega)
  have A₆ : AccOK P R e₆ (x.1 + x.2.1) (γ₁ + 1) := A₅.keep fr₆ fun q hq => f₆.1 q (by
    simp only [decide_eq_false_iff_not]; omega)
  refine ⟨e₆, k₁ + (k₃ + ((k₄ + k₅) + k₆)), .seq ex₁ (.seq ex₃ (.seq (.seq ex₄ ex₅) ex₆)),
    ⟨ex₆.wb_right, fun q hq hq' => ?_, y20, by rw [f₆.1 _ (by decide), s04], E₆, y24, by omega,
      ?_,
      x.1 + x.2.1, γ₁ + 1, y21, g3, Or.inr ⟨by omega, by omega, A₆, by omega, by omega, x8⟩⟩,
    by unfold lfB; omega, ?_⟩
  · rw [f₆.1 q (by simp only [decide_eq_false_iff_not]; omega),
      u₅ q hq (by omega), u₄ q (by omega), o₃ q hq hq', u₁ q (by omega)]
    exact hI.keep q hq hq'
  · have h1 : lfB pc = 2 * pc + 30 := rfl
    have e1 : ((R.leaves P).length - i) * lfB pc =
        ((R.leaves P).length - (i + 1)) * lfB pc + lfB pc := by
      rw [show (R.leaves P).length - i = (R.leaves P).length - (i + 1) + 1 by omega, Nat.succ_mul]
    have := fr₁.2.2.2.2.2.2
    omega
  · have := (((fr₁.trans fr₃).trans fr₄).trans fr₅).trans fr₆
    simp only [Finset.union_self] at this
    exact this.mono (le_refl _) (by omega)


/-- **The leaf loop.** -/
theorem lfLoop_exec {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ} (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Rb : ℕ} (e : Config)
    (hI : LInv P W R V (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) Rb 0 e) :
    ∃ e' k, Exec P W (lfLoop sp sM) e e' k ∧
      LInv P W R V (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) Rb (R.leaves P).length e' ∧
      k ≤ (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ)) + 2) * (R.leaves P).length + 2 ∧
      Frame drvBands e e' k := by
  obtain ⟨e', k, ex, hI', hk, fr⟩ := forLoopF (P := P) (W := W) (ir := 219220) (nr := 219004)
    (B := drvBands) (LInv P W R V (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) Rb)
    (lfB (pcB κP (κ 130) κs (lemma41Nat R.μ))) (R.leaves P).length
    (fun j c h => ⟨h.wb, h.r20, h.r04⟩)
    (fun j c hj h => lfBody_exec hsp hM hF c hj h) hI (Nat.zero_le _)
  exact ⟨e', k, ex, hI', by simpa using hk, fr⟩


/-- **The last connector.** -/
theorem finCon_exec {sp sM : Stmt} {κP κs : ℕ} {κ : ℕ → ℕ} (hsp : PcMeets O sp κP)
    (hM : L41.MergeMeets sM κ (L41.scF κs) (L41.scG κs) cutGran (gradeCtx O) OkModel)
    (hF : RFacts O P W R) {V : ℕ → ℕ} {Lb : ℕ} (e : Config)
    (hI : LInv P W R V Lb (pcB κP (κ 130) κs (lemma41Nat R.μ) + 2) (R.leaves P).length e) :
    ∃ e' k γ, Exec P W (finCon sp sM) e e' k ∧ k ≤ pcB κP (κ 130) κs (lemma41Nat R.μ) + 6 ∧
      WordsBounded W e' ∧ REnv R e' ∧ AccOK P R e' (R.NP - 1) γ ∧ R.γ₀ ≤ γ ∧
      γ ≤ R.γ₀ + 2 * (R.leaves P).length ∧
      (∀ q, bandOf q = bDownDrv → (q < 218000 ∨ 220000 ≤ q) → e'.nreg q = e.nreg q) ∧
      Frame drvBands e e' k := by
  set pc := pcB κP (κ 130) κs (lemma41Nat R.μ) with hpc
  have E := hI.env
  have hw := hI.wb
  have hNP3 := hF.hNP3
  have hroom := hI.room
  obtain ⟨pos, γ, hpos, hgap, hst⟩ := hI.st
  rw [List.drop_length] at hgap
  obtain ⟨g1, g2⟩ := hgap
  by_cases hlt : pos < R.NP - 1
  · obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, f₂⟩ : ∃ e₂ k₂, Exec P W
        (block [.copyN 219240 219221, .subN 219241 219223 219221, .constN 219242 0,
          .constN 219243 0]) e e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
        e₂.nreg 219241 = R.NP - 1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
        e₂.nmem = e.nmem ∧ FrameM (fun q => decide (219240 ≤ q ∧ q ≤ 219243)) e e₂ := by
      obtain ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂⟩ : ∃ e₂ k₂, Exec P W
          (block [.copyN 219240 219221, .subN 219241 219223 219221, .constN 219242 0,
            .constN 219243 0]) e e₂ k₂ ∧ k₂ = 4 ∧ e₂.nreg 219240 = pos ∧
          e₂.nreg 219241 = R.NP - 1 - pos ∧ e₂.nreg 219242 = 0 ∧ e₂.nreg 219243 = 0 ∧
          e₂.nmem = e.nmem := by
        exec_block
        all_goals try (config_simp; (try simp only [hpos, E.r223]); omega)
        refine ⟨rfl, ?_, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> simp only [hpos, E.r223]
      exact ⟨e₂, k₂, ex₂, hk₂, w40, w41, w42, w43, m₂, exec_frameM ex₂ (by decide)⟩
    have fr₂ : Frame drvBands e e₂ k₂ := frame_band (fun q hq => by
      simp only [decide_eq_true_eq] at hq; simp only [bandOf, bDownDrv]; omega) f₂ m₂ k₂
    have hA₂ : e₂.nreg ALLOC = e.nreg ALLOC := f₂.1 ALLOC (by decide)
    have E₂ : REnv R e₂ := E.keep (fun q hq => f₂.1 q (by
      obtain ⟨-, -, -, -, b5⟩ := envRegs_band2 q hq
      simp only [decide_eq_false_iff_not]; omega)) (fun a _ => by rw [m₂]) (by omega)
    have u₂ : ∀ q, (q < 219240 ∨ 219243 < q) → e₂.nreg q = e.nreg q := fun q hq => f₂.1 q (by
      simp only [decide_eq_false_iff_not]; omega)
    have hacc : (e₂.nreg 219222 = 0 ∧ pos = 0 ∧ (if pos = 0 then R.γ₀ else γ) = R.γ₀) ∨
        (0 < pos ∧ AccOK P R e₂ pos (if pos = 0 then R.γ₀ else γ)) := by
      rcases hst with ⟨-, hp0, h22⟩ | ⟨-, hp0, A, -⟩
      · left; refine ⟨?_, hp0, by rw [ite_eq_left hp0]⟩
        rw [u₂ _ (by omega), h22]
      · right; refine ⟨hp0, ?_⟩
        rw [ite_eq_right (by omega)]
        exact A.keep fr₂ fun q hq => u₂ q (by omega)
    have hK60 := leaves_length_le hF
    have hγb : R.γ₀ ≤ (if pos = 0 then R.γ₀ else γ) ∧
        (if pos = 0 then R.γ₀ else γ) + 1 ≤ R.γ₀ + 2 * (R.leaves P).length + 1 := by
      rcases hst with ⟨-, hp0, -⟩ | ⟨hi0, hp0, -, h1, h2, -⟩
      · rw [ite_eq_left hp0]; omega
      · rw [ite_eq_right (by omega)]; omega
    obtain ⟨e₃, k₃, ex₃, hk₃, E₃, A₃, u₃, fr₃⟩ := pcS_exec (P := P) (W := W) hsp hM hF e₂
      ex₂.wb_right E₂ w40 w41 w42 w43 hacc hγb.1 (by omega) (by omega) (by omega) (by omega)
      (fun h => absurd h (by norm_num)) (fun _ => by omega)
      (fun hp => by
        rcases hst with ⟨-, hp0, -⟩ | ⟨-, -, -, -, -, hj⟩
        · omega
        · exact hj)
      (by rw [hA₂]; omega)
    refine ⟨e₃, k₂ + k₃ + 1, if pos = 0 then R.γ₀ else γ + 1, .ifLtN_true (by
      rw [hpos, E.r223]; exact hlt) (.seq ex₂ ex₃), by omega, ex₃.wb_right, E₃,
      by rw [show pos + (R.NP - 1 - pos) = R.NP - 1 by omega] at A₃; split_ifs at A₃ ⊢ <;> exact A₃,
      ?_, ?_, fun q hq hq' => by rw [u₃ q hq (by omega), u₂ q (by omega)], ?_⟩
    · split_ifs <;> omega
    · rcases hst with ⟨hi0, hp0, -⟩ | ⟨-, hp0, -, -, h2, -⟩
      · rw [ite_eq_left hp0]; omega
      · rw [ite_eq_right (by omega)]; omega
    · have := fr₂.trans fr₃
      rw [Finset.union_self] at this
      exact this.mono (le_refl _) (by omega)
  · have heq : pos = R.NP - 1 := by omega
    rcases hst with ⟨-, hp0, -⟩ | ⟨hi0, hp0, A, h1, h2, -⟩
    · omega
    refine ⟨e, 0 + 2, γ, .ifLtN_false (by rw [hpos, E.r223]; exact hlt) (.skip hw), by omega, hw,
      E, by rw [← heq]; exact A, h1, by omega, fun q _ _ => rfl, frame_refl _ _ _⟩

end exec

end

end DrvG

end Chazelle.Core
