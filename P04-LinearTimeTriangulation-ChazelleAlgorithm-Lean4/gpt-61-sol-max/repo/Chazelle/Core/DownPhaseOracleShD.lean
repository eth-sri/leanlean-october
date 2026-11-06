module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleShC

/-!
# WP-M (E7-B, RAM part 11): one sub-query of the interior shooter

A sub-query serves a subarc of `L ≤ n - 1` walk edges of the interior walk from `⟨u, sh⟩` to
`⟨(u + ee) mod n, eh⟩` (registers `170033 … 170037`, `SubOK`): `sqS sh` builds the chain
`ch Q u L` and its descriptor (`chainI`), then shoots at its one chain arc (`τ ≤ L`,
`chainArcs_one`) or at its two chain arcs meeting at the top (`L < τ`, `chainArcs_two`).
`sqS_exec`: the running best hit then describes the first hit on the union with the point set
`oset (interiorWalk Q) u x (ee + t₂)` of the subarc.
-/


namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim
open Chazelle.Visibility (rayPt)

@[expose] public section

/-! ## The programs -/

/-- The one chain arc `⟨6 + τ, sh⟩ … ⟨6 + τ + ee, eh⟩`. -/
def arcOne : Stmt :=
  block [.constN 170133 6, .addN 140001 170133 170077, .copyN 140002 170034,
    .addN 140003 140001 170035, .copyN 140004 170036]

/-- The first of two chain arcs: `⟨6 + τ, sh⟩ … ⟨2 L + 6, 0⟩`. -/
def arcTwoA : Stmt :=
  block [.constN 170133 6, .addN 140001 170133 170077, .copyN 140002 170034,
    .addN 140003 170089 170133, .constN 140004 0]

/-- The second of two chain arcs: `⟨6, 0⟩ … ⟨6 + (ee - (2 L - τ)), eh⟩`. -/
def arcTwoB : Stmt :=
  block [.constN 170133 6, .copyN 140001 170133, .constN 140002 0, .subN 170142 170089 170077,
    .subN 170143 170035 170142, .addN 140003 170133 170143, .copyN 140004 170036]

/-- **A sub-query of the interior shooter.** -/
def sqS (sh : Stmt) : Stmt :=
  .seq chainI (.ifLtN 170037 170077
    (.seq arcTwoA (.seq (shotI sh) (.seq arcTwoB (shotI sh))))
    (.seq arcOne (shotI sh)))

/-- The registers of band `17` a sub-query writes. -/
def BSQ (r : ℕ) : Bool :=
  decide (170038 ≤ r ∧ r < 170042) || decide (170046 ≤ r ∧ r < 170092) ||
    decide (170130 ≤ r ∧ r < 170144)

/-- The registers an arc block writes. -/
def Barc (r : ℕ) : Bool :=
  decide (140000 ≤ r ∧ r < 140014) || decide (r = 170133 ∨ r = 170142 ∨ r = 170143)

theorem wr_arcOne : wr Barc arcOne = true := by decide
theorem wr_arcTwoA : wr Barc arcTwoA = true := by decide
theorem wr_arcTwoB : wr Barc arcTwoB = true := by decide

theorem barc_io {r : ℕ} (h : Barc r = true) : bandOf r ∈ ioBands ∧ r ≠ ALLOC :=
  io_of_band (by ram_grind)

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

section
variable (c : Config) (hw : WordsBounded W c)
include hw
theorem arcOne_exec {τ sh ee eh : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (hW : 6 + τ + ee ≤ W) :
    ∃ c' k, Exec P W arcOne c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧ c'.nreg 140002 = sh ∧
      c'.nreg 140003 = 6 + τ + ee ∧ c'.nreg 140004 = eh ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcOne c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧
      c'.nreg 140002 = sh ∧ c'.nreg 140003 = 6 + τ + ee ∧ c'.nreg 140004 = eh by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcOne⟩
  unfold arcOne
  exec_block
  · omega
  · omega_nf
  · omega_nf
  ram_simp

theorem arcTwoA_exec {τ sh L : ℕ}
    (h77 : c.nreg 170077 = τ) (h34 : c.nreg 170034 = sh) (h89 : c.nreg 170089 = 2 * L)
    (hW : 2 * L + 6 ≤ W) (hτ : 6 + τ ≤ W) :
    ∃ c' k, Exec P W arcTwoA c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧ c'.nreg 140002 = sh ∧
      c'.nreg 140003 = 2 * L + 6 ∧ c'.nreg 140004 = 0 ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoA c c' k ∧ k = 5 ∧ c'.nreg 140001 = 6 + τ ∧
      c'.nreg 140002 = sh ∧ c'.nreg 140003 = 2 * L + 6 ∧ c'.nreg 140004 = 0 by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcTwoA⟩
  unfold arcTwoA
  exec_block
  · omega
  all_goals simp_all

theorem arcTwoB_exec {τ ee eh L : ℕ}
    (h77 : c.nreg 170077 = τ) (h35 : c.nreg 170035 = ee) (h36 : c.nreg 170036 = eh)
    (h89 : c.nreg 170089 = 2 * L) (hW : 6 + ee ≤ W) :
    ∃ c' k, Exec P W arcTwoB c c' k ∧ k = 7 ∧ c'.nreg 140001 = 6 ∧ c'.nreg 140002 = 0 ∧
      c'.nreg 140003 = 6 + (ee - (2 * L - τ)) ∧ c'.nreg 140004 = eh ∧ FrameB Barc c c' := by
  suffices h : ∃ c' k, Exec P W arcTwoB c c' k ∧ k = 7 ∧ c'.nreg 140001 = 6 ∧
      c'.nreg 140002 = 0 ∧ c'.nreg 140003 = 6 + (ee - (2 * L - τ)) ∧ c'.nreg 140004 = eh by
    obtain ⟨c', k, e, h1, h2, h3, h4, h5⟩ := h
    exact ⟨c', k, e, h1, h2, h3, h4, h5, exec_frameB e wr_arcTwoB⟩
  unfold arcTwoB
  exec_block
  · omega
  · omega
  · omega_nf
  omega_nf


end

/-- The frame of `chainI`. -/
theorem frame_chainI {c c' : Config} {k : ℕ} (hk : 14 ≤ k) (hA : c'.nreg ALLOC = c.nreg ALLOC + 6)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a)
    (hr : ∀ r, Bchain r = false → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hrr : ∀ r, Bchain r = false → c'.rreg r = c.rreg r) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : Frame ioBands c c' k := by
  have hB : ∀ r, Bchain r = true → bandOf r ∈ ioBands := fun r h => (io_of_band (by
    ram_grind)).1
  refine ⟨fun r hr' ha => ?_, fun r hr' => ?_, hm, fun a _ => by rw [hrm], ho, by omega,
    by omega⟩
  all_goals grind

/-- The subarc's offsets: its end offset is at most `L`. -/
theorem sub_y_le {Q : Polygon} {u L sh ee eh : ℕ} (h : SubOK Q u L sh ee eh) :
    (ee : ℝ) + (interiorModel Q).param Q ⟨(u + ee) % Q.n, eh⟩ ≤ L := by
  rcases h.hee with ⟨h0, h1⟩ | ⟨h0, h1, -⟩
  · simp_all
  · have := h.he.2.1
    aesop (add safe (by nlinarith))

/-- **A sub-query of the interior shooter.** -/
theorem sqS_exec {sh : Stmt} {F : ℕ → ℕ}
    (hsh : ShooterOK sh oracleBands F (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) {u L sh₀ ee eh : ℕ}
    (h33 : c.nreg 170033 = u) (h34 : c.nreg 170034 = sh₀) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h37 : c.nreg 170037 = L)
    (hsub : SubOK (Qof P) u L sh₀ ee eh) (hLγ : L ≤ s.γ)
    (ho1 : |(s.o.eval (Qof P)).1| ≤ Jordan.coordBound (Qof P))
    (ho2 : |(s.o.eval (Qof P)).2| ≤ Jordan.coordBound (Qof P)) (hol : s.o.Lt P.n)
    (hoA : s.o.eval (Qof P) ∉ oset (interiorWalk (Qof P)) u
      ((interiorModel (Qof P)).param (Qof P) ⟨u, sh₀⟩)
      (ee + (interiorModel (Qof P)).param (Qof P) ⟨(u + ee) % (Qof P).n, eh⟩))
    {Sp : Set Point} (hB : BestI P c Sp (s.o.eval (Qof P)) (dirOf s.dir))
    (hroom : c.nreg ALLOC + 2 * F s.γ + 1204 * Nat.log 2 (2 * L) + 4500 ≤ W) :
    ∃ c' k, Exec P W (sqS sh) c c' k ∧ k ≤ 2 * F s.γ + 1204 * Nat.log 2 (2 * L) + 4500 ∧
      BestI P c' (Sp ∪ oset (interiorWalk (Qof P)) u
        ((interiorModel (Qof P)).param (Qof P) ⟨u, sh₀⟩)
        (ee + (interiorModel (Qof P)).param (Qof P) ⟨(u + ee) % (Qof P).n, eh⟩))
        (s.o.eval (Qof P)) (dirOf s.dir) ∧ SEnv P W O s c' ∧ Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → BSQ r = false → c'.nreg r = c.nreg r) := by
  have hQ : (Qof P).n = P.n := qn'
  have hW := hS.hW
  unfold hostWords at hW
  have h1 := hsub.h1
  have h2 := hsub.h2
  have hu := hsub.hu
  have hee := sub_ee_le hsub
  have hcap : L ≤ 2 ^ (s.m₀ s.h - 1) := hLγ.trans hS.cap
  set x := (interiorModel (Qof P)).param (Qof P) ⟨u, sh₀⟩ with hx
  set y := (ee : ℝ) + (interiorModel (Qof P)).param (Qof P) ⟨(u + ee) % (Qof P).n, eh⟩ with hy
  have hyL : y ≤ L := sub_y_le hsub
  set C := ch (Qof P) u L h1 h2 with hCd
  have hsubC : oset (interiorWalk (Qof P)) u x y ⊆ C.set := oset_sub_set hu h1 h2 hyL
  -- the chain
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', C₁, d78, dA, dm, dr, drr, drm, dout⟩ := chainI_exec c hw hS h33 h37
    (by omega) h1 h2 hcap (by omega)
  have F₁ : Frame ioBands c c₁ k₁ := frame_chainI hk₁' dA dm dr drr drm dout
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, 170000 ≤ r → r < 180000 → BSQ r = false → c₁.nreg r = c.nreg r :=
    fun r r1 r2 hr => dr r (by
      simp only [BSQ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
      simp only [Bchain, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
      (by omega_nf)
  have hB₁ : BestI P c₁ Sp (s.o.eval (Qof P)) (dirOf s.dir) := hB.keep (fun r r1 r2 => dr r
    (by simp only [Bchain, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
    (by omega_nf))
  have b34 : c₁.nreg 170034 = sh₀ := by ram_simp
  have b35 : c₁.nreg 170035 = ee := by ram_simp
  have b36 : c₁.nreg 170036 = eh := by ram_simp
  have hτ : tau (Qof P) u L h1 h2 < 2 * L := tau_lt
  -- the arc blocks keep the chain state and the best hit
  have keepArc : ∀ {d d' : Config}, FrameB Barc d d' → CEnv P W O s u L h1 h2 d →
      CEnv P W O s u L h1 h2 d' := fun F hC => hC.keep (fun r hr => F.1 r (by
        unfold CRegs at hr; simp only [Barc, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
      (fun a _ => by rw [F.2.2.1]) (by rw [F.1 _ (by decide)])
  have keepArcB : ∀ {d d' : Config} {S' : Set Point}, FrameB Barc d d' →
      BestI P d S' (s.o.eval (Qof P)) (dirOf s.dir) →
      BestI P d' S' (s.o.eval (Qof P)) (dirOf s.dir) := fun F hb => hb.keep (fun r r1 r2 =>
        F.1 r (by simp only [Barc, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
  have bandArc : ∀ {d d' : Config}, FrameB Barc d d' → ∀ r, 170000 ≤ r → r < 180000 →
      BSQ r = false → d'.nreg r = d.nreg r := fun F r r1 r2 hr => F.1 r (by
        simp only [BSQ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp only [Barc, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have bandShot : ∀ {d d' : Config}, (∀ r, 170000 ≤ r → r < 180000 → Bupd r = false →
      d'.nreg r = d.nreg r) → ∀ r, 170000 ≤ r → r < 180000 → BSQ r = false →
      d'.nreg r = d.nreg r := fun F r r1 r2 hr => F r r1 r2 (by
        simp only [BSQ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        simp only [Bupd, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  by_cases hs : tau (Qof P) u L h1 h2 ≤ L
  · -- one chain arc
    have hb : ¬ c₁.nreg 170037 < c₁.nreg 170077 := by rw [C₁.r37, C₁.r77]; omega
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, Fa⟩ := arcOne_exec (P := P) c₁ w₁ C₁.r77 b34 b35 b36
      (by omega)
    have C₂ := keepArc Fa C₁
    have harc := chainArcs_one hsub hs hLγ
    obtain ⟨c₃, k₃, e₃, hk₃, hB₃, C₃, F₃, g₃⟩ := shotI_exec hsh c₂ e₂.wb_right C₂
      (sa := ⟨6 + tau (Qof P) u L h1 h2, sh₀⟩) (ea := ⟨6 + tau (Qof P) u L h1 h2 + ee, eh⟩)
      a1 a2 a3 a4 harc hsubC ho1 ho2 hol hoA (keepArcB Fa hB₁) (by
        rw [Fa.1 _ (by decide), dA]; omega)
    have ex : Exec P W (sqS sh) c c₃ (k₁ + (k₂ + k₃ + 2)) :=
      .seq e₁ (.ifLtN_false hb (.seq e₂ e₃))
    have Fa' : Frame ioBands c₁ c₂ k₂ := frameIO_of_frameB (fun r h => barc_io h) Fa k₂
    refine ⟨c₃, _, ex, by omega, hB₃, C₃.env, ((F₁.trans Fa').trans F₃).mono (by simp)
      (by omega), fun r r1 r2 hr => ?_⟩
    rw [bandShot g₃ r r1 r2 hr, bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]
  · -- two chain arcs meeting at the top
    push Not at hs
    have hb : c₁.nreg 170037 < c₁.nreg 170077 := by rw [C₁.r37, C₁.r77]; exact hs
    obtain ⟨harcA, harcB⟩ := chainArcs_two hsub hs hLγ
    set L₁ := 2 * L - tau (Qof P) u L h1 h2 with hL₁
    have hle : L₁ ≤ ee := by rcases hsub.hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
    have hx1 : x ≤ (L₁ : ℝ) := by
      have := hsub.hs.2.1
      have : (1 : ℝ) ≤ L₁ := by exact_mod_cast (show 1 ≤ L₁ by omega)
      linarith
    have hL₁y : (L₁ : ℝ) ≤ y := by
      have : (L₁ : ℝ) ≤ ee := by exact_mod_cast hle
      have := hsub.he.1
      linarith
    have hU := oset_union (interiorWalk (Qof P)) u hx1 hL₁y
    have sA : oset (interiorWalk (Qof P)) u x L₁ ⊆ C.set :=
      (oset_mono _ _ le_rfl hL₁y).trans hsubC
    have sB : oset (interiorWalk (Qof P)) u L₁ y ⊆ C.set :=
      (oset_mono _ _ hx1 le_rfl).trans hsubC
    have oA : s.o.eval (Qof P) ∉ oset (interiorWalk (Qof P)) u x L₁ := fun h =>
      hoA (oset_mono _ _ le_rfl hL₁y h)
    have oB : s.o.eval (Qof P) ∉ oset (interiorWalk (Qof P)) u L₁ y := fun h =>
      hoA (oset_mono _ _ hx1 le_rfl h)
    -- the first arc
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, Fa⟩ := arcTwoA_exec (P := P) c₁ w₁ C₁.r77 b34 C₁.r89
      (by omega) (by omega)
    have C₂ := keepArc Fa C₁
    obtain ⟨c₃, k₃, e₃, hk₃, hB₃, C₃, F₃, g₃⟩ := shotI_exec hsh c₂ e₂.wb_right C₂
      (sa := ⟨6 + tau (Qof P) u L h1 h2, sh₀⟩) (ea := ⟨2 * L + 6, 0⟩)
      a1 a2 a3 a4 harcA sA ho1 ho2 hol oA (keepArcB Fa hB₁) (by
        rw [Fa.1 _ (by decide), dA]; omega)
    -- the second arc
    have c35 : c₃.nreg 170035 = ee := by
      rw [bandShot g₃ _ (by norm_num) (by norm_num) (by decide),
        bandArc Fa _ (by norm_num) (by norm_num) (by decide)]; exact b35
    have c36 : c₃.nreg 170036 = eh := by
      rw [bandShot g₃ _ (by norm_num) (by norm_num) (by decide),
        bandArc Fa _ (by norm_num) (by norm_num) (by decide)]; exact b36
    obtain ⟨c₄, k₄, e₄, hk₄, a1', a2', a3', a4', Fb⟩ := arcTwoB_exec (P := P) c₃ e₃.wb_right
      C₃.r77 c35 c36 C₃.r89 (by omega)
    have C₄ := keepArc Fb C₃
    have hA₃ := F₃.2.2.2.2.2.2
    obtain ⟨c₅, k₅, e₅, hk₅, hB₅, C₅, F₅, g₅⟩ := shotI_exec hsh c₄ e₄.wb_right C₄
      (sa := ⟨6, 0⟩) (ea := ⟨6 + (ee - L₁), eh⟩) a1' a2' a3' a4' harcB sB ho1 ho2 hol oB
      (keepArcB Fb hB₃) (by
        rw [Fb.1 _ (by decide)]
        have := Fa.1 ALLOC (by decide)
        omega)
    have ex : Exec P W (sqS sh) c c₅ (k₁ + ((k₂ + (k₃ + (k₄ + k₅))) + 1)) :=
      .seq e₁ (.ifLtN_true hb (.seq e₂ (.seq e₃ (.seq e₄ e₅))))
    have Fa' : Frame ioBands c₁ c₂ k₂ := frameIO_of_frameB (fun r h => barc_io h) Fa k₂
    have Fb' : Frame ioBands c₃ c₄ k₄ := frameIO_of_frameB (fun r h => barc_io h) Fb k₄
    refine ⟨c₅, _, ex, by omega, ?_, C₅.env,
      ((((F₁.trans Fa').trans F₃).trans Fb').trans F₅).mono (by simp) (by omega),
      fun r r1 r2 hr => ?_⟩
    · grind
    · rw [bandShot g₅ r r1 r2 hr, bandArc Fb r r1 r2 hr, bandShot g₃ r r1 r2 hr,
        bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]

end exec

end

end IOrc

end Chazelle.Core
