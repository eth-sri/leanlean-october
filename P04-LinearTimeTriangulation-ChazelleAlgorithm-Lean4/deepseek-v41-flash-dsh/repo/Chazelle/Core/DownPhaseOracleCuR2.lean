module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseOracleCuR1

/-!
# WP-M (E7-B, RAM part 16): one sub-query of the interior cutter

A sub-query serves a subarc of `L ≤ n - 1` walk edges of the interior walk from `⟨u, sh⟩` to
`⟨(u + ee) mod n, eh⟩` (registers `170033 … 170037`, `SubOK`), at the unwrapped offset `off` from
the start `e₁` of the query: `sqC cu b` builds the chain `ch Q u L` and its descriptor (`chainI`),
then cuts its one chain arc (`τ ≤ L`) or its two chain arcs meeting at the top (`L < τ`), recorded
as slots `b`, `b + 1`.

* `str_one`, `str_twoA`, `str_twoB`: the stretches of the chain arcs;
* `sqC_exec`: the slot state advances from the unwrapped key of the start of the subarc to that of
  its end.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Chazelle.Core

namespace IOrc

open Machine Machine.Stmt Programs SignK WalkKey SweepPrim

@[expose] public section

/-! ## The stretches of the chain arcs -/

section str

variable {Q : Polygon} {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)
  (hD : DistinctHeights Q) (hn : 3 ≤ Q.n)

include hu hD hn in
/-- **The stretch of the one chain arc.** -/
theorem str_one (hs : tau Q u L h1 h2 ≤ L) :
    Stretch Q (ch Q u L h1 h2) u (6 + tau Q u L h1 h2) L := by
  have hA := agree_pre hu h1 h2
  Ξ' min_eq_left (⋄) at hA
  exact ⟨hu, ⋄, by rw [ch_m]; omega, ch_P, hD, hn, ⋄, hA⟩

include hu hD hn in
/-- **The stretch of the first of two chain arcs.** -/
theorem str_twoA (hs : L < tau Q u L h1 h2) :
    Stretch Q (ch Q u L h1 h2) u (6 + tau Q u L h1 h2) (2 * L - tau Q u L h1 h2) := by
  have hA := agree_pre hu h1 h2
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  Ξ' min_eq_right (⋄) at hA
  exact ⟨hu, ⋄, by rw [ch_m]; omega, ch_P, hD, hn, ⋄, hA⟩

include hu hD hn in
/-- **The stretch of the second of two chain arcs.** -/
theorem str_twoB (hs : L < tau Q u L h1 h2) :
    Stretch Q (ch Q u L h1 h2) ((u + (2 * L - tau Q u L h1 h2)) % Q.n) 6
      (L - (2 * L - tau Q u L h1 h2)) := by
  have hA := agree_post hu h1 h2 hs
  have ht : tau Q u L h1 h2 < 2 * L := tau_lt
  have hiw : (interiorWalk Q).n = Q.n := Trans.iw_n
  refine ⟨Nat.mod_lt _ (⋄), le_rfl, by rw [ch_m]; omega, ch_P, hD, hn, ⋄,
    fun d hd => ?_⟩
  Ξ hiw, Nat.mod_add_mod, ← hiw
  exact hA d hd

end str

/-- **The slot state with fewer free slots.** -/
theorem SlotSt.mono {P : Polygon} {Hγ Gγ e₁ : ℕ} {V0 V : ℝ} {k k' : ℕ} {c : Config}
    (h : SlotSt P Hγ Gγ e₁ V0 V k c) (hk : k ≤ k') : SlotSt P Hγ Gγ e₁ V0 V k' c :=
  ⟨h.ok, fun j h1 h2 => h.free j (⋄) h2, h.bit, h.qG⟩

/-! ## The program -/

/-- **A sub-query of the interior cutter**, recorded as slots `b` (and `b + 1`). -/
def sqC (cu : Stmt) (b : ℕ) : Stmt :=
  .seq chainI (.ifLtN 170037 170077
    (.seq arcTwoAC (.seq (cutR cu b) (.seq arcTwoBC (cutR cu (b + 1)))))
    (.seq arcOneC (cutR cu b)))

/-- The registers of band `17` a sub-query of the cutter writes. -/
def BSQC (r : ℕ) : Bool :=
  decide (170038 ≤ r ∧ r < 170042) || decide (170046 ≤ r ∧ r < 170092) ||
    decide (170133 ≤ r ∧ r < 170147) || decide (170200 ≤ r ∧ r < 170220)

/-! ## Execution -/

section exec

variable {P : Polygon} {W : ℕ} {O : OracleIface} {s : Stat}

/-- **A sub-query of the interior cutter.** -/
theorem sqC_exec {cu : Stmt} {G H : ℕ → ℕ}
    (hcu : CutterOK cu oracleBands G H (gradeCtx O) OkModel) (c : Config) (hw : WordsBounded W c)
    (hS : SEnv P W O s c) {u L sh₀ ee eh off : ℕ}
    (h33 : c.nreg 170033 = u) (h34 : c.nreg 170034 = sh₀) (h35 : c.nreg 170035 = ee)
    (h36 : c.nreg 170036 = eh) (h37 : c.nreg 170037 = L)
    (hsub : SubOK (Qof P) u L sh₀ ee eh) (hLγ : L ≤ s.γ) (hoff : u = (s.e₁ + off) % (Qof P).n)
    {b : ℕ} (hb : b + 2 ≤ 4) {V0 : ℝ}
    (hT : SlotSt P (H s.γ) (G s.γ) s.e₁ V0
      ((s.e₁ : ℝ) + off + (interiorModel (Qof P)).param (Qof P) ⟨u, sh₀⟩) b c)
    (hroom : c.nreg ALLOC + 2 * G s.γ + 1204 * Nat.log 2 (2 * L) + 2600 ≤ W) :
    ∃ c' k, Exec P W (sqC cu b) c c' k ∧ k ≤ 2 * G s.γ + 1204 * Nat.log 2 (2 * L) + 2600 ∧
      SlotSt P (H s.γ) (G s.γ) s.e₁ V0 ((s.e₁ : ℝ) + off + ee +
        (interiorModel (Qof P)).param (Qof P) ⟨(u + ee) % (Qof P).n, eh⟩) (b + 2) c' ∧
      SEnv P W O s c' ∧ Frame ioBands c c' k ∧
      (∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → c'.nreg r = c.nreg r) := by
  have hQ : (Qof P).n = P.n := qn'
  have hW := hS.hW
  unfold hostWords at hW
  have h1 := hsub.h1
  have h2 := hsub.h2
  have hu := hsub.hu
  have hee := sub_ee_le hsub
  have hcap : L ≤ 2 ^ (s.m₀ s.h - 1) := hLγ.trans hS.cap
  have hG := hS.good
  have hD : DistinctHeights (Qof P) := (goodShear_epsOf hG.2).2.1
  have hn3 : 3 ≤ (Qof P).n := by rw [hQ]; exact Chazelle.Jordan.simple_three_le hG.1
  set x := (interiorModel (Qof P)).param (Qof P) ⟨u, sh₀⟩ with hx
  set t := (interiorModel (Qof P)).param (Qof P) ⟨(u + ee) % (Qof P).n, eh⟩ with ht
  have hyL : (ee : ℝ) + t ≤ L := sub_y_le hsub
  have hx0 := hsub.hs.1
  have hx1 := hsub.hs.2.1
  have ht0 := hsub.he.1
  have hxy := hsub.hxy
  set C := ch (Qof P) u L h1 h2 with hCd
  -- the chain
  obtain ⟨c₁, k₁, e₁, hk₁, hk₁', C₁, d78, dA, dm, dr, drr, drm, dout⟩ := chainI_exec c hw hS h33 h37
    (by rw [← hQ]; exact hu) h1 h2 hcap (⋄)
  have F₁ : Frame ioBands c c₁ k₁ := frame_chainI hk₁' dA dm dr drr drm dout
  have w₁ := e₁.wb_right
  have g₁ : ∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → c₁.nreg r = c.nreg r :=
    fun r r1 r2 hr => dr r (by
      ϴ' BSQC, Bool.or_eq_false_iff, decide_eq_false_iff_not at hr
      simp only [Bchain, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
      (by unfold ALLOC; omega)
  have T₁ : SlotSt P (H s.γ) (G s.γ) s.e₁ V0 ((s.e₁ : ℝ) + off + x) b c₁ :=
    hT.keep (fun r r1 r2 => dr r (by
      simp only [Bchain, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
      (by unfold ALLOC; omega)) dm (⋄)
  have b34 : c₁.nreg 170034 = sh₀ := by rw [g₁ _ (⊛) (⊛) (⌖)]; exact h34
  have b35 : c₁.nreg 170035 = ee := by rw [g₁ _ (⊛) (⊛) (⌖)]; exact h35
  have b36 : c₁.nreg 170036 = eh := by rw [g₁ _ (⊛) (⊛) (⌖)]; exact h36
  have hτ : tau (Qof P) u L h1 h2 < 2 * L := tau_lt
  -- the arc blocks keep the chain state and the slot state
  have keepArc : ∀ {d d' : Config}, FrameB BarcC d d' → CEnv P W O s u L h1 h2 d →
      CEnv P W O s u L h1 h2 d' := fun F hC => hC.keep (fun r hr => F.1 r (by
        unfold CRegs at hr; simp only [BarcC, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
      (fun a _ => Ρ F.2.2.1) (Ρ F.1 _ (⌖))
  have keepArcT : ∀ {d d' : Config} {V : ℝ} {k : ℕ}, FrameB BarcC d d' →
      SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V k d → SlotSt P (H s.γ) (G s.γ) s.e₁ V0 V k d' :=
    fun F hT' => hT'.keep (fun r r1 r2 => F.1 r (by
        simp only [BarcC, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega))
      (fun a _ => Ρ F.2.2.1) (Ρ F.1 _ (⌖))
  have bandArc : ∀ {d d' : Config}, FrameB BarcC d d' → ∀ r, 170000 ≤ r → r < 180000 →
      BSQC r = false → d'.nreg r = d.nreg r := fun F r r1 r2 hr => F.1 r (by
        ϴ' BSQC, Bool.or_eq_false_iff, decide_eq_false_iff_not at hr
        simp only [BarcC, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have bandCut : ∀ {d d' : Config} {k : ℕ}, (∀ r, 170000 ≤ r → r < 180000 →
      (r < 170200 + 5 * k ∨ 170205 + 5 * k ≤ r) → d'.nreg r = d.nreg r) → k < 4 →
      ∀ r, 170000 ≤ r → r < 180000 → BSQC r = false → d'.nreg r = d.nreg r :=
    fun F hk r r1 r2 hr => F r r1 r2 (by
        ϴ' BSQC, Bool.or_eq_false_iff, decide_eq_false_iff_not at hr; omega)
  have hps := param_start hu h1 h2 sh₀
  have ks : (chainModel C).key (Qof P) ⟨6 + tau (Qof P) u L h1 h2, sh₀⟩ =
      ((6 + tau (Qof P) u L h1 h2 : ℕ) : ℝ) + x := Ρ key_eq, hps
  by_cases hs : tau (Qof P) u L h1 h2 ≤ L
  · -- one chain arc
    set τ := tau (Qof P) u L h1 h2 with hτd
    have hb' : ¬ c₁.nreg 170037 < c₁.nreg 170077 := by rw [C₁.r37, C₁.r77]; omega
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, a45, a46, Fa⟩ := arcOneC_exec (P := P) c₁ w₁
      C₁.r77 b34 b35 b36 C₁.r33 (⋄)
    have C₂ := keepArc Fa C₁
    have harc := chainArcs_one hsub hs hLγ
    have hpe := param_end_one hu h1 h2 (e := ee) (h₂ := eh) hs (sub_he' hsub)
    have ke : (chainModel C).key (Qof P) ⟨6 + τ + ee, eh⟩ = ((6 + τ + ee : ℕ) : ℝ) + t := by
      Ξ key_eq, hpe
    have hV : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨6 + τ, sh₀⟩ = s.e₁ + off + x := by rw [ks]; ring
    have hV' : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨6 + τ + ee, eh⟩ = s.e₁ + off + ee + t := by
      rw [ke]; push_cast; ring
    obtain ⟨c₃, k₃, e₃, hk₃, T₃, C₃, F₃, g₃⟩ := cutR_exec hcu c₂ e₂.wb_right C₂
      (sa := ⟨6 + τ, sh₀⟩) (ea := ⟨6 + τ + ee, eh⟩) a1 a2 a3 a4 harc a45 a46
      (str_one hu h1 h2 hD hn3 hs) hoff
      (by rw [ks]; push_cast; linarith)
      (by rw [ke]; push_cast; linarith)
      (by rw [ks, ke]; push_cast; linarith) (k := b) (⋄)
      (by rw [hV]; exact keepArcT Fa T₁) (by rw [Fa.1 _ (⌖), dA]; omega)
    Ξ' hV' at T₃
    have ex : Exec P W (sqC cu b) c c₃ (k₁ + (k₂ + k₃ + 2)) :=
      .seq e₁ (.ifLtN_false hb' (.seq e₂ e₃))
    have Fa' : Frame ioBands c₁ c₂ k₂ := frameIO_of_frameB (fun r h => barcC_io h) Fa k₂
    refine ⟨c₃, _, ex, ⋄, T₃.mono (⋄), C₃.env,
      ((F₁.trans Fa').trans F₃).mono (✓) (⋄), fun r r1 r2 hr => ?_⟩
    Ξ bandCut g₃ (⋄) r r1 r2 hr, bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr
  · -- two chain arcs meeting at the top
    push Not at hs
    set τ := tau (Qof P) u L h1 h2 with hτd
    have hb' : c₁.nreg 170037 < c₁.nreg 170077 := by rw [C₁.r37, C₁.r77]; exact hs
    obtain ⟨harcA, harcB⟩ := chainArcs_two hsub hs hLγ
    set L₁ := 2 * L - τ with hL₁
    have hle : L₁ ≤ ee := by rcases hsub.hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
    have hpe := param_end_two hu h1 h2 (e := ee) (h₂ := eh) hs hle (sub_he' hsub)
    have ke : (chainModel C).key (Qof P) ⟨2 * L + 6, 0⟩ = ((2 * L + 6 : ℕ) : ℝ) := by
      Ξ key_eq, param_hgt_zero, add_zero
    have k6 : (chainModel C).key (Qof P) ⟨6, 0⟩ = ((6 : ℕ) : ℝ) := by
      Ξ key_eq, param_hgt_zero, add_zero
    have keB : (chainModel C).key (Qof P) ⟨6 + (ee - L₁), eh⟩ = ((6 + (ee - L₁) : ℕ) : ℝ) + t := by
      Ξ key_eq, hpe
    have hL₁r : ((L₁ : ℕ) : ℝ) = 2 * L - τ := by rw [hL₁, Nat.cast_sub (⋄)]; push_cast; ring
    have hel : ((ee - L₁ : ℕ) : ℝ) = ee - L₁ := Nat.cast_sub hle
    -- the first arc
    obtain ⟨c₂, k₂, e₂, hk₂, a1, a2, a3, a4, a45, a46, Fa⟩ := arcTwoAC_exec (P := P) c₁ w₁
      C₁.r77 b34 C₁.r89 C₁.r33 (⋄) (⋄)
    have C₂ := keepArc Fa C₁
    have hVA : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨6 + τ, sh₀⟩ = s.e₁ + off + x := by rw [ks]; ring
    have hVA' : (s.e₁ : ℝ) + off - ((6 + τ : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨2 * L + 6, 0⟩ = s.e₁ + ((off + L₁ : ℕ) : ℝ) := by
      rw [ke]; push_cast; rw [hL₁r]; ring
    obtain ⟨c₃, k₃, e₃, hk₃, T₃, C₃, F₃, g₃⟩ := cutR_exec hcu c₂ e₂.wb_right C₂
      (sa := ⟨6 + τ, sh₀⟩) (ea := ⟨2 * L + 6, 0⟩) a1 a2 a3 a4 harcA a45 a46
      (str_twoA hu h1 h2 hD hn3 hs) hoff
      (by rw [ks]; push_cast; linarith)
      (by rw [ke]; push_cast; rw [hL₁r]; linarith)
      (by rw [ks, ke]; push_cast
          have : (τ : ℝ) + 1 ≤ 2 * L := by exact_mod_cast (show τ + 1 ≤ 2 * L by omega)
          linarith) (k := b) (⋄)
      (by rw [hVA]; exact keepArcT Fa T₁) (by rw [Fa.1 _ (⌖), dA]; omega)
    Ξ' hVA' at T₃
    -- the second arc
    have c35 : c₃.nreg 170035 = ee := by
      rw [g₃ _ (⊛) (⊛) (Or.inl (⋄)),
        bandArc Fa _ (⊛) (⊛) (⌖)]; exact b35
    have c36 : c₃.nreg 170036 = eh := by
      rw [g₃ _ (⊛) (⊛) (Or.inl (⋄)),
        bandArc Fa _ (⊛) (⊛) (⌖)]; exact b36
    have c10 : c₃.nreg 170010 = (Qof P).n := Ρ C₃.env.r10, hQ
    obtain ⟨c₄, k₄, e₄, hk₄, a1', a2', a3', a4', a45', a46', Fb⟩ := arcTwoBC_exec (P := P) c₃
      e₃.wb_right C₃.r77 c35 c36 C₃.r89 C₃.r33 c10 hu (⋄) (⋄) (⋄)
    have C₄ := keepArc Fb C₃
    have hA₃ := F₃.2.2.2.2.2.2
    have hoff' : (u + L₁) % (Qof P).n = (s.e₁ + (off + L₁)) % (Qof P).n := by
      Ξ hoff, Nat.mod_add_mod, Nat.add_assoc
    have hVB : (s.e₁ : ℝ) + ((off + L₁ : ℕ) : ℝ) - ((6 : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨6, 0⟩ = s.e₁ + ((off + L₁ : ℕ) : ℝ) := by rw [k6]; ring
    have hVB' : (s.e₁ : ℝ) + ((off + L₁ : ℕ) : ℝ) - ((6 : ℕ) : ℝ) +
        (chainModel C).key (Qof P) ⟨6 + (ee - L₁), eh⟩ = s.e₁ + off + ee + t := by
      rw [keB]; push_cast; rw [hel]; ring
    obtain ⟨c₅, k₅, e₅, hk₅, T₅, C₅, F₅, g₅⟩ := cutR_exec hcu c₄ e₄.wb_right C₄
      (sa := ⟨6, 0⟩) (ea := ⟨6 + (ee - L₁), eh⟩) a1' a2' a3' a4' harcB a45' a46'
      (str_twoB hu h1 h2 hD hn3 hs) hoff' (off := off + L₁)
      (Ρ k6)
      (by rw [keB]; push_cast; Ξ hel
          have : (L₁ : ℝ) ≤ ee := by exact_mod_cast hle
          have : ((L - L₁ : ℕ) : ℝ) = L - L₁ := Nat.cast_sub (⋄)
          rw [this]; linarith)
      (by rw [k6, keB]; push_cast; Ξ hel
          have : (L₁ : ℝ) < ee + t := by
            rcases hsub.hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
            · have : (L₁ : ℝ) < ee := by exact_mod_cast (show L₁ < ee by omega)
              linarith
            · have : (L₁ : ℝ) ≤ ee := by exact_mod_cast hle
              linarith
          linarith) (k := b + 1) (⋄)
      (by rw [hVB]; exact keepArcT Fb T₃) (by
        Ξ Fb.1 _ (⌖)
        have := Fa.1 ALLOC (⌖)
        omega)
    Ξ' hVB' at T₅
    have ex : Exec P W (sqC cu b) c c₅ (k₁ + ((k₂ + (k₃ + (k₄ + k₅))) + 1)) :=
      .seq e₁ (.ifLtN_true hb' (.seq e₂ (.seq e₃ (.seq e₄ e₅))))
    have Fa' : Frame ioBands c₁ c₂ k₂ := frameIO_of_frameB (fun r h => barcC_io h) Fa k₂
    have Fb' : Frame ioBands c₃ c₄ k₄ := frameIO_of_frameB (fun r h => barcC_io h) Fb k₄
    refine ⟨c₅, _, ex, ⋄, T₅, C₅.env,
      ((((F₁.trans Fa').trans F₃).trans Fb').trans F₅).mono (✓) (⋄),
      fun r r1 r2 hr => ?_⟩
    rw [bandCut g₅ (⋄) r r1 r2 hr, bandArc Fb r r1 r2 hr, bandCut g₃ (⋄) r r1 r2 hr,
      bandArc Fa r r1 r2 hr, g₁ r r1 r2 hr]

end exec

end

end IOrc

end Chazelle.Core
