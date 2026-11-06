module

public import Chazelle.Core.SweepIoLHit5

/-!
# The sweep RAM (WP-D), answers: positions of the chain models in the model of `C`

A walk position of the model `M₁` of `C₁` (or `M₂` of `C₂`) that is a point of the chain or of a
vertical side of the box is converted to a walk position of the model `M` of `C = J.whole` with
the same point (`convVal`, `conv_pos`):

* on a vertical side of the box (edges `1`, `3`) the boxes agree (`boxTwin_pos`);
* the start of the up-slit edge (the top of the chain, parameter `0`) is the tour vertex `6`;
* a tour edge is mapped by the correspondence of its side (`corrL_sidePt`, `corrR_sidePt`):
  offset `d₂` from the base `g'` of the side model, inverse of `dq`, and the edge `(g + d) mod n`
  of `M`.

`convS b nr pe po` computes it on the RAM from the constants of the correspondence
(`sw 40 … 44` right, `sw 45 … 49` left; `b` their base) and the walk length `nr` of the side model.
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Visibility (rayPt)
open Chazelle.Chain (sidePt sideLeft sideInArc)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The mathematics -/

/-- Agreeing walk points give agreeing edge ends. -/
theorem wab_of_sidePt {W W' : Polygon} {p p' : ℕ} (h : ∀ t, sidePt W p t = sidePt W' p' t) :
    W.vtx p = W'.vtx p' ∧ W.vtx ((p + 1) % W.n) = W'.vtx ((p' + 1) % W'.n) := by
  constructor
  · have := h 0; rwa [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero] at this
  · have := h 1; rwa [Restore.sidePt_one', Restore.sidePt_one'] at this

/-- Positions on edges with the same ends have the same parameter and point. -/
theorem param_pos_of_wab {M M' : Model} {p p' : ℕ} (ha : M.wa p = M'.wa p')
    (hb : M.wb p = M'.wb p') (Q : Polygon) (h : ℕ) :
    M.param Q ⟨p, h⟩ = M'.param Q ⟨p', h⟩ ∧ M.pos Q ⟨p, h⟩ = M'.pos Q ⟨p', h⟩ := by
  have hp : M.param Q ⟨p, h⟩ = M'.param Q ⟨p', h⟩ := by
    unfold Model.param; simp only; rw [ha, hb]
  exact ⟨hp, by unfold Model.pos; simp only; rw [ha, hb, hp]⟩

/-- **A side of a junction for the conversion**: the side model `M'` of the chain `C'`, the
constants of its correspondence with the model `M` of `C` (with the three cases of the lengths),
and the agreement of the vertical box sides. -/
structure SideConv (M M' : Model) (C' : Chain) (g g' L1 L2 δ : ℕ) : Prop where
  hM' : M' = chainModel C'
  hτ : ∃ τ, g' = 6 + τ ∧ τ < 2 * C'.m ∧ ((L1 = 2 * C'.m + 7 ∧ L2 = 0 ∧ δ = 0) ∨
    (τ = 0 ∧ L1 = 2 * C'.m ∧ L2 = 0 ∧ δ = 0) ∨ (0 < τ ∧ L1 = 2 * C'.m - τ ∧ L2 = τ ∧ δ = 7))
  hg : g < M.W.n
  hMn : 6 < M.W.n
  hL : L1 + L2 ≤ M.W.n
  corr : ∀ d, d < L1 + L2 → ∀ t,
    sidePt M.W ((g + d) % M.W.n) t = sidePt M'.W ((g' + Sweep.dq L1 δ d) % M'.W.n) t
  box : ∀ e, (e = 1 ∨ e = 3) → M.wa e = M'.wa e ∧ M.wb e = M'.wb e

/-- The side of `C₂`. -/
theorem sideConvR (J : Merge.Junction) (hP : J.P.Simple) :
    SideConv (chainModel J.whole) (chainModel J.right) J.right (6 + tpos J.whole J.m₁)
      (6 + tpos J.right 0) (Sweep.rL1 J) (Sweep.rL2 J) (Sweep.rδ J) := by
  have hC := Sweep.corr_right0 J hP (S₂ := ∅) (Set.empty_subset _) Set.finite_empty
  have hτ := tpos_lt J.right 0
  have hm2 : J.right.m = J.m₂ := rfl
  refine ⟨rfl, ⟨tpos J.right 0, rfl, hτ, ?_⟩, hC.hg, by rw [cm_n]; omega, hC.hL,
    fun d hd t => corrR_sidePt J hP hd t,
    fun e he => ?_⟩
  · unfold Sweep.rL1 Sweep.rL2 Sweep.rδ
    simp only [hm2] at hτ ⊢
    split_ifs with h1 h2
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; left; refine ⟨by omega, rfl, rfl, rfl⟩
    · right; right; refine ⟨by omega, rfl, by omega, rfl⟩
  · obtain ⟨ha, hb, -, -⟩ := boxTwin_pos (FuseMath.radius_of_P J (C' := J.right) rfl) he
      ⟨[]⟩ 0
    exact ⟨ha.symm, hb.symm⟩

/-- The side of `C₁`. -/
theorem sideConvL (J : Merge.Junction) (hP : J.P.Simple) :
    SideConv (chainModel J.whole) (chainModel J.left) J.left (6 + tpos J.whole (J.m₁ + 2 * J.m₂))
      (6 + tpos J.left J.m₁) (Sweep.lL1 J) (Sweep.lL2 J) (Sweep.lδ J) := by
  have hC := Sweep.corr_left0 J hP (S₁ := ∅) (Set.empty_subset _) Set.finite_empty
  have hτ := tpos_lt J.left J.m₁
  have hm1 : J.left.m = J.m₁ := rfl
  refine ⟨rfl, ⟨tpos J.left J.m₁, rfl, hτ, ?_⟩, hC.hg, by rw [cm_n]; omega, hC.hL,
    fun d hd t => corrL_sidePt J hP hd t,
    fun e he => ?_⟩
  · unfold Sweep.lL1 Sweep.lL2 Sweep.lδ
    simp only [hm1] at hτ ⊢
    split_ifs with h1 h2
    · left; exact ⟨rfl, rfl, rfl⟩
    · right; left; refine ⟨by omega, rfl, rfl, rfl⟩
    · right; right; refine ⟨by omega, rfl, by omega, rfl⟩
  · obtain ⟨ha, hb, -, -⟩ := boxTwin_pos (FuseMath.radius_of_P J (C' := J.left) rfl) he
      ⟨[]⟩ 0
    exact ⟨ha.symm, hb.symm⟩

/-- The offset in `M` of the tour edge `x` of the side model (inverse of `dq`). -/
def convD (g' L1 δ n' x : ℕ) : ℕ :=
  if (if x < g' then x + (n' - g') else x - g') < L1 then (if x < g' then x + (n' - g') else x - g')
  else (if x < g' then x + (n' - g') else x - g') - δ

/-- The edge `(g + d) mod n`. -/
def convM (g n d : ℕ) : ℕ := if d < n - g then g + d else d - (n - g)

/-- **The converted edge.** -/
def convVal (g g' L1 δ n' n e : ℕ) : ℕ :=
  if e < 6 then e else convM g n (convD g' L1 δ n' (if e + 1 = n' then 6 else e))

/-- The tour vertex `6` of a chain model is its top, as is the vertex `2m + 6`. -/
theorem slit_start_pos (C : Chain) (Q : Polygon) {h : ℕ}
    (h0 : (chainModel C).param Q ⟨2 * C.m + 6, h⟩ = 0) :
    (chainModel C).param Q ⟨6, h⟩ = 0 ∧
      (chainModel C).pos Q ⟨6, h⟩ = (chainModel C).pos Q ⟨2 * C.m + 6, h⟩ := by
  have hv6 : (chainModel C).wa 6 = C.top := C.sideWalk_vtx_six _
  have hvt : (chainModel C).wa (2 * C.m + 6) = C.top := by
    show (C.sideWalk C.sideBeta).vtx (2 * C.m + 6) = C.top
    rw [show 2 * C.m + 6 = 2 * C.m + 6 by rfl, C.sideWalk_vtx_tour _ le_rfl, Chain.sideTour_two_m]
  have hwb : (chainModel C).wb (2 * C.m + 6) = C.slitTop := C.sideWalk_vtx_wrap _
  have hR := C.top_snd_lt_radius
  have hp6 : (chainModel C).param Q ⟨6, h⟩ = 0 := by
    rcases h with _ | k
    · rfl
    · have hk : (Q.vtx k).2 = C.top.2 := by
        unfold Model.param at h0; simp only at h0
        rw [hvt, hwb] at h0
        have hne : C.slitTop.2 - C.top.2 ≠ 0 := by
          simp only [Chain.slitTop]; linarith
        rw [ite_eq_right (by simp only [Chain.slitTop]; linarith)] at h0
        rcases div_eq_zero_iff.1 h0 with h3 | h3
        · linarith
        · exact absurd h3 hne
      unfold Model.param; simp only; rw [hv6]
      split_ifs
      · rfl
      · rw [hk, sub_self, zero_div]
  refine ⟨hp6, ?_⟩
  unfold Model.pos
  rw [hp6, h0, Geometry.lerp_zero, Geometry.lerp_zero, hv6, hvt]

/-- The index arithmetic of a tour edge. -/
theorem conv_arith {m τ L1 L2 δ x : ℕ} (hτ : τ < 2 * m)
    (hc : (L1 = 2 * m + 7 ∧ L2 = 0 ∧ δ = 0) ∨ (τ = 0 ∧ L1 = 2 * m ∧ L2 = 0 ∧ δ = 0) ∨
      (0 < τ ∧ L1 = 2 * m - τ ∧ L2 = τ ∧ δ = 7)) (hx6 : 6 ≤ x) (hx : x < 2 * m + 6) :
    convD (6 + τ) L1 δ (2 * m + 7) x < L1 + L2 ∧
      (6 + τ + Sweep.dq L1 δ (convD (6 + τ) L1 δ (2 * m + 7) x)) % (2 * m + 7) = x := by
  have key : ∀ v, v = x ∨ v = x + (2 * m + 7) → v % (2 * m + 7) = x := by
    rintro v (rfl | rfl)
    · exact Nat.mod_eq_of_lt (by omega)
    · rw [Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
  unfold Sweep.dq convD
  constructor
  · rcases hc with ⟨h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> subst h1 h2 h3 <;>
      split_ifs <;> omega
  · apply key
    rcases hc with ⟨h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ | ⟨h0, h1, h2, h3⟩ <;> subst h1 h2 h3 <;>
      split_ifs <;> omega

theorem add_mod_cases {g d n : ℕ} (hg : g < n) (hd : d < n) : (g + d) % n = convM g n d := by
  unfold convM
  split_ifs with h
  · exact Nat.mod_eq_of_lt (by omega)
  · rw [show g + d = (d - (n - g)) + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- **The converted position has the same point.** -/
theorem conv_pos {M M' : Model} {C' : Chain} {g g' L1 L2 δ : ℕ}
    (hS : SideConv M M' C' g g' L1 L2 δ) (Q : Polygon) {e h : ℕ}
    (hv : (e = 1 ∨ e = 3) ∨ (6 ≤ e ∧ e < 2 * C'.m + 6) ∨
      (e = 2 * C'.m + 6 ∧ M'.param Q ⟨e, h⟩ = 0)) :
    convVal g g' L1 δ M'.W.n M.W.n e < M.W.n ∧
      M.param Q ⟨convVal g g' L1 δ M'.W.n M.W.n e, h⟩ = M'.param Q ⟨e, h⟩ ∧
      M.pos Q ⟨convVal g g' L1 δ M'.W.n M.W.n e, h⟩ = M'.pos Q ⟨e, h⟩ := by
  obtain ⟨hM', ⟨τ, hg', hτ, hc⟩, hg, hMn, hL, hcorr, hbox⟩ := hS
  subst hM' hg'
  have hn' : (chainModel C').W.n = 2 * C'.m + 7 := cm_n C'
  -- the tour case for an edge `x`
  have tour : ∀ x, 6 ≤ x → x < 2 * C'.m + 6 →
      convM g M.W.n (convD (6 + τ) L1 δ (chainModel C').W.n x) < M.W.n ∧
      M.param Q ⟨convM g M.W.n (convD (6 + τ) L1 δ (chainModel C').W.n x), h⟩ =
        (chainModel C').param Q ⟨x, h⟩ ∧
      M.pos Q ⟨convM g M.W.n (convD (6 + τ) L1 δ (chainModel C').W.n x), h⟩ =
        (chainModel C').pos Q ⟨x, h⟩ := by
    intro x hx6 hx
    rw [hn']
    obtain ⟨hdL, hmod⟩ := conv_arith hτ hc hx6 hx
    have hdn : convD (6 + τ) L1 δ (2 * C'.m + 7) x < M.W.n := by omega
    rw [← add_mod_cases hg hdn]
    have hs : ∀ t, sidePt M.W ((g + convD (6 + τ) L1 δ (2 * C'.m + 7) x) % M.W.n) t =
        sidePt (chainModel C').W x t := by
      intro t; rw [hcorr _ hdL t, hn', hmod]
    obtain ⟨ha, hb⟩ := wab_of_sidePt hs
    obtain ⟨hp, hq⟩ := param_pos_of_wab (M := M) (M' := chainModel C') ha hb Q h
    exact ⟨Nat.mod_lt _ (by omega), hp, hq⟩
  unfold convVal
  rcases hv with he | ⟨he6, he⟩ | ⟨rfl, h0⟩
  · have he6 : e < 6 := by omega
    rw [ite_eq_left he6]
    obtain ⟨ha, hb⟩ := hbox e he
    obtain ⟨hp, hq⟩ := param_pos_of_wab ha hb Q h
    exact ⟨by omega, hp, hq⟩
  · rw [ite_eq_right (show ¬ e < 6 by omega),
      ite_eq_right (show ¬ (e + 1 = (chainModel C').W.n) by rw [hn']; omega)]
    exact tour e he6 he
  · rw [ite_eq_right (show ¬ 2 * C'.m + 6 < 6 by omega),
      ite_eq_left (show 2 * C'.m + 6 + 1 = (chainModel C').W.n by rw [hn'])]
    obtain ⟨h6, hpos⟩ := slit_start_pos C' Q h0
    obtain ⟨t1, t2, t3⟩ := tour 6 le_rfl (by have := C'.one_le; omega)
    exact ⟨t1, by rw [t2, h6, h0], by rw [t3, hpos]⟩

/-! ## The RAM -/

def cX : ℕ := sw 3300
def cT : ℕ := sw 3301
def cDd : ℕ := sw 3302

/-- **The conversion** of the edge in `pe` to the edge `po` of `M`, with the constants of the
correspondence at `b … b + 4` (`g, g', L1, L2, δ`) and the walk length of the side model in `nr`
(scratch `cX, cT, cDd`). -/
def convS (b nr pe po : ℕ) : Stmt :=
  .ifLtN pe K6 (.instr (.copyN po pe))
    (.seq (block [.copyN cX pe, .addN cT pe K1])
    (.seq (eqT cT nr (.instr (.copyN cX K6)))
    (.seq (.ifLtN cX (b + 1) (block [.subN cT nr (b + 1), .addN cT cX cT])
        (.instr (.subN cT cX (b + 1))))
    (.seq (.ifLtN cT (b + 2) (.instr (.copyN cDd cT)) (.instr (.subN cDd cT (b + 4))))
    (.seq (.instr (.subN cT (sw 35) b))
      (.ifLtN cDd cT (.instr (.addN po b cDd)) (.instr (.subN po cDd cT))))))))

/-- The registers `convS` writes. -/
def CvSet (po r : ℕ) : Prop := r = po ∨ r = cX ∨ r = cT ∨ r = cDd

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **The conversion on the RAM.** -/
theorem convS_irs {b nr pe po : ℕ} (hbr : b = sw 40 ∨ b = sw 45) (hnr : nr = sw 33 ∨ nr = sw 34)
    (hpe : pe ≠ cX ∧ pe ≠ cT ∧ pe ≠ cDd) (hpo : IScr po ∧ po ≠ cX ∧ po ≠ cT ∧ po ≠ cDd)
    (hI : IInv W c₀ c) (hK : Consts c₀)
    (hpn : c.nreg pe < c.nreg nr) (hg' : c.nreg (b + 1) < c.nreg nr) (hnW : c.nreg nr ≤ W)
    (hg : c.nreg b < c.nreg (sw 35)) (hnW' : c.nreg (sw 35) ≤ W) :
    IRS P W c₀ (convS b nr pe po) c 22 (fun c' =>
      c'.nreg po = convVal (c.nreg b) (c.nreg (b + 1)) (c.nreg (b + 2)) (c.nreg (b + 4))
        (c.nreg nr) (c.nreg (sw 35)) (c.nreg pe) ∧
      (∀ r, ¬ CvSet po r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem) := by
  have hKc := hK.fix hI
  have k1 : c.nreg K1 = 1 := hKc.2.1
  have k6 : c.nreg K6 = 6 := hKc.2.2.1
  have hbl : 240040 ≤ b ∧ b ≤ 240045 := by rcases hbr with rfl | rfl <;> simp [sw]
  have hnl : 240033 ≤ nr ∧ nr ≤ 240034 := by rcases hnr with rfl | rfl <;> simp [sw]
  have eX : cX = 243300 := rfl
  have eT : cT = 243301 := rfl
  have eD : cDd = 243302 := rfl
  have e6 : K6 = 240612 := rfl
  have e1 : K1 = 240611 := rfl
  have e35 : sw 35 = 240035 := rfl
  have scX : IScr cX := iscr_sw (by rw [eX]; norm_num) (by rw [eX]; norm_num)
  have scT : IScr cT := iscr_sw (by rw [eT]; norm_num) (by rw [eT]; norm_num)
  have scD : IScr cDd := iscr_sw (by rw [eD]; norm_num) (by rw [eD]; norm_num)
  unfold convS
  by_cases hbox : c.nreg pe < c.nreg K6
  · refine (IRS.ifT hbox (IRS.instr1 (i := .copyN po pe) hI hpo.1)).mono (by norm_num) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · show upd c.nreg po (c.nreg pe) po = _
      rw [upd_same]; unfold convVal; rw [ite_eq_left (show c.nreg pe < 6 by rwa [k6] at hbox)]
    · show upd c.nreg po (c.nreg pe) r = _
      exact upd_other _ _ _ (fun h => hr (Or.inl h))
  refine IRS.mono (K := 21) (IRS.ifF hbox ?_) (by norm_num) (fun _ h => h)
  -- the box test failed: `6 ≤ e`
  set e := c.nreg pe
  -- step 1
  have ok1 : okB W c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg :=
    ⟨scX, ⟨scT, by
      simp only [regI, upd]
      rw [ite_eq_right hpe.1, ite_eq_right (show ¬ K1 = cX by unfold K1 cX sw; norm_num), k1]; omega⟩, trivial⟩
  refine (IRS.seq (K₂ := 17) (IRS.block _ hI ok1) ?_).mono (by simp) (fun _ h => h)
  rintro c₁ hI₁ - - hc1
  have v1X : c₁.nreg cX = e := by
    rw [hc1]; show regB c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg cX = _
    simp only [regB, regI]; rw [upd_other _ _ _ (by rw [eX, eT]; norm_num), upd_same]
  have v1T : c₁.nreg cT = e + 1 := by
    rw [hc1]; show regB c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg cT = _
    simp only [regB, regI]; rw [upd_same, upd_other _ _ _ hpe.1, upd_other _ _ _ (by rw [e1, eX]; norm_num), k1]
  have k1r : ∀ r, r ≠ cX → r ≠ cT → c₁.nreg r = c.nreg r := by
    intro r h1 h2; rw [hc1]; show regB c.nmem [.copyN cX pe, .addN cT pe K1] c.nreg r = _
    simp only [regB, regI]; rw [upd_other _ _ _ h2, upd_other _ _ _ h1]
  have hm1 : c₁.nmem = c.nmem := by rw [hc1]
  have fx : ∀ r, 240000 ≤ r → r < 240700 → c₁.nreg r = c.nreg r := fun r h1 h2 =>
    k1r r (by rw [eX]; omega) (by rw [eT]; omega)
  -- step 2: `x := 6` at the end of the walk
  have hnr1 : c₁.nreg nr = c.nreg nr := fx nr (by omega) (by omega)
  have k6' : c₁.nreg K6 = 6 := by rw [fx K6 (by rw [e6]; norm_num) (by rw [e6]; norm_num), k6]
  have st2 : IRS P W c₀ (eqT cT nr (.instr (.copyN cX K6))) c₁ 6 (fun c' =>
      c'.nreg cX = (if e + 1 = c.nreg nr then 6 else e) ∧
      (∀ r, r ≠ cX → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem) := by
    unfold eqT
    by_cases h1 : c₁.nreg cT < c₁.nreg nr
    · refine (IRS.ifT h1 (IRS.skip (K := 0) hI₁ ?_)).mono (by norm_num) (fun _ h => h)
      rw [v1T, hnr1] at h1
      exact ⟨by rw [v1X, ite_eq_right (show ¬ (e + 1 = c.nreg nr) by omega)], fun _ _ => rfl, rfl⟩
    refine IRS.mono (K := 6) (IRS.ifF h1 ?_) (by norm_num) (fun _ h => h)
    by_cases h2 : c₁.nreg nr < c₁.nreg cT
    · refine (IRS.ifT h2 (IRS.skip (K := 0) hI₁ ?_)).mono (by norm_num) (fun _ h => h)
      rw [v1T, hnr1] at h2
      exact ⟨by rw [v1X, ite_eq_right (show ¬ (e + 1 = c.nreg nr) by omega)], fun _ _ => rfl, rfl⟩
    refine (IRS.ifF h2 (IRS.instr1 (i := .copyN cX K6) hI₁ scX)).mono (by norm_num) ?_
    rintro c' rfl
    refine ⟨?_, fun r hr => ?_, rfl⟩
    · show upd c₁.nreg cX (c₁.nreg K6) cX = _
      rw [v1T, hnr1] at h1 h2
      rw [upd_same, k6', ite_eq_left (show e + 1 = c.nreg nr by omega)]
    · show upd c₁.nreg cX (c₁.nreg K6) r = _
      exact upd_other _ _ _ hr
  refine (IRS.seq (K₂ := 11) st2 ?_).mono (by norm_num) (fun _ h => h)
  rintro c₂ hI₂ - - ⟨v2X, k2r, hm2⟩
  set x := (if e + 1 = c.nreg nr then 6 else e)
  have fx2 : ∀ r, 240000 ≤ r → r < 240700 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k2r r (by rw [eX]; omega), fx r h1 h2]
  -- step 3: `d₂`
  have g2 : c₂.nreg (b + 1) = c.nreg (b + 1) := fx2 _ (by omega) (by omega)
  have n2 : c₂.nreg nr = c.nreg nr := fx2 _ (by omega) (by omega)
  have st3 : IRS P W c₀ (.ifLtN cX (b + 1) (block [.subN cT nr (b + 1), .addN cT cX cT])
      (.instr (.subN cT cX (b + 1)))) c₂ 4 (fun c' =>
      c'.nreg cT = (if x < c.nreg (b + 1) then x + (c.nreg nr - c.nreg (b + 1))
        else x - c.nreg (b + 1)) ∧
      (∀ r, r ≠ cT → c'.nreg r = c₂.nreg r) ∧ c'.nmem = c₂.nmem) := by
    by_cases h1 : c₂.nreg cX < c₂.nreg (b + 1)
    · have ok3 : okB W c₂.nmem [.subN cT nr (b + 1), .addN cT cX cT] c₂.nreg := by
        refine ⟨scT, ⟨scT, ?_⟩, trivial⟩
        show (upd c₂.nreg cT (c₂.nreg nr - c₂.nreg (b + 1))) cX +
          (upd c₂.nreg cT (c₂.nreg nr - c₂.nreg (b + 1))) cT ≤ W
        rw [upd_other _ _ _ (show cX ≠ cT by rw [eX, eT]; norm_num), upd_same, n2, g2, v2X]
        rw [v2X, g2] at h1; omega
      refine (IRS.ifT h1 (IRS.block _ hI₂ ok3)).mono (by norm_num) ?_
      rintro c' rfl
      refine ⟨?_, fun r hr => ?_, rfl⟩
      · show regB c₂.nmem [.subN cT nr (b + 1), .addN cT cX cT] c₂.nreg cT = _
        simp only [regB, regI]
        rw [upd_same, upd_other _ _ _ (by rw [eX, eT]; norm_num), upd_same, n2, g2, v2X]
        rw [v2X, g2] at h1; rw [ite_eq_left h1]
      · show regB c₂.nmem [.subN cT nr (b + 1), .addN cT cX cT] c₂.nreg r = _
        simp only [regB, regI]; rw [upd_other _ _ _ hr, upd_other _ _ _ hr]
    · refine (IRS.ifF h1 (IRS.instr1 (i := .subN cT cX (b + 1)) hI₂ scT)).mono (by norm_num) ?_
      rintro c' rfl
      refine ⟨?_, fun r hr => ?_, rfl⟩
      · show upd c₂.nreg cT (c₂.nreg cX - c₂.nreg (b + 1)) cT = _
        rw [upd_same, v2X, g2]; rw [v2X, g2] at h1; rw [ite_eq_right h1]
      · show upd c₂.nreg cT _ r = _
        exact upd_other _ _ _ hr
  refine (IRS.seq (K₂ := 7) st3 ?_).mono (by norm_num) (fun _ h => h)
  rintro c₃ hI₃ - - ⟨v3T, k3r, hm3⟩
  set d₂ := (if x < c.nreg (b + 1) then x + (c.nreg nr - c.nreg (b + 1)) else x - c.nreg (b + 1))
    with hd₂
  have fx3 : ∀ r, 240000 ≤ r → r < 240700 → c₃.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k3r r (by rw [eT]; omega), fx2 r h1 h2]
  -- step 4: `d`
  have l3 : c₃.nreg (b + 2) = c.nreg (b + 2) := fx3 _ (by omega) (by omega)
  have δ3 : c₃.nreg (b + 4) = c.nreg (b + 4) := fx3 _ (by omega) (by omega)
  have st4 : IRS P W c₀ (.ifLtN cT (b + 2) (.instr (.copyN cDd cT))
      (.instr (.subN cDd cT (b + 4)))) c₃ 3 (fun c' =>
      c'.nreg cDd = convD (c.nreg (b + 1)) (c.nreg (b + 2)) (c.nreg (b + 4)) (c.nreg nr) x ∧
      (∀ r, r ≠ cDd → c'.nreg r = c₃.nreg r) ∧ c'.nmem = c₃.nmem) := by
    by_cases h1 : c₃.nreg cT < c₃.nreg (b + 2)
    · refine (IRS.ifT h1 (IRS.instr1 (i := .copyN cDd cT) hI₃ scD)).mono (by norm_num) ?_
      rintro c' rfl
      refine ⟨?_, fun r hr => ?_, rfl⟩
      · show upd c₃.nreg cDd (c₃.nreg cT) cDd = _
        rw [upd_same, v3T]; rw [v3T, l3] at h1; unfold convD; rw [← hd₂, ite_eq_left h1]
      · show upd c₃.nreg cDd _ r = _
        exact upd_other _ _ _ hr
    · refine (IRS.ifF h1 (IRS.instr1 (i := .subN cDd cT (b + 4)) hI₃ scD)).mono (by norm_num) ?_
      rintro c' rfl
      refine ⟨?_, fun r hr => ?_, rfl⟩
      · show upd c₃.nreg cDd (c₃.nreg cT - c₃.nreg (b + 4)) cDd = _
        rw [upd_same, v3T, δ3]; rw [v3T, l3] at h1; unfold convD; rw [← hd₂, ite_eq_right h1]
      · show upd c₃.nreg cDd _ r = _
        exact upd_other _ _ _ hr
  refine (IRS.seq (K₂ := 4) st4 ?_).mono (by norm_num) (fun _ h => h)
  rintro c₄ hI₄ - - ⟨v4D, k4r, hm4⟩
  set d := convD (c.nreg (b + 1)) (c.nreg (b + 2)) (c.nreg (b + 4)) (c.nreg nr) x
  have fx4 : ∀ r, 240000 ≤ r → r < 240700 → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k4r r (by rw [eD]; omega), fx3 r h1 h2]
  -- step 5: `n - g`
  have b4 : c₄.nreg b = c.nreg b := fx4 _ (by omega) (by omega)
  have n4 : c₄.nreg (sw 35) = c.nreg (sw 35) := fx4 _ (by rw [e35]; norm_num) (by rw [e35]; norm_num)
  refine (IRS.seq (K₂ := 3) (IRS.instr1 (i := .subN cT (sw 35) b) hI₄ scT) ?_).mono (by norm_num)
    (fun _ h => h)
  rintro c₅ hI₅ - - rfl
  have v5T : (upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b)) cT = c.nreg (sw 35) - c.nreg b := by
    rw [upd_same, b4, n4]
  have v5D : (upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b)) cDd = d := by
    rw [upd_other _ _ _ (by rw [eD, eT]; norm_num), v4D]
  have v5b : (upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b)) b = c.nreg b := by
    rw [upd_other _ _ _ (by rw [eT]; omega), b4]
  -- step 6: the edge
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b) } with hc5
  have hpost : ∀ c' : Config, c'.nreg po = convVal (c.nreg b) (c.nreg (b + 1)) (c.nreg (b + 2))
      (c.nreg (b + 4)) (c.nreg nr) (c.nreg (sw 35)) e →
      (∀ r, r ≠ po → c'.nreg r = c₅.nreg r) → c'.nmem = c₅.nmem →
      c'.nreg po = convVal (c.nreg b) (c.nreg (b + 1)) (c.nreg (b + 2)) (c.nreg (b + 4))
        (c.nreg nr) (c.nreg (sw 35)) (c.nreg pe) ∧
      (∀ r, ¬ CvSet po r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
    intro c' h1 h2 h3
    refine ⟨h1, fun r hr => ?_, by rw [h3, hm4, hm3, hm2, hm1]⟩
    rw [h2 r (fun h => hr (Or.inl h))]
    show upd c₄.nreg cT _ r = _
    rw [upd_other _ _ _ (fun h => hr (Or.inr (Or.inr (Or.inl h)))),
      k4r r (fun h => hr (Or.inr (Or.inr (Or.inr h)))),
      k3r r (fun h => hr (Or.inr (Or.inr (Or.inl h)))),
      k2r r (fun h => hr (Or.inr (Or.inl h))),
      k1r r (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inr (Or.inr (Or.inl h))))]
  have hval : convVal (c.nreg b) (c.nreg (b + 1)) (c.nreg (b + 2)) (c.nreg (b + 4)) (c.nreg nr)
      (c.nreg (sw 35)) e = convM (c.nreg b) (c.nreg (sw 35)) d := by
    unfold convVal; rw [ite_eq_right (show ¬ e < 6 by omega)]
  by_cases h6 : c₅.nreg cDd < c₅.nreg cT
  · have ok6 : okI W c₅.nreg (.addN po b cDd) := ⟨hpo.1, by
      show (upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b)) b +
        (upd c₄.nreg cT (c₄.nreg (sw 35) - c₄.nreg b)) cDd ≤ W
      rw [v5b, v5D]; have := h6; simp only [hc5] at this; rw [v5D, v5T] at this; omega⟩
    refine (IRS.ifT h6 (IRS.instr1 hI₅ ok6)).mono (by norm_num) ?_
    rintro c' rfl
    refine hpost _ ?_ (fun r hr => ?_) rfl
    · show upd c₅.nreg po (c₅.nreg b + c₅.nreg cDd) po = _
      rw [upd_same, hval]
      have h6' := h6; simp only [hc5] at h6'; rw [v5D, v5T] at h6'
      simp only [hc5]; rw [v5b, v5D]; unfold convM; rw [ite_eq_left h6']
    · show upd c₅.nreg po _ r = _
      exact upd_other _ _ _ hr
  · refine (IRS.ifF h6 (IRS.instr1 (i := .subN po cDd cT) hI₅ hpo.1)).mono (by norm_num) ?_
    rintro c' rfl
    refine hpost _ ?_ (fun r hr => ?_) rfl
    · show upd c₅.nreg po (c₅.nreg cDd - c₅.nreg cT) po = _
      rw [upd_same, hval]
      have h6' := h6; simp only [hc5] at h6'; rw [v5D, v5T] at h6'
      simp only [hc5]; rw [v5D, v5T]; unfold convM; rw [ite_eq_right h6']
    · show upd c₅.nreg po _ r = _
      exact upd_other _ _ _ hr

end

end SweepIo

end Chazelle.Core
