module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvRLvB
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Core.OracleQueryExec
public import Mathlib.Data.List.GetD

namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)
variable {Q : Polygon}

/-! ## Vertices of the interior walk -/

/-- The vertex of `Q` at vertex `p` of the interior walk. -/
noncomputable def iv (Q : Polygon) (p : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then p else Q.n - 1 - p
variable {p : ℕ}
theorem iv_lt (hp : p < Q.n) : iv Q p < Q.n := by
  zumta
theorem iw_vtx (hp : p < Q.n) : (interiorWalk Q).vtx p = Q.vtx zttpr := by
  unfold iv
  zucla
  · zunyq; exact Trans.iw_vtx_left hL p
  · zunyq; exact Trans.iw_vtx_right hL hp
theorem mi_n : (interiorModel Q).W.n = Q.n := interiorModel_n Q

/-! ## The chain of a stretch of the interior walk -/

/-- The first vertex (in `Q`) of the chain read along the interior walk from `u` for `L`
steps. -/
noncomputable def cStart (Q : Polygon) (u L : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then u else ztjlk % Q.n
theorem cStart_lt {u L : ℕ} (hu : u < Q.n) : cStart Q u L < Q.n := by
  unfold cStart; split_ifs
  · exact hu
  · zuisr
theorem uStart_cStart {u L : ℕ} (hu : u < Q.n) (hL : L < Q.n) : uStart Q ztllx L = u := by
  unfold uStart cStart
  by_cases hl : Mountain.LeftInside Q
  · zunyr; exact Nat.mod_eq_of_lt hu
  · zunyr
    have e : (ztjlk % Q.n + L) % Q.n = Q.n - 1 - u := by
      rw [Nat.mod_add_mod, show Q.n - 1 - u + zttbm + L = (Q.n - 1 - u) + Q.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt by_omega]
    omega

/-- **The chain of the stretch** of `L` edges of the interior walk from `u`. -/
noncomputable def ch (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : Chain :=
  subChain Q ztllx L h1 h2
theorem ch_m {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} : (ch Q u L h1 h2).m = L := rfl
theorem ch_P {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} : (ch Q u L h1 h2).P = Q := rfl

/-- The tour offset of the chain read along the interior walk. -/
noncomputable def tau (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : ℕ :=
  WalkEmbed.tpos ztra ztjzd
theorem tau_lt {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} : tau Q u L h1 h2 < 2 * L :=
  WalkEmbed.tpos_lt _ _
theorem cm_n' {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} :
    (chainModel ztra).W.n = 2 * L + 7 := WalkEmbed.cm_n _

/-- **The interior walk agrees with the chain model walk** from `u`, resp. `6 + τ`, up to the top
of the chain or the end of the stretch. -/
theorem agree_pre {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) :
    WalkEmbed.Agree ztkb (chainModel ztra).W u
      ztgcu (min L ztnc) := by
  zuip
  zuftu
  have e1 := iw_tour (a := cStart Q u L) (hm1 := h1) (hm := h2) hQ1 (d := d)
    by_omega
  zueeb
  zukd
  zubas
  exact (WalkEmbed.walk_tour _ _ d (by
    show tau Q u L h1 h2 + d ≤ 2 * L; omega)).symm

/-- **After the top** (when the tour passes the box inside the stretch): the interior walk from
`u + L₁` agrees with the chain model walk from its vertex `6`. -/
theorem agree_post {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)
    (hs : L < tau Q u L h1 h2) :
    WalkEmbed.Agree ztkb (chainModel ztra).W
      ztzyi 6 ztztu := by
  zuip
  zuftu
  zubas
  have e1 := iw_tour (a := cStart Q u L) (hm1 := h1) (hm := h2) hQ1
    (d := 2 * L - tau Q u L h1 h2 + d) by_omega
  zueeb
  rw [show u + ztnc + d = u + (2 * L - tau Q u L h1 h2 + d) by ring, e1]
  have e2 := WalkEmbed.walk_after ztra ztjzd d (by
    show d ≤ 2 * L; omega)
  have e3 : (6 + WalkEmbed.tpos ztra ztjzd +
      (2 * (ch Q u L h1 h2).m - WalkEmbed.tpos ztra ztjzd) + 7 + d) %
      (chainModel ztra).W.n = ztfmw % (chainModel ztra).W.n := by
    rw [cm_n', ch_m]
    have : WalkEmbed.tpos ztra _ < 2 * L := tau_lt
    rw [show 6 + WalkEmbed.tpos _ _ +
      (2 * L - WalkEmbed.tpos _ _) + 7 + d = ztfmw + (2 * L + 7) by
      omega, Nat.add_mod_right]
  zvnak at e2
  tauto

/-! ## The point set of the interior subarc -/
theorem key_eq (M : Model) (Q : Polygon) (x : WPos) : M.key Q x = x.edge + M.param Q x := rfl

/-! ## Chain arcs -/
section chainArc
variable {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n)

/-- The chain model of the stretch. -/
noncomputable abbrev MC (Q : Polygon) (u L : ℕ) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) : Model :=
  chainModel ztra
include hu in
/-- The start parameter is the same in both models. -/
theorem param_start (h₁ : ℕ) :
    (MC Q u L h1 h2).param Q ⟨6 + tau Q u L h1 h2, h₁⟩ = (interiorModel Q).param Q ztcyh := by
  zucvs
  zubas
  have h0 : 0 < min L ztnc := by_omega
  have := param_agree (M := interiorModel Q) (M' := MC Q u L h1 h2) hA Q h0 h₁
  rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, cm_n',
    Nat.mod_eq_of_lt by_omega] at this
  simp_all
include hu in
/-- The end parameter is the same in both models (no split). -/
theorem param_end_one {e h₂ : ℕ} (hs : tau Q u L h1 h2 ≤ L) (he : e < L ∨ zterr) :
    (MC Q u L h1 h2).param Q ztivz =
      (interiorModel Q).param Q ztro := by
  zugrr
  · zucvs
    have := param_agree (M := interiorModel Q) hA Q
      (d := e) by_omega h₂
    rw [mi_n, cm_n', Nat.mod_eq_of_lt (show 6 + tau Q u L h1 h2 + e < 2 * L + 7 by omega)]
      at this
    simp_all
  · rfl
include hu in
/-- The end parameter is the same in both models (after the top). -/
theorem param_end_two {e h₂ : ℕ} (hs : L < tau Q u L h1 h2)
    (hle : 2 * L - tau Q u L h1 h2 ≤ e) (he : e < L ∨ zterr) :
    (MC Q u L h1 h2).param Q ztygc =
      (interiorModel Q).param Q ztro := by
  zugrr
  · zudyb
    have := param_agree (M := interiorModel Q) hA Q
      (d := e - ztnc) by_omega h₂
    zubas
    rw [mi_n, cm_n', Nat.mod_eq_of_lt (show 6 + (e - ztnc) < 2 * L + 7 by
      omega), show u + (2 * L - tau Q u L h1 h2) + (e - (2 * L - tau Q u L h1 h2)) = u + e by
      omega] at this
    simp_all
  · rfl
include hu in
/-- **The chain arc, no split**: the same point set as the interior subarc. -/
theorem chain_arcSet_one {e h₁ h₂ : ℕ} (hs : tau Q u L h1 h2 ≤ L)
    (hx : 0 ≤ (interiorModel Q).param Q ztcyh ∧ (interiorModel Q).param Q ztcyh < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ztro ∧
      (interiorModel Q).param Q ztro < 1)
    (he : e < L ∨ zterr)
    (hxy : (interiorModel Q).param Q ztcyh < e + (interiorModel Q).param Q ztro) :
    (MC Q u L h1 h2).arcSet ztezn
      ((MC Q u L h1 h2).key Q ztivz) =
      oset ztkb u ztynq
        ztyep := by
  zubaf

  zubas
  zueha

  rw [key_eq, key_eq, param_start hu h1 h2, param_end_one hu h1 h2 hs he]
  zukcc
  have hb0 : (0 : ℝ) ≤ ((g + e : ℕ) : ℝ) + t₂ := by_grind
  have hbn : ((g + e : ℕ) : ℝ) + t₂ < (MC Q u L h1 h2).W.n := by
    have : ((g + e : ℕ) : ℝ) + 1 ≤ (MC Q u L h1 h2).W.n := by
      zujjo
    grind
  show (MC Q u L h1 h2).arcSet ztmyw (((g + e : ℕ) : ℝ) + t₂) = _
  rw [arcSet_eq_oset _ hg' hx.1 hx.2 hb0 hbn]
  have hmod : (g + e) % (MC Q u L h1 h2).W.n = g + e := Nat.mod_eq_of_lt by_omega
  have hlap : (e : ℝ) + t₂ ≤ x + (MC Q u L h1 h2).W.n := by
    grind
  have hl := len_key hg' hx.2 hy.1 hxy hlap
  zukvb
  rw [hl, show x + (e + t₂ - x) = e + t₂ by ring]
  have hyL : (e : ℝ) + t₂ ≤ ((min L ztnc : ℕ) : ℝ) := by
    zulqn
    zugrs
    · have : (e : ℝ) + 1 ≤ L := by exact_mod_cast he
      grind
    simp_all
  exact (oset_congr ztrkp hyL).symm
include hu in
/-- **The chain arcs, split at the top**: the union has the point set of the interior subarc. -/
theorem chain_arcSet_two {e h₁ h₂ : ℕ} (hs : L < tau Q u L h1 h2)
    (hle : 2 * L - tau Q u L h1 h2 ≤ e)
    (hx : 0 ≤ (interiorModel Q).param Q ztcyh ∧ (interiorModel Q).param Q ztcyh < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ztro ∧
      (interiorModel Q).param Q ztro < 1)
    (he : e < L ∨ zterr)
    (hxy : (2 * L - tau Q u L h1 h2 : ℕ) <
      e + (interiorModel Q).param Q ztro) :
    (MC Q u L h1 h2).arcSet ztezn
      ((MC Q u L h1 h2).key Q ztexi) =
      oset ztkb u ztynq
        ((2 * L - tau Q u L h1 h2 : ℕ) : ℝ) ∧
    (MC Q u L h1 h2).arcSet ((MC Q u L h1 h2).key Q ztbcw)
      ((MC Q u L h1 h2).key Q ztygc) =
      oset ztkb u ((2 * L - tau Q u L h1 h2 : ℕ) : ℝ)
        ztyep := by
  zubaf

  set L₁ := 2 * L - tau Q u L h1 h2 with hL₁
  zubas
  zueha

  have hL₁0 : 0 < L₁ := by_omega
  have hL₁L : L₁ < L := by_omega
  constructor
  · rw [key_eq, key_eq, param_start hu h1 h2, param_zero, add_zero]
    zukcc
    have hb0 : (0 : ℝ) ≤ ((2 * L + 6 : ℕ) : ℝ) := by_positivity
    have hbn : ((2 * L + 6 : ℕ) : ℝ) < (MC Q u L h1 h2).W.n := by
      zvmxq; grind
    have hb' : ((2 * L + 6 : ℕ) : ℝ) = (((g + L₁) % (MC Q u L h1 h2).W.n : ℕ) : ℝ) + 0 := by
      rw [add_zero, Nat.mod_eq_of_lt by_omega]
      zugjy
    show (MC Q u L h1 h2).arcSet _ ((2 * L + 6 : ℕ) : ℝ) = _
    rw [arcSet_eq_oset _ hg' hx.1 hx.2 hb0 hbn, hb']
    have hL₁r : ztiwy := by exact_mod_cast hL₁0
    have hlap : (L₁ : ℝ) + 0 ≤ x + (MC Q u L h1 h2).W.n := by
      zubdb
      have : (L₁ : ℝ) ≤ ((2 * L + 7 : ℕ) : ℝ) := by exact_mod_cast by_grind
      grind
    rw [len_key hg' hx.2 le_rfl by_grind hlap,
      show x + (L₁ + 0 - x) = L₁ by ring]
    exact (oset_congr ztrkp (by rw [min_eq_right by_omega])).symm
  · zudyb
    rw [key_eq, key_eq, param_zero, param_end_two hu h1 h2 hs hle he, add_zero]
    have h6 : (6 : ℕ) < (MC Q u L h1 h2).W.n := by_omega
    have hb0 : (0 : ℝ) ≤ ((6 + zthgn : ℕ) : ℝ) + t₂ := by_grind
    have hbn : ((6 + zthgn : ℕ) : ℝ) + t₂ < (MC Q u L h1 h2).W.n := by
      have : ((6 + zthgn : ℕ) : ℝ) + 1 ≤ (MC Q u L h1 h2).W.n := by
        zujjo
      grind
    have ha : (((6 : ℕ) : ℝ)) = ((6 : ℕ) : ℝ) + 0 := by_ring
    show (MC Q u L h1 h2).arcSet ((6 : ℕ) : ℝ) _ = _
    rw [ha, arcSet_eq_oset _ h6 le_rfl zero_lt_one hb0 hbn]
    have hmod : (6 + zthgn) % (MC Q u L h1 h2).W.n = 6 + zthgn :=
      Nat.mod_eq_of_lt by_omega
    have hpos : (0 : ℝ) < (e - L₁ : ℕ) + t₂ := by
      zuhvr

    have hlap : ((e - L₁ : ℕ) : ℝ) + t₂ ≤ 0 + (MC Q u L h1 h2).W.n := by
      grind
    have hl := len_key h6 zero_lt_one hy.1
      hpos hlap
    zukvb
    rw [hl, show (0 : ℝ) + (((e - L₁ : ℕ) : ℝ) + t₂ - 0) = ((e - L₁ : ℕ) : ℝ) + t₂ by ring]
    have hy' : ((e - L₁ : ℕ) : ℝ) + t₂ ≤ ((L - L₁ : ℕ) : ℝ) := by
      zugrs
      · have : ((e - L₁ : ℕ) : ℝ) + 1 ≤ ((L - L₁ : ℕ) : ℝ) := by
          zuhuk
        grind
      · zuefu

    rw [← oset_congr hA hy', ← oset_shift _ _ L₁ le_rfl]
    zucr
    · ring
    · zuhvr
end chainArc
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)
open Chazelle.Visibility (xAt)
variable {Q : Polygon}

/-! ## Boundary symbolic points -/

/-- **A boundary symbolic point** of `Q`: a vertex, or a point of an edge strictly between the
heights of its ends. -/
def BSym (Q : Polygon) : SymPt → Prop
  | .vtx q => q < Q.n
  | .onEdge e h => e < Q.n ∧ h < Q.n ∧
      (ztbaka ∨
        ztbakb)
theorem BSym.lt {s : SymPt} (h : BSym Q s) : s.Lt Q.n := by
  cases s with
  | vtx q => exact h
  | onEdge e h' => exact ⟨h.1, h.2.1⟩
theorem iv_iv {q : ℕ} (hq : q < Q.n) : iv Q zttps = q := by
  zumta

/-- The edge of the interior walk carrying the edge `e` of `Q`. -/
noncomputable def iEdge (Q : Polygon) (e : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then e else if e + 1 < Q.n then Q.n - 2 - e else Q.n - 1
theorem iEdge_lt (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) : iEdge Q e < Q.n := by
  unfold iEdge; grind

/-- The two ends of the interior walk edge `iEdge e` are the ends of the edge `e` of `Q`. -/
theorem iEdge_ends (hn : 3 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    (iv Q ztfso = e ∧ iv Q ztflw = ztda % Q.n) ∨
      (iv Q ztfso = ztda % Q.n ∧ iv Q ztflw = e) := by
  unfold iEdge iv
  zucla
  · simp_all
  · zuckr
    right
    zuhsm
    · zuckq
      rw [Nat.mod_eq_of_lt (show Q.n - 2 - e + 1 < Q.n by omega), Nat.mod_eq_of_lt h1]
      omega
    · zuckq
      rw [show Q.n - 1 + 1 = Q.n by omega, Nat.mod_self, show e + 1 = Q.n by omega, Nat.mod_self]
      omega

/-- **The interior-walk position of a boundary symbolic point.** -/
noncomputable def iPos (Q : Polygon) : SymPt → WPos
  | .vtx q => ⟨iv Q q, 0⟩
  | .onEdge e h => ⟨iEdge Q e, h + 1⟩
variable {p : ℕ}
theorem mi_wa (hp : p < Q.n) : (interiorModel Q).wa p = Q.vtx zttpr := iw_vtx hp
theorem mi_wb (hp : p < Q.n) :
    (interiorModel Q).wb p = Q.vtx (iv Q ztwqx) := by
  zumrf
  zumos
  exact iw_vtx ztcv

/-- The parameter of a height strictly between the heights of the ends. -/
theorem param_between {a b y : ℝ} (h : zthdk ∨ (b < y ∧ y < a)) :
    0 < ztkhj / zthu ∧ ztkhj / zthu < 1 := by
  zuwr
  · have hb : ztmsn := by_linarith
    constructor
    · simp_all
    · rw [div_lt_one hb]; linarith
  · have hb : ztsdm := by_linarith
    constructor
    · exact div_pos_of_neg_of_neg by_linarith hb
    · rw [div_lt_one_of_neg hb]; linarith

/-- **The interior position of a boundary symbolic point** is proper, on the walk, and evaluates
to the point. -/
theorem iPos_spec (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {s : SymPt} (hs : BSym Q s) :
    ProperPos ztd Q Q.n zttpc ∧ (iPos Q s).edge < Q.n ∧
      (interiorModel Q).pos Q zttpc = s.eval Q := by
  cases s with
  | vtx q =>
    have hq : q < Q.n := hs
    refine ⟨ztdxk, iv_lt hq, ?_⟩
    show lerp ((interiorModel Q).wa zttps) _ 0 = Q.vtx q
    rw [lerp_zero, mi_wa ztvxm, iv_iv hq]
  | onEdge e h =>
    obtain ⟨he, hh, hbt⟩ := hs
    have hp := iEdge_lt by_grind he
    have hwa := mi_wa hp
    have hwb := mi_wb hp
    have hnh : ((interiorModel Q).wa ztfso).2 ≠ ((interiorModel Q).wb ztfso).2 := by
      zucpy
      zuqz
      · grind
      grind
    -- the parameter lies in `(0, 1)`
    have hpar : 0 < (interiorModel Q).param Q zthni ∧
        (interiorModel Q).param Q zthni < 1 := by
      zufde
      zubi
      rw [ite_eq_right hnh, hwa, hwb]
      zuqz
      · zvmws; exact param_between hbt
      · zvmws; exact param_between hbt.symm
    refine ⟨⟨hpar.1.le, hpar.2, by_tauto⟩, hp, ?_⟩
    have hok : HostEdgeOK Q.n (.vtx (iv Q ztfso)) (.vtx (iv Q ztflw)) := by
      zuqz
      · zuiho
      · zuiho
    have := ShootCut.pos_eq_onEdge _ hD by_omega (h := h)
      (sp₁ := .vtx _) (sp₂ := .vtx _) hwa hwb
      ztvxl ztyjj hok hnh
    rw [show iPos Q _ = zthni from rfl, this]
    zucr
    zuqz
    · zvmws; simp [ShootCut.edgeOf]
    · zuea
      zulry
      zucjw
      zuchg
      -- `e = (e + 2) mod n` is impossible for `n ≥ 3`
      have : e = (e + 2) % Q.n := by
        grind
      rcases (show e + 2 < Q.n ∨ e + 2 = Q.n ∨ e + 2 = Q.n + 1 by omega) with h1 | h1 | h1
      · zufu
      · rw [h1, Nat.mod_self] at this; omega
      · rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt by_omega] at this; omega

/-! ## Hit points of a chain model -/
section chain
variable (C : Chain)

/-- The vertex of `Q = C.P` at the walk vertex `e` (`6 ≤ e ≤ 2m + 6`) of the chain model. -/
noncomputable def cVtx (e : ℕ) : ℕ := (C.s + C.sideIdx C.sideBeta ztbcs) % C.P.n

/-- **The boundary symbolic point of a chain-model position on the chain.** -/
noncomputable def hitSym (e h : ℕ) : SymPt := by
  classical
  exact if e < 6 ∨ 2 * C.m + 6 ≤ e then .vtx ztbabc
    else if h = 0 ∨ h - 1 = cVtx C e then .vtx ztcuz
    else .onEdge (ShootCut.edgeOf C.P.n ztbadm ztbasd) zthhn
theorem cVtx_lt (e : ℕ) : cVtx C e < C.P.n := Nat.mod_lt _ C.n_pos
variable {e : ℕ}
theorem cm_vtx_tour (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) :
    (chainModel C).W.vtx e = C.P.vtx ztcuz := by
  zugqb
  show (C.sideWalk C.sideBeta).vtx _ = _
  zudth
  rfl

/-- The points of the walk edges `0 … 5` of a chain model (the box and the slit down) are not
on the chain. -/
theorem box_pos_not_mem (he : e < 6) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) :
    lerp ztiey ((chainModel C).W.vtx (ztda % (chainModel C).W.n)) t ∉
      C.set := by
  zuhgp
  have hb := C.set_subset_box hmem
  zulll
  zubo
  zumco
  zucmi
  zubt
  zvmxq at hmem hb htop
  simp only [Chain.mem_box_iff] at hb
  have hs : ((chainModel C).W.vtx 6) = C.top := C.sideWalk_vtx_six _
  interval_cases e
  · zubyl
    zuffb

    zublt
    zugza

  · zubyl
    have e0 : ztwsk := rfl
    have e1 : ztwsl := rfl
    zublt
    zuiot

  · zubyl
    have e0 : ztwsl := rfl
    have e1 : ztwvm := rfl
    zublt
    simp only [Chazelle.Geometry.lerp_snd] at hb
    grind
  · zubyl
    have e0 : ztwvm := rfl
    have e1 : ztytn := rfl
    zublt
    zuiot

  · zubyl
    have e0 : ztytn := rfl
    have e1 : ztidf := rfl
    zublt
    zugza

  · zvmyc at htop
    have e0 : ztidf := rfl
    rw [e0, hs] at htop
    zuhov
    nlinarith

/-- **The boundary symbolic point of a hit**: a proper chain-model position (edge `< 2m + 7`)
whose point lies on the chain is a boundary symbolic point of `Q = C.P` with that point. -/
theorem hitSym_spec (hD : DistinctHeights C.P) {e h : ℕ}
    (hp : ProperPos ztc C.P C.P.n ztcq) (he : e < 2 * C.m + 7)
    (hmem : (chainModel C).pos C.P ztcq ∈ C.set) :
    BSym C.P (hitSym C e h) ∧ (hitSym C e h).eval C.P = (chainModel C).pos C.P ztcq := by
  zucmi
  zubt
  have hnP := C.add_one_le
  have hpar0 := hp.1
  have hpar1 := hp.2.1
  unfold hitSym
  by_cases hbox : e < 6
  · exfalso
    exact box_pos_not_mem C hbox hpar0 hpar1 hmem
  by_cases hslit : 2 * C.m + 6 ≤ e
  · -- the slit up from the top: the point is the top
    zufup
    simp only [hbox, hslit, or_true, ↓reduceIte]
    refine ⟨Nat.mod_lt _ C.n_pos, ?_⟩
    have hwa : (chainModel C).wa e = C.top := by
      zujpz
      rw [he', cm_vtx_tour C by_omega le_rfl]
      zucfe

    have hwb : (chainModel C).wb e = C.slitTop := by
      unfold Model.wb; rw [hn, he', show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]; rfl
    zulll
    unfold Model.pos at htop ⊢
    rw [hwa, hwb] at htop ⊢
    zuhov
    zumco
    have ht : ztykw := by_nlinarith
    rw [ht, lerp_zero]; rfl
  simp only [hbox, hslit, or_self, ↓reduceIte]
  -- a walk edge of the double boundary
  have hwa : ztmrd := cm_vtx_tour C by_omega by_omega
  have hwb : ztbanl := by
    zueex

  -- the two ends are consecutive vertices of the chain
  zucav

  have hcons : HostEdgeOK C.P.n ztbadm ztbasd := by
    simp only [HostEdgeOK, cVtx, e7]
    rcases hstep with h1 | h1
    · grind
    grind
  have hne : ztyym := by
    zulbj

    zuchg
    have := C.sideEdgeIdx_inj hk1 hk2 hc
    omega
  have hnh : ((chainModel C).wa e).2 ≠ ((chainModel C).wb e).2 := by
    rw [hwa, hwb]; exact hD _ _ ztjsr ztnwt hne
  by_cases hv : h = 0 ∨ h - 1 = cVtx C e
  · zuipn
    refine ⟨cVtx_lt C e, ?_⟩
    have ht : ztykw := by
      zujue
      · simp_all
      · have h0 := hv.resolve_left hz
        zulr
        zufde
        simp_all
    show C.P.vtx _ = lerp _ _ _
    simp_all
  · zuipn
    zugrj
    obtain ⟨h0, hne'⟩ := hv
    zulr
    simp only [Nat.add_sub_cancel] at hne' ⊢
    have hh' : h' < C.P.n := by have := hp.2.2; simp_all
    have hpos := ShootCut.pos_eq_onEdge _ hD by_omega (h := h')
      (sp₁ := .vtx _) (sp₂ := .vtx _) hwa hwb ztjsr
      ztnwt hcons hnh
    refine ⟨?_, hpos.symm⟩
    -- the parameter is in `(0, 1)`: the height lies strictly between the ends
    have hpar : (chainModel C).param C.P ztcju =
        ((C.P.vtx h').2 - (C.P.vtx ztcuz).2) /
          ((C.P.vtx ztwts).2 - (C.P.vtx ztcuz).2) := by
      zudcl
    have hpos0 : 0 < (chainModel C).param C.P ztcju := by
      rcases hpar0.lt_or_eq with hlt | heq
      · omega
      · exfalso
        zvokb at heq
        have hden : (C.P.vtx ztwts).2 - (C.P.vtx ztcuz).2 ≠ 0 := by
          grind
        have := hD _ _ hh' ztjsr hne'
        grind
    have hbt : ((C.P.vtx ztcuz).2 < (C.P.vtx h').2 ∧
        (C.P.vtx h').2 < (C.P.vtx ztwts).2) ∨
        ((C.P.vtx ztwts).2 < (C.P.vtx h').2 ∧
          (C.P.vtx h').2 < (C.P.vtx ztcuz).2) := by
      zvokb at hpos0 hpar1
      set a := (C.P.vtx ztcuz).2
      set b := (C.P.vtx ztwts).2
      set y := (C.P.vtx h').2
      rcases lt_or_gt_of_ne (show b - a ≠ 0 from by
          grind) with hd | hd
      · right
        zudcw

        · linarith
        · rw [div_lt_one_of_neg hd] at hpar1
          simp_all
      · left
        zudcw

        · rw [div_lt_one hd] at hpar1
          simp_all
        grind
    -- the edge of `Q` carrying the walk edge
    zulry
    split_ifs with hcase
    · refine ⟨cVtx_lt C e, hh', ?_⟩
      simp_all
    · refine ⟨cVtx_lt C _, hh', ?_⟩
      have hc2 : cVtx C e = (cVtx C ztda + 1) % C.P.n := by
        simp only [HostEdgeOK] at hcons
        omega
      grind
end chain

/-! ## Inner points -/

/-- **Points within the coordinate bound are inner points of a chain model** (the box band). -/
theorem innerPt_chain (C : Chain) {z : Point} (h1 : |z.1| ≤ Jordan.coordBound C.P)
    (h2 : |z.2| ≤ Jordan.coordBound C.P) : (chainModel C).InnerPt z := by
  zumch
  zucmi
  zubt
  zubbq

  rw [abs_le] at h1 h2
  refine ztbrc
  · grind
  · grind
  · grind
  grind

/-- **Inner points of the interior model lie within the coordinate bound of `Q`.** -/
theorem innerPt_interior_bound {z : Point} (h : (interiorModel Q).InnerPt z) :
    |z.1| ≤ Jordan.coordBound Q ∧ |z.2| ≤ Jordan.coordBound Q := by
  obtain ⟨⟨p, q, hp, hq, hp1, hq1⟩, ⟨p', q', hp', hq', hp1', hq1'⟩⟩ := h
  rw [mi_n] at hp hq hp' hq'
  have hv : ∀ r, r < Q.n → ((interiorModel Q).W.vtx r) = Q.vtx _ := fun r hr => iw_vtx hr
  rw [hv p hp] at hp1
  rw [hv q hq] at hq1
  rw [hv p' hp'] at hp1'
  rw [hv q' hq'] at hq1'
  have a1 := abs_le.1 (Jordan.abs_snd_vtx_le_coordBound Q ztvxl)
  have a2 := abs_le.1 (Jordan.abs_snd_vtx_le_coordBound Q ztvxm)
  have a3 := abs_le.1 (Jordan.abs_fst_vtx_le_coordBound Q (iv_lt hp'))
  have a4 := abs_le.1 (Jordan.abs_fst_vtx_le_coordBound Q (iv_lt hq'))
  grind
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one lerp_fst lerp_snd)
variable {Q : Polygon}

/-! ## Point sets -/
theorem oset_mod (W : Polygon) (g : ℕ) (x y : ℝ) : oset W (g % W.n) x y = oset W g x y := by
  zumaj
  · zufh
    exact ztfjx
  · zufh
    exact ztfjx

/-- **The points of a subarc lie on its chain.** -/
theorem oset_sub_set {u L : ℕ} (hu : u < Q.n) (h1 : 1 ≤ L) (h2 : L + 1 ≤ Q.n) {x y : ℝ}
    (hy : y ≤ L) : oset ztkb u x y ⊆ (ch Q u L h1 h2).set := by
  rintro _ ⟨d, t, ht0, ht1, hx, hdy, rfl⟩
  zuftu
  have hd : d ≤ L := by
    zujvv

  have tv : ∀ k, k ≤ L → (interiorWalk Q).vtx _ =
      WalkEmbed.tourV ztra _ k := fun k hk => by
    have e1 := iw_tour (a := cStart Q u L) (hm1 := h1) (hm := h2) hQ1 hk
    zueeb
    exact e1
  zudsi
  · have hd1 : ztsht := by
      grind
    rw [tv d hd, show u + d + 1 = u + ztet by ring, tv _ hd1]
    unfold jStart
    split_ifs
    · rw [ShootCut.tourV_up _ hd, ShootCut.tourV_up _ hd1]
      exact ShootCut.segment_mem_set _ (show d < (ch Q u L h1 h2).m by rw [ch_m]; omega)
        (ShootCut.lerp_mem_segment ht0 ht1)
    · have e1 : WalkEmbed.tourV _ L d = (ch Q u L h1 h2).vertex _ :=
        ShootCut.tourV_down ztra hd
      have e2 : WalkEmbed.tourV _ L _ =
          (ch Q u L h1 h2).vertex _ := ShootCut.tourV_down ztra hd1
      zuea
      refine ShootCut.segment_mem_set _ (k := L - ztet) ztnte ?_
      rw [show L - ztet + 1 = L - d by omega, Chazelle.Geometry.segment_comm]
      exact ShootCut.lerp_mem_segment ht0 ht1
  · rw [lerp_zero, tv d hd]
    unfold WalkEmbed.tourV
    exact Chain.vertex_mem_set _ (Chazelle.Chain.sideE_le (Nat.mod_lt _ (Chain.two_m_pos _)).le)

/-! ## Points of the interior walk are within the coordinate bound -/
theorem abs_lerp_le {a b : ℝ} {B t : ℝ} (ha : |a| ≤ B) (hb : |b| ≤ B) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : |a + t * zthu| ≤ B := by
  rw [abs_le] at *
  zueop

/-- A proper position of the interior walk lies within the coordinate bound of `Q`. -/
theorem mi_pos_bound {p h : ℕ} (hp : p < Q.n) (hpp : ProperPos ztd Q Q.n ztnk) :
    |((interiorModel Q).pos Q ⟨p, h⟩).1| ≤ Jordan.coordBound Q ∧
      |((interiorModel Q).pos Q ⟨p, h⟩).2| ≤ Jordan.coordBound Q := by
  zudot
  have ha := mi_wa hp
  have hb := mi_wb hp
  have i1 := iv_lt hp
  have i2 := iv_lt (p := ztr % Q.n) zthp
  zueew
  zubi
  rw [ha, hb, lerp_fst, lerp_snd]
  exact ⟨abs_lerp_le (Jordan.abs_fst_vtx_le_coordBound Q i1)
      (Jordan.abs_fst_vtx_le_coordBound Q i2) hpp.1 hpp.2.1.le,
    abs_lerp_le (Jordan.abs_snd_vtx_le_coordBound Q i1)
      (Jordan.abs_snd_vtx_le_coordBound Q i2) hpp.1 hpp.2.1.le⟩

/-! ## The normalized end -/

/-- **The normalized height code**: a code at the height of the start vertex of the edge becomes
the vertex code `0` (same key, same point). -/
noncomputable def nh (Q : Polygon) (e h : ℕ) : ℕ := by
  classical
  exact if h ≠ 0 ∧ h - 1 = iv Q e then 0 else h
variable {e h : ℕ}
theorem param_nh (he : e < Q.n) :
    (interiorModel Q).param Q ztpfh = (interiorModel Q).param Q ztcq := by
  unfold nh
  zugif
  · obtain ⟨h0, h1⟩ := hc
    zulr
    simp only [Nat.add_sub_cancel] at h1
    show (0 : ℝ) = _
    zufde
    zubi
    rw [mi_wa he, ← h1]
    simp
  · rfl
theorem nh_le : nh Q e h ≤ h := by
  zumtp
theorem nh_zero_or : nh Q e h = 0 ∨ nh Q e h = h := by
  zumtp

/-- A nonzero normalized code has a positive parameter. -/
theorem param_pos_nh (hD : DistinctHeights Q) (hn : 2 ≤ Q.n) {e h : ℕ} (he : e < Q.n)
    (hh : h ≤ Q.n) (hp0 : 0 ≤ (interiorModel Q).param Q ztcq) (h0 : nh Q e h ≠ 0) :
    0 < (interiorModel Q).param Q ztpfh := by
  have hnh := nh_zero_or.resolve_left h0
  rw [hnh] at h0 ⊢
  have hc : ¬ (h ≠ 0 ∧ h - 1 = iv Q e) := by
    intro hc; unfold nh at hnh; simp_all
  zulr
  have hne : h' ≠ iv Q e := by_omega
  rcases hp0.lt_or_eq with hlt | heq
  · omega
  · exfalso
    unfold Model.param at heq
    simp only at heq
    have hwa := mi_wa he
    have hwb := mi_wb he
    have hnh' : ztcrb := by
      zucpy
      have h1 := iv_lt he
      have h2 := iv_lt (p := ztda % Q.n) ztcv
      refine hD _ _ h1 h2 ?_
      unfold iv
      split_ifs
      · intro hc2
        zucpa
        · zuhkj
        · zuguk
      · intro hc2
        zucpa
        · zuhkj
        · zuguk
    rw [ite_eq_right hnh', eq_comm, div_eq_zero_iff] at heq
    rcases heq with heq | heq
    · rw [hwa] at heq
      exact hD _ _ by_omega zthyl hne by_linarith
    grind

/-! ## The plan of a query -/

/-- **The offset of the end edge** of an interior query from its start edge: `dOf`, or on one
edge `0` (the end after the start) or `n` (the query goes once around). -/
noncomputable def eeOf (Q : Polygon) (e₁ h₁ e₂ h₂ : ℕ) : ℕ := by
  classical
  exact if WalkEmbed.dOf Q.n e₁ e₂ = 0 then
    (if (interiorModel Q).param Q ztcbt < (interiorModel Q).param Q ztcbu then 0 else Q.n)
  else WalkEmbed.dOf Q.n e₁ e₂

/-- The number of walk edges met by a query whose end edge is at offset `ee`. -/
def spanL (ee h₂ : ℕ) : ℕ := ee + (if h₂ = 0 then 0 else 1)
theorem param_hgt_zero (M : Model) (e : ℕ) : M.param Q ztjy = 0 := rfl

/-- The weight of a query going once around past its start. -/
theorem arcWt_around {e₁ : ℕ} (he₁ : e₁ < Q.n) {x t₂ : ℝ} (hx : x < 1) (ht0 : 0 < t₂)
    (htx : t₂ ≤ x) : (interiorModel Q).arcWt ((e₁ : ℝ) + x) ((e₁ : ℝ) + t₂) = Q.n := by
  have hc : ∀ p, p < (interiorModel Q).W.n →
      ztcqn := fun p hp => by
    zueza
  rw [(interiorModel Q).arcWt_closed hc le_rfl by_grind by_grind, mi_n]
  zuluc
  grind

/-- **The plan of an interior query** (with the normalized end). -/
theorem plan_arc (hn : 3 ≤ Q.n) {e₁ h₁ e₂ h₂ : ℕ} (he₁ : e₁ < Q.n) (he₂ : e₂ < Q.n)
    (hx : 0 ≤ (interiorModel Q).param Q ztcbt ∧ (interiorModel Q).param Q ztcbt < 1)
    (hy : 0 ≤ (interiorModel Q).param Q ztcbu ∧ (interiorModel Q).param Q ztcbu < 1)
    (hnz : h₂ = 0 ∨ 0 < (interiorModel Q).param Q ztcbu) :
    (interiorModel Q).arcSet ztrr
        ztrs =
      oset ztkb e₁ ztwza
        (eeOf Q e₁ h₁ e₂ h₂ + (interiorModel Q).param Q ztcbu) ∧
    (interiorModel Q).param Q ztcbt < eeOf Q e₁ h₁ e₂ h₂ + (interiorModel Q).param Q ztcbu ∧
    (e₁ + eeOf Q e₁ h₁ e₂ h₂) % Q.n = e₂ ∧ eeOf Q e₁ h₁ e₂ h₂ ≤ Q.n ∧
    ((h₂ = 0 ∧ eeOf Q e₁ h₁ e₂ h₂ = spanL ztczg h₂) ∨
      (h₂ ≠ 0 ∧ eeOf Q e₁ h₁ e₂ h₂ + 1 = spanL ztczg h₂ ∧
        0 < (interiorModel Q).param Q ztcbu)) ∧
    1 ≤ spanL ztczg h₂ ∧
    (spanL ztczg h₂ ≤ Q.n → (interiorModel Q).arcWt
      ztrr ztrs =
        spanL ztczg h₂) ∧
    (Q.n < spanL ztczg h₂ → (interiorModel Q).arcWt
      ztrr ztrs = Q.n) := by
  set x := (interiorModel Q).param Q ztcbt with hxd
  set t₂ := (interiorModel Q).param Q ztcbu with ht₂
  set ee := eeOf Q e₁ h₁ e₂ h₂ with heed
  zufvu
  have hd := WalkEmbed.add_dOf he₁ he₂
  have hdl := WalkEmbed.dOf_lt hn0 e₁ e₂
  -- the offset and its properties
  have hE : (x < ee + t₂ ∧ (ee : ℝ) + t₂ ≤ x + Q.n) ∧ zterx % Q.n = e₂ ∧ ee ≤ Q.n ∧
      (ee = 0 → h₂ ≠ 0) := by
    rw [heed]
    unfold eeOf
    by_cases h0 : WalkEmbed.dOf Q.n e₁ e₂ = 0
    · zuhmd
      rw [h0, Nat.add_zero, Nat.mod_eq_of_lt he₁] at hd
      by_cases hlt : x < t₂
      · rw [ite_eq_left hlt]
        have h3 : (3 : ℝ) ≤ Q.n := by_simp_all
        refine ⟨by_grind, by
          rw [Nat.add_zero, Nat.mod_eq_of_lt he₁, hd], by_omega, fun _ hz => ?_⟩
        zvncr at ht₂
        have : ztsmq := by_simp_all
        grind
      · rw [ite_eq_right hlt]
        push Not at hlt
        refine ⟨⟨by linarith [hy.1, hx.2, (show (1 : ℝ) ≤ Q.n by exact_mod_cast by_grind)], by_linarith⟩, by rw [Nat.add_mod_right, Nat.mod_eq_of_lt he₁, hd], le_rfl,
          by grind⟩
    · zucqa
      have h1 : (1 : ℝ) ≤ WalkEmbed.dOf Q.n e₁ e₂ := by exact_mod_cast by_grind
      have h2 : zthnx := by exact_mod_cast hdl
      grind
  obtain ⟨⟨hxy, hlap⟩, hmod, heen, hee0⟩ := hE
  have hsp : ((h₂ = 0 ∧ ee = spanL ee h₂) ∨ (h₂ ≠ 0 ∧ ee + 1 = spanL ee h₂ ∧ 0 < t₂)) := by
    unfold spanL
    grind
  have hkc : keyCeil ee t₂ = spanL ee h₂ := by
    unfold keyCeil
    rcases hsp with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
    · zuefu

    grind
  have hb : (interiorModel Q).key Q ztcbu = ((zterx % Q.n : ℕ) : ℝ) + t₂ := by
    rw [hmod]; rfl
  have hu' : e₁ < (interiorModel Q).W.n := by rw [mi_n]; omega
  refine ⟨?_, hxy, hmod, heen, hsp, ?_, fun hle => ?_, fun hlt => ?_⟩
  · rw [key_eq, hb]
    have hb0 : (0 : ℝ) ≤ ((zterx % Q.n : ℕ) : ℝ) + t₂ := by_grind
    have hbn : ((zterx % Q.n : ℕ) : ℝ) + t₂ < (interiorModel Q).W.n := by
      zumos
      have : (zterx % Q.n : ℕ) + 1 ≤ Q.n := by_omega
      have : ((zterx % Q.n : ℕ) : ℝ) + 1 ≤ Q.n := by exact_mod_cast this
      grind
    rw [arcSet_eq_oset _ hu' hx.1 hx.2 hb0 hbn, mi_n, len_key he₁ hx.2 hy.1 hxy hlap]
    congr 1; ring
  · omega
  · have hc : ∀ p, p < (interiorModel Q).W.n →
        ztcqn := fun p hp => by
      zueza
    rw [key_eq, hb, ← hkc]
    have := arcWt_off _ hc le_rfl hu' ztbg hx.1 hx.2 hy.1 hy.2 hxy
      (Or.inl ⟨rfl, rfl, by rw [hkc, mi_n]; omega⟩)
    rw [mi_n] at this
    omega
  · -- once around: `ee = n`, the end on the start edge, before the start
    rcases hsp with ⟨h0, h1⟩ | ⟨h0, h1, ht0⟩
    · omega
    · have hen : ee = Q.n := by_omega
      rw [hen, Nat.add_mod_right, Nat.mod_eq_of_lt he₁] at hmod
      have htx : t₂ ≤ x := by
        grind
      rw [key_eq, key_eq]
      show (interiorModel Q).arcWt _ ((e₂ : ℝ) + t₂) = Q.n
      rw [← hmod]
      exact arcWt_around he₁ hx.2 ht0 htx
end
end IOrc
end Chazelle.Core
namespace Chazelle.Core
namespace IOrc
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)
variable {Q : Polygon}

/-- **A chain arc query**: the ends are proper positions on the walk of the chain model, non-vertex
ends are inner points, the weight is at most `γ`, and the point set is `S`. -/
def CArc (Q : Polygon) (C : Chain) (s e : WPos) (γ : ℕ) (S : Set Point) : Prop :=
  ProperPos ztc Q Q.n s ∧ ProperPos ztc Q Q.n e ∧
    s.edge < (chainModel C).W.n ∧ e.edge < (chainModel C).W.n ∧
    (s.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos Q s)) ∧
    (e.hgt = 0 ∨ (chainModel C).InnerPt ((chainModel C).pos Q e)) ∧
    (chainModel C).arcWt ztbaj ztbai ≤ γ ∧
    (chainModel C).arcSet ztbaj ztbai = S

/-- **A subarc of the interior walk** from `⟨u, sh⟩` to `⟨(u + ee) mod n, eh⟩` meeting `L ≤ n - 1`
walk edges (the end normalized). -/
structure SubOK (Q : Polygon) (u L sh ee eh : ℕ) : Prop where
  hu : u < Q.n
  h1 : 1 ≤ L
  h2 : L + 1 ≤ Q.n
  hs : ProperPos ztd Q Q.n ztujo
  he : ProperPos ztd Q Q.n ztuh
  hee : (eh = 0 ∧ ee = L) ∨
    (eh ≠ 0 ∧ ee + 1 = L ∧ 0 < (interiorModel Q).param Q ztuh)
  hxy : (interiorModel Q).param Q ztujo < ee + (interiorModel Q).param Q ztuh
theorem chain_counted (C : Chain) :
    ∀ p, p < (chainModel C).W.n → ztfxr :=
  fun p hp => chainModel_counted_iff C p hp
theorem keyCeil_le_succ {e : ℕ} {f : ℝ} : keyCeil e f ≤ e + 1 := by
  zufdj

/-- An inner point of the chain model from a proper interior position with the same point. -/
theorem innerPt_of_mi {C : Chain} (hC : C.P = Q) {p h : ℕ} (hp : p < Q.n)
    (hpp : ProperPos ztd Q Q.n ztnk) {z : Point}
    (hz : z = (interiorModel Q).pos Q ztnk) : (chainModel C).InnerPt z := by
  obtain ⟨b1, b2⟩ := mi_pos_bound hp hpp
  rw [← hz, ← hC] at *
  exact innerPt_chain C b1 b2
section
variable {u L sh ee eh : ℕ} (h : SubOK Q u L sh ee eh)
include h in
theorem sub_ee_le : ee ≤ L := by
  rcases h.hee with ⟨-, h1⟩ | ⟨-, h1, -⟩ <;> omega
include h in
theorem sub_he' : ee < L ∨ (ee = L ∧ eh = 0) := by
  rcases h.hee with ⟨h0, h1⟩ | ⟨-, h1, -⟩
  · omega
  omega
include h in
theorem sub_keyCeil : keyCeil ee ((interiorModel Q).param Q ztuh) = L := by
  unfold keyCeil
  rcases h.hee with ⟨h0, h1⟩ | ⟨h0, h1, h2⟩
  · simp_all
  grind
include h in
/-- **The chain arc of a subarc, no split.** -/
theorem chainArcs_one (hs : tau Q u L h.h1 h.h2 ≤ L) {γ : ℕ} (hγ : L ≤ γ) :
    CArc Q ztbww ztkye
      ⟨6 + tau Q u L h.h1 h.h2 + ee, eh⟩ γ
      (oset ztkb u ztjcm
        ztyeq) := by
  zucdf

  zudhz

  zuhzw
  have hpe := param_end_one hu h.h1 h.h2 (e := ee) (h₂ := eh) hs ztmoq
  zuivm
  refine ⟨ztfvw,
    ⟨by zungd; exact h.he.1, by zungd; exact h.he.2.1, h.he.2.2⟩,
    by grind, by_grind, ?_, ?_, ?_,
    chain_arcSet_one hu h.h1 h.h2 hs ztugr ⟨h.he.1, h.he.2.1⟩ ztmoq h.hxy⟩
  · right
    have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := 0)
      by_omega sh
    rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, hn,
      Nat.mod_eq_of_lt ztitm] at this
    zujva
  · zujsi
    · simp_all
    zubyf

    have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := ee)
      by_omega eh
    rw [mi_n, hn, Nat.mod_eq_of_lt ztiau] at this
    zujvb
  · zuglz

    have hw := arcWt_off ztzed (lo := 6) (hi := 2 * L + 6) hc
      by_simp_all (u := 6 + τ) (e := ee) by_grind by_omega
      h.hs.1 h.hs.2.1 h.he.1 h.he.2.1 h.hxy (Or.inr ztomu)
    rw [hn, Nat.mod_eq_of_lt ztiau, hk] at hw
    rw [key_eq, key_eq, hps, hpe]
    simp_all
include h in
/-- **The chain arcs of a subarc, split at the top.** -/
theorem chainArcs_two (hs : L < tau Q u L h.h1 h.h2) {γ : ℕ} (hγ : L ≤ γ) :
    CArc Q ztbww ztkye ztexi γ
      (oset ztkb u ztjcm
        ((2 * L - tau Q u L h.h1 h.h2 : ℕ) : ℝ)) ∧
    CArc Q ztbww ztbcw ⟨6 + (ee - (2 * L - tau Q u L h.h1 h.h2)), eh⟩ γ
      (oset ztkb u ((2 * L - tau Q u L h.h1 h.h2 : ℕ) : ℝ)
        ztyeq) := by
  zucdf

  zugyf
  zudhz

  have hle : ztscb := by rcases h.hee with ⟨-, h'⟩ | ⟨-, h', -⟩ <;> omega
  zuhzw
  have hpe := param_end_two hu h.h1 h.h2 (e := ee) (h₂ := eh) hs hle ztmoq
  zuivm
  have hA2 := agree_post hu h.h1 h.h2 hs
  have hxy2 : (L₁ : ℝ) < ee + (interiorModel Q).param Q ztuh := by
    rcases h.hee with ⟨h0, h'⟩ | ⟨h0, h', hp⟩
    · have : ztpgp := by exact_mod_cast (show L₁ < ee by omega)
      simp_all
    · have : ztfzw := by_simp_all
      linarith
  obtain ⟨hS1, hS2⟩ := chain_arcSet_two hu h.h1 h.h2 hs hle ztugr
    ⟨h.he.1, h.he.2.1⟩ ztmoq hxy2
  zuglz

  constructor
  · refine ⟨ztfvw,
      ⟨le_rfl, zero_lt_one, Nat.zero_le _⟩,
      by grind, by_grind, ?_,
      Or.inl rfl, ?_, hS1⟩
    · right
      have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA Q (d := 0)
        by_omega sh
      rw [Nat.add_zero, Nat.add_zero, mi_n, Nat.mod_eq_of_lt hu, hn,
        Nat.mod_eq_of_lt ztitm] at this
      zujva
    · have hw := arcWt_off ztzed (lo := 6) (hi := 2 * L + 6) hc
        by_grind (u := 6 + τ) (e := L₁) (t₂ := 0) by_grind by_omega
        h.hs.1 h.hs.2.1 le_rfl zero_lt_one
        (by have : ztiwy := by exact_mod_cast (show 1 ≤ L₁ by omega)
            linarith [h.hs.2.1])
        (Or.inr ⟨by unfold keyCeil; grind, by_grind⟩)
      rw [hn, Nat.mod_eq_of_lt (show 6 + τ + L₁ < 2 * L + 7 by omega)] at hw
      have hk0 : keyCeil L₁ (0 : ℝ) = L₁ := by unfold keyCeil; simp
      rw [key_eq, key_eq, hps, param_zero, add_zero,
        show ((2 * L + 6 : ℕ) : ℝ) = ((6 + τ + L₁ : ℕ) : ℝ) + 0 by
          zvncl; congr 1; omega]
      grind
  · refine ⟨ztdxk,
      ⟨by zungd; exact h.he.1, by zungd; exact h.he.2.1, h.he.2.2⟩,
      by grind, by_grind, Or.inl rfl,
      ?_, ?_, hS2⟩
    · zujsi
      · grind
      zubyf

      have := pos_agree (M := interiorModel Q) (M' := MC Q u L h.h1 h.h2) hA2 Q (d := ee - L₁)
        by_omega eh
      rw [mi_n, hn, Nat.mod_eq_of_lt ztxsj,
        show u + L₁ + ztfrc = u + ee by omega] at this
      zujvb
    · have hpos : (0 : ℝ) < ((ee - L₁ : ℕ) : ℝ) + (interiorModel Q).param Q ztuh := by
        have e1 : zticx := Nat.cast_sub hle
        grind
      have hw := arcWt_off ztzed (lo := 6) (hi := 2 * L + 6) hc
        by_grind (u := 6) (e := ee - L₁) (t₁ := 0) by_grind le_rfl
        le_rfl zero_lt_one h.he.1 h.he.2.1 hpos
        (Or.inr ⟨by have := keyCeil_le_succ (e := ee - L₁)
                        (f := (interiorModel Q).param Q ztuh)
                    omega, by_grind⟩)
      rw [hn, Nat.mod_eq_of_lt ztxsj] at hw
      rw [key_eq, key_eq, hpe, param_zero, show ((6 : ℕ) : ℝ) + 0 = ((6 : ℕ) : ℝ) + 0 from rfl]
      zujjy
      have := keyCeil_le_succ (e := ee - L₁) (f := (interiorModel Q).param Q ztuh)
      omega
end
end
end IOrc
end Chazelle.Core
section
set_option hygiene false
local macro "zqvb" : tactic => `(tactic| (obtain ⟨-, -, hne', -⟩ := arc_facts hN hne hr
                                          by_cases h : sk ztc Q N r < ek ztc Q N r))
local macro "zqvc" : tactic => `(tactic| (have hGM : ztebh := Or.inl ⟨C, hP, rfl⟩
                                          obtain ⟨δ, hδ, h⟩ := h
                                          obtain ⟨δ', hδ', h'⟩ := h'
                                          have e0 : 0 < min δ δ' / 2 := by_simp_all
                                          have e1 : min δ δ' / 2 < δ := by_grind
                                          have e2 : min δ δ' / 2 < δ' := by_grind
                                          exact interior_unique hN hGM hne hq hq' by_simp_all (h' _ e0 e2)))
local macro "zqvd" : tactic => `(tactic| (refine ⟨ek _ Q N r - sk _ Q N r, by_linarith, fun ε e1 e2 => ?_⟩
                                          unfold sideInArc; grind))
local macro "zqve" : tactic => `(tactic| (refine ⟨1, one_pos, fun ε e1 e2 => ?_⟩
                                          unfold sideInArc; simp_all))
local macro "zqvf" : tactic => `(tactic| have hGM : ztebh := Or.inl ⟨C, hP, rfl⟩)
local macro "zqvg" : tactic => `(tactic| (set s := sk ztc Q N p
                                          set e := ek ztc Q N p))
local macro "zqvh" : tactic => `(tactic| (set s := sk ztc Q N q
                                          set e := ek ztc Q N q))
local macro "zqvi" : tactic => `(tactic| (obtain ⟨δ, hδ, h⟩ := int_nhd hin
                                          exact ⟨δ, hδ, by_simp_all⟩))
local macro "zqvj" : tactic => `(tactic| (have hT6 := κT_ge C
                                          have hT7 := κT_lt C))
local macro "zqvk" : tactic => `(tactic| refine zipRel_of_mk by_linarith by_linarith ztrri ?_)
local macro "zqvl" : tactic => `(tactic| by_cases hc : (chainModel C).IsCut ztwjh y)
set_option hygiene true

/-!
# Lemma 3.6 (WP-H), part 29: the mirror of the chain in walk keys

The walk keys `κ ∈ [6, 2 m + 6]` are the tour positions of the double boundary of the chain; two
of them have the same point iff they are equal or their sum is `12 - 2 S` modulo `2 m`
(`mirror_sum`, and its converse `same_point_of_sum`).  In walk keys the mirror is two reflections:
of `[6, κT]` and of `[κT, 2 m + 6]` (`mk`), where `κT` is the key of the second visit of the top.
-/
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Chain (sidePt sideE sideInArc)
open Chazelle.Geometry (lerp lerp_zero)
namespace OracleQ
variable (C : Chain)

/-- **Tour positions with opposite tour coordinates have the same point.** -/
theorem same_point_of_opp {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) {t t' : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : ((tj C i + tj C i' : ℕ) : ℝ) + t + t' = 2 * C.m ∨
      ((tj C i + tj C i' : ℕ) : ℝ) + t + t' = 0) :
    sidePt ztcs ztcy t = sidePt ztcs ztetl t' := by
  rw [tour_pt C i hi, tour_pt C i' hi']
  have ha := tj_lt C i
  have hb := tj_lt C i'
  set a := tj C i with hadef
  set b := tj C i' with hbdef
  push_cast at h
  -- the fractional parts
  have hint : ∀ z : ℤ, (a : ℝ) + b + t + t' = z → t + t' = 0 ∨ t + t' = 1 := by
    zugh
    have h1 : ((z - a - b : ℤ) : ℝ) = t + t' := by push_cast; linarith
    have h2 : (z - a - b : ℤ) < 2 := by
      have : ((z - a - b : ℤ) : ℝ) < 2 := by_grind
      zufc
    have h3 : 0 ≤ (z - a - b : ℤ) := by
      have : (0 : ℝ) ≤ ((z - a - b : ℤ) : ℝ) := by_grind
      zufc
    rcases (by omega : (z - a - b : ℤ) = 0 ∨ (z - a - b : ℤ) = 1) with e | e
    · left; zuofv; simp
    · right; zuofv; simp
  zubt
  zuy
  · rcases hint ztbb by_simp_all with h0 | h1
    · have ht0 : ztbhh := by_linarith
      have ht0' : ztmwy := by_linarith
      zultf
      have hab : a + b = 2 * C.m := by
        have : ((a + b : ℕ) : ℝ) = ((2 * C.m : ℕ) : ℝ) := by_simp_all
        zufc
      unfold tk
      grind
    · have htp : ztfkp := by
        grind
      have htp' : ztrzn := by
        grind
      have hab : a + b + 1 = 2 * C.m := by
        have : ((a + b + 1 : ℕ) : ℝ) = ((2 * C.m : ℕ) : ℝ) := by_grind
        zufc
      unfold tk
      grind
  · have ht0 : ztbhh := by
      grind
    have ht0' : ztmwy := by
      grind
    zultf
    have hab : a + b = 0 := by
      have : ((a + b : ℕ) : ℝ) = 0 := by_simp_all
      zufc
    unfold tk
    simp_all

/-- A walk position with key in `[6, 2 m + 6]` is a tour position, up to the closing vertex. -/
theorem tour_norm {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6) :
    ∃ i : ℕ, ∃ e : ℕ, i < 2 * C.m ∧ ztlnc ∧ (p : ℝ) + t = 6 + i + t + e ∧
      sidePt ztcs p t = sidePt ztcs ztcy t := by
  zubt
  have hp6 : ztsaj := by
    have : (5 : ℝ) < p := by_linarith
    have : 5 < p := by_simp_all
    omega
  rcases Nat.lt_or_ge p ztcc with h | h
  · refine ⟨p - 6, 0, by_omega, Or.inl rfl, ?_, by_simp_all⟩
    simp_all
  · zudzk

    zukgf
    zudlw
    exact ⟨0, 2 * C.m, by_omega, Or.inr rfl, by_grind, sidePt_last C⟩

/-- **Keys with sum `12 - 2 S` modulo `2 m` have the same point.** -/
theorem same_point_of_sum {p p' : ℕ} (hp : p < 2 * C.m + 7) (hp' : p' < 2 * C.m + 7)
    {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6)
    (h6' : (6 : ℝ) ≤ p' + t') (h7' : (p' : ℝ) + t' ≤ 2 * C.m + 6)
    {z : ℤ} (hz : ztdj + ztjg = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z) :
    sidePt ztcs p t = sidePt ztcs p' t' := by
  zubt
  obtain ⟨i, e, hi, he, hk, hpt⟩ := tour_norm C hp ht ht1 h6 h7
  obtain ⟨i', e', hi', he', hk', hpt'⟩ := tour_norm C hp' ht' ht1' h6' h7'
  rw [hpt, hpt']
  refine same_point_of_opp C hi hi' ht ht1 ht' ht1' ?_
  -- the tour indices
  have e1 := Nat.mod_add_div ztwz ztbb
  have e2 := Nat.mod_add_div zteeg ztbb
  have ha : tj C i = ztwz % ztbb := rfl
  have hb : tj C i' = zteeg % ztbb := rfl
  set qa := ztwz / ztbb
  set qb := zteeg / ztbb
  have e1r : ((tj C i : ℕ) : ℝ) + 2 * C.m * qa = C.sideS C.sideBeta + i := by
    rw [ha]; exact_mod_cast e1
  have e2r : ((tj C i' : ℕ) : ℝ) + 2 * C.m * qb = C.sideS C.sideBeta + i' := by
    rw [hb]; exact_mod_cast e2
  have hA := tj_lt C i
  have hB := tj_lt C i'
  set A : ℝ := ((tj C i + tj C i' : ℕ) : ℝ) + t + t' with hAdef
  have hAz : ∃ w : ℤ, A = 2 * C.m * w := by
    have ee : (e : ℝ) + e' = 2 * C.m * (ztmlo + ztmlp : ℤ) := by
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;>
        simp [show 2 * C.m ≠ 0 by omega]; ring
    refine ⟨z - qa - qb - (ztmlo + ztmlp), ?_⟩
    zupah; push_cast at ee ⊢
    grind
  obtain ⟨w, hw⟩ := hAz
  have hA0 : 0 ≤ A := by_grind
  have hA4 : A < 4 * C.m := by
    zupah; push_cast
    have : ((tj C i : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hA
    have : ((tj C i' : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hB
    linarith
  zufvl
  have hw0 : 0 ≤ w := by
    zuca
    have : (w : ℝ) ≤ -1 := by exact_mod_cast by_grind
    nlinarith
  have hw2 : w < 2 := by
    zuca
    have : (2 : ℝ) ≤ w := by exact_mod_cast hc
    nlinarith
  rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
  · grind
  grind

/-- The tour index of the second visit of the top. -/
noncomputable def rT : ℕ := ztgcn % ztbb

/-- The key of the second visit of the top. -/
noncomputable def κT : ℝ := 6 + rT C
open Classical in
/-- **The mirror of the chain in walk keys**: the reflections of `[6, κT]` and `[κT, 2 m + 6]`. -/
noncomputable def mk (κ : ℝ) : ℝ := if κ ≤ κT C then 6 + κT C - κ else κT C + 2 * C.m + 6 - κ
theorem rT_lt : rT C < 2 * C.m := Nat.mod_lt _ (by have := C.one_le; omega)
theorem κT_ge : (6 : ℝ) ≤ κT C := by unfold κT; simp
theorem κT_lt : κT C < 2 * C.m + 6 := by
  unfold κT
  have : zthnz := by exact_mod_cast rT_lt C
  linarith

/-- The mirror stays in the tour range, and the sum of a key and its mirror is `12 - 2 S`
modulo `2 m`. -/
theorem mk_facts {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) :
    6 ≤ mk C κ ∧ mk C κ ≤ 2 * C.m + 6 ∧
      ∃ z : ℤ, κ + mk C κ = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z := by
  zuec
  have hr := Nat.mod_add_div ztgcn ztbb
  set q := ztgcn / ztbb
  have hrr : ((rT C : ℕ) : ℝ) + 2 * C.m * q = 4 * C.m - 2 * C.sideS C.sideBeta := by
    have : ((rT C + 2 * C.m * q : ℕ) : ℝ) = ((4 * C.m - 2 * C.sideS C.sideBeta : ℕ) : ℝ) := by
      tauto
    rw [Nat.cast_sub by_omega] at this; simp_all
  zqvj
  unfold mk
  zus
  · refine ⟨by_linarith, by_linarith, 2 - q, ?_⟩
    zuiqi
  · zubpo
    refine ⟨by_linarith, by_linarith, 3 - q, ?_⟩
    zuiqi

/-- **Keys of one point**: a key with sum `12 - 2 S` (mod `2 m`) with `κ` is `mk κ`, up to `2 m`. -/
theorem eq_mk_of_sum {κ κ' : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) (h6' : 6 ≤ κ')
    (h7' : κ' ≤ 2 * C.m + 6) {z : ℤ}
    (hz : κ + κ' = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z) :
    κ' = mk C κ ∨ κ' + 2 * C.m = mk C κ ∨ κ' = mk C κ + 2 * C.m := by
  obtain ⟨a1, a2, z0, hz0⟩ := mk_facts C h6 h7
  have hm : ztdjm := by exact_mod_cast C.one_le
  have hd : κ' - mk C κ = 2 * C.m * ((z - z0 : ℤ) : ℝ) := by_grind
  have hlt : ((z - z0 : ℤ) : ℝ) < 2 := by_nlinarith
  have hgt : -2 < ((z - z0 : ℤ) : ℝ) := by_nlinarith
  have h1 : z - z0 < 2 := by exact_mod_cast hlt
  have h2 : -2 < z - z0 := by exact_mod_cast hgt
  rcases (by omega : z - z0 = 0 ∨ z - z0 = 1 ∨ z - z0 = -1) with e | e | e <;> zvmwe at hd <;>
    push_cast at hd
  · grind
  · grind
  grind

/-! ## The zipper pairs -/
section Zip
variable {C} {Q : Polygon} {N : NF}

/-- The arc at spine position `q` contains the keys just before `y`. -/
def Before (C : Chain) (Q : Polygon) (N : NF) (q : ℕ) (y : ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc ztwlp ztwkp (y - ε)

/-- The arc at spine position `q` contains the keys just after `y`. -/
def After (C : Chain) (Q : Polygon) (N : NF) (q : ℕ) (y : ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc ztwlp ztwkp (y + ε)

/-- The interior of an arc is free of cuts. -/
theorem not_cut_of_int (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {x : ℝ}
    (hx : sideInArc ztwlo ztwnk x) :
    ¬ (chainModel C).IsCut ztwjh x :=
  (arc_facts hN hne hp).2.2.2 x hx

/-- **An interval ending at an interior key and free of cuts lies in the arc.** -/
theorem int_of_noCut_left (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {L κ : ℝ}
    (hκ : sideInArc ztwlo ztwnk κ)
    (hno : ∀ x, L < x → x ≤ κ → ¬ (chainModel C).IsCut ztwjh x)
    {x : ℝ} (h1 : L < x) (h2 : x ≤ κ) :
    sideInArc ztwlo ztwnk x := by
  obtain ⟨hs, he, -, -⟩ := arc_facts hN hne hp
  zqvg
  have hsL : ¬ (L < s ∧ s ≤ κ) := by_grind
  have heL : ¬ (L < e ∧ e ≤ κ) := by_grind
  zucri

/-- **An interval starting at an interior key and free of cuts lies in the arc.** -/
theorem int_of_noCut_right (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {q : ℕ} (hq : q < N.arcs.length) {κ R : ℝ}
    (hκ : sideInArc ztwlp ztwkp κ)
    (hno : ∀ x, κ ≤ x → x < R → ¬ (chainModel C).IsCut ztwjh x)
    {x : ℝ} (h1 : κ ≤ x) (h2 : x < R) :
    sideInArc ztwlp ztwkp x := by
  obtain ⟨hs, he, -, -⟩ := arc_facts hN hne hq
  zqvh
  have hsL : ¬ (κ ≤ s ∧ s < R) := by_grind
  have heL : ¬ (κ ≤ e ∧ e < R) := by_grind
  zucri

/-- A cut just before an interval inside an arc is the start of the arc. -/
theorem start_eq_of (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {c κ : ℝ} (hc : (chainModel C).IsCut ztwjh c)
    (hcκ : c < κ)
    (hin : ∀ x, c < x → x ≤ κ → sideInArc ztwlo ztwnk x) :
    sk ztc Q N p = c := by
  obtain ⟨-, -, -, hfree⟩ := arc_facts hN hne hp
  zqvg
  have hss : ¬ sideInArc s e s := by unfold sideInArc; simp
  have hκ := hin κ hcκ le_rfl
  zuirz
  have hs1 : ¬ (c < s ∧ s ≤ κ) := by_grind
  zuldf
  zucri

/-- A cut just after an interval inside an arc is the end of the arc. -/
theorem end_eq_of (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {q : ℕ} (hq : q < N.arcs.length) {c κ : ℝ} (hc : (chainModel C).IsCut ztwjh c)
    (hcκ : κ < c)
    (hin : ∀ x, κ ≤ x → x < c → sideInArc ztwlp ztwkp x) :
    ek ztc Q N q = c := by
  obtain ⟨-, -, -, hfree⟩ := arc_facts hN hne hq
  zqvh
  have hee : ¬ sideInArc s e e := by unfold sideInArc; simp
  have hκ := hin κ le_rfl hcκ
  zuirz
  have he1 : ¬ (κ ≤ e ∧ e < c) := by_grind
  zuldf
  zucri

/-- **The core of the zipper**: two arcs containing `κ` and its reflection `a + b - κ` in the
interval `[a, b]` meet at the ends of `[a, b]`, at the start of the first (its reflection in the
second), or at the end of the second (its reflection in the first). -/
theorem zip_core (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) {a b κ : ℝ} (haκ : a < κ) (hκb : κ < b)
    (hmk : ∀ x, a < x → x < b → mk C x = a + b - x)
    (hκp : sideInArc ztwlo ztwnk κ)
    (hκq : sideInArc ztwlp ztwkp (a + b - κ)) :
    (After C Q N p a ∧ Before C Q N q b) ∨
      (a < sk ztc Q N p ∧ sk ztc Q N p < b ∧
        Before C Q N q ztbarl) ∨
      (a < ek ztc Q N q ∧ ek ztc Q N q < b ∧
        After C Q N p ztbark) := by
  classical
  zqvf
  zubm
  set F := N.F _ Q
  have hCu : {x : ℝ | (chainModel C).IsCut F x}.Finite := hM.finite_cuts hN.1.2.1 hN.1.1
  set Cu := hCu.toFinset
  set Z : Finset ℝ := insert a ((Cu.filter (fun c => a < c ∧ c < κ)) ∪
    ((Cu.filter (fun c => a < c ∧ c < b ∧ a + b - c < κ)).image (fun c => a + b - c))) with hZ
  have haZ : a ∈ Z := by_simp_all
  set L := Z.max' by_grind with hL
  have hLa : a ≤ L := Z.le_max' a haZ
  have hZlt : ∀ x ∈ Z, x < κ := by
    grind
  have hLκ : L < κ := hZlt L (Z.max'_mem _)
  have hcutκ : ¬ (chainModel C).IsCut F κ := not_cut_of_int hN hne hp hκp
  have hcutκ' : ¬ (chainModel C).IsCut F _ := not_cut_of_int hN hne hq hκq
  -- no cut after `L`
  have hno1 : ∀ x, L < x → x ≤ κ → ¬ (chainModel C).IsCut F x := by
    zuhgx
    zujdn
    · grind
    have : x ∈ Z := by
      rw [hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      exact Or.inr (Or.inl ⟨hCu.mem_toFinset.2 hx, by_linarith, e⟩)
    have := Z.le_max' x this
    linarith
  -- no cut before the reflection of `L`
  have hno2 : ∀ x, a + b - κ ≤ x → x < a + b - L → ¬ (chainModel C).IsCut F x := by
    zuhgx
    rcases eq_or_lt_of_le h1 with e | e
    · grind
    have : a + b - x ∈ Z := by
      rw [hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      refine Or.inr (Or.inr ⟨x, ?_, rfl⟩)
      rw [Finset.mem_filter]
      exact ⟨hCu.mem_toFinset.2 hx, by_linarith, by_linarith, by_linarith⟩
    have := Z.le_max' _ this
    linarith
  have hin1 : ∀ x, L < x → x ≤ κ →
      sideInArc _ _ x :=
    fun x h1 h2 => int_of_noCut_left hN hne hp hκp hno1 h1 h2
  have hin2 : ∀ x, a + b - κ ≤ x → x < a + b - L →
      sideInArc _ _ x :=
    fun x h1 h2 => int_of_noCut_right hN hne hq hκq hno2 h1 h2
  -- the origin of `L`
  have hLZ := Z.max'_mem by_grind
  rw [← hL, hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_image] at hLZ
  rcases hLZ with hLa' | ⟨hc, h1, h2⟩ | ⟨c, hc, hcL⟩
  · -- the end of the interval
    left
    refine ⟨⟨κ - a, by_linarith, by_grind⟩,
      ⟨κ - a, by_linarith, by_grind⟩⟩
  · -- the start of `p`
    zuhl
    have hs := start_eq_of hN hne hp ztvsu hLκ hin1
    zubqb
    refine ⟨h1, by_linarith, κ - L, by_linarith, fun ε e1 e2 => ?_⟩
    rw [hmk L h1 by_linarith]
    grind
  · -- the end of `q`
    zulw
    rw [Finset.mem_filter] at hc
    obtain ⟨hc, c1, c2, c3⟩ := hc
    have hcL' : c = a + b - L := by_linarith
    have he := end_eq_of hN hne hq ztvsu by_grind
      (fun x h1 h2 => hin2 x h1 by_linarith)
    zucjo
    refine ⟨c1, c2, κ - L, by_linarith, fun ε e1 e2 => ?_⟩
    rw [hmk c c1 c2]
    exact hin1 _ by_linarith by_linarith

/-- The keys of the top. -/
def TopKey (C : Chain) (x : ℝ) : Prop := x = 6 ∨ x = κT C ∨ x = 2 * C.m + 6

/-- The open halves of the tour range. -/
def InI (C : Chain) (x : ℝ) : Prop := (6 < x ∧ x < κT C) ∨ (κT C < x ∧ x < 2 * C.m + 6)

/-- **The generating cases of the zipper pairs.** -/
def ZipGen (C : Chain) (Q : Polygon) (N : NF) (p q : ℕ) : Prop :=
  (∃ x y, TopKey C x ∧ TopKey C y ∧ x ≠ y ∧
    sideInArc ztwlo ztwnk x ∧
    sideInArc ztwlp ztwkp y) ∨
  (InI C ztwlo ∧ Before C Q N q ztbarl) ∨
  (InI C ztwkp ∧ After C Q N p ztbark) ∨
  (6 < κT C ∧ After C Q N p 6 ∧ Before C Q N q ztbgn) ∨
  (After C Q N p ztbgn ∧ Before C Q N q ztcc)

/-- **Every zipper pair is generated.** -/
theorem zip_cases (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) (hpq : p ≠ q) (hZ : ZipRel C Q N p q) : ZipGen C Q N p q := by
  zqvf
  obtain ⟨p₁, p₂, t₁, t₂, h1, h2, h3, h4, h5, h6, hx, he, i1, i2⟩ := hZ
  zuru
  rw [hnW] at h1 h2
  have hx' : sidePt (chainModel C).W p₂ t₂ ∈ C.set := by_simp_all
  obtain ⟨r1, r2⟩ := key_range C h1 h3 h4 hx
  obtain ⟨r1', r2'⟩ := key_range C h2 h5 h6 hx'
  have hkk : (p₁ : ℝ) + t₁ ≠ p₂ + t₂ := fun e => hpq (interior_unique hN hGM hne hp hq i1 by_simp_all)
  have ms := mirror_sum C hP h1 h2 h3 h4 h5 h6 hx he hkk
  generalize (p₁ : ℝ) + t₁ = κ at r1 r2 i1 hkk ms
  generalize (p₂ : ℝ) + t₂ = κ' at r1' r2' i2 hkk ms
  zqvj
  have top : ∀ x y, TopKey C x → TopKey C y → x ≠ y →
      sideInArc _ _ x →
      sideInArc _ _ y → ZipGen C Q N p q :=
    fun x y a b c d e => Or.inl ⟨x, y, a, b, c, d, e⟩
  rcases ms with ⟨z, hz⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  swap
  · exact top κ κ' ztvbv ztcgy hkk i1 i2
  swap
  · exact top κ κ' ztcgy (Or.inl e2) hkk i1 i2
  zugmt
  zugmu
  have hmkl : mk C ztcc = κT C := by
    unfold mk; simp_all
  rcases eq_mk_of_sum C by_linarith by_linarith by_linarith by_linarith hz with e | e | e
  swap
  · -- `κ' + 2 m = mk κ`: impossible
    exfalso
    zumtm
    grind
  swap
  · -- `κ' = mk κ + 2 m`: `κ = κT`, `κ' = 2 m + 6`
    zumtm
    split_ifs at e with h
    swap
    · grind
    have hk : κ = κT C := by_grind
    have hk' : κ' = 2 * C.m + 6 := by_grind
    exact top κ κ' (Or.inr (Or.inl hk)) (Or.inr (Or.inr hk')) hkk i1 i2
  -- the mirror
  by_cases h6k : κ = 6
  · exact top κ κ' (Or.inl h6k) ztcgy hkk i1 i2
  by_cases hTk : κ = κT C
  · exact top κ κ' (Or.inr (Or.inl hTk)) ztmbv hkk i1 i2
  by_cases hlk : κ = 2 * C.m + 6
  · exact top κ κ' (Or.inr (Or.inr hlk)) ztbmd hkk i1 i2
  rcases lt_or_gt_of_ne hTk with hlt | hgt
  · -- the first half
    have h6' : 6 < κ := by_grind
    have hmk : ztfdx := fun x a b => by
      zumtn
    have hq' : sideInArc ztwlp ztwkp (6 + κT C - κ) := by
      grind
    rcases zip_core hN hP hne hp hq h6' hlt hmk i1 hq' with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · zufsb
    · exact Or.inr ztnnp
    · exact Or.inr (Or.inr ztnnp)
  · -- the second half
    have hl' : κ < 2 * C.m + 6 := by_grind
    have hmk : ztwxv :=
      fun x a b => by unfold mk; grind
    have hq' : sideInArc ztwlp ztwkp
        (κT C + ztcc - κ) := by
      grind
    rcases zip_core hN hP hne hp hq hgt hl' hmk i1 hq' with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · zufsb
    · exact Or.inr ztnnq
    · exact Or.inr (Or.inr ztnnq)

/-- A key of the tour range is the key of a walk position. -/
theorem key_decomp {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) :
    ∃ p : ℕ, ∃ t : ℝ, p < 2 * C.m + 7 ∧ 0 ≤ t ∧ t < 1 ∧ (p : ℝ) + t = κ := by
  have h0 : 0 ≤ κ := by_linarith
  refine ⟨⌊κ⌋₊, κ - ⌊κ⌋₊, ?_, by linarith [Nat.floor_le h0], by
    linarith [Nat.lt_floor_add_one κ], by_ring⟩
  have  := (Nat.floor_le h0).trans h7
  have : ⌊κ⌋₊ ≤ 2 * C.m + 6 := by exact_mod_cast this
  omega

/-- The point of a key of the tour range is on the chain. -/
theorem pt_on_chain {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6) :
    sidePt ztcs p t ∈ C.set := by
  obtain ⟨i, e, hi, -, -, hpt⟩ := tour_norm C hp ht ht1 h6 h7
  rw [hpt, C.sidePt_tour C.sideBeta hi]
  refine ztlwp
  zunkl; exact ⟨t, ht, ht1.le, rfl⟩

/-- **A key and its mirror in two arcs make a zipper pair.** -/
theorem zipRel_of_mk {p q : ℕ} {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6)
    (hp : sideInArc ztwlo ztwnk κ)
    (hq : sideInArc ztwlp ztwkp (mk C κ)) :
    ZipRel C Q N p q := by
  obtain ⟨a1, a2, z, hz⟩ := mk_facts C h6 h7
  obtain ⟨p₁, t₁, h1, h2, h3, e1⟩ := key_decomp h6 h7
  obtain ⟨p₂, t₂, h1', h2', h3', e2⟩ := key_decomp a1 a2
  zuru
  refine ⟨p₁, p₂, t₁, t₂, by_omega, by_omega, h2, h3, h2', h3',
    pt_on_chain h1 h2 h3 by_simp_all by_simp_all, ?_,
    by simp_all, by_simp_all⟩
  exact same_point_of_sum C h1 h1' h2 h3 h2' h3' by_simp_all by_simp_all
    by_simp_all by_simp_all (z := z) by_simp_all

/-- The top keys have one point: the top. -/
theorem top_keys_same {x y : ℝ} (hx : TopKey C x) (hy : TopKey C y) :
    ∃ p₁ p₂ : ℕ, p₁ < 2 * C.m + 7 ∧ p₂ < 2 * C.m + 7 ∧ (p₁ : ℝ) = x ∧ (p₂ : ℝ) = y ∧
      sidePt ztcs p₁ 0 = sidePt ztcs p₂ 0 := by
  zubt
  have hr := rT_lt C
  -- the three keys as naturals with the top as point
  have key : ∀ x, TopKey C x → ∃ p : ℕ, p < 2 * C.m + 7 ∧ (p : ℝ) = x ∧
      sidePt ztcs p 0 = sidePt ztcs 6 0 := by
    zuh
    rcases hx with rfl | rfl | rfl
    · exact ⟨6, by_omega, by_norm_num, rfl⟩
    · refine ⟨6 + rT C, by_omega, by unfold κT; simp, ?_⟩
      have hsum := mk_facts C (κT_ge C) (le_of_lt (κT_lt C))
      obtain ⟨-, -, z, hz⟩ := hsum
      zugmu
      rw [hmkT] at hz
      refine same_point_of_sum C by_omega by_omega le_rfl one_pos le_rfl one_pos
        by_simp
        (by
          have hrR : zthnz := by exact_mod_cast hr
          grind)
        by_norm_num by_simp (z := z) ?_
      push_cast; unfold κT at hz; linarith
    · refine ⟨2 * C.m + 6, by_omega, by_simp, ?_⟩
      have := sidePt_last C; omega
  obtain ⟨p₁, a1, b1, c1⟩ := key x hx
  obtain ⟨p₂, a2, b2, c2⟩ := key y hy
  exact ⟨p₁, p₂, a1, a2, b1, b2, c1.trans c2.symm⟩

/-- **Every generated pair is a zipper pair.** -/
theorem zipRel_of_gen (hN : IsNF ztc Q N) (_hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) (hG : ZipGen C Q N p q) : ZipRel C Q N p q := by
  zqvj
  zuru
  obtain ⟨-, -, hne_p, -⟩ := arc_facts hN hne hp
  obtain ⟨-, -, hne_q, -⟩ := arc_facts hN hne hq
  -- points just after the start / before the end of an arc are inside it
  have after_start : ∀ r, r < N.arcs.length → After C Q N r ztzhb := by
    zuz
    zqvb
    · zqvd
    · zqve
  have before_end : ∀ r, r < N.arcs.length → Before C Q N r ztzem := by
    zuz
    zqvb
    · zqvd
    · zqve
  have mk1 : ztfdx := fun x a b => by
    zumtn
  have mk2 : ztwxv :=
    fun x a b => by unfold mk; grind
  rcases hG with ⟨x, y, hx, hy, -, i1, i2⟩ | ⟨hI, δ, hδ, hB⟩ | ⟨hI, δ, hδ, hA⟩ |
      ⟨h6T, ⟨δ, hδ, hA⟩, ⟨δ', hδ', hB⟩⟩ | ⟨⟨δ, hδ, hA⟩, ⟨δ', hδ', hB⟩⟩
  · -- the top
    obtain ⟨p₁, p₂, a1, a2, b1, b2, c⟩ := top_keys_same hx hy
    refine ⟨p₁, p₂, 0, 0, by_omega, by_omega, le_rfl, one_pos, le_rfl,
      one_pos, ?_, c, by_simp_all, by_simp_all⟩
    have hx6 : 6 ≤ x ∧ x ≤ 2 * C.m + 6 := by
      rcases hx with rfl | rfl | rfl <;> constructor <;> linarith
    exact pt_on_chain a1 le_rfl one_pos by_simp_all
      by_simp_all
  · -- the start of `p`
    obtain ⟨δ', hδ', hAs⟩ := after_start p hp
    set s := sk _ Q N p
    obtain ⟨a, b, h6a, has, hsb, hb, hmk⟩ : ∃ a b : ℝ, 6 ≤ a ∧ a < s ∧ s < b ∧ b ≤ 2 * C.m + 6 ∧
        ∀ x, a < x → x < b → mk C x = a + b - x := by
      zuejq
      · grind
      grind
    set ε := min ztfth (b - s) / 2 with hε
    have hε0 : ztbad := by
      grind
    zukhs
    have hε2 : ztpqy := by
      grind
    have hε3 : ε < b - s := by_grind
    refine zipRel_of_mk by_linarith by_linarith (hAs ε hε0 hε2) ?_
    rw [hmk _ by_linarith by_linarith]
    grind
  · -- the end of `q`
    obtain ⟨δ', hδ', hBe⟩ := before_end q hq
    set e := ek _ Q N q
    obtain ⟨a, b, h6a, has, hsb, hb, hmk⟩ : ∃ a b : ℝ, 6 ≤ a ∧ a < e ∧ e < b ∧ b ≤ 2 * C.m + 6 ∧
        ∀ x, a < x → x < b → mk C x = a + b - x := by
      zuejq
      · grind
      grind
    set ε := min ztfth ztjug / 2 with hε
    have hε0 : ztbad := by
      grind
    zukhs
    have hε2 : ztpqy := by
      grind
    have hε3 : ε < e - a := by_grind
    have hme : mk C e = a + b - e := by_grind
    refine zipRel_of_mk by_grind by_grind
      ztrri ?_
    rw [hmk _ by_grind by_grind, hme]
    grind
  · -- the first half from its ends
    zugmt
    set ε := min ztfth (κT C - 6) / 2 with hε
    have hε0 : ztbad := by
      simp_all
    have hε1 : ztpqx := by
      grind
    have hε2 : ztpqy := by
      grind
    have hε3 : ε < κT C - 6 := by_grind
    zqvk
    grind
  · -- the second half from its ends
    set ε := min ztfth (2 * C.m + 6 - κT C) / 2 with hε
    have hε0 : ztbad := by
      simp_all
    have hε1 : ztpqx := by
      grind
    have hε2 : ztpqy := by
      grind
    have hε3 : ε < 2 * C.m + 6 - κT C := by
      grind
    zqvk
    grind
theorem succP_predP {A p : ℕ} (hp : p < A) : succP A (predP A p) = p := by
  unfold succP predP; grind

/-- Every arc ends where its successor starts. -/
theorem ek_eq_sk_succ (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {p : ℕ} (hp : p < N.arcs.length) :
    ek ztc Q N p = sk ztc Q N (succP N.arcs.length p) := by
  zqvf
  obtain ⟨-, hc, -, -⟩ := arc_facts hN hne hp
  obtain ⟨U, hU, b, hab⟩ := (arcCover ztc Q _ hGM hN.1).2 _ hc
  obtain ⟨j, hj, hjs, -⟩ := NFLoc.listed_of_isArc hN hU hab
  zufkm
  have hsr : sk ztc Q N r = ek ztc Q N p := by
    show (chainModel C).key Q (N.arc ztnne).s = _
    simp_all
  have := end_start_adj hN hGM hne hp hr hsr.symm
  simp_all

/-- Points just after the start of an arc are inside it. -/
theorem after_start (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {r : ℕ} (hr : r < N.arcs.length) : After C Q N r ztzhb := by
  zqvb
  · zqvd
  · zqve

/-- Points just before the end of an arc are inside it. -/
theorem before_end (hN : IsNF ztc Q N) (hne : (N.F ztc Q).Nonempty)
    {r : ℕ} (hr : r < N.arcs.length) : Before C Q N r ztzem := by
  zqvb
  · zqvd
  · zqve

/-- Interior points have their neighbours inside. -/
theorem int_nhd {s e x : ℝ} (h : sideInArc s e x) : ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc s e (x - ε) ∧ sideInArc s e ztudo := by
  zusg
  split_ifs at h ⊢ with hse
  · refine ⟨min ztfvh (e - x), by_simp_all, fun ε e1 e2 => ?_⟩
    grind
  · zuy
    · refine ⟨x - s, by_linarith, by_grind⟩
    · refine ⟨e - x, by_linarith, by_grind⟩
open Classical in
/-- **The arc just before a located key.** -/
theorem before_of_loc (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) {y : ℝ}
    (hl1 : ¬ (chainModel C).IsCut ztwjh y →
      sideInArc ztwvb ztwus y)
    (hl2 : (chainModel C).IsCut ztwjh y →
      sk ztc Q N j = y ∨ ek ztc Q N j = y) :
    Before C Q N (if sk ztc Q N j = y then predP N.arcs.length j else j) y := by
  zqvl
  · zulsv
    · have hpj := predP_lt hj
      have := ek_eq_sk_succ hN hP hne hpj
      rw [succP_predP hj, hs] at this
      zvnnr; exact before_end hN hne hpj
    · zujds
      · simp_all
      · zvmzi; exact before_end hN hne hj
  · zulkf
    have hs : ¬ sk ztc Q N j = y := by
      zudih
    zulqj
    zqvi
open Classical in
/-- **The arc just after a located key.** -/
theorem after_of_loc (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) {y : ℝ}
    (hl1 : ¬ (chainModel C).IsCut ztwjh y →
      sideInArc ztwvb ztwus y)
    (hl2 : (chainModel C).IsCut ztwjh y →
      sk ztc Q N j = y ∨ ek ztc Q N j = y) :
    After C Q N (if ek ztc Q N j = y then succP N.arcs.length j else j) y := by
  zqvl
  · split_ifs with he
    · have := ek_eq_sk_succ hN hP hne hj
      zugdu
      zvmwk; exact after_start hN hne (succP_lt hj)
    · zujds
      · zvmzi; exact after_start hN hne hj
      simp_all
  · zulkf
    have he : ¬ ek ztc Q N j = y := by
      zudih
    zulqf
    zqvi
theorem before_unique (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {q q' : ℕ} (hq : q < N.arcs.length)
    (hq' : q' < N.arcs.length) {y : ℝ} (h : Before C Q N q y) (h' : Before C Q N q' y) :
    q = q' := by
  zqvc
theorem after_unique (hN : IsNF ztc Q N) (hP : C.P.Simple)
    (hne : (N.F ztc Q).Nonempty) {q q' : ℕ} (hq : q < N.arcs.length)
    (hq' : q' < N.arcs.length) {y : ℝ} (h : After C Q N q y) (h' : After C Q N q' y) :
    q = q' := by
  zqvc
end Zip
end OracleQ
end
end Chazelle.Core
end
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def lexLe (m : ℕ → ℕ) (B1 B2 K a b : ℕ) : Bool :=
  if a < K then
    (if b < K then decide (m ztdsu < m ztdsv ∨ (m ztdsu = m ztdsv ∧
      m ztgzw ≤ m ztgzx)) else true)
  else ztdva
variable (m : ℕ → ℕ)
theorem lexLe_total (B1 B2 K a b : ℕ) :
    (lexLe m B1 B2 K a b || lexLe m B1 B2 K b a) = true := by
  unfold lexLe
  grind
theorem lexLe_trans (B1 B2 K a b c : ℕ) (h1 : lexLe m B1 B2 K a b = true)
    (h2 : lexLe m B1 B2 K b c = true) : lexLe m B1 B2 K a c = true := by
  unfold lexLe at *
  grind

/-- **The comparator.** -/
def lexCmp : Stmt :=
  .ifLtN 30000 115005
    (.ifLtN 30001 115005
      (.seq (block [.addN 115002 115000 30000, .loadN 115003 115002, .addN 115002 115000 30001,
          .loadN 115004 115002])
        (.ifLtN 115003 115004 ztjo
          (.ifLtN 115004 115003 ztlr
            (.seq (block [.addN 115002 115001 30000, .loadN 115003 115002,
                .addN 115002 115001 30001, .loadN 115004 115002])
              (.ifLtN 115004 115003 ztlr ztjo)))))
      ztjo)
    (.ifLtN 30001 115005 ztlr
      ztxft)

/-- The invariant of the comparator: the bases, the bound and the memory below `A₀`. -/
def LexJ (m₀ : ℕ → ℕ) (A₀ B1 B2 K : ℕ) (c : Config) : Prop :=
  c.nreg 115000 = B1 ∧ c.nreg 115001 = B2 ∧ c.nreg 115005 = K ∧ ∀ a, a < A₀ → c.nmem a = m₀ a
theorem lexJ_stable (m₀ : ℕ → ℕ) (A₀ B1 B2 K : ℕ) : SortR.JStable ztoxd A₀ := by
  zudid
  have hb : ∀ r, 115000 ≤ r → r < 116000 → c'.nreg r = c.nreg r := fun r a b =>
    hr r ztfgf ztu
  exact ⟨by_simp_all,
    by simp_all,
    by simp_all, fun a ha => (hm a ha).trans (h4 a ha)⟩

/-- **The contract of the comparator.** -/
theorem lexCmp_ok {P : Polygon} {W : ℕ} {m₀ : ℕ → ℕ} {A₀ B1 B2 K : ℕ}
    (hB1 : B1 + K ≤ A₀) (hB2 : B2 + K ≤ A₀) (hW : 1 ≤ W) (hAW : A₀ ≤ W) :
    SortR.CmpOK P W lexCmp {11} ztoxd (lexLe m₀ B1 B2 K) 20 := by
  zufhy
  have hwr : wr (fun r => decide ztkdj || decide (115002 ≤ r ∧ r ≤ 115004)) lexCmp = true := by
    decide
  suffices H : ∃ c' k, Exec P W lexCmp c c' k ∧ k ≤ 20 ∧
      c'.nreg 30002 = (if lexLe m₀ B1 B2 K ztjry ztjrz then 1 else 0) by
    zubcs

    refine ⟨c', k, ex, hk, ⟨?_, ?_, ?_, fun a ha => by zunkg; simp_all⟩, hbit,
      fun r h0 h1 h2 hb => f.1 r ?_, fun r _ => fr r rfl, f.2.2.1, f.2.2.2.1, f.2.2.2.2⟩
    · zudjx
    · zuhlg
    · zuome; exact j3
    · zuhou

      zucor
      · exact hb (by rw [Finset.mem_singleton]; unfold bandOf; omega)
      · zugik
  have h1 : c.nreg 115005 = K := j3
  unfold lexCmp lexLe
  have hW' := hW
  zuirl
  · zudd
    zucur
    · zudd
      set a := c.nreg 30000
      set b := c.nreg 30001
      have ma : c.nmem ztdsu = m₀ ztdsu := j4 _ by_omega
      have mb : c.nmem ztdsv = m₀ ztdsv := j4 _ by_omega
      have ma2 : c.nmem ztgzw = m₀ ztgzw := j4 _ by_omega
      have mb2 : c.nmem ztgzx = m₀ ztgzx := j4 _ by_omega
      obtain ⟨c₁, k₁, e₁, hk₁, v3, v4, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 115002 115000 30000,
          .loadN 115003 115002, .addN 115002 115000 30001, .loadN 115004 115002]) c c₁ k₁ ∧ k₁ = 4 ∧
          c₁.nreg 115003 = m₀ ztdsu ∧ c₁.nreg 115004 = m₀ ztdsv ∧
          (∀ r, r < 115002 ∨ 115004 < r → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
        exec_block
        · omega
        · config_simp; omega
        · refine ⟨rfl, ?_, ?_, fun r hr => ?_, rfl⟩
          · config_simp; grind
          · config_simp; grind
          · config_simp; upd_solve
      zud
      zugar
      by_cases hlt : m₀ ztdsu < m₀ ztdsv
      · refine spec_ifLtN_true by_omega (spec_instr ztgdo
          fun _ => zteh)
        simp_all
      zubv
      by_cases hgt : m₀ ztdsv < m₀ ztdsu
      · refine spec_ifLtN_true by_omega (spec_instr (Exec.constN w₁ 30002 0
          ztbg) fun _ => ⟨by_omega, ?_⟩)
        simp [ha, hb, hlt]; omega
      zubv
      have heq : m₀ ztdsu = m₀ ztdsv := by_omega
      obtain ⟨c₂, k₂, e₂, hk₂, u3, u4⟩ : ∃ c₂ k₂, Exec P W (block [.addN 115002 115001 30000,
          .loadN 115003 115002, .addN 115002 115001 30001, .loadN 115004 115002]) c₁ c₂ k₂ ∧
          k₂ = 4 ∧ c₂.nreg 115003 = m₀ ztgzw ∧ c₂.nreg 115004 = m₀ ztgzx := by
        have g1 : c₁.nreg 115001 = B2 := by_simp_all
        have g2 : c₁.nreg 30000 = a := r₁ _ by_omega
        have g3 : c₁.nreg 30001 = b := r₁ _ by_omega
        exec_block
        · omega
        · config_simp; omega
        simp_all
      zue
      zulon
      by_cases h2 : m₀ ztgzx < m₀ ztgzw
      · refine spec_ifLtN_true by_omega (spec_instr (Exec.constN w₂ 30002 0
          ztbg) fun _ => ⟨by_omega, ?_⟩)
        simp_all
      · refine spec_ifLtN_false by_omega (spec_instr (Exec.constN w₂ _ _ hW)
          fun _ => zteh)
        simp_all
    · refine spec_ifLtN_false by_omega (spec_instr ztcsz fun _ =>
        ⟨by_omega, ?_⟩)
      simp_all
  · zubv
    zucur
    · refine spec_ifLtN_true by_omega (spec_instr ztbbp
        fun _ => zteh)
      simp_all
    · zubv
      zuhsy
      · refine spec_ifLtN_true hc (spec_instr ztbbp fun _ =>
          ⟨by_omega, ?_⟩)
        simp_all
      · zulol
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
@[expose] public section
def pLoadA : Stmt :=
  block [.inputSize 120010, .constN 120011 1, .constN 120012 0, .constN 120048 2,
    .constN 120028 6, .copyN 120013 110000, .copyN 120014 110001]

/-- `sideS` and the top vertex. -/
def pLoadC : Stmt :=
  .seq ztzge
    (.seq ztnal ztttn)

/-- `A` and `K`. -/
def pLoadD : Stmt :=
  block [.addN 120190 120014 120011, .loadN 120030 120190, .loadN 120039 120014]

/-- **Loading the constants of the preprocessing.** -/
def pLoad : Stmt := .seq pLoadA (.seq qLoadB (.seq pLoadC pLoadD))

/-- The registers written by `pLoad`. -/
def BPL (r : ℕ) : Bool := decide ztgxn || decide ztgxq
theorem wr_pLoad : wr BPL pLoad = true := by_decide

/-- The facts loaded by `pLoad`. -/
structure PLoaded (P : Polygon) (D NB s mm ti bb A K CB AB RB SB LB : ℕ) (c : Config) : Prop where
  n : c.nreg 120010 = P.n
  one : c.nreg 120011 = 1
  zero : c.nreg 120012 = 0
  two : c.nreg 120048 = 2
  six : c.nreg 120028 = 6
  rD : c.nreg 120013 = D
  rNB : c.nreg 120014 = NB
  rs : c.nreg 120015 = s
  rm : c.nreg 120016 = mm
  rti : c.nreg 120017 = ti
  rbb : c.nreg 120018 = bb
  twoM : c.nreg 120019 = 2 * mm
  nW : c.nreg 120020 = 2 * mm + 7
  tEnd : c.nreg 120029 = 2 * mm + 6
  sS : c.nreg 120021 = (if bb = 1 then ti else 2 * mm - ti)
  tv : c.nreg 120022 = (s + ti) % P.n
  rA : c.nreg 120030 = A
  rK : c.nreg 120039 = K
  rCB : c.nreg 120043 = CB
  rAB : c.nreg 120044 = AB
  rRB : c.nreg 120045 = RB
  rSB : c.nreg 120046 = SB
  rLB : c.nreg 120047 = LB

/-- **The load of the preprocessing.** -/
theorem pLoad_exec {P : Polygon} {W : ℕ} (c : Config) (hw : WordsBounded W c)
    {H : Host} {C : Chain} {N : NF} (hD : ChainDescAt c.nmem ztmfm zta H C)
    (hCQ : C.P = Qof P) (hsl : C.s < C.P.n) (hNF : NFAt c.nmem ztmfn N)
    (hDW : c.nreg 110000 + 5 ≤ W) (hNW : c.nreg 110001 + 7 ≤ W) (hW : 8 * P.n + 32 ≤ W) :
    ∃ c' k, Exec P W pLoad c c' k ∧ k ≤ 60 ∧ FrameB BPL c c' ∧
      PLoaded P ztmfm ztmfn C.s C.m C.topIdx ztnwl
        N.arcs.length N.chords.length ztnwm ztnwn
        (c.nmem (c.nreg 110001 + 5)) (c.nmem (c.nreg 110001 + 6)) (c.nmem (c.nreg 110001 + 7)) c' := by
  zuc
  obtain ⟨-, -, hd1, hd2, hd3, -⟩ := hD
  zucme
  have hs : ztpiv := by_simp_all
  zumex
  set D := c.nreg 110000
  set NB := c.nreg 110001
  -- the constants and handles
  obtain ⟨c₁, k₁, e₁, hk₁, v₁⟩ : ∃ c₁ k₁, Exec P W pLoadA c c₁ k₁ ∧ k₁ = 7 ∧
      (c₁.nreg 120010 = P.n ∧ c₁.nreg 120011 = 1 ∧ c₁.nreg 120012 = 0 ∧ c₁.nreg 120048 = 2 ∧
        c₁.nreg 120028 = 6 ∧ c₁.nreg 120013 = D ∧ c₁.nreg 120014 = NB ∧ c₁.nmem = c.nmem) := by
    unfold pLoadA
    exec_block
    all_goals (try omega)
    trivial
  obtain ⟨a10, a11, a12, a48, a28, a13, a14, m₁⟩ := v₁
  have f₁ := exec_frameB e₁ (B := BPL) by_decide
  -- the chain descriptor and the areas
  obtain ⟨c₂, k₂, e₂, hk₂, v₂⟩ : ∃ c₂ k₂, Exec P W qLoadB c₁ c₂ k₂ ∧ k₂ = 25 ∧
      (c₂.nreg 120015 = C.s ∧ c₂.nreg 120016 = C.m ∧ c₂.nreg 120017 = C.topIdx ∧
        c₂.nreg 120018 = c.nmem ztcel ∧ c₂.nreg 120019 = 2 * C.m ∧ c₂.nreg 120020 = 2 * C.m + 7 ∧
        c₂.nreg 120029 = 2 * C.m + 6 ∧ c₂.nreg 120043 = c.nmem ztclt ∧
        c₂.nreg 120044 = c.nmem ztcth ∧ c₂.nreg 120045 = c.nmem ztceq ∧
        c₂.nreg 120046 = c.nmem (NB + 6) ∧ c₂.nreg 120047 = c.nmem (NB + 7)) := by
    zud
    unfold qLoadB
    exec_block
    all_goals (config_simp; (try simp only [a11, a13, a14, m₁, hd2, Nat.add_assoc] at *); (try norm_num); (try omega))
  obtain ⟨b15, b16, b17, b18, b19, b20, b29, b43, b44, b45, b46, b47⟩ := v₂
  have f₂ := exec_frameB e₂ (B := BLdB) wr_qLoadB
  have g₂ : ∀ r, BLdB r = false → c₂.nreg r = c₁.nreg r := f₂.1
  zue
  zucxa
  -- sideS and the top vertex
  obtain ⟨c₃, k₃, e₃, hk₃, v21, v22, r₃, m₃⟩ : ∃ c₃ k₃, Exec P W pLoadC c₂ c₃ k₃ ∧ k₃ ≤ 10 ∧
      c₃.nreg 120021 = ztwwg ∧
      c₃.nreg 120022 = ztwi % P.n ∧
      (∀ r, r ≠ 120021 → r ≠ 120022 → c₃.nreg r = c₂.nreg r) ∧ c₃.nmem = c₂.nmem := by
    have h11 : zthoq := by zuomj; omega
    have h10 : c₂.nreg 120010 = P.n := by zuomj; omega
    obtain ⟨c₁', k₁', e₁', hk₁', v₁', r₁'⟩ : ∃ c₁' k₁', Exec P W (ifEq 120018 120011
        ztfet ztejs) c₂ c₁' k₁' ∧
        k₁' ≤ 5 ∧ c₁'.nreg 120021 = ztwwg ∧
        (∀ r, r ≠ 120021 → c₁'.nreg r = c₂.nreg r) := by
      by_cases hb : c.nmem ztcel = 1
      · obtain ⟨cc, ec, vc, rc⟩ := copy_exec (P := P) w₂ 120021 120017
        exact ⟨cc, _, ifEq_eq_exec by_omega ec, by_omega,
          by simp_all, rc⟩
      · obtain ⟨k', e', hk'⟩ := ifEq_ne_exec (S := .instr (.copyN 120021 120017))
          (show c₂.nreg 120018 ≠ c₂.nreg 120011 by rw [b18, h11]; exact hb)
          (Exec.subN (P := P) w₂ 120021 120019 120017)
        refine zthmf
        · simp_all
        simp_all
    zumfv
    obtain ⟨cA, eA, vA, rA, mA⟩ := add_exec (P := P) w₁' 120022 120015 120017 (by
      grind)
    rw [r₁' _ by_decide, r₁' _ by_decide, b15, b17] at vA
    obtain ⟨cB, kB, eB, hkB, vB, rB, mB, -⟩ := modSub_exec (P := P) (r := 120022) (nr := 120010)
      by_decide cA eA.wb_right by_grind
    rw [vA, rA _ by_decide, r₁' _ by_decide, h10] at vB
    have v21' : cB.nreg 120021 = ztwwg := by
      simp_all
    refine ⟨cB, _, .seq e₁' (.seq eA eB), by_omega, v21', vB, fun r h1 h2 => ?_, ?_⟩
    · simp_all
    · rw [mB, mA]
      exact exec_frameB e₁' (B := fun r => decide (r = 120021)) by_decide |>.2.2.1
  zubj
  -- `A` and `K`
  obtain ⟨c₄, k₄, e₄, hk₄, v30, v39, r₄⟩ : ∃ c₄ k₄, Exec P W pLoadD c₃ c₄ k₄ ∧ k₄ = 3 ∧
      c₄.nreg 120030 = N.arcs.length ∧ c₄.nreg 120039 = N.chords.length ∧
      (∀ r, r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → c₄.nreg r = c₃.nreg r) := by
    have h14 : c₃.nreg 120014 = NB := by zunpt; omega
    have h11 : zthos := by zunpt; omega
    unfold pLoadD
    exec_block
    · omega
    · refine ⟨rfl, ?_, ?_, fun r h1 h2 h3 => ?_⟩
      · config_simp; rw [h14, h11, m₃, m₂]; exact hNF.2.1
      · config_simp; rw [h14, m₃, m₂]; exact hNF.1
      simp_all
  have ex : Exec P W pLoad c c₄ _ := .seq e₁ ztcb
  -- the final values
  have R4 : ∀ r, r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → r ≠ 120021 → r ≠ 120022 →
      c₄.nreg r = c₂.nreg r := fun r a b c d e => by_simp_all
  have R1 : ∀ r, BLdB r = false → r ≠ 120190 → r ≠ 120030 → r ≠ 120039 → r ≠ 120021 →
      r ≠ 120022 → c₄.nreg r = c₁.nreg r := fun r h a b c d e => by rw [R4 r a b c d e, g₂ r h]
  refine ⟨c₄, _, ex, by_omega, exec_frameB ex wr_pLoad, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (rw [R1 _ by_decide by_decide by_decide by_decide by_decide by_decide];
       assumption)
    | (rw [R4 _ by_decide by_decide by_decide by_decide by_decide]; assumption)
    | (zunys; assumption)
    | assumption
def forS (ri rn r1 : ℕ) (body : Stmt) : Stmt :=
  .seq (.instr (.constN ri 0)) (.whileLtN ri rn (.seq body ztnbc))
variable {P : Polygon} {W : ℕ} {m : ℕ → ℕ} {g f : ℕ → ℕ} {B : ℕ → Bool} {S : Finset ℕ} {c c' : Config}
/-- **The counting loop.**  `I i c`: the invariant after `i` rounds. -/
theorem forS_exec {ri rn r1 : ℕ} {body : Stmt} (_hir : ri ≠ rn)
    (_hi1 : ri ≠ r1) {n κ : ℕ} (I : ℕ → Config → Prop)
    (hI : ∀ i c, I i c → WordsBounded W c ∧ c.nreg rn = n ∧ c.nreg r1 = 1)
    (hstab : ∀ i c v, I i c → WordsBounded W { c with nreg := upd c.nreg ri v } →
      I i { c with nreg := upd c.nreg ri v })
    (hbody : ∀ i c, i < n → I i c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ c'.nreg ri = i ∧ I ztg c')
    {c : Config} (hw : WordsBounded W c) (hn : n ≤ W)
    (h0 : ∀ c', WordsBounded W c' → c'.nreg ri = 0 → (∀ r, r ≠ ri → c'.nreg r = c.nreg r) →
      c'.nmem = c.nmem → c'.rreg = c.rreg → c'.rmem = c.rmem → c'.output = c.output → I 0 c') :
    ∃ c' k, Exec P W (forS ri rn r1 body) c c' k ∧ k ≤ n * zthlq + 3 ∧ I n c' ∧
      c'.nreg ri = n ∧ n ≤ k := by
  -- the start
  have x₀ := Exec.constN (P := P) hw ri 0 ztbg
  set c₀ : Config := { c with nreg := upd c.nreg ri 0 } with hc₀
  have I₀ := h0 c₀ x₀.wb_right (by zunad; simp) (fun r hr => by zunad; zumwy)
    rfl rfl rfl rfl
  -- the loop, with the counter in the invariant
  obtain ⟨c', k, ex, ⟨i, hI', hi, hin⟩, hstop, hk, hψ⟩ := SortR.whileLtN_potential_lb (P := P)
    (W := W) (a := ri) (b := rn) (body := .seq body ztnbc)
    (fun d => ∃ i, I i d ∧ d.nreg ri = i ∧ i ≤ n) (fun d => (n - d.nreg ri) * zthlq)
    (fun d => d.nreg ri)
    (fun d ⟨i, h, _⟩ => (hI i d h).1)
    (fun d ⟨i, hId, hri, hin⟩ ht => by
      obtain ⟨hwd, hrn, hr1⟩ := hI i d hId
      rw [hri, hrn] at ht
      obtain ⟨d₁, k₁, e₁, hk₁, hr₁, hI₁⟩ := hbody i d ht hId hri
      obtain ⟨hw₁, hrn₁, hr1₁⟩ := hI ztg d₁ hI₁
      have e₂ := Exec.addN (P := P) hw₁ ri ri r1 by_omega
      refine ⟨_, _, .seq e₁ e₂, ⟨i + 1, ?_, ?_, by_omega⟩, ?_, ?_⟩
      · exact hstab _ _ _ hI₁ e₂.wb_right
      · zucac
      · zumwv; rw [hr₁, hr1₁, hri]
        have : (n - ztg) * zthlq + zthlq = (n - i) * zthlq := by
          zujly
        omega
      · zumwv; omega)
    ⟨0, I₀, by zunad; simp, Nat.zero_le _⟩
  obtain ⟨-, hrn, -⟩ := hI i c' hI'
  rw [hi, hrn] at hstop
  have hin' : i = n := by_omega
  subst hin'
  have : c₀.nreg ri = 0 := by zunad; simp
  zvmwk at hk hψ
  refine ⟨c', _, .seq x₀ ex, ?_, hI', hi, ?_⟩
  · grind
  omega

/-! ## Scattering values into memory -/

/-- The memory after the stores `g i ↦ f i` for `i < n`, in order. -/
def scat (m : ℕ → ℕ) (g f : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => m
  | i + 1 => upd (scat m g f i) ztvqw ztmjd
theorem scat_other {n a : ℕ} (h : ∀ i, i < n → g i ≠ a) :
    scat m g f n a = m a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    zulsi
    zuimv
    zubfo
theorem scat_at {n i : ℕ} (hi : i < n)
    (hg : ∀ j, j < n → i < j → g j ≠ g i) : scat m g f n ztvqw = f i := by
  induction n with
  | zero => omega
  | succ n ih =>
    zulsi
    by_cases hin : i = n
    · simp_all
    · zuimv
      grind
theorem scat_below {n lo : ℕ} (hg : ∀ i, i < n → lo ≤ g i) {a : ℕ}
    (ha : a < lo) : scat m g f n a = m a :=
  scat_other by_grind

/-- **A scatter loop**: `body` computes an address in `ra` and a value in `rv`; they are stored. -/
def scatS (ri rn r1 ra rv : ℕ) (body : Stmt) : Stmt :=
  forS ri rn r1 (.seq body ztowd)

/-- **The scatter loop.**  The body writes only registers of `B` (not the counter, the bound, the
constant `1`) and no memory, and computes the address `g i ≥ lo` and the value `f i`; `J` is an
invariant insensitive to the registers of `B`, the counter and the memory from `lo` on. -/
theorem scatS_exec {ri rn r1 ra rv : ℕ} {body : Stmt} {B : ℕ → Bool}
    (hBi : B ri = false) (hBn : B rn = false) (hB1 : B r1 = false) (hir : ri ≠ rn) (hi1 : ri ≠ r1)
    (J : Config → Prop) (lo : ℕ)
    (hJ : ∀ c c', J c → ztgnf →
      zteda → J c')
    {n κ : ℕ} (g f : ℕ → ℕ) (hg : ∀ i, i < n → lo ≤ g i)
    (hbody : ∀ i c, i < n → J c → WordsBounded W c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ FrameB B c c' ∧ c'.nreg ra = g i ∧ c'.nreg rv = f i)
    {c : Config} (hw : WordsBounded W c) (hJc : J c) (hn : c.nreg rn = n) (h1 : c.nreg r1 = 1)
    (hnW : n ≤ W) :
    ∃ c' k, Exec P W (scatS ri rn r1 ra rv body) c c' k ∧ k ≤ n * (κ + 4) + 3 ∧
      ztgnf ∧
      ztbge ∧ c'.nmem = scat c.nmem g f n ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ J c' ∧ c'.nreg ri = n := by
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧
    (∀ r, B r = false → r ≠ ri → d.nreg r = c.nreg r) ∧
    ztimq ∧ d.nmem = scat c.nmem g f i ∧
    d.rmem = c.rmem ∧ d.output = c.output ∧ J d
  obtain ⟨c', k, ex, hk, ⟨_, h2, h3, h4, h5, h6, h7⟩, hi, -⟩ := forS_exec (P := P) (W := W)
    (body := .seq body ztowd) hir hi1 (n := n) (κ := κ + 1) I
    (fun i d ⟨hw, hr, _⟩ => ⟨hw, by_grind,
      by grind⟩)
    (fun i d v ⟨_, hr, hrr, hm, hrm, ho, hJd⟩ hw' => ⟨hw', fun r hB hri => by
        simp only; zuncc; grind, hrr, hm, hrm, ho,
      hJ d _ hJd (fun r _ hri => by simp only; zuncc)
        ztcj⟩)
    (fun i d hin ⟨hwd, hr, hrr, hm, hrm, ho, hJd⟩ hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, ha₁, hv₁⟩ := hbody i d hin hJd hwd hri
      have e₂ := Exec.storeN (P := P) e₁.wb_right ra rv
      refine ⟨_, _, .seq e₁ e₂, by_omega, by zuomi; omega, e₂.wb_right, ?_, ?_, ?_,
        ?_, ?_, ?_⟩
      · intro r hB hr'; exact (f₁.1 r hB).trans (hr r hB hr')
      · intro r hB; exact (f₁.2.1 r hB).trans by_grind
      · simp only [scat]; rw [ha₁, hv₁, f₁.2.2.1, hm]
      · exact f₁.2.2.2.1.trans hrm
      · exact f₁.2.2.2.2.trans ho
      · refine hJ d _ hJd (fun r hB _ => f₁.1 r hB) ztts
        zubi
        rw [ha₁, upd_other _ _ _ by_grind, f₁.2.2.1])
    hw hnW (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, fun r _ hri => hr r hri,
      fun r _ => by zvnhk, by_tauto, hrm, ho,
      hJ c d hJc (fun r _ hri => hr r hri) ztdnr⟩)
  refine ⟨c', k, ex, by_nlinarith, h2, h3, h4, h5, h6, h7, hi⟩

/-! ## Emitting pairs into two arrays -/

/-- The pairs emitted by the first `i` rounds. -/
def emitted (φ : ℕ → Option ztw) (i : ℕ) : List ztw := (List.range i).filterMap φ
theorem emitted_succ (φ : ℕ → Option ztw) (i : ℕ) :
    emitted φ ztg = emitted φ i ++ (φ i).toList := by
  unfold emitted
  rw [List.range_succ, List.filterMap_append]
  rfl
theorem emitted_length_le (φ : ℕ → Option ztw) (i : ℕ) : (emitted φ i).length ≤ i := by
  induction i with
  | zero => simp [emitted]
  | succ i ih => rw [emitted_succ]; cases φ i <;> simp <;> omega
theorem mem_emitted {φ : ℕ → Option ztw} {i : ℕ} {x : ℕ × ℕ} :
    x ∈ emitted φ i ↔ ∃ j, j < i ∧ φ j = some x := by
  unfold emitted; simp

/-- Pairs stored in two arrays from the given bases. -/
def PairsAt (m : ℕ → ℕ) (R1 R2 : ℕ) (l : List ztw) : Prop :=
  ∀ t, t < l.length → m ztnol = (l.getD t ztdr).1 ∧ m ztnom = (l.getD t ztdr).2

/-- **An emission loop**: when the flag `rf` is set, the pair `(rv1, rv2)` is stored at the
counter `rc` of the arrays with bases in `rR1`, `rR2`, and the counter advances. -/
def emitS (ri rn r1 rf rv1 rv2 rR1 rR2 rc rt : ℕ) (body : Stmt) : Stmt :=
  forS ri rn r1 (.seq body (.ifLtN rf r1 .skip
    ztebx))

/-- **The emission loop.**  The body writes only registers of `B` (not the loop registers) and no
memory, and sets the flag and the pair of `φ i`; `J` is insensitive to the registers of `B`, the
counter, the output counter, the scratch and the memory from `lo` on.  The pairs are appended
after `c₀` entries to the arrays at `R1`, `R2` (with room for `n` more entries in the first). -/
theorem emitS_exec {ri rn r1 rf rv1 rv2 rR1 rR2 rc rt : ℕ} {body : Stmt}
    {B : ℕ → Bool} (hreg : [ri, rn, r1, rc, rR1, rR2, rt].Nodup ∧ rt ≠ rv1 ∧ rt ≠ rv2 ∧
      rf ≠ rt ∧ rf ≠ rc)
    (hBi : B ri = false) (hBn : B rn = false) (hB1 : B r1 = false) (hBc : B rc = false)
    (hBR1 : B rR1 = false) (hBR2 : B rR2 = false)
    {R1 R2 c₀ n κ : ℕ} (J : Config → Prop)
    (hJ : ∀ c c', J c → ztedd →
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + n ≤ a ∧ a < R2 + c₀) ∨ R2 + c₀ + n ≤ a) →
        c'.nmem a = c.nmem a) → J c')
    (φ : ℕ → Option ztw)
    (hbody : ∀ i c, i < n → J c → WordsBounded W c → c.nreg ri = i →
      ∃ c' k, Exec P W body c c' k ∧ k ≤ κ ∧ FrameB B c c' ∧ (φ i = none → c'.nreg rf = 0) ∧
        ∀ x, φ i = some x → c'.nreg rf = 1 ∧ c'.nreg rv1 = x.1 ∧ c'.nreg rv2 = x.2)
    {c : Config} (hw : WordsBounded W c) (hJc : J c) (hn : c.nreg rn = n) (h1 : c.nreg r1 = 1)
    (hR1 : c.nreg rR1 = R1) (hR2 : c.nreg rR2 = R2) (hc₀ : c.nreg rc = c₀)
    (hR12 : R1 + c₀ + n ≤ R2) (hRW : R2 + c₀ + n ≤ W) :
    ∃ c' k, Exec P W (emitS ri rn r1 rf rv1 rv2 rR1 rR2 rc rt body) c c' k ∧
      k ≤ n * (κ + 10) + 3 ∧
      ztedd ∧
      ztbge ∧
      c'.nreg rc = c₀ + (emitted φ n).length ∧
      PairsAt c'.nmem ztfol ztenu (emitted φ n) ∧
      (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (emitted φ n).length ≤ a ∧ a < R2 + c₀) ∨
        R2 + c₀ + (emitted φ n).length ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧ J c' := by
  obtain ⟨hnd, ht1, ht2, hft, hfc⟩ := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true, not_or] at hnd
  obtain ⟨⟨hin, hi1, hic, hiR1, hiR2, hit⟩, ⟨hn1, hnc, hnR1, hnR2, hnt⟩, ⟨h1c, h1R1, h1R2, h1t⟩,
    ⟨hcR1, hcR2, hct⟩, ⟨hR1R2, hR1t⟩, hR2t, -⟩ := hnd
  let I : ℕ → Config → Prop := fun i d => WordsBounded W d ∧
    (∀ r, B r = false → r ≠ ri → r ≠ rc → r ≠ rt → d.nreg r = c.nreg r) ∧
    ztimq ∧ d.nreg rc = c₀ + (emitted φ i).length ∧
    PairsAt d.nmem ztfol ztenu (emitted φ i) ∧
    (∀ a, (a < R1 + c₀ ∨ (R1 + c₀ + (emitted φ i).length ≤ a ∧ a < R2 + c₀) ∨
      R2 + c₀ + (emitted φ i).length ≤ a) → d.nmem a = c.nmem a) ∧
    d.rmem = c.rmem ∧ d.output = c.output ∧ J d
  obtain ⟨c', k, ex, hk, ⟨_, h2, h3, h4, h5, h6, h7, h8, h9⟩, -, -⟩ := forS_exec (P := P) (W := W)
    (body := .seq body (.ifLtN rf r1 .skip
      ztebx))
    hin hi1 (n := n) (κ := κ + 7) I
    (fun i d ⟨hw, hr, _⟩ => ⟨hw, by_grind,
      by grind⟩)
    (fun i d v ⟨_, hr, hrr, hc, hp, hm, hrm, ho, hJd⟩ hw' => ⟨hw', fun r hB hri hrc hrt => by
        simp only; zuncc; grind, hrr,
      by simp only; rw [upd_other _ _ _ ztvbf]; exact hc, hp, hm, hrm,
      ho, hJ d _ hJd (fun r _ hri _ _ => by simp only; zuncc)
        ztcj⟩)
    (fun i d hin' ⟨hwd, hr, hrr, hc, hp, hm, hrm, ho, hJd⟩ hri => by
      obtain ⟨d₁, k₁, e₁, hk₁, f₁, hn₁, hs₁⟩ := hbody i d hin' hJd hwd hri
      zud
      have hlen := emitted_length_le φ i
      have hc₁ : d₁.nreg rc = c₀ + (emitted φ i).length := by rw [f₁.1 _ hBc]; exact hc
      have hR1₁ : d₁.nreg rR1 = R1 := by
        rw [f₁.1 _ hBR1, hr _ hBR1 (Ne.symm hiR1) (Ne.symm hcR1) hR1t]; omega
      have hR2₁ : d₁.nreg rR2 = R2 := by
        rw [f₁.1 _ hBR2, hr _ hBR2 (Ne.symm hiR2) (Ne.symm hcR2) hR2t]; omega
      have h1₁ : d₁.nreg r1 = 1 := by
        rw [f₁.1 _ hB1, hr _ hB1 (Ne.symm hi1) h1c h1t]; exact h1
      have hri₁ : d₁.nreg ri = i := by zuomi; omega
      cases hφ : φ i with
      | none =>
        have hf0 := hn₁ hφ
        refine ⟨d₁, k₁ + 1, .seq e₁ (.ifLtN_true by_omega
          ztwd), by_omega, hri₁, w₁, fun r hB a b c => (f₁.1 r hB).trans (hr r hB a b c),
          fun r hB => (f₁.2.1 r hB).trans (hrr r hB), ?_, ?_, ?_, f₁.2.2.2.1.trans hrm,
          f₁.2.2.2.2.trans ho, hJ d d₁ hJd (fun r hB _ _ _ => f₁.1 r hB)
            ztdnq⟩
        · rw [emitted_succ, hφ]; simp only [Option.toList_none, List.append_nil]; omega
        · zunzs; simpa using hp
        · zunzs; simpa using hm
      | some x =>
        obtain ⟨hf1, hv1, hv2⟩ := hs₁ x hφ
        set L := emitted φ i with hL
        have hLn : L.length < n := by_omega
        obtain ⟨d₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ d₂ k₂, Exec P W (block [.addN rt rR1 rc,
            .storeN rt rv1, .addN rt rR2 rc, .storeN rt rv2, .addN rc rc r1]) d₁ d₂ k₂ ∧ k₂ = 5 ∧
            d₂.nreg = upd _ rc _ ∧
            d₂.nmem = upd _ _ x.2 ∧
            d₂.rreg = d₁.rreg ∧ d₂.rmem = d₁.rmem ∧ d₂.output = d₁.output := by
          have u1 := upd_other d₁.nreg rt ztjue hR2t
          have u2 := upd_other d₁.nreg rt ztjue hct
          have u3 := upd_other d₁.nreg rt ztjue (Ne.symm ht1)
          have u4 := upd_other d₁.nreg rt ztjuf (Ne.symm ht2)
          have u5 := upd_other d₁.nreg rt ztjuf hct
          have u6 := upd_other d₁.nreg rt ztjuf h1t
          exec_block
          · omega
          · grind
          · grind
          · refine ⟨rfl, ?_, ?_, rfl, rfl, rfl⟩
            · config_simp
              rw [u1, u2, u5, u6, hR2₁, hc₁, h1₁]
            · config_simp
              rw [u3, u1, u2, u4, hR1₁, hR2₁, hc₁, hv1, hv2]
        have hne12 : ∀ t, t < n → R1 + c₀ + t ≠ R2 + ztnxi := by_grind
        refine ⟨d₂, k₁ + ztoci, .seq e₁ (.ifLtN_false by_omega
          e₂), by_omega, ?_, e₂.wb_right, ?_, ?_, ?_, ?_, ?_, by zuoez; exact f₁.2.2.2.1.trans hrm,
          by zuofa; exact f₁.2.2.2.2.trans ho, ?_⟩
        · rw [n₂, upd_other _ _ _ hic, upd_other _ _ _ hit]; omega
        · intro r hB a b c'
          rw [n₂, upd_other _ _ _ b, upd_other _ _ _ c']; exact (f₁.1 r hB).trans (hr r hB a b c')
        · intro r hB; zunsn; exact (f₁.2.1 r hB).trans (hrr r hB)
        · rw [n₂, upd_same, emitted_succ, hφ, ← hL]; simp; omega
        · zucj
          rw [emitted_succ, hφ] at ht ⊢
          simp only [Option.toList_some, List.length_append, List.length_cons, List.length_nil]
            at ht
          rw [m₂, f₁.2.2.1]
          rcases Nat.lt_or_ge t L.length with htl | htl
          · rw [List.getD_append _ _ _ _ htl]
            obtain ⟨p1, p2⟩ := hp t htl
            zujx
            · rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, p1]
            · rw [upd_other _ _ _ by_omega, upd_other _ _ _ by_omega, p2]
          · have hteq : t = L.length := by_omega
            subst hteq
            rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self]
            try simp only [List.getD_cons_zero]
            zujx
            · rw [upd_other _ _ _ by_omega, show R1 + c₀ + L.length = R1 + ztnxi by
                omega, upd_same]; rfl
            · rw [show R2 + c₀ + L.length = R2 + ztnxi by omega, upd_same]; rfl
        · zuge
          rw [emitted_succ, hφ] at ha
          simp only [Option.toList_some, List.length_append, List.length_cons,
            List.length_nil] at ha
          zuneo
          exact hm a by_omega
        · refine hJ d d₂ hJd (fun r hB _ hrc hrt => ?_) ztts
          · rw [n₂, upd_other _ _ _ hrc, upd_other _ _ _ hrt]; exact f₁.1 r hB
          · zuneo)
    hw by_omega (fun d hwd h0 hr hm hrr hrm ho => ⟨hwd, fun r _ hri _ _ => hr r hri,
      fun r _ => by zvnhk, by rw [hr rc ztvbf, hc₀]; rfl,
      fun t ht => by_tauto, fun a _ => by zvmwi, hrm, ho,
      hJ c d hJc (fun r _ hri _ _ => hr r hri) ztdnr⟩)
  exact ⟨c', k, ex, by_nlinarith, h2, h3, h4, h5, h6, h7, h8, h9⟩

/-- Pairs at two bases, then more pairs after them. -/
theorem PairsAt.append {R1 R2 : ℕ} {l l' : List ztw} (h : PairsAt m R1 R2 l)
    (h' : PairsAt m (R1 + l.length) (R2 + l.length) l') : PairsAt m R1 R2 ztrsu := by
  zucj
  rw [List.length_append] at ht
  rcases Nat.lt_or_ge t l.length with h1 | h1
  · zunvf; exact h t h1
  · rw [List.getD_append_right _ _ _ _ h1]
    have := h' (t - l.length) by_omega
    simp_all

/-- Pairs survive memory changes away from their cells. -/
theorem PairsAt.congr {m m' : ℕ → ℕ} {R1 R2 : ℕ} {l : List ztw} (h : PairsAt m R1 R2 l)
    (hm : ∀ t, t < l.length → m' ztnol = m ztnol ∧ m' ztnom = m ztnom) :
    PairsAt m' R1 R2 l := fun t ht => by
  rw [(hm t ht).1, (hm t ht).2]; exact h t ht

/-! ## Invariants of the loops: kept registers and old memory -/

/-- The registers of `K` keep their values of `c₀` and the memory below `lo` is that of `c₀`. -/
def JK (c₀ : Config) (K : ℕ → Bool) (lo : ℕ) (d : Config) : Prop :=
  (∀ r, K r = true → d.nreg r = c₀.nreg r) ∧ (∀ a, a < lo → d.nmem a = c₀.nmem a)
theorem JK.refl (c₀ : Config) (K : ℕ → Bool) (lo : ℕ) : JK c₀ K lo c₀ :=
  ⟨by_omega, by_omega⟩

/-- `JK` survives writes to registers outside `K` and to memory from `lo` on. -/
theorem JK.stable {c₀ : Config} {K : ℕ → Bool} {lo : ℕ} {B : ℕ → Bool} {rs : List ℕ}
    (hK : ∀ r, K r = true → B r = false ∧ r ∉ rs) {c c' : Config} (h : JK c₀ K lo c)
    (hr : ∀ r, B r = false → r ∉ rs → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < lo → c'.nmem a = c.nmem a) : JK c₀ K lo c' :=
  ⟨fun r hr' => by rw [hr r by_simp_all by_simp_all]; exact h.1 r hr',
    fun a ha => by zunps; exact h.2 a ha⟩

/-! ## The frame of a stage -/

/-- **The frame of a stage**: registers outside `B` and memory below `lo` unchanged, real memory
below `lo` unchanged, nothing emitted. -/
def PF (B : ℕ → Bool) (lo : ℕ) (c c' : Config) : Prop :=
  ztcjh ∧ ztbge ∧
    zteda ∧ ztiuo ∧
    c'.output = c.output
theorem PF.trans {lo : ℕ} {c₁ c₂ c₃ : Config} (h₁ : PF B lo c₁ c₂)
    (h₂ : PF B lo c₂ c₃) : PF B lo c₁ c₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans zthhr, fun r hr => (h₂.2.1 r hr).trans ztfsm,
    fun a ha => (h₂.2.2.1 a ha).trans ztobj,
    fun a ha => (h₂.2.2.2.1 a ha).trans ztobk, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
theorem PF.mono {B B' : ℕ → Bool} {lo lo' : ℕ} {c c' : Config} (h : PF B lo c c')
    (hB : ∀ r, B r = true → B' r = true) (hlo : lo' ≤ lo) : PF B' lo' c c' := by
  have hf : ∀ r, B' r = false → B r = false := fun r hr => by
    grind
  exact ⟨fun r hr => h.1 r by_simp_all, fun r hr => h.2.1 r by_simp_all,
    fun a ha => h.2.2.1 a by_omega, fun a ha => h.2.2.2.1 a by_omega, h.2.2.2.2⟩

/-- **A frame without the allocator bounds.** -/
def FrameN (S : Finset ℕ) (c c' : Config) : Prop :=
  ztgnh ∧ ztimv ∧
    zth ∧
    ztgo ∧ c'.output = c.output
theorem FrameN.trans {c c₁ c₂ : Config} (h₁ : FrameN S c c₁) (h₂ : FrameN S c₁ c₂)
    (hA : c.nreg ALLOC ≤ c₁.nreg ALLOC) : FrameN S c c₂ :=
  ⟨fun r hr ha => (h₂.1 r hr ha).trans (h₁.1 r hr ha), fun r hr => (h₂.2.1 r hr).trans ztfsm,
    fun a ha => (h₂.2.2.1 a by_omega).trans ztobj,
    fun a ha => (h₂.2.2.2.1 a by_omega).trans ztobk, h₂.2.2.2.2.trans h₁.2.2.2.2⟩
theorem FrameN.mono {S S' : Finset ℕ} {c c' : Config} (h : FrameN S c c') (hS : S ⊆ S') :
    FrameN S' c c' :=
  ⟨fun r hr ha => h.1 r by_grind ha, fun r hr => h.2.1 r by_grind,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
theorem Frame.toN {k : ℕ} (h : Frame S c c' k) : FrameN S c c' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

/-- A stage frame is a frame without the allocator bounds. -/
theorem PF.frameN (h : PF B ztm c c')
    (hB : ∀ r, B r = true → bandOf r ∈ S ∨ r = ALLOC) (hrA : c'.rreg ALLOC = c.rreg ALLOC) :
    FrameN S c c' := by
  refine ⟨fun r hr hra => h.1 r ?_, fun r hr => ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · grind
  · zujtu
    · simp_all
    refine h.2.1 r ?_
    grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Chazelle.Chain (sideE)
namespace OracleQ
variable {x M : ℕ} {w : ℕ}
theorem mod_lt_two (hx : x < 2 * M) :
    ztlun ∨ (M ≤ x ∧ x % M = x - M) := by
  rcases Nat.lt_or_ge x M with h | h
  · zulem
  · zugao
theorem mod_le_two (_hM : 0 < M) (hx : x ≤ 2 * M) :
    ztlun ∨ (M ≤ x ∧ x < 2 * M ∧ x % M = x - M) ∨ (x = 2 * M ∧ x % M = 0) := by
  rcases Nat.lt_or_ge x ztfms with h | h
  · rcases mod_lt_two h with h' | h'
    · omega
    omega
  · have : x = 2 * M := by_omega
    simp_all
variable (C : Chain)

/-! ## The walk vertices -/

/-- The index in `C.P` of the walk vertex `w`, for `6 ≤ w ≤ 2 m + 6`. -/
noncomputable def vaIdx (w : ℕ) : ℕ := (C.s + sideE C.m (tj C ztvu)) % C.P.n
theorem vaIdx_lt (w : ℕ) : vaIdx C w < C.P.n := Nat.mod_lt _ C.n_pos

/-- **The walk vertex `w`** is the vertex `vaIdx w` of `C.P`. -/
theorem walk_vtx (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6) :
    (chainModel C).W.vtx w = C.P.vtx ztucx := by
  zucxw
  show (C.sideWalk C.sideBeta).vtx _ = _
  zudth
  rfl
theorem walk_next (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    (chainModel C).W.vtx ztuz = C.P.vtx (vaIdx C zthkx) := by
  rw [walk_n, Nat.mod_eq_of_lt by_omega]
  exact walk_vtx C by_omega by_omega

/-- Consecutive walk vertices of the tour are distinct vertices of `C.P`. -/
theorem vaIdx_succ_ne (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    vaIdx C w ≠ vaIdx C zthkx := by
  zubt
  zumec
  zuec
  unfold vaIdx tj
  rw [show w + 1 - 6 = ztvu + 1 by omega]
  zuhof
  set i := w - 6
  zukcl
  -- the two chain indices differ by one
  obtain ⟨k, k', hk, hk', hkk⟩ : ∃ k k', sideE C.m ((S + i) % (2 * C.m)) = k ∧
      sideE C.m (ztypu % ztbb) = k' ∧ (k' = k + 1 ∨ k = k' + 1) := by
    refine ⟨_, _, rfl, rfl, ?_⟩
    have e1 : ztypu % ztbb = (ztbat % ztbb + 1) % ztbb := by
      grind
    zukd
    have hX : ztbat % ztbb < 2 * C.m := Nat.mod_lt _ by_omega
    generalize ztbat % ztbb = X at hX ⊢
    rcases Nat.lt_or_ge ztnqh ztbb with h | h
    · zvnnm; unfold sideE; grind
    · rw [show X + 1 = 2 * C.m by omega, Nat.mod_self]; unfold sideE; grind
  rw [hk, hk']
  have hkm : ztidw := by zunki; exact Chazelle.Chain.sideE_le (Nat.mod_lt _ by_omega).le
  have hkm' : ztskc := by rw [← hk']; exact Chazelle.Chain.sideE_le (Nat.mod_lt _ by_omega).le
  zuq
  have hn2 : ztsaf := by_omega
  rcases hkk with rfl | rfl
  · have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rw [show C.s + zts - zttw = 1 by omega] at this
    simp_all
  · have := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [show C.s + ztjzg - (C.s + k') = 1 by omega] at this
    simp_all

/-- The walk edges `6 … 2 m + 6` are not horizontal. -/
theorem walk_nonhoriz (hD : DistinctHeights C.P) {w : ℕ} (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6) :
    ((chainModel C).W.vtx w).2 ≠ ((chainModel C).W.vtx ztuz).2 := by
  rcases Nat.lt_or_ge w ztcc with h | h
  · rw [walk_vtx C h6 h7, walk_next C h6 h]
    exact hD _ _ ztucy (vaIdx_lt C _) (vaIdx_succ_ne C h6 h)
  · have hw : ztpqi := by_omega
    subst hw
    show ((C.sideWalk C.sideBeta).vtx _).2 ≠
      ((C.sideWalk C.sideBeta).vtx (ztbjc % (C.sideWalk C.sideBeta).n)).2
    zugto
    unfold Chain.slitTop
    exact (C.top_snd_lt_radius).ne

/-! ## Parameters and keys -/

/-- The height code, normalised to `0` at the start vertex of the walk edge. -/
noncomputable def nz (w hc : ℕ) : ℕ := if hc = 0 ∨ hc = vaIdx C w + 1 then 0 else hc
theorem param_of_ne (hD : DistinctHeights C.P) {w : ℕ} (h6 : 6 ≤ w) (h7 : w ≤ 2 * C.m + 6)
    (h : ℕ) : (chainModel C).param C.P ztboe =
      ((C.P.vtx h).2 - ((chainModel C).W.vtx w).2) /
        (((chainModel C).W.vtx ztuz).2 - ((chainModel C).W.vtx w).2) := by
  zujpx
  simp_all

/-- **The parameter is zero iff the normalised code is.** -/
theorem param_eq_zero_iff (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w)
    (h7 : w ≤ 2 * C.m + 6) (hh : hc ≤ C.P.n) :
    (chainModel C).param C.P ztbfp = 0 ↔ nz C w hc = 0 := by
  unfold nz
  rcases hc with _ | h
  · tauto
  · have hiff : ((if h + 1 = 0 ∨ h + 1 = vaIdx C w + 1 then 0 else h + 1) = 0) ↔
        h = vaIdx C w := by
      simp
    rw [hiff, param_of_ne C hD h6 h7, walk_vtx C h6 h7]
    zuhzl
    rw [walk_vtx C h6 h7] at hne
    have hd : ((chainModel C).W.vtx _).2 -
        (C.P.vtx _).2 ≠ 0 := sub_ne_zero.2 ztnr
    rw [div_eq_zero_iff, sub_eq_zero, or_iff_left hd]
    constructor
    · zuchf
      zuirz
      exact hD _ _ by_omega ztucy hne' e
    simp_all
theorem key_eq_param (w hc : ℕ) :
    (chainModel C).key C.P ztbfp = w + (chainModel C).param C.P ztbfp := rfl
theorem floor_eq {w w2 : ℕ} {t t2 : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht2 : 0 ≤ t2) (ht21 : t2 < 1)
    (h : (w2 : ℝ) + t2 = w + t) : w2 = w ∧ t2 = t := by
  have a : (w2 : ℝ) < w + 1 := by_linarith
  have b : (w : ℝ) < w2 + 1 := by_linarith
  have a' : w2 < w + 1 := by exact_mod_cast a
  have b' : w < w2 + 1 := by exact_mod_cast b
  grind
theorem nz_of_ne {w hc : ℕ} (h : nz C w hc ≠ 0) : nz C w hc = hc := by
  unfold nz at *; simp_all

/-- **Equal keys**: for `6 ≤ w ≤ 2 m + 6`, a proper position has the key of `⟨w, hc⟩` iff it lies
on the walk edge `w` with the same normalised height code. -/
theorem key_eq_iff (hD : DistinctHeights C.P) {w hc w2 hc2 : ℕ} (h6 : 6 ≤ w)
    (h7 : w ≤ 2 * C.m + 6) (hh : hc ≤ C.P.n) (hh2 : hc2 ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ztbfp ∧ (chainModel C).param C.P ztbfp < 1)
    (hp2 : 0 ≤ (chainModel C).param C.P ztkne ∧ (chainModel C).param C.P ztkne < 1) :
    (chainModel C).key C.P ztkne = (chainModel C).key C.P ztbfp ↔
      w2 = w ∧ nz C w hc2 = nz C w hc := by
  rw [key_eq_param, key_eq_param]
  constructor
  · zuq
    obtain ⟨rfl, ht⟩ := floor_eq hp.1 hp.2 hp2.1 hp2.2 h
    zubee
    by_cases h0 : (chainModel C).param C.P ⟨w2, hc⟩ = 0
    · rw [(param_eq_zero_iff C hD h6 h7 hh).1 h0,
        (param_eq_zero_iff C hD h6 h7 hh2).1 (ht.trans h0)]
    · have h0' : (chainModel C).param C.P ztkne ≠ 0 := by_simp_all
      have n1 := fun e => h0 ((param_eq_zero_iff C hD h6 h7 hh).2 e)
      have n2 := fun e => h0' ((param_eq_zero_iff C hD h6 h7 hh2).2 e)
      rw [nz_of_ne C n1, nz_of_ne C n2]
      have hc0 : hc ≠ 0 := fun e => by
        apply n1; unfold nz; simp_all
      have hc20 : hc2 ≠ 0 := fun e => by
        apply n2; unfold nz; simp_all
      obtain ⟨h1, rfl⟩ : ∃ h1, hc = h1 + 1 := ztdqr
      obtain ⟨h2, rfl⟩ : ∃ h2, hc2 = h2 + 1 := ⟨hc2 - 1, by_omega⟩
      rw [param_of_ne C hD h6 h7, param_of_ne C hD h6 h7] at ht
      zuhzl
      have hd : ((chainModel C).W.vtx _).2 -
          ((chainModel C).W.vtx w2).2 ≠ 0 := sub_ne_zero.2 ztnr
      rw [div_left_inj' hd, sub_left_inj] at ht
      zuirz
      exact hD h2 h1 by_omega by_omega by_omega ht
  · rintro ⟨rfl, hz⟩
    by_cases h0 : nz C w2 hc = 0
    · rw [(param_eq_zero_iff C hD h6 h7 hh).2 h0,
        (param_eq_zero_iff C hD h6 h7 hh2).2 (hz.trans h0)]
    · have n2 : nz C w2 hc2 ≠ 0 := by_omega
      rw [nz_of_ne C h0, nz_of_ne C n2] at hz
      zudur

/-- The key of a vertex position `⟨X, 0⟩`. -/
theorem key_zero (X : ℕ) : (chainModel C).key C.P ztomg = X := by
  zugga

/-! ## The mirror -/

/-- The mirrored walk edge of a vertex position. -/
noncomputable def mirW0 (w : ℕ) : ℕ :=
  (if w ≤ 6 + rT C then 12 + rT C else 12 + rT C + 2 * C.m) - w

/-- The mirrored walk edge of an inner position. -/
noncomputable def mirW1 (w : ℕ) : ℕ :=
  (if w < 6 + rT C then 11 + rT C else 11 + rT C + 2 * C.m) - w

/-- **The mirrored walk position.** -/
noncomputable def mirPos (w hc : ℕ) : WPos :=
  if nz C w hc = 0 then ⟨mirW0 C w, 0⟩ else ⟨mirW1 C w, hc⟩
theorem rT_def : (rT C : ℝ) + 6 = κT C := by unfold κT; ring

/-- **The tour reversal**: the mirrored walk edge runs along the same chain edge backwards. -/
theorem rev_idx (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6) :
    vaIdx C (mirW1 C w) = vaIdx C zthkx ∧ vaIdx C (mirW1 C w + 1) = vaIdx C w := by
  zubt
  zuec
  zubwh
  unfold vaIdx tj
  zuhof
  set R := rT C
  set M := 2 * C.m with hM
  have hRdef : R = (4 * C.m - 2 * S) % M := rfl
  set i := w - 6 with hi
  have hiM : i < M := by_omega
  -- the mirrored tour index
  obtain ⟨i', hi', hi'M⟩ : ∃ i', mirW1 C w - 6 = i' ∧ (i' = (if i < R then R - 1 - i else R + M - 1 - i)) := by
    refine ⟨_, rfl, ?_⟩
    unfold mirW1; grind
  have e1 : mirW1 C w + 1 - 6 = i' + 1 := by
    have : 6 ≤ mirW1 C w := by unfold mirW1; grind
    omega
  rw [e1, hi', show w + 1 - 6 = i + 1 by omega]
  -- the residues
  have hX := mod_lt_two (x := S + i) (M := M) by_omega
  have hY := mod_lt_two (x := S + i') (M := M) by_grind
  have hR4 := mod_le_two (x := 4 * C.m - 2 * S) (M := M) by_omega by_omega
  rw [← hRdef] at hR4
  obtain ⟨X, hXd⟩ : ∃ X, (S + i) % M = X := by_grind
  obtain ⟨Y, hYd⟩ : ∃ Y, (S + i') % M = Y := by_grind
  have hXY : Y = M - 1 - X := by
    rw [hXd] at hX; rw [hYd] at hY
    split_ifs at hi'M <;> rcases hX with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hY with ⟨c, d⟩ | ⟨c, d⟩ <;>
      rcases hR4 with ⟨e, f⟩ | ⟨e, f, g⟩ | ⟨e, f⟩ <;> omega
  have hXM : X < M := by_omega
  have e2 : ztypu % M = ztnqh % M := by
    rw [← Nat.add_assoc, Nat.add_mod, hXd, Nat.mod_eq_of_lt ztpdp]
  have e3 : (S + ztduy) % M = ztteg % M := by
    rw [← Nat.add_assoc, Nat.add_mod, hYd, Nat.mod_eq_of_lt ztpdp]
  rw [hYd, hXd, e2, e3, hXY]
  have sym : ∀ j, j ≤ M → sideE C.m (M - j) = sideE C.m j := by
    intro j hj; unfold sideE; split_ifs <;> omega
  constructor
  · rcases Nat.lt_or_ge _ M with h | h
    · rw [Nat.mod_eq_of_lt h, show M - 1 - X = M - ztnqh by omega, sym _ h.le]
    · rw [show X + 1 = M by omega, Nat.mod_self, show M - 1 - X = 0 by omega]
  · rcases Nat.eq_zero_or_pos X with h | h
    · rw [h, show M - 1 - 0 + 1 = M by omega, Nat.mod_self]
    · rw [show M - 1 - X + 1 = M - X by omega, Nat.mod_eq_of_lt (show M - X < M by omega),
        sym _ hXM.le]

/-- **The mirror of a walk position**: a proper position in the tour range whose key is the
mirror `mk` of the key. -/
theorem mir_key (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6)
    (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ztbfp ∧ (chainModel C).param C.P ztbfp < 1) :
    (chainModel C).key C.P zthyw = mk C ztxjf ∧
      0 ≤ (chainModel C).param C.P zthyw ∧
      (chainModel C).param C.P zthyw < 1 ∧ (mirPos C w hc).hgt ≤ C.P.n ∧
      6 ≤ (mirPos C w hc).edge ∧ (mirPos C w hc).edge ≤ 2 * C.m + 6 ∧
      (nz C w hc ≠ 0 → 0 < (chainModel C).param C.P zthyw) := by
  zubwh
  zuljf
  unfold mirPos
  zujpn
  · -- a vertex position
    have hpar := (param_eq_zero_iff C hD h6 h7.le hh).2 h0
    rw [show (chainModel C).key C.P ztbfp = w by rw [key_eq_param, hpar, add_zero], key_zero]
    have hm0 : 6 ≤ mirW0 C w ∧ mirW0 C w ≤ 2 * C.m + 6 := by unfold mirW0; grind
    refine ⟨?_, by_rfl, by_positivity, Nat.zero_le _, hm0.1, hm0.2,
      by omega⟩
    unfold mk mirW0
    by_cases hw : w ≤ 6 + rT C
    · have hw' : (w : ℝ) ≤ κT C := by rw [← hT]; exact_mod_cast by_grind
      zueyp
    · have hw' : ¬ (w : ℝ) ≤ κT C := by
        rw [← hT]; push Not; exact_mod_cast by_grind
      zueyt
  · -- an inner position
    have hc0 : hc ≠ 0 := fun e => h0 (by unfold nz; simp_all)
    obtain ⟨h, rfl⟩ : ∃ h, hc = h + 1 := ztdqr
    have hm1 : 6 ≤ mirW1 C w ∧ mirW1 C w < 2 * C.m + 6 := by unfold mirW1; grind
    obtain ⟨r1, r2⟩ := rev_idx C h6 h7
    have ht := param_of_ne C hD h6 h7.le h
    have ht' := param_of_ne C hD hm1.1 hm1.2.le h
    rw [walk_vtx C h6 h7.le, walk_next C h6 h7] at ht
    rw [walk_vtx C hm1.1 hm1.2.le, walk_next C hm1.1 hm1.2, r1, r2] at ht'
    set a := (C.P.vtx ztucx).2
    set b := (C.P.vtx (vaIdx C _)).2
    have hab : b - a ≠ 0 := by
      have := walk_nonhoriz C hD h6 h7.le
      rw [walk_vtx C h6 h7.le, walk_next C h6 h7] at this
      grind
    have hba : a - b ≠ 0 := by_grind
    set t := (chainModel C).param C.P ztboe with htdef
    have hpt : (chainModel C).param C.P ⟨mirW1 C w, h + 1⟩ = 1 - t := by
      grind
    have ht0 := fun e => h0 ((param_eq_zero_iff C hD h6 h7.le hh).1 e)
    zukgh
    refine ⟨?_, by_grind, by_grind, hh, hm1.1, hm1.2.le,
      by grind⟩
    rw [key_eq_param, key_eq_param, hpt, ← htdef]
    unfold mk mirW1
    by_cases hw : w < 6 + rT C
    · have hw' : (w : ℝ) + t ≤ κT C := by
        zuhnu
        zuhvd

      zueyp
    · have hw' : ¬ (w : ℝ) + t ≤ κT C := by
        rw [← hT]; push Not
        have : ztlwy := by exact_mod_cast by_grind
        linarith
      zueyt

/-- The normalised code of the mirror is its height code. -/
theorem nz_mir (hD : DistinctHeights C.P) {w hc : ℕ} (h6 : 6 ≤ w) (h7 : w < 2 * C.m + 6)
    (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ztbfp ∧ (chainModel C).param C.P ztbfp < 1) :
    nz C (mirPos C w hc).edge (mirPos C w hc).hgt = (mirPos C w hc).hgt := by
  obtain ⟨-, -, -, ph, e6, e7, hpos⟩ := mir_key C hD h6 h7 hh hp
  zuhbk
  · have : (mirPos C w hc).hgt = 0 := by unfold mirPos; simp_all
    zukyx
  · have hp0 := hpos h0
    have hne := fun e =>
      hp0.ne' ((param_eq_zero_iff C hD e6 e7 ph).2 e)
    exact nz_of_ne C hne

/-- The natural test of `InI`. -/
def inTest (C : Chain) (z w : ℕ) : Prop :=
  if z = 0 then ztkpw ∨ zthqp
  else 6 ≤ w ∧ w < 2 * C.m + 6

/-- **The open halves of the tour range in natural arithmetic.** -/
theorem inI_iff (hD : DistinctHeights C.P) {w hc : ℕ} (hw : w < 2 * C.m + 7) (hh : hc ≤ C.P.n)
    (hp : 0 ≤ (chainModel C).param C.P ztbfp ∧ (chainModel C).param C.P ztbfp < 1) :
    InI C ztxjf ↔ inTest C ztrua w := by
  zubwh
  zuljf
  rw [key_eq_param]
  unfold InI inTest
  zuhnu
  set t := (chainModel C).param C.P ztbfp
  by_cases hin : 6 ≤ w ∧ w < 2 * C.m + 6
  · zuhbk
    · have ht : ztbhh := (param_eq_zero_iff C hD hin.1 hin.2.le hh).2 h0
      rw [ite_eq_left h0, ht, add_zero]
      constructor
      · zuekn
        · left; constructor <;> [exact_mod_cast a; (have : (w : ℝ) < rT C + 6 := b; exact_mod_cast (show w < rT C + 6 by exact_mod_cast this) |>.trans_le by_omega)]
        · right; constructor
          · have  := a
            have : rT C + 6 < w := by exact_mod_cast this
            omega
          omega
      · zuekn
        · left; refine ztbjy
          zuhuk
        · right; refine ⟨?_, by exact_mod_cast b⟩
          zuhuk
    · have ht0 := fun e => h0 ((param_eq_zero_iff C hD hin.1 hin.2.le hh).1 e)
      zukgh
      zucqa
      simp only [hin, and_self, iff_true]
      have h6 : (6 : ℝ) ≤ w := by_simp_all
      have h7 : (w : ℝ) + 1 ≤ 2 * C.m + 6 := by exact_mod_cast by_grind
      rcases Nat.lt_or_ge w (rT C + 6) with h | h
      · left; refine ztkix
        zuhvd

      · right; refine zthma
        have : ztlwy := by exact_mod_cast h
        linarith
  · have hfalse : ¬ ((if nz C w hc = 0 then ztkpw ∨
        zthqp else 6 ≤ w ∧ w < 2 * C.m + 6)) := by
      grind
    simp only [hfalse, iff_false]
    rcases Nat.lt_or_ge w 6 with h | h
    · have : (w : ℝ) + 1 ≤ 6 := by exact_mod_cast by_simp_all
      grind
    · have hw' : ztpqi := by_omega
      have : (2 * C.m + 6 : ℝ) = w := by zuofq; simp
      have hRl : (rT C : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hR
      grind
