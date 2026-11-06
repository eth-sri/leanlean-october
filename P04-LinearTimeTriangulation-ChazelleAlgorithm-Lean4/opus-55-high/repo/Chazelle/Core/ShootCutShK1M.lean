module

public import Chazelle.MacT
public import Chazelle.Core.DownPhaseDrvBFar1
public import Chazelle.Core.WalkEmbed
public import Chazelle.Core.ShootCutLoop2
public import Chazelle.Core.OracleQuery
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.OracleBook

namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (xAt xAt_lerp edgeX)
namespace ShootCut
def k1Out (p₀ x0 w dir e' h : ℕ) : WPos :=
  if x0 ≤ e' ∧ e' < x0 + w then
    (if dir = 1 then (if h = e' + 1 then zteyx else zteyy)
     else (if h = e' then ztxmf
       else ztxmg))
  else if dir = 1 then (if h = x0 then zteyz else ztdqu)
  else (if h = x0 then ztdqu else zteyz)
variable {a b X : Point}
/-- A point of a non-horizontal segment is determined by its height. -/
theorem seg_pt (hab : a.2 ≠ b.2) (hX : X ∈ Chazelle.segment a b) :
    X = lerp a b (ztnqk / ztti) ∧ 0 ≤ ztnqk / ztti ∧
      ztnqk / ztti ≤ 1 := by
  zufkt
  have hne : ztmuc := sub_ne_zero.2 ztmbt
  have ht : (a.2 + t * ztti - a.2) / ztti = t := by_simp_all
  zubi
  zubys
  tauto

/-- **A point of a walk edge at the height of a vertex of `Q`** is the position with that height
code; its parameter is below `1` unless it is the end of the edge. -/
theorem walk_pos_at {M : Model} {Q : Polygon} {p h : ℕ} {X : Point}
    (hne : (M.wa p).2 ≠ (M.wb p).2) (hX : X ∈ Chazelle.segment ztpr ztoa)
    (hXh : X.2 = (Q.vtx h).2) (hb : X.2 ≠ (M.wb p).2) :
    M.pos Q ztdw = X ∧ 0 ≤ M.param Q ztdw ∧ M.param Q ztdw < 1 := by
  obtain ⟨hXe, h0, h1⟩ := seg_pt hne hX
  have hpar : M.param Q ztdw = (X.2 - (M.wa p).2) / ztcrr := by
    show ztgrq = _
    grind
  have hd : ztehi := sub_ne_zero.2 ztnr
  refine ⟨?_, by_grind, ?_⟩
  · show lerp ztpr ztoa (M.param Q ztdw) = X
    grind
  · zueyf
    refine lt_of_le_of_ne h1 fun h => hb ?_
    grind

/-- The abscissa of a point of an edge of `Q` at a given height. -/
theorem edge_x {Q : Polygon} {e h : ℕ} {X : Point} (hne : (Q.vtx e).2 ≠ (Q.vtx ztwki).2)
    (hX : X ∈ Q.edge e) (hXh : X.2 = (Q.vtx h).2) : X.1 = ((SymPt.onEdge e h).eval Q).1 := by
  zufjj
  show X.1 = edgeX Q e (Q.vtx h).2
  unfold edgeX
  rw [← hXh]
  conv_lhs => rw [hXe]
  rw [← xAt_lerp hne, ← hXe]

/-- A point of a segment between two points of a box of radius `r` is in it. -/
theorem seg_abs_le {r : ℝ} (ha : |a.1| ≤ r) (hb : |b.1| ≤ r)
    (hX : X ∈ Chazelle.segment a b) : |X.1| ≤ r := by
  zufkt
  zubi
  have h' : ztxtd := by_ring
  rw [h', abs_le]
  have := abs_le.1 ha
  have := abs_le.1 hb
  zueop
variable {C : Chain} {Q : Polygon}

/-- **The walk position of the hit of a kind-1 piece.** -/
theorem k1_hit (hD : DistinctHeights Q) (hS : Q.Simple) {p₀ x0 w dir : ℕ}
    (hblk : BlockWalk (chainModel C).W Q p₀ x0 w dir) (hw1 : 1 ≤ w) (hxw : x0 + w < Q.n)
    (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6) (hdir : dir = 1 ∨ dir = 0) {X : Point} {e' h : ℕ}
    (hXS : X ∈ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) (hXe : X ∈ Q.edge e')
    (he' : e' < Q.n) (hh : h < Q.n) (hXh : X.2 = (Q.vtx h).2) :
    (k1Out p₀ x0 w dir e' h).edge < 2 * C.m + 7 ∧
      ProperPos ztc Q Q.n ztets ∧
      (chainModel C).pos Q ztets = X ∧
      X.1 = ((SymPt.onEdge e' h).eval Q).1 ∧ |X.1| < C.radius := by
  zubzd
  zuerv
  have hn2 : ztsag := by_omega
  -- the walk edge of `X`
  obtain ⟨d, hd, hXd⟩ := (arcSet_nat (M := M) (p₀ := p₀) hw1 by_omega X).1 hXS
  -- abscissa and box
  have hx : X.1 = ((SymPt.onEdge e' h).eval Q).1 :=
    edge_x (SweepPrim.edge_heights_ne hD hn2 he') hXe hXh
  have hmemv : ∀ q, 6 ≤ q → q ≤ 2 * C.m + 6 → |(M.W.vtx q).1| ≤ Chazelle.Jordan.coordBound C.P := fun q h1 h2 => by
    zubpf
    zukpy
    exact (C.abs_le_coordBound_of_mem_set ztxuz).1
  have hbox : |X.1| < C.radius := lt_of_le_of_lt (seg_abs_le ztrrw
    ztrrw hXd) C.coordBound_lt_radius
  have hpos0 : ∀ q, M.pos Q ztkmm = M.W.vtx q := fun q => pos_box_vtx C Q q
  have wv : ztxrr := fun q hq => by
    unfold Model.wb; zuost
  have edge_eq : ∀ k, k + 1 < Q.n → Q.edge k = Chazelle.segment ztbda (Q.vtx zts) :=
    fun k hk => by unfold Polygon.edge; rw [Nat.mod_eq_of_lt hk]
  have hvinj : ∀ i j, i < Q.n → j < Q.n → (Q.vtx i).2 = (Q.vtx j).2 → i = j := fun i j hi hj he => by
    by_contra hne; exact hD i j hi hj hne he
  have atEnd : ∀ {a b : Point}, a.2 ≠ b.2 → X ∈ Chazelle.segment a b → X.2 = b.2 → X = b :=
    fun {a b} hne hX hy => by
      zufjj
      rw [hXe, hy, div_self (sub_ne_zero.2 ztnr)]
      simp
  have hw' : ∀ i j, i < Q.n → j < Q.n → Q.vtx i = Q.vtx j → i = j := fun i j hi hj he =>
    Chazelle.Jordan.simple_vtx_inj hS hi hj he
  have hpp : ∀ q, ProperPos M Q Q.n ztkmm := fun q => proper_vtx _ _ _ _
  suffices key : ∃ q : WPos, k1Out p₀ x0 w dir e' h = q ∧ q.edge < 2 * C.m + 7 ∧
      ProperPos M Q Q.n q ∧ M.pos Q q = X by
    obtain ⟨q, hq, a, b, c⟩ := key
    zvnck; exact ⟨a, b, c, hx, hbox⟩
  unfold k1Out
  by_cases hin : x0 ≤ e' ∧ e' < x0 + w
  · zulpy
    obtain ⟨j, hj⟩ : ∃ j, e' = x0 + j := ⟨e' - x0, by_omega⟩
    have hj' : e' - x0 = j := by_omega
    zuocw
    have hjw : j < w := by_omega
    have hEe := SweepPrim.edge_heights_ne hD hn2 he'
    rw [Nat.mod_eq_of_lt (show e' + 1 < Q.n by omega)] at hEe
    have hXe' : X ∈ Chazelle.segment ztvcv ztbafd := by
      grind
    zucos
    · zubyt
      have ha : M.W.vtx ztoet = Q.vtx e' := by
        have := hblk j by_omega; grind
      have hb : M.W.vtx (p₀ + j + 1) = Q.vtx zters := by
        have := hblk ztl by_omega; grind
      have hwa : M.wa ztoet = Q.vtx e' := ha
      have hwb : M.wb ztoet = Q.vtx zters := by zuobc
      by_cases hhe : h = e' + 1
      · zuiky

      · zulqg
        obtain ⟨hp, h0, h1⟩ := walk_pos_at (M := M) (Q := Q) (p := p₀ + j) (h := h)
          by_grind by_grind hXh
          by_grind
        exact zthmj
    · zuges
      set p := p₀ + ztqyj
      have ha : M.W.vtx p = Q.vtx zters := by
        have := hblk ztqyj by_omega; zvnee at this
        rw [this, hj]; congr 1; omega
      have hb : M.W.vtx ztr = Q.vtx e' := by
        have := hblk ztojs by_omega
        zvnee at this
        rw [show p + 1 = p₀ + ztojs by simp only [p]; ring, this, hj]; congr 1; omega
      have hwa : M.wa p = Q.vtx zters := ha
      have hwb : M.wb p = Q.vtx e' := by zuobc
      have hXr : X ∈ Chazelle.segment ztbafd ztvcv := by
        zukoy
      by_cases hhe : h = e'
      · zuiky

      · zulqg
        obtain ⟨hp, h0, h1⟩ := walk_pos_at (M := M) (Q := Q) (p := p) (h := h)
          by_grind by_grind hXh
          by_grind
        exact zthmj
  -- outside the block: `X` is an end of the chain
  rw [ite_eq_right hin]
  obtain ⟨k, hk1, hk2, hXk⟩ : ∃ k, x0 ≤ k ∧ k < x0 + w ∧ X ∈ Q.edge k := by
    zucos
    · refine ⟨x0 + d, by_omega, by_omega, ?_⟩
      zukrf
      have ha := hblk d by_omega; rw [ite_eq_left rfl] at ha
      have hb := hblk ztet by_omega; grind
    · refine ⟨x0 + w - d - 1, by_omega, by_omega, ?_⟩
      zukrf
      have ha := hblk d by_omega; zvnee at ha
      have hb := hblk ztet by_omega; zvnee at hb
      rw [ha, show p₀ + d + 1 = p₀ + ztet by ring, hb, Chazelle.Geometry.segment_comm] at hXd
      rwa [show x0 + w - ztet = x0 + w - d - 1 by omega,
        show x0 + w - d = x0 + w - d - 1 + 1 by omega] at hXd
  have hke : k ≠ e' := fun h' => hin by_omega
  have e1 := Chazelle.Jordan.simple_endpoint_of_mem_two hS (i := k) (j := e') by_omega he' hke
    hXk hXe
  have e2 := Chazelle.Jordan.simple_endpoint_of_mem_two hS (i := e') (j := k) he' by_omega
    (Ne.symm hke) hXe hXk
  rw [Nat.mod_eq_of_lt (show k + 1 < Q.n by omega)] at e1
  obtain ⟨v, hv1, hv2, hXv⟩ : ∃ v, x0 ≤ v ∧ v ≤ x0 + w ∧ X = Q.vtx v := by
    zukkj
    · exact ⟨k, by_omega, by_omega, e⟩
    · exact ⟨k + 1, by_omega, by_omega, e⟩
  have hhv : h = v := hvinj _ _ hh by_omega by_grind
  have hvend : v = x0 ∨ v = x0 + w := by
    zux

    zukkk
    · grind
    · rcases Nat.lt_or_ge zters Q.n with hl | hl
      · rw [Nat.mod_eq_of_lt hl] at e
        grind
      · rw [show e' + 1 = Q.n by omega, Nat.mod_self] at e
        have := hw' _ _ by_omega by_omega (hXv.symm.trans e); omega
  have hv0 : M.W.vtx p₀ = Q.vtx (if dir = 1 then x0 else x0 + w) := by
    have := hblk 0 by_omega; omega
  have hvw : M.W.vtx (p₀ + w) = Q.vtx (if dir = 1 then x0 + w else x0) := by
    have := hblk w le_rfl; zvmwk
    simp
  zucos
  · zubyt
    rw [ite_eq_left rfl] at hv0 hvw
    zujuc
    · zujke

    · zufnu

  · zuges
    zvnee at hv0 hvw
    zujuc
    · zujke

    · zufnu
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
namespace ShootCut
def InC (C : Chain) (x : Point) : Prop := |x.1| < C.radius ∧ |x.2| < C.radius ∧ x.2 ≤ C.top.2
theorem inC_of_mem {C : Chain} {x : Point} (h : x ∈ C.set) : InC C x :=
  ⟨lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set h).1 C.coordBound_lt_radius,
    lt_of_le_of_lt (C.abs_le_coordBound_of_mem_set h).2 C.coordBound_lt_radius,
    C.snd_le_top_of_mem_set h⟩
theorem conv_gt {lo a b t : ℝ} (ha : lo < a) (hb : lo < b) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    lo < ztca * a + t * b := by
  zukkm
  · nlinarith [mul_pos h (sub_pos.2 hb), mul_nonneg ztkfr (sub_pos.2 ha).le]
  · zujpp
theorem conv_lt {hi a b t : ℝ} (ha : a < hi) (hb : b < hi) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ztca * a + t * b < hi := by
  have := conv_gt (lo := -hi) (a := -a) (b := -b) by_linarith by_linarith h0 h1
  linarith

/-- A segment between two points of `C` is in `InC C`. -/
theorem inC_seg {C : Chain} {a b x : Point} (ha : a ∈ C.set) (hb : b ∈ C.set)
    (hx : x ∈ Chazelle.segment a b) : InC C x := by
  have la := inC_of_mem ha
  have lb := inC_of_mem hb
  obtain ⟨t, h0, h1, rfl⟩ := hx
  simp only [InC] at la lb ⊢
  have e1 : ztxtd := by_ring
  have e2 : a.2 + t * ztti = ztca * a.2 + t * b.2 := by_ring
  zuea
  obtain ⟨a1, a2, a3⟩ := la
  obtain ⟨b1, b2, b3⟩ := lb
  zvncj at a1 a2 b1 b2 ⊢
  zumlw
  refine ⟨⟨conv_gt a1.1 b1.1 h0 h1, conv_lt a1.2 b1.2 h0 h1⟩,
    ⟨conv_gt a2.1 b2.1 h0 h1, conv_lt a2.2 b2.2 h0 h1⟩, by_nlinarith⟩

/-- **The points of a block of tour edges** are points of `C`. -/
theorem block_inC {C : Chain} {p₀ w : ℕ} (hw : 1 ≤ w) (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6)
    {x : Point} (hx : x ∈ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) : InC C x := by
  zucwl
  obtain ⟨d, hd, hxd⟩ := (arcSet_nat (M := chainModel C) (p₀ := p₀) hw by_omega x).1 hx
  have hv : ∀ q, 6 ≤ q → q ≤ 2 * C.m + 6 → (chainModel C).W.vtx q ∈ C.set := fun q h1 h2 => by
    zubpf
    zukpy
    exact C.vertex_mem_set ztbdw
  exact inC_seg ztrsf ztrsf hxd
variable {C : Chain} {S : Set Point} {z : Point} {σ : ℝ}

/-- **No hit from the side of the box ahead of the ray.** -/
theorem noHit_ahead_side (hσ : σ = 1 ∨ σ = -1) (hz : z.1 = σ * C.radius)
    (hS : ∀ x ∈ S, InC C x) : NoHit S z σ := fun t ht hm => by
  have h := (hS _ hm).1
  simp only [rayPt_fst, hz] at h
  zvncj at h
  rcases hσ with rfl | rfl <;> [linarith [h.2]; linarith [h.1]]

/-- **No hit above the top of `C`.** -/
theorem noHit_above (hz : C.top.2 < z.2) (hS : ∀ x ∈ S, InC C x) : NoHit S z σ :=
  fun t _ hm => by
    have h := (hS _ hm).2.2
    zuipu

/-- **No hit on the line of the top or of the bottom of the box.** -/
theorem noHit_ext (hz : C.radius ≤ |z.2|) (hS : ∀ x ∈ S, InC C x) : NoHit S z σ :=
  fun t _ hm => by
    have h := (hS _ hm).2.1
    zuipu

/-- **Shifting the origin along the side of the box behind the ray.** -/
theorem box_shift (hσ : σ = 1 ∨ σ = -1) {R R' : ℝ} {z' : Point} (hz : z.1 = -σ * R)
    (hz' : z'.1 = -σ * R') (hy : z.2 = z'.2) (hS : ∀ x ∈ S, |x.1| < R ∧ |x.1| < R') :
    ztxcv ∧
      ztlfk := by
  refine firstHit_shift hσ hy fun x hx _ => ?_
  have h := hS x hx
  simp only [abs_lt] at h
  rw [hz, hz']
  zur
  · grind
  simp_all

/-- **The relation of a query origin to the origin of the ray.** -/
def QRel (P : Polygon) (C : Chain) (σ : ℝ) (z : Point) : QOrigin → Prop
  | .sym s => s.eval zta = z
  | .box h => z = (-σ * C.radius, ((Qof P).vtx h).2)

/-- **The answer of a query** for the origin of the ray, from the answer for a related query
origin. -/
theorem query_transfer {P : Polygon} (hσ : σ = 1 ∨ σ = -1) {Cα : Chain} {o : QOrigin}
    (hrel : QRel P C σ z o) (hS : S ⊆ Cα.set) (hSC : ∀ x ∈ S, InC C x) :
    (∀ t', FirstHit S ztwyf σ t' →
      FirstHit S z σ ztbalt ∧
        rayPt z σ ztbalt =
          rayPt ztwyf σ t') ∧
      (NoHit S ztwyf σ → NoHit S z σ) := by
  zuhfy
  cases o with
  | sym s =>
    zujnw
    simp only [QOrigin.eval, hrel]
    refine ⟨fun t' ht' => ?_, id⟩
    have : σ * ((rayPt z σ t').1 - z.1) = t' := by
      zugff
    zvmwk; exact ⟨ht', rfl⟩
  | box h =>
    zujnw
    simp only [QOrigin.eval]
    have hsh := box_shift (S := S) (z := z) hσ (R := C.radius) (R' := Cα.radius)
      (z' := zthqe) by_simp_all rfl by_simp_all
      (fun x hx => ⟨(hSC x hx).1, (Cα.set_subset_box (hS hx)).1⟩)
    refine ⟨fun t' ht' => ?_, hsh.2⟩
    have hf := hsh.1 t' ht'
    have e : σ * ((rayPt zthqe σ t').1 - z.1) =
        t' + σ * ((-σ * Cα.radius, ((Qof P).vtx h).2).1 - z.1) := by
      zugff
    zui
    refine ⟨hf, ?_⟩
    ext
    · zudch
    · simp_all
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## The environment across a query -/

/-- **The environment survives** a step keeping its registers (but the allocator), the memory
below the allocator, and not lowering the allocator. -/
theorem ShEnv.of_agree {c c' : Config} (E : ShEnv P W H C z σ c)
    (hr : ∀ r, envR r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    ShEnv P W H C z σ c' := by
  have e403 := hr _ ztp by_decide
  obtain ⟨hB5, hwf⟩ := E.hwf
  obtain ⟨hlen, hHwf, hHA, hs⟩ := hwf H C E.hD
  have hD' : ChainDescAt c'.nmem _ _ H C :=
    chainDesc_agree' E.hD hB5 hHA hm
  have hB' : c'.nmem _ = c.nmem ztfgq := hm _ by_omega
  -- a host read in the new memory is the host
  have hback : ∀ H' C', ChainDescAt c'.nmem ztfgq _ H' C' →
      ChainDescAt c.nmem _ zta H' C' := fun H' C' h' => by
    have hlen' : H'.length = H.length := by
      have a1 := h'.1.1
      zulhb

    exact chainDesc_agree' h' hB5 by_omega by_simp_all
  refine ⟨E.hG, E.hW, by_simp_all, ⟨by_omega, fun H' C' h' => ?_⟩,
    fun H' h' => ?_, by rw [hr K1 by_tauto by_decide]; exact E.k1, ?_, ?_, ?_,
    E.hσ⟩
  · grind
  · rw [e403, hB'] at h'
    have hlen' : H'.length = H.length := by
      have a1 := h'.1
      zulhb

    exact E.hreg H' (hostAt_agree' h' by_omega ztfbu)
  · exact E.ox.copy ztrsa (hr _ by_tauto
      by_decide) (hr _ by_tauto by_decide) (hr _ by_tauto
      by_decide)
  · exact E.oy.copy ztrsa (hr _ by_tauto
      by_decide) (hr _ by_tauto by_decide)
  · rw [hr 140241 by_tauto by_decide]; exact E.sig

/-! ## The walk position of the hit on the RAM -/

/-- `if a = b then T else E`. -/
def ifEq (a b : ℕ) (T E : Stmt) : Stmt := .ifLtN a b E (.ifLtN b a E T)

/-- Write the walk position `(e, h)` given by two instructions. -/
def wpos (i₁ i₂ : Instr) : Stmt := block [i₁, i₂]

/-- **`k1Out` on the RAM**: inputs `p₀ = 140250`, `x₀ = 140256`, `dir = 140257`, `w = 140258`,
`e' = 120006`, `h = 140236`; output `140225`, `140226`. -/
def k1OutR : Stmt :=
  .seq (.instr (.addN 140351 140256 140258))
    (.ifLtN 120006 140256
      (.ifLtN 140257 K1
        (ifEq 140236 140256 ztxyh
          ztxyi)
        (ifEq 140236 140256 ztxyi
          ztxyh))
      (.ifLtN 120006 140351
        (.seq (.instr (.subN 140352 120006 140256))
          (.ifLtN 140257 K1
            (.seq (block [.subN 140353 140258 K1, .subN 140353 140353 140352,
                .addN 140353 140250 140353])
              (ifEq 140236 120006 ztzyk
                ztitz))
            (.seq (block [.addN 140353 140250 140352, .addN 140354 120006 K1])
              (ifEq 140236 140354 ztzyk
                ztitz))))
        (.ifLtN 140257 K1
          (ifEq 140236 140256 ztxyh
            ztxyi)
          (ifEq 140236 140256 ztxyi
            ztxyh))))

/-- The registers written by `k1OutR`. -/
def Bko (r : ℕ) : Bool := r == 140225 || r == 140226 || decide (140351 ≤ r ∧ r < 140355)
theorem wr_k1OutR : wr Bko k1OutR = true := by_decide
theorem ifEq_exec {a b : ℕ} {T E : Stmt} (c : Config) {K : ℕ} {R : Config → Prop}
    (hT : c.nreg a = c.nreg b → ∃ c' k, Exec P W T c c' k ∧ k ≤ K ∧ R c')
    (hE : c.nreg a ≠ c.nreg b → ∃ c' k, Exec P W E c c' k ∧ k ≤ K ∧ R c') :
    ∃ c' k, Exec P W (ifEq a b T E) c c' k ∧ k ≤ K + 4 ∧ R c' := by
  unfold ifEq
  zubai
  · zueal
    exact ⟨c', _, .ifLtN_true h1 ex, by_omega, q⟩
  zubjz
  · zueal
    exact ⟨c', _, .ifLtN_false h1 (.ifLtN_true h2 ex), by_omega, q⟩
  · obtain ⟨c', k, ex, hk, q⟩ := hT by_omega
    exact ⟨c', _, .ifLtN_false h1 (.ifLtN_false h2 ex), by_omega, q⟩
theorem wpos_exec {i₁ i₂ : Instr} {c c₁ c₂ : Config} (e₁ : Exec P W (.instr i₁) c c₁ 1)
    (e₂ : Exec P W (.instr i₂) c₁ c₂ 1) : Exec P W (wpos i₁ i₂) c c₂ 2 :=
  Exec.block_cons e₁ ztihc
theorem k1OutR_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1)
    {p₀ x0 w dir e' h : ℕ} (h50 : c.nreg 140250 = p₀) (h56 : c.nreg 140256 = x0)
    (h57 : c.nreg 140257 = dir) (h58 : c.nreg 140258 = w) (h06 : c.nreg 120006 = e')
    (h36 : c.nreg 140236 = h) (hdir : dir = 1 ∨ dir = 0) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) (hW3 : e' + 1 ≤ W) (hW4 : h + 1 ≤ W) :
    ∃ c' k, Exec P W k1OutR c c' k ∧ k ≤ 30 ∧ c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt ∧ FrameB Bko c c' := by
  suffices key : ∃ c' k, Exec P W k1OutR c c' k ∧ k ≤ 30 ∧
      c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt by
    obtain ⟨c', k, ex, hk, a, b⟩ := key
    exact ⟨c', k, ex, hk, a, b, exec_frameB ex wr_k1OutR⟩
  have e₀ := Exec.addN (P := P) hw 140351 140256 140258 by_omega
  set c₁ : Config := { c with nreg := upd c.nreg 140351 _ } with hc₁
  have w₁ := e₀.wb_right
  have g₁ : ∀ r, r ≠ 140351 → c₁.nreg r = c.nreg r := by_simp_all
  have q51 : c₁.nreg 140351 = x0 + w := by_simp_all
  have q50 := (g₁ 140250 by_decide).trans h50
  have q56 := (g₁ 140256 by_decide).trans h56
  have q57 := (g₁ 140257 by_decide).trans h57
  have q58 := (g₁ 140258 by_decide).trans h58
  have q06 := (g₁ 120006 by_decide).trans h06
  have q36 := (g₁ 140236 by_decide).trans h36
  have qK := (g₁ K1 by_decide).trans h1
  -- the leaves: a vertex position `(p₀, 0)` or `(p₀ + w, 0)`
  have vP : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 140250 = p₀ →
      ∃ c' k, Exec P W _ c₂ c' k ∧ k ≤ 2 ∧
        c'.nreg 140225 = p₀ ∧ c'.nreg 140226 = 0 := fun c₂ hw₂ g50 => by
    have ea := Exec.copyN (P := P) hw₂ 140225 140250
    zudxu

  have vW : ∀ c₂ : Config, WordsBounded W c₂ → c₂.nreg 140250 = p₀ → c₂.nreg 140258 = w →
      ∃ c' k, Exec P W _ c₂ c' k ∧ k ≤ 2 ∧
        c'.nreg 140225 = p₀ + w ∧ c'.nreg 140226 = 0 := fun c₂ hw₂ g50 g58 => by
    have ea := Exec.addN (P := P) hw₂ 140225 140250 140258 by_omega
    zudxu

  -- the outside cases
  have outside : ¬ (x0 ≤ e' ∧ e' < x0 + w) → ∃ c' k, Exec P W (.ifLtN 140257 K1
      _
      _) c₁ c' k ∧ k ≤ 8 ∧
      c'.nreg 140225 = (k1Out p₀ x0 w dir e' h).edge ∧
      c'.nreg 140226 = (k1Out p₀ x0 w dir e' h).hgt := fun hout => by
    unfold k1Out
    rw [ite_eq_right hout]
    zucos
    · zubyt
      obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 140256)
        (T := wpos ztfma ztbtj)
        (E := wpos zteee ztbtj) c₁ (K := 2)
        (R := fun c' => c'.nreg 140225 = (if h = x0 then (zteyz : WPos) else ztdqu).edge ∧
          c'.nreg 140226 = (if h = x0 then (zteyz : WPos) else ztdqu).hgt)
        by_simp_all
        by_simp_all
      exact ⟨c', _, .ifLtN_false by_omega ex, by_omega, v1, v2⟩
    · zufa
      obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (P := P) (W := W) (a := 140236) (b := 140256)
        (T := wpos zteee ztbtj)
        (E := wpos ztfma ztbtj) c₁ (K := 2)
        (R := fun c' => c'.nreg 140225 = (if h = x0 then (ztdqu : WPos) else zteyz).edge ∧
          c'.nreg 140226 = (if h = x0 then (ztdqu : WPos) else zteyz).hgt)
        by_simp_all
        by_simp_all
      exact ⟨c', _, .ifLtN_true by_omega ex, by_omega, v1, v2⟩
  unfold k1OutR
  by_cases t1 : c₁.nreg 120006 < c₁.nreg 140256
  · zudiq
    exact ⟨c', _, .seq e₀ ztspp, by_omega, v1, v2⟩
  by_cases t2 : c₁.nreg 120006 < c₁.nreg 140351
  swap
  · zudiq
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 ztjdk), by_omega, v1, v2⟩
  -- inside the block
  have hin : x0 ≤ e' ∧ e' < x0 + w := by_omega
  have e₁ := Exec.subN (P := P) w₁ 140352 120006 140256
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg 140352 _ }
    with hc₂
  have w₂ := e₁.wb_right
  have g₂ : ∀ r, r ≠ 140352 → c₂.nreg r = c₁.nreg r := by_simp_all
  have q52 : c₂.nreg 140352 = e' - x0 := by_simp_all
  have r50 := (g₂ 140250 by_decide).trans q50
  have r57 := (g₂ 140257 by_decide).trans q57
  have r58 := (g₂ 140258 by_decide).trans q58
  have r06 := (g₂ 120006 by_decide).trans q06
  have r36 := (g₂ 140236 by_decide).trans q36
  have rK := (g₂ K1 by_decide).trans qK
  unfold k1Out
  zulpy
  zucos
  · -- upward
    zubyt
    obtain ⟨c₃, k₃, e₃, hk₃, s53, s54, g₃⟩ : ∃ c₃ k₃, Exec P W _ c₂ c₃ k₃ ∧ k₃ = 2 ∧ c₃.nreg 140353 = p₀ + (e' - x0) ∧
        c₃.nreg 140354 = e' + 1 ∧ ∀ r, r ≠ 140353 → r ≠ 140354 → c₃.nreg r = c₂.nreg r := by
      have ea := Exec.addN (P := P) w₂ 140353 140250 140352 by_omega
      have eb := Exec.addN (P := P) ea.wb_right 140354 120006 K1 (by
        zuned; zunwr; omega)
      refine ⟨_, _, Exec.block_cons ea ztbws, rfl,
        by zuned; omega, by zuned; zunwr, fun r h1 h2 => by
          zungi⟩
    zubj
    zukir
    have sK : ztizo := by rw [g₃ _ by_decide by_decide, rK]
    obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (b := 140354) c₃
      (R := fun c' => c'.nreg 140225 = (if h = e' + 1 then (zteyx : WPos)
          else zteyy).edge ∧
        c'.nreg 140226 = (if h = e' + 1 then (zteyx : WPos)
          else zteyy).hgt)
      (fun he => by
        zuimn
        zubqn

        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_left he]; zuont; exact sK,
          by rw [ite_eq_left he]; simp⟩)
      (fun he => by
        zuimn
        zuffh
        have eb' := Exec.addN (P := P) ea'.wb_right 140226 140236 K1
          ztgge
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by zunky; zupbi,
          by zunky; zuned; zunws⟩)
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 (.ifLtN_true t2 (.seq e₁ (.ifLtN_false
      by_omega ztncp)))), by_omega, v1, v2⟩
  · -- downward
    zufa
    obtain ⟨c₃, k₃, e₃, hk₃, s53, g₃⟩ : ∃ c₃ k₃, Exec P W _ c₂ c₃ k₃ ∧ k₃ = 3 ∧
        c₃.nreg 140353 = p₀ + ztbns ∧
        ∀ r, r ≠ 140353 → c₃.nreg r = c₂.nreg r := by
      have ea := Exec.subN (P := P) w₂ 140353 140258 K1
      have eb := Exec.subN (P := P) ea.wb_right 140353 140353 140352
      have ec := Exec.addN (P := P) eb.wb_right 140353 140250 140353 (by
        zuned; omega)
      refine ⟨_, _, Exec.block_cons ea (Exec.block_cons eb (Exec.block_cons ec
        (Exec.block_nil ec.wb_right))), rfl, ?_, fun r hr => by zumwy⟩
      zuned; rw [← K1, r50, r58, rK, q52]
    zubj
    zukir
    have s06 : c₃.nreg 120006 = e' := by_grind
    have sK : ztizo := by rw [g₃ _ by_decide, rK]
    obtain ⟨c', k, ex, hk, v1, v2⟩ := ifEq_exec (b := 120006) c₃
      (R := fun c' => c'.nreg 140225 = (if h = e' then (ztxmf : WPos)
          else ztxmg).edge ∧
        c'.nreg 140226 = (if h = e' then (ztxmf : WPos)
          else ztxmg).hgt)
      (fun he => by
        zuimm
        zubqn

        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by rw [ite_eq_left he]; zuont; exact sK,
          by rw [ite_eq_left he]; simp⟩)
      (fun he => by
        zuimm
        zuffh
        have eb' := Exec.addN (P := P) ea'.wb_right 140226 140236 K1
          ztgge
        exact ⟨_, _, wpos_exec ea' eb', le_rfl, by zunky; zupbi,
          by zunky; zuned; zunws⟩)
    exact ⟨c', _, .seq e₀ (.ifLtN_false t1 (.ifLtN_true t2 (.seq e₁ (.ifLtN_true
      by_omega ztncp)))), by_omega, v1, v2⟩
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
@[expose] public section
def qSet : Stmt :=
  block [.addN 140350 140255 K1, .addN 140350 140350 K1, .loadN 120000 140350,
    .copyN 120001 140238, .copyN 120002 140239, .copyN 120003 140240, .copyN 120004 140008]

/-- The candidate of a hit. -/
def qHit : Stmt :=
  .seq k1OutR (block [.constN 140220 1, .constN 140221 1, .constN 140222 1, .copyN 140223 120006,
    .copyN 140224 140236])

/-- **A kind-1 piece.** -/
def pieceK1 (query : Stmt) : Stmt :=
  .ifLtN 140237 K1 .skip
    (.seq qSet (.seq query (.seq (.ifLtN 120005 K1 cand0 ztprw) mrg)))
variable {c c' : Config}
theorem qOriginIn_of_eq {r : ℕ} {o : QOrigin} (h : QOriginIn c r o)
    (he : ∀ j, r ≤ j → j < r + 3 → c'.nreg j = c.nreg j) : QOriginIn c' r o := by
  cases o with
  | sym s => exact symPtIn_of_eq h he
  | box h' =>
    zubkx
    exact ztkjb
theorem qOriginIn_copy {r r' : ℕ} {o : QOrigin} (h : QOriginIn c r o)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : QOriginIn c' r' o := by
  cases o with
  | sym s => exact NFLoc.symPtIn_copy h h0 h1 h2
  | box h' =>
    obtain ⟨a, b⟩ := h
    exact ztgy

/-- The band-`14` registers written by `pieceK1`. -/
def Wk1 (r : ℕ) : Bool :=
  decide (140210 ≤ r ∧ r < 140227) || r == 140310 || decide (140350 ≤ r ∧ r < 140355)
theorem oracleBands_mem (r : ℕ) (h : bandOf r = 1 ∨ bandOf r = 3 ∨ bandOf r = 4 ∨ bandOf r = 5 ∨
    bandOf r = 6 ∨ bandOf r = 12 ∨ bandOf r = 13 ∨ bandOf r = 14 ∨ bandOf r = 15) :
    bandOf r ∈ oracleBands := by
  simp only [oracleBands, kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bShoot,
    bCut, bCluster, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  omega
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
theorem wr_qSet : wr (fun r => r == 140350 || decide ztgxm) qSet = true := by
  decide
theorem qSet_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {en : ℕ}
    (h55 : c.nreg 140255 = en) (hW : en + 2 ≤ W) :
    ∃ c' k, Exec P W qSet c c' k ∧ k = 7 ∧ c'.nreg 120000 = c.nmem ztfrd ∧
      c'.nreg 120001 = c.nreg 140238 ∧ c'.nreg 120002 = c.nreg 140239 ∧
      c'.nreg 120003 = c.nreg 140240 ∧ c'.nreg 120004 = c.nreg 140008 ∧
      FrameB (fun r => r == 140350 || decide ztgxm) c c' := by
  zubfu
  obtain ⟨c', k, ex, hk, v0, v1, v2, v3, v4⟩ : ∃ c' k, Exec P W qSet c c' k ∧ k = 7 ∧
      c'.nreg 120000 = c.nmem ztfrd ∧ c'.nreg 120001 = c.nreg 140238 ∧
      c'.nreg 120002 = c.nreg 140239 ∧ c'.nreg 120003 = c.nreg 140240 ∧
      c'.nreg 120004 = c.nreg 140008 := by
    unfold qSet
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; rw [h55, h1']; omega) | skip
    simp_all
  exact ⟨c', k, ex, hk, v0, v1, v2, v3, v4, exec_frameB ex wr_qSet⟩

/-- The registers written by `qHit`. -/
def Bqh (r : ℕ) : Bool := Bko r || decide (140220 ≤ r ∧ r < 140225)
theorem wr_qHit : wr Bqh qHit = true := by_decide
theorem qHit_exec (c : Config) (hw : WordsBounded W c) (h1 : c.nreg K1 = 1)
    {p₀ x0 w dir e' h : ℕ} (h50 : c.nreg 140250 = p₀) (h56 : c.nreg 140256 = x0)
    (h57 : c.nreg 140257 = dir) (h58 : c.nreg 140258 = w) (h06 : c.nreg 120006 = e')
    (h36 : c.nreg 140236 = h) (hdir : dir = 1 ∨ dir = 0) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) (hW3 : e' + 1 ≤ W) (hW4 : h + 1 ≤ W) {S : Set Point} {X : Point}
    (he' : e' < P.n) (hh : h < P.n) (hF : FirstHit S z σ ztbabg) (hXz : X.2 = z.2)
    (hout : (k1Out p₀ x0 w dir e' h).edge < 2 * C.m + 7 ∧
      ProperPos ztc zta P.n ztets ∧
      (chainModel C).pos zta ztets = X ∧
      X.1 = ((SymPt.onEdge e' h).eval zta).1 ∧ |X.1| < C.radius) :
    ∃ c' k, Exec P W qHit c c' k ∧ k ≤ 40 ∧ CandAt P C c' 140220 S z σ ∧ FrameB Bqh c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, v25, v26, f₁⟩ := k1OutR_exec (P := P) c hw h1 h50 h56 h57 h58 h06 h36
    hdir hW1 hW2 hW3 hW4
  zumfm
  have q06 : c₁.nreg 120006 = e' := by rw [k₁' _ by_decide, h06]
  have q36 : c₁.nreg 140236 = h := by rw [k₁' _ by_decide, h36]
  obtain ⟨c₂, k₂, e₂, hk₂, v20, v21, v22, v23, v24, g₂⟩ : ∃ c₂ k₂, Exec P W (block
      [.constN 140220 1, .constN 140221 1, .constN 140222 1, .copyN 140223 120006,
        .copyN 140224 140236]) c₁ c₂ k₂ ∧ k₂ = 5 ∧ c₂.nreg 140220 = 1 ∧ c₂.nreg 140221 = 1 ∧
      c₂.nreg 140222 = 1 ∧ c₂.nreg 140223 = e' ∧ c₂.nreg 140224 = h ∧
      ∀ r, (r < 140220 ∨ 140225 ≤ r) → c₂.nreg r = c₁.nreg r := by
    zud
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by_simp_all,
      by simp_all, fun r hr => ?_⟩
    zubd
  have ex : Exec P W qHit c c₂ _ := .seq e₁ e₂
  obtain ⟨ho1, ho2, ho3, ho4, ho5⟩ := hout
  zulkt
  refine ⟨c₂, _, ex, by_omega, ⟨by zuods, by_omega, fun _ => ⟨X.1, ⟨C.radius_pos,
    Or.inr (Or.inr ⟨v21, ho5, .onEdge e' h, ⟨v22, v23, v24⟩, ⟨he', hh⟩, ho4.symm⟩)⟩, hF,
    by simp_all,
    by simp_all,
    by rw [g₂ _ by_omega, g₂ _ by_omega, v25, v26, ho3]; grind⟩⟩,
    exec_frameB ex wr_qHit⟩

/-- A frame of a statement writing only registers of `B` and bands of `oracleBands`. -/
theorem frame_ob {B : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → ztbav ∧
      r ≠ ALLOC) (k : ℕ) : Frame oracleBands c c' k :=
  frame_of_frameB h (fun r hr => ⟨oracleBands_mem r by_grind,
    by simp_all⟩) k
theorem pieceK1_exec {O : OracleIface} (hV : O.Valid) (c : Config) (hw : WordsBounded W c)
    (E : ShEnv P W H C z σ c) (h08 : dirOf ztghb = σ) {S₀ : Set Point}
    (hB : CandAt P C c 140210 S₀ z σ) {p₀ en x0 w dir : ℕ} (h50 : c.nreg 140250 = p₀)
    (h55 : c.nreg 140255 = en) (h56 : c.nreg 140256 = x0) (h57 : c.nreg 140257 = dir)
    (h58 : c.nreg 140258 = w) (hblk : BlockWalk (chainModel C).W zta p₀ x0 w dir)
    (hw1 : 1 ≤ w) (hxw : x0 + w < P.n) (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6)
    (hdir : dir = 1 ∨ dir = 0)
    (hAt : O.At P c.nmem ztzdt)
    (hCα : ∃ Hs Cα, ChainDescAt c.nmem (c.nmem ztzdt) zta Hs Cα ∧
      Cα.set = (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ))
    (hqk : c.nreg 140237 ≤ 1)
    (hq0 : c.nreg 140237 = 0 → NoHit ((chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) z σ)
    (hq1 : c.nreg 140237 = 1 → c.nreg 140234 = 1 ∧
      ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o)
    (hQs : (Qof P).Simple) {Kq : ℕ}
    (hcost : ⌈(O.κ : ℝ) * ((c.nmem (c.nmem ztfrd + 2) : ℝ) ^ ztby *
      ((c.nmem (c.nmem ztzdt + 2) : ℝ) + 1) ^ ztcd + 1)⌉₊ ≤ Kq)
    (hroom : c.nreg ALLOC + Kq + 400 ≤ W) (hWen : en + 2 ≤ W) (hW1 : p₀ + w + 1 ≤ W)
    (hW2 : x0 + w ≤ W) :
    ∃ c' k, Exec P W ztwbs c c' k ∧ k ≤ Kq + 400 ∧
      CandAt P C c' 140210 (S₀ ∪ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) z σ ∧
      Frame oracleBands c c' k ∧
      (∀ r, 140000 ≤ r → r < 160000 → Wk1 r = false → c'.nreg r = c.nreg r) ∧
      ShEnv P W H C z σ c' := by
  set S := (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ) with hSdef
  have hW' : ztmd := by have := E.hW; unfold hostWords at this; omega
  zuc
  have hD := distinct_Qof E.hG
  zujac
  unfold pieceK1
  by_cases t0 : c.nreg 140237 < c.nreg K1
  · -- no query: no hit
    have hN := hq0 by_omega
    zugqx
    have hu := cand_union E.hσ c₁' (show Cand S z σ 0 0 from ⟨by_omega,
      by grind⟩)
    simp only [zero_ne_one, false_and, ↓reduceIte] at hu
    exact ⟨c, _, .ifLtN_true t0 ztjd, by_omega, CandAt.of_cand hB.1 hu r₁,
      frame_of_frameB (FrameB.refl ztczi c) (fun r h => by_grind) _,
      by omega, E⟩
  have hq : ztunn := by_omega
  obtain ⟨hyk, o, hoIn, hoLt, hrel⟩ := hq1 hq
  -- the origin is at the height of a vertex of `Q`
  obtain ⟨-, hzR, -, hhi, hzh⟩ : c.nreg 140234 = 1 ∧ |z.2| < C.radius ∧
      c.nreg ztsrv = 0 ∧ c.nreg ztfmr < P.n ∧
      z.2 = ((Qof P).vtx (c.nreg ztfmr)).2 := by
    rcases E.oy with ⟨h', _⟩ | ⟨h', _⟩ | h' <;> [omega; omega; exact h']
  set h := c.nreg ztfmr with hhdef
  -- the query inputs
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, v3, v4, f₁⟩ := qSet_exec (P := P) c hw k1 h55 hWen
  have kq₁ : ∀ r, r ≠ 140350 → ¬ ztgxm → c₁.nreg r = c.nreg r :=
    fun r h1 h2 => f₁.1 r by_grind
  zugmw
  have hA₁ : ztdc := kq₁ _ by_decide by_decide
  have hoIn₁ := qOriginIn_copy hoIn v1 v2 v3
  have hq0' : rd c₁ bOQuery 0 = c.nmem _ := v0
  -- the query
  obtain ⟨c₂, k₂, e₂, hk₂, post₂, F₂⟩ := hV.2.2 P W c₁ e₁.wb_right
    ⟨E.hG, E.hW, by_grind, o, hoLt, hoIn₁⟩ (by
      grind)
  replace hk₂ : k₂ ≤ Kq := by
    grind
  obtain ⟨Hs, Cα, hCd, hCs⟩ := hCα
  have hpost := post₂ Hs Cα o by_grind hoIn₁
  have hdir₁ : dirOf (rd c₁ bOQuery 4) = σ := by show dirOf (c₁.nreg 120004) = σ; grind
  rw [hdir₁] at hpost
  -- the frame of the query
  obtain ⟨Fr, Frr, Fm, Frm, Fo, Fa1, Fa2⟩ := F₂
  have kq₂ := Fr
  have band14 : ∀ r, 140000 ≤ r → r < 160000 → bandOf r ∉ kernelBands ∪ {bOQuery} := fun r h1 h2 => by
    simp only [kernelBands, bSign, bSort, bBuild, bLocate, bDecomp, bOQuery, bandOf,
      Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have k₂' : ∀ r, 140000 ≤ r → r < 160000 → c₂.nreg r = c₁.nreg r := fun r h1 h2 =>
    kq₂ r by_grind ztu
  have hE₂ : ShEnv P W H C z σ c₂ := by
    refine ShEnv.of_agree E (fun r hr hra => ?_) ztts by_omega
    · have h14 : 140000 ≤ r ∧ r < 160000 := by unfold envR K1 ALLOC at hr; unfold ALLOC at hra; omega
      rw [k₂' r h14.1 h14.2, kq₁ r (by unfold envR K1 ALLOC at hr; omega) by_omega]
    grind
  have hSC : ∀ x ∈ S, InC C x := fun x hx => block_inC hw1 hp6 hp hx
  have htr := query_transfer E.hσ hrel (by rw [hCs]) hSC
  rw [hCs] at hpost
  zue
  have k1₂ := hE₂.k1
  -- the candidate
  have wr_c0 : wr (fun r => Bqh r || r == 140220) cand0 = true := by_decide
  have r50 : c₂.nreg 140250 = p₀ := by
    rw [k₂' _ by_norm_num by_norm_num, kq₁ _ by_decide by_omega, h50]
  have r56 : c₂.nreg 140256 = x0 := by
    rw [k₂' _ by_norm_num by_norm_num, kq₁ _ by_decide by_omega, h56]
  have r57 : c₂.nreg 140257 = dir := by
    rw [k₂' _ by_norm_num by_norm_num, kq₁ _ by_decide by_omega, h57]
  have r58 : c₂.nreg 140258 = w := by
    rw [k₂' _ by_norm_num by_norm_num, kq₁ _ by_decide by_omega, h58]
  have r36 : c₂.nreg 140236 = h := by
    rw [k₂' _ by_norm_num by_norm_num, kq₁ _ by_decide by_omega]
  obtain ⟨c₃, k₃, e₃, hk₃, ca, fc⟩ : ∃ c₃ k₃, Exec P W (.ifLtN 120005 K1 cand0
      ztprw) c₂ c₃ k₃ ∧ k₃ ≤ 50 ∧ CandAt P C c₃ 140220 S z σ ∧
      FrameB (fun r => Bqh r || r == 140220) c₂ c₃ := by
    by_cases t1 : c₂.nreg 120005 < c₂.nreg K1
    · have hN := htr.2 (hpost.2 (by rw [k1₂] at t1; show c₂.nreg 120005 ≠ 1; omega))
      zucxn
      exact ⟨c₃, _, .ifLtN_true t1 ex, by_omega, ca, exec_frameB ex wr_c0⟩
    by_cases t2 : c₂.nreg K1 < c₂.nreg 120005
    · have hN := htr.2 (hpost.2 (by rw [k1₂] at t2; show c₂.nreg 120005 ≠ 1; omega))
      zucxn
      exact ⟨c₃, _, .ifLtN_false t1 ztspr, by_omega, ca, exec_frameB ex wr_c0⟩
    have hf : c₂.nreg 120005 = 1 := by_omega
    obtain ⟨t', hF', he'n, hXe⟩ := hpost.1 hf
    obtain ⟨hFz, hXz⟩ := htr.1 t' hF'
    set X := rayPt ztwyf σ t' with hX
    have hXS : X ∈ S := by rw [← hXz]; exact hFz.2.1
    have hXy : X.2 = z.2 := by rw [← hXz, rayPt_snd]
    set e' := rd c₂ bOQuery 6 with he'def
    have hout := k1_hit hD hQs hblk hw1 by_omega hp6 hp hdir hXS hXe
      (by zvmxg; exact he'n) (by zvmxg; exact hhi) (by rw [hXy, hzh])
    zvmxg at hout
    obtain ⟨c₃, k, ex, hk, ca, f⟩ := qHit_exec (P := P) (C := C) (S := S) (X := X) c₂ w₂ k1₂ r50 r56
      r57 r58 rfl r36 hdir by_omega hW2
      (by have : rd c₂ bOQuery 6 = c₂.nreg 120006 := rfl; omega) by_omega he'n hhi hFz hXy hout
    exact ⟨c₃, _, .ifLtN_false t1 ztjdk, by_omega, ca,
      FrameB.wk f by_grind⟩
  zubj
  have hE₃ := hE₂.frame fc fun r hr => by
    unfold envR at hr
    simp only [Bqh, Bko, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
      beq_eq_false_iff_ne] at hr ⊢
    omega
  have hB₃ := hB.keep fun j hj => by
    rw [fc.1 _ ztljn, k₂' _ by_omega by_omega,
      kq₁ _ by_omega by_omega]
  obtain ⟨c₄, k₄, e₄, hk₄, cb, fm⟩ := mrg_exec c₃ w₃ hE₃ hB₃ ca
  have hE₄ := hE₃.frame fm Bmrg_env
  refine ⟨c₄, _, .ifLtN_false t0 ztwri, by_omega, cb, ?_, ?_, hE₄⟩
  · -- the frame
    have F1 := frame_ob f₁ (fun r hr => by
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₁
    have F2 : Frame oracleBands c₁ c₂ k₂ :=
      Frame.mono ⟨Fr, Frr, Fm, Frm, Fo, Fa1, Fa2⟩ (by
        decide) le_rfl
    have F3 := frame_ob fc (fun r hr => by
      simp only [Bqh, Bko, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₃
    have F4 := frame_ob fm (fun r hr => by
      simp only [Bmrg, Bk, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hr
      unfold bandOf ALLOC; omega) k₄
    have := ((F1.trans F2).trans F3).trans F4
    simp only [Finset.union_self] at this
    exact this.mono le_rfl by_omega
  · intro r h1 h2 hr
    simp only [Wk1, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at hr
    rw [fm.1 r (by zuons; omega), fc.1 r ztljn,
      k₂' r h1 h2, kq₁ r by_omega by_omega]
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Chazelle.Chain (sideInArc)
namespace ShootCut
variable {M : Model} {Q : Polygon}

/-- **The unwrapped ends of a piece** of a path lie within the range of the path. -/
theorem KPath.mem {n : ℝ} : ∀ {V : ℝ} {ps : List Pc} {V' : ℝ}, KPath M Q n V ps V' →
    ∀ pc ∈ ps, ∃ U U₁ : ℝ, V ≤ U ∧ U < U₁ ∧ U₁ ≤ V' ∧ (∃ i : ℤ, U = M.key Q pc.s + i * n) ∧
      ∃ j : ℤ, U₁ = M.key Q pc.e + j * n
  | _, [], _, _, _, h => by_simp_all
  | V, q :: qs, V', ⟨h1, V₁, h2, h3, h4⟩, pc, hpc => by
    zucyl
    · exact ⟨V, V₁, le_rfl, h2, h4.le, h1, h3⟩
    · obtain ⟨U, U₁, a1, a2, a3, a4, a5⟩ := KPath.mem h4 pc hpc
      grind
variable {P : Polygon} {C : Chain} {m₀ : ℕ → ℕ} {h γ : ℕ} {s e : WPos} {ps : List Pc}
/-- **A kind-1 piece is no longer than the weight of the subarc.** -/
theorem kind1_pw_le
 (arc : ArcOK C zta s e ps)
    (hs : 0 ≤ (chainModel C).key zta s ∧
      (chainModel C).key zta s < ((2 * C.m + 7 : ℕ) : ℝ))
    (he : 0 ≤ (chainModel C).key zta e ∧
      (chainModel C).key zta e < ((2 * C.m + 7 : ℕ) : ℝ))
    {pc : Pc} (hpc : pc ∈ ps) (hok : PcOK P C m₀ h γ pc) (hk : pc.kind = 1) :
    pc.pw ≤ (chainModel C).arcWt ztwlj
      ztwli := by
  obtain ⟨g, b, -, -, -, -, hpw, -, -, -, hs0, he0, h6, hee, hem, -, -⟩ :=
    hok.2.2.2.2.2.2 hk
  zulz
  set a := (chainModel C).key zta s with ha
  set b' := (chainModel C).key zta e with hb'
  zufvt
  set T := a + len (n : ℝ) a b' with hT
  have hTA : T ≤ a + n := by have := len_le (n : ℝ) a b' hs.1 he.2; linarith
  obtain ⟨U, U₁, hAU, hUU, hUT, ⟨i, hi⟩, ⟨j, hj⟩⟩ := KPath.mem arc.kp pc hpc
  have ks : (chainModel C).key zta pc.s = (pc.s.edge : ℝ) := by
    rw [show pc.s = ztkmk by rw [← hs0]]; simp
  have ke : (chainModel C).key zta pc.e = (pc.s.edge : ℝ) + ((2 ^ g : ℕ) : ℝ) := by
    rw [show pc.e = zthnm by rw [← he0], key_hgt0, hee]; simp
  rw [ks] at hi
  rw [ke] at hj
  replace hi : U = (pc.s.edge : ℝ) + i * (n : ℝ) := hi
  replace hj : U₁ = (pc.s.edge : ℝ) + ((2 ^ g : ℕ) : ℝ) + j * (n : ℝ) := hj
  replace hAU : a ≤ U := hAU
  replace hUT : U₁ ≤ T := hUT
  set p₀ := pc.s.edge with hp₀
  have hpn : (p₀ : ℝ) + ((2 ^ g : ℕ) : ℝ) + 1 ≤ n := by
    exact_mod_cast (show p₀ + 2 ^ g + 1 ≤ n by omega)
  have hg0 : (0 : ℝ) < ((2 ^ g : ℕ) : ℝ) := by_positivity
  -- the two unwrappings agree
  have hji : ztsjr := by
    have d1 : (0 : ℝ) < ((2 ^ g : ℕ) : ℝ) + ztmzf * n := by_linarith
    have d2 : ((2 ^ g : ℕ) : ℝ) + ztmzf * n ≤ n := by_linarith
    have ec : ((j - i : ℤ) : ℝ) = (j : ℝ) - i := by_simp
    have a1 : ((j - i : ℤ) : ℝ) > -1 := by
      zuelm
    have a2 : ((j - i : ℤ) : ℝ) < 1 := by
      zuelm
    have b1 : j - i > -1 := by exact_mod_cast a1
    have b2 : j - i < 1 := by exact_mod_cast a2
    omega
  rw [hji] at hj
  -- the unwrapped start is a natural number
  have hi0 : 0 ≤ i := by
    have : (-1 : ℝ) < i := by
      zuca
      have : (i : ℝ) * n ≤ -n := by_nlinarith
      grind
    have : (-1 : ℤ) < i := by exact_mod_cast this
    omega
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, i = i' := ⟨i.toNat, (Int.toNat_of_nonneg hi0).symm⟩
  have hv : ((p₀ + i' * n : ℕ) : ℝ) = U := by rw [hi]; simp
  have hv2 : ((p₀ + i' * n : ℕ) : ℝ) + ((2 ^ g : ℕ) : ℝ) = U₁ := by_grind
  rw [hpw]
  obtain ⟨k, hk'⟩ := T_unw a b' (n : ℝ)
  refine arcWt_ge C (A := a) (T := T) hs he ztufo ⟨k, hk'⟩ hTA
    (v := p₀ + i' * n) (L := 2 ^ g) ?_ ?_ by_grind ?_
  · zuhkc
  · zuhkc
  grind

/-- **A kind-1 piece of a subarc of weight `≤ γ`** has at most `γ` edges. -/
theorem kind1_pw_le_γ
 (arc : ArcOK C zta s e ps)
    (hsP : ProperPos ztc zta P.n s) (heP : ProperPos ztc zta P.n e)
    (hs1 : s.edge < 2 * C.m + 7) (he1 : e.edge < 2 * C.m + 7)
    (hwt : (chainModel C).arcWt ztwlj
      ztwli ≤ γ)
    {pc : Pc} (hpc : pc ∈ ps) (hok : PcOK P C m₀ h γ pc) (hk : pc.kind = 1) : pc.pw ≤ γ :=
  le_trans (kind1_pw_le arc zttqx zttqw hpc hok hk) hwt

/-- **The cost of a query** on a kind-1 piece: granularity `gg ≤ cutGran γ`, `M ≤ γ` edges. -/
theorem query_cost_le {κ gg M γ : ℕ} (hg : gg ≤ cutGran γ) (hM : M ≤ γ) :
    ⌈(κ : ℝ) * ((gg : ℝ) ^ ztby * ztded ^ ztcd + 1)⌉₊ ≤
      κ * ztbamk := by
  have e : (gg : ℝ) ^ ztby * ztded ^ ztcd =
      ztydf ^ ztby := by
    rw [Real.mul_rpow by_positivity by_positivity, ← Real.rpow_natCast,
      ← Real.rpow_mul by_positivity]
    norm_num
  have h1 : ztydf ^ ztby ≤
      ztxmp ^ ztby := by
    apply Real.rpow_le_rpow by_positivity _ by_norm_num
    push_cast
    have a : (gg : ℝ) ≤ cutGran γ := by_simp_all
    have b0 : (M : ℝ) ≤ γ := by_simp_all
    have b : (M : ℝ) + 1 ≤ γ + 1 := by_linarith
    have b2 : ztded ^ 2 ≤ ((γ : ℝ) + 1) ^ 2 := by
      apply pow_le_pow_left₀ by_positivity b
    exact mul_le_mul a b2 by_positivity by_positivity
  have h2 : ztxmp ^ ztby ≤
      (rpowCeil ztwku ztby : ℝ) := Nat.le_ceil _
  zui
  apply Nat.ceil_le.2
  push_cast
  exact mul_le_mul_of_nonneg_left by_grind by_positivity

/-- **The query facts of a kind-1 piece**, read from the grade table in any memory `m'` agreeing
with `m` below the bound `A` of the table: its Lemma 3.6 structure, the chain of the structure
(whose point set is the piece), its granularity and its length. -/
theorem kind1_query {O : OracleIface} {P : Polygon} {C : Chain} {m m' : ℕ → ℕ} {h γ A : ℕ}
    {pc : Pc} (hok : PcOK P C m h γ pc) (hk : pc.kind = 1)
    (hR : Robust A m fun m'' => GradeRaw O P m'' h A) (hm' : ∀ a, a < A → m' a = m a) :
    pc.entry + 2 < A ∧ O.At P m' ztiln ∧
      (∃ Hs Cα, ChainDescAt m' (m' ztiln) zta Hs Cα ∧
        Cα.set = (chainModel C).arcSet (pc.s.edge : ℝ) ((pc.s.edge + pc.pw : ℕ) : ℝ)) ∧
      m' (m' (pc.entry + 2) + 2) ≤ cutGran γ ∧ m' (m' ztiln + 2) = pc.pw := by
  obtain ⟨hwf', Hs', Cα', N', hC', -, -, hset, -, -⟩ := kind1_facts hok hk hR hm' (le_refl A)
  obtain ⟨-, -, -, -, -, -, h1⟩ := hok
  zukm

  have hΛ : ztuul := by
    have := (grade_low hR).1
    grind
  obtain ⟨Hs, Cα, N, hC, -, -, -, -, -, hmC, -, -, hAt, hS0, -, hS2⟩ := hR'.holds.2.2.2 g b hΛ hb
  obtain ⟨h2, hr, hlt⟩ := grade_entry hR hgΛ hb
  have hent : ztxth := by
    zubtc

  rw [hent] at hC hAt hS0 hS2
  zuegz
  refine ⟨by_omega, hAt, ⟨Hs', Cα', by_grind, ?_⟩,
    by omega, ?_⟩
  · rw [← hset, show pc.s = ztkmk by zunwt, show pc.e = zthnm by zuota,
      key_hgt0, key_hgt0, hee, hpw]
  · rw [hS0, hC.2.2.2.1, hlen, hpw]
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
namespace ShootCut
variable (C : Chain)

/-- **All walk abscissae lie in `[-R, R]`.** -/
theorem walk_x_bounds {q : ℕ} (hq : q < 2 * C.m + 7) :
    -C.radius ≤ ((chainModel C).W.vtx q).1 ∧ ((chainModel C).W.vtx q).1 ≤ C.radius := by
  zubo
  have ht := abs_lt.1 (abs_top_lt C)
  zuknh
  · show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx q).1 ∧
      ((C.sideWalk C.sideBeta).vtx q).1 ≤ C.radius
    interval_cases q
    · rw [C.sideWalk_vtx_zero]; unfold Chazelle.Chain.slitTop
      grind
    · zugbq
    · zukov
    · zugbr
    · zukos
    · rw [C.sideWalk_vtx_five]; unfold Chazelle.Chain.slitTop
      grind
  · zubpf
    show -C.radius ≤ ((C.sideWalk C.sideBeta).vtx ztcy).1 ∧
      ((C.sideWalk C.sideBeta).vtx ztcy).1 ≤ C.radius
    zudth
    zuljn
    have := abs_lt.1 hb.1
    unfold Chazelle.Chain.sideTour
    grind

/-- **An inner point of a chain model** lies strictly inside the height range of the box and
inside its abscissa range. -/
theorem innerPt_bounds {z : Point} (h : (chainModel C).InnerPt z) :
    |z.2| < C.radius ∧ |z.1| ≤ C.radius := by
  obtain ⟨⟨p, q, hp, hq, h1, h2⟩, ⟨p', q', hp', hq', h3, h4⟩⟩ := h
  zubgg
  zvmxq at hp hq hp' hq'
  have a := walk_y_bounds C hp
  have b := walk_y_bounds C hq
  have a' := walk_x_bounds C hp'
  have b' := walk_x_bounds C hq'
  grind

/-- **A position inside the slit**: a position of the walk strictly inside the box that is
neither on a tour edge (edges `6 … 2m + 5`) nor a vertex lies above the top of the chain. -/
theorem walk_above {Q : Polygon} {N e hc : ℕ} (hp : ProperPos ztc Q N ztev)
    (hen : e < 2 * C.m + 7)
    (hx : |((chainModel C).pos Q ⟨e, hc⟩).1| < C.radius)
    (hy : |((chainModel C).pos Q ⟨e, hc⟩).2| < C.radius)
    (hno : ¬ (6 ≤ e ∧ (e < 2 * C.m + 6 ∨ (chainModel C).param Q ztev = 0))) :
    C.top.2 < ((chainModel C).pos Q ztev).2 := by
  zubgg
  zubo
  zubnz
  have t0 := hp.1
  have t1 := hp.2.1
  have hpos : (chainModel C).pos Q ztev = lerp ztiey
      ((chainModel C).W.vtx (ztda % ztz)) ((chainModel C).param Q ztev) := by
    zvocr; rfl
  zvnbl at hx hy ⊢
  obtain ⟨t, htd⟩ : ∃ t, (chainModel C).param Q ⟨e, hc⟩ = t := zths
  rw [htd] at hx hy t0 t1 hno ⊢
  simp only [lerp_fst, lerp_snd] at hx hy ⊢
  zvncj at hx hy
  have V : ∀ q, (chainModel C).W.vtx q = (C.sideWalk C.sideBeta).vtx q := fun _ => rfl
  have V6 : ztidg := SweepPrim.walk_vtx_six C
  rcases (show e ≤ 5 ∨ 6 ≤ e by omega) with h5 | h6
  · zvmyc at hx hy ⊢
    interval_cases e
    · simp only [V, C.sideWalk_vtx_zero, C.sideWalk_vtx_one, Chazelle.Chain.slitTop] at hy
      simp_all
    · simp only [V, C.sideWalk_vtx_one, C.sideWalk_vtx_two] at hx
      simp_all
    · simp only [V, C.sideWalk_vtx_two, C.sideWalk_vtx_three] at hy
      simp_all
    · simp only [V, C.sideWalk_vtx_three, C.sideWalk_vtx_four] at hx
      simp_all
    · simp only [V, C.sideWalk_vtx_four, C.sideWalk_vtx_five, Chazelle.Chain.slitTop] at hy
      simp_all
    · rw [show (5 : ℕ) + 1 = 6 from rfl, V6, V, C.sideWalk_vtx_five]
      unfold Chazelle.Chain.slitTop
      zubvt
      nlinarith [mul_pos ztcqc (show 0 < C.radius - C.top.2 by linarith)]
  · have he : ztblf := by
      omega
    have ht0 : ztmwx := fun h => hno ⟨h6, Or.inr h⟩
    have tp : ztfkp := lt_of_le_of_ne t0 ztqbb
    zulsz
    rw [show 2 * C.m + 6 + 1 = 2 * C.m + 7 by omega, Nat.mod_self, SweepPrim.walk_vtx_last, V,
      C.sideWalk_vtx_zero]
    unfold Chazelle.Chain.slitTop
    simp_all
end ShootCut
end
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def oInit : Stmt := .seq ztjph
  (ifEq 140008 K1 (.instr ztsos) (.instr ztsor))

/-- A symbolic origin: its record and its query origin. -/
def oSym : Stmt := .seq (block [.constN 140230 1, .copyN 140231 140005, .copyN 140232 140006,
    .copyN 140233 140007, .constN 140234 1, .constN 140235 0, .constN 140237 1,
    .copyN 140238 140005, .copyN 140239 140006, .copyN 140240 140007])
  ztfmd

/-- No query. -/
def qk0 : Stmt := .instr (.constN 140237 0)

/-- The box query origin at the height of the origin. -/
def oBox : Stmt := block [.constN 140237 1, .constN 140238 2, .copyN 140239 140236]

/-- A walk origin on a side of the box or in the slit. -/
def oSide : Stmt := .ifLtN 140230 K1 (.ifLtN 140241 K1 qk0 oBox)
  (.ifLtN K1 140230 (.ifLtN 140241 K1 oBox qk0) qk0)

/-- The query decision for a walk origin. -/
def oFix : Stmt := .ifLtN 140234 K1 qk0 (.ifLtN K1 140234 qk0 (ifEq 140237 K1 .skip oSide))

/-- A walk origin. -/
def oWalk : Stmt := .seq (ptLoad 140006 140007 140230) oFix

/-- **The origin of the ray.** -/
def orig : Stmt := .seq oInit (.ifLtN K1 140005 oWalk oSym)

/-- The registers written by `orig`. -/
def Borg (r : ℕ) : Bool := Bld 140230 r || r == 140401 || r == 140403 || r == 140241
theorem wr_orig : wr Borg orig = true := by_decide

/-! ## The query decision -/

/-- **The query decision** for the kind-1 pieces. -/
structure OrgOK (P : Polygon) (C : Chain) (z : Point) (σ : ℝ) (c : Config) : Prop where
  qk : c.nreg 140237 ≤ 1
  q0 : c.nreg 140237 = 0 → ∀ S : Set Point, ztgnq → NoHit S z σ
  q1 : c.nreg 140237 = 1 → c.nreg 140234 = 1 ∧
    ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
theorem OrgOK.keep {c c' : Config} (h : OrgOK P C z σ c)
    (hr : ∀ r, 140234 ≤ r → r < 140241 → c'.nreg r = c.nreg r) : OrgOK P C z σ c' := by
  have e37 := hr 140237 by_norm_num by_norm_num
  refine ⟨by rw [e37]; exact h.qk, fun h0 => h.q0 by_omega, fun h1 => ?_⟩
  obtain ⟨a, o, ho, hl, hq⟩ := h.q1 by_omega
  exact ⟨by_simp_all, o,
    qOriginIn_of_eq ho by_grind, hl, hq⟩
variable {c : Config}
theorem orgOK_zero (h : c.nreg 140237 = 0)
    (hN : ∀ S : Set Point, ztgnq → NoHit S z σ) : OrgOK P C z σ c :=
  ⟨by_omega, by_simp_all, by_simp_all⟩
theorem orgOK_one (h : c.nreg 140237 = 1) (h34 : c.nreg 140234 = 1)
    (hq : ∃ o, QOriginIn c 140238 o ∧ o.Lt P.n ∧ QRel P C σ z o) : OrgOK P C z σ c :=
  ⟨by zvmwc, by_simp_all, by_simp_all⟩
theorem dirOf_cases (v : ℕ) : dirOf v = 1 ∨ dirOf v = -1 := by
  zubqi

/-! ## The pieces -/
theorem oInit_exec (c : Config) (hw : WordsBounded W c) (hMD : c.nreg 140000 + 1 ≤ W) :
    ∃ c' k, Exec P W oInit c c' k ∧ k ≤ 10 ∧ c'.nreg K1 = 1 ∧
      c'.nreg 140403 = c.nreg 140000 + 1 ∧ c'.nreg 140241 ≤ 1 ∧
      (c'.nreg 140241 = 1 ↔ dirOf ztghb = 1) ∧
      (∀ r, r ≠ 140401 → r ≠ 140403 → r ≠ 140241 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem := by
  obtain ⟨c₁, k₁, e₁, hk₁, a1, a3, r₁, m₁⟩ : ∃ c₁ k₁, Exec P W
      ztjph c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 140401 = 1 ∧
      c₁.nreg 140403 = c.nreg 140000 + 1 ∧
      (∀ r, r ≠ 140401 → r ≠ 140403 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem := by
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; omega) | skip
    simp_all
  zud
  have b08 : c₁.nreg 140008 = c.nreg 140008 := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v41, r₂, m₂⟩ := ifEq_exec (P := P) (W := W) (a := 140008) (b := K1)
    (T := .instr ztsos) (E := .instr ztsor) c₁ (K := 1)
    (R := fun c' => (c'.nreg 140241 = if c.nreg 140008 = 1 then 1 else 0) ∧
      (∀ r, r ≠ 140241 → c'.nreg r = c₁.nreg r) ∧ c'.nmem = c₁.nmem)
    (fun h => ⟨_, _, Exec.constN w₁ 140241 1 by_omega, le_rfl,
      by zuocj; rw [ite_eq_left (by rw [← b08, h]; exact a1)],
      fun r hr => by_simp_all, rfl⟩)
    (fun h => by
      have hne : c.nreg 140008 ≠ 1 := fun h' => h (by rw [b08, h']; tauto)
      exact ⟨_, _, Exec.constN w₁ 140241 0 ztbg, le_rfl,
        by simp_all,
        by simp_all, rfl⟩)
  refine ⟨c₂, k₁ + k₂, by_tauto, by_omega, ?_, ?_, ?_, ?_,
    by simp_all, by_simp_all⟩
  · show c₂.nreg 140401 = 1; simp_all
  · simp_all
  · grind
  · rw [v41]; by_cases hd : c.nreg 140008 = 1 <;> simp [dirOf, hd] <;> norm_num
theorem oSym_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (h1 : c.nreg K1 = 1)
    {s : SymPt}
    (hs : SymPtIn c 140005 s) :
    ∃ c' k, Exec P W oSym c c' k ∧ k ≤ 20 ∧ c'.nreg 140230 = 1 ∧ SymPtIn c' 140231 s ∧
      c'.nreg 140234 = 1 ∧ c'.nreg 140235 = 0 ∧ c'.nreg 140236 = hIdx s ∧
      c'.nreg 140237 = 1 ∧ SymPtIn c' 140238 s ∧
      (∀ r, (r < 140230 ∨ 140241 ≤ r) → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem := by
  zubfu
  obtain ⟨c₁, k₁, e₁, hk₁, a30, a31, a32, a33, a34, a35, a37, a38, a39, a40, r₁, m₁⟩ :
      ∃ c₁ k₁, Exec P W (block [.constN 140230 1, .copyN 140231 140005, .copyN 140232 140006,
        .copyN 140233 140007, .constN 140234 1, .constN 140235 0, .constN 140237 1,
        .copyN 140238 140005, .copyN 140239 140006, .copyN 140240 140007]) c c₁ k₁ ∧
      k₁ = 10 ∧ c₁.nreg 140230 = 1 ∧ c₁.nreg 140231 = c.nreg 140005 ∧
      c₁.nreg 140232 = c.nreg 140006 ∧ c₁.nreg 140233 = c.nreg 140007 ∧
      c₁.nreg 140234 = 1 ∧ c₁.nreg 140235 = 0 ∧ c₁.nreg 140237 = 1 ∧
      c₁.nreg 140238 = c.nreg 140005 ∧ c₁.nreg 140239 = c.nreg 140006 ∧
      c₁.nreg 140240 = c.nreg 140007 ∧
      (∀ r, (r < 140230 ∨ 140236 = r ∨ 140241 ≤ r) → c₁.nreg r = c.nreg r) ∧
      c₁.nmem = c.nmem := by
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      by config_simp, by config_simp, by config_simp, by config_simp, by config_simp,
      fun r hr => ?_, rfl⟩
    zufcb
  zud
  have b1 : c₁.nreg 140401 = 1 := by_simp_all
  have b05 : c₁.nreg 140005 = c.nreg 140005 := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, v36, r₂, m₂⟩ : ∃ c₂ k₂, Exec P W
      ztfmd c₁ c₂ k₂ ∧
      k₂ ≤ 3 ∧ c₂.nreg 140236 = hIdx s ∧ (∀ r, r ≠ 140236 → c₂.nreg r = c₁.nreg r) ∧
      c₂.nmem = c₁.nmem := by
    cases s with
    | vtx i =>
      obtain ⟨i0, i1⟩ := hs
      refine ⟨_, _, .ifLtN_true (by show c₁.nreg 140005 < c₁.nreg 140401; omega)
        zteeh, by_norm_num, ?_, by_simp_all, rfl⟩
      zunwu; rw [r₁ _ by_omega, i1]
    | onEdge e h =>
      obtain ⟨i0, i1, i2⟩ := hs
      refine ⟨_, _, .ifLtN_false (by show ¬ c₁.nreg 140005 < c₁.nreg 140401; omega)
        zteeh, by_norm_num, ?_, by_simp_all, rfl⟩
      zunwu; rw [r₁ _ by_omega, i2]
  zumau
  refine ⟨c₂, k₁ + k₂, by unfold oSym; exact .seq e₁ e₂, by_omega, by_simp_all,
    NFLoc.symPtIn_copy hs by_simp_all by_simp_all
      by_simp_all,
    by simp_all, by_simp_all, v36, by_simp_all,
    NFLoc.symPtIn_copy hs by_simp_all by_simp_all
      by_simp_all,
    fun r hr => by_grind, by_simp_all⟩
theorem wr_oFix : wr (fun r => r == 140237 || r == 140238 || r == 140239) oFix = true := by
  decide
theorem qk0_exec (c : Config) (hw : WordsBounded W c) :
    ∃ c' k, Exec P W qk0 c c' k ∧ k ≤ 1 ∧ c'.nreg 140237 = 0 := by
  exact ⟨_, _, Exec.constN hw 140237 0 ztbg, le_rfl, by_simp⟩
theorem oBox_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) :
    ∃ c' k, Exec P W oBox c c' k ∧ k ≤ 3 ∧ c'.nreg 140237 = 1 ∧ c'.nreg 140238 = 2 ∧
      c'.nreg 140239 = c.nreg 140236 ∧ c'.nreg 140234 = c.nreg 140234 := by
  unfold oBox
  exec_block
  all_goals first | omega | skip
  simp

/-- **The query decision for a walk origin**, from its point record. -/
theorem oFix_exec (c : Config) (hw : WordsBounded W c) (hW : 2 ≤ W) (h1 : c.nreg K1 = 1)
    (hσ : σ = 1 ∨ σ = -1) (hsig : c.nreg 140241 ≤ 1 ∧ ztmfs)
    (hrec : PtRecB P c 140230 z C.radius)
    (hsl : c.nreg 140237 ≠ 1 → |z.1| < C.radius → |z.2| < C.radius → C.top.2 < z.2) :
    ∃ c' k, Exec P W oFix c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' ∧
      FrameB (fun r => r == 140237 || r == 140238 || r == 140239) c c' := by
  zubfu
  zubo
  obtain ⟨ax, hy, hf⟩ := hrec
  suffices H : ∃ c' k, Exec P W oFix c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' by
    obtain ⟨c', k, ex, hk, ok⟩ := H
    exact ⟨c', k, ex, hk, ok, exec_frameB ex wr_oFix⟩
  -- no query
  have noq : (∀ S : Set Point, ztgnq → NoHit S z σ) →
      ∀ {s : Stmt}, (∀ {c' k}, Exec P W qk0 c c' k → ∃ k', Exec P W s c c' k' ∧ k' ≤ k + 5) →
      ∃ c' k, Exec P W s c c' k ∧ k ≤ 30 ∧ OrgOK P C z σ c' := fun hN s hs => by
    obtain ⟨c', k, ex, hk, v⟩ := qk0_exec (P := P) c hw
    obtain ⟨k', ex', hk'⟩ := hs ex
    exact ⟨c', k', ex', by_omega, orgOK_zero v hN⟩
  unfold oFix
  -- the height of the origin
  rcases hy with ⟨k0, hy0⟩ | ⟨k2, hy2⟩ | ⟨k1, hyR, h35, h36, hyv⟩
  · have hN : ztbaf := fun S hS =>
      noHit_ext by_grind hS
    have u1 : c.nreg 140234 < c.nreg 140401 := by_grind
    exact noq hN fun ex => ⟨_, .ifLtN_true u1 ex, by_omega⟩
  · have hN : ztbaf := fun S hS =>
      noHit_ext by_grind hS
    have u1 : ¬ c.nreg 140234 < c.nreg 140401 := by_grind
    have u2 : c.nreg 140401 < c.nreg 140234 := by_grind
    exact noq hN fun ex => ⟨_, .ifLtN_false u1 (.ifLtN_true u2 ex), by_omega⟩
  have t1 : ¬ c.nreg 140234 < c.nreg K1 := by_grind
  have t2 : ¬ c.nreg K1 < c.nreg 140234 := by_grind
  obtain ⟨c', k, ex, hk, ok⟩ : ∃ c' k, Exec P W (ifEq 140237 K1 .skip oSide) c c' k ∧ k ≤ 20 + 4 ∧
      OrgOK P C z σ c' := by
    refine ifEq_exec c ztrqj ztrqj
    · -- a symbolic point
      have hq' : ztunn := by_omega
      obtain ⟨s, hs, hl, hv⟩ := hf hq'
      exact ⟨c, 0, .skip hw, by_omega, orgOK_one hq' k1 ⟨.sym s, hs, hl, hv⟩⟩
    · have hq' : c.nreg 140237 ≠ 1 := by_omega
      unfold oSide
      obtain ⟨hRx, ak⟩ := ax
      rcases ak with ⟨a0, hx0⟩ | ⟨a2, hx2⟩ | ⟨a1, hx1, -⟩
      · have t : c.nreg 140230 < c.nreg K1 := by_omega
        zujtw
        · have tb : ztrhh := by
            grind
          zucdq
          refine ⟨c', _, .ifLtN_true t ztspd, by_omega,
            orgOK_one v37 by_omega ztivy⟩
          show z = zthqd
          grind
        · zulli
          have tb : ztseo := by
            grind
          have hN : ztbaf := fun S hS =>
            noHit_ahead_side hσ by_grind hS
          zubha
          exact ⟨c', _, .ifLtN_true t ztsps, by_omega, orgOK_zero v hN⟩
      · zukis
        have t' : c.nreg K1 < c.nreg 140230 := by_omega
        zujtw
        · have tb : ztrhh := by
            grind
          have hN : ztbaf := fun S hS =>
            noHit_ahead_side hσ by_grind hS
          zubha
          exact ⟨c', _, .ifLtN_false t (.ifLtN_true t' ztspd), by_omega,
            orgOK_zero v hN⟩
        · zulli
          have tb : ztseo := by
            grind
          zucdq
          refine ⟨c', _, .ifLtN_false t (.ifLtN_true t' ztsps), by_omega,
            orgOK_one v37 by_omega ztivy⟩
          show z = zthqd
          grind
      · -- inside the slit
        zukis
        have t' : ¬ c.nreg K1 < c.nreg 140230 := by_omega
        have hab := hsl hq' hx1 hyR
        have hN : ztbaf := fun S hS =>
          noHit_above hab hS
        zubha
        exact ⟨c', _, .ifLtN_false t (.ifLtN_false t' ex), by_omega, orgOK_zero v hN⟩
  exact ⟨c', _, .ifLtN_false t1 ztjdk, by_omega, ok⟩

/-! ## The origin -/

/-- **The origin of the ray**: the shooting environment and the query decision. -/
theorem orig_exec (c : Config) (hw : WordsBounded W c) (hG : GoodEnv P) (hW : hostWords P.n ≤ W)
    (hD : ChainDescAt c.nmem zthuk zta H C)
    (hwf : ChainWF P ztm c.nmem zthuk)
    (hreg : ∀ H', HostAt c.nmem (c.nmem zthuk) H' → HostRegular P.n H')
    {o : Origin} (hoIn : OriginIn c 140005 o) (hoLt : o.Lt P.n ztc)
    (hoK : ztbnv ∨ ((chainModel C).InnerPt ztwqq ∧
      ∀ x, o = .walk x → ProperPos ztc zta P.n x))
    (hroom : c.nreg ALLOC + 15800 ≤ W) (hMD : c.nreg 140000 + 1 ≤ W) :
    ∃ c' k, Exec P W orig c c' k ∧ k ≤ 16000 ∧
      ShEnv P W H C ztwqq ztbaho c' ∧
      OrgOK P C ztwqq ztbaho c' ∧
      FrameB Borg c c' ∧ c'.nreg 140403 = c.nreg 140000 + 1 := by
  zudoc
  zubo
  zucmi
  set z := o.eval _ _ with hz
  zujnd
  zuizy
  obtain ⟨c₁, k₁, e₁, hk₁, b1, b403, b41, b41', r₁, m₁⟩ := oInit_exec (P := P) c hw hMD
  zud
  have k₁' : ∀ r, 140000 ≤ r → r < 140010 → c₁.nreg r = c.nreg r := by_grind
  have bA : ztdc := r₁ _ by_decide by_decide by_decide
  have L : LdEnv P W H C c₁ := ⟨hG, hW, by_simp_all,
    by simp_all, by_simp_all⟩
  have ex₀ : ∀ {c' k}, Exec P W _ c₁ c' k →
      Exec P W orig c c' _ := fun ex => by unfold orig; exact .seq e₁ ex
  cases o with
  | sym s =>
    have hs : SymPtIn c 140005 s := hoIn
    have hs₁ : SymPtIn c₁ 140005 s := symPtIn_of_eq hs by_grind
    have hin : (chainModel C).InnerPt z := by
      simp_all
    have hb := innerPt_bounds C hin
    have t : ¬ c₁.nreg K1 < c₁.nreg 140005 := by
      zupbj
      cases s with
      | vtx i => zupbk; omega
      | onEdge e h => zupbk; omega
    obtain ⟨c₂, k₂, e₂, hk₂, a30, a31, a34, a35, a36, a37, a38, r₂, m₂⟩ :=
      oSym_exec c₁ w₁ hW2 b1 hs₁
    have ex := ex₀ ztnaf
    have hl : s.Lt P.n := hoLt
    have hzs : z = s.eval _ := rfl
    have k2 : ∀ r, 140241 ≤ r → c₂.nreg r = c₁.nreg r := by_grind
    refine ⟨c₂, _, ex, by_omega, ⟨hG, hW, ?_, ?_, ?_, ?_, ⟨hR, by_grind⟩, Or.inr (Or.inr ⟨a34, hb.1, a35, by rw [a36]; exact hIdx_lt hl,
      by rw [a36, hzs]; exact hIdx_snd _ s⟩), ?_, hσ⟩,
      orgOK_one a37 a34 ⟨.sym s, a38, hl, by_rfl⟩,
      exec_frameB ex wr_orig, by_grind⟩
    · grind
    · rw [m₂, r₂ ALLOC ztbuo, k2 140403 by_norm_num]; grind
    · grind
    · show c₂.nreg 140401 = 1; rw [k2 _ by_norm_num]; exact b1
    · grind
  | walk x =>
    obtain ⟨o5, o6, o7⟩ : c.nreg 140005 = 2 ∧ c.nreg _ = x.edge ∧
        c.nreg _ = x.hgt := hoIn
    have t : c₁.nreg K1 < c₁.nreg 140005 := by_grind
    have q6 : c₁.nreg 140006 = x.edge := by_grind
    have q7 : c₁.nreg 140007 = x.hgt := by_grind
    have hxe : ztjau := hoLt.1
    have hxP : ProperPos ztc zta P.n x := by
      rcases hoK with ⟨p, hp⟩ | ⟨-, h⟩
      · cases hp
        exact ztdjf
      grind
    have hxy : x.hgt = 0 ∨ |((chainModel C).pos zta x).2| < C.radius := by
      rcases hoK with ⟨p, hp⟩ | ⟨h, -⟩
      · grind
      · exact Or.inr (innerPt_bounds C h).1
    have hzx : z = (chainModel C).pos _ x := rfl
    obtain ⟨c₂, k₂, e₂, hk₂, rec₂, f₂, fl₂⟩ := ptLoad_exec'
      (e := 140006) (h := 140007) (B := 140230) c₁ w₁ L by_norm_num by_norm_num by_norm_num
      by_omega ztlil ztlil
      by_omega
    rw [q6, q7, ← hzx] at rec₂
    rw [q6, q7] at fl₂
    have kb : ∀ r, Bld 140230 r = false → c₂.nreg r = c₁.nreg r := f₂.1
    have g1 : ztgat := by zuokh; exact b1
    have g41 : c₂.nreg 140241 = c₁.nreg 140241 := kb _ by_decide
    have hsl : c₂.nreg _ ≠ 1 → |z.1| < C.radius → |z.2| < C.radius →
        C.top.2 < z.2 := fun hf hx hy => by
      rw [hzx] at hx hy ⊢
      refine walk_above C hxP by_omega hx hy fun h => hf (fl₂ h.1 ?_)
      grind
    obtain ⟨c₃, k₃, e₃, hk₃, ok, f₃⟩ := oFix_exec c₂
      e₂.wb_right hW2 g1 hσ by_grind rec₂ hsl
    have ex := ex₀ (.ifLtN_true t ztcr)
    have k3 : ∀ r, r ≠ 140237 → r ≠ 140238 → r ≠ 140239 → c₃.nreg r = c₂.nreg r :=
      fun r h1 h2 h3 => f₃.1 r by_grind
    have m₃ : ztckd := by zunyb
    have g403 : c₃.nreg 140403 = c.nreg 140000 + 1 := by
      rw [k3 _ by_norm_num by_norm_num by_norm_num, kb _ by_decide, b403]
    have gA : ztcke := by
      rw [k3 _ by_decide by_decide by_decide, kb _ by_decide, bA]
    obtain ⟨ax, hy, -⟩ := rec₂
    refine ⟨c₃, _, ex, by_omega, ⟨hG, hW, by_grind,
      by grind, by_grind, ?_, ?_, ?_, ?_, hσ⟩,
      ok, exec_frameB ex wr_orig, g403⟩
    · show c₃.nreg 140401 = 1
      rw [k3 _ by_norm_num by_norm_num by_norm_num]; exact g1
    · exact AbsRecW.copy (AbsRec.weak ax) by_grind
        by_grind
        by_grind
        by_grind
    · exact HRecS.copy hy by_grind
        by_grind
        by_grind
    · grind
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK NFLoc
@[expose] public section
def shStoreA : Stmt := block [.storeN 140100 150050, .addN 140100 140100 140103,
  .storeN 140100 150051, .addN 140100 140100 140103, .storeN 140100 150052,
  .addN 140100 140100 140103, .storeN 140100 150053, .addN 140100 140100 140103,
  .storeN 140100 150054, .addN 140100 140100 140103]

/-- The last four words of a piece. -/
def shStoreB : Stmt := block [.storeN 140100 150055,
  .addN 140100 140100 140103, .storeN 140100 150056, .addN 140100 140100 140103,
  .storeN 140100 150057, .addN 140100 140100 140103, .storeN 140100 150058,
  .addN 140100 140100 140103]

/-- The nine words of a piece. -/
def shStore : Stmt := .seq shStoreA shStoreB

/-- **The ray-shooter's `emit`**: the record of the piece, if there is room. -/
def shEmit : Stmt := .ifLtN 140100 140107 shStore .skip

/-- The doubling loop of the limit. -/
def shLimBody : Stmt := block [.addN 140109 140109 140109, .addN 140107 140107 140108]

/-- The constants of the set-up. -/
def shInitA : Stmt := block [.constN 140103 1, .constN 140108 18900, .constN 140109 1]

/-- The pointers of the set-up. -/
def shInitB : Stmt := block [.copyN 140101 ALLOC, .addN 140100 ALLOC 140103]

/-- The set-up of the records. -/
def shInit : Stmt :=
  .seq shInitA (.seq shInitB (.seq (.instr (.addN 140107 140100 140108))
    (.whileLtN 140109 150009 shLimBody)))

/-- Raise the allocator one by one to the end of the records. -/
def shFin : Stmt := .whileLtN ALLOC 140100 (.instr ztrhx)

/-! ## The records -/

/-- The records of the pieces `ps` from the list base `L + 1` on. -/
def Rec9 (mem : ℕ → ℕ) (L : ℕ) (ps : List Pc) : Prop :=
  ∀ i (hi : i < ps.length),
    mem (L + 1 + 9 * i) = (ps[i]'hi).s.edge ∧ mem (L + 1 + 9 * i + 1) = (ps[i]'hi).s.hgt ∧
    mem (L + 1 + 9 * i + 2) = (ps[i]'hi).e.edge ∧ mem (L + 1 + 9 * i + 3) = (ps[i]'hi).e.hgt ∧
    mem (L + 1 + 9 * i + 4) = (ps[i]'hi).kind ∧
    ((ps[i]'hi).kind = 1 → mem (L + 1 + 9 * i + 5) = (ps[i]'hi).entry ∧
      mem (L + 1 + 9 * i + 6) = (ps[i]'hi).x0 ∧ mem (L + 1 + 9 * i + 7) = (ps[i]'hi).dir ∧
      mem (L + 1 + 9 * i + 8) = (ps[i]'hi).pw)

/-- **The invariant of `shEmit`** (`Nmax` records fit below `LIM = A₀ + 1 + 9 Nmax`); the
registers `140000 … 140099` keep their values in `c₀`. -/
structure ShI (W A₀ Nmax : ℕ) (m₀ : ℕ → ℕ) (c₀ : Config) (ps : List Pc) (c : Config) : Prop where
  alloc : c.nreg ALLOC = A₀
  base : c.nreg 140101 = A₀
  one : c.nreg 140103 = 1
  lim : c.nreg 140107 = A₀ + 1 + 9 * Nmax
  limW : A₀ + 1 + 9 * Nmax + 9 ≤ W
  mem : ∀ a, a < A₀ → c.nmem a = m₀ a
  ptr : c.nreg 140100 = A₀ + 1 + 9 * min ps.length Nmax
  recs : Rec9 c.nmem A₀ ztwbw
  keep : ∀ r, 140000 ≤ r → r < 140100 → c.nreg r = c₀.nreg r
theorem rec9_append {mem mem' : ℕ → ℕ} {L : ℕ} {ps : List Pc} {pc : Pc}
    (hold : Rec9 mem L ps) (hsame : ∀ a, a < L + 1 + 9 * ps.length → mem' a = mem a)
    (h0 : mem' (L + 1 + 9 * ps.length) = pc.s.edge)
    (h1 : mem' (L + 1 + 9 * ps.length + 1) = pc.s.hgt)
    (h2 : mem' (L + 1 + 9 * ps.length + 2) = pc.e.edge)
    (h3 : mem' (L + 1 + 9 * ps.length + 3) = pc.e.hgt)
    (h4 : mem' (L + 1 + 9 * ps.length + 4) = pc.kind)
    (h58 : pc.kind = 1 → mem' (L + 1 + 9 * ps.length + 5) = pc.entry ∧
      mem' (L + 1 + 9 * ps.length + 6) = pc.x0 ∧ mem' (L + 1 + 9 * ps.length + 7) = pc.dir ∧
      mem' (L + 1 + 9 * ps.length + 8) = pc.pw) :
    Rec9 mem' L ztdvs := by
  zug
  zuvw
  zukng
  · zulpd
    obtain ⟨a0, a1, a2, a3, a4, a58⟩ := hold i hlt
    grind
  simp_all

/-! ## The contract of `shEmit` -/
variable {P : Polygon} {W : ℕ} (c : Config)
theorem shStoreA_exec (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W shStoreA c c' k ∧ k = 10 ∧ c'.nreg 140100 = p + 5 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem ztr = c.nreg 150051 ∧
      c'.nmem ztcao = c.nreg 150052 ∧ c'.nmem ztdhu = c.nreg 150053 ∧
      c'.nmem zthiz = c.nreg 150054 ∧ ztbiu ∧
      ztedm := by
  unfold shStoreA
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ztedx
  zulf
theorem shStoreB_exec (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 4 ≤ W) :
    ∃ c' k, Exec P W shStoreB c c' k ∧ k = 8 ∧ c'.nreg 140100 = p + 4 ∧
      c'.nmem p = c.nreg 150055 ∧ c'.nmem ztr = c.nreg 150056 ∧
      c'.nmem ztcao = c.nreg 150057 ∧ c'.nmem ztdhu = c.nreg 150058 ∧
      ztbiu ∧
      ztedm := by
  unfold shStoreB
  exec_block
  all_goals first | (config_simp; rw [h00, h03]; omega) | skip
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, fun a ha => ?_, fun x hx => ?_⟩
  zulf
theorem shStore_exec (hw : WordsBounded W c) {p : ℕ}
    (h00 : c.nreg 140100 = p) (h03 : c.nreg 140103 = 1) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W shStore c c' k ∧ k = 18 ∧ c'.nreg 140100 = p + 9 ∧
      c'.nmem p = c.nreg 150050 ∧ c'.nmem ztr = c.nreg 150051 ∧
      c'.nmem ztcao = c.nreg 150052 ∧ c'.nmem ztdhu = c.nreg 150053 ∧
      c'.nmem zthiz = c.nreg 150054 ∧ c'.nmem ztkbt = c.nreg 150055 ∧
      c'.nmem ztoec = c.nreg 150056 ∧ c'.nmem zttva = c.nreg 150057 ∧
      c'.nmem zttvb = c.nreg 150058 ∧ ztbiu ∧
      ztedm := by
  obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, qm, qr⟩ := shStoreA_exec (P := P) c hw h00 h03 hp
  obtain ⟨c₂, k₂, e₂, hk₂, u00, u5, u6, u7, u8, um, ur⟩ := shStoreB_exec (P := P) c₁ e₁.wb_right
    q00 by_simp_all by_omega
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, by rw [u00], by_simp_all,
    by simp_all, by_simp_all, by_simp_all,
    by simp_all, by_simp_all, ?_, ?_, ?_,
    fun a ha => by_grind, by_simp_all⟩
  · simp_all
  · simp_all
  simp_all

/-- **The contract of the ray-shooter's `emit`.** -/
theorem shEmit_ok {W A₀ : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config} (Pv : Pc → Prop)
    (Nmax : ℕ) : EmitOK P W shEmit A₀ Pv (ShI W A₀ Nmax m₀ c₀) 30 := by
  refine ztfwi
  · zuiaz

    exact ⟨by zuonj; exact hI.alloc, by zumyu; exact hI.base,
      by zumyu; exact hI.one, by zumyu; exact hI.lim, hI.limW,
      fun a ha => by zunke; exact hI.mem a ha, by zumyu; exact hI.ptr,
      by zunke; exact hI.recs,
      fun r h1 h2 => by rw [k r (by unfold Scr; grind)]; exact hI.keep r h1 h2⟩
  · obtain ⟨hA, hB, h1, hL, hLW, hm, hp, hrec, hkeep⟩ := hI
    zudrq
    zujtq
    · zulkn
      zukva
      zufwn

      set p := A₀ + 1 + 9 * ps.length with hpdef
      have t₀ : c.nreg 140100 < c.nreg 140107 := by_omega
      obtain ⟨c₁, k₁, e₁, hk₁, q00, q0, q1, q2, q3, q4, q5, q6, q7, q8, qm, qr⟩ :=
        shStore_exec c hw hp h1 by_omega
      have ex : Exec P W shEmit c c₁ _ := .ifLtN_true t₀ e₁
      refine ⟨c₁, _, ex, by_omega, ⟨?_, ?_, ?_, ?_, hLW,
        fun a ha => by_grind, ?_, ?_,
        fun r a b => by_grind⟩, fun r hr => ?_,
        by grind⟩
      · grind
      · grind
      · grind
      · grind
      · grind
      · zulpf
        refine rec9_append hrec by_omega ?_ ?_ ?_ ?_ ?_ ?_
        · grind
        · grind
        · grind
        · grind
        · grind
        grind
      · zumrb
        grind
    · zukdu
      zukva
      have t₀ : ¬ c.nreg 140100 < c.nreg 140107 := by_omega
      refine ⟨c, _, .ifLtN_false t₀ ztjd, by_omega, ⟨hA, hB, h1, hL, hLW, hm, ?_, ?_,
        hkeep⟩, by_omega, by_omega⟩
      · grind
      grind

/-! ## The set-up and the finish -/

/-- **The set-up of the records.** -/
theorem shInit_exec (d : Config) (hw : WordsBounded W d) {γ A₀ : ℕ}
    {m₀ : ℕ → ℕ} (hm : ∀ a, a < A₀ → d.nmem a = m₀ a) (h09 : d.nreg 150009 = γ)
    (hA : d.nreg ALLOC = A₀) (hγW : 2 * γ ≤ W)
    (hroom : A₀ + 18900 * Nat.clog 2 γ + 18910 ≤ W) :
    ∃ d' k Nmax, Exec P W shInit d d' k ∧ k ≤ 5 * Nat.clog 2 γ + 20 ∧
      ShI W A₀ Nmax m₀ d [] d' ∧ 2100 * Nat.log 2 γ + 2100 ≤ Nmax ∧
      (∀ x, ¬ ztekl → d'.nreg x = d.nreg x) ∧ d'.nmem = d.nmem ∧
      d'.rreg = d.rreg ∧ d'.rmem = d.rmem ∧ d'.output = d.output := by
  zuk
  have hW1 : A₀ + 18910 ≤ W := by_omega
  obtain ⟨da, ka, ea, hka, a03, a08, a09, ra, ma⟩ : ∃ d₁ k₁, Exec P W shInitA d d₁ k₁ ∧
      k₁ = 3 ∧ d₁.nreg 140103 = 1 ∧ d₁.nreg 140108 = 18900 ∧ d₁.nreg 140109 = 1 ∧
      (∀ x, ¬ ztekl → d₁.nreg x = d.nreg x) ∧ d₁ = { d with nreg := d₁.nreg } := by
    zujup
    unfold shInitA
    exec_block
    all_goals first | omega | skip
    refine ⟨rfl, ?_, ?_, ?_, fun x hx => ?_, rfl⟩
    all_goals first | (config_simp; done) | skip
    zubd
  have hAa : ztutq := by_grind
  obtain ⟨db, kb, eb, hkb, b01, b00, rb, mb⟩ : ∃ d₁ k₁, Exec P W shInitB da d₁ k₁ ∧
      k₁ = 2 ∧ d₁.nreg 140101 = A₀ ∧ d₁.nreg 140100 = A₀ + 1 ∧
      (∀ x, x ≠ 140101 → x ≠ 140100 → d₁.nreg x = da.nreg x) ∧ d₁ = { da with nreg := d₁.nreg } := by
    zuffj

    unfold shInitB
    rw [hAl]
    exec_block
    all_goals first | (config_simp; rw [hAa, a03]; omega) | skip
    refine ztdqy
    · tauto
    · config_simp; omega
    · zubd
  have b03 : db.nreg 140103 = 1 := by_grind
  have b08 : db.nreg 140108 = 18900 := by_grind
  have ec := Exec.addN (P := P) eb.wb_right 140107 140100 140108 by_omega
  set d₁ := ({ db with nreg := upd db.nreg 140107 _ } : Config)
    with hd₁
  have r₁ : ∀ x, ¬ ztekl → d₁.nreg x = d.nreg x := fun x hx => by
    zuipl

  have g₁ : ∀ x, x ≠ 140107 → d₁.nreg x = db.nreg x := fun x hx => by
    simp only [hd₁, upd]; grind
  have o03 : d₁.nreg 140103 = 1 := by_grind
  have o08 : d₁.nreg 140108 = 18900 := by_grind
  have o01 : d₁.nreg 140101 = A₀ := by_grind
  have o00 : d₁.nreg 140100 = A₀ + 1 := by_grind
  have o09 : d₁.nreg 140109 = 1 := by_grind
  have o07 : d₁.nreg 140107 = A₀ + 1 + 18900 := by
    simp only [hd₁, upd, ↓reduceIte]; omega
  have m₁ : d₁ = { d with nreg := d₁.nreg } := by
    grind
  -- the doubling loop
  obtain ⟨T, hT⟩ : ztorv := by_grind
  zugdl
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c = { d with nreg := c.nreg } ∧
    (∀ x, ¬ ztekl → c.nreg x = d.nreg x) ∧ c.nreg 140103 = 1 ∧
    c.nreg 140108 = 18900 ∧ c.nreg 140101 = A₀ ∧ c.nreg 140100 = A₀ + 1 ∧
    ∃ t, c.nreg 140109 = 2 ^ t ∧ c.nreg 140107 = A₀ + 1 + ztjeo ∧ t ≤ T
  have I₁ : Inv d₁ := ⟨ec.wb_right, m₁, r₁, o03, o08, o01, o00, 0, by_omega,
    by zupbd, Nat.zero_le _⟩
  obtain ⟨d₂, k₂, e₂, I₂, hx₂, hk₂⟩ := Exec.whileLtN_bounded (P := P) (a := 140109) (b := 150009)
    (body := shLimBody) Inv
    (fun c => T + 1 - (Nat.log 2 (c.nreg 140109))) 2 ztjvp
    (fun c ⟨hw', hm', hr', h3, h8, h1, h0, t, h9, h7, ht⟩ hlt => by
      zubbo

      have hmul := Nat.mul_le_mul_left 18900 ztmoh
      have hW7 : A₀ + 1 + ztjeo + 18900 ≤ W := by
        grind
      unfold shLimBody
      obtain ⟨c', k, e, hk, o9, o7, r', m'⟩ : ∃ c' k, Exec P W (block [.addN 140109 140109 140109,
          .addN 140107 140107 140108]) c c' k ∧ k = 2 ∧ c'.nreg 140109 = 2 ^ (t + 1) ∧
          c'.nreg 140107 = A₀ + 1 + ztjeo + 18900 ∧
          (∀ x, x ≠ 140109 → x ≠ 140107 → c'.nreg x = c.nreg x) ∧
          c' = { c with nreg := c'.nreg } := by
        have h2W : ztmsr := by_omega
        clear hroom hγW hm hmul hlt
        exec_block
        all_goals first | (config_simp; rw [h9]; omega) | (config_simp; rw [h7, h8]; omega) |
          skip
        refine ztdqy
        · config_simp; omega
        · config_simp; grind
        · zubd
      refine ⟨c', k, e, ⟨e.wb_right, by_grind, fun x hx => by
        grind, by_grind,
        by grind, by_grind,
        by grind, t + 1, o9, by_grind, by_omega⟩,
        by omega, ?_⟩
      zufoe
      omega) I₁
  obtain ⟨hw₂, hm₂, hr₂, h3, h8, h1, h0, t, h9, h7, ht⟩ := I₂
  zuegd

  have hlog : ztsce := by
    zujde
    · zukrp
    · have := Nat.log_lt_of_lt_pow (b := 2) (x := t + 1) (y := γ) by_omega
        by_omega
      omega
  have hmul := Nat.mul_le_mul_left 18900 ht
  zukdf
  have hmem : ztmvn := by zundq
  refine ⟨d₂, ka + ztzwr, 2100 * t + 2100, .seq ea ztnck, ?_,
    ⟨by_grind, h1, h3, by_grind, by_linarith,
    fun a ha => by_grind,
    by grind,
    fun i hi => by_grind, by_grind⟩, by_omega, hr₂, hmem,
    by zundq, by zundq, by zundq⟩
  omega

/-- **The finish**: the allocator raised to the end of the records. -/
theorem shFin_exec {W A₀ Nmax : ℕ} {m₀ : ℕ → ℕ} {c₀ : Config} {ps : List Pc}
    (d : Config) (hw : WordsBounded W d) (hI : ShI W A₀ Nmax m₀ c₀ ps d)
    (hq : ps.length ≤ Nmax) :
    ∃ d' k, Exec P W shFin d d' k ∧ k ≤ 3 * (1 + 9 * ps.length) + 2 ∧
      d'.nreg ALLOC = A₀ + 1 + 9 * ps.length ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + k ∧
      (∀ x, x ≠ ALLOC → d'.nreg x = d.nreg x) ∧ d' = { d with nreg := d'.nreg } := by
  zuk
  obtain ⟨hA, -, h1, -, hLW, -, hp, -, -⟩ := hI
  rw [min_eq_left hq] at hp
  set E := A₀ + 1 + 9 * ps.length with hE
  let Inv : Config → Prop := fun c => WordsBounded W c ∧ c.nreg ALLOC ≤ E ∧
    (∀ x, x ≠ ALLOC → c.nreg x = d.nreg x) ∧ c = { d with nreg := c.nreg }
  obtain ⟨d₂, k₂, e₂, ⟨hw₂, hA₂, hr₂, hm₂⟩, hx₂, hk₂, hψ⟩ :=
    whileLtN_potential_lb' (P := P) (W := W) (a := ALLOC) (b := 140100)
    (body := .instr ztrhx) Inv ztjvn
    ztesf ztcvf
    (fun c ⟨hw', hA', hr', hm'⟩ ht => by
      have e3 : c.nreg 140103 = 1 := by_grind
      have e0 : c.nreg 140100 = E := by_grind
      zukqt
      have ex := Exec.addN (P := P) hw' ALLOC ALLOC 140103 by_omega
      refine ⟨_, 1, ex, ⟨ex.wb_right, ?_, fun x hx => ?_, ?_⟩, ?_, ?_⟩
      · zudlc
      · zumzy; rw [Machine.upd_other _ _ _ hx]; grind
      · zumnn
      · zudlc
      · zuock; zvnak)
    ⟨hw, by_omega, fun _ _ => rfl, rfl⟩
  have e0 : d₂.nreg 140100 = E := by_grind
  zukqu
  refine ⟨d₂, k₂, e₂, ?_, by_omega, by_omega, hr₂, hm₂⟩
  omega
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def lpInit : Stmt := block [.addN 140113 140403 K1, .addN 140113 140113 K1, .loadN 140112 140113,
  .addN 140114 140112 140112, .constN 140115 7, .addN 140334 140114 140115,
  .addN 140110 140101 K1, .constN 140210 0]

/-- The first five words of a record. -/
def lpLoadA : Stmt := block [.loadN 140250 140110, .addN 140110 140110 K1,
  .loadN 140251 140110, .addN 140110 140110 K1, .loadN 140252 140110, .addN 140110 140110 K1,
  .loadN 140253 140110, .addN 140110 140110 K1, .loadN 140254 140110, .addN 140110 140110 K1]

/-- The last four words of a record. -/
def lpLoadB : Stmt := block [.loadN 140255 140110, .addN 140110 140110 K1,
  .loadN 140256 140110, .addN 140110 140110 K1, .loadN 140257 140110, .addN 140110 140110 K1,
  .loadN 140258 140110, .addN 140110 140110 K1]

/-- A record into `140250 …`. -/
def lpLoad : Stmt := .seq lpLoadA lpLoadB

/-- One piece. -/
def lpBody (query : Stmt) : Stmt := .seq lpLoad (.ifLtN 140254 K1 pieceK0 (pieceK1 query))

/-- **The loop over the pieces.** -/
def shLoop (query : Stmt) : Stmt := .seq lpInit (.whileLtN 140110 140100 (lpBody query))

/-- The registers written by `lpInit`. -/
def Blpi (r : ℕ) : Bool := decide (140110 ≤ r ∧ r < 140116) || r == 140334 || r == 140210

/-- The registers written by `lpLoad`. -/
def Blpl (r : ℕ) : Bool := decide (140250 ≤ r ∧ r < 140259) || r == 140110
theorem wr_lpInit : wr Blpi lpInit = true := by_decide
theorem wr_lpLoad : wr Blpl lpLoad = true := by_decide

/-! ## The set-up and the loads -/
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}
theorem noHit_empty : NoHit (∅ : Set Point) z σ := fun _ _ hm => hm
variable (c : Config)
theorem lpInit_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {D A₀ m : ℕ}
    (h403 : c.nreg 140403 = D) (hm : c.nmem ztmo = m) (h101 : c.nreg 140101 = A₀)
    (hD : D + 2 ≤ W) (hmW : 2 * m + 7 ≤ W) (hA : A₀ + 1 ≤ W) :
    ∃ c' k, Exec P W lpInit c c' k ∧ k = 8 ∧ c'.nreg 140334 = 2 * m + 7 ∧
      c'.nreg 140110 = A₀ + 1 ∧ c'.nreg 140210 = 0 ∧ FrameB Blpi c c' := by
  zubfu
  obtain ⟨c', k, ex, hk, v34, v10, v210⟩ : ∃ c' k, Exec P W lpInit c c' k ∧ k = 8 ∧
      c'.nreg 140334 = 2 * m + 7 ∧ c'.nreg 140110 = A₀ + 1 ∧ c'.nreg 140210 = 0 := by
    unfold lpInit
    simp only [K1]
    exec_block
    all_goals first | omega | (config_simp; rw [h403, h1']; omega) |
      (config_simp; rw [h403, h1', show D + 1 + 1 = D + 2 by omega, hm]; omega) |
      (config_simp; rw [h101, h1']; omega) | skip
  exact ⟨c', k, ex, hk, v34, v10, v210, exec_frameB ex wr_lpInit⟩
theorem lpLoadA_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W lpLoadA c c' k ∧ k = 10 ∧ c'.nreg 140110 = p + 5 ∧
      c'.nreg 140250 = c.nmem p ∧ c'.nreg 140251 = c.nmem ztr ∧
      c'.nreg 140252 = c.nmem ztcao ∧ c'.nreg 140253 = c.nmem ztdhu ∧
      c'.nreg 140254 = c.nmem zthiz := by
  zubfu
  unfold lpLoadA
  simp only [K1]
  exec_block
  all_goals first | (config_simp; rw [h10, h1']; omega) | skip
  simp_all
theorem lpLoadB_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 4 ≤ W) :
    ∃ c' k, Exec P W lpLoadB c c' k ∧ k = 8 ∧ c'.nreg 140110 = p + 4 ∧
      c'.nreg 140255 = c.nmem p ∧ c'.nreg 140256 = c.nmem ztr ∧
      c'.nreg 140257 = c.nmem ztcao ∧ c'.nreg 140258 = c.nmem ztdhu := by
  zubfu
  unfold lpLoadB
  simp only [K1]
  exec_block
  all_goals first | (config_simp; rw [h10, h1']; omega) | skip
  simp_all
theorem lpLoad_exec (hw : WordsBounded W c) (h1 : c.nreg K1 = 1) {p : ℕ}
    (h10 : c.nreg 140110 = p) (hp : p + 9 ≤ W) :
    ∃ c' k, Exec P W lpLoad c c' k ∧ k = 18 ∧ c'.nreg 140110 = p + 9 ∧
      c'.nreg 140250 = c.nmem p ∧ c'.nreg 140251 = c.nmem ztr ∧
      c'.nreg 140252 = c.nmem ztcao ∧ c'.nreg 140253 = c.nmem ztdhu ∧
      c'.nreg 140254 = c.nmem zthiz ∧ c'.nreg 140255 = c.nmem ztkbt ∧
      c'.nreg 140256 = c.nmem ztoec ∧ c'.nreg 140257 = c.nmem zttva ∧
      c'.nreg 140258 = c.nmem zttvb ∧ FrameB Blpl c c' := by
  obtain ⟨c₁, k₁, e₁, hk₁, q10, q0, q1, q2, q3, q4⟩ := lpLoadA_exec (P := P) c hw h1 h10 hp
  have f₁ := exec_frameB (B := Blpl) e₁ by_decide
  have g1 : ztcpf := by zuomh; exact h1
  obtain ⟨c₂, k₂, e₂, hk₂, u10, u5, u6, u7, u8⟩ := lpLoadB_exec (P := P) c₁ e₁.wb_right g1 q10
    by_omega
  have f₂ := exec_frameB (B := fun r => decide (140255 ≤ r ∧ r < 140259) || r == 140110) e₂
    by_decide
  have ex : Exec P W lpLoad c c₂ ztbct := .seq e₁ e₂
  have hm : ztwh := f₁.2.2.1
  refine ⟨c₂, _, ex, by_omega, by rw [u10], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    exec_frameB ex wr_lpLoad⟩
  · rw [f₂.1 _ by_decide, q0]
  · rw [f₂.1 _ by_decide, q1]
  · rw [f₂.1 _ by_decide, q2]
  · rw [f₂.1 _ by_decide, q3]
  · rw [f₂.1 _ by_decide, q4]
  · simp_all
  · simp_all
  · simp_all
  simp_all

/-! ## The invariant -/

/-- The point set of a piece. -/
noncomputable def pcSetOf (C : Chain) (Q : Polygon) (pc : Pc) : Set Point :=
  (chainModel C).arcSet ztmyp ztmyo

/-- The point set of a list of pieces. -/
noncomputable def psSet (C : Chain) (Q : Polygon) (l : List Pc) : Set Point :=
  ⋃ pc ∈ l, pcSetOf C Q pc
theorem psSet_nil (C : Chain) (Q : Polygon) : psSet C Q [] = ∅ := by simp [psSet]
theorem psSet_append (C : Chain) (Q : Polygon) (l : List Pc) (pc : Pc) :
    psSet C Q (l ++ [pc]) = psSet C Q l ∪ pcSetOf C Q pc := by
  ext x; simp [psSet, or_comm]

/-- A frame for the bands of the oracles, without its bound on the growth of the allocator. -/
def FrameNK (c c' : Config) : Prop :=
  (∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
    (∀ r, bandOf r ∉ oracleBands → c'.rreg r = c.rreg r) ∧
    zth ∧
    ztgo ∧ c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC
theorem FrameNK.refl : FrameNK c c :=
  ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, le_rfl⟩
theorem FrameNK.step {c c₁ c₂ : Config} {k : ℕ} (h₁ : FrameNK c c₁)
    (h₂ : Frame oracleBands c₁ c₂ k) : FrameNK c c₂ := by
  obtain ⟨r₁, rr₁, m₁, rm₁, o₁, a₁⟩ := h₁
  obtain ⟨r₂, rr₂, m₂, rm₂, o₂, a₂, -⟩ := h₂
  exact ⟨fun r hr hra => by_simp_all, fun r hr => by_simp_all,
    fun a ha => by_grind,
    fun a ha => by_grind, o₂.trans o₁, a₁.trans a₂⟩
theorem FrameNK.frame {c c' : Config} {k : ℕ} (h : FrameNK c c')
    (hk : c'.nreg ALLOC ≤ c.nreg ALLOC + k) : Frame oracleBands c c' k :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2, hk⟩

/-- **The fixed facts of the loop.** -/
structure LpCtx (O : OracleIface) (P : Polygon) (W : ℕ) (C : Chain) (z : Point)
    (m₀ : ℕ → ℕ) (h γ A₀ : ℕ) (s e : WPos) (ps : List Pc) : Prop where
  hV : O.Valid
  arc : ArcOK C zta s e ps
  ok : ∀ pc ∈ ps, PcOK P C m₀ h γ pc
  hsP : ProperPos ztc zta P.n s
  heP : ProperPos ztc zta P.n e
  hs1 : s.edge < 2 * C.m + 7
  he1 : e.edge < 2 * C.m + 7
  hsin : s.hgt = 0 ∨ |((chainModel C).pos zta s).2| < C.radius
  hein : e.hgt = 0 ∨ |((chainModel C).pos zta e).2| < C.radius
  hwt : (chainModel C).arcWt ztwlj ztwli ≤ γ
  hz : z ∉ (chainModel C).arcSet ztwlj ztwli
  hR : Robust A₀ m₀ fun m' => GradeRaw O P m' h A₀
  hQs : (Qof P).Simple
  hnW : 2 * C.m + 7 + 1 ≤ W

/-- **The invariant of the loop** (start `cs`, per-piece bound `K`). -/
def LpI (P : Polygon) (W : ℕ) (H : Host) (C : Chain) (z : Point) (σ : ℝ) (m₀ : ℕ → ℕ)
    (A₀ : ℕ) (ps : List Pc) (cs : Config) (K : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ ShEnv P W H C z σ c ∧ OrgOK P C z σ c ∧ dirOf ztghb = σ ∧
    c.nreg 140334 = 2 * C.m + 7 ∧ c.nreg 140100 = A₀ + 1 + 9 * ps.length ∧
    Rec9 c.nmem A₀ ps ∧ ztiuf ∧
    A₀ + 1 + 9 * ps.length ≤ c.nreg ALLOC ∧ FrameNK cs c ∧
    c.nreg ALLOC + ztfaz * ztnu ≤ W ∧
    ∃ j, j ≤ ps.length ∧ c.nreg 140110 = A₀ + 1 + 9 * j ∧
      CandAt P C c 140210 (psSet C zta ztwbx) z σ
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace ShootCut
open Machine Machine.Stmt Programs SignK WalkKey NFLoc SweepPrim
@[expose] public section
def LoopR (r : ℕ) : Prop :=
  r = 140008 ∨ r = 140334 ∨ r = 140100 ∨ r = 140110 ∨ (140234 ≤ r ∧ r < 140241) ∨ r = ALLOC
variable (r : ℕ) {O : OracleIface} {m₀ : ℕ → ℕ} {h γ A₀ : ℕ} {s e : WPos} {ps : List Pc}
theorem Blpl_env (h : envR r) : Blpl r = false := by
  zufdg
  simp only [Blpl, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega
theorem Blpl_org (h1 : 140234 ≤ r) (h2 : r < 140241) : Blpl r = false := by
  simp only [Blpl, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
  omega
theorem Bk0_loop (h : LoopR r) : Bk0 r = false := by
  zumrd
  simp only [Bk0, Bedge, Bmrg, Bk, Bprim, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega
theorem Wk1_loop (h : LoopR r) : Wk1 r = false := by
  zumrd
  simp only [Wk1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega
theorem Bk0_ob (h : Bk0 r = true) :
    ztbav ∧ r ≠ ALLOC := by
  simp only [Bk0, Bedge, Bmrg, Bk, Bprim, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  zuhai
theorem Blpl_ob (h : Blpl r = true) :
    ztbav ∧ r ≠ ALLOC := by
  simp only [Blpl, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  zuhai
variable {P : Polygon} {W : ℕ} {H : Host} {C : Chain} {z : Point} {σ : ℝ}

/-! ## One piece -/

/-- **One piece of the loop.** -/
theorem lpBody_exec
    {cs : Config} {K : ℕ} (X : LpCtx O P W C z m₀ h γ A₀ s e ps)
    (hK : O.κ * ztbamk + 600500 ≤ K)
    (c : Config) (hI : LpI P W H C z σ m₀ A₀ ps cs K c) (hlt : c.nreg 140110 < c.nreg 140100) :
    ∃ c' k, Exec P W ztqtd c c' k ∧ LpI P W H C z σ m₀ A₀ ps cs K c' ∧
      ztfay * ztnu + k + 2 ≤
        ztfaz * ztnu ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨hw, E, Og, h08, h34, h100, hrec, hm0, hEA, fr, hbud, j, hj, h110, hB⟩ := hI
  have hjq : j < ps.length := by_omega
  set pc := ps[j]'hjq with hpc
  have hpcm := List.getElem_mem hjq
  have hok := X.ok pc hpcm
  obtain ⟨r0, r1, r2, r3, r4, r58⟩ := hrec j hjq
  set p := A₀ + 1 + 9 * j with hp
  set L := A₀ + 1 + 9 * ps.length with hL
  have hLp : L - p = zthbd + 9 := by_omega
  have hbud' : c.nreg ALLOC + (zthbd * ztnu + 9 * ztnu) ≤ W := by
    rw [h110, hLp, Nat.add_mul] at hbud; omega
  have hAW : c.nreg ALLOC + 9 * ztnu ≤ W := by
    omega
  have htk : ps.take ztl = ps.take j ++ [pc] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hjq]; rfl
  -- the keys and the subarc
  have hks := key_range X.hsP X.hs1
  have hke := key_range X.heP X.he1
  have hA := arcSet_pieces X.arc hks hke fun q hq => pcOK_keys (X.ok q hq)
  have hzpc : z ∉ pcSetOf C _ pc := fun hzp => X.hz (by
    zvmze; exact Set.mem_biUnion hpcm hzp)
  -- the load
  obtain ⟨c₁, k₁, e₁, hk₁, q10, v50, v51, v52, v53, v54, v55, v56, v57, v58, f₁⟩ :=
    lpLoad_exec (P := P) c hw E.k1 h110 by_omega
  zud
  have E₁ := E.frame f₁ Blpl_env
  have Og₁ := Og.keep fun r a b => f₁.1 r (Blpl_org r a b)
  have g1 := E₁.k1
  have kl : ∀ r, LoopR r → r ≠ 140110 → c₁.nreg r = c.nreg r := fun r hr hr' =>
    f₁.1 r (by
      unfold LoopR at hr
      simp only [Blpl, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne] at hr ⊢
      omega)
  have hA₁ : ztdc := kl _ ztcun by_decide
  zugmw
  have hB₁ : CandAt P C c₁ 140210 _ z σ :=
    hB.keep fun i hi => f₁.1 _ (by simp only [Blpl, Bool.or_eq_false_iff,
      decide_eq_false_iff_not, beq_eq_false_iff_ne]; omega)
  have F₁ := frame_of_frameB f₁ (fun r hr =>
    ⟨oracleBands_mem r (by have := (Blpl_ob r hr).1; omega), (Blpl_ob r hr).2⟩) k₁
  -- the ends of the piece
  have hends := X.arc.ends pc hpcm
  have hxe : pc.s.hgt = 0 ∨ |((chainModel C).pos zta pc.s).2| < C.radius := by
    rcases hends.1 with h' | h'
    · zvmxl; exact X.hsin
    omega
  have hye : pc.e.hgt = 0 ∨ |((chainModel C).pos zta pc.e).2| < C.radius := by
    rcases hends.2 with h' | h'
    · zvmxl; exact X.hein
    omega
  have hW₀ := E.hW
  -- the rest of the invariant after the piece
  have finish : ∀ (c₂ : Config) (k₂ : ℕ), Exec P W (.ifLtN 140254 K1 pieceK0 ztwbs)
      c₁ c₂ k₂ → k₂ + 20 ≤ K → WordsBounded W c₂ → ShEnv P W H C z σ c₂ →
      Frame oracleBands c₁ c₂ k₂ → (∀ r, LoopR r → r ≠ ALLOC → c₂.nreg r = c₁.nreg r) →
      CandAt P C c₂ 140210 (psSet C zta ztwbx ∪ pcSetOf C zta pc) z σ →
      ∃ c' k, Exec P W ztqtd c c' k ∧ LpI P W H C z σ m₀ A₀ ps cs K c' ∧
        ztfay * ztnu + k + 2 ≤
          ztfaz * ztnu ∧
        c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
    intro c₂ k₂ e₂ hk₂ w₂ E₂ F₂ kr hB₂
    have ex : Exec P W ztqtd c c₂ ztbct := by unfold lpBody; exact .seq e₁ e₂
    have F := F₁.trans F₂
    rw [Finset.union_self] at F
    obtain ⟨-, -, fm, -, -, fa, fk⟩ := F
    have k2 : ∀ r, LoopR r → r ≠ ALLOC → r ≠ 140110 → c₂.nreg r = c.nreg r := by_grind
    have n10 : c₂.nreg 140110 = p + 9 := by rw [kr _ ztcun by_decide, q10]
    have Og₂ := Og₁.keep fun r a b =>
      kr r (by unfold LoopR; omega)
        ztu
    refine ⟨c₂, _, ex, ⟨w₂, E₂, Og₂, ?_, ?_, ?_, ?_, ?_, ?_, FrameNK.step fr (F₁.trans F₂ |>.mono
      by_simp le_rfl), ?_, j + 1, by_omega, by_omega, ?_⟩, ?_, by_omega⟩
    · zudai
    · zudai
    · zudai
    · zug
      have := hrec i hi
      have hlt' : ∀ f, f < 9 → A₀ + 1 + 9 * i + f < c.nreg ALLOC := by_grind
      have h0' := hlt' 0 by_norm_num
      rw [Nat.add_zero] at h0'
      refine ⟨by rw [fm _ h0']; omega, by zumyx; omega,
        by zumyx; omega,
        by zumyx; omega,
        by zumyx; omega, fun hk => ?_⟩
      obtain ⟨b5, b6, b7, b8⟩ := this.2.2.2.2.2 hk
      exact ⟨by zumyx; exact b5,
        by zumyx; exact b6,
        by zumyx; exact b7,
        by zumyx; exact b8⟩
    · zuge
      rw [fm a by_omega]; grind
    · omega
    · rw [n10]
      grind
    · rw [htk, psSet_append]; omega
    · rw [n10, h110]
      show zthbd * ztnu + ztbct + 2 ≤ (L - p) * ztnu
      rw [hLp, Nat.add_mul]
      omega
  -- the kind of the piece
  rcases hok.2.2.2.2.1 with hk0 | hk1
  · -- kind 0
    have t : c₁.nreg 140254 < c₁.nreg K1 := by_grind
    obtain ⟨c₂, k₂, e₂, hk₂, hB₂, f₂⟩ := pieceK0_exec c₁ w₁ E₁ by_grind by_grind
      by_grind by_grind
      ztyat hok.1 hok.2.1 hok.2.2.1
      hok.2.2.2.1 (hok.2.2.2.2.2.1 hk0) hxe hye hzpc hB₁ X.hnW by_omega
    exact finish c₂ _ ztspo by_omega e₂.wb_right (E₁.frame f₂ Bk0_env)
      (frame_of_frameB f₂ (fun r hr => ⟨oracleBands_mem r (by have := (Bk0_ob r hr).1; omega),
        (Bk0_ob r hr).2⟩) _) (fun r hr _ => f₂.1 r (Bk0_loop r hr)) hB₂
  · -- kind 1
    have t : ¬ c₁.nreg 140254 < c₁.nreg K1 := by_grind
    obtain ⟨g, b, hg1, hgΛ, hb, hE, hpw, hx0, hbn, hgran, hs0, he0, h6, hee, hem, hdir, hWk⟩ :=
      hok.2.2.2.2.2.2 hk1
    obtain ⟨r5, r6, r7, r8⟩ := r58 hk1
    have hmA : ∀ a, a < A₀ → c₁.nmem a = m₀ a := fun a ha => by_grind
    obtain ⟨hen, hAt, hCα, hgg, hMpw⟩ := kind1_query hok hk1 X.hR hmA
    have hpwγ := kind1_pw_le_γ X.arc X.hsP X.heP X.hs1 X.he1 X.hwt hpcm hok hk1
    have hcost := query_cost_le (κ := O.κ) hgg (show c₁.nmem _
      ≤ γ by rw [hMpw]; exact hpwγ)
    have hw1 : 1 ≤ pc.pw := by rw [hpw]; exact Nat.one_le_two_pow
    have hpp : pc.s.edge + pc.pw ≤ 2 * C.m + 6 := by_omega
    zuc
    have hPW : ztfku := by unfold hostWords at hW₀; omega
    zumei
    obtain ⟨c₂, k₂, e₂, hk₂, hB₂, F₂, keep₂, E₂⟩ := pieceK1_exec X.hV c₁ w₁ E₁
      ztyat hB₁ (x0 := pc.x0)
      (by rw [v50, r0]) (by rw [v55, r5]) (by rw [v56, r6]) (by rw [v57, r7]) (by rw [v58, r8])
      (by rw [hx0, hpw]; omega) hw1 by_omega h6 hpp hdir hAt hCα
      Og₁.qk (fun h0 => Og₁.q0 h0 _ fun x hx => block_inC hw1 h6 hpp hx) Og₁.q1 X.hQs hcost
      by_omega by_omega by_omega by_omega
    have hset : pcSetOf C zta pc =
        (chainModel C).arcSet (pc.s.edge : ℝ) ((pc.s.edge + pc.pw : ℕ) : ℝ) := by
      unfold pcSetOf
      rw [show pc.s = ztkmk by zunwt, show pc.e = zthnm by zuota,
        key_hgt0, key_hgt0, hee, hpw]
    exact finish c₂ _ ztnaf by_omega e₂.wb_right E₂ (F₂.mono ztibe
      by_omega)
      (fun r hr ha => keep₂ r (by unfold LoopR ALLOC at hr; unfold ALLOC at ha; omega)
        (by unfold LoopR ALLOC at hr; omega) (Wk1_loop r hr))
      (by rw [hset]; omega)

/-! ## The loop -/
theorem Blpi_env (h : envR r) : Blpi r = false := by
  zufdg
  simp only [Blpi, K1, ALLOC, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne] at h ⊢
  omega
theorem Blpi_ob (h : Blpi r = true) :
    ztbav ∧ r ≠ ALLOC := by
  simp only [Blpi, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  zuhai

/-- **The loop over the pieces**: the best first hit on all of them. -/
theorem shLoop_exec
    {K : ℕ} (X : LpCtx O P W C z m₀ h γ A₀ s e ps)
    (hK : O.κ * ztbamk + 600500 ≤ K)
    (c : Config) (hw : WordsBounded W c) (E : ShEnv P W H C z σ c) (Og : OrgOK P C z σ c)
    (h08 : dirOf ztghb = σ) (h100 : c.nreg 140100 = A₀ + 1 + 9 * ps.length)
    (h101 : c.nreg 140101 = A₀) (hrec : Rec9 c.nmem A₀ ps)
    (hm0 : ∀ a, a < A₀ → c.nmem a = m₀ a) (hEA : A₀ + 1 + 9 * ps.length ≤ c.nreg ALLOC)
    (hbud : c.nreg ALLOC + 9 * ps.length * ztnu ≤ W) :
    ∃ c' k, Exec P W ztwds c c' k ∧ k ≤ 9 * ps.length * ztnu + 20 ∧
      CandAt P C c' 140210 (psSet C zta ps) z σ ∧ Frame oracleBands c c' k ∧
      ShEnv P W H C z σ c' := by
  have hD := E.hD
  have hwf := E.hwf
  zumei
  obtain ⟨c₁, k₁, e₁, hk₁, v34, v10, v210, f₁⟩ := lpInit_exec (P := P) c hw E.k1 rfl
    hD.2.2.2.1 h101 (by have := hwf.1; omega) by_omega by_omega
  have E₁ := E.frame f₁ Blpi_env
  zumfm
  zuhwk
  have F₁ := frame_of_frameB f₁ (fun r hr =>
    ⟨oracleBands_mem r (by have := (Blpi_ob r hr).1; omega), (Blpi_ob r hr).2⟩) k₁
  have I₁ : LpI P W H C z σ m₀ A₀ ps c K c₁ := by
    refine ⟨e₁.wb_right, E₁, Og.keep fun r a b => k₁' r (by simp only [Blpi,
      Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]; omega),
      by zuonv; omega, v34, by zuonv; omega,
      by rw [f₁.2.2.1]; omega, fun a ha => by rw [f₁.2.2.1]; simp_all,
      by omega, FrameNK.step (FrameNK.refl c) F₁, ?_, 0, Nat.zero_le _,
      by rw [v10], ?_⟩
    · simp_all
    · rw [List.take_zero, psSet_nil]
      have h0 : c₁.nreg (140210 : ℕ) ≠ 1 := by_omega
      exact ⟨by_omega, fun _ => noHit_empty, by_simp_all⟩
  obtain ⟨c₂, k₂, e₂, I₂, hx₂, hk₂, hψ⟩ := whileLtN_potential_lb' (P := P) (W := W)
    (a := 140110) (b := 140100) (body := lpBody O.query) (LpI P W H C z σ m₀ A₀ ps c K)
    (fun c' => ztfay * ztnu) ztcht
    (fun _ hI => hI.1) (fun c' hI ht => lpBody_exec X hK c' hI ht) I₁
  obtain ⟨-, E₂, -, -, -, h100₂, -, -, -, fr₂, -, j, hj, h110, hB⟩ := I₂
  have hjq : j = ps.length := by_omega
  rw [hjq, List.take_length] at hB
  have ex : Exec P W ztwds c c₂ ztbct := by unfold shLoop; exact .seq e₁ e₂
  refine ⟨c₂, _, ex, ?_, hB, fr₂.frame ?_, E₂⟩
  · rw [v10, show A₀ + 1 + 9 * ps.length - ztfnc = 9 * ps.length by omega] at hk₂
    omega
  omega
end
end ShootCut
end Chazelle.Core
namespace Chazelle.Core
namespace DrvB
open Machine Machine.Stmt Programs SignK WalkKey
open DrvR (qE)
@[expose] public section
def BestOK (Q : Polygon) (n i : ℕ) (σ : ℝ) (li : Bool) (ES : ℕ → Prop) (f bw bq : ℕ) : Prop :=
  f ≤ 1 ∧
  (f = 1 → bw < n ∧ ES bw ∧ bq = qE li n bw ∧ Cand Q i σ bq ∧
    ∀ w, ES w → w < n → Cand Q i σ ztlsb →
      σ * edgeXAt Q bq i ≤ σ * edgeXAt Q ztlsb i) ∧
  (f = 0 → ∀ w, ES w → w < n → ¬ Cand Q i σ ztlsb)
variable {Q : Polygon} {n i : ℕ} {σ : ℝ} {li : Bool} {c : Config}
theorem BestOK.congr {ES ES' : ℕ → Prop}
    (h : ∀ w, ES w ↔ ES' w) {f bw bq : ℕ} (hb : BestOK Q n i σ li ES f bw bq) :
    BestOK Q n i σ li ES' f bw bq := by
  zugpc
  refine ⟨h1, fun hf => ?_, by_simp_all⟩
  grind

/-- **One visited walk edge** `w'`: a candidate replaces the best if there is none or if it is
strictly nearer. -/
theorem bestOK_step {ES : ℕ → Prop} {f bw bq : ℕ}
    (hb : BestOK Q n i σ li ES f bw bq) {w' : ℕ} (hw' : w' < n) {f' bw' bq' : ℕ}
    (hup : Cand Q i σ ztefo ∧ (f = 0 ∨
        σ * edgeXAt Q ztefo i < σ * edgeXAt Q bq i) →
      bw' = w' ∧ bq' = qE li n w' ∧ f' = 1)
    (hkeep : ¬ (Cand Q i σ ztefo ∧ (f = 0 ∨
        σ * edgeXAt Q ztefo i < σ * edgeXAt Q bq i)) →
      bw' = bw ∧ bq' = bq ∧ f' = f) :
    BestOK Q n i σ li (fun w => ES w ∨ w = w') f' bw' bq' := by
  zugpc
  by_cases hu : Cand Q i σ ztefo ∧ (f = 0 ∨
      σ * edgeXAt Q ztefo i < σ * edgeXAt Q bq i)
  · obtain ⟨e1, e2, e3⟩ := hup hu
    zumpz
    refine ⟨le_rfl, fun _ => ⟨hw', Or.inr rfl, rfl, hu.1, fun w hw hwn hc => ?_⟩,
      by grind⟩
    grind
  · obtain ⟨e1, e2, e3⟩ := hkeep hu
    zumpz
    refine ⟨h1, fun hf => ?_, fun hf w hw hwn hc => ?_⟩
    · grind
    grind

/-- The walk edges of the ranges before `t` and the first `u` walk edges of range `t`. -/
def ESr (n : ℕ) (stF cntF : ℕ → ℕ) (t u w : ℕ) : Prop :=
  (∃ t', t' < t ∧ ∃ u', u' < cntF t' ∧ w = (stF t' + u') % n) ∨
    (∃ u', u' < u ∧ w = (stF t + u') % n)
theorem ESr_succ (n : ℕ) (stF cntF : ℕ → ℕ) (t u w : ℕ) :
    ESr n stF cntF t ztcol w ↔ ESr n stF cntF t u w ∨ w = (stF t + u) % n := by
  unfold ESr
  constructor
  · rintro (h | ⟨u', hu', rfl⟩)
    · simp_all
    grind
  · rintro ((h | ⟨u', hu', rfl⟩) | rfl)
    · simp_all
    · grind
    grind
theorem ESr_next (n : ℕ) (stF cntF : ℕ → ℕ) (t w : ℕ) :
    ESr n stF cntF t ztqjv w ↔ ESr n stF cntF ztbx 0 w := by
  unfold ESr
  constructor
  · rintro (⟨t', ht', h⟩ | h)
    · exact Or.inl ⟨t', by_omega, h⟩
    · exact Or.inl ⟨t, by_omega, h⟩
  · rintro (⟨t', ht', h⟩ | ⟨u', hu', -⟩)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 ht' with h' | rfl
      · exact Or.inl ⟨t', h', h⟩
      simp_all
    · omega
theorem ESr_zero (n : ℕ) (stF cntF : ℕ → ℕ) (w : ℕ) : ¬ ESr n stF cntF 0 0 w := by
  unfold ESr; omega

/-! ## The program -/

/-- Range loader, `K = 0`: the whole walk. -/
def ldAll : Stmt := block [.constN 212093 0, .copyN 212092 212010]

/-- Range loader, `K > 0`: arc `j = mem[lp + t]`, `st = s.edge`, `cnt = arcCnt`. -/
def ldArcR : Stmt :=
  .seq (block [.addN 212037 212033 212036, .loadN 212037 212037,
    .addN 212038 212037 212037, .addN 212038 212038 212038, .addN 212038 212038 212037,
    .addN 212038 212038 216014, .addN 212038 212038 212000, .loadN 212093 212038,
    .addN 212038 212038 212002, .loadN 212092 212038, .addN 212092 212092 212010,
    .subN 212092 212092 212093])
  (.seq (.ifLtN 212092 212010 .skip (.instr (.subN 212092 212092 212010)))
    (.instr (.addN 212092 212092 212000)))

/-- The range loader. -/
def ldRange : Stmt := .ifLtN 212001 212012 ldArcR ldAll

/-- One range of the scan. -/
def rangeB : Stmt :=
  .seq ldRange (.seq (.instr (.constN 212091 0)) (.seq ztrie
    (.instr (.addN 212036 212036 212000))))

/-- **The far-end scan.** -/
def farS : Stmt :=
  .seq (block [.constN 212099 0, .constN 212036 0]) (.whileLtN 212036 212034 rangeB)

/-- The registers the scan writes. -/
def Bfar (r : ℕ) : Bool := Bk r || decide ztnfp || decide ztnfq
theorem bfar_vis (r : ℕ) (h : Bvis r = true) : Bfar r = true := by
  unfold Bvis at h; unfold Bfar
  grind
theorem bfar_of {r : ℕ} (h : ztnfp ∨ ztnfq) :
    Bfar r = true := by
  unfold Bfar; grind
theorem wr_ldRange : wr (fun r => decide ztogi || decide ztogj ||
    decide ztogk || decide ztogl) ldRange = true := by_decide

/-- The data of range `t`: the whole walk (`K = 0`) or arc `mem[lp + t]` of the region. -/
def LdOK (c : Config) (n t st cnt : ℕ) : Prop :=
  (c.nreg 212012 = 0 ∧ st = 0 ∧ cnt = n) ∨
  (0 < c.nreg 212012 ∧ st = c.nmem (c.nreg 216014 + 5 * c.nmem ztdmp + 1) ∧
    st < n ∧ c.nmem ztxdw < n ∧
    cnt = ztbaor % n + 1)
theorem LdOK.st_lt {n t st cnt : ℕ} (h : LdOK c n t st cnt) (hn : 0 < n) : st < n := by
  rcases h with ⟨-, h, -⟩ | ⟨-, -, h, -⟩ <;> omega
theorem LdOK.cnt_le {n t st cnt : ℕ} (h : LdOK c n t st cnt) (hn : 0 < n) :
    cnt ≤ n := by
  rcases h with ⟨-, -, h⟩ | ⟨-, -, -, -, h⟩
  · omega
  · zvmwc; have := Nat.mod_lt ztbaor hn
    omega
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **The range loader.** -/
theorem ldRange_exec (c : Config) (hw : WordsBounded W c) {n t st cnt : ℕ}
    (hn : c.nreg 212010 = n) (hn0 : 0 < n) (ht : c.nreg 212036 = t) (hld : LdOK c n t st cnt)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hW : 2 * n + 1 ≤ W)
    (hAB : 0 < c.nreg 212012 → c.nreg 216014 + 5 * c.nmem ztdmp + 3 ≤ W)
    (hlp : 0 < c.nreg 212012 → c.nreg 212033 + t ≤ W) :
    ∃ c' k, Exec P W ldRange c c' k ∧ k ≤ 18 ∧ c'.nreg 212093 = st ∧ c'.nreg 212092 = cnt ∧
      FrameB (fun r => decide ztogi || decide ztogj || decide ztogk ||
        decide ztogl) c c' := by
  rcases hld with ⟨hK, hs, hc⟩ | ⟨hK, hs, hsn, hen, hc⟩
  · obtain ⟨c', k, ex, hk, v1, v2⟩ : ∃ c' k, Exec P W ldAll c c' k ∧ k = 2 ∧
        c'.nreg 212093 = st ∧ c'.nreg 212092 = cnt := by
      unfold ldAll
      exec_block
      · omega
      simp_all
    have ex' : Exec P W ldRange c c' _ := .ifLtN_false by_omega ex
    exact ⟨c', _, ex', by_omega, v1, v2, exec_frameB ex' wr_ldRange⟩
  · have hAB := hAB hK
    have hlp := hlp hK
    set j := c.nmem _ with hj
    set e := c.nmem (c.nreg 216014 + 5 * j + 3) with he
    obtain ⟨c₁, k₁, e₁, hk₁, v1, v2, v38⟩ : ∃ c₁ k₁, Exec P W (block [.addN 212037 212033 212036,
        .loadN 212037 212037, .addN 212038 212037 212037, .addN 212038 212038 212038,
        .addN 212038 212038 212037, .addN 212038 212038 216014, .addN 212038 212038 212000,
        .loadN 212093 212038, .addN 212038 212038 212002, .loadN 212092 212038,
        .addN 212092 212092 212010, .subN 212092 212092 212093]) c c₁ k₁ ∧ k₁ = 12 ∧
        c₁.nreg 212093 = st ∧ c₁.nreg 212092 = e + n - st ∧ c₁.nreg 212010 = n := by
      have hj5 : 5 * j ≤ W := by_omega
      have hA1 : c.nmem (j + j + ztcvv + j + c.nreg 216014 + 1) = st := by
        grind
      have hA3 : c.nmem (j + j + ztcvv + j + c.nreg 216014 + 1 + 2) = e := by
        grind
      exec_block
      all_goals try (config_simp; (try simp only [hn, ht, c0, c2]); omega)
      all_goals (config_simp; simp only [hn, ht, c0, c2, ← hj])
      · omega
      grind
    zud
    have f₁ : FrameB (fun r => decide ztogi || decide ztogj ||
        decide ztogk || decide ztogl) c c₁ := exec_frameB e₁ by_decide
    zuefw
    by_cases hlt : e + n - st < n
    · have e₂ := Exec.addN (P := P) w₁ 212092 212092 212000 by_omega
      have ex : ztpjp :=
        .seq e₁ (.seq ztxdi e₂)
      zugkz

      · dsimp only; rw [Machine.upd_other _ _ _ by_norm_num, v1]
      · zumzo; rw [v2, c0', hc, Nat.mod_eq_of_lt hlt]
    · have e₂ := Exec.subN (P := P) w₁ 212092 212092 212010
      zue
      have e₃ := Exec.addN (P := P) w₂ 212092 212092 212000 (by
        zuvz
        rw [Machine.upd_other _ _ _ by_norm_num, v2, v38, c0']; omega)
      have ex : ztpjp :=
        .seq e₁ (.seq ztcry e₃)
      zugkz

      · zubvt
        rw [Machine.upd_other _ _ _ by_norm_num, Machine.upd_other _ _ _ by_norm_num, v1]
      · zuvz
        rw [Machine.upd_other _ _ _ by_norm_num, v2, v38, c0', hc,
          Nat.mod_eq_sub_mod by_omega, Nat.mod_eq_of_lt by_omega]
set_option maxHeartbeats 4000000 in
/-- **The walk edges of one range.** -/
theorem visLoop_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW2 : 2 * P.n + 2 ≤ W) (c : Config)
    (hw : WordsBounded W c) {stF cntF : ℕ → ℕ} {t i d : ℕ} {li : Bool}
    (hn : c.nreg 212010 = P.n) (hst : c.nreg 212093 = stF t) (hcnt : c.nreg 212092 = cntF t)
    (hu : c.nreg 212091 = 0) (hsn : stF t < P.n) (hcn : cntF t ≤ P.n)
    (hli : c.nreg 212011 = if li then 1 else 0) (hi : c.nreg 212070 = i) (hin : i < P.n)
    (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2)
    (hb : BestOK zta P.n i ztbgl li ztown
      (c.nreg 212099) (c.nreg 212097) ztjrw) :
    ∃ c' k, Exec P W ztrie c c' k ∧ k ≤ ztcom * cntF t + 2 ∧
      FrameB Bvis c c' ∧
      BestOK zta P.n i ztbgl li (ESr P.n stF cntF ztbx 0)
        ztvgk ztvgi ztvgj := by
  let Inv : ℕ → Config → Prop := fun u e => WordsBounded W e ∧ e.nreg 212091 = u ∧
    e.nreg 212092 = cntF t ∧ FrameB Bvis c e ∧
    BestOK zta P.n i ztbgl li (ESr P.n stF cntF t u)
      ztvpp ztvpn ztvpo
  have I0 : ztpki := ⟨hw, hu, hcnt, FrameB.refl _ _, hb⟩
  obtain ⟨c', k, ex, ⟨-, -, -, hf, hb'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212091)
    (nr := 212092) Inv visK ztqjv ztbko
    (fun u e hu ⟨hw, h1, h2, hf, hbe⟩ => by
      zugla
      obtain ⟨hb1, hb2, hb3⟩ := id hbe
      obtain ⟨e', k, ex, hk, hf', v91, u1, u2⟩ := visitS_exec (P := P) hG hW hW2 e hw
        (st := stF t) (u := u) (i := i) (d := d) (li := li)
        ztlhg (by rw [g _ by_decide, hst]) h1 hsn by_omega
        (by rw [g _ by_decide, hli]) (by rw [g _ by_decide, hi]) hin
        (by rw [g _ by_decide, hd]) hd1 ztlhd
        ztlhe ztlhf hb1
        (fun h => by obtain ⟨a1, -, a3, -⟩ := hb2 h; rw [a3]; exact DownMath.qE_lt li a1)
      refine ⟨e', k, ex, ⟨ex.wb_right, v91, by zunya, hf.trans hf', ?_⟩,
        hk⟩
      refine (bestOK_step hbe ztcv
        ztep ztep).congr (fun w => (ESr_succ P.n stF cntF t u w).symm)
      · grind
      grind)
    I0 ztbg
  exact ⟨c', k, ex, by_omega, hf, hb'.congr (ESr_next P.n stF cntF t)⟩
theorem LdOK.congr {c e : Config} {n t st cnt : ℕ} (h : LdOK c n t st cnt)
    (h12 : e.nreg 212012 = c.nreg 212012) (h14 : e.nreg 216014 = c.nreg 216014)
    (h33 : e.nreg 212033 = c.nreg 212033) (hm : e.nmem = c.nmem) : LdOK e n t st cnt := by
  unfold LdOK; rw [h12, h14, h33, hm]; exact h
set_option maxHeartbeats 4000000 in
/-- **The far-end scan**: the σ-nearest candidate over the walk edges of all ranges. -/
theorem farS_exec (hG : GoodEnv P) (hW : P.n + 3 ≤ W) (hW2 : 2 * P.n + 2 ≤ W) (c : Config)
    (hw : WordsBounded W c) {stF cntF : ℕ → ℕ} {nR i d Cm : ℕ} {li : Bool}
    (hn : c.nreg 212010 = P.n) (hnR : c.nreg 212034 = nR)
    (hld : ∀ t, t < nR → LdOK c P.n t (stF t) ztqjv) (hCm : ∀ t, t < nR → cntF t ≤ Cm)
    (hAB : ∀ t, t < nR → 0 < c.nreg 212012 →
      c.nreg 216014 + 5 * c.nmem ztdmp + 3 ≤ W)
    (hlp : 0 < c.nreg 212012 → c.nreg 212033 + nR ≤ W)
    (hli : c.nreg 212011 = if li then 1 else 0) (hi : c.nreg 212070 = i) (hin : i < P.n)
    (hd : c.nreg 212086 = d) (hd1 : d ≤ 1)
    (c0 : c.nreg 212000 = 1) (c1 : c.nreg 212001 = 0) (c2 : c.nreg 212002 = 2) :
    ∃ c' k, Exec P W farS c c' k ∧ k ≤ ztzhm * nR + 4 ∧ FrameB Bfar c c' ∧
      BestOK zta P.n i ztbgl li (ESr P.n stF cntF nR 0)
        ztvgk ztvgi ztvgj := by
  zufvs
  -- the initialisation
  obtain ⟨c₁, k₁, e₁, hk₁, v99, v36⟩ : ∃ c₁ k₁, Exec P W (block [.constN 212099 0,
      .constN 212036 0]) c c₁ k₁ ∧ k₁ = 2 ∧ c₁.nreg 212099 = 0 ∧ c₁.nreg 212036 = 0 := by
    exec_block
    all_goals try omega
    simp
  have f₁ : FrameB Bfar c c₁ := exec_frameB e₁ by_decide
  zuepx
  let Inv : ℕ → Config → Prop := fun t e => WordsBounded W e ∧ e.nreg 212036 = t ∧
    e.nreg 212034 = nR ∧ FrameB Bfar c e ∧
    BestOK zta P.n i ztbgl li ztown
      ztvpp ztvpn ztvpo
  have I0 : Inv 0 c₁ := ⟨e₁.wb_right, v36, by rw [g₁ _ by_decide, hnR], f₁,
    ⟨by_omega, by_omega,
      fun _ w hw => absurd hw (ESr_zero P.n stF cntF w)⟩⟩
  obtain ⟨c', k, ex, ⟨-, -, -, hf, hb'⟩, hk⟩ := DrvR.forLoop (P := P) (W := W) (ir := 212036)
    (nr := 212034) (body := rangeB) Inv (ztcom * Cm + 22) nR ztbko
    (fun t e ht ⟨hw, h1, h2, hf, hbe⟩ => by
      zugla
      have hld' := (hld t ht).congr ztnzt ztnzt ztnzt
        hf.2.2.1
      have hsn := (hld t ht).st_lt hn0
      have hcn := (hld t ht).cnt_le hn0
      -- the range
      obtain ⟨e₁, k₁, x₁, hk₁, s₁, s₂, f₁⟩ := ldRange_exec (P := P) e hw
        ztlhg hn0 h1 hld' ztlhd
        ztlhe ztlhf by_omega
        (fun hK => by
          rw [g _ by_decide, g _ by_decide, hf.2.2.1]
          exact hAB t ht ztljj)
        (fun hK => by
          zumxb
          have := hlp ztljj; omega)
      have g₁ : ∀ r, r ≠ 212037 → r ≠ 212038 → r ≠ 212092 → r ≠ 212093 →
          e₁.nreg r = e.nreg r := fun r a b c d => f₁.1 r (by
            simp_all)
      -- the counter
      have x₂ := Exec.constN (P := P) x₁.wb_right 212091 0 ztbg
      set e₂ : Config := { e₁ with nreg := upd e₁.nreg 212091 0 } with he₂
      have g₂ : ∀ r, r ≠ 212091 → e₂.nreg r = e₁.nreg r := by_simp_all
      have G : ∀ r, Bfar r = false → e₂.nreg r = c.nreg r := fun r h => by
        zuivb
        simp only [Bfar, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h'
        grind
      -- the walk edges
      obtain ⟨e₃, k₃, x₃, hk₃, f₃, hb₃⟩ := visLoop_exec (P := P) hG hW hW2 e₂ x₂.wb_right
        (stF := stF) (cntF := cntF) (t := t) (i := i) (d := d) (li := li)
        (by rw [G _ by_decide, hn]) by_simp_all
        by_simp_all by_rfl hsn hcn
        (by rw [G _ by_decide, hli]) (by rw [G _ by_decide, hi]) hin
        (by rw [G _ by_decide, hd]) hd1 (by rw [G _ by_decide, c0])
        (by rw [G _ by_decide, c1]) (by rw [G _ by_decide, c2])
        by_simp_all
      -- the range counter
      have v36 : e₃.nreg 212036 = t := by
        rw [f₃.1 _ by_decide, g₂ _ by_decide,
          g₁ _ by_decide by_decide by_decide by_decide, h1]
      have v00 : e₃.nreg 212000 = 1 := by rw [f₃.1 _ by_decide, G _ by_decide, c0]
      have hnRW : nR ≤ W := by have := hw.1 212034; omega
      have x₄ := Exec.addN (P := P) x₃.wb_right 212036 212036 212000 by_omega
      have f₄ : FrameB (fun r => decide (r = 212036)) e₃ _ := exec_frameB x₄ by_decide
      have ex : Exec P W rangeB e _ _ := .seq x₁ ztgxf
      have hk₃' : k₃ ≤ ztcom * Cm + 2 := by
        have := Nat.mul_le_mul_left ztcom (hCm t ht); omega
      refine ⟨_, _, ex, ⟨x₄.wb_right, ?_, ?_, ?_, ?_⟩, by_omega⟩
      · simp only [Machine.upd_same, v36, v00]
      · rw [f₄.1 _ by_decide, f₃.1 _ by_decide, G _ by_decide, hnR]
      · refine hf.trans ((fbMono f₁ fun r h => ?_).trans ((fbMono (exec_frameB x₂ (by decide :
          wr ztlor _ = true)) fun r h => ?_).trans
          ((fbMono f₃ bfar_vis).trans (fbMono f₄ fun r h => ?_))))
        · simp only [Bool.or_eq_true, decide_eq_true_eq] at h; exact bfar_of by_omega
        · zugho
        · zugho
      · have e99 : ∀ r, r ≠ 212036 → (upd e₃.nreg 212036 (e₃.nreg 212036 + e₃.nreg 212000)) r =
            e₃.nreg r := fun r h => Machine.upd_other _ _ _ h
        grind)
    I0 ztbg
  have e : (ztcom * Cm + 22 + 2) * (nR - 0) = ztzhm * nR := by
    simp
  refine ⟨c', _, .seq e₁ ex, by_omega, hf, hb'⟩
end exec
end
end DrvB
end Chazelle.Core
namespace Chazelle.Core
namespace BuildRam
open Machine Machine.Stmt Programs SignK
@[expose] public section
def offF (cA cC : ℕ → ℕ) (r : ℕ) : ℕ := ((List.range r).map fun r' => cA r' + cC r').sum
variable (cA cC : ℕ → ℕ) (m₁ : ℕ → ℕ) {RT FA R : ℕ}
theorem offF_succ (r : ℕ) : offF cA cC ztgu = offF cA cC r + cA r + cC r := by
  unfold offF
  rw [List.range_succ, List.map_append, List.sum_append]
  grind
theorem offF_mono {r r' : ℕ} (h : r ≤ r') : offF cA cC r ≤ offF cA cC r' := by
  induction r' with
  | zero => zunwb
  | succ n ih =>
    rcases Nat.lt_or_ge r ztkk with h' | h'
    · rw [offF_succ]; omega
    · grind

/-- The word `q` of the region table. -/
def rtv (cA cC wR : ℕ → ℕ) (q : ℕ) : ℕ :=
  if q % 5 = 0 then cA ztftv else if q % 5 = 1 then offF cA cC ztftv
  else if q % 5 = 2 then cC ztftv else if q % 5 = 3 then offF cA cC ztftv + cA ztftv
  else wR ztftv

/-- The memory after the records of the first `n` regions. -/
def recRMem (m₁ : ℕ → ℕ) (RT FA R : ℕ) (cA cC wR : ℕ → ℕ) (n a : ℕ) : ℕ :=
  if RT ≤ a ∧ a < RT + 5 * n then rtv cA cC wR (a - RT)
  else if FA ≤ a ∧ a < FA + n then offF cA cC (a - FA)
  else if FA + R ≤ a ∧ a < FA + R + n then offF cA cC ztnqp + cA ztnqp
  else m₁ a
theorem rtv_eq (cA cC wR : ℕ → ℕ) (r f : ℕ) (hf : f < 5) :
    rtv cA cC wR ztgcs = if f = 0 then cA r else if f = 1 then offF cA cC r
      else if f = 2 then cC r else if f = 3 then offF cA cC r + cA r else wR r := by
  unfold rtv
  grind

/-- The memory step of the region records. -/
theorem recR_step (cA cC wR : ℕ → ℕ) {n : ℕ} (hn : n < R)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT) (a : ℕ) :
    upd (upd (upd (upd (upd (upd (upd (recRMem m₁ RT FA R cA cC wR n) ztqcl (cA n))
      (RT + 5 * n + 1) ztruc) (RT + 5 * n + 2) (cC n))
      (RT + 5 * n + 3) (offF cA cC n + cA n)) (RT + 5 * n + 4) (wR n))
      (FA + n) ztruc) (FA + R + n) (offF cA cC n + cA n) a =
      recRMem m₁ RT FA R cA cC wR ztkk a := by
  zudlr
  unfold recRMem
  have hr : a < RT ∨ (RT ≤ a ∧ a < RT + 5 * n) ∨ (∃ f, f < 5 ∧ a = RT + 5 * n + f) ∨
      (RT + 5 * n + 5 ≤ a ∧ a < RT + 5 * R) ∨ RT + 5 * R ≤ a := by
    by_cases h : RT + 5 * n ≤ a ∧ a < RT + 5 * n + 5
    · exact Or.inr (Or.inr (Or.inl ⟨a - ztqcl, by_omega, by_omega⟩))
    · omega
  have hq : a < FA ∨ (FA ≤ a ∧ a < FA + n) ∨ a = FA + n ∨ (FA + n + 1 ≤ a ∧ a < FA + R) ∨
      (FA + R ≤ a ∧ a < FA + R + n) ∨ a = FA + R + n ∨ FA + R + n + 1 ≤ a := by_omega
  rcases hr with h | h | ⟨f, hf, rfl⟩ | h | h
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega | (congr 1; omega) | (congr 1 <;> congr 1 <;> omega)
  · ifs_omega
  · interval_cases f <;> ifs_omega <;>
      first
        | rfl
        | (rw [show RT + 5 * n + 0 - RT = 5 * n + 0 by omega, rtv_eq _ _ _ _ _ by_norm_num];
           rfl)
        | (rw [show RT + 5 * n + 1 - RT = 5 * n + 1 by omega, rtv_eq _ _ _ _ _ by_norm_num];
           rfl)
        | (rw [show RT + 5 * n + 2 - RT = 5 * n + 2 by omega, rtv_eq _ _ _ _ _ by_norm_num];
           rfl)
        | (rw [show RT + 5 * n + 3 - RT = 5 * n + 3 by omega, rtv_eq _ _ _ _ _ by_norm_num];
           rfl)
        | (rw [show RT + 5 * n + 4 - RT = 5 * n + 4 by omega, rtv_eq _ _ _ _ _ by_norm_num];
           rfl)
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega
  · rcases hq with h' | h' | rfl | h' | h' | rfl | h' <;> ifs_omega <;>
      first | rfl | omega | (congr 1; omega) | (congr 1 <;> congr 1 <;> omega)

/-- `recR_step` with the addresses and values given by equations. -/
theorem recR_step' (cA cC wR : ℕ → ℕ) {n : ℕ} (hn : n < R)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT) {M : ℕ → ℕ}
    (hM : M = recRMem m₁ RT FA R cA cC wR n)
    {a0 a1 a2 a3 a4 a5 a6 v0 v1 v2 v3 v4 v5 v6 : ℕ}
    (e0 : a0 = RT + 5 * n) (e1 : a1 = RT + 5 * n + 1) (e2 : a2 = RT + 5 * n + 2)
    (e3 : a3 = RT + 5 * n + 3) (e4 : a4 = RT + 5 * n + 4) (e5 : a5 = FA + n)
    (e6 : a6 = FA + R + n) (w0 : v0 = cA n) (w1 : v1 = offF cA cC n) (w2 : v2 = cC n)
    (w3 : v3 = offF cA cC n + cA n) (w4 : v4 = wR n) (w5 : v5 = offF cA cC n)
    (w6 : v6 = offF cA cC n + cA n) :
    upd (upd (upd (upd (upd (upd (upd M a0 v0) a1 v1) a2 v2) a3 v3) a4 v4) a5 v5) a6 v6 =
      recRMem m₁ RT FA R cA cC wR ztkk := by
  subst a0 a1 a2 a3 a4 a5 a6 v0 v1 v2 v3 v4 v5 v6 M
  funext a
  exact recR_step m₁ cA cC wR hn hlay a

/-- The region records and the fill pointers. -/
def regRecLoop : Stmt :=
  .whileLtN 43201 43200 (block [
    .addN 43211 43201 43201, .addN 43211 43211 43211, .addN 43211 43211 43201,
    .addN 43211 43211 44003,
    .addN 43212 44008 43201, .loadN 43213 43212,
    .addN 43212 43212 43200, .loadN 43214 43212,
    .addN 43212 43212 43200, .loadN 43215 43212,
    .storeN 43211 43213, .addN 43211 43211 43011, .storeN 43211 43210,
    .addN 43211 43211 43011, .storeN 43211 43214, .addN 43211 43211 43011,
    .addN 43216 43210 43213, .storeN 43211 43216, .addN 43211 43211 43011,
    .storeN 43211 43215,
    .addN 43217 44011 43201, .storeN 43217 43210,
    .addN 43217 43217 43200, .storeN 43217 43216,
    .addN 43210 43216 43214,
    .addN 43201 43201 43011])

/-- The registers `regRecLoop` writes. -/
def BregRec (r : ℕ) : Bool := decide ztevb || decide (43210 ≤ r ∧ r < 43218)
theorem wr_regRecLoop : wrM BregRec regRecLoop = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}

/-- **The region records and the fill pointers.** -/
theorem regRecLoop_exec (d : Config) (hw : WordsBounded W d) {m₀ : ℕ → ℕ} {CA R RT FA : ℕ}
    {cA cC wR : ℕ → ℕ} (hCA : d.nreg 44008 = CA) (hR : d.nreg 43200 = R) (h1 : d.nreg 43011 = 1)
    (hi : d.nreg 43201 = 0) (hP : d.nreg 43210 = 0) (hRT : d.nreg 44003 = RT)
    (hFA : d.nreg 44011 = FA) (hRTW : RT + 5 * R ≤ W) (hFAW : FA + 2 * R ≤ W)
    (hlay : RT + 5 * R ≤ FA ∨ FA + 2 * R ≤ RT)
    (hdis : (RT + 5 * R ≤ CA ∨ CA + 3 * R ≤ RT) ∧ (FA + 2 * R ≤ CA ∨ CA + 3 * R ≤ FA))
    (hoff : offF cA cC R ≤ W) (hCAW : CA + 3 * R ≤ W)
    (hm : d.nmem = regMem m₀ CA R cA cC wR) :
    ∃ d' k, Exec P W regRecLoop d d' k ∧ k ≤ 28 * R + 2 ∧ 26 * R ≤ k ∧ WordsBounded W d' ∧
      FrameM BregRec d d' ∧
      d'.nmem = recRMem zthke RT FA R cA cC wR R := by
  obtain ⟨d', k, e, ⟨hw', n, hn', hnR, hPn, hf, hm'⟩, htest, hk, hψ⟩ :=
    SortR.whileLtN_potential_lb (P := P) (W := W) (a := 43201) (b := 43200) (body := _)
    (fun e => WordsBounded W e ∧ ∃ n, e.nreg 43201 = n ∧ n ≤ R ∧ e.nreg 43210 = offF cA cC n ∧
      FrameM BregRec d e ∧ e.nmem = recRMem zthke RT FA R cA cC wR n)
    (fun e => 28 * ztrkd) (fun e => 26 * e.nreg 43201) ztchu
    (fun e ⟨hwe, n, hne, hnR, hPe, hfe, hme⟩ htest => by
      have r1 : ztuug := by zunzg
      zuboh

      have r5 : e.nreg 44003 = RT := by rw [hfe.1 _ by_decide, hRT]
      zuehy
      rw [hne, r2] at htest
      have ma : e.nmem (CA + n) = cA n := by
        zuexz
        rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega, regMem_rdA _ _ _ _ _ _ htest]
      have mc : e.nmem (CA + n + R) = cC n := by
        zuexz
        rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega,
          show CA + n + R = CA + R + n by omega, regMem_rdC _ _ _ _ _ _ htest]
      have mw : e.nmem (CA + n + R + R) = wR n := by
        zuexz
        rw [ite_eq_right by_omega, ite_eq_right by_omega, ite_eq_right by_omega,
          show CA + n + R + R = CA + 2 * R + n by omega, regMem_rdW _ _ _ _ _ _ htest]
      have ho1 := offF_succ cA cC n
      have ho2 := offF_mono cA cC (show n + 1 ≤ R by omega)
      have X : ∃ e' k, Exec P W (block [
          .addN 43211 43201 43201, .addN 43211 43211 43211, .addN 43211 43211 43201,
          .addN 43211 43211 44003,
          .addN 43212 44008 43201, .loadN 43213 43212,
          .addN 43212 43212 43200, .loadN 43214 43212,
          .addN 43212 43212 43200, .loadN 43215 43212,
          .storeN 43211 43213, .addN 43211 43211 43011, .storeN 43211 43210,
          .addN 43211 43211 43011, .storeN 43211 43214, .addN 43211 43211 43011,
          .addN 43216 43210 43213, .storeN 43211 43216, .addN 43211 43211 43011,
          .storeN 43211 43215,
          .addN 43217 44011 43201, .storeN 43217 43210,
          .addN 43217 43217 43200, .storeN 43217 43216,
          .addN 43210 43216 43214,
          .addN 43201 43201 43011]) e e' k ∧ k = 26 ∧ e'.nreg 43201 = n + 1 ∧
          e'.nreg 43210 = offF cA cC ztkk ∧
          e'.nmem = recRMem zthke RT FA R cA cC wR ztkk := by
        exec_block
        all_goals first
          | (config_simp; simp (config := { failIfUnchanged := false }) only [r1, r2, r4, r5, r6,
              hne, hPe, ma, mc, mw]; omega)
          | skip
        refine zthnq <;> config_simp
        · omega
        · grind
        · rw [r1, r2, r4, r5, r6, hne, hPe, ma, mc, mw]
          exact recR_step' _ cA cC wR htest hlay hme by_omega by_omega by_omega by_omega
            by_omega by_omega by_omega rfl rfl rfl rfl rfl rfl rfl
      obtain ⟨e', k, x, hk, hn', hP', hm'⟩ := X
      exact ⟨e', k, x, ⟨x.wb_right, n + 1, hn', by_omega, hP',
        hfe.trans ztjux, hm'⟩, by_omega,
        by omega⟩)
    ⟨hw, 0, hi, Nat.zero_le _, by_tauto, FrameM.refl _ _, by
      zvmwi; funext a; unfold recRMem; grind⟩
  have hnR' : n = R := by
    rw [hn', hf.1 _ by_decide, hR] at htest; omega
  subst hnR'
  exact ⟨d', k, e, by_omega, by_omega, hw', hf, hm'⟩
