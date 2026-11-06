module

public import Chazelle.MacT
public import Chazelle.Core.FuseAsmMain
public import Chazelle.Core.RestoreFComplete2
public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.ClusterLabelStage
public import Chazelle.Core.ShootCutLoop2
public import Chazelle.Core.FuseMathCut
public import Chazelle.Core.GranInitL3
public import Chazelle.Core.SweepPrimJun
public import Chazelle.Core.SweepChainT
public import Chazelle.Core.ShootCutCore2
public import Chazelle.Core.DownPhaseDrvBCorner
public import Chazelle.Core.ShootCutShPt

namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideInArc)
open OracleQ (sj sk ek succP predP)
namespace Sweep
section FaceMath
theorem sideInArc_nhds {a b x : ℝ} (h : sideInArc a b x) :
    ∃ δ > (0 : ℝ), ∀ s, 0 < s → s < δ → sideInArc a b ztfvh ∧ sideInArc a b ztkgy := by
  zusg
  zudwd
  · refine ⟨min (x - a) (b - x), by_simp_all,
      fun s hs0 hs => ?_⟩
    grind
  · zuy
    · exact ⟨x - a, by_linarith, by_grind⟩
    · exact ⟨b - x, by_linarith, by_grind⟩
variable {M : Model}
variable {F : Set (Set Point)} {U : Set Point} {a b : ℝ}
/-- **A walk vertex strictly inside an arc**: its region is faced just after it. -/
theorem afterFaces_of_inArc
    (harc : M.IsArc F U a b) {p : ℕ} (hp : p < M.W.n) (hin : sideInArc a b p) :
    AfterFaces M p 0 U := by
  zubhp
  refine zteze
  exact harc.2.2.2.2.2.2 p _ hp by_linarith hs2 by_simp_all

/-- **A walk vertex strictly inside an arc**: its region is faced just before it. -/
theorem beforeFaces_of_inArc
    (harc : M.IsArc F U a b) {p : ℕ} (hp : p < M.W.n) (hin : sideInArc a b p) :
    BeforeFaces M p 0 U := by
  zubhp
  zuiy
  zucyn
  · -- the arc wraps around the start of the walk
    zuhxy

    have hb : ¬ a < b := by
      intro hab
      zubix
      grind
    have hnr : (0 : ℝ) < (M.W.n : ℝ) - a := by_linarith
    refine ⟨min 1 _, lt_min one_pos hnr, by_simp_all,
      fun _ s hs0 hs1 => ?_⟩
    have h1 := min_le_left 1 ztmyc
    have h2 := min_le_right 1 ztmyc
    have e : ztcrd := by
      simp
    zui
    zuiex
    have e2 : ((M.W.n - 1 : ℕ) : ℝ) + zteb = (M.W.n : ℝ) - s := by
      simp_all
    zucjj
    zuiq

  · refine ⟨min δ 1, by_simp_all, by_simp_all, fun _ s hs0 hs1 => ?_⟩
    have h1 := min_le_left δ 1
    have h2 := min_le_right δ 1
    zukyh
    zuiex
    simp_all

/-- **The empty family**: the region of any arc is faced at every position inside a walk edge. -/
theorem faces_of_empty (harc : M.IsArc F U a b)
    (hF : F = ∅) {p : ℕ} (hp : p < M.W.n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : M.Faces p t U := by
  have hab : ztiyu := by
    zutm
    · simp_all
    simp_all
  refine harc.2.2.2.2.2.2 p t hp ht0 ht1 ?_
  rw [hab.1, hab.2]
  zuiq
theorem afterFaces_of_empty
    (harc : M.IsArc F U a b) (hF : F = ∅) {p : ℕ} (hp : p < M.W.n) : AfterFaces M p 0 U :=
  ⟨1, one_pos, fun s hs0 _ hs2 => faces_of_empty harc hF hp by_linarith hs2⟩
theorem beforeFaces_of_empty
    (harc : M.IsArc F U a b) (hF : F = ∅) {p : ℕ} (hp : p < M.W.n) : BeforeFaces M p 0 U := by
  zuiy
  exact ⟨1, one_pos, by_simp_all, fun _ s hs0 hs1 =>
    faces_of_empty harc hF zthp by_linarith by_linarith⟩

/-- **The key test**: the key of a proper position is the walk vertex `fe` iff its edge is `fe`
and its normalised height code is `0`. -/
theorem key_eq_nat_iff {Q : Polygon} {n : ℕ} {x : WPos} (hx : ProperPos M Q n x) (fe : ℕ) :
    M.key Q x = fe ↔ x.edge = fe ∧ (Restore.normOf M Q x).hgt = 0 := by
  have hk : ztehv := rfl
  have hp0 : x.hgt = 0 → M.param Q x = 0 := fun h => by simp [Model.param, h]
  constructor
  · zuq
    have h1 : (x.edge : ℝ) ≤ fe := by zungt
    have h2 : (fe : ℝ) < x.edge + 1 := by zunsm
    have e1 : x.edge ≤ fe := by exact_mod_cast h1
    have e2 : fe < x.edge + 1 := by exact_mod_cast h2
    have he : x.edge = fe := by_omega
    refine ztood
    have hpar : ztmtm := by_simp_all
    unfold Restore.normOf; simp_all
  · zukoj
    have hpar : ztmtm := by
      unfold Restore.normOf at hh
      grind
    simp_all

/-- The key of the walk vertex `(p, 0)`. -/
theorem key_vertex (Q : Polygon) (p : ℕ) : M.key Q ztcye = p := by
  zugga
end FaceMath
section FaceNF
variable {C : Chain} {P : Polygon} {N : NF}

/-- The arc at a spine position is an arc of its recorded region. -/
theorem arc_regOf {M : Model} {Q : Polygon} (hN : IsNF M Q N) {p : ℕ}
    (hp : p < N.arcs.length) :
    (N.arc ztmh).reg < N.nRegions ∧
      M.IsArc ztdu (regOf M Q N (N.arc ztmh).reg) ztcja ztchs :=
  (regOf_spec hN).2.2.1.1 _ ztctk

/-- **A cut at a walk vertex** is not the top of the slit: an arc end at the key `fe` has
`1 ≤ fe`. -/
theorem one_le_of_arc_end (hP : C.P.Simple) (hN : IsNF ztc zta N)
    (hne : (N.F ztc zta).Nonempty) {p fe : ℕ} (hp : p < N.arcs.length)
    (h : sk ztc zta N p = fe ∨ ek ztc zta N p = fe) : 1 ≤ fe := by
  have hi := NFLoc.seq_lt hN hp
  obtain ⟨hs, he⟩ := Restore.arc_abs_lt hP hN hne hi
  obtain ⟨pps, ppe⟩ := (regOf_spec hN).2.2.2.2.2.2 _ hi
  have go : ∀ x : WPos, ProperPos ztc zta (Qof P).n x →
      |((chainModel C).pos (Qof P) x).2| < C.radius → (chainModel C).key (Qof P) x = fe →
      1 ≤ fe := by
    intro x hx hb hk
    obtain ⟨he', hh⟩ := (key_eq_nat_iff hx fe).1 hk
    have hpar : ztxir := by
      have hk' : (chainModel C).key _ x = x.edge + (chainModel C).param zta x := rfl
      simp_all
    have := key_pos_of_band C hb hpar
    omega
  tauto
variable (hP : C.P.Simple) (hN : IsNF (chainModel C) (Qof P) N) {fe j : ℕ}
  (hfe : fe < (chainModel C).W.n) (hj : j < N.arcs.length)
  (hl1 : ¬ (chainModel C).IsCut ztwjq fe →
    N.F ztc zta = ∅ ∨
      sideInArc ztzhc ztzen fe)
  (hl2 : (chainModel C).IsCut ztwjq fe →
    sk ztc zta N j = fe ∨ ek ztc zta N j = fe)
include hP hN hfe hj

/-- **Just after, the arc at `j` ends at the vertex**: the region of the arc at `j + 1`. -/
theorem face_after_eq (hE : ek ztc zta N j = fe) :
    AfterFaces ztc fe 0
      (regOf ztc zta N (N.arc ztcaz).reg) := by
  obtain ⟨-, harcN⟩ := arc_regOf hN ztqbg
  zucfk
  · exact afterFaces_of_empty harcN hF hfe
  zucwm
  zuiv
  obtain ⟨-, hce, -, -⟩ := OracleQ.arc_facts hN hne hj
  rw [hE] at hce
  obtain ⟨U, hU, b, hab⟩ := (arcCover _ _ _ hGM hN.1).2 _ hce
  zuebg
  zufkl
  have hsq : sk ztc zta N q = fe := by
    show (chainModel C).key _ (N.arc zttaj).s = _
    simp_all
  have hq' := OracleQ.end_start_adj hN hGM hne hj hq (hE.trans hsq.symm)
  subst hq'
  zubxe

  rw [hsq] at harc hne'
  zuebz
include hl1 hl2 in
omit hP hN hfe hj hl1 hl2 in
/-- **Just after, the arc at `j` does not end at the vertex**: the region of the arc at `j`. -/
theorem face_after_ne (_hP : C.P.Simple) (hN : IsNF ztc zta N)
    (hfe : fe < (chainModel C).W.n) (hj : j < N.arcs.length)
    (hl1 : ¬ (chainModel C).IsCut ztwjq fe → N.F ztc
    zta = ∅ ∨ sideInArc ztzhc ztzen fe)
    (hl2 : (chainModel C).IsCut ztwjq fe → sk ztc
    zta N j = fe ∨ ek ztc zta N j = fe) (hE : ek (chainModel C)
    zta N j ≠ fe) :
    AfterFaces ztc fe 0 ztyfn := by
  zuboq
  zucfk
  · exact afterFaces_of_empty harc hF hfe
  zucwm
  zugjj
  · zujdt
    · zueag
      zvmyz at harc hne'
      zuebz

    simp_all
  · zuevl
    · simp_all
    · exact afterFaces_of_inArc harc hfe h

/-- **Just before, the arc at `j` starts at the vertex**: the region of the arc at `j - 1`. -/
theorem face_before_eq (hS : sk ztc zta N j = fe) :
    BeforeFaces ztc fe 0
      (regOf ztc zta N (N.arc ztcay).reg) := by
  obtain ⟨-, harcP⟩ := arc_regOf hN ztqbf
  zucfk
  · exact beforeFaces_of_empty harcP hF hfe
  zucwm
  zuiv
  have hM := walkAx_chainModel hP
  have h1 := one_le_of_arc_end hP hN hne hj ztvbw
  obtain ⟨hcs, -, -, -⟩ := OracleQ.arc_facts hN hne hj
  zvojf at hcs
  obtain ⟨c, hc, p', t', hA, hkey⟩ := hcs
  obtain ⟨-, V, l, -, -, hV, -, -, harcV, -⟩ := hM.attach_face hN.1.2.1 hN.1.1 hc hA
  rw [← hkey] at harcV
  obtain ⟨i, hi, -, hie⟩ := NFLoc.listed_of_isArc hN hV harcV
  zufkl
  have heq : ek ztc zta N q = fe := by
    show (chainModel C).key _ (N.arc zttaj).e = _
    simp_all
  have hjq := OracleQ.end_start_adj hN hGM hne hq hj (heq.trans hS.symm)
  have hqP : q = predP N.arcs.length j := by rw [hjq, OracleQ.predP_succP hq]
  subst hqP
  zubxe

  zvnbk at harc hne'
  refine beforeFaces_of_arc_end hfe h1 ztcmb by_grind
include hl1 hl2 in
/-- **Just before, the arc at `j` does not start at the vertex**: the region of the arc at `j`. -/
theorem face_before_ne (hS : sk ztc zta N j ≠ fe) :
    BeforeFaces ztc fe 0 ztyfn := by
  zuboq
  zucfk
  · exact beforeFaces_of_empty harc hF hfe
  zucwm
  zugjj
  · zujdt
    · simp_all
    · have h1 := one_le_of_arc_end hP hN hne hj (Or.inr he)
      zueag
      zvmxm at harc hne'
      exact beforeFaces_of_arc_end hfe h1 ztcmb
        by_simp_all
  · zuevl
    · simp_all
    · exact beforeFaces_of_inArc harc hfe h
end FaceNF
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology
open Chazelle.Chain (SideAttach sidePt sideInArc)
open OracleQ (sj sk ek succP predP)
namespace Sweep
section FaceR
variable {M : Model} {Q : Polygon} {N : NF}

/-- **A non-cut position faces the region of the arc at `j` just after it.** -/
theorem frc_after (hN : IsNF M Q N) {j : ℕ} (hj : j < N.arcs.length) {e : ℕ} {t : ℝ}
    (he : e < M.W.n) (ht0 : 0 ≤ t) (_ht1 : t < 1)
    (hl1 : N.F M Q = ∅ ∨ sideInArc ztevn zteru ztmyr) :
    AfterFaces M e t ztyfm := by
  zuboq
  zufzz
  · exact ⟨1, one_pos, fun s hs0 _ hs2 => faces_of_empty harc hF he by_linarith hs2⟩
  · zubhp
    refine zteze
    refine harc.2.2.2.2.2.2 e ztuf he by_linarith hs2 ?_
    grind

/-- **A non-cut position faces the region of the arc at `j` just before it.** -/
theorem frc_before (hN : IsNF M Q N) {j : ℕ} (hj : j < N.arcs.length) {e : ℕ} {t : ℝ}
    (he : e < M.W.n) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hl1 : N.F M Q = ∅ ∨ sideInArc ztevn zteru ztmyr) :
    BeforeFaces M e t ztyfm := by
  zuboq
  zudsi
  · zufzz
    · refine ⟨1, one_pos, fun _ s hs0 _ hst => ?_, fun h => absurd h htp.ne'⟩
      exact faces_of_empty harc hF he by_linarith by_linarith
    · zubhp
      refine ⟨δ, hδ, fun _ s hs0 hs1 hst => ?_, fun h => absurd h htp.ne'⟩
      refine harc.2.2.2.2.2.2 e ztfuw he by_linarith by_linarith ?_
      grind
  · zufzz
    · exact beforeFaces_of_empty harc hF he
    · zvncl at hin
      exact beforeFaces_of_inArc harc he hin
end FaceR
section Box
variable {C : Chain} {P : Polygon} {N : NF}

/-- **A walk vertex on the box is not a cut.** -/
theorem frc_box_noncut (hP : C.P.Simple) (hN : IsNF ztc zta N) {e : ℕ}
    (he : e < 6) : ¬ (chainModel C).IsCut ztwjq (e : ℝ) := by
  zuchg
  have hne : ztziv := by
    obtain ⟨c, hc', -⟩ := hc; tauto
  zuoj
  obtain ⟨U, hU, b, hab⟩ := (arcCover _ _ _ hGM hN.1).2 _ hc
  zuebg
  obtain ⟨hs, -⟩ := Restore.arc_abs_lt hP hN hne hi
  obtain ⟨pps, -⟩ := (regOf_spec hN).2.2.2.2.2.2 _ hi
  obtain ⟨hedge, -⟩ := (key_eq_nat_iff pps e).1 his
  have hpar : (chainModel C).param zta (N.arc i).s = 0 := by
    have hk : (chainModel C).key zta (N.arc i).s =
        (N.arc i).s.edge + (chainModel C).param zta (N.arc i).s := rfl
    simp_all
  have hv : (chainModel C).pos zta (N.arc i).s = (chainModel C).W.vtx e := by
    show sidePt (chainModel C).W (N.arc i).s.edge ((chainModel C).param zta (N.arc i).s) = _
    rw [hpar, hedge, Chazelle.Chain.sidePt_zero]
  zvmyq at hs
  zuiza
  rcases ShootCut.walk_vtx_box (C := C) (q := e) by_omega with h | h <;> zvmwc at hs
  · grind
  grind
end Box
end Sweep
end
end Chazelle.Core
namespace Chazelle.Core
namespace SweepRam
open Machine Machine.Stmt Programs
open ShotList (hostAt_agree chainDescAt_copy chainWF_copy)
@[expose] public section
def sw (i : ℕ) : ℕ := 240000 + i

/-! ## Copying a chain descriptor -/

/-- Copy one word from the address in `sw 97` to the address in `sw 96`, advancing both. -/
def cp1 : Stmt := block [.loadN ztdpr ztbhz, .storeN ztwg ztdpr,
  .addN ztwg ztwg ztxr, .addN ztbhz ztbhz ztxr]

/-- A model descriptor of a chain model: `0`, then the five words of the chain descriptor at the
address in `sw 97` (the destination pointer `sw 96` advances by `6`). -/
def copyDesc : Stmt :=
  .seq (block [.storeN ztwg ztcwn, .addN ztwg ztwg ztxr])
    (.seq cp1 (.seq cp1 (.seq cp1 (.seq cp1 cp1))))
variable {P : Polygon} {W : ℕ} (c : Config)
theorem cp1_exec (hw : WordsBounded W c)
    (h1 : c.nreg ztxr = 1) (hP : c.nreg ztwg + 1 ≤ W) (hS : c.nreg ztbhz + 1 ≤ W) :
    ∃ c' k, Exec P W cp1 c c' k ∧ k = 4 ∧
      c'.nreg ztwg = c.nreg ztwg + 1 ∧ c'.nreg ztbhz = c.nreg ztbhz + 1 ∧
      c'.nmem = upd c.nmem ztbags (c.nmem (c.nreg ztbhz)) ∧
      ztexf ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold cp1 sw at *
  exec_block
  · simp_all
  · simp_all
  simp_all

/-- **Copying a chain descriptor**: `copyDesc` writes `0` at the destination `D` and the five
words at `S` after it, and advances the destination pointer by `6` (source below destination). -/
theorem copyDesc_exec (hw : WordsBounded W c)
    (h0 : c.nreg ztcwn = 0) (h1 : c.nreg ztxr = 1) (hSD : c.nreg ztbhz + 5 ≤ c.nreg ztwg)
    (hDW : c.nreg ztwg + 6 ≤ W) :
    ∃ c' k, Exec P W copyDesc c c' k ∧ k = 22 ∧
      c'.nreg ztwg = c.nreg ztwg + 6 ∧
      c'.nmem ztbags = 0 ∧
      (∀ j, j < 5 → c'.nmem (c.nreg ztwg + 1 + j) = c.nmem (c.nreg ztbhz + j)) ∧
      (∀ a, a < c.nreg ztwg → c'.nmem a = c.nmem a) ∧
      (∀ a, c.nreg ztwg + 6 ≤ a → c'.nmem a = c.nmem a) ∧
      ztexf ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  set D := c.nreg ztwg with hD
  set S := c.nreg ztbhz with hS
  -- the head: `0` at `D`
  have e₁ := Exec.storeN (P := P) hw ztwg ztcwn
  set c₁ : Config := { c with nmem := upd c.nmem (c.nreg (sw 96)) (c.nreg (sw 90)) } with hc₁
  zud
  have e₂ := Exec.addN (P := P) w₁ ztwg ztwg ztxr (by
    grind)
  set c₂ : Config := { c₁ with nreg := upd c₁.nreg (sw 96) (c₁.nreg (sw 96) + c₁.nreg (sw 91)) }
    with hc₂
  zue
  have r₂ : ztjbk := fun r hr => by
    simp_all
  have d₂ : c₂.nreg ztwg = D + 1 := by_simp_all
  have m₂ : c₂.nmem = upd c.nmem D 0 := by_simp_all
  -- five copies, with the invariant after `k` of them
  have step : ∀ (cc : Config) (k : ℕ), WordsBounded W cc → k < 5 → cc.nreg ztwg = D + 1 + k →
      cc.nreg ztbhz = S + k → cc.nreg ztxr = 1 →
      (∀ a, (a < D + 1 ∨ D + 1 + k ≤ a) → cc.nmem a = c₂.nmem a) →
      (∀ j, j < k → cc.nmem ztjht = c.nmem zthck) →
      ∃ c' k', Exec P W cp1 cc c' k' ∧ k' = 4 ∧ c'.nreg ztwg = D + 1 + zts ∧
        c'.nreg ztbhz = S + zts ∧
        (∀ a, (a < D + 1 ∨ D + 1 + zts ≤ a) → c'.nmem a = c₂.nmem a) ∧
        (∀ j, j < k + 1 → c'.nmem ztjht = c.nmem zthck) ∧
        (∀ r, r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 → c'.nreg r = cc.nreg r) ∧
        c'.rreg = cc.rreg ∧ c'.rmem = cc.rmem ∧ c'.output = cc.output := by
    intro cc k hcc hk hd hs hone hkeep hval
    obtain ⟨c', k', ex, hk', a, b, m, r, x, y, z⟩ := cp1_exec (P := P) cc hcc hone
      by_omega by_omega
    have hread : cc.nmem zttby = c.nmem zttby := by
      rw [hkeep _ ztec, m₂, upd_other _ _ _ by_omega]
    refine ⟨c', k', ex, hk', by_omega, by_omega, fun a' ha' => ?_,
      fun j hj => ?_, r, x, y, z⟩
    · rw [m, hd, hs, upd_other _ _ _ by_omega]
      grind
    · rw [m, hd, hs]
      rcases (Nat.lt_succ_iff.1 hj).lt_or_eq with hj' | rfl
      · zugxh
      · rw [upd_same, hread]
  have hr2 : ztjbk := r₂
  obtain ⟨c₃, k₃, e₃, hk₃, d₃, s₃, m₃, v₃, r₃, x₃, y₃, z₃⟩ :=
    step c₂ 0 w₂ by_omega (by rw [d₂]) by_rfl
      by_grind ztcj (fun j hj => absurd hj by_omega)
  have o3 : ztbacw := by
    rw [r₃ _ by_decide by_decide by_decide,
      hr2 _ by_decide, h1]
  obtain ⟨c₄, k₄, e₄, hk₄, d₄, s₄, m₄, v₄, r₄, x₄, y₄, z₄⟩ :=
    step c₃ 1 e₃.wb_right by_omega d₃ s₃ o3 m₃ v₃
  have o4 : ztbacx := by
    rw [r₄ _ by_decide by_decide by_decide, o3]
  obtain ⟨c₅, k₅, e₅, hk₅, d₅, s₅, m₅, v₅, r₅, x₅, y₅, z₅⟩ :=
    step c₄ 2 e₄.wb_right by_omega d₄ s₄ o4 m₄ v₄
  have o5 : c₅.nreg ztxr = 1 := by
    rw [r₅ _ by_decide by_decide by_decide, o4]
  obtain ⟨c₆, k₆, e₆, hk₆, d₆, s₆, m₆, v₆, r₆, x₆, y₆, z₆⟩ :=
    step c₅ 3 e₅.wb_right by_omega d₅ s₅ o5 m₅ v₅
  have o6 : c₆.nreg ztxr = 1 := by
    rw [r₆ _ by_decide by_decide by_decide, o5]
  obtain ⟨c₇, k₇, e₇, hk₇, d₇, s₇, m₇, v₇, r₇, x₇, y₇, z₇⟩ :=
    step c₆ 4 e₆.wb_right by_omega d₆ s₆ o6 m₆ v₆
  have ex : Exec P W copyDesc c c₇ (1 + 1 + 0 + (k₃ + ztber)) := by
    unfold copyDesc
    exact .seq (Exec.block_cons e₁ ztoww)
      ztyoi
  refine ⟨c₇, _, ex, by_omega, by rw [d₇], ?_, fun j hj => v₇ j hj, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m₇ _ ztec, m₂, upd_same]
  · zuge
    rw [m₇ _ ztec, m₂, upd_other _ _ _ by_omega]
  · zuge
    rw [m₇ _ ztbh, m₂, upd_other _ _ _ by_omega]
  · intro r h96 h97 h98
    rw [r₇ r h96 h97 h98, r₆ r h96 h97 h98, r₅ r h96 h97 h98, r₄ r h96 h97 h98,
      r₃ r h96 h97 h98, hr2 r h96]
  · rw [x₇, x₆, x₅, x₄, x₃]
  · rw [y₇, y₆, y₅, y₄, y₃]
  · rw [z₇, z₆, z₅, z₄, z₃]

/-! ## The copied descriptor describes the chain model -/

/-- **The copied model descriptor** describes the chain model and is well formed. -/
theorem modelDesc_of_copy {m m' : ℕ → ℕ} {bw A E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C) (hEA : E ≤ A)
    (he : ∀ a, a < E → m' a = m a) (h0 : m' A = 0)
    (hc : ∀ j, j < 5 → m' ztcsp = m ztctz) (hE' : A + 6 ≤ E') :
    ModelDescAt m' A zta ztc ∧ ModelDescWF P E' m' A ∧
      ChainDescAt m' ztbo zta H C := by
  zuta
  zudye
  exact ⟨Or.inl ⟨h0, H, C, hC', rfl⟩,
    ⟨by_omega, fun _ => chainWF_copy hwf hC he hc by_omega by_omega⟩, hC'⟩

/-! ## The junction of the descriptors -/

/-- **The junction is determined by its descriptors.** -/
theorem junction_unique {m : ℕ → ℕ} {bl br bw : ℕ} {Q : Polygon} {H H' : Host}
    {J J' : Merge.Junction} (h : JunctionAt m bl br bw Q H J) (h' : JunctionAt m bl br bw Q H' J') :
    J = J' := by
  have hl := NFLoc.chain_eq_of_desc h.1 h'.1
  have hr := NFLoc.chain_eq_of_desc h.2.1 h'.2.1
  obtain ⟨P, s, m₁, m₂, a, b, c⟩ := J
  obtain ⟨P', s', m₁', m₂', a', b', c'⟩ := J'
  simp only [Merge.Junction.left, Merge.Junction.right, Chain.mk.injEq] at hl hr
  simp_all
end
end SweepRam
end Chazelle.Core
namespace Chazelle.Core
namespace SweepRam
open Machine Machine.Stmt Programs SignK SweepPrim
open ShotList (hostAt_agree chainDescAt_copy chainWF_copy)
@[expose] public section
noncomputable def cstR (J : Merge.Junction) (k : ℕ) : ℕ :=
  [6 + WalkEmbed.tpos J.whole J.m₁, 6 + WalkEmbed.tpos J.right 0, Sweep.rL1 J, Sweep.rL2 J,
    Sweep.rδ J].getD k 0

/-- The five constants of the left correspondence. -/
noncomputable def cstL (J : Merge.Junction) (k : ℕ) : ℕ :=
  [6 + WalkEmbed.tpos J.whole ztbv, 6 + WalkEmbed.tpos J.left J.m₁, Sweep.lL1 J,
    Sweep.lL2 J, Sweep.lδ J].getD k 0

/-- The constants of the correspondence of the label chain of side `i`. -/
noncomputable def cstLb (J : Merge.Junction) (i k : ℕ) : ℕ := if i = 0 then cstR J k else cstL J k

/-- The constants of the correspondence of the query chain of side `i`. -/
noncomputable def cstQ (J : Merge.Junction) (i k : ℕ) : ℕ := if i = 0 then cstL J k else cstR J k

/-! ## The blocks -/

/-- The register constants and the inputs of `junConst`. -/
def init0 : Stmt := block [.constN ztcwn 0, .constN ztxr 1, .constN ztcwo 7,
  .constN ztevu 2, .copyN 50200 ztbop, .copyN 50201 ztboq, .copyN 50202 ztjl]

/-- Side `0`: query chain `C₁`, label chain `C₂`. -/
def sideT : Stmt := block [.copyN ztiw ztbop, .copyN zted ztboq, .copyN ztgmi ztea,
  .copyN ztgmj ztbz, .copyN ztfg 50210, .copyN ztbex 50211, .copyN ztyl 50212,
  .copyN ztbsy 50213, .copyN ztbsz 50214, .copyN ztbca 50215, .copyN ztbuy 50216,
  .copyN ztddn 50217, .copyN ztmot 50218, .copyN ztcdx 50219]

/-- Side `1`: query chain `C₂`, label chain `C₁`. -/
def sideF : Stmt := block [.copyN ztiw ztboq, .copyN zted ztbop, .copyN ztgmi ztbz,
  .copyN ztgmj ztea, .copyN ztfg 50215, .copyN ztbex 50216, .copyN ztyl 50217,
  .copyN ztbsy 50218, .copyN ztbsz 50219, .copyN ztbca 50210, .copyN ztbuy 50211,
  .copyN ztddn 50212, .copyN ztmot 50213, .copyN ztcdx 50214]

/-- The side selection. -/
def initSide : Stmt := .ifLtN ztbdl ztxr sideT sideF

/-- The walk lengths `2 m + 7` of the three chain models. -/
def nBlk : Stmt := block [
  .addN ztbhz ztiw ztevu, .loadN ztdpr ztbhz, .addN ztna ztdpr ztdpr,
  .addN ztna ztna ztcwo,
  .addN ztbhz zted ztevu, .loadN ztdpr ztbhz, .addN zthy ztdpr ztdpr,
  .addN zthy zthy ztcwo,
  .addN ztbhz ztjl ztevu, .loadN ztdpr ztbhz, .addN zthg ztdpr ztdpr,
  .addN zthg zthg ztcwo]

/-- Destination pointer at the allocator; the query model descriptor's base. -/
def mdA : Stmt := block [.copyN ztwg ALLOC, .copyN ztbbz ALLOC, .copyN ztbhz ztiw]

/-- The label model descriptor's base. -/
def mdB : Stmt := block [.copyN ztqm ztwg, .copyN ztbhz zted]

/-- Move the allocator past the two descriptors. -/
def mdC : Stmt := block [.copyN ALLOC ztwg]

/-- The two model descriptors. -/
def mdBlk : Stmt := .seq mdA (.seq copyDesc (.seq mdB (.seq copyDesc mdC)))

/-- **Stage 0.** -/
def initS : Stmt := .seq init0 (.seq junConst (.seq initSide (.seq nBlk mdBlk)))

/-! ## Write sets -/

/-- The registers of the sweep band and the input slots of the primitives. -/
def Bs0 (r : ℕ) : Bool := decide ztngb || decide (50100 ≤ r ∧ r < 50220)

/-- `junConst` writes no register of the sweep band. -/
theorem Bjun_sw (j : ℕ) : Bjun ztgc = false := by
  unfold sw; simp only [Bjun, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega

/-- `init0` writes inside `Bs0`. -/
theorem wr_init0 : wr Bs0 init0 = true := by_decide

/-- The registers `init0` writes. -/
def B0 (r : ℕ) : Bool := decide (240090 ≤ r ∧ r < 240094) || decide ztdfd

/-- The registers `initSide` writes. -/
def Bside (r : ℕ) : Bool := decide (240020 ≤ r ∧ r < 240050)

/-- The registers `nBlk` writes. -/
def Bn (r : ℕ) : Bool := decide (240033 ≤ r ∧ r < 240036) || decide (240097 ≤ r ∧ r < 240099)

/-- `init0` writes only `B0`. -/
theorem wr_init0' : wr B0 init0 = true := by_decide
/-- `initSide` writes only `Bside`. -/
theorem wr_initSide' : wr Bside initSide = true := by_decide
/-- `nBlk` writes only `Bn`. -/
theorem wr_nBlk' : wr Bn nBlk = true := by_decide
/-- `initSide` writes inside `Bs0`. -/
theorem wr_initSide : wr Bs0 initSide = true := by_decide
/-- `nBlk` writes inside `Bs0`. -/
theorem wr_nBlk : wr Bs0 nBlk = true := by_decide

/-! ## Execution of the blocks -/
variable {P : Polygon} {W : ℕ} (c : Config) (J : Merge.Junction)
/-- **`init0`**: the register constants and the inputs of `junConst`. -/
theorem init0_exec (hw : WordsBounded W c) (hW : 7 ≤ W) :
    ∃ c' k, Exec P W init0 c c' k ∧ k = 7 ∧
      c'.nreg ztcwn = 0 ∧ c'.nreg ztxr = 1 ∧ c'.nreg ztcwo = 7 ∧ c'.nreg ztevu = 2 ∧
      c'.nreg 50200 = c.nreg ztbop ∧ c'.nreg 50201 = c.nreg ztboq ∧
      c'.nreg 50202 = c.nreg ztjl := by
  unfold init0
  zvmyk at *
  exec_block
  all_goals try omega
  simp

/-- **Side `0`** of the side selection. -/
theorem sideT_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W sideT c c' k ∧ k = 14 ∧
      c'.nreg ztiw = c.nreg ztbop ∧ c'.nreg zted = c.nreg ztboq ∧
      c'.nreg ztgmi = c.nreg ztea ∧ c'.nreg ztgmj = c.nreg ztbz ∧
      c'.nreg ztfg = c.nreg 50210 ∧ c'.nreg ztbex = c.nreg 50211 ∧
      c'.nreg ztyl = c.nreg 50212 ∧ c'.nreg ztbsy = c.nreg 50213 ∧
      c'.nreg ztbsz = c.nreg 50214 ∧ c'.nreg ztbca = c.nreg 50215 ∧
      c'.nreg ztbuy = c.nreg 50216 ∧ c'.nreg ztddn = c.nreg 50217 ∧
      c'.nreg ztmot = c.nreg 50218 ∧ c'.nreg ztcdx = c.nreg 50219 := by
  unfold sideT
  zvmyk at *
  exec_block
  simp

/-- **Side `1`** of the side selection. -/
theorem sideF_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W sideF c c' k ∧ k = 14 ∧
      c'.nreg ztiw = c.nreg ztboq ∧ c'.nreg zted = c.nreg ztbop ∧
      c'.nreg ztgmi = c.nreg ztbz ∧ c'.nreg ztgmj = c.nreg ztea ∧
      c'.nreg ztfg = c.nreg 50215 ∧ c'.nreg ztbex = c.nreg 50216 ∧
      c'.nreg ztyl = c.nreg 50217 ∧ c'.nreg ztbsy = c.nreg 50218 ∧
      c'.nreg ztbsz = c.nreg 50219 ∧ c'.nreg ztbca = c.nreg 50210 ∧
      c'.nreg ztbuy = c.nreg 50211 ∧ c'.nreg ztddn = c.nreg 50212 ∧
      c'.nreg ztmot = c.nreg 50213 ∧ c'.nreg ztcdx = c.nreg 50214 := by
  unfold sideF
  zvmyk at *
  exec_block
  simp

/-- **The side selection**: query chain descriptor, label chain descriptor, normal forms and
correspondence constants of the side `i = sw 7`. -/
theorem initSide_exec (hw : WordsBounded W c)
    (h91 : c.nreg ztxr = 1) (hi : c.nreg ztbdl ≤ 1) :
    ∃ c' k, Exec P W initSide c c' k ∧ k ≤ 16 ∧
      c'.nreg ztiw = c.nreg (sw (c.nreg ztbdl)) ∧
      c'.nreg zted = c.nreg (sw (1 - c.nreg ztbdl)) ∧
      c'.nreg ztgmi = c.nreg (sw (3 + c.nreg ztbdl)) ∧
      c'.nreg ztgmj = c.nreg (sw (4 - c.nreg ztbdl)) ∧
      (∀ k, k < 5 → c'.nreg ztfit =
        c.nreg (if c.nreg ztbdl = 0 then 50210 + k else 50215 + k)) ∧
      (∀ k, k < 5 → c'.nreg ztfiu =
        c.nreg (if c.nreg ztbdl = 0 then 50215 + k else 50210 + k)) := by
  unfold initSide
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with h0 | h1
  · obtain ⟨c', k, ex, hk, a20, a21, a23, a24, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49⟩ :=
      sideT_exec c hw
    refine ⟨c', k + 1, .ifLtN_true by_omega ex, by_omega, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · grind
    grind
  · obtain ⟨c', k, ex, hk, a20, a21, a23, a24, a40, a41, a42, a43, a44, a45, a46, a47, a48, a49⟩ :=
      sideF_exec c hw
    refine ⟨c', k + 2, .ifLtN_false by_omega ex, by_omega, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_⟩
    · simp_all
    · simp_all
    · simp_all
    · simp_all
    · zukrs
    · zukrs

/-- **The walk lengths** `2 m + 7` read from the three chain descriptors. -/
theorem nBlk_exec (hw : WordsBounded W c)
    (h92 : c.nreg ztcwo = 7) (h93 : c.nreg ztevu = 2)
    (a20 : c.nreg ztiw + 2 ≤ W) (a21 : c.nreg zted + 2 ≤ W) (a2 : c.nreg ztjl + 2 ≤ W)
    (m20 : 2 * c.nmem ztzkv + 7 ≤ W) (m21 : 2 * c.nmem ztwpc + 7 ≤ W)
    (m2 : 2 * c.nmem ztzky + 7 ≤ W) :
    ∃ c' k, Exec P W nBlk c c' k ∧ k = 12 ∧
      c'.nreg ztna = 2 * c.nmem ztzkv + 7 ∧
      c'.nreg zthy = 2 * c.nmem ztwpc + 7 ∧
      c'.nreg zthg = 2 * c.nmem ztzky + 7 := by
  unfold nBlk
  zvmyk at *
  exec_block
  all_goals (config_simp; simp only [h92, h93]; omega)

/-- The first block of `mdBlk`. -/
theorem mdA_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdA c c' k ∧ k = 3 ∧ c'.nreg ztwg = c.nreg ALLOC ∧
      c'.nreg ztbbz = c.nreg ALLOC ∧ c'.nreg ztbhz = c.nreg ztiw ∧
      (∀ r, r ≠ sw 96 → r ≠ sw 30 → r ≠ sw 97 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdA ALLOC
  zvmyk at *
  exec_block
  simp_all

/-- The second block of `mdBlk`. -/
theorem mdB_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdB c c' k ∧ k = 2 ∧ c'.nreg ztqm = c.nreg ztwg ∧
      c'.nreg ztbhz = c.nreg zted ∧
      (∀ r, r ≠ sw 31 → r ≠ sw 97 → c'.nreg r = c.nreg r) ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdB
  zvmyk at *
  exec_block
  simp_all

/-- The allocator update of `mdBlk`. -/
theorem mdC_exec (hw : WordsBounded W c) :
    ∃ c' k, Exec P W mdC c c' k ∧ k = 1 ∧ c'.nreg ALLOC = c.nreg ztwg ∧
      ztjn ∧
      c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold mdC ALLOC
  zvmyk at *
  exec_block
  simp_all

/-- **The two model descriptors**: `0` and the query chain descriptor at `A = ALLOC`, `0` and
the label chain descriptor at `A + 6`; the allocator moves to `A + 12`. -/
theorem mdBlk_exec (hw : WordsBounded W c)
    (h90 : c.nreg ztcwn = 0) (h91 : c.nreg ztxr = 1)
    (s20 : c.nreg ztiw + 5 ≤ c.nreg ALLOC) (s21 : c.nreg zted + 5 ≤ c.nreg ALLOC)
    (hA : c.nreg ALLOC + 12 ≤ W) :
    ∃ c' k, Exec P W mdBlk c c' k ∧ k ≤ 50 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 12 ∧ c'.nreg ztbbz = c.nreg ALLOC ∧
      c'.nreg ztqm = c.nreg ALLOC + 6 ∧
      c'.nmem ztm = 0 ∧
      ztxhq ∧
      c'.nmem zthve = 0 ∧
      ztxhr ∧
      zth ∧
      (∀ r, r ≠ ALLOC → r ≠ sw 30 → r ≠ sw 31 → r ≠ sw 96 → r ≠ sw 97 → r ≠ sw 98 →
        c'.nreg r = c.nreg r) ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  zudbg
  have n96 : sw 96 ≠ ALLOC := by_decide
  have n90 : sw 90 ≠ sw 96 ∧ sw 90 ≠ sw 97 ∧ sw 90 ≠ sw 30 ∧ sw 90 ≠ sw 31 ∧ sw 90 ≠ sw 98 := by
    decide
  have n91 : sw 91 ≠ sw 96 ∧ sw 91 ≠ sw 97 ∧ sw 91 ≠ sw 30 ∧ sw 91 ≠ sw 31 ∧ sw 91 ≠ sw 98 := by
    decide
  obtain ⟨c₁, k₁, e₁, hk₁, a96, a30, a97, ar, am, arr, arm, ao⟩ := mdA_exec (P := P) c hw
  rw [← hAd] at a96 a30
  have b90 : c₁.nreg ztcwn = 0 := by_simp_all
  have b91 : c₁.nreg ztxr = 1 := by_simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, d96, d0, dv, dlo, dhi, dr, drr, drm, dout⟩ :=
    copyDesc_exec (P := P) c₁ e₁.wb_right b90 b91 by_omega
      by_omega
  have c90 : c₂.nreg ztcwn = 0 := by_grind
  have c91 : ztbacs := by_grind
  obtain ⟨c₃, k₃, e₃, hk₃, b31, b97, br, bm, brr, brm, bo⟩ := mdB_exec (P := P) c₂ e₂.wb_right
  have g90 : c₃.nreg ztcwn = 0 := by_grind
  have g91 : ztbacw := by_grind
  have g96 : c₃.nreg ztwg = A + 6 := by
    grind
  have g97 : c₃.nreg ztbhz = c.nreg zted := by
    rw [b97, dr _ by_decide by_decide by_decide,
      ar _ by_decide by_decide by_decide]
  obtain ⟨c₄, k₄, e₄, hk₄, f96, f0, fv, flo, fhi, fr, frr, frm, fout⟩ :=
    copyDesc_exec (P := P) c₃ e₃.wb_right g90 g91 by_omega by_omega
  obtain ⟨c₅, k₅, e₅, hk₅, hA5, hr5, hm5, hrr5, hrm5, ho5⟩ := mdC_exec (P := P) c₄ e₄.wb_right
  have ex : Exec P W mdBlk c c₅ _ :=
    .seq e₁ ztbq
  -- memory of the final configuration
  have mem : ∀ a, c₅.nmem a = c₄.nmem a := by_grind
  have m4 : ∀ a, a < A + 6 → c₄.nmem a = c₂.nmem a := fun a ha => by
    grind
  have m2 : ztkny := fun a ha => by
    grind
  refine ⟨c₅, _, ex, by_omega, ?_, ?_, ?_, ?_, fun j hj => ?_, ?_, fun j hj => ?_,
    fun a ha => ?_, fun r h1 h2 h3 h4 h5 h6 => ?_, ?_, ?_, ?_⟩
  · omega
  · rw [hr5 _ by_decide,
      fr _ by_decide by_decide by_decide,
      br _ by_decide by_decide,
      dr _ by_decide by_decide by_decide, a30]
  · rw [hr5 _ by_decide,
      fr _ by_decide by_decide by_decide, b31, d96, a96]
  · grind
  · grind
  · grind
  · rw [mem, ← g96, fv j hj, g97, bm, dlo _ by_omega, am]
  · grind
  · grind
  · grind
  · grind
  grind

/-! ## The state after stage 0 -/

/-- A chain descriptor below `E` survives a change of the memory at or above `E`. -/
theorem chainDesc_keep {m m' : ℕ → ℕ} {bw E E' : ℕ} {H : Host} {C : Chain}
    (hwf : ChainWF P E m bw) (hC : ChainDescAt m bw zta H C)
    (he : ∀ a, a < E → m' a = m a) (hEE : E ≤ E') :
    ChainDescAt m' bw zta H C ∧ ChainWF P E' m' bw := by
  obtain ⟨hb, hwf'⟩ := hwf
  zueaf
  have hc : ∀ j, j < 5 → m' _ = m ztctz := fun j hj => he _ by_omega
  exact ⟨chainDescAt_copy hC hEb he hc, chainWF_copy ⟨hb, hwf'⟩ hC he hc by_omega hEE⟩

/-- **The state after stage 0** (entry configuration `c₀`, junction `J` on host `H`, side
`i = sw 7`). -/
def St0 (P : Polygon) (c₀ c : Config) (H : Host) (J : Merge.Junction) : Prop :=
  c.nreg ztcwn = 0 ∧ c.nreg ztxr = 1 ∧ c.nreg ztcwo = 7 ∧ c.nreg ztevu = 2 ∧
    (∀ j, j < 20 → c.nreg ztgc = c₀.nreg ztgc) ∧
    c.nreg ALLOC = c₀.nreg ALLOC + 12 ∧
    JunctionAt c.nmem ztxcj ztxck ztwzq zta H J ∧
    JunctionWF P ztm c.nmem ztxcj ztxck ztwzq ∧
    ChainDescAt c.nmem ztxwd zta H ztbart ∧
    ChainWF P ztm c.nmem ztxwd ∧
    ChainDescAt c.nmem ztxnj zta H ztbaru ∧
    ChainWF P ztm c.nmem ztxnj ∧
    c.nreg ztgmi = c₀.nreg (sw (3 + c₀.nreg ztbdl)) ∧
    c.nreg ztgmj = c₀.nreg (sw (4 - c₀.nreg ztbdl)) ∧
    (∀ k, k < 5 → c.nreg ztfit = cstLb J ztxwh k) ∧
    (∀ k, k < 5 → c.nreg ztfiu = cstQ J ztxwh k) ∧
    c.nreg ztna = 2 * (sideChain J ztxwh).m + 7 ∧
    c.nreg zthy = 2 * (sideChain J ztydk).m + 7 ∧
    c.nreg zthg = 2 * J.whole.m + 7 ∧
    ModelDescAt c.nmem ztxwc zta (chainModel ztbart) ∧
    ModelDescWF P ztm c.nmem ztxwc ∧
    ModelDescAt c.nmem ztxgo zta
      (chainModel ztbaru) ∧
    ModelDescWF P ztm c.nmem ztxgo

/-- The side facts of the entry configuration. -/
theorem side_desc {m : ℕ → ℕ} {E b0 b1 b2 : ℕ} {H : Host} {J : Merge.Junction}
    (hJ : JunctionAt m b0 b1 b2 zta H J) (wl : ChainWF P E m b0) (wr' : ChainWF P E m b1)
    {t : ℕ} (ht : t ≤ 1) :
    ChainDescAt m ztmls zta H (sideChain J t) ∧
      ChainWF P E m ztmls := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 ht with rfl | rfl
  · simp only [sideChain, ↓reduceIte]; exact ⟨hJ.1, wl⟩
  · simp only [sideChain, one_ne_zero, ↓reduceIte]; exact ⟨hJ.2.1, wr'⟩

/-- A side chain has at most as many edges as the union. -/
theorem sideChain_m_le (t : ℕ) : (sideChain J t).m ≤ J.whole.m := by
  unfold sideChain
  split
  · simp
  simp

/-- Reading the descriptor register of side `t ≤ 1`. -/
theorem sw_side {c : Config} {t : ℕ} (ht : t ≤ 1) :
    c.nreg (sw t) = c.nreg (if t = 0 then sw 0 else sw 1) := by
  grind

/-- `junConst` writes inside `Bs0`. -/
theorem wr_junConst' : wr Bs0 junConst = true := by_decide

/-- The correspondence constants selected by the side. -/
theorem cstLb_eq {i : ℕ} (hi : i ≤ 1) (m : ℕ → ℕ)
    (h : ∀ k, k < 5 → m ztstu = cstR J k) (h' : ∀ k, k < 5 → m ztstv = cstL J k)
    {k : ℕ} (hk : k < 5) :
    m (if i = 0 then 50210 + k else 50215 + k) = cstLb J i k ∧
      m (if i = 0 then 50215 + k else 50210 + k) = cstQ J i k := by
  zueve
  · tauto
  tauto

/-- **Stage 0.** -/
theorem initS_exec (hw : WordsBounded W c) {H : Host}
    {J : Merge.Junction} (hi : c.nreg ztbdl ≤ 1)
    (hJ : JunctionAt c.nmem ztxcj ztxck ztwzq zta H J)
    (hwf : JunctionWF P ztm c.nmem ztxcj ztxck ztwzq)
    (hWm : 2 * J.whole.m + 7 ≤ W) (hroom : c.nreg ALLOC + 220 ≤ W) :
    ∃ c' k, Exec P W initS c c' k ∧ k ≤ 220 ∧ St0 P c c' H J ∧
      Frame {bSweep, bLocate} c c' k := by
  set i := c.nreg ztbdl with hi_def
  set A := c.nreg ALLOC with hA_def
  zuflb
  have hl5 := wl.1
  have hr5 := wr'.1
  have hw5 := ww.1
  zuehq
  have mle := sideChain_m_le J
  zudpo
  -- 0.1
  obtain ⟨c₁, k₁, e₁, hk₁, u90, u91, u92, u93, u200, u201, u202⟩ :=
    init0_exec (P := P) c hw by_omega
  have G₁ := exec_frameB e₁ wr_init0'
  have ulo : ∀ j, j < 20 → c₁.nreg _ = c.nreg ztgc := fun j hj => G₁.1 _ (by
    unfold sw; simp only [B0, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have F₁ := exec_frameB e₁ wr_init0
  have A1 := F₁.1 ALLOC by_rfl
  have M1 := F₁.2.2.1
  have hJ1 : JunctionAt c₁.nmem ztghz (c₁.nreg 50201) (c₁.nreg 50202) zta H J := by
    simp_all
  -- 0.2: `junConst`
  obtain ⟨c₂, k₂, e₂, hk₂, p₂, -⟩ := junConst_meets P W c₁ e₁.wb_right
    ⟨by_omega, by_omega, by_omega, H, J, hJ1, hWm⟩
    by_grind
  replace hk₂ : k₂ ≤ 120 := hk₂
  obtain ⟨v10, v11, v12, v13, v14, v15, v16, v17, v18, v19⟩ := p₂ H J hJ1
  have J₂ := exec_frameB e₂ wr_junConst
  have F₂ := exec_frameB e₂ wr_junConst'
  have k₂s : ∀ j, c₂.nreg _ = c₁.nreg _ := fun j => J₂.1 _ (Bjun_sw j)
  have A2 : ztlyb := by
    rw [J₂.1 ALLOC by_rfl, A1]
  have M2 : ztckc := by rw [J₂.2.2.1, M1]
  have cR : ∀ k, k < 5 → c₂.nreg ztstu = cstR J k := fun k hk => by
    interval_cases k <;> simp only [cstR] <;> assumption
  have cL : ∀ k, k < 5 → c₂.nreg ztstv = cstL J k := fun k hk => by
    interval_cases k <;> simp only [cstL] <;> assumption
  -- 0.3: the side
  have i2 : c₂.nreg ztbdl = i := by rw [k₂s, ulo _ by_omega]
  have o91 : ztbacs := by rw [k₂s, u91]
  obtain ⟨c₃, k₃, e₃, hk₃, t20, t21, t23, t24, t40, t45⟩ :=
    initSide_exec (P := P) c₂ e₂.wb_right o91 by_omega
  have G₃ := exec_frameB e₃ wr_initSide'
  have tlo : ∀ r, (r < sw 20 ∨ sw 50 ≤ r) → c₃.nreg r = c₂.nreg r := fun r hr => G₃.1 r (by
    unfold sw at hr; simp only [Bside, decide_eq_false_iff_not]; omega)
  rw [i2] at t20 t21 t23 t24 t40 t45
  have F₃ := exec_frameB e₃ wr_initSide
  have A3 : c₃.nreg ALLOC = A := by rw [F₃.1 ALLOC by_rfl, A2]
  have M3 : ztckd := by rw [F₃.2.2.1, M2]
  have lo3 : ∀ j, j < 20 → c₃.nreg ztgc = c.nreg _ := fun j hj => by
    rw [tlo _ ztbaes, k₂s, ulo _ by_omega]
  have hi1 : 1 - i ≤ 1 := by_omega
  obtain ⟨dq, wq⟩ := side_desc hJ wl wr' hi
  obtain ⟨dl, wl'⟩ := side_desc hJ wl wr' hi1
  have q20 : c₃.nreg ztiw = if i = 0 then c.nreg ztbop else c.nreg ztboq := by
    rw [t20, k₂s, ulo _ by_omega, sw_side hi]; split <;> rfl
  have q21 : c₃.nreg zted = if 1 - i = 0 then c.nreg ztbop else c.nreg ztboq := by
    rw [t21, k₂s, ulo _ by_omega, sw_side hi1]; split <;> rfl
  -- 0.4: the walk lengths
  have x92 : c₃.nreg ztcwo = 7 := by
    rw [tlo _ ztbcz, k₂s, u92]
  have x93 : c₃.nreg ztevu = 2 := by
    rw [tlo _ ztbcz, k₂s, u93]
  have mq : c.nmem _ = (sideChain J i).m :=
    dq.2.2.2.1
  have ml : c.nmem _ =
      (sideChain J _).m := dl.2.2.2.1
  have mw : ztunk := hJ.2.2.2.2.2.1
  have bq := wq.1
  have bl := wl'.1
  have mq' := mle i
  have ml' := mle (1 - i)
  obtain ⟨c₄, k₄, e₄, hk₄, n33, n34, n35⟩ := nBlk_exec (P := P) c₃ e₃.wb_right x92 x93
    by_omega by_omega (by rw [lo3 _ by_omega]; omega)
    (by rw [M3, q20, mq]; omega) (by rw [M3, q21, ml]; omega)
    (by rw [M3, lo3 _ by_omega, mw]; omega)
  have F₄ := exec_frameB e₄ wr_nBlk
  have G₄ := exec_frameB e₄ wr_nBlk'
  have nlo : ∀ r, r ≠ sw 33 → r ≠ sw 34 → r ≠ sw 35 → r ≠ sw 97 → r ≠ sw 98 →
      c₄.nreg r = c₃.nreg r := fun r h1 h2 h3 h4 h5 => G₄.1 r (by
    unfold sw at h1 h2 h3 h4 h5
    simp only [Bn, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega)
  have A4 : c₄.nreg ALLOC = A := by rw [F₄.1 ALLOC by_rfl, A3]
  have M4 : zteid := by rw [F₄.2.2.1, M3]
  have k4 : ∀ j, j ≠ 33 → j ≠ 34 → j ≠ 35 → j ≠ 97 → j ≠ 98 → c₄.nreg _ = c₃.nreg ztgc :=
    fun j h1 h2 h3 h4 h5 => nlo _ ztce ztce
      ztce ztce ztce
  -- 0.5: the model descriptors
  have y90 : c₄.nreg ztcwn = 0 := by
    rw [k4 _ by_omega by_omega by_omega by_omega by_omega,
      tlo _ ztbcz, k₂s, u90]
  have y91 : ztbacx := by
    rw [k4 _ by_omega by_omega by_omega by_omega by_omega,
      tlo _ ztbcz, k₂s, u91]
  have y20 : c₄.nreg ztiw = if i = 0 then c.nreg ztbop else c.nreg ztboq := by
    rw [k4 _ by_omega by_omega by_omega by_omega by_omega, q20]
  have y21 : c₄.nreg zted = if 1 - i = 0 then c.nreg ztbop else c.nreg ztboq := by
    rw [k4 _ by_omega by_omega by_omega by_omega by_omega, q21]
  obtain ⟨c₅, k₅, e₅, hk₅, zA, z30, z31, z0, zq, z6, zl, zlo, zr, zrr, zrm, zo⟩ :=
    mdBlk_exec (P := P) c₄ e₄.wb_right y90 y91 by_omega
      by_omega by_omega
  rw [A4] at zA z30 z31 z0 zq z6 zl zlo
  rw [y20, M4] at zq
  rw [y21, M4] at zl
  rw [M4] at zlo
  have k5 : ∀ j, j ≠ 30 → j ≠ 31 → j ≠ 96 → j ≠ 97 → j ≠ 98 → c₅.nreg _ = c₄.nreg _ :=
    fun j h1 h2 h3 h4 h5 => zr _ ztvzi ztce ztce
      ztce ztce ztce
  have ex : Exec P W initS c c₅ _ :=
    .seq e₁ ztbq
  -- register reading through stages 0.4 and 0.5
  have r45 : ∀ j, j < 30 ∨ (35 < j ∧ j < 96) → c₅.nreg ztgc = c₃.nreg _ := fun j hj => by
    rw [k5 _ by_omega by_omega by_omega by_omega by_omega,
      k4 _ by_omega by_omega by_omega by_omega by_omega]
  have lo5 : ∀ j, j < 20 → c₅.nreg ztgc = c.nreg _ := fun j hj => by
    rw [r45 _ by_omega, lo3 _ hj]
  -- memory
  have keep := fun {b : ℕ} {C : Chain} (hw' : ChainWF P A c.nmem b)
      (hC : ChainDescAt c.nmem b _ H C) =>
    chainDesc_keep (E' := A + 12) hw' hC zlo by_omega
  obtain ⟨j0, w0⟩ := keep wl hJ.1
  obtain ⟨j1, w1⟩ := keep wr' hJ.2.1
  obtain ⟨j2, w2⟩ := keep ww hJ.2.2
  obtain ⟨jq, wq5⟩ := keep wq dq
  obtain ⟨jl, wl5⟩ := keep wl' dl
  obtain ⟨mdq, mwq, -⟩ := modelDesc_of_copy (E' := A + 12) wq dq le_rfl zlo z0
    (fun j hj => zq j hj) by_omega
  obtain ⟨mdl, mwl, -⟩ := modelDesc_of_copy (A := A + 6) (E' := A + 12) wl' dl by_omega zlo z6
    (fun j hj => zl j hj) by_omega
  refine ⟨c₅, _, ex, by_omega, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, lo5, zA, ?_, ztfh, ?_, ?_, ?_, ?_, ?_, ?_,
      fun k hk => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r45 _ by_omega, tlo _ ztbcz, k₂s, u90]
    · rw [r45 _ by_omega, tlo _ ztbcz, k₂s, u91]
    · rw [r45 _ by_omega, x92]
    · rw [r45 _ by_omega, x93]
    · rw [lo5 0 by_omega, lo5 1 by_omega, lo5 2 by_omega]; exact ztrdq
    · rw [lo5 0 by_omega, zA]; exact w0
    · rw [lo5 1 by_omega, zA]; exact w1
    · rw [lo5 2 by_omega, zA]; exact w2
    · zujap
      rw [lo5 2 by_omega] at hH'
      have hb : c₅.nmem _ = c.nmem ztwzq := zlo _ by_omega
      zucpv

      have hH : HostAt c₅.nmem _ H := hostAt_agree hJ.2.2.1 hEb zlo
      zugcg
      zulyy
    · rw [r45 _ by_omega, q20]; exact jq
    · rw [r45 _ by_omega, q20, zA]; omega
    · rw [r45 _ by_omega, q21]; exact jl
    · rw [r45 _ by_omega, q21, zA]; omega
    · rw [r45 _ by_omega, t23, k₂s, ulo _ by_omega]
    · rw [r45 _ by_omega, t24, k₂s, ulo _ by_omega]
    · rw [r45 _ by_omega, t40 k hk]
      exact (cstLb_eq J hi c₂.nreg cR cL hk).1
    · rw [r45 _ by_omega, t45 k hk]
      exact (cstLb_eq J hi c₂.nreg cR cL hk).2
    · rw [k5 _ by_omega by_omega by_omega by_omega by_omega, n33, M3, q20, mq]
    · rw [k5 _ by_omega by_omega by_omega by_omega by_omega, n34, M3, q21, ml]
    · rw [k5 _ by_omega by_omega by_omega by_omega by_omega, n35, M3,
        lo3 _ by_omega, mw]
    · rw [z30]; omega
    · rw [z30, zA]; omega
    · rw [z31]; omega
    · rw [z31, zA]; omega
  · -- the frame
    have F4 := F₁.trans ztpyz
    have hB : ∀ r, bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) → Bs0 r = false := by
      zuz
      simp only [bandOf, bSweep, bLocate, Finset.mem_insert, Finset.mem_singleton] at hr
      simp only [Bs0, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
    have hsw : ∀ r j, bandOf r ∉ ({bSweep, bLocate} : Finset ℕ) → j < 10000 → r ≠ sw j := by
      intro r j hr hj h
      zuhbg
      zvmwc; unfold sw
      simp only [bandOf, bSweep, bLocate, Finset.mem_insert, Finset.mem_singleton]; omega
    zuife
    · rw [zr r hra (hsw r 30 hr by_omega) (hsw r 31 hr by_omega) (hsw r 96 hr by_omega)
        (hsw r 97 hr by_omega) (hsw r 98 hr by_omega), F4.1 r ztfsg]
    · rw [zrr, F4.2.1 r ztfsg]
    · rw [zlo a ha]
    · rw [zrm, F4.2.2.2.1]
    · rw [zo, F4.2.2.2.2]
    · omega
    omega
end
end SweepRam
end Chazelle.Core
namespace Chazelle.Core
@[expose] public section
open Chazelle.Machine (Stmt)
namespace SweepEv
open SweepRam

/-- **The stage-0 state of side `0`** (`SweepRam.St0` for `c₀.nreg (sw 7) = 0`, without the entry
configuration): the register constants, the descriptors of `C₁` (`sw 20`) and `C₂` (`sw 21`), the
normal forms (`sw 23 = sw 3`, `sw 24 = sw 4`), the constants of the right correspondence
(`sw 40 … 44`) and of the left one (`sw 45 … 49`), the walk lengths (`sw 33 … 35`) and the model
descriptors of `C₁` (`sw 30`) and `C₂` (`sw 31`). -/
def St0S (P : Polygon) (c : Config) (H : Host) (J : Merge.Junction) : Prop :=
  c.nreg ztcwn = 0 ∧ c.nreg ztxr = 1 ∧ c.nreg ztcwo = 7 ∧ c.nreg ztevu = 2 ∧
    JunctionAt c.nmem ztxcj ztxck ztwzq zta H J ∧
    JunctionWF P ztm c.nmem ztxcj ztxck ztwzq ∧
    ChainDescAt c.nmem ztxwd zta H J.left ∧
    ChainWF P ztm c.nmem ztxwd ∧
    ChainDescAt c.nmem ztxnj zta H J.right ∧
    ChainWF P ztm c.nmem ztxnj ∧
    c.nreg ztgmi = c.nreg ztea ∧ c.nreg ztgmj = c.nreg ztbz ∧
    (∀ k, k < 5 → c.nreg ztfit = cstR J k) ∧
    (∀ k, k < 5 → c.nreg ztfiu = cstL J k) ∧
    c.nreg ztna = 2 * J.left.m + 7 ∧ c.nreg zthy = 2 * J.right.m + 7 ∧
    c.nreg zthg = 2 * J.whole.m + 7 ∧
    ModelDescAt c.nmem ztxwc zta ztbw ∧
    ModelDescWF P ztm c.nmem ztxwc ∧
    ModelDescAt c.nmem ztxgo zta ztj ∧
    ModelDescWF P ztm c.nmem ztxgo

/-- `St0` of side `0` gives `St0S`. -/
theorem st0S_of_st0 {P : Polygon} {c₀ c : Config} {H : Host} {J : Merge.Junction}
    (h : St0 P c₀ c H J) (h7 : c₀.nreg ztbdl = 0) : St0S P c H J := by
  obtain ⟨h90, h91, h92, h93, hlo, -, hJ, hwf, d20, w20, d21, w21, h23, h24, h40, h45, h33, h34,
    h35, d30, w30, d31, w31⟩ := h
  simp only [h7, sideChain, ↓reduceIte, Nat.sub_zero, one_ne_zero, Nat.add_zero] at *
  refine ⟨h90, h91, h92, h93, hJ, hwf, d20, w20, d21, w21, ?_, ?_, fun k hk => ?_,
    fun k hk => ?_, h33, h34, h35, d30, w30, d31, w31⟩
  · simp_all
  · simp_all
  · tauto
  tauto

/-- **The precondition of stages 2 and 3.** -/
def Pre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztefy ztm ∧
    rd c bSweep 5 ≤ X.cap P c.nmem ztefy ∧
    JunctionWF P ztm c.nmem ztcds ztcdt ztcdu ∧
    ∃ H J N₁ N₂, JunctionAt c.nmem ztcds ztcdt ztcdu zta H J ∧
      J.P.Simple ∧
      Ok P ztbw ∧ Ok P ztj ∧
      NFWithin c.nmem ztwb ztm N₁ ∧
      NFWithin c.nmem ztrl ztm N₂ ∧
      IsNF ztbw zta N₁ ∧ IsNF ztj zta N₂ ∧
      (chainModel J.left).DegLe ztwjx ztbwd ∧
      (chainModel J.right).DegLe ztwis ztbwd ∧
      (chainModel J.left).Semigranular ztwjx ztbro ∧
      (chainModel J.right).Semigranular ztwis ztbro ∧
      St0S P c H J

/-- **Word-level facts of a stored position** `(e, h)` of the walk of `C`: an edge of the walk, a
proper position, and a height code `0` only on the tour (so that `offCmp`, `arrivalPos` and
`absKey` accept it). -/
def PosW (P : Polygon) (J : Merge.Junction) (e h : ℕ) : Prop :=
  e < (chainModel J.whole).W.n ∧ ProperPos ztbm zta P.n ztcq ∧
    (h = 0 → 6 ≤ e)

/-- **The outputs of stages 2 and 3** for one junction and normal form `N₂` of `S₂`: the stops,
the event log and the endpoint table, in the memory of `c'` at the bases read in `c'`, with the
word-level facts of the stored positions, codes and labels. -/
def Out (P : Polygon) (J : Merge.Junction) (N₂ : NF) (c' : Config) : Prop :=
  ∃ (rs : List ztcf) (ls : List ztck),
    rs.length = rd c' bSweep 201 ∧ Sweep.StopRecsAt c'.nmem (rd c' bSweep 200) rs ∧
    Sweep.StopsOK J ztwis (Sweep.stopsOf J zta N₂ rs) ∧
    (∀ r ∈ rs, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 2 ∧ r.2.2.2.2 ≤ 1 ∧
      zthkb) ∧
    ls.length = rd c' bSweep 301 ∧ Sweep.LogRecsAt c'.nmem (rd c' bSweep 300) ls ∧
    Sweep.LogOK J ztwis (Sweep.logOf J zta N₂ ls) ∧
    (∀ r ∈ ls, PosW P J r.1 r.2.1 ∧ r.2.2.1 ≤ 4 ∧
      ztndi ∧ ztndq ∧
      ztnfj ∧ ztnge) ∧
    Sweep.TabOK J zta N₂ (Sweep.tabOf J zta c'.nmem (rd c' bSweep 302)) ∧
    ∀ j, j < 2 * N₂.nChords → c'.nmem ztmni ≤ 1 ∧
      (c'.nmem ztmni = 1 →
        PosW P J (c'.nmem (rd c' bSweep 302 + 3 * j + 1)) (c'.nmem (rd c' bSweep 302 + 3 * j + 2)))

/-- **The postcondition of stages 2 and 3.** -/
def Post (P : Polygon) (c c' : Config) : Prop :=
  (∀ j, j < 200 → c'.nreg ztgc = c.nreg ztgc) ∧
    c.nreg ALLOC ≤ rd c' bSweep 200 ∧
    rd c' bSweep 200 + 5 * rd c' bSweep 201 ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ rd c' bSweep 300 ∧
    rd c' bSweep 300 + 7 * rd c' bSweep 301 ≤ c'.nreg ALLOC ∧
    c.nreg ALLOC ≤ rd c' bSweep 302 ∧
    rd c' bSweep 302 + 3 * ztzjq ≤ c'.nreg ALLOC ∧
    rd c' bSweep 201 ≤ 16 * ztwou ∧
    rd c' bSweep 301 ≤ 16 * ztwou ∧
    ∀ H J N₂, JunctionAt c.nmem ztcds ztcdt ztcdu zta H J →
      NFAt c.nmem ztrl N₂ → IsNF ztj zta N₂ →
      Out P J N₂ c'

/-- **The cost of stages 2 and 3.** -/
def cost (κ F : ℕ → ℕ) (_P : Polygon) (c : Config) : ℕ :=
  κ ztbwd * ztwou *
    (F ztbro + Nat.clog 2 ztwou + 1)
end SweepEv

/-- **WP-D, stages 2 and 3 of the sweep** (finding S-1): the stops, the event log with label sets
and the endpoint table of the sweep along the `C₁` part of the walk of `C`, for every shooter. -/
def SweepEvSpec : Prop :=
  ∃ (mk : Stmt → Stmt) (κ : ℕ → ℕ), ∀ (sh : Stmt) (Bs : Finset ℕ) (F : ℕ → ℕ)
    (X : MemCtx) (Ok : Polygon → Model → Prop), X.CapLocal → Bs ⊆ oracleBands →
    ShooterOK sh Bs F X Ok →
    Meets ztkbc ztdwg (SweepEv.Pre X Ok) SweepEv.Post (SweepEv.cost κ F)
end
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam
@[expose] public section
def regI (m : ℕ → ℕ) : Instr → ztjx → ztjx
  | .constN r k, f => upd f r k
  | .copyN r a, f => upd f r ztbaa
  | .addN r a b, f => upd f r ztqmu
  | .subN r a b, f => upd f r ztqmv
  | .loadN r a, f => upd f r ztbaia
  | _, f => f

/-- The register effect of a block. -/
def regB (m : ℕ → ℕ) : List Instr → ztjx → ztjx
  | [], f => f
  | i :: l, f => regB m l ztefz

/-- The destination register of a covered instruction. -/
def dstI : Instr → ℕ
  | .constN r _ => r
  | .copyN r _ => r
  | .addN r _ _ => r
  | .subN r _ _ => r
  | .loadN r _ => r
  | _ => 0
theorem regI_other (m f : ℕ → ℕ) (i : Instr) {q : ℕ} (hq : dstI i ≠ q) :
    regI m i f q = f q := by
  cases i <;> simp only [regI, dstI] at hq ⊢ <;> exact upd_other _ _ _ ztvbm

/-- **A block leaves the registers it does not write.** -/
theorem regB_other (m : ℕ → ℕ) : ∀ (l : List Instr) (f : ℕ → ℕ) {q : ℕ},
    ztluv → regB m l f q = f q
  | [], _, _, _ => rfl
  | i :: l, f, q, h => by
    zudvf

/-! ## Registers and bands -/

/-- The bands of the sweep (and of the procedures it inlines). -/
def ioBands : Finset ℕ := sweepBands ∪ oracleBands

/-- A fixed register of the answer stage: `sw 0 … 699`. -/
def IFix (q : ℕ) : Prop := 240000 ≤ q ∧ q < 240700

/-- A scratch register of the answer stage: band `bSweep` from `sw 700` on, or an oracle band. -/
def IScr (r : ℕ) : Prop := (240700 ≤ r ∧ r < 250000) ∨ bandOf r ∈ oracleBands
variable {r : ℕ} {s : Stmt} {a b : ℕ} {t e : Stmt} {K : ℕ} {Q : Config → Prop} {c' : Config} {i : Instr}
theorem band_sw (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r = bSweep := by
  unfold bandOf bSweep; omega
theorem bSweep_mem : bSweep ∈ ioBands := by_decide
theorem oracle_sub : oracleBands ⊆ ioBands := Finset.subset_union_right
theorem alloc_not_io : bandOf ALLOC ∉ ioBands := by_decide
theorem fix_not_scr {q : ℕ} (h : IFix q) : ¬ IScr q := by
  rintro (h' | h')
  · unfold IFix at h; omega
  · unfold IFix at h
    rw [band_sw by_omega by_omega] at h'
    tauto
theorem alloc_not_scr : ¬ IScr ALLOC := by
  zunp
  · tauto
  tauto
theorem scr_band (h : IScr r) : bandOf r ∈ ioBands := by
  zuy
  · rw [band_sw by_omega h.2]; decide
  tauto

/-! ## The invariant and the run steps -/

/-- **The invariant of the answer stage** relative to `c₀`. -/
structure IInv (W : ℕ) (c₀ c : Config) : Prop where
  hw : WordsBounded W c
  hin : ∀ q, IFix q → c.nreg q = c₀.nreg q
  hA : c₀.nreg ALLOC ≤ c.nreg ALLOC
  hm : ∀ a, a < c₀.nreg ALLOC → c.nmem a = c₀.nmem a
  hrm : ∀ a, a < c₀.nreg ALLOC → c.rmem a = c₀.rmem a

/-- **The relative frame** of a step: registers outside the bands unchanged (except the
allocator), nothing emitted, the allocator raised by at most the step count. -/
def IFr (c c' : Config) (k : ℕ) : Prop :=
  ztgnj ∧
    ztimy ∧ c'.output = c.output ∧
    c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + k
theorem IFr.refl (c : Config) (k : ℕ) : IFr c c k :=
  ⟨by_omega, by_simp_all, rfl, le_rfl, by_omega⟩
theorem IFr.trans {c c₁ c₂ : Config} {k₁ k₂ : ℕ} (h₁ : IFr c c₁ k₁) (h₂ : IFr c₁ c₂ k₂) :
    IFr c c₂ ztbct := by
  obtain ⟨r₁, rr₁, o₁, a₁, b₁⟩ := h₁
  obtain ⟨r₂, rr₂, o₂, a₂, b₂⟩ := h₂
  exact ⟨by_simp_all, by_simp_all,
    o₂.trans o₁, a₁.trans a₂, by_omega⟩
theorem IFr.mono {c c' : Config} {k k' : ℕ} (h : IFr c c' k) (hk : k ≤ k') : IFr c c' k' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2.2.2.2; omega⟩
theorem IFr.of_frame {B : Finset ℕ} {c c' : Config} {k : ℕ} (h : Frame B c c' k)
    (hB : B ⊆ ioBands) : IFr c c' k :=
  ⟨fun r hr hra => h.1 r by_grind hra, fun r hr => h.2.1 r by_grind,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- **A run step of the answer stage.** -/
def IRS (P : Polygon) (W : ℕ) (c₀ : Config) (s : Stmt) (c : Config) (K : ℕ)
    (Q : Config → Prop) : Prop :=
  ∃ c' k, Exec P W s c c' k ∧ k ≤ K ∧ IInv W c₀ c' ∧ IFr c c' k ∧ Q c'
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem IRS.mono {K K' : ℕ} {Q Q' : Config → Prop} (h : IRS P W c₀ s c K Q)
    (hK : K ≤ K') (hQ : ∀ c', Q c' → Q' c') : IRS P W c₀ s c K' Q' := by
  zums
  exact ⟨c', k, ex, by_omega, hI, hfr, by_simp_all⟩
theorem IRS.seq {s t : Stmt} {K₁ K₂ : ℕ} {Q₁ Q₂ : Config → Prop} (h₁ : IRS P W c₀ s c K₁ Q₁)
    (h₂ : ∀ c₁, IInv W c₀ c₁ → c.nreg ALLOC ≤ c₁.nreg ALLOC → c₁.nreg ALLOC ≤ c.nreg ALLOC + K₁ →
      Q₁ c₁ → IRS P W c₀ t c₁ K₂ Q₂) : IRS P W c₀ (.seq s t) c (K₁ + K₂) Q₂ := by
  obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hfr₁, hq₁⟩ := h₁
  obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := h₂ c₁ hI₁ hfr₁.2.2.2.1
    (by have := hfr₁.2.2.2.2; omega) hq₁
  exact ⟨c', k₁ + k₂, .seq e₁ e₂, by_omega, hI', hfr₁.trans hfr₂, hq⟩
theorem IRS.ifT
    (ht : c.nreg a < c.nreg b) (h : IRS P W c₀ t c K Q) :
    IRS P W c₀ ztva c ztnu Q := by
  zums
  exact ⟨c', k + 1, .ifLtN_true ht ex, by_omega, hI, hfr.mono by_omega, hq⟩
theorem IRS.ifF
    (ht : ¬ c.nreg a < c.nreg b) (h : IRS P W c₀ e c K Q) :
    IRS P W c₀ ztva c ztnu Q := by
  zums
  exact ⟨c', k + 2, .ifLtN_false ht ex, by_omega, hI, hfr.mono by_omega, hq⟩
theorem IRS.ite
    (ht : c.nreg a < c.nreg b → IRS P W c₀ t c K Q)
    (he : ¬ c.nreg a < c.nreg b → IRS P W c₀ e c K Q) :
    IRS P W c₀ ztva c ztnu Q := by
  zubjy
  · exact IRS.ifT h (ht h)
  · exact IRS.ifF h (he h)
theorem IRS.skip (hI : IInv W c₀ c) (hq : Q c) :
    IRS P W c₀ .skip c K Q :=
  ⟨c, 0, .skip hI.hw, by_omega, hI, IFr.refl c 0, hq⟩

/-- A register-only change on scratch registers keeps the invariant. -/
theorem IInv.regs {k : ℕ} (hI : IInv W c₀ c) (hw : WordsBounded W c')
    (hr : ∀ r, ¬ IScr r → c'.nreg r = c.nreg r)
    (hrr : c'.rreg = c.rreg) (hm : c'.nmem = c.nmem) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) : IInv W c₀ c' ∧ IFr c c' k := by
  have hA := hr ALLOC alloc_not_scr
  refine ⟨⟨hw, fun q hq => (hr q (fix_not_scr hq)).trans ztfsi, by zvmze; exact hI.hA,
    fun a ha => by zvmwi; exact hI.hm a ha, fun a ha => by zvnmc; exact hI.hrm a ha⟩,
    fun r hr' _ => hr r ztmjn, by_simp_all, ho, by_omega,
    by omega⟩

/-- **One register instruction** on a scratch register. -/
theorem IRS.reg {r v : ℕ} (hI : IInv W c₀ c) (hr : IScr r)
    (hex : Exec P W ztbgj c { c with nreg := upd c.nreg r v } 1) :
    IRS P W c₀ ztbgj c 1 (fun c' => c' = { c with nreg := upd c.nreg r v }) := by
  obtain ⟨hI', hfr⟩ := hI.regs (k := 1) hex.wb_right
    (fun q h => by
      zuby
      grind) rfl rfl rfl rfl
  exact ⟨_, 1, hex, le_rfl, hI', hfr, rfl⟩

/-- An instruction the block lemma covers: a register instruction writing a scratch register,
with its value within the word bound. -/
def okI (W : ℕ) (f : ℕ → ℕ) : Instr → Prop
  | .constN r k => IScr r ∧ k ≤ W
  | .copyN r _ => IScr r
  | .addN r a b => IScr r ∧ f a + f b ≤ W
  | .subN r _ _ => IScr r
  | .loadN r _ => IScr r
  | _ => False

/-- The side conditions of a block, along its run. -/
def okB (W : ℕ) (m : ℕ → ℕ) : List Instr → ztjx → Prop
  | [], _ => True
  | i :: l, f => okI W f i ∧ okB W m l ztefz

/-- One covered instruction. -/
theorem IRS.instr1 (hI : IInv W c₀ c) (hi : okI W c.nreg i) :
    IRS P W c₀ ztbgj c 1 (fun c' => c' = { c with nreg := regI c.nmem i c.nreg }) := by
  cases i with
  | constN r k => exact IRS.reg hI hi.1 ztpxt
  | copyN r a => exact IRS.reg hI hi zthqx
  | addN r a b => exact IRS.reg hI hi.1 ztows
  | subN r a b => exact IRS.reg hI hi ztjin
  | loadN r a => exact IRS.reg hI hi ztlel
  | _ => exact absurd hi by_tauto

/-- **A straight-line block** of register instructions. -/
theorem IRS.block : ∀ (l : List Instr) {c : Config}, IInv W c₀ c →
    okB W c.nmem l c.nreg →
    IRS P W c₀ ztqcu c l.length
      (fun c' => c' = { c with nreg := regB c.nmem l c.nreg })
  | [], c, hI, _ => IRS.skip hI rfl
  | i :: l, c, hI, hok => by
    zuicq
    have h := IRS.seq (IRS.instr1 hI hi) (fun c₁ hI₁ _ _ h₁ => by
      subst h₁
      exact IRS.block l hI₁ hl)
    zugzd

/-- **A store** at an address at or above `c₀`'s allocator. -/
theorem IRS.store {a v : ℕ} (hI : IInv W c₀ c) (ha : c₀.nreg ALLOC ≤ c.nreg a) :
    IRS P W c₀ (.instr (.storeN a v)) c 1
      (fun c' => c' = { c with nmem := upd c.nmem (c.nreg a) (c.nreg v) }) := by
  have ex := Exec.storeN (P := P) hI.hw a v
  refine ⟨_, 1, ex, le_rfl, ⟨ex.wb_right, hI.hin, hI.hA, fun b hb => ?_, hI.hrm⟩,
    ⟨by_simp_all, by_simp_all, rfl, le_rfl, by_simp_all⟩, rfl⟩
  zuby
  zufa
  exact hI.hm b hb

/-- **A loop**: an invariant `I` and a measure `μ`; each iteration costs at most `Kb` and lowers
`μ`.  The allocator must leave room for all iterations. -/
theorem IRS.while {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (Kb : ℕ)
    (hpos : ∀ c, I c → c.nreg a < c.nreg b → 0 < μ c)
    (hbody : ∀ c, IInv W c₀ c → I c → c.nreg a < c.nreg b → c.nreg ALLOC + Kb ≤ W →
      IRS P W c₀ body c Kb ztesi)
    (hI : IInv W c₀ c) (hc : I c) (hroom : c.nreg ALLOC + ztkq * μ c ≤ W) :
    IRS P W c₀ ztpx c ztxrk
      ztcpy := by
  induction hn : μ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    zudm
    · zukht
      obtain ⟨c₁, k₁, e₁, hk₁, hI₁, hfr₁, hc₁, hμ₁⟩ := hbody c hI hc ht (by
        zuhdn
        omega)
      zumbm
      have hroom₁ : ztxiw := by
        zudxq

      obtain ⟨c', k₂, e₂, hk₂, hI', hfr₂, hq⟩ := ih ztgne by_omega hI₁ hc₁ hroom₁ rfl
      refine ⟨c', k₁ + 2 + k₂, .whileLtN_true ht e₁ e₂, ?_, hI',
        (hfr₁.trans hfr₂).mono by_omega, hq⟩
      zucfy

    · exact ztfwb

/-- **A call of a statement with a `Meets` contract in the oracle bands**: the fixed registers
are kept by the frame. -/
theorem IRS.callO {B' : Finset ℕ} {Pre : Polygon → ℕ → Config → Prop}
    {Post : Polygon → Config → Config → Prop} {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ oracleBands) (hI : IInv W c₀ c)
    (hpre : Pre P W c) (hroom : c.nreg ALLOC + cost P c ≤ W) :
    IRS P W c₀ s c ztnxg (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      zth ∧
      ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  zute
  have hkeep : ∀ r, bandOf r ∉ oracleBands → r ≠ ALLOC → c'.nreg r = c.nreg r :=
    fun r hr hra => hfr.1 r by_grind hra
  have hfix : ∀ q, IFix q → c'.nreg q = c.nreg q := fun q hq => hkeep q (by
    unfold IFix at hq; rw [band_sw by_omega by_omega]; decide) (by unfold IFix at hq; unfold ALLOC; omega)
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hfix q hq).trans ztfsi,
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a ztftc).trans ztduw,
    fun a ha => (hfr.2.2.2.1 a ztftc).trans zttmj⟩,
    IFr.of_frame hfr (hB.trans oracle_sub), hpost, hfr.2.2.2.2.2.1, hfr.2.2.1, hkeep⟩

/-- **A run step from an execution** that writes scratch registers, the allocator (raised by at
most the step count) and memory at or above `c₀`'s allocator. -/
theorem IRS.ofExec {k K : ℕ} {Q : Config → Prop} (hI : IInv W c₀ c)
    (ex : Exec P W s c c' k) (hk : k ≤ K)
    (hr : ∀ r, ¬ IScr r → r ≠ ALLOC → c'.nreg r = c.nreg r) (hrr : c'.rreg = c.rreg)
    (hm : ∀ a, a < c₀.nreg ALLOC → c'.nmem a = c.nmem a) (hrm : c'.rmem = c.rmem)
    (ho : c'.output = c.output) (hA1 : c.nreg ALLOC ≤ c'.nreg ALLOC)
    (hA2 : c'.nreg ALLOC ≤ c.nreg ALLOC + k) (hq : Q c') : IRS P W c₀ s c K Q :=
  ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq' => (hr q (fix_not_scr hq') (by
      unfold IFix at hq'; unfold ALLOC; omega)).trans (hI.hin q hq'), le_trans hI.hA hA1,
      fun a ha => (hm a ha).trans ztduw, fun a ha => by zvnmc; exact hI.hrm a ha⟩,
    ⟨fun r hr' hra => hr r ztmjn hra, by_simp_all, ho, hA1, hA2⟩,
    hq⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
def cps (l : List ztw) : List Instr := l.map fun p => .copyN p.1 p.2
theorem cps_length (l : List ztw) : (cps l).length = l.length := by simp [cps]

/-- **The effect of a block of copies** with distinct targets, no source being a target. -/
theorem regB_cps (m : ℕ → ℕ) : ∀ (l : List ztw) (f : ℕ → ℕ),
    (l.map Prod.fst).Nodup → (∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1) →
    (∀ p ∈ l, regB m ztqka f p.1 = f p.2) ∧
      ∀ r, r ∉ l.map Prod.fst → regB m ztqka f r = f r
  | [], f, _, _ => ⟨by_simp_all, fun r _ => rfl⟩
  | (d, s) :: l, f, hnd, hsrc => by
    zuhfk
    have hsrc' : ∀ p ∈ l, ∀ q ∈ l, p.2 ≠ q.1 := by_grind
    obtain ⟨ih1, ih2⟩ := regB_cps m l (upd f d (f s)) hnd'.2 hsrc'
    have hcps : cps (ztfqw :: l) = .copyN d s :: cps l := rfl
    rw [hcps]
    zudj
    refine ⟨fun p hp => ?_, fun r hr => ?_⟩
    · zueuz
      · rw [ih2 _ by_grind]
        simp
      · rw [ih1 p hp]
        have  := hsrc p by_omega ztfqw List.mem_cons_self
        simp [upd, this]
    · zugha
      rw [ih2 r hr.2]
      simp [upd, hr.1]

/-- The side conditions of a block of copies into scratch registers. -/
theorem okB_cps (W : ℕ) (m : ℕ → ℕ) : ∀ (l : List ztw) (f : ℕ → ℕ),
    (∀ p ∈ l, IScr p.1) → okB W m ztqka f
  | [], _, _ => trivial
  | (d, s) :: l, _f, h => ⟨h ztfqw List.mem_cons_self,
      okB_cps W m l _ by_grind⟩
variable {r : ℕ}
theorem iscr_sw (h1 : 240700 ≤ r) (h2 : r < 250000) : IScr r := Or.inl by_omega
theorem not_oracle_sw (h1 : 240000 ≤ r) (h2 : r < 250000) : bandOf r ∉ oracleBands := by
  zuecu

/-! ## The chain of a descriptor register -/

/-- The facts a primitive needs about the chain descriptor at the address held in register
`dsc`. -/
def ChainCtx (P : Polygon) (W : ℕ) (c : Config) (dsc : ℕ) (C : Chain) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ChainWF P ztm c.nmem ztqis ∧
    (∃ H, ChainDescAt c.nmem ztqis zta H C ∧ HostRegular P.n H) ∧ C.P.Simple ∧
    2 * C.m + 7 ≤ W

/-- The chain context transported along a step that keeps the descriptor register, the memory
below the allocator, and does not lower the allocator. -/
theorem ChainCtx.transport {P : Polygon} {W : ℕ} {c c' : Config} {dsc dsc' : ℕ} {C : Chain}
    (h : ChainCtx P W c dsc C) (hr : c'.nreg dsc' = c.nreg dsc)
    (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) :
    ChainCtx P W c' dsc' C := by
  obtain ⟨hG, hW, hwf, ⟨H, hC, hreg⟩, hP, hWm⟩ := h
  obtain ⟨hC', hwf'⟩ := chainDesc_keep hwf hC hm hA
  rw [← hr] at hC' hwf'
  exact ⟨hG, hW, hwf', by_grind, hP, hWm⟩

/-- The primitive's precondition from the chain context, at `50200`. -/
theorem primPre_of {P : Polygon} {W : ℕ} {c : Config} {C : Chain}
    {Inp : Polygon → ℕ → Chain → Config → Prop} (h : ChainCtx P W c 50200 C) (hin : Inp P W C c) :
    PrimPre Inp P W c := by
  obtain ⟨hG, hW, hwf, ⟨H, hC, -⟩, -, -⟩ := h
  exact ⟨hG, hW, hwf, H, C, hC, hin⟩

/-- The host of a chain context is regular, at any host pointer. -/
theorem ChainCtx.hostReg {P : Polygon} {W : ℕ} {c : Config} {dsc : ℕ} {C : Chain}
    (h : ChainCtx P W c dsc C) :
    ∀ H', HostAt c.nmem (c.nmem ztqis) H' → HostRegular P.n H' := by
  obtain ⟨-, -, -, ⟨H, hC, hreg⟩, -, -⟩ := h
  zujap
  rw [← NFLoc.hostAt_unique hC.1 hH']
  omega

/-! ## A generic call -/
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- **Copy in, run a primitive, copy out.** -/
def callP (ins : List ztw) (s : Stmt) (outs : List ztw) : Stmt :=
  .seq (block (cps ins)) (.seq s (block (cps outs)))

/-- **The run step of a primitive call**: the inputs are copied to oracle registers, the
primitive meets its contract from there, and the outputs are copied to scratch registers outside
the oracle bands. -/
theorem callP_irs {ins outs : List ztw} {s : Stmt} {B' : Finset ℕ}
    {Pre : Polygon → ℕ → Config → Prop} {Post : Polygon → Config → Config → Prop} {K : ℕ}
    (hs : Meets s B' Pre Post ztgis) (hB : B' ⊆ oracleBands) (hI : IInv W c₀ c)
    (hin1 : (ins.map Prod.fst).Nodup) (hin2 : ∀ p ∈ ins, ∀ q ∈ ins, p.2 ≠ q.1)
    (hin3 : ∀ p ∈ ins, bandOf p.1 ∈ oracleBands)
    (hout1 : (outs.map Prod.fst).Nodup) (hout2 : ∀ p ∈ outs, ∀ q ∈ outs, p.2 ≠ q.1)
    (hout3 : ∀ p ∈ outs, 240700 ≤ p.1 ∧ p.1 < 250000)
    (hpre : ∀ c₁ : Config, c₁.nmem = c.nmem → c₁.nreg ALLOC = c.nreg ALLOC →
      ztkyb →
      ztimz → Pre P W c₁)
    (hroom : c.nreg ALLOC + ztqrs ≤ W) :
    IRS P W c₀ (callP ins s outs) c ztqrs
      (fun c' => ∃ c₁ c₂, c₁.nmem = c.nmem ∧ ztkyb ∧
        ztimz ∧ Post P c₁ c₂ ∧
        (∀ p ∈ outs, c'.nreg p.1 = c₂.nreg p.2) ∧
        (∀ r, bandOf r ∉ oracleBands → r ∉ outs.map Prod.fst → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hsc1 : ∀ p ∈ ins, IScr p.1 := fun p hp => Or.inr by_grind
  have hsc2 : ∀ p ∈ outs, IScr p.1 := fun p hp => iscr_sw by_grind by_grind
  refine (IRS.seq (K₂ := K + outs.length)
    (IRS.block _ hI (okB_cps W _ ins _ hsc1)) ?_).mono
    (by zupdj; omega) ztb
  intro c₁ hI₁ hA₁ hA₁' hc₁
  subst hc₁
  obtain ⟨e1, e2⟩ := regB_cps c.nmem ins c.nreg hin1 hin2
  have hA1 : regB c.nmem _ c.nreg ALLOC = c.nreg ALLOC :=
    e2 ALLOC (fun h => by
      zufyw
      have := hin3 p hp
      rw [hpa] at this
      tauto)
  set c₁ : Config := { c with nreg := regB c.nmem (cps ins) c.nreg } with hc₁def
  have hpre₁ : Pre P W c₁ := by_grind
  refine IRS.seq (IRS.callO hs hB hI₁ hpre₁ (by
    grind)) ?_
  rintro c₂ hI₂ hA₂ hA₂' ⟨hpost, -, hm₂, hk₂⟩
  refine (IRS.block _ hI₂ (okB_cps W _ outs _ hsc2)).mono (by zupdj)
    ?_
  zufxk
  subst hc'
  obtain ⟨f1, f2⟩ := regB_cps c₂.nmem outs c₂.nreg hout1 hout2
  refine ⟨c₁, c₂, rfl, e1, e2, hpost, f1, fun r hr ho hra => ?_, ?_, ?_⟩
  · grind
  · show c.nreg ALLOC ≤ regB c₂.nmem _ c₂.nreg ALLOC
    rw [f2 ALLOC (fun h => by
      zufyw
      have := hout3 p hp; rw [hpa] at this; tauto)]
    omega
  grind
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sidePt sideLeft)
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}
theorem nodup2 {a b : ℕ} (h1 : a ≠ b) : [a, b].Nodup := by_simp_all
theorem primBands_oracle : primBands ⊆ oracleBands := by_decide
theorem band5_oracle {r : ℕ} (h1 : 50000 ≤ r) (h2 : r < 60000) : bandOf r ∈ oracleBands := by
  zucvl
  zuvs
theorem nodup3 {a b d : ℕ} (h1 : a ≠ b) (h2 : a ≠ d) (h3 : b ≠ d) : [a, b, d].Nodup := by
  simp_all
theorem nodup4 {a b d e : ℕ} (h1 : a ≠ b) (h2 : a ≠ d) (h3 : a ≠ e) (h4 : b ≠ d) (h5 : b ≠ e)
    (h6 : d ≠ e) : [a, b, d, e].Nodup := by
  simp_all

/-! ## `arrivalPos` -/

/-- **The result of an arrival-position call** at registers `f, p, hc`: flag `1` and a proper
arrival position, or flag `0` and no arrival position. -/
def ArrAt (P : Polygon) (C : Chain) (e h ρ f p hc : ℕ) : Prop :=
  f ≤ 1 ∧
    (f = 1 → p < (chainModel C).W.n ∧ ProperPos ztc zta P.n ztujc ∧
      Sweep.Arrival (chainModel C).W ztwqb ztdep p
        ((chainModel C).param zta ztujc)) ∧
    (f ≠ 1 → ∀ p t, ¬ Sweep.Arrival (chainModel C).W ztwqb
      ztdep p t)

/-- `arrivalPos` on the descriptor `dsc`, the position `(re, rh)`, the reversed direction code
`rd`, with the outputs in `o, o + 1, o + 2`. -/
def callArr (dsc re rh rd o : ℕ) : Stmt :=
  callP [ztcso, ztdsq, ztdsr, ztstq] arrivalPos
    [ztcnz, ztbsv, ztciw]
set_option maxRecDepth 20000 in
theorem callArr_irs {dsc re rh rd o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000 ∧
      240000 ≤ rd ∧ rd < 250000) (ho : 240700 ≤ o ∧ o + 2 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztcbr)
    (hy : |((chainModel C).pos zta ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 35007 ≤ W) :
    IRS P W c₀ (callArr dsc re rh rd o) c 35007
      (fun c' => ArrAt P C ztvjw ztvjx (c.nreg rd) ztjrl (c'.nreg ztbql)
          (c'.nreg ztdvm) ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ o → r ≠ o + 1 → r ≠ o + 2 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have h := callP_irs
    (ins := [ztcso, ztdsq, ztdsr, ztstq])
    (outs := [ztcnz, ztbsv, ztciw]) arrivalPos_meets primBands_oracle hI
    by_simp_all
    by_grind
    (by zvmwt
        decide)
    by_simp_all
    by_grind
    by_grind
    (fun c₁ hm hA e1 e2 => by
      zuej
      zufja
      refine primPre_of (hctx.transport g0 by_simp_all ztchd) ?_
      refine ⟨ztcg, hctx.2.2.2.2.1, hctx.2.2.2.2.2⟩
      · omega
      · simp_all
      simp_all)
    by_omega
  zuo

  zufja
  zugqh
  zujd

  zuesd
  unfold ArrOut ArrRes at hres
  rw [g1, g2, g3] at hres
  obtain ⟨r1, r2, r3⟩ := hres
  refine ⟨⟨by_omega, fun hf => ?_, fun hf => ?_⟩, fun r hr h0 h1 h2 hra => hk r hr
    ztyo
    hra, hA, hm'⟩
  · grind
  grind

/-! ## `absKey` and `absCmp` -/

/-- An abscissa record survives a copy of its four words. -/
theorem absRec_transport {c c' : Config} {r r' : ℕ} {x R : ℝ} (h : AbsRec P c r x R)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) (h3 : c'.nreg ztkdl = c.nreg ztkdd) :
    AbsRec P c' r' x R := by
  zuchy
  refine ztfwn
  rcases h with ⟨k, hx⟩ | ⟨k, hx⟩ | ⟨k, hx, s, hs, hl, he⟩
  · simp_all
  · simp_all
  · refine Or.inr (Or.inr ⟨by_omega, hx, s, ?_, hl, he⟩)
    have e2 : c'.nreg (r' + 1 + 1) = c.nreg (r + 1 + 1) := by
      omega
    have e3 : c'.nreg (r' + 1 + 2) = c.nreg (r + 1 + 2) := by
      omega
    cases s with
    | vtx i => exact ⟨by zvmwp; exact hs.1, by zvnlz; exact hs.2⟩
    | onEdge e k => exact ⟨by zvmwp; exact hs.1, by zvnlz; exact hs.2.1, by zvnak; exact hs.2.2⟩

/-- `absKey` on the descriptor `dsc` and the position `(re, rh)`, outputs at `o … o + 3`. -/
def callAbs (dsc re rh o : ℕ) : Stmt :=
  callP [ztcso, ztdsq, ztdsr] absKey
    [ztcnz, ztbsv, ztciw, ztglc]
set_option maxRecDepth 20000 in
theorem callAbs_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 3 < 250000)
    (he : c.nreg re < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztcbr)
    (hy : |((chainModel C).pos zta ⟨c.nreg re, c.nreg rh⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 16707 ≤ W) :
    IRS P W c₀ (callAbs dsc re rh o) c 16707
      (fun c' => AbsRec P c' o ((chainModel C).pos zta ztcbr).1 C.radius ∧
        (∀ r, bandOf r ∉ oracleBands → ztlsd → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have h := callP_irs
    (ins := [ztcso, ztdsq, ztdsr])
    (outs := [ztcnz, ztbsv, ztciw, ztglc]) absKey_meets
    primBands_oracle hI
    by_simp_all
    by_grind
    (by zvmwt
        decide)
    by_simp_all
    by_grind
    by_grind
    (fun c₁ hm hA e1 e2 => by
      zuej
      zuqr
      zuixr
      refine primPre_of hctx₁ ztbabl
      · omega
      · simp_all
      · simp_all
      · zunqs; exact hctx.hostReg)
    by_omega
  zuo

  zuqr
  zufkh
  zujd

  zuesd
  unfold AbsKeyOut at hres
  rw [g1, g2] at hres
  refine ⟨absRec_transport hres k0 k1 k2 k3, fun r hr h0 hra => hk r hr
    ztyo
    hra, hA, hm'⟩

/-- `absCmp` of the records at `a … a + 3` and `b … b + 3`, output bit at `o`. -/
def callAbsCmp (a b o : ℕ) : Stmt :=
  callP [ztdsp, ztpun, ztpuo, ztpup, ztsts,
    ztpuq, ztpur, ztpus] absCmp [(o, 50210)]
set_option maxRecDepth 20000 in
theorem callAbsCmp_irs {a b o : ℕ} (hI : IInv W c₀ c) (hG : GoodEnv P) (hW : P.n + 3 ≤ W)
    (hr : 240000 ≤ a ∧ a + 3 < 250000 ∧ 240000 ≤ b ∧ b + 3 < 250000)
    (ho : 240700 ≤ o ∧ o < 250000) {x₁ x₂ R : ℝ} (h₁ : AbsRec P c a x₁ R)
    (h₂ : AbsRec P c b x₂ R) (hroom : c.nreg ALLOC + 269 ≤ W) :
    IRS P W c₀ (callAbsCmp a b o) c 269
      (fun c' => BitIs c' o ztokg ∧
        ztcfm ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hb : ∀ r, 50201 ≤ r → r ≤ 50208 → bandOf r ∈ oracleBands := fun r h1 h2 =>
    band5_oracle by_omega by_omega
  have h := callP_irs
    (ins := [ztdsp, ztpun, ztpuo, ztpup, ztsts,
      ztpuq, ztpur, ztpus])
    (outs := [ztcnz]) absCmp_meets primBands_oracle hI
    by_simp
    ztdau
    by_simp_all
    by_simp
    by_grind
    by_simp_all
    (fun c₁ hm hA e1 e2 => by
      zuej
      zucso
      exact ⟨hG, hW, x₁, x₂, R, absRec_transport h₁ g1 g2 g3 g4,
        absRec_transport h₂ g5 g6 g7 g8⟩)
    by_omega
  zuo

  zucso
  have hres := hpost x₁ x₂ R (absRec_transport h₁ g1 g2 g3 g4) (absRec_transport h₂ g5 g6 g7 g8)
  refine ⟨BitIs.of_eq hres f1, fun r hr h0 hra => hk r hr
    ztyo
    hra, hA, hm'⟩

/-! ## `offCmp` -/

/-- `offCmp` on the descriptor `dsc`, the positions `(ex, hx)`, `(ey, hy)` and the base `g`,
output bits at `o`, `o + 1`. -/
def callOff (dsc ex hx ey hy g o : ℕ) : Stmt :=
  callP [ztcso, ztstk, ztstm, ztstp, ztstr, ztstt] offCmp
    [ztcnz, ztbsv]
set_option maxRecDepth 20000 in
theorem callOff_irs {dsc ex hx ey hy g o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ ex ∧ ex < 250000 ∧ 240000 ≤ hx ∧ hx < 250000 ∧
      240000 ≤ ey ∧ ey < 250000 ∧ 240000 ≤ hy ∧ hy < 250000 ∧ 240000 ≤ g ∧ g < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000)
    (hex : c.nreg ex < (chainModel C).W.n) (hey : c.nreg ey < (chainModel C).W.n)
    (hg : c.nreg g < (chainModel C).W.n)
    (hpx : ProperPos ztc zta P.n ztgon)
    (hpy : ProperPos ztc zta P.n ztkjy)
    (h6x : c.nreg hx = 0 → 6 ≤ c.nreg ex) (h6y : c.nreg hy = 0 → 6 ≤ c.nreg ey)
    (hroom : c.nreg ALLOC + 11008 ≤ W) :
    IRS P W c₀ ztmhh c 11008
      (fun c' =>
        BitIs c' o (off (chainModel C).W.n ztmgv
            ztymp <
          off (chainModel C).W.n ztmgv ztymq) ∧
        BitIs c' ztbql (off (chainModel C).W.n ztmgv
            ztymq <
          off (chainModel C).W.n ztmgv ztymp) ∧
        ztdwu ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have hb : ∀ r, 50200 ≤ r → r ≤ 50205 → bandOf r ∈ oracleBands := fun r h1 h2 =>
    band5_oracle by_omega by_omega
  have h := callP_irs
    (ins := [ztcso, ztstk, ztstm, ztstp, ztstr, ztstt])
    (outs := [ztcnz, ztbsv]) offCmp_meets primBands_oracle hI
    by_simp
    ztdau
    by_simp_all
    by_simp_all
    by_grind
    by_grind
    (fun c₁ hm hA e1 e2 => by
      zuej
      zudrc
      have hctx₁ := hctx.transport g0 by_grind ztchd
      refine primPre_of hctx₁ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hctx.2.2.2.2.2⟩
      · omega
      · omega
      · omega
      · grind
      · grind
      · omega
      omega)
    by_omega
  zuo

  zudrc
  obtain ⟨k0, k1⟩ := f1
  zujd

  zuesd
  unfold OffOut at hres
  simp only [g1, g2, g3, g4, g5] at hres
  refine ⟨BitIs.of_eq hres.1 k0, BitIs.of_eq hres.2 k1, fun r hr h0 h1 hra => hk r hr
    ztyo
    hra, hA, hm'⟩
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepIo
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed
open Chazelle.Chain (sidePt sideLeft sideInArc)
@[expose] public section
def K0 : ℕ := sw 610
def K1 : ℕ := sw 611
def K6 : ℕ := sw 612
def K4 : ℕ := sw 613
def K5 : ℕ := sw 614
def K2 : ℕ := sw 615
def K3 : ℕ := sw 616

/-- The constants hold their values. -/
def Consts (c : Config) : Prop :=
  c.nreg K0 = 0 ∧ c.nreg K1 = 1 ∧ c.nreg K6 = 6 ∧ c.nreg K4 = 4 ∧ c.nreg K5 = 5 ∧
    c.nreg K2 = 2 ∧ c.nreg K3 = 3
theorem Consts.fix {c₀ c : Config} {W : ℕ} (h : Consts c₀) (hI : IInv W c₀ c) : Consts c := by
  have k : ∀ i, 610 ≤ i → i ≤ 616 → c.nreg _ = c₀.nreg ztcdy := fun i h1 h2 =>
    hI.hin _ ztze
  obtain ⟨a, b, d, e, f, g, i⟩ := h
  exact ⟨(k 610 le_rfl by_norm_num).trans a, (k 611 by_norm_num by_norm_num).trans b,
    (k 612 by_norm_num by_norm_num).trans d, (k 613 by_norm_num by_norm_num).trans e,
    (k 614 by_norm_num by_norm_num).trans f, (k 615 by_norm_num by_norm_num).trans g,
    (k 616 by_norm_num le_rfl).trans i⟩
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## Normalising a position -/

/-- The box rule: on the horizontal box edges `0, 2, 4` the height code becomes `0`. -/
def normBox (pe ph : ℕ) : Stmt :=
  .ifLtN pe K1 ztdsc
    (.ifLtN pe K2 .skip
      (.ifLtN pe K3 ztdsc
        (.ifLtN pe K4 .skip
          (.ifLtN pe K5 ztdsc .skip))))

/-- **Normalise the position `(pe, ph)` in place**: on a walk edge `≥ 6`, compare the keys of
`(pe, 0)` and `(pe, ph)` (bits at `o`, `o + 1`) and set `ph := 0` unless the parameter is
positive; on the box edges apply `normBox`. -/
def normS (dsc pe ph o : ℕ) : Stmt :=
  .ifLtN pe K6 (normBox pe ph)
    (.seq (callOff dsc pe K0 pe ph K0 o) (.ifLtN K0 o .skip ztdsc))

/-- The normalised height code of a position. -/
noncomputable def nhgt (M : Model) (Q : Polygon) (u : WPos) : ℕ := (Restore.normOf M Q u).hgt
set_option maxRecDepth 20000 in
theorem normS_irs {dsc pe ph o : ℕ} {C : Chain} (hI : IInv W c₀ c) (hK : Consts c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240700 ≤ pe ∧ pe < 250000 ∧ 240700 ≤ ph ∧ ph < 250000)
    (ho : 240700 ≤ o ∧ o + 1 < 250000 ∧ o ≠ pe ∧ o ≠ ph ∧ o + 1 ≠ pe ∧ o + 1 ≠ ph ∧ pe ≠ ph)
    (he : c.nreg pe < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztpn)
    (hy : c.nreg pe < 6 → c.nreg pe ≠ 0 → c.nreg pe ≠ 2 → c.nreg pe ≠ 4 →
      |((chainModel C).pos (Qof P) ⟨c.nreg pe, c.nreg ph⟩).2| < C.radius)
    (hroom : c.nreg ALLOC + 11015 ≤ W) :
    IRS P W c₀ ztglb c 11015
      (fun c' => c'.nreg pe = c.nreg pe ∧
        c'.nreg ph = nhgt ztc zta ztpn ∧
        (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  zuch
  have hK0 : K0 = 240610 := rfl
  have hK6 : K6 = 240612 := rfl
  set u : WPos := ztpn with hu
  unfold normS
  zuhsx
  · refine (IRS.ifT hbox ?_).mono (K := 11013) by_omega ztb
    zuduv
    -- the horizontal box edges: the code becomes `0`
    have hzero : (c.nreg pe = 0 ∨ c.nreg pe = 2 ∨ c.nreg pe = 4) →
        IRS P W c₀ ztdsc c 1 (fun c' => c'.nreg pe = c.nreg pe ∧
          c'.nreg ph = nhgt ztc zta ztpn ∧
          (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
            c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
      intro he0
      have hpar : ztykx :=
        Model.param_horizontal (ShootCut.box_horizontal (C := C) he0)
      refine (IRS.reg hI zttpp
        (Exec.constN hI.hw ph 0 ztbg)).mono le_rfl ?_
      zuu
      zubi
      refine ⟨by_simp_all, by
        zunkc; unfold nhgt Restore.normOf; simp_all, fun r hr1 hr2 hr3 hr4 hr5 => ?_,
        by zuoby, by_simp_all⟩
      simp_all
    -- the other box edges: the code is kept
    have hkeep : (c.nreg pe = 1 ∨ c.nreg pe = 3 ∨ c.nreg pe = 5) →
        IRS P W c₀ .skip c 0 (fun c' => c'.nreg pe = c.nreg pe ∧
          c'.nreg ph = nhgt ztc zta ztpn ∧
          (∀ r, bandOf r ∉ oracleBands → r ≠ ph → r ≠ o → r ≠ o + 1 → r ≠ ALLOC →
            c'.nreg r = c.nreg r) ∧
          c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
      intro he1
      refine IRS.skip hI ⟨rfl, ?_, by_omega, le_rfl, by_omega⟩
      have hpos := ShootCut.box_param_pos' C _ hbox hpp.1
        by_grind
      zulur
      grind
    unfold normBox
    rcases (by omega : c.nreg pe = 0 ∨ c.nreg pe = 1 ∨ c.nreg pe = 2 ∨ c.nreg pe = 3 ∨
      c.nreg pe = 4 ∨ c.nreg pe = 5) with h | h | h | h | h | h
    · exact (IRS.ifT by_omega (hzero zteg)).mono by_omega by_grind
    · exact (IRS.ifF by_omega (IRS.ifT by_omega
        (hkeep zteg))).mono by_omega by_grind
    · exact (IRS.ifF by_omega (IRS.ifF by_omega
        ztoxb)).mono by_omega
        by_grind
    · exact (IRS.ifF by_omega (IRS.ifF by_omega
        (IRS.ifF by_omega (IRS.ifT by_omega
          ztvvj)))).mono by_omega by_grind
    · exact (IRS.ifF by_omega (IRS.ifF by_omega
        (IRS.ifF by_omega (IRS.ifF by_omega
          ztoxb)))).mono by_omega
        by_grind
    · exact (IRS.ifF by_omega (IRS.ifF by_omega
        (IRS.ifF by_omega (IRS.ifF by_omega
          (IRS.ifF by_omega ztvvj))))).mono by_omega
        by_grind
  · refine IRS.mono (K := 11013) ztsyc by_omega ztb
    zuduv
    have hn6 : 6 ≤ c.nreg pe := by_omega
    have hn0 : ztixp := by_omega
    refine IRS.seq (K₂ := 3) (callOff_irs hI hctx by_omega
      by_omega he he by_omega ?_ hpp by_simp_all
      by_simp_all by_omega) ?_
    · zvnib; exact ⟨le_rfl, by_norm_num, Nat.zero_le _⟩
    rintro c₁ hI₁ hA₁ hA₁' ⟨b0, -, hk1, -, hm1⟩
    zvnib at b0
    have hlt := (off_lt_iff _ _ hn0 (x := (⟨c.nreg pe, 0⟩ : WPos))
      he le_rfl by_norm_num he hpp.1 hpp.2.1)
    zumps
    have h10 : zteib := by
      rw [hk1 _ ztbet by_omega
        by_omega by_decide, k0]
    have hpe1 : c₁.nreg pe = c.nreg pe := hk1 _ ztbet by_omega
      by_omega ztu
    have hph1 : c₁.nreg ph = c.nreg ph := hk1 _ ztbet by_omega
      by_omega ztu
    by_cases hb : c₁.nreg K0 < c₁.nreg o
    · refine (IRS.ifT hb (IRS.skip (K := 1) hI₁ ?_)).mono by_omega ztb
      zukrq
      have hbit : c₁.nreg o = 1 := by have := b0.1; omega
      have hp := (b0.2.1 hbit)
      rw [hlt] at hp
      have hpar : 0 < (chainModel C).param zta u := by
        rcases hp with hp | ⟨-, hp⟩
        · grind
        tauto
      refine ⟨hpe1, ?_, by_grind, hA₁, hm1⟩
      rw [hph1]; unfold nhgt Restore.normOf; grind
    · refine IRS.mono (K := 1 + 2) ztsyb by_omega ztb
      zukrq
      have hbit : c₁.nreg o ≠ 1 := by_omega
      have hpar : ztykx := by
        zuct
        exact hbit ((b0.2).2 ((hlt).2 (Or.inr ⟨rfl, lt_of_le_of_ne hpp.1 ztnr⟩)))
      refine (IRS.reg hI₁ zttpp
        (Exec.constN hI₁.hw ph 0 ztbg)).mono le_rfl ?_
      zuu
      zubi
      refine ⟨by rw [upd_other _ _ _ ho.2.2.2.2.2.2]; omega, by
        zunkc; unfold nhgt Restore.normOf; grind, fun r hr1 hr2 hr3 hr4 hr5 => ?_,
        by zuoby; omega, hm1⟩
      rw [upd_other _ _ _ hr2]; grind
/-! ## Double identification with the spine position -/

/-- The table of powers of two of the answer stage (base and length). -/
def TBR : ℕ := sw 600
def TLR : ℕ := sw 601
variable {r : ℕ}
theorem band12_oracle (h1 : 120000 ≤ r) (h2 : r < 130000) : bandOf r ∈ oracleBands := by
  have : bandOf r = bOQuery := by unfold bandOf bOQuery; omega
  zuvs
theorem band1_oracle (h1 : 10000 ≤ r) (h2 : r < 20000) : bandOf r ∈ oracleBands := by
  zucvk
  zuvs
theorem bl_oracle (h : OracleR.BL r = true) : bandOf r ∈ oracleBands := by
  simp only [OracleR.BL, NFLoc.Bdir, NFLoc.Bloc, WalkKey.Bcmp, WalkKey.Bk, Bool.or_eq_true,
    decide_eq_true_eq] at h
  by_cases h1 : r < 20000
  · exact band1_oracle by_omega h1
  by_cases h5 : r < 60000
  · exact band5_oracle by_omega h5
  · exact band12_oracle by_omega by_omega

/-- **An oracle-framed run** as an answer-stage step: it writes only oracle registers, keeps the
memory and emits nothing. -/
theorem IRS.ofFrameB {s : Stmt} {B : ℕ → Bool} {c' : Config} {k K : ℕ} {Q : Config → Prop}
    (hI : IInv W c₀ c) (ex : Exec P W s c c' k) (hk : k ≤ K) (fr : SignK.FrameB B c c')
    (hB : ∀ r, B r = true → bandOf r ∈ oracleBands) (hq : Q c') : IRS P W c₀ s c K Q := by
  have hf : ∀ r, bandOf r ∉ oracleBands → B r = false := fun r hr => by
    grind
  have hA : ztble := fr.1 _ (hf _ by_decide)
  refine ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq' => ?_, by zvmze; exact hI.hA,
    fun a ha => by rw [fr.2.2.1]; exact hI.hm a ha,
    fun a ha => by rw [fr.2.2.2.1]; exact hI.hrm a ha⟩,
    ⟨fun r hr _ => fr.1 r ztzwa,
      fun r hr => fr.2.1 r ztzwa, fr.2.2.2.2, by zvmze,
      by omega⟩, hq⟩
  rw [fr.1 q (hf q (fun h => fix_not_scr hq' ztbho))]
  exact hI.hin q hq'

/-- **Double identification** of the position `(pe, ph)` in the normal form at `nf` of the model
of the descriptor at `md`, leaving the spine position in `o`. -/
def locJ (md nf pe ph o : ℕ) : Stmt :=
  .seq (block (cps [ztste, ztstf, ztstg, ztsth, ztsqz,
      ztsra] ++ [.constN 120012 0, .constN 120011 1]))
    (.seq OracleR.myLoc (.instr (.copyN o 120170)))
set_option maxRecDepth 20000 in
theorem locJ_irs {md nf pe ph o : ℕ} {C : Chain} {N : NF} (hI : IInv W c₀ c)
    (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hr : 240000 ≤ md ∧ md < 250000 ∧ 240000 ≤ nf ∧ nf < 250000 ∧ 240000 ≤ pe ∧ pe < 250000 ∧
      240000 ≤ ph ∧ ph < 250000) (ho : 240700 ≤ o ∧ o < 250000)
    (hmd : ModelDescAt c.nmem zthvi zta ztc)
    (hmwf : ModelDescWF P ztm c.nmem zthvi) (hP : C.P.Simple)
    (hN : NFAt c.nmem ztvjt N) (hNF : IsNF ztc zta N)
    (he : c.nreg pe < (chainModel C).W.n)
    (hpp : ProperPos ztc zta P.n ztpn)
    (htab : ∀ j, j < c.nreg TLR → c.nmem ztllh = 2 ^ j)
    (hbig : N.arcs.length < 2 ^ c.nreg TLR) (hB : c.nreg nf + 7 ≤ c.nreg TBR)
    (hAB : c.nmem (c.nreg nf + 4) + 5 * N.arcs.length ≤ c.nreg TBR)
    (hSB : c.nmem (c.nreg nf + 6) + N.arcs.length ≤ c.nreg TBR)
    (hTW : c.nreg TBR + c.nreg TLR ≤ W)
    (_hroom : c.nreg ALLOC + ztwzf ≤ W) :
    IRS P W c₀ (locJ md nf pe ph o) c ztwzf
      (fun c' => c'.nreg o < N.arcs.length ∧
        (¬ (chainModel C).IsCut ztwjq
            ztxjp →
          N.F ztc zta = ∅ ∨
            sideInArc (OracleQ.sk ztc zta N ztjrl)
              (OracleQ.ek ztc zta N ztjrl)
              ztxjp) ∧
        ((chainModel C).IsCut ztwjq
            ztxjp →
          OracleQ.sk ztc zta N ztjrl =
              (chainModel C).key zta ztpn ∨
            OracleQ.ek ztc zta N ztjrl =
              (chainModel C).key zta ztpn) ∧
        ztcfm ∧
        c'.nreg ALLOC = c.nreg ALLOC ∧ c'.nmem = c.nmem) := by
  have hTB : TBR = 240600 := rfl
  have hTL : TLR = 240601 := rfl
  unfold locJ
  set ins := [ztste, ztstf, ztstg, ztsth, ztsqz, ztsra]
    with hins
  have hnd : (ins.map Prod.fst).Nodup := by_simp_all
  have hsrc : ∀ p ∈ ins, ∀ q ∈ ins, p.2 ≠ q.1 := by
    simp only [hins, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      hTB, hTL]; omega
  -- the setup block
  have hTBv : c.nreg TBR = c.nreg 240600 := rfl
  have hTLv : c.nreg TLR = c.nreg 240601 := rfl
  set l : List Instr := cps ins ++ [.constN 120012 0, .constN 120011 1] with hl
  have hok : okB W c.nmem l c.nreg := by
    simp only [hl, hins, cps, List.map, List.cons_append, List.nil_append, okB, okI]
    refine ⟨Or.inr ztjok,
      Or.inr ztjok,
      Or.inr ztjok,
      Or.inr ztjok,
      Or.inr ztjoj,
      Or.inr ztjoj,
      ⟨Or.inr ztjoj, Nat.zero_le _⟩,
      ⟨Or.inr ztjoj, ?_⟩, trivial⟩
    omega
  have hlen : l.length = 8 := by_rfl
  refine IRS.mono (K := l.length + (5500 * ztuc + 1))
    (IRS.seq ztrjq ?_) by_grind ztb
  zufg
  set c₁ : Config := { c with nreg := regB c.nmem l c.nreg } with hc₁
  have hreg : ∀ r, c₁.nreg r = (if r = 120011 then 1 else if r = 120012 then 0 else
      if r = 120042 then c.nreg TLR else if r = 120041 then c.nreg TBR else
      if r = 50003 then c.nreg ph else if r = 50002 then c.nreg pe else
      if r = 50001 then c.nreg nf else if r = 50000 then c.nreg md else c.nreg r) := by
    intro r
    show regB c.nmem l c.nreg r = _
    simp only [hl, hins, cps, List.map, List.cons_append, List.nil_append, regB, regI]
    zuby
    have h1 : md ≠ 50000 := by_omega
    have h2 : nf ≠ 50000 ∧ nf ≠ 50001 := by_omega
    have h3 : pe ≠ 50000 ∧ pe ≠ 50001 ∧ pe ≠ 50002 := by_omega
    have h4 : ph ≠ 50000 ∧ ph ≠ 50001 ∧ ph ≠ 50002 ∧ ph ≠ 50003 := by_omega
    have h5 : (240600 : ℕ) ≠ 50000 ∧ (240600 : ℕ) ≠ 50001 ∧ (240600 : ℕ) ≠ 50002 ∧
      (240600 : ℕ) ≠ 50003 := by_omega
    have h6 : (240601 : ℕ) ≠ 50000 ∧ (240601 : ℕ) ≠ 50001 ∧ (240601 : ℕ) ≠ 50002 ∧
      (240601 : ℕ) ≠ 50003 ∧ (240601 : ℕ) ≠ 120041 := by_omega
    simp only [TBR, TLR, sw, ite_eq_right h2.1, ite_eq_right h3.1, ite_eq_right h3.2.1,
      ite_eq_right h4.1, ite_eq_right h4.2.1, ite_eq_right h4.2.2.1]
    simp
  have r00 : c₁.nreg 50000 = c.nreg md := by_rfl
  have r01 : c₁.nreg 50001 = c.nreg nf := by_grind
  have r02 : c₁.nreg 50002 = c.nreg pe := by_grind
  have r03 : c₁.nreg 50003 = c.nreg ph := by_grind
  have r41 : c₁.nreg 120041 = c.nreg TBR := by_rfl
  have r42 : c₁.nreg 120042 = c.nreg TLR := by_rfl
  have r12 : ztpmr := by_rfl
  have r11 : ztdxr := by_rfl
  have rother : ∀ r, bandOf r ∉ oracleBands → c₁.nreg r = c.nreg r := by
    zuz
    zumod
    have h5 : r < 50000 ∨ 60000 ≤ r := by
      by_contra h'; push Not at h'; exact hr (band5_oracle h'.1 h'.2)
    have h12 : r < 120000 ∨ 130000 ≤ r := by
      by_contra h'; push Not at h'; exact hr (band12_oracle h'.1 h'.2)
    have : r ≠ 120011 ∧ r ≠ 120012 ∧ r ≠ 120042 ∧ r ≠ 120041 ∧ r ≠ 50003 ∧ r ≠ 50002 ∧
        r ≠ 50001 ∧ r ≠ 50000 := by_omega
    grind
  zukdw
  have hA1 := rother ALLOC by_decide
  clear_value c₁
  clear hreg hc₁
  -- the locate call
  zufgh
  obtain ⟨hD6, hLW⟩ := NFLoc.locChainWF_of hmwf by_omega hWh
  have hD : NFLoc.LocDPre P W c₁ := ⟨hG, hW3, by_omega,
    by grind, chainModel C, by_grind, by_omega⟩
  have hst : ∀ j, j < N.arcs.length → ProperPos ztc zta P.n (N.arc j).s := by
    zun
    obtain ⟨_, -, -, -, -, -, -, hpr⟩ := hNF.2.2.2
    have := (hpr j hj).1
    zuic
  obtain ⟨c₂, k₂, e₂, hk₂, fr₂, hj₂, hl1, hl2⟩ := OracleR.myLoc_exec arcCover (P := P) (W := W)
    (c := c₁) hI₁.hw hD hG hW3 (M := chainModel C) (N := N) by_grind
    ztxgi by_grind hNF by_grind hst
    r41 r42 r12 r11 ztjwa hbig
    by_omega by_grind by_grind hTW
  have hfo := fun r hr => fr₂.1 r (by
    cases h : OracleR.BL r
    · rfl
    · exact absurd (bl_oracle h) hr)
  refine IRS.seq (IRS.ofFrameB hI₁ e₂ hk₂
    fr₂ (fun r h => bl_oracle h) (Q := fun c' => c' = c₂) rfl) ?_ |>.mono le_rfl (fun _ h => h)
  zudsv
  refine IRS.mono (IRS.reg hI₃ (iscr_sw ho.1 ho.2)
    (Exec.copyN hI₃.hw o 120170)) le_rfl ?_
  zuu
  zuby
  rw [r02, r03] at hl1 hl2
  refine ⟨hj₂, fun h => ?_, fun h => ?_, fun r hr hro hra => ?_, ?_, fr₂.2.2.1.trans hm₁⟩
  · exact hl1 h
  · exact hl2 h
  · rw [ite_eq_right hro, hfo r hr, rother r hr]
  · rw [ite_eq_right (show ALLOC ≠ o from fun h => absurd ho.1 (by zvmzi; decide)),
      hfo ALLOC by_decide, hA1]
end
end SweepIo
end Chazelle.Core
namespace Chazelle.Core
namespace SweepPrim
open Machine Machine.Stmt Programs SignK WalkKey NFLoc
@[expose] public section
theorem tour_pt {P : Polygon} (hG : GoodEnv P) {H : Host} {C : Chain} (hCP : C.P = H.poly zta)
    (hreg : HostRegular P.n H) (hNn : C.P.n = (H.pts P.n).length) {i : ℕ} (hi : i < 2 * C.m)
    {s₁ s₂ : SymPt}
    (h1 : ztbkj[ztema % (H.pts P.n).length]? = some s₁)
    (h2 : ztbkj[ztxfx % (H.pts P.n).length]? = some s₂)
    (hl₁ : s₁.Lt P.n) (hl₂ : s₂.Lt P.n)
    (hv₁ : s₁.eval zta = (chainModel C).W.vtx ztcy)
    (hv₂ : s₂.eval zta = (chainModel C).W.vtx ztxyx) {hc : ℕ}
    (ht : 0 < (chainModel C).param zta ztcbx) :
    hostEdgeIdx P.n s₁ s₂ < P.n ∧
      (chainModel C).pos zta ztcbx =
        (SymPt.onEdge ztfsk ztzk).eval zta := by
  obtain ⟨hE, hx⟩ := tour_abs hG hCP hreg hNn hi h1 h2 hl₁ hl₂ hv₁ hv₂ ht
  refine ⟨hE, Prod.ext hx ?_⟩
  zubkn
  zulpg
  have hc1 : ztixw := by
    zuzn
    · zulxw
    omega
  zucnu

/-! ## The machine -/

/-- Output the point `onEdge (50142) (h - 1)` into `50210 … 50212`. -/
def outS : Stmt := block [.constN 50210 1, .copyN 50211 50142, .subN 50212 50202 50032]

/-- A tour vertex: its host point. -/
def symVtx : Stmt := .seq ztbdp (tvLoad 50210)

/-- Inside a tour edge: the point of the edge of `Q` carrying the host edge. -/
def symInt : Stmt :=
  .seq ztbdp (.seq ztkgf
    (.seq ztnat (.seq ztkgg (.seq edgeIdxS outS))))

/-- The core: by the (normalised) height code. -/
def symCore : Stmt := .ifLtN 50202 50032 symVtx symInt

/-- **The primitive `symAt`.** -/
def symAt : Stmt := .seq pHead symCore
theorem wr_symAt : wr Bprim symAt = true := by_decide
theorem symVtx_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) {e hc : ℕ} (h01 : c.nreg 50201 = e) (he6 : 6 ≤ e)
    (hen : e < 2 * C.m + 7) (hpar : (chainModel C).param zta ztev = 0) :
    ∃ c' k, Exec P W symVtx c c' k ∧ k ≤ 27 * H.length + 41 ∧
      ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
        s.eval zta = (chainModel C).pos zta ztev := by
  zuiu
  zumz
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, sp, isp, lsp, vsp, -⟩ := tvLoad_exec _ hE₁ (i := e - 6)
    zteqd by_omega (dst := 50210) by_norm_num
  have hv : ztwnq := by
    zubab
  exact ⟨c₂, _, .seq e₁ e₂, by_omega, sp, isp, lsp, by_simp_all⟩
theorem symInt_exec {P : Polygon} {W : ℕ} {H : Host} {C : Chain} (c : Config)
    (hE : CEnv P W H C c) (hreg : HostRegular P.n H) {e hc : ℕ} (h01 : c.nreg 50201 = e)
    (h02 : c.nreg 50202 = hc) (he6 : 6 ≤ e) (hen : e < 2 * C.m + 6)
    (ht : 0 < (chainModel C).param zta ztev) (hhn : hc ≤ P.n) :
    ∃ c' k, Exec P W symInt c c' k ∧ k ≤ 60 * H.length + 200 ∧
      ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
        s.eval zta = (chainModel C).pos zta ztev := by
  zuol
  zubb
  zuhxc

  zubnw
  zuckk
  have hlt : ztdrl := by_omega
  zuiu
  zudky
  zumz
  have q20 : c₁.nreg 50120 = i := by
    show upd c.nreg 50120 (c.nreg 50201 - c.nreg 50081) 50120 = i
    rw [upd_same, h01, hE.r81]
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, hE₂, s₁, i₁, l₁, v₁, x₁⟩ := tvLoad_exec c₁ hE₁ (i := i) q20
    hlt.le (dst := 50130) by_norm_num
  zue
  have e₃ := Exec.addN (P := P) w₂ 50120 50120 50032
    ztdtz
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 50120 _ }
    with hc₃
  zucls
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, hE₄, s₂, i₂, l₂, v₂, x₂⟩ := tvLoad_exec c₃ hE₃ (i := i + 1)
    ztbtw
    by_omega (dst := 50136) by_norm_num
  have i₁' := symPtIn_keep (symPtIn_of_eq i₁ fun j h1 h2 => by
    zumwr; zunbj) f₄
    by_decide
  obtain ⟨c₅, k₅, e₅, hk₅, v₅, r₅⟩ := edgeIdxS_exec (P := P) c₄ e₄.wb_right by_omega
    hE₄.r32 i₁' i₂ l₁ l₂
  have q02 : ztlyi := by
    zuwy
    zubi
    rw [upd_other _ _ _ by_decide, f₂.1 _ by_decide, hc₁]
    simp_all
  have q32 : ztlyh := by
    zubqc
  have ht' : 0 < (chainModel C).param zta ztcbx := by
    simp_all
  obtain ⟨hEi, hpt⟩ := tour_pt hE.hG hE.hP hreg hNn hlt x₁ x₂ l₁ l₂ v₁ v₂ ht'
  have hc1 : ztixw := by
    zuzn
    · zulxx
    omega
  obtain ⟨c₆, k₆, e₆, hk₆, q⟩ : ∃ c₆ k₆, Exec P W outS c₅ c₆ k₆ ∧ k₆ = 3 ∧
      SymPtIn c₆ 50210 ztyoc := by
    zumtv
    zudpp
    exec_block
    all_goals try omega
    refine ⟨rfl, by config_simp, by config_simp; exact v₅, ?_⟩
    config_simp; omega
  have ex : Exec P W symInt c c₆ _ :=
    .seq e₁ ztfv
  refine ⟨c₆, _, ex, by_omega, _, q, ztonu, ?_⟩
  grind

/-- The input condition of `symAt`: a tour position with a normalised height code, a regular
host. -/
def SymIn (P : Polygon) (_ : ℕ) (C : Chain) (c : Config) : Prop :=
  6 ≤ c.nreg 50201 ∧ c.nreg 50201 < 2 * C.m + 6 ∧
    ProperPos ztc zta P.n ztbce ∧
    (c.nreg 50202 = 0 ↔ (chainModel C).param zta ztbce = 0) ∧
    ∀ H', HostAt c.nmem ztzdq H' → HostRegular P.n H'

/-- The output condition of `symAt`: the symbolic point of the position. -/
def SymOut (P : Polygon) (C : Chain) (c c' : Config) : Prop :=
  ∃ s : SymPt, SymPtIn c' 50210 s ∧ s.Lt P.n ∧
    s.eval zta = (chainModel C).pos zta ztbce

/-- **Contract of `symAt`.** -/
theorem symAt_meets : Meets symAt primBands ztvcu ztvct
    (fun _ _ => 1000 + 60 * 0 + 30000) := by
  refine prim_meets (K := 30200) by_simp_all wr_symAt ?_
  intro P W H C c₀ c hC hE ⟨h6, hen, ⟨hp0, hp1, hhn⟩, hnorm, hreg⟩ hinp
  zudpd
  zubgf
  zuhq

  unfold SymOut symCore
  by_cases hz : c.nreg 50202 < c.nreg 50032
  · have hc0 : c₀.nreg 50202 = 0 := by zuotf; rw [hE.r32] at hz; omega
    obtain ⟨c', k, ex, hk, s, hs⟩ := symVtx_exec c hE i01 h6 by_omega (hnorm.1 hc0)
    exact ⟨c', _, .ifLtN_true hz ex, by_omega, s, hs⟩
  · have hc0 : c₀.nreg 50202 ≠ 0 := by zuotf; rw [hE.r32] at hz; omega
    have hpos : 0 < (chainModel C).param _ ztdqp :=
      lt_of_le_of_ne hp0 by_grind
    obtain ⟨c', k, ex, hk, s, hs⟩ := symInt_exec c hE hregH i01 i02 h6 hen hpos hhn
    exact ⟨c', _, .ifLtN_false hz ex, by_omega, s, hs⟩
end
end SweepPrim
namespace SweepEv
open Machine Machine.Stmt Programs SweepIo SweepPrim
@[expose] public section
variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-- A symbolic point survives a copy of its three words. -/
theorem symPtIn_transport {c c' : Config} {r r' : ℕ} {s : SymPt} (h : SymPtIn c r s)
    (h0 : c'.nreg r' = c.nreg r) (h1 : c'.nreg ztcwh = c.nreg ztgu)
    (h2 : c'.nreg ztcwi = c.nreg ztbcu) : SymPtIn c' r' s := by
  cases s with
  | vtx i => exact ⟨by zvmzn; exact h.1, by zvmwp; exact h.2⟩
  | onEdge e k => exact ⟨by zvmzn; exact h.1, by zvmwp; exact h.2.1, by zvmxx; exact h.2.2⟩

/-- `symAt` on the descriptor `dsc`, the position `(re, rh)`, output at `o … o + 2`. -/
def callSym (dsc re rh o : ℕ) : Stmt :=
  callP [ztcso, ztdsq, ztdsr] symAt [ztcnz, ztbsv, ztciw]
set_option maxRecDepth 20000 in
theorem callSym_irs {dsc re rh o : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hctx : ChainCtx P W c dsc C)
    (hr : 240000 ≤ dsc ∧ dsc < 250000 ∧ 240000 ≤ re ∧ re < 250000 ∧ 240000 ≤ rh ∧ rh < 250000)
    (ho : 240700 ≤ o ∧ o + 2 < 250000) (h6 : 6 ≤ c.nreg re) (hen : c.nreg re < 2 * C.m + 6)
    (hpp : ProperPos ztc zta P.n ztcbr)
    (hnorm : c.nreg rh = 0 ↔ (chainModel C).param zta ztcbr = 0)
    (hroom : c.nreg ALLOC + 31006 ≤ W) :
    IRS P W c₀ ztqjn c 31006
      (fun c' => (∃ s : SymPt, SymPtIn c' o s ∧ s.Lt P.n ∧
          s.eval zta = (chainModel C).pos zta ztcbr) ∧
        (∀ r, bandOf r ∉ oracleBands → (r < o ∨ o + 2 < r) → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
        c.nreg ALLOC ≤ c'.nreg ALLOC ∧ zth) := by
  have h := callP_irs
    (ins := [ztcso, ztdsq, ztdsr])
    (outs := [ztcnz, ztbsv, ztciw]) symAt_meets
    primBands_oracle hI
    by_simp_all
    by_grind
    (by zvmwt
        decide)
    by_simp_all
    by_grind
    by_grind
    (fun c₁ hm hA e1 e2 => by
      zuej
      zuqr
      zuixr
      refine primPre_of hctx₁ ztln
      · omega
      · omega
      · simp_all
      · simp_all
      · zunqs; exact hctx.hostReg)
    by_omega
  zuo

  zuqr
  zugqh
  zujd

  obtain ⟨s, hs, hsl, hse⟩ := hpost H C hC₁
  rw [g1, g2] at hse
  refine ⟨⟨s, symPtIn_transport hs k0 k1 k2, hsl, hse⟩, fun r hr h0 hra => hk r hr
    ztyo
    hra, hA, hm'⟩
end
end SweepEv
end Chazelle.Core
section
set_option hygiene false
local macro "zqbht" : tactic => `(tactic| (subst hec
                                           rcases hcatt q' u' hQ' with h | h <;> zvmwc <;> constructor <;> linarith))
local macro "zqbhu" : tactic => `(tactic| (intro e he heZ q u hQ h1 h2 q' u' hQ'
                                           by_cases hec : e = Y))
local macro "zqbhv" : tactic => `(tactic| (have hS₂a := hS₂.2.1
                                           have hS₂f := hS₂.1
                                           have hC := corr_right0 J hP hS₂a hS₂f
                                           zust
                                           have hGM : ztebh := Or.inl ztexm))
local macro "zqbhw" : tactic => `(tactic| have hg0 : ztee := Nat.cast_nonneg _)
local macro "zqbhx" : tactic => `(tactic| rcases hatK e he q u hQ h1.symm with h | h)
local macro "zqbhy" : tactic => `(tactic| (have hZnb : ¬ EvBrk J Z := fun h => by have := h pz tz hZz; linarith))
local macro "zqbhz" : tactic => `(tactic| exact closed_nested hP hS₂a hS₂f hc he ztvbc hA hB hKqb hQ h1 h2 hQ')
local macro "zqbia" : tactic => `(tactic| rcases h.lt_or_eq with h | h)
set_option hygiene true

/-!
# The sweep (WP-D), stage 3: the invariant after a key with an anchored chord (main lemma)

`evInv_anchor`: at a key `K` of the `C₁` part carrying an anchored chord `Z` (attached also at a
position of the open right stretch), with no chord at `K` attached at offset `0` (no pocket), the
label set made of the side labels of the anchored chords at `K` satisfies `EvInv` at `K`.
-/
namespace Chazelle.Core
@[expose] public section
open Set Filter Topology Metric
open Chazelle.Chain (SideAttach sidePt sideInArc)
open WalkEmbed
namespace Sweep
section Anchor2
variable {J : Merge.Junction}

/-- `e` bounds the region faced just after `(pK, tK)`. -/
def AftChord (J : Merge.Junction) (S₂ : Set ztf) (pK : ℕ) (tK : ℝ) (e : Set Point) :
    Prop :=
  ∀ R ∈ (chainModel J.whole).regions ztbi, AfterFaces ztbm pK tK R →
    ∃ ρ : ℝ, ztbtc ∧ SideOf ztbm ρ e R

/-- **Case A**: the position just after `K` is not enclosed: the region after `K` has a valid
label set. -/
theorem anchor_caseA (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) {pK : ℕ} {tK : ℝ}
    (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J ztkm) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J zthe < Lst J)
    {Λ : Set ztf}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e)
    {Ra : Set Point} (hRa : Ra ∈ (chainModel J.whole).regions ztbi)
    (hWa : AfterFaces ztbm pK tK Ra) {s : ℝ}
    (hncy : ¬ (chainModel J.whole).IsCut ztbi zttn)
    (hoy : oW J zttn = oW J ztkm + s) (hs0 : 0 < s) (hs1 : tK + s < 1)
    (hgapy : ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
        ¬ ztxlf)
    (hEy : ¬ EvEncl J S₂ ztxxt) : EvVal J S₂ Λ Ra := by
  zqbhv
  zqbhy
  obtain ⟨X, Y, dX, dY, hX, hY, hXK, hYK, hdX, hdY, hall, haft, hbef, -, -⟩ :=
    keyStruct hGM hF hZ hZK
  zuiwx
  by_cases hYb : EvBrk J Y
  · exfalso
    have hYZ : Y ≠ Z := by_grind
    have hXZ : X = Z := by
      grind
    obtain ⟨pb, tb, hB, hBne⟩ := hM.other_attach (hC.hF hY) hYK
    have hBL := hYb pb tb hB
    have hBne' : oW J ztbd ≠ oW J ztkm := by
      zuq
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hB.1 hpK hB.2.1 hB.2.2.1 htK0 htK1 h
      grind
    rcases lt_or_gt_of_ne hBne' with hlt | hgt
    · -- `Y` closes at `K`: the region before `K` is on a side of `Z`, faced inside `Y`'s arc
      obtain ⟨Rb, hRb, hWb, q, u, hq, hu, -, hfq, h1, h2, -⟩ := before_region_exists' hP hS₂a hS₂f
        hpK htK0 htK1 by_grind
        (show 0 < oW J ztkm - oW J _ by linarith)
      have hRbZ := hbef Rb hRb hWb
      rw [hXZ] at hRbZ
      exact side_comp_off hP hS₂a hS₂f hY hZ hB hYK hlt hZz by_grind hRb hRbZ hq hu
        by_linarith h2 hfq
    · -- `Y` opens at `K`: the position just after `K` is enclosed
      have hyB : oW J zttn < oW J ztbd := by
        rcases lt_or_ge ztxxt (oW J ztbd) with h | h
        · zubh
        · exfalso
          zqbia
          · zuhhw
            exact hgapy _ ⟨Y, hY, pb, tb, hB, rfl⟩ k0 k1 by_grind
          · zuhhw
            have hk := Corr.key_mem hpK by_grind hs1
            zqbhw
            have hgn : ztcx := by
              zucfu
            have hkey := off_inj hg0 hgn hk.1 hk.2 k0 k1 (by zuobl; grind)
            exact hncy ⟨Y, hY, pb, tb, hB, hkey⟩
      exact hEy ⟨Y, hY, pK, pb, tK, tb, hYK, hB, hBne.symm, hLst, by_grind,
        Or.inl hyB⟩
  · obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = -dY := by_grind
    have hρ : -dY = 1 ∨ -dY = -1 := by rcases hdY.cases with h | h <;> zumxk
    exact hlab Y hY hYK hYb (Or.inl fun R hR hW => by_grind) Ra hRa _ hρ hRaY

/-- **The second piece is alone at its far end**: `c` and `s'` tie at `B`, `s'` is attached also at
`C`, both beyond the start, `C` not an attachment of `c`; then `s'` is the only chord at `C` (three
chords would be pieces of one chord of `S₂`). -/
theorem alone_far (hP : J.P.Simple) {S₂ : Set ztf} (hS₂ : S₂ ⊆ Merge.augChords J.right)
    (hS₂f : S₂.Finite) (hNTV : NoTieV J S₂) {c s' : Set Point} (hc : c ∈ F₂plus J S₂)
    (hs' : s' ∈ F₂plus J S₂) (hcs : c ≠ s') {pa qb qc : ℕ} {ta sb sc : ℝ}
    (hcA : SideAttach (chainModel J.whole).W c pa ta) (hcB : SideAttach (chainModel J.whole).W c qb sb)
    (hsB : SideAttach (chainModel J.whole).W s' qb sb)
    (hsC : SideAttach (chainModel J.whole).W s' qc sc) (hLB : (Lst J : ℝ) < oW J ztbjt)
    (hLC : (Lst J : ℝ) < oW J ztdvv) (hCa : oW J ztdvv ≠ oW J ztbf)
    (hCb : oW J ztdvv ≠ oW J ztbjt) (hab : oW J ztbf ≠ oW J ztbjt) :
    ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e qc sc → e = s' := by
  zuv
  intro e he hE
  zuct
  have hout : ∀ {q : ℕ} {u : ℝ}, (Lst J : ℝ) < oW J ztzq →
      ¬ (0 < oW J ztzq ∧ oW J ztzq < Lst J) := by_grind
  have hDC : sidePt (chainModel J.whole).W qc sc ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f hs' he ztnr hsC hE (hout hLC) with h | h
    · zubh
    · exact (hNTV s' hs' e he ztnr qc sc hsC hE h hLC).elim
  have hDB : sidePt (chainModel J.whole).W qb sb ∈ J.right.dom := by
    rcases tie_dom hP hS₂ hS₂f hc hs' hcs hcB hsB (hout hLB) with h | h
    · zubh
    · exact (hNTV c hc s' hs' hcs qb sb hcB hsB h hLB).elim
  obtain ⟨p₁, hp₁, hs'1, he1⟩ := tie_parent J hP hS₂ hs' he hne hsC hE hDC
  obtain ⟨p₂, hp₂, hc2, hs'2⟩ := tie_parent J hP hS₂ hc hs' (Ne.symm hcs) hcB hsB hDB
  have hpp := parent_unique hS₂ hp₁ hp₂
    (pt_ne_of_off_ne hP hS₂ hS₂f hs' hsB hsC (Ne.symm hCb)) (hs'1 hsB.2.2.2.1)
    (hs'1 hsC.2.2.2.1) (hs'2 hsB.2.2.2.1) (hs'2 hsC.2.2.2.1)
  subst hpp
  rcases pieces_le_two hP hS₂ hp₁ hc hs' he hc2 hs'1 he1 hcB hsB hE hDB hDB hDC with h | h | h
  · simp_all
  · zubst
    rcases key_of_two hC.hM ztjxf hcA hcB (pt_ne_of_off_ne hP hS₂ hS₂f hc hcA hcB hab) hE with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp_all
    simp_all
  simp_all

/-- **Case B**: the position just after `K` is enclosed: a bracket `c` opens at `K` (with `Z`, a
tie) and closes before `x`; the region at `x` is the middle region of the tie at `K`, on a side of
`Z`. -/
theorem anchor_caseB (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) (hNTV : NoTieV J S₂) {pK : ℕ}
    {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J ztkm) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J zthe < Lst J)
    (hnp : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK →
      ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J ztej ≠ 0)
    {Λ : Set ztf}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e)
    {p : ℕ} {t : ℝ} (hp : p < (chainModel J.whole).W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hnc : ¬ (chainModel J.whole).IsCut ztbi ztk)
    (hbr : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s →
      oW J ztkm < oW J ztej → oW J ztej < oW J ztk → EvBrk J e)
    (hEx : ¬ EvEncl J S₂ ztxae) {G : Set Point}
    (hG : G ∈ (chainModel J.whole).regions ztbi) (hf : (chainModel J.whole).Faces p t G)
    {s : ℝ} (hs0 : 0 < s) (hs1 : tK + s < 1)
    (hncy : ¬ (chainModel J.whole).IsCut ztbi zttn)
    (hoy : oW J zttn = oW J ztkm + s) (hyx : oW J zttn < oW J ztk)
    (hgapy : ∀ x, (chainModel J.whole).IsCut ztbi x → 0 ≤ x →
      x < (chainModel J.whole).W.n →
        ¬ ztxlf)
    {Ra : Set Point} (hRa : Ra ∈ (chainModel J.whole).regions ztbi)
    (hWa : AfterFaces ztbm pK tK Ra)
    (hfy : (chainModel J.whole).Faces pK (tK + s) Ra)
    (hEy : EvEncl J S₂ ztxxt) : EvVal J S₂ Λ G := by
  zqbhv
  zqbhw
  have hgn : ztcx := by
    zucfu
  zuiwi
  set o' := oW J ztkm with ho'
  set oy := oW J zttn with hoydef
  set ox := oW J ztk with hoxdef
  zqbhy
  -- attachments are not at `y` nor at `x`, and offsets determine positions
  have hcg : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      ¬ (o' < oW J _ ∧ oW J _ < oy) := fun e he q u hA => by
    zudja
    exact hgapy _ ⟨e, he, q, u, hA, rfl⟩ k0 k1
  have hnex : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J _ ≠ ox := fun e he q u hA h => by
    zudja
    zubhm
    exact hnc ⟨e, he, q, u, hA, off_inj hg0 hgn x0 x1 k0 k1 by_tauto⟩
  have hposK : ∀ {q : ℕ} {u : ℝ}, q < (chainModel J.whole).W.n → 0 ≤ u → u < 1 →
      oW J _ = o' → q = pK ∧ u = tK := fun hq hu0 hu1 h =>
    pos_eq_of_oW hP hS₂a hS₂f hq hpK hu0 hu1 htK0 htK1 h
  -- the enclosing chord of `y` is a bracket opening at `K`
  obtain ⟨c, hc, qa, qb, sa, sb, hA, hB, hAB, hLa, hay, hby⟩ := hEy
  have hqa : oW J zteuu ≤ o' := by
    grind
  rcases hby with hby | hby
  swap
  · -- a pocket
    exfalso
    zukmc
    · exact hEx ⟨c, hc, qa, qb, sa, sb, hA, hB, hAB, hLa, by_linarith, Or.inr hby⟩
    · obtain ⟨rfl, rfl⟩ := hposK hA.1 hA.2.1 hA.2.2.1 h
      grind
  have hcZ : c ≠ Z := by
    zunq
    rcases key_of_two hM ztjxf hA hB hAB hZz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hqa' : oW J zteuu = o' := by
    zukmc
    · exact absurd (anchor_not_inside hP hS₂a hS₂f hZ hc hcZ.symm hZK hZz hA hB h by_linarith
        by_linarith) id
    omega
  obtain ⟨hq1, hq2⟩ := hposK hA.1 hA.2.1 hA.2.2.1 hqa'
  rw [hq1, hq2] at hA hAB
  clear hq1 hq2 hqa hqa' hay hLa
  -- `c` closes before `x`
  have hbx : oW J ztbjt < ox := by
    rcases lt_or_ge (oW J ztbjt) ox with h | h
    · zubh
    · zqbia
      · exact absurd ⟨c, hc, pK, qb, tK, sb, hA, hB, hAB, hLst, by_linarith, Or.inl h⟩ hEx
      grind
  have hKqb : o' < oW J ztbjt := by_linarith
  -- the structure at `K`: `X = Z`, `Y = c`
  obtain ⟨X, Y, dX, dY, hX, hY, hXK, hYK, hdX, hdY, hall, haft, hbef, hmid, hXY⟩ :=
    keyStruct hGM hF hZ hZK
  zuiwx
  have hYZ : Y ≠ Z := by
    zunq
    exact side_comp_off hP hS₂a hS₂f hc hY hA hB hKqb hZz by_grind hRa hRaY hpK
      ⟨by_linarith, hs1⟩ by_grind by_omega hfy
  have hXZ : X = Z := by
    rcases hall Z hZ hZK with h | h
    · grind
    grind
  have hYc : Y = c := by
    rcases hall c hc hA with h | h
    · grind
    grind
  subst hXZ hYc
  have hXYne : X ≠ Y := by_grind
  -- the middle region `M` at `K`, on a side of `Z` (and of `c`)
  obtain ⟨Mk, hMk, hMks⟩ := side_region_exists hM hC.hF hC.hfin hc
    (show dY = 1 ∨ dY = -1 from hdY.cases)
  have hMkZ := (hmid hXYne Mk hMk).1 hMks
  have hcbrk : EvBrk J Y := fun q u hQ => by
    rcases key_of_two hM ztjxf hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> linarith
  have hMval :=
    hlab X hX hXK hZnb (Or.inr fun e' he' hA' hne => by
      rcases hall e' he' hA' with h | h
      · grind
      grind) Mk hMk _ (by rcases hdX.cases with h | h <;> zumxk) hMkZ
  suffices hGM' : G = Mk by rw [hGM']; exact hMval
  -- `c` at `qb`
  have hcA := F₂plus_subset J hS₂a hc
  have hdq : DirAt (chainModel J.whole).W Y qb sb _ := dirAt_other hP hcA hA hB hAB hdY
  obtain ⟨X', Y', dX', dY', hX', hY', hXq, hYq, hdX', hdY', hall', haft', hbef', hmid', hXY'⟩ :=
    keyStruct hGM hF hc hB
  have hLq : (Lst J : ℝ) ≤ oW J ztbjt := by_linarith
  have hqbx : 0 < ox - oW J ztbjt := by_linarith
  -- the region on a side of `c` near `c`
  obtain ⟨zc, hzc, hzcD⟩ := exists_mem_dom hM hcA hA
  have hMeq : ∀ R ∈ (chainModel J.whole).regions _,
      SideOf _ dY Y R → R = Mk :=
    fun R hR hRs => sideOf_eq hR hMk hRs hMks hzc hzcD
  -- the region after `qb` and a position just after it
  obtain ⟨-, -, -, -, Ra', hRa', hWa'⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hB.1 hB.2.1
    hB.2.2.1
  obtain ⟨s₁, hs₁0, hs₁ε, hs₁1, hfy₁, hncy₁, hoy₁, hgapy₁⟩ := after_pos_eps hP hS₂a hS₂f hB.1
    hB.2.1 hB.2.2.1 hWa' hqbx
  have hy₁x : oW J (qb + (sb + s₁)) < ox := by_grind
  -- the region at `x` from a non-enclosed position before it
  have hGfrom : ∀ {q : ℕ} {u : ℝ} {R : Set Point}, q < (chainModel J.whole).W.n →
      u ∈ Ioo (0 : ℝ) 1 → ¬ (chainModel J.whole).IsCut _ _ →
      o' < oW J ztzq → oW J _ < ox → ¬ EvEncl J S₂ _ →
      R ∈ (chainModel J.whole).regions _ → (chainModel J.whole).Faces q u R → R = G :=
    fun hq hu hncq h1 h2 hE hR hfq => evGL hP hS₂a hS₂f hq hp hu ht hncq hnc h2 hE hEx
      (fun e he q' u' hQ h3 h4 => hbr e he q' u' hQ by_linarith h4) hR hG hfq hf
  -- chords at `K` other than `Z` and `c`
  have hatK : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J _ = o' → e = X ∨ e = Y := fun e he q u hQ h => by
    obtain ⟨rfl, rfl⟩ := hposK hQ.1 hQ.2.1 hQ.2.2.1 h
    exact hall e he hQ
  -- chords at `qb`
  have hatB : ∀ e ∈ F₂plus J S₂, ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W e q u →
      oW J _ = oW J _ → e = X' ∨ e = Y' := fun e he q u hQ h => by
    obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hB.1 hQ.2.1 hQ.2.2.1 hB.2.1 hB.2.2.1 h
    exact hall' e he hQ
  -- the attachments of `c`
  have hcatt : ∀ (q : ℕ) (u : ℝ), SideAttach (chainModel J.whole).W Y q u →
      oW J ztzq = o' ∨ oW J ztzq = oW J ztbjt := fun q u hQ => by
    rcases key_of_two hM hcA hA hB hAB hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · zulej
    simp
  by_cases htie : X' = Y'
  · -- `c` alone at `qb`
    subst htie
    have hYX' : Y = X' := by rcases hall' Y hY hB with h | h <;> exact h
    have hdY' : ztutp := by
      have := hdY'
      rw [← hYX'] at this
      exact dirAt_unique hP hcA hB this hdq
    have hRa'c : ztzpb := by
      have := haft' Ra' hRa' hWa'
      rw [hdY', neg_neg, ← hYX'] at this
      omega
    have hnE : ztguv := by
      refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst hKqb.le ?_ by_linarith
        hy₁x (fun e he q u hQ h => hgapy₁ _ zteyh (attach_key_mem hQ).1
          (attach_key_mem hQ).2 h) hEx
      zqbhu
      · zqbht
      zuff
      · zudt
        · zqbhz
        · rcases hatB e he q u hQ h2 with h | h <;> exact absurd (h.trans hYX'.symm) hec
      · zqbhx
        · tauto
        tauto
    rw [← hMeq Ra' hRa' hRa'c]
    exact (hGfrom hB.1 ztomk hncy₁ by_linarith hy₁x hnE hRa'
      hfy₁).symm
  · -- a tie at `qb`: `c` and the other chord `s'`
    obtain ⟨s', hs', hs'B, hs'c, hcase⟩ : ∃ s' ∈ F₂plus J S₂,
        SideAttach (chainModel J.whole).W s' qb sb ∧ s' ≠ Y ∧
        ((Y = X' ∧ s' = Y') ∨ (Y = Y' ∧ s' = X')) := by
      rcases hall' Y hY hB with h | h
      · exact ⟨Y', hY', hYq, fun h' => htie ztqoz, Or.inl ztugp⟩
      · exact ⟨X', hX', hXq, fun h' => htie ztvro, Or.inr ztugp⟩
    have hs'brk := hbr s' hs' qb sb hs'B hKqb hbx
    have hs'Z : s' ≠ X := fun h => hZnb (h ▸ hs'brk)
    -- the direction of `s'` at `qb` is `dY`
    have hs'A := F₂plus_subset J hS₂a hs'
    have hds : DirAt (chainModel J.whole).W s' qb sb dY := by
      rcases hM.tie_pair hC.hF hc hs' ztvbp hB hs'B with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have := dirAt_unique hP hcA hB (Or.inl ztujh) hdq
        have hd : dY = -1 := by_linarith
        exact Or.inr ztuhm
      · have := dirAt_unique hP hcA hB (Or.inr ztujh) hdq
        have hd : dY = 1 := by_linarith
        exact Or.inl ztuhm
    -- the other attachment of `s'`
    obtain ⟨qc, sc, hC', hC'ne⟩ := hM.other_attach (hC.hF hs') hs'B
    have hLc := hs'brk qc sc hC'
    have hcb : oW J ztdvv ≠ oW J ztbjt := by
      zuq
      obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hC'.1 hB.1 hC'.2.1 hC'.2.2.1 hB.2.1 hB.2.2.1 h
      tauto
    have hcK : o' < oW J ztdvv := by
      rcases lt_or_ge o' ztzxk with h | h
      · zubh
      · exfalso
        zqbia
        · exact anchor_not_inside hP hS₂a hS₂f hZ hs' (Ne.symm hs'Z) hZK hZz hC' hs'B h hKqb
            by_linarith
        · rcases hatK s' hs' qc sc hC' h with h' | h'
          · tauto
          tauto
    have hcx : oW J ztdvv < ox := by
      rcases lt_or_ge ztzxk ox with h | h
      · zubh
      · exfalso
        zqbia
        · exact hEx ⟨s', hs', qb, qc, sb, sc, hs'B, hC', hC'ne.symm, hLq, hbx, Or.inl h⟩
        · exact hnex s' hs' qc sc hC' h.symm
    -- `s'` is alone at `qc`
    have halone :=
      alone_far hP hS₂a hS₂f hNTV hc hs' ztvbp hA hB hs'B hC' by_linarith by_linarith
        by_linarith hcb by_linarith
    have hdsC : DirAt (chainModel J.whole).W s' qc sc _ :=
      dirAt_other hP hs'A hs'B hC' hC'ne.symm hds
    obtain ⟨X'', Y'', dX'', dY'', hX'', hY'', hXc, hYc, hdX'', hdY'', hall'', haft'', hbef'', -,
      -⟩ := keyStruct hGM hF hs' hC'
    have hX''s := halone X'' hX'' hXc
    have hY''s := halone Y'' hY'' hYc
    subst hX''s
    have hdX''e := dirAt_unique hP hs'A hC' hdX'' hdsC
    have hdY''e := dirAt_unique hP hs'A hC' (hY''s ▸ hdY'') hdsC
    obtain ⟨zs, hzs, hzsD⟩ := exists_mem_dom hM hs'A hs'B
    have hs'eq : ∀ {ρ : ℝ} {R R' : Set Point}, R ∈ (chainModel J.whole).regions _ →
        R' ∈ (chainModel J.whole).regions ztbi → SideOf _ ρ X'' R →
        SideOf _ ρ X'' R' → R = R' :=
      fun hR hR' h h' => sideOf_eq hR hR' h h' hzs hzsD
    rcases hcase with ⟨hYX', hs'Y'⟩ | ⟨hYY', hs'X'⟩
    · -- (a) `c` bounds the region before `qb`, `s'` the one after
      have hdY'e : dY' = dY := by
        rw [← hs'Y'] at hdY'; exact dirAt_unique hP hs'A hs'B hdY' hds
      have hdX'e : dX' = -dY := by
        rw [← hYX'] at hdX'; exact dirAt_unique hP hcA hB hdX' hdq
      have hRa's : SideOf ztbm (-dY) X'' Ra' := by
        have := haft' Ra' hRa' hWa'
        rw [hdY'e, ← hs'Y'] at this; omega
      zujed
      · -- (iii) `qc` before `qb`: the region before `qc` is the region after `qb`: impossible
        exfalso
        obtain ⟨Rb', hRb', hWb', w, u, hw, hu, -, hfw, h1, h2, -⟩ := before_region_exists' hP hS₂a
          hS₂f hC'.1 hC'.2.1 hC'.2.2.1 by_linarith (show 0 < oW J _ - o' by linarith)
        have hRb's := hbef'' Rb' hRb' hWb'
        rw [hdX''e] at hRb's
        have heq := hs'eq hRb' hRa' hRb's hRa's
        zufpx
        exact faced_both_off hP hS₂a hS₂f hc hA hB hKqb hRb' hw hB.1 hu
          ⟨by zuntw, hs₁1⟩ by_linarith by_linarith ztvcf
          hfw hfy₁
      · -- (iv) `qc` after `qb`: the region after `qc` is the middle region at `K`
        have hMs : SideOf ztbm dY X'' Mk := by
          have := (hmid' by_omega Mk hMk).2
          rw [hdY'e, hdX'e, neg_neg, ← hYX', ← hs'Y'] at this
          exact this hMks
        obtain ⟨-, -, -, -, Ra'', hRa'', hWa''⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hC'.1
          hC'.2.1 hC'.2.2.1
        zudhi

        have hRM := hs'eq hRa'' hMk hRa''s hMs
        obtain ⟨s₂, hs₂0, hs₂ε, hs₂1, hfy₂, hncy₂, hoy₂, hgapy₂⟩ := after_pos_eps hP hS₂a hS₂f hC'.1
          hC'.2.1 hC'.2.2.1 hWa'' (show 0 < ox - oW J _ by linarith)
        have hnE : ¬ EvEncl J S₂ (oW J (qc + (sc + s₂))) := by
          refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst by_linarith ?_
            by_linarith by_linarith
            (fun e he q u hQ h => hgapy₂ _ zteyh (attach_key_mem hQ).1
              (attach_key_mem hQ).2 h) hEx
          zqbhu
          · zqbht
          zujti
          · subst hes
            rcases key_of_two hM hs'A hs'B hC' hC'ne.symm hQ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              zulea
          zuff
          · rcases lt_trichotomy _ (oW J _) with h3 | h3 | h3
            · have := closed_nested hP hS₂a hS₂f hc he ztvbc hA hB hKqb hQ h1 h3 hQ'
              zuhtu
            · rcases hatB e he q u hQ h3 with h | h
              · exact absurd (h.trans hYX'.symm) hec
              · exact absurd (h.trans hs'Y'.symm) hes
            · zudt
              · have := closed_nested hP hS₂a hS₂f hs' he (Ne.symm hes) hs'B hC' hgt hQ h3 h2 hQ'
                zuhtu
              · obtain ⟨rfl, rfl⟩ := pos_eq_of_oW hP hS₂a hS₂f hQ.1 hC'.1 hQ.2.1 hQ.2.2.1 hC'.2.1
                  hC'.2.2.1 h2
                exact absurd (halone e he hQ) hes
          · zqbhx
            · exact absurd h heZ
            · exact absurd h hec
        zulqx
        exact (hGfrom hC'.1 ⟨by zupbw, hs₂1⟩ hncy₂ by_linarith
          by_linarith hnE hRa'' hfy₂).symm
    · -- (b) `s'` bounds the region before `qb`, `c` the one after
      have hdY'e : ztutp := by
        rw [← hYY'] at hdY'; exact dirAt_unique hP hcA hB hdY' hdq
      have hdX'e : dX' = dY := by
        rw [← hs'X'] at hdX'; exact dirAt_unique hP hs'A hs'B hdX' hds
      have hRa'c : ztzpb := by
        have := haft' Ra' hRa' hWa'
        rw [hdY'e, neg_neg, ← hYY'] at this; omega
      have hRM := hMeq Ra' hRa' hRa'c
      zujed
      · -- (iii) `qc` before `qb`: the position after `qb` is not enclosed
        have hnE : ztguv := by
          refine noEncl_of_closed hP hS₂a hS₂f hZ hZK hZz hzL hLst hKqb.le ?_
            by_linarith hy₁x (fun e he q u hQ h => hgapy₁ _ zteyh
              (attach_key_mem hQ).1 (attach_key_mem hQ).2 h) hEx
          zqbhu
          · zqbht
          zujti
          · subst hes
            rcases key_of_two hM hs'A hs'B hC' hC'ne.symm hQ' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              zulea
          zuff
          · zudt
            · zqbhz
            · rcases hatB e he q u hQ h2 with h | h
              · exact absurd (h.trans hs'X'.symm) hes
              · exact absurd (h.trans hYY'.symm) hec
          · zqbhx
            · tauto
            tauto
        zulqx
        exact (hGfrom hB.1 ztomk hncy₁ by_linarith hy₁x hnE
          hRa' hfy₁).symm
      · -- (iv) `qc` after `qb`: the region after `qc` is the region before `qb`: impossible
        exfalso
        obtain ⟨Rb, hRb, hWb, w, u, hw, hu, -, hfw, h1, h2, -⟩ := before_region_exists' hP hS₂a
          hS₂f hB.1 hB.2.1 hB.2.2.1 by_linarith (show 0 < oW J ztbjt - o' by linarith)
        have hRbs := hbef' Rb hRb hWb
        rw [hdX'e, ← hs'X'] at hRbs
        obtain ⟨-, -, -, -, Ra'', hRa'', hWa''⟩ := after_region_exists hM hC.hF hC.hfin hC.hg hC'.1
          hC'.2.1 hC'.2.2.1
        zudhi

        have heq := hs'eq hRa'' hRb hRa''s hRbs
        zufpx
        obtain ⟨s₂, hs₂0, hs₂ε, hs₂1, hfy₂, -, hoy₂, -⟩ := after_pos_eps hP hS₂a hS₂f hC'.1
          hC'.2.1 hC'.2.2.1 hWa'' ztja
        exact faced_both_off hP hS₂a hS₂f hc hA hB hKqb hRa'' hw hC'.1 hu
          ⟨by zupbw, hs₂1⟩ by_linarith by_linarith
          ztvcf hfw hfy₂

/-- **The invariant after a key with an anchored chord.**  At a key `K` of the `C₁` part carrying an
anchored chord `Z` (attached also at offset in `(0, Lst)`) and no chord attached at offset `0`, a
label set containing the side labels of every non-bracket chord at `K` satisfies `EvInv` at `K`. -/
theorem evInv_anchor (hP : J.P.Simple) {Q : Polygon} {S₂ : Set ztf}
    (hS₂ : (chainModel J.right).ChordFamily Q S₂)
    (hF : (chainModel J.whole).ChordFamily Q ztbi) (hNTV : NoTieV J S₂) {pK : ℕ}
    {tK : ℝ} (hpK : pK < (chainModel J.whole).W.n) (htK0 : 0 ≤ tK) (htK1 : tK < 1)
    (hLst : (Lst J : ℝ) ≤ oW J ztkm) {Z : Set Point} (hZ : Z ∈ F₂plus J S₂)
    (hZK : SideAttach (chainModel J.whole).W Z pK tK) {pz : ℕ} {tz : ℝ}
    (hZz : SideAttach (chainModel J.whole).W Z pz tz) (hzL : oW J zthe < Lst J)
    (hnp : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK →
      ∀ (q : ℕ) (s : ℝ), SideAttach (chainModel J.whole).W e q s → oW J ztej ≠ 0)
    {Λ : Set ztf}
    (hlab : ∀ e ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e pK tK → ¬ EvBrk J e →
      (AftChord J S₂ pK tK e ∨ ∀ e' ∈ F₂plus J S₂, SideAttach (chainModel J.whole).W e' pK tK →
        e' ≠ e → EvBrk J e') → EvSideLab J S₂ Λ e) :
    EvInv J S₂ ztyrk Λ := by
  zueab

  · tauto
  zuloz

  zubfw

  obtain ⟨-, -, -, -, Ra, hRa, hWa⟩ := after_region_exists hC.hM hC.hF hC.hfin hC.hg hpK htK0 htK1
  obtain ⟨s, hs0, hsε, hs1, hfy, hncy, hoy, hgapy⟩ := after_pos_eps hP hS₂a hS₂f hpK htK0 htK1 hWa
    (show 0 < oW J ztk - oW J ztkm by linarith)
  have hyx : oW J zttn < oW J ztk := by_grind
  by_cases hEy : EvEncl J S₂ ztxxt
  · exact anchor_caseB hP hS₂ hF hNTV hpK htK0 htK1 hLst hZ hZK hZz hzL hnp hlab hp ht hnc hbr hEx
      hG hf hs0 hs1 hncy hoy hyx hgapy hRa hWa hfy hEy
  · have hRaG := evGL hP hS₂a hS₂f hpK hp by_grind ht hncy hnc hyx hEy hEx
      by_grind hRa hG hfy hf
    rw [← hRaG]
    exact anchor_caseA hP hS₂ hF hpK htK0 htK1 hLst hZ hZK hZz hzL hlab hRa hWa hncy hoy hs0 hs1
      hgapy hEy
