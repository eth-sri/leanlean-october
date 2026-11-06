module

public import Chazelle.MacT
public import Chazelle.Core.ShootCutShPt
public import Chazelle.Core.SpecNF
public import Chazelle.Core.DownPhaseDrvRExtSpec

namespace Chazelle.Core
namespace DownMath
@[expose] public section
open Set
open DownHost
open BuildNF (buildNF)
open DrvR (walkItems regHost)

/-- **H-R1 / H-R2.** -/
theorem hostR1Spec : DrvR.HostR1Spec := by
  intro P L E reg r hG hLne hL hperm hsort _hdeg hregs hr Q N S
  classical
  have hQ : Q.Simple := (shearInvariance ztbhs P).1 hG.1
  have hdh : DistinctHeights Q := (goodShear_epsOf hG.2).2.1
  zueqj
  have X : RegCtx Q L E reg r := ⟨hQ, hdh, hL, hperm, hsort, hK, hregs, hr⟩
  set li := decide ztqah with hlidef
  have hli : li = true ↔ Mountain.LeftInside Q := decide_eq_true_iff
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, hwf⟩ := walk_rep X hli
  zuemz
  -- the context
  have hN : ztyyf := isNF_build hQ hL hperm hsort
  zujzg
  zugmy
  have hne : S.Nonempty :=
    ⟨_, (chordPos_attach hN (show 0 < N.nChords by rw [hnc]; exact hK) ztp).1⟩
  have hR : ztmwp := hregs.1.1 r hr
  have Xc : Extract.Ctx Q S ztcz := ztonv
  zuhod
  zuyn
  have hrep' : ztxca :=
    fun j hj => hrep j by_omega
  have hrot : ztxis :=
    poly_of_rep hQ hFam hne hR hli hdh hlen hrep'
  have hedge := edgeOK_of_rep hQ hFam hne hR hdh hlen hrep'
  zuhzy
  zuldk
  · -- counterclockwise
    zuhfc
    have hH : regHost li Q.n N r = walkItems li Q.n N r := by unfold regHost; simp_all
    rw [ite_eq_left hl] at hpts
    have hpoly : (regHost li Q.n N r).poly Q = (hostPoly Q S ztcz).rotate i0 := by
      rw [← hrot]; unfold Host.poly; simp_all
    zudiw
    refine ⟨by_grind, ?_, by_simp_all, by_simp_all,
      by simp_all, by_simp_all, ?_⟩
    · apply hostRegular_of_list
      zuowr; omega
    · zulmh
      exact extractOK_rot Xc hgK hgc hgi (hP.trans hpoly) hs0 hm
  · -- clockwise
    have hl : ztppd := by
      simp_all
    have hH : regHost li Q.n N r = (walkItems li Q.n N r).reverse := by
      unfold regHost; simp_all
    zvnen at hpts
    zvnhh at hpts
    rw [← hl] at hpts
    set P' := (regHost li Q.n N r).poly Q with hP'
    have hverts : P'.vertices = (WP.map ztbzb).reverse := by
      rw [hP']
      show ((regHost li Q.n N r).pts Q.n).map ztbzb = _
      simp_all
    have hP'n : P'.n = K := by
      show P'.vertices.length = K
      simp_all
    have hrn : ztxss := by
      zukpb
    have hP'v : ∀ k, k < K → P'.vtx k = ((hostPoly Q S ztcz).rotate i0).vtx
        ztxjc := by
      zugf
      rw [hrn, ← hrot]
      show P'.vertices.getD k ztdr = (WP.map ztbzb).getD ztcgr ztdr
      rw [hverts, List.getD_eq_getElem _ _ by_simp_all, List.getElem_reverse,
        List.getD_eq_getElem _ _ by_grind]
      simp [hlen]
    have hfacts : PolyFacts Q S ztcz P' := polyFacts_rev hQ hFam hne hR i0
      by_omega
      (fun k hk => hP'v k by_omega)
    obtain ⟨hs, hint, hbd, hvx⟩ := hfacts
    refine ⟨?_, ?_, hs, hint, hbd, hvx, ?_⟩
    · rw [hH]; intro it hit; exact hwf it (List.mem_reverse.1 hit)
    · apply hostRegular_of_list
      rw [hpts, ← hWP]
      exact regular_reverse hedge
    · zulmh
      refine extractOK_rev Xc hgK hgc hgi by_grind ztjwb (hP ▸ hs) hs0 hm
      rw [hP, hP'v k hk, Existence.vtx_rotate _ _ zthew, hostPoly_n,
        Existence.n_rotate, hostPoly_n]
end
end DownMath
namespace DrvX
@[expose] public section
open Chazelle.Chain (sideE)
open DrvR (ivB qE)

/-- The symbolic host point number `k`. -/
def hpt (n : ℕ) (H : Host) (k : ℕ) : SymPt := (H.pts n).getD k ztga

/-- The height vertex of a symbolic point. -/
def hidx : SymPt → ℕ
  | .vtx j => j
  | .onEdge _ h => h

/-- The tour offset (`Chain.sideS`). -/
def tS (m T : ℕ) (β : Bool) : ℕ := if β then T else 2 * m - T

/-- The tour position of walk edge `p`. -/
def tU (m T : ℕ) (β : Bool) (p : ℕ) : ℕ := ztkxt % ztdk

/-- The chain vertex at the start of walk edge `p`. -/
def tK (m T : ℕ) (β : Bool) (p : ℕ) : ℕ := sideE m (tU m T β p)

/-- The end at walk edge `p`, height `h` is the start vertex of `p`. -/
def tZ (n : ℕ) (H : Host) (m T : ℕ) (β : Bool) (h p : ℕ) : Prop :=
  h = hidx ztddc
instance (n : ℕ) (H : Host) (m T : ℕ) (β : Bool) (h p : ℕ) : Decidable (tZ n H m T β h p) := by
  unfold tZ; infer_instance

/-- **A regular position on the inner side.** -/
def RegIn (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) : Prop :=
  6 ≤ p ∧ p ≤ 2 * m + 6 ∧ (p = 2 * m + 6 → tZ n H m T β h p) ∧
    ¬ (tZ n H m T β h p ∧ ztcbf) ∧ (tU m T β p < m ↔ li = true)
instance (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) :
    Decidable (RegIn n H li m T β h p) := by
  unfold RegIn; infer_instance

/-- **The kept test** (X-R1). -/
def KeptT (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) : Prop :=
  RegIn n H li m T β h lp ∨ RegIn n H li m T β h rp
instance (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) :
    Decidable (KeptT n H li m T β h lp rp) := by
  unfold KeptT; infer_instance

/-- **The interior walk edge of a host point** (X-R2): the walk edge starting at a vertex, or the
walk edge carrying an edge point, or the next one if the point is the end of that walk edge (an arc
end at a vertex). -/
def pEdge (li : Bool) (n : ℕ) : SymPt → ℕ
  | .vtx j => ivB li n j
  | .onEdge e h => if h = ivB li n (ztpda % n) then ztpda % n else qE li n e

/-- **The interior walk position of a kept end.** -/
def xPos (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h p : ℕ) : WPos :=
  ⟨pEdge li n ztddc, h + 1⟩

/-- The interior triple of a kept chord record. -/
def xTriple (n : ℕ) (H : Host) (li : Bool) (m T : ℕ) (β : Bool) (h lp rp : ℕ) : ℕ × ℕ × ℕ :=
  (h, (xPos n H li m T β h lp).edge, (xPos n H li m T β h rp).edge)

/-! ## Comparing interior keys -/

/-- The interior walk edge `q` goes up (`Q` vertex heights). -/
def EdgeUp (Q : Polygon) (li : Bool) (q : ℕ) : Prop :=
  (Q.vtx ztlqk).2 < (Q.vtx ztbamz).2

/-- **The key order of two positions of the interior walk**, by edges, then heights. -/
def PosLt (Q : Polygon) (li : Bool) (x y : WPos) : Prop :=
  x.edge < y.edge ∨ (x.edge = y.edge ∧ x.hgt ≠ y.hgt ∧
    ztxid)

/-- Equal keys: equal positions. -/
def PosEq (x y : WPos) : Prop := x.edge = y.edge ∧ x.hgt = y.hgt

/-- **The bucket formula** for a position `x` on the closure of arc `j` (`A` arcs). -/
def bktF (A j : ℕ) (eqS eqE gtS : Prop) [Decidable eqS] [Decidable eqE] [Decidable gtS] : ℕ :=
  if eqS then 2 * j + 1 else if eqE then 2 * ztxek + 1 else if gtS then 2 * j + 2 else 0

/-! ## Basic arithmetic -/
variable {m T : ℕ} (β : Bool) (li : Bool)
theorem tU_lt (hm : 1 ≤ m) (p : ℕ) : tU m T β p < 2 * m :=
  Nat.mod_lt _ by_omega
theorem tK_le (hm : 1 ≤ m) (p : ℕ) : tK m T β p ≤ m :=
  Chazelle.Chain.sideE_le (tU_lt β hm p).le
theorem tK_eq_of_lt {β : Bool} {p : ℕ} (h : tU m T β p < m) : tK m T β p = tU m T β p := by
  zufds
theorem tK_eq_of_ge {β : Bool} {p : ℕ} (h : m ≤ tU m T β p) :
    tK m T β p = 2 * m - tU m T β p := by
  zufds
theorem tK_eq_zero_iff (hm : 1 ≤ m) (p : ℕ) :
    tK m T β p = 0 ↔ tU m T β p = 0 := by
  have := tU_lt (T := T) β hm p
  zufds
theorem tK_eq_m_iff (hm : 1 ≤ m) (p : ℕ) :
    tK m T β p = m ↔ tU m T β p = m := by
  have := tU_lt (T := T) β hm p
  zufds

/-- The last walk edge (up the slit) has the tour position of the first one. -/
theorem tU_last (m T : ℕ) (β : Bool) : tU m T β ztgch = tU m T β 6 := by
  unfold tU
  simp
theorem tK_last (m T : ℕ) (β : Bool) : tK m T β ztgch = tK m T β 6 := by
  unfold tK; rw [tU_last]

/-- `ivB` is an involution. -/
theorem ivB_ivB {n p : ℕ} (hp : p < n) : ivB li n (ivB li n p) = p := by
  zujqn

/-- `qE` is an involution. -/
theorem qE_qE {n e : ℕ} (he : e < n) : qE li n ztlsa = e := by
  unfold qE
  grind
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
@[expose] public section
open Set DownHost DownMath
open BuildNF (buildNF)
open DrvR (regHost walkItems)

/-- **The hypotheses of the extraction.** -/
structure XHyp (P : Polygon) (li : Bool) (L : List zte) (E : List ℕ)
    (reg : ℕ → Set Point) (r : ℕ) (C : Chain) (NR : NF) : Prop where
  hG : GoodEnv P
  hli : li = true ↔ Mountain.LeftInside zta
  hLne : L ≠ []
  hL : ChordTriplesOK ztwiq zta L
  hperm : E.Perm ztct
  hsort : E.Pairwise ztbajk
  hregs : Restore.NFRegs ztwiq zta
    ztbajc reg
  hr : r < (buildNF ztwiq zta L E).nRegions
  hCP : C.P = (regHost li (Qof P).n ztbajc r).poly zta
  hCs : C.s = 0
  hCm : C.m + 1 = C.P.n
  hNR : IsNF ztc zta NR

/-- The walk-order index of host point `k`. -/
def rho (li : Bool) (K k : ℕ) : ℕ := if li then k else K - 1 - k
theorem rho_lt (li : Bool) {K k : ℕ} (hk : k < K) : rho li K k < K := by
  zumug

/-- **The context of the extraction.** -/
structure XCtx (P : Polygon) (li : Bool) (L : List zte) (E : List ℕ)
    (reg : ℕ → Set Point) (r : ℕ) (C : Chain) (NR : NF) (i0 g : ℕ) : Prop where
  X : XHyp P li L E reg r C NR
  hg : g < nk ztwiq
    ztbajb ztcz
  hgc : ChordGap ztwiq
    ztbajb ztcz g
  hgi : ztbs % nk ztwiq
    ztbajb ztcz =
      i0 % nk ztwiq
        ztbajb ztcz
  hn : C.P.n = nk ztwiq
    ztbajb ztcz
  hrep : ∀ k, k < nk ztwiq
      ztbajb ztcz →
    RepPt li zta ((buildNF ztwiq zta L E).F ztwiq
      zta) (reg r)
      ((i0 + rho li (nk ztwiq
        ztbajb ztcz)
          k) % nk (interiorModel (Qof P))
        ztbajb ztcz)
      (hpt (Qof P).n (regHost li (Qof P).n ztbajc r) k)
  hvtx : ∀ k, k < nk ztwiq
      ztbajb ztcz →
    C.P.vtx k = (hostPoly zta
      ztbajb ztcz).vtx
      ((i0 + rho li (nk ztwiq
        ztbajb ztcz)
          k) % nk (interiorModel (Qof P))
        ztbajb ztcz)
  hfacts : PolyFacts zta
    ztbajb ztcz C.P
  hext : DownDrv.ExtractOK zta
    ztbajb ztcz C
  hbd : C.P.boundary = (hostPoly zta
    ztbajb ztcz).boundary
namespace XHyp
variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF}
theorem hQ (X : XHyp P li L E reg r C NR) : (Qof P).Simple :=
  (shearInvariance ztbhs P).1 X.hG.1
theorem hdh (X : XHyp P li L E reg r C NR) : DistinctHeights zta :=
  (goodShear_epsOf X.hG.2).2.1
theorem hK (X : XHyp P li L E reg r C NR) : 0 < L.length :=
  List.length_pos_iff_exists_mem.2 (List.exists_mem_of_ne_nil _ X.hLne)
theorem regCtx (X : XHyp P li L E reg r C NR) : RegCtx zta L E reg r :=
  ⟨X.hQ, X.hdh, X.hL, X.hperm, X.hsort, X.hK, X.hregs, X.hr⟩
theorem hN (X : XHyp P li L E reg r C NR) :
    IsNF ztwiq zta ztbajc :=
  isNF_build X.hQ X.hL X.hperm X.hsort
theorem hFam (X : XHyp P li L E reg r C NR) :
    (interiorModel zta).ChordFamily zta
      ztbajb :=
  X.hN.1
theorem hne (X : XHyp P li L E reg r C NR) :
    ((buildNF ztwiq zta L E).F ztwiq zta).Nonempty := by
  have hnc := nChords_build X.hQ X.hL X.hperm X.hsort
  exact ⟨_, (chordPos_attach X.hN (show 0 < (buildNF ztwiq zta L E).nChords
    by rw [hnc]; exact X.hK) (Or.inl rfl)).1⟩
theorem hR (X : XHyp P li L E reg r C NR) :
    reg r ∈ (interiorModel zta).regions
      ztbajb :=
  X.hregs.1.1 r X.hr
theorem ectx (X : XHyp P li L E reg r C NR) :
    Extract.Ctx zta
      ztbajb ztcz :=
  ⟨X.hQ, X.hFam, X.hne, X.hR⟩

/-- **The context exists.** -/
theorem ctx (X : XHyp P li L E reg r C NR) : ∃ i0 g, XCtx P li L E reg r C NR i0 g := by
  classical
  set Q := Qof P with hQdef
  zudbj
  set S := N.F ztd Q with hSdef
  zuhxd

  have hli := X.hli
  obtain ⟨i0, g, hrep, hlen, hgK, hgc, hgi, -⟩ := walk_rep X.regCtx hli
  zuemz
  have hFam := X.hFam
  have hne := X.hne
  have hR := X.hR
  have Xc := X.ectx
  zuhod
  zuyn
  have hrep' : ztxca :=
    fun j hj => hrep j by_omega
  have hrot : ztxis :=
    poly_of_rep hQ hFam hne hR hli hdh hlen hrep'
  zuhzy
  -- the host points in walk order
  have hHp : ∀ k, k < K → hpt Q.n ztqvm k = WP.getD (rho li K k) ztga := by
    zugf
    unfold hpt rho
    zufrc
    · simp_all
    grind
  have hHlen : ((regHost li Q.n N r).pts Q.n).length = K := by
    zufrc
    · simp_all
    simp_all
  have hn : C.P.n = K := by
    rw [X.hCP]; show (((regHost li Q.n N r).pts Q.n).map ztbzb).length = K
    simp_all
  have hrepH : ∀ k, k < K → RepPt li Q S ztcz ztzzt
      (hpt Q.n ztqvm k) := by
    zugf
    rw [hHp k hk]
    exact hrep' _ (rho_lt li hk)
  have hvtx : ∀ k, k < K → C.P.vtx k = (hostPoly Q S ztcz).vtx ztzzt := by
    zugf
    have hι : ztfhx % K < K := Nat.mod_lt _ by_omega
    rw [hostPoly_vtx hι, ← rep_eval hQ hFam hne hR hli hdh hι (hrepH k hk), X.hCP]
    show (((regHost li Q.n N r).pts Q.n).map ztbzb).getD k ztdr = _
    zuhjx
    unfold hpt
    zujgp
  -- polygon facts and extraction facts
  have hrn : ztxss := by
    zukpb
  zuldk
  · zuhfc
    have hpoly : C.P = (hostPoly Q S ztcz).rotate i0 := by
      apply poly_eq_of_vtx by_omega
      zugf
      zugeh
      rw [hvtx k hk, Existence.vtx_rotate _ _ by_simp_all, hostPoly_n]
      zumuh
    refine ztedu
    · rw [hpoly]; exact polyFacts_rotate hQ hFam hne hR i0
    · exact extractOK_rot Xc hgK hgc hgi hpoly X.hCs X.hCm
    · rw [hpoly, Existence.boundary_rotate]
  · have hl : ztppd := by
      grind
    have hPv : ∀ k, k < K → C.P.vtx k = ((hostPoly Q S ztcz).rotate i0).vtx
        ztxjc := by
      zugf
      rw [hvtx k hk, hrn, Existence.vtx_rotate _ _ zthew, hostPoly_n]
      zumuh
    refine ztedu
    · exact polyFacts_rev hQ hFam hne hR i0 by_grind
        ztnzg
    · refine extractOK_rev Xc hgK hgc hgi hn ztjwb
        (polyFacts_rev hQ hFam hne hR i0 by_grind
          ztnzg).1 X.hCs X.hCm
      rw [hvtx k hk]
      zumug
    · rw [Mountain.rev_boundary by_omega (fun k hk => hPv k by_omega),
        Existence.boundary_rotate]
end XHyp
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sidePt)
open BuildNF (codeLe wposOf buildNF gapStarts evs evOf)
open DrvR (keyBkt OnArcKey ivB)
variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## The gaps of the event list -/

/-- The key of the event at index `i`. -/
noncomputable def kE (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (i : ℕ) : ℝ :=
  M.key Q ztzyl
variable {m : ℕ} {j : ℕ}
theorem kap_evs' (hm : m < E.length) :
    BuildSort.kap ztll m = kE M Q L E m := by
  zuue
theorem kE_mono' (hsort : E.Pairwise ztxi) {i i' : ℕ} (hii : i ≤ i')
    (hi' : i' < E.length) : kE M Q L E i ≤ kE M Q L E i' := by
  zujcr
  · simp
  · zuffq

    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem by_omega, Option.getD_some,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
    zubpp
    · grind
    simp_all

/-- The start index of gap `j`. -/
noncomputable def gsX (M : Model) (Q : Polygon) (L : List zte) (E : List ℕ) (j : ℕ) : ℕ :=
  (gapStarts M Q L E).getD j 0
theorem mem_gapStarts' : m ∈ gapStarts M Q L E ↔ m < E.length ∧
    ztwwi := by
  unfold gapStarts; simp
theorem gsX_eq (hj : j < (gapStarts M Q L E).length) :
    gsX M Q L E j = ztdon[j] := by
  unfold gsX; simp_all
theorem gsX_mem (hj : j < (gapStarts M Q L E).length) :
    gsX M Q L E j ∈ gapStarts M Q L E := by
  rw [gsX_eq hj]; simp
theorem gsX_lt_len (hj : j < (gapStarts M Q L E).length) : gsX M Q L E j < E.length :=
  (mem_gapStarts'.1 (gsX_mem hj)).1
theorem gsX_lt {j j' : ℕ} (hjj : j < j') (hj' : j' < (gapStarts M Q L E).length) :
    gsX M Q L E j < gsX M Q L E j' := by
  have hj : ztccc := by_omega
  rw [gsX_eq hj, gsX_eq hj']
  exact List.pairwise_iff_getElem.1 (List.Pairwise.filter _ List.pairwise_lt_range) j j' hj
    hj' hjj

/-- Every gap start is some `gsX k`. -/
theorem gsX_of_mem (hm : m ∈ gapStarts M Q L E) :
    ∃ k, k < (gapStarts M Q L E).length ∧ gsX M Q L E k = m := by
  obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.1 hm
  exact ⟨k, hk, by rw [gsX_eq hk]; omega⟩

/-- **The keys are constant between consecutive gap starts.** -/
theorem kE_const (hsort : E.Pairwise ztxi) {a b : ℕ} (hab : a ≤ b) (hb : b < E.length)
    (hno : ∀ m, a ≤ m → m < b → m ∉ gapStarts M Q L E) : kE M Q L E a = kE M Q L E b := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [ih by_omega by_grind]
    have hnm := hno b hab by_omega
    rw [mem_gapStarts'] at hnm
    push Not at hnm
    obtain ⟨-, hk⟩ := hnm by_omega
    rw [kap_evs' hb, kap_evs' by_omega] at hk
    exact le_antisymm (kE_mono' hsort by_omega hb) hk
theorem gsX_last (hE : 0 < E.length) :
    0 < (gapStarts M Q L E).length ∧
      gsX M Q L E ztdbp = E.length - 1 := by
  have hmem : ztmsy := mem_gapStarts'.2 by_omega
  obtain ⟨j₀, hj₀, hj₀e⟩ := gsX_of_mem hmem
  zuhwf

  zuct
  have hlt : ztknn := by
    grind
  have h1 := gsX_lt (M := M) (Q := Q) (L := L) (E := E) hlt by_omega
  have h2 := gsX_lt_len (M := M) (Q := Q) (L := L) (E := E)
    (j := (gapStarts M Q L E).length - 1) by_omega
  omega

/-! ## The arcs of `buildNF` -/
section arcs
variable (hK : 0 < L.length) (hsort : E.Pairwise (codeLe M Q L))
  (hE : E.length = 2 * L.length)
include hK hsort hE
omit hK hsort hE in
theorem arcsLen (hK : 0 < L.length) (_hsort : E.Pairwise ztxi)
    (_hE : E.length = 2 * L.length) : (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
  zuewm
omit hK hsort hE in
theorem keyS (hK : 0 < L.length) (_hsort : E.Pairwise ztxi)
    (_hE : E.length = 2 * L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).s = kE M Q L E (gsX M Q L E j) := by
  zudnb
  zuhqo
omit hK hsort hE in
theorem keyE (hK : 0 < L.length) (_hsort : E.Pairwise ztxi)
    (_hE : E.length = 2 * L.length) {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    M.key Q ((buildNF M Q L E).arc j).e = kE M Q L E ((gsX M Q L E j + 1) % E.length) := by
  zudnb
  zuhqo

/-- **The start keys of the arcs increase strictly.** -/
theorem key_s_strict {j j' : ℕ} (hjj : j < j') (hj' : j' < (buildNF M Q L E).arcs.length) :
    M.key Q ((buildNF M Q L E).arc j).s < M.key Q ((buildNF M Q L E).arc j').s := by
  rw [arcsLen hK hsort hE] at hj'
  zujzd
  rw [keyS hK hsort hE by_omega, keyS hK hsort hE hj']
  have hlt := gsX_lt hjj hj'
  have hj'len := gsX_lt_len hj'
  rcases (mem_gapStarts'.1 (gsX_mem
    (show j < (gapStarts M Q L E).length by omega))).2 with h | h
  · omega
  · rw [kap_evs' by_omega, kap_evs' by_omega] at h
    exact lt_of_lt_of_le h (kE_mono' hsort by_omega hj'len)

/-- **Each arc ends where the next one starts.** -/
theorem key_e_next {j : ℕ} (hj : j < (buildNF M Q L E).arcs.length) :
    M.key Q ((buildNF M Q L E).arc j).e =
      M.key Q ((buildNF M Q L E).arc (ztl % (buildNF M Q L E).arcs.length)).s := by
  rw [arcsLen hK hsort hE] at hj ⊢
  zujzd
  obtain ⟨hA, hlast⟩ := gsX_last (M := M) (Q := Q) (L := L) hE0
  rw [keyE hK hsort hE hj, keyS hK hsort hE (Nat.mod_lt _ hA)]
  by_cases hj1 : j + 1 < (gapStarts M Q L E).length
  · rw [Nat.mod_eq_of_lt hj1]
    have h1 := gsX_lt ztmnz hj1
    have h2 := gsX_lt_len hj1
    zuey
    refine kE_const hsort by_omega h2 fun m hm1 hm2 hmem => ?_
    zufyr
    rcases Nat.lt_or_ge k ztl with hk' | hk'
    · rcases Nat.lt_or_ge k j with hk'' | hk''
      · have := gsX_lt hk'' hj; omega
      grind
    · rcases Nat.lt_or_ge ztl k with hk'' | hk''
      · have := gsX_lt hk'' hk; omega
      grind
  · have hjl : j = (gapStarts M Q L E).length - 1 := by_omega
    rw [show j + 1 = (gapStarts M Q L E).length by omega, Nat.mod_self, hjl, hlast,
      Nat.sub_add_cancel hE0, Nat.mod_self]
    have h0 := gsX_lt_len hA
    refine kE_const hsort ztbg h0 fun m hm1 hm2 hmem => ?_
    zufyr
    zuevc
    · omega
    · have := gsX_lt hk0 hk; omega
end arcs

/-! ## Counting the arc starts below a key -/
theorem filter_range_length {A c : ℕ} {p : ℕ → Bool} (hc : c ≤ A)
    (hp : ∀ j, j < A → (p j = true ↔ j < c)) : ((List.range A).filter p).length = c := by
  induction A generalizing c with
  | zero => simp; omega
  | succ A ih =>
    rw [List.range_succ, List.filter_append, List.length_append]
    rcases Nat.lt_or_ge A c with h | h
    · have hc' : c = A + 1 := by_omega
      have hA := (hp A by_omega).2 h
      have h1 := ih le_rfl by_grind
      grind
    · grind
open Classical in
/-- **The bucket of a position on the closure of an arc** of `N`. -/
theorem keyBkt_eq {N : NF} {A : ℕ} (hA : N.arcs.length = A)
    (hinc : ∀ j j', j < j' → j' < A →
      (interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q (N.arc j').s)
    (hnext : ∀ j, j < A →
      (interiorModel Q).key Q (N.arc j).e = (interiorModel Q).key Q (N.arc ztxek).s)
    (hfree : ∀ j j', j < A → j' < A → ¬ sideInArc ztejb
      zteja ztjcl)
    {x : WPos} {j : ℕ} (hj : j < A) (hon : OnArcKey Q N j x) :
    keyBkt Q N x = bktF A j
      ((interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).s)
      ((interiorModel Q).key Q x = (interiorModel Q).key Q (N.arc j).e)
      ztblk := by
  set ks : ℕ → ℝ := fun j => (interiorModel Q).key Q (N.arc j).s with hks
  set ke : ℕ → ℝ := fun j => (interiorModel Q).key Q (N.arc j).e with hke
  set kx := (interiorModel Q).key Q x with hkx
  have hinj : ∀ j j', j < A → j' < A → ks j = ks j' → j = j' := by
    intro j j' hj hj' he
    zuct
    zubxx
    · grind
    grind
  -- the count of starts below `ks c`, for a start index `c`
  have hcount : ∀ c, c ≤ A → (∀ j', j' < A → (ks j' < kx ↔ j' < c)) →
      ((List.range N.arcs.length).filter fun j' =>
        decide ((interiorModel Q).key Q (N.arc j').s < kx)).length = c := by
    intro c hc h
    zugum
    exact filter_range_length hc fun j' hj' => by zvmwo; exact h j' hj'
  have hbelow : ∀ c, c < A → ∀ j', j' < A → (ks j' < ks c ↔ j' < c) := by
    intro c hc j' hj'
    constructor
    · zulms
      rcases (Nat.le_of_not_lt h').lt_or_eq with h'' | rfl
      · grind
      grind
    grind
  unfold keyBkt bktF
  by_cases hS : kx = ks j
  · rw [ite_eq_left hS, hcount j hj.le (fun j' hj' => by zvojf; exact hbelow j hj j' hj'),
      ite_eq_left by_grind]
  · rw [ite_eq_right hS]
    by_cases hE : kx = ke j
    · have hj2 : ztl % A < A := Nat.mod_lt _ by_omega
      have hE' : kx = ks _ := hE.trans (hnext j hj)
      rw [ite_eq_left hE, hcount _ hj2.le (fun j' hj' => by rw [hE']; exact hbelow _ hj2 j' hj'),
        ite_eq_left ⟨_, by_omega, hE'.symm⟩]
    · rw [ite_eq_right hE]
      have hin : sideInArc (ks j) (ke j) kx := by
        zuied
        · grind
        · grind
        omega
      have hnoeq : ¬ ∃ j', j' < N.arcs.length ∧ (interiorModel Q).key Q (N.arc j').s = kx := by
        grind
      rw [ite_eq_right hnoeq]
      by_cases hG : ks j < kx
      · rw [ite_eq_left hG, hcount ztl by_omega fun j' hj' => ?_]
        · ring
        · constructor
          · zulms
            have hjj : j < j' := by_omega
            zujfa
            have h1 := hinc j j' hjj hj'
            zucrh
            zulap
            · grind
            grind
          grind
      · have hlt : kx < ks j := by_grind
        rw [ite_eq_right hG, hcount 0 ztbg fun j' hj' => ?_]
        constructor
        · zuq
          exfalso
          zujfa
          zucrh
          zulap
          · grind
          grind
        simp

/-! ## Comparing keys of interior positions -/
section keys
variable {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q) (hdh : DistinctHeights Q)
  (hn : 2 ≤ Q.n)
include hli hdh hn

/-- The parameter of an interior position at a vertex height. -/
theorem param_eq {x : WPos} (hx1 : 1 ≤ x.hgt) (hq : x.edge < Q.n) :
    (interiorModel Q).param Q x = ((Q.vtx ztzs).2 - (Q.vtx ztdos).2) /
      ((Q.vtx ztwpf).2 - (Q.vtx ztdos).2) := by
  zuiac
  have hd : ztbamo := by
    zugsm
    have := DownMath.ivB_inj li hq hq1 h'
    zuhsp
    · zufu
    · zudkp
  zucmb
  have ha : (interiorModel Q).wa x.edge = Q.vtx ztdos := by
    zugim
  have hb : (interiorModel Q).wb x.edge = Q.vtx ztwpf := by
    unfold Model.wb; rw [hW, DownMath.walk_n, DownMath.walk_vtx hli hq1]
  zubkw
  cases h with
  | zero => simp at hx1
  | succ h =>
    show (if ((interiorModel Q).wa e).2 = ((interiorModel Q).wb e).2 then 0
      else ((Q.vtx h).2 - ((interiorModel Q).wa e).2) /
        (((interiorModel Q).wb e).2 - ((interiorModel Q).wa e).2)) = _
    simp only at ha hb hd ⊢
    rw [ha, hb, ite_eq_right hd, Nat.add_sub_cancel]
variable {x y : WPos}
/-- On one walk edge, the parameter order is the height order (reversed on a descending edge). -/
theorem param_lt_iff (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt) (hxy : x.edge = y.edge)
    (hq : x.edge < Q.n) (ha : x.hgt - 1 < Q.n) (hb : y.hgt - 1 < Q.n) (hab : x.hgt ≠ y.hgt) :
    (interiorModel Q).param Q x < (interiorModel Q).param Q y ↔
      ztxid := by
  zuiac
  rw [param_eq hli hdh hn hx1 hq, param_eq hli hdh hn hy1 by_omega, ← hxy]
  have hd : ztbamo := by
    zugsm
    have := DownMath.ivB_inj li hq hq1 h'
    zuhsp
    · zufu
    · zudkp
  have hab' := hdh _ _ ha hb by_omega
  unfold EdgeUp
  rcases lt_or_gt_of_ne hd with hup | hdown
  · have hpos : 0 < (Q.vtx ztwpf).2 - (Q.vtx ztdos).2 := by
      linarith
    rw [div_lt_div_iff_of_pos_right hpos]
    simp_all
  · have hneg : (Q.vtx ztwpf).2 - (Q.vtx ztdos).2 < 0 := by
      linarith
    rw [div_lt_div_right_of_neg hneg]
    grind

/-- **Key order of interior positions** by edges and heights. -/
theorem key_lt_iff (hx : ProperPos ztd Q Q.n x)
    (hy : ProperPos ztd Q Q.n y) (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt)
    (hxe : x.edge < Q.n) :
    (interiorModel Q).key Q x < (interiorModel Q).key Q y ↔ PosLt Q li x y := by
  zucha

  have hpx := hx.1
  have hpx1 := hx.2.1
  have hpy := hy.1
  have hpy1 := hy.2.1
  have hkx : (interiorModel Q).key Q x = x.edge + (interiorModel Q).param Q x := rfl
  have hky : (interiorModel Q).key Q y = y.edge + (interiorModel Q).param Q y := rfl
  rw [hkx, hky]
  unfold PosLt
  constructor
  · zuq
    rcases Nat.lt_or_ge x.edge y.edge with h1 | h1
    · omega
    · rcases h1.lt_or_eq with h2 | h2
      · exfalso
        have : ztddy := by exact_mod_cast h2
        linarith
      · right
        have he := h2.symm
        have hne : x.hgt ≠ y.hgt := by
          zujba
          have : x = y := by cases x; cases y; simp_all
          simp_all
        refine ⟨he, hne, ?_⟩
        zvmxm at h
        exact (param_lt_iff hli hdh hn hx1 hy1 he hxe hxn hyn hne).1 by_linarith
  · rintro (h | ⟨h1, h2, h3⟩)
    · zuepg
      linarith
    · have := (param_lt_iff hli hdh hn hx1 hy1 h1 hxe hxn hyn h2).2 h3
      simp_all

/-- **Key equality of interior positions**: equal edges and heights. -/
theorem key_eq_iff (hx : ProperPos ztd Q Q.n x)
    (hy : ProperPos ztd Q Q.n y) (hx1 : 1 ≤ x.hgt) (hy1 : 1 ≤ y.hgt)
    (hxe : x.edge < Q.n) (hye : y.edge < Q.n) :
    (interiorModel Q).key Q x = (interiorModel Q).key Q y ↔ PosEq x y := by
  constructor
  · zuq
    have h1 : ¬ PosLt Q li x y := fun h' =>
      absurd h ((key_lt_iff hli hdh hn hx hy hx1 hy1 hxe).2 h').ne
    have h2 : ¬ PosLt Q li y x := fun h' =>
      absurd h.symm ((key_lt_iff hli hdh hn hy hx hy1 hx1 hye).2 h').ne
    unfold PosLt at h1 h2
    have he : ztsnc := by
      omega
    refine ztood
    by_contra hh
    zucha

    have hd := hdh _ _ hxn hyn by_omega
    grind
  · zukoj
    have : x = y := by cases x; simp_all
    simp_all
end keys
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
@[expose] public section
open Set
open Chazelle.Chain (sideInArc sidePt)
open BuildNF (codeLe wposOf buildNF gapStarts)
open DrvR (keyBkt OnArcKey ivB)

/-- **The arc test by comparisons.** -/
def OnArcP (Q : Polygon) (li : Bool) (N : NF) (j : ℕ) (x : WPos) : Prop :=
  PosEq x (N.arc j).s ∨ PosEq x (N.arc j).e ∨
    ((PosLt Q li (N.arc j).s (N.arc j).e → PosLt Q li (N.arc j).s x ∧ PosLt Q li x (N.arc j).e) ∧
      (¬ PosLt Q li (N.arc j).s (N.arc j).e → PosLt Q li (N.arc j).s x ∨ PosLt Q li x (N.arc j).e))

/-- A position fit for comparisons: proper, at a vertex height, on a walk edge `< n`. -/
def GoodPos (Q : Polygon) (x : WPos) : Prop :=
  ProperPos ztd Q Q.n x ∧ 1 ≤ x.hgt ∧ x.edge < Q.n
theorem bktF_congr {A j : ℕ} {a a' b b' c c' : Prop} [Decidable a] [Decidable a']
    [Decidable b] [Decidable b'] [Decidable c] [Decidable c'] (ha : a ↔ a') (hb : b ↔ b')
    (hc : c ↔ c') : bktF A j a b c = bktF A j a' b' c' := by
  simp_all
instance (x y : WPos) : Decidable (PosEq x y) := by unfold PosEq; infer_instance
section
variable {Q : Polygon} {li : Bool} (hli : li = true ↔ Mountain.LeftInside Q)
  (hdh : DistinctHeights Q) (hn : 2 ≤ Q.n)
include hli hdh hn
variable {N : NF}
/-- **The arc test by comparisons.** -/
theorem onArc_iff {j : ℕ} {x : WPos} (hx : GoodPos Q x) (hs : GoodPos Q (N.arc j).s)
    (he : GoodPos Q (N.arc j).e) : OnArcKey Q N j x ↔ OnArcP Q li N j x := by
  unfold OnArcKey OnArcP
  rw [key_eq_iff hli hdh hn hx.1 hs.1 hx.2.1 hs.2.1 hx.2.2 hs.2.2,
    key_eq_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2 he.2.2]
  apply or_congr_right; apply or_congr_right
  have h1 := key_lt_iff hli hdh hn hs.1 he.1 hs.2.1 he.2.1 hs.2.2
  have h2 := key_lt_iff hli hdh hn hs.1 hx.1 hs.2.1 hx.2.1 hs.2.2
  have h3 := key_lt_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2
  zuiq
open Classical in
/-- **The bucket by comparisons.** -/
theorem bkt_spec {A : ℕ} (hA : N.arcs.length = A)
    (hinc : ∀ j j', j < j' → j' < A →
      (interiorModel Q).key Q (N.arc j).s < (interiorModel Q).key Q (N.arc j').s)
    (hnext : ∀ j, j < A →
      (interiorModel Q).key Q (N.arc j).e = (interiorModel Q).key Q (N.arc ztxek).s)
    (hfree : ∀ j j', j < A → j' < A → ¬ sideInArc ztejb
      zteja ztjcl)
    {x : WPos} {j : ℕ} (hj : j < A) (hx : GoodPos Q x) (hs : GoodPos Q (N.arc j).s)
    (he : GoodPos Q (N.arc j).e) (hon : OnArcP Q li N j x) :
    keyBkt Q N x = bktF A j zthca zthbz
      (PosLt Q li (N.arc j).s x) := by
  classical
  rw [keyBkt_eq hA hinc hnext hfree hj ((onArc_iff hli hdh hn hx hs he).2 hon)]
  exact bktF_congr (key_eq_iff hli hdh hn hx.1 hs.1 hx.2.1 hs.2.1 hx.2.2 hs.2.2)
    (key_eq_iff hli hdh hn hx.1 he.1 hx.2.1 he.2.1 hx.2.2 he.2.2)
    (key_lt_iff hli hdh hn hs.1 hx.1 hs.2.1 hx.2.1 hs.2.2)
end

/-! ## The arcs of the interior normal form -/
section
variable {P : Polygon} {li : Bool} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ} {reg : ℕ → Set Point}
  {r : ℕ} {C : Chain} {NR : NF}
namespace XHyp
variable (X : XHyp P li L E reg r C NR)
include X
theorem hE : E.length = 2 * L.length := by rw [X.hperm.length_eq, List.length_range]

/-- **The arcs of the interior normal form.** -/
theorem arc_facts :
    (∀ j, j < (buildNF ztwiq zta L E).arcs.length →
      GoodPos zta ((buildNF ztwiq zta L E).arc j).s ∧
      GoodPos zta ((buildNF ztwiq zta L E).arc j).e) ∧
    (∀ j j', j < j' → j' < (buildNF ztwiq zta L E).arcs.length →
      (interiorModel zta).key zta ((buildNF ztwiq zta L E).arc j).s <
        (interiorModel zta).key zta ((buildNF ztwiq zta L E).arc j').s) ∧
    (∀ j, j < (buildNF ztwiq zta L E).arcs.length →
      (interiorModel zta).key zta ((buildNF ztwiq zta L E).arc j).e =
        (interiorModel zta).key zta ((buildNF ztwiq zta L E).arc
          (ztl % (buildNF ztwiq zta L E).arcs.length)).s) ∧
    (∀ j j', j < (buildNF ztwiq zta L E).arcs.length →
      j' < (buildNF ztwiq zta L E).arcs.length →
      ¬ sideInArc
        ((interiorModel zta).key zta ((buildNF ztwiq zta L E).arc j).s)
        ((interiorModel zta).key zta ((buildNF ztwiq zta L E).arc j).e)
        ((interiorModel zta).key zta
          ((buildNF ztwiq zta L E).arc j').s)) := by
  set N := buildNF ztwiq zta L E with hNdef
  have hN := X.hN
  have hK := X.hK
  have hE := X.hE
  have hArcs := X.hregs.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hprop⟩ := hN
  have hWn : ztxcy := DownMath.walk_n _
  -- every arc is an arc of its region
  have harc : ∀ j, j < N.arcs.length → (interiorModel zta).IsArc
      (N.F ztwiq zta) ztpdl
      ztwzc
      ztwzb := fun j hj => (hArcs.1 j hj).2
  -- the ends of the arcs are chord positions
  have hhgt : ∀ j, j < N.arcs.length → 1 ≤ (N.arc j).s.hgt ∧ 1 ≤ (N.arc j).e.hgt := by
    zun
    obtain ⟨⟨i, -, hi⟩, ⟨i', -, hi'⟩⟩ := DownMath.arc_pos X.hQ X.hL X.hperm X.hsort hK hj
    constructor
    · rcases hi with h | h <;> zvmwc <;> exact Nat.succ_pos _
    · rcases hi' with h | h <;> zvmwc <;> exact Nat.succ_pos _
  have hedge : ∀ x : WPos, ProperPos ztwiq zta (Qof P).n x →
      (interiorModel zta).key zta x < (Qof P).n → x.edge < (Qof P).n := by
    intro x hx hk
    have : (x.edge : ℝ) < (Qof P).n := by
      have := hx.1; unfold Model.key at hk; linarith
    simp_all
  refine ⟨fun j hj => ?_, fun j j' hjj hj' => key_s_strict hK X.hsort hE hjj hj',
    fun j hj => key_e_next hK X.hsort hE hj, fun j j' hj hj' hin => ?_⟩
  · obtain ⟨hs, he⟩ := hprop j hj
    obtain ⟨-, has, -, hbe, -⟩ := harc j hj
    zvnux at has hbe
    exact ⟨⟨hs, (hhgt j hj).1, hedge _ hs has⟩, ⟨he, (hhgt j hj).2, hedge _ he hbe⟩⟩
  · have hcut := (WalkAx.arc_cuts X.hne (harc j' hj')).1
    exact (harc j hj).2.2.2.2.2.1 _ hin hcut
end XHyp
end

/-! ## Heights by the lexicographic order of the input -/

/-- **Heights of the geometry polygon** compare like the `(y, x)` order of the input. -/
theorem hlt_iff {P : Polygon} (hG : GoodEnv P) {u v : ℕ} (hu : u < (Qof P).n) (hv : v < (Qof P).n) :
    ((Qof P).vtx u).2 < ((Qof P).vtx v).2 ↔ Mountain.ylexLT ztenr ztvcp := by
  have hgood := goodShear_epsOf hG.2
  zudzj
  rw [hgood.2.2.1 u v by_omega by_omega]
  show _ ↔ ((Qof P).vtx u).2 < ((Qof P).vtx v).2 ∨
    (((Qof P).vtx u).2 = ((Qof P).vtx v).2 ∧ ((Qof P).vtx u).1 < ((Qof P).vtx v).1)
  constructor
  · simp_all
  · zuczb
    · zubh
    · by_cases huv : u = v
      · simp_all
      · exact absurd h (hgood.2.1 u v hu hv huv)
end
end DrvX
end Chazelle.Core
namespace Chazelle.Core
namespace DrvX
@[expose] public section
open Set
open Chazelle.Chain (sideE sidePt sideLeft sideLeftOf sideCcw)

/-- The next chain vertex along side `A` (up) or `B` (down). -/
def kNext (A : Bool) (k : ℕ) : ℕ := if A then k + 1 else k - 1

/-- The previous chain vertex along side `A` (up) or `B` (down). -/
def kPrev (A : Bool) (k : ℕ) : ℕ := if A then k - 1 else k + 1
variable {C : Chain}
theorem chain_vertex_eq (hs : C.s = 0) {k : ℕ} (hk : k < C.P.n) : C.vertex k = C.P.vtx k := by
  unfold Chain.vertex Chain.edgeIdx; rw [hs, zero_add, Nat.mod_eq_of_lt hk]
variable (β : Bool) (i : ℕ) {m u : ℕ}
theorem sideIdx_eq_tK : C.sideIdx β i = tK C.m C.topIdx β ztcy := by
  rfl
theorem tU_eq :
    tU C.m C.topIdx β ztcy = ztty % ztbb := by
  rfl

/-- **The tour vertex at the start of walk edge `p`.** -/
theorem walk_vtx (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h6 : 6 ≤ p)
    (hp : p ≤ 2 * C.m + 6) : (C.sideWalk β).vtx p = C.P.vtx ztevx := by
  zuii
  zukou
  zueev
  rw [sideIdx_eq_tK, chain_vertex_eq hs (by have := tK_le β C.one_le ztcy (T := C.topIdx); omega)]
theorem sideE_succ' (hu : u < 2 * m) :
    sideE m ztcol = kNext ztpap ztuah := by
  unfold sideE kNext
  grind

/-- **The tour vertex at the end of walk edge `p`.** -/
theorem walk_next (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h6 : 6 ≤ p)
    (hp : p < 2 * C.m + 6) :
    (C.sideWalk β).vtx ztxao =
      C.P.vtx ztzwo := by
  zuii
  zubb
  zugtn
  zueev
  have hle := C.sideIdx_le β ztg
  have hu := Nat.mod_lt ztty ztcdw
  rw [chain_vertex_eq hs by_omega, C.sideIdx_succ, tK, tU_eq, sideE_succ' hu]
theorem sideE_pred' (hu0 : 1 ≤ u) (hu : u < 2 * m) (hum : u ≠ m) :
    sideE m ztewa = kPrev ztpap ztuah := by
  unfold sideE kPrev
  grind
theorem mod_pred {x M : ℕ} (hM : 0 < M) (hx : 1 ≤ x % M) : ztoka % M = x % M - 1 := by
  have h1 := Nat.div_add_mod x M
  have h2 : x - 1 = M * (x / M) + (x % M - 1) := by_omega
  rw [h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt x hM; omega)]

/-- **The tour vertex before walk edge `p`** (away from the chain ends). -/
theorem walk_prev (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h7 : 7 ≤ p)
    (hp : p ≤ 2 * C.m + 6) (hu0 : tU C.m C.topIdx β p ≠ 0) (hum : tU C.m C.topIdx β p ≠ C.m) :
    (C.sideWalk β).vtx (ztlro % (C.sideWalk β).n) =
      C.P.vtx (kPrev ztfbt ztevx) := by
  obtain ⟨i, rfl⟩ : ∃ i, p = (i + 1) + 6 := ⟨p - 7, by_omega⟩
  zubb
  rw [C.sideWalk_prev_tour β by_omega by_omega, C.sideWalk_vtx_tour β by_omega]
  zueev
  have hle := C.sideIdx_le β (i + 1 - 1)
  rw [chain_vertex_eq hs by_omega, Nat.add_sub_cancel, Chain.sideIdx_eq, tK]
  have hu := tU_lt (T := C.topIdx) β hm1 (i + 1 + 6)
  rw [← sideE_pred' by_omega hu hum]
  zucr
  rw [tU_eq] at hu0 ⊢
  rw [← mod_pred by_omega by_omega, show C.sideS β + ztg - 1 = C.sideS β + i by omega]

/-! ## Sectors -/

/-- **Inside a tour edge** the left sector is the left half-plane of the chain edge. -/
theorem walk_sector_edge (hP : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool)
    {p : ℕ} (h6 : 6 ≤ p) (hp : p < 2 * C.m + 6) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft ztft p t x ↔
      0 < det (C.P.vtx ztevx)
        (C.P.vtx ztzwo) x := by
  have hne : (C.sideWalk β).vtx p ≠ (C.sideWalk β).vtx ztxao := by
    zuii
    rw [C.sideWalk_next_tour β by_omega, C.sideWalk_vtx_tour β by_omega,
      C.sideWalk_vtx_tour β by_omega]
    zueev
    rcases C.sideTour_step β i with h | h
    · zuhlm
    · zuezv
  rw [Chazelle.Chain.sideLeft_edge hne ht, walk_vtx hs hm β h6 hp.le, walk_next hs hm β h6 hp]

/-- **At a tour vertex** away from the chain ends, the left sector lies in the corner of the
chain on the side of the position (at the top vertex: the sub-corner beside the slit). -/
theorem walk_sector_vtx (hP : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) {p : ℕ}
    (h6 : 6 ≤ p) (hp : p ≤ 2 * C.m + 6) (hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0)
    (hum : tU C.m C.topIdx C.sideBeta p ≠ C.m) {x : Point}
    (h : sideLeft ztcs p 0 x) :
    sideLeftOf
      (C.P.vtx (kPrev ztxgq ztqn))
      ztbadx
      (C.P.vtx ztbany)
      x := by
  set β := C.sideBeta with hβ
  zubb
  rcases lt_or_eq_of_le h6 with h7 | h6'
  · zujdy
    · -- an inner tour vertex
      zuii
      rw [C.sideLeft_tour_inner β by_omega by_omega] at h
      have e1 := walk_prev hs hm β (show 7 ≤ i + 6 by omega) hp'.le hu0 hum
      have e2 := walk_next hs hm β h6 hp'
      have e3 := walk_vtx hs hm β h6 hp'.le
      rw [C.sideWalk_prev_tour β by_omega by_omega, C.sideWalk_vtx_tour β by_omega] at e1
      rw [C.sideWalk_next_tour β by_omega, C.sideWalk_vtx_tour β by_omega] at e2
      rw [C.sideWalk_vtx_tour β by_omega] at e3
      simp_all
    · -- the last position, up the slit
      subst hp'
      rw [C.sideLeft_tour_last] at h
      have hT : tK C.m C.topIdx β ztcc = C.topIdx := by
        zuorj; exact C.sideIdx_two_m β
      have hT0 : C.topIdx ≠ 0 := by
        zufou
      have hTm : C.topIdx ≠ C.m := by
        zufov
      have hgood : sideCcw ztblu ztyy
          ztwmj := by
        zuhif
        · omega
        · omega
        omega
      have e1 := walk_prev hs hm β ztkxk le_rfl hu0 hum
      rw [C.sideWalk_prev_tour β by_omega le_rfl, C.sideWalk_vtx_tour β by_omega] at e1
      zuhdv
      rw [show 6 = 0 + 6 from rfl, C.sideWalk_next_tour β by_omega,
        C.sideWalk_vtx_tour β by_omega] at e2
      zuhep
      have hK6 : tK C.m C.topIdx β 6 = tK C.m C.topIdx β ztcc := (tK_last _ _ _).symm
      rw [hK6, ← hU] at e2
      have hTop : C.top = C.P.vtx (tK C.m C.topIdx β ztcc) := by
        zvncs; unfold Chain.top; exact chain_vertex_eq hs (by have := C.topIdx_le; omega)
      rw [← e1, ← hTop]
      zulqv
      zulva
      exact Chazelle.Chain.sideCcw_sub_right ztbais
        (sub_ne_zero.2 C.sideSlitTop_ne_top)
        (sub_ne_zero.2 ztdsw) hgood h
  · -- the first position, down the slit
    subst h6'
    rw [show (6 : ℕ) = 0 + 6 from rfl, C.sideLeft_tour_first] at h
    have hT : tK C.m C.topIdx β 6 = C.topIdx := by
      rw [show (6 : ℕ) = 0 + 6 from rfl, ← sideIdx_eq_tK]; exact C.sideIdx_zero β
    have hT0 : C.topIdx ≠ 0 := by
      zufou
    have hTm : C.topIdx ≠ C.m := by
      zufov
    have hgood : sideCcw ztblu ztyy
        ztwmj := by
      zuhif
      · omega
      · omega
      omega
    zuhep
    have hK6 : tK C.m C.topIdx β ztcc = tK C.m C.topIdx β 6 := tK_last _ _ _
    have e1 := walk_prev hs hm β ztkxk le_rfl
      by_omega by_omega
    rw [C.sideWalk_prev_tour β by_omega le_rfl, C.sideWalk_vtx_tour β by_omega, hU,
      hK6] at e1
    zuhdv
    rw [show 6 = 0 + 6 from rfl, C.sideWalk_next_tour β by_omega,
      C.sideWalk_vtx_tour β by_omega] at e2
    have hTop : C.top = C.P.vtx (tK C.m C.topIdx β ztfmo) := by
      rw [show (0 + 6 : ℕ) = 6 from rfl, hT]; unfold Chain.top
      exact chain_vertex_eq hs (by have := C.topIdx_le; omega)
    rw [show (0 + 6 : ℕ) = 6 from rfl] at hTop e2
    rw [← e1, ← hTop, ← e2]
    zulva
    exact Chazelle.Chain.sideCcw_sub_left ztbais hgood h

/-! ## The box and the slit -/

/-- **The points of the box and slit edges** (and of the slit above the top vertex) are outside
the square of the coordinates of `C.P`, or above all its vertices. -/
theorem walk_box {p : ℕ} {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1)
    (hp : p ≤ 5 ∨ ztcap) :
    Chazelle.Jordan.coordBound C.P < |(sidePt ztft p t).1| ∨
      Chazelle.Jordan.coordBound C.P < |(sidePt ztft p t).2| ∨
      C.top.2 < (sidePt ztft p t).2 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C.sidePt_box β t
  have hr := C.coordBound_lt_radius
  have hr0 := C.radius_pos
  have htr := C.top_snd_lt_radius
  rcases hp with hp | ⟨rfl, ht⟩
  · interval_cases p
    · simp_all
    · grind
    · grind
    · grind
    · simp_all
    · right; right; rw [b5]; simp only; nlinarith
  simp_all
