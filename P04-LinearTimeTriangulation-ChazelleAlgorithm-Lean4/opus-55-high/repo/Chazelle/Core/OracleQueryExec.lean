module

public import Chazelle.MacT
public import Chazelle.Core.OracleRamLoad
public import Chazelle.Core.Lemma41Cover
public import Chazelle.Core.DownPhaseDrvTPiece
public import Chazelle.Core.DownPhaseDrvRExtSpec
public import Chazelle.Core.DownPhaseDrvBCtx
public import Chazelle.Core.NFBuildRegFill
public import Chazelle.Core.NFDecompBfs
public import Chazelle.Core.ClusterEulerRam
public import Chazelle.Core.SweepPrimKer

namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook
@[expose] public section
def qry : Stmt := .seq qLoad restS

/-- The registers written by the query. -/
def BQ (r : ℕ) : Bool := BLd r || BRest r
variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}
theorem sgnOf_σbOf (d : ℕ) : sgnOf ztmpr = dirOf d := by
  unfold sgnOf σbOf dirOf; simp

/-- **The origin of the query**, semantically. -/
theorem semOK_of (h : QAt P m O E V H C N B k) (hG : GoodEnv P) {o : QOrigin} (hol : o.Lt P.n)
    (d : ℕ) : SemOK P C ztkdc (o.eval zta C ztwf) := by
  have hv := h.qvok hol d
  refine ⟨hv, distinctHeights_of_goodEnv hG, ?_, ?_, ?_⟩
  · show _ = ((Qof P).vtx (qhzOf o)).2
    rcases o with (i | ⟨e, hh⟩) | hh <;> rfl
  · show sgnOf ztmpr = 1 ∨ sgnOf ztmpr = -1
    exact sgnOf_cases _
  · show ZoOK C (sgnOf ztmpr) _ (qzoOf zta o)
    rw [sgnOf_σbOf]
    rcases o with p | hh
    · tauto
    tauto

/-- **The query of Lemma 3.6 runs and answers.** -/
theorem qry_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF} {B : BookData} {k : ℕ}
    (hA : QAt P m O E V H C N B k) (hEW : E ≤ W) (hHW : hostWords P.n ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    {o : QOrigin} (ho : QOriginIn c ztdtv o) (hol : o.Lt P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost m ztcdm u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize m ztcdm
      (lab m ztcdm u) ≤ CS) :
    ∃ c' k', Exec P W qry c c' k' ∧
      k' ≤ 100 + (715 * V.L + 700 + dstarCost m ztcdm +
        4 * candCost ztcdm NC CS + 500) ∧
      FrameB BQ c c' ∧
      Answer P C (o.eval zta C ztbahn) ztbahn
        ztvga ztvgb := by
  set V' := qV V P o ztfgo with hV'
  have hA' : QAt P m O E V' H C N B k := hA.withQ o _
  have hv := hA.qvok hol ztfgo
  have hT := hA'.topOK hG hv
  have hs := semOK_of hA hG hol ztfgo
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁⟩ := qLoad_exec hA hEW c hw hm hO hW ho hol
  have m₁ : c₁.nmem = m := by zunok
  have hDL : V'.DL + V'.nD ≤ W := by have := hA'.DL_le; omega
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, tr⟩ := restS_exec arcCover hG hW hs c₁ e₁.wb_right hq₁
    (by zvmxn; exact hA'.qmem hEW) (by zvmxn; exact hA'.ordOK hEW)
    (by zvmxn; exact hA'.chordMem hEW) (by zvmxn; exact hA'.chordTab hEW)
    (by zvmxn; exact hA'.locMem hEW hHW) hDL hT.tv_lt (NC := NC) (CS := CS)
    ztnuf ztnuf
    (by zvmxn; exact chPr_mono ztvsm)
    (by
      zvmxn
      intro t hpart hnd bD hD hbD kk hkk
      obtain ⟨X, hX⟩ := sel_facts ztvsm hs hA.simple hpart hnd hD hbD
      obtain ⟨h1, h2⟩ := hX.stop.1 kk hkk
      exact ⟨by rw [walk_n]; exact h1, h2⟩)
  zvmxn at hk₂ tr
  have hk₂' : k₂ ≤ 715 * V.L + 700 + dstarCost m V' + 4 * candCost V' NC CS + 500 := hk₂
  refine ⟨c₂, _, .seq e₁ e₂, by_omega, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, fun r hr => ?_, f₂.2.2.1.trans f₁.2.2.1,
      f₂.2.2.2.1.trans f₁.2.2.2.1, f₂.2.2.2.2.trans f₁.2.2.2.2⟩
    · zuhop
      rw [f₂.1 r hr.2, f₁.1 r hr.1]
    · zuhop
      rw [f₂.2.1 r hr.2, f₁.2.1 r hr.1]
  · have := rest_answer (hA'.mainCtx hT) hs tr
    rwa [show sgnOf V'.σb = dirOf ztfgo from sgnOf_σbOf _] at this
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ
open Chazelle.Chain (sideInArc)
@[expose] public section
variable {C : Chain} {Q : Polygon} {N : NF} {γ : ℕ}

/-- An arc of a region of a `γ`-semigranular family meets at most `γ` counted edges. -/
theorem arcWt_le_gamma {M : Model} (hGM : GoodModel M) {F : Set ztf}
    (hF : M.ChordFamily Q F) (hsg : M.Semigranular F γ) {U : Set Point} (hU : U ∈ M.regions F)
    {a b : ℝ} (harc : M.IsArc F U a b) : M.arcWt a b ≤ γ := by
  zubm
  have hbdd : BddAbove ztezo :=
    ((hM.arcs_bound hF.2.1 hF.1 hU).1.image _).bddAbove
  have hle : M.arcWt a b ≤ M.weight F U := le_csSup hbdd ztziu
  exact hle.trans (hsg U hU)

/-- A finite set of counted edges met by an interval bounds its weight from below. -/
theorem card_le_arcWt {M : Model} {a b : ℝ} (T : Finset ℕ)
    (hT : ∀ q ∈ T, q < M.W.n ∧ M.counted q ∧ sideInArc a b ((q : ℝ) + 1 / 2)) :
    T.card ≤ M.arcWt a b := by
  zuiqa
  zuezr
  refine Set.ncard_le_ncard zteso ztkpg
  grind

/-- **`γ ≥ 1`** for a `γ`-canonical normal form of a chain. -/
theorem gamma_pos (hP : C.P.Simple) (hC : IsCanonicalNF ztc Q N γ 4) : 1 ≤ γ := by
  zuoj
  zubm
  zuivx
  zufwi

  zubb
  zuccr
  have hγ : γ = 0 := by_omega
  subst hγ
  zudgp
  · exact hM.not_semigranular_zero hF.2.1 hF.1 hne (p₀ := 6) by_omega
      (show 6 ≤ 6 ∧ 6 < 2 * C.m + 6 by omega) hsg
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    obtain ⟨U, hU, a, b, harc⟩ := (arcCover ztc Q _ hGM hF).1
    have hab : ztiyu := by
      zutm
      · simp_all
      simp_all
    zuidd
    have := card_le_arcWt (M := chainModel C) (a := 0) (b := 0) {6} (by
      zuco
      rw [Finset.mem_singleton] at hq; subst hq
      refine ⟨by_omega, show 6 ≤ 6 ∧ 6 < 2 * C.m + 6 by omega, ?_⟩
      unfold sideInArc; grind)
    have := arcWt_le_gamma hGM hF hsg hU harc
    simp_all

/-- All but at most seven walk edges of a set are counted edges. -/
theorem card_counted_ge (m : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, q < 2 * m + 7) :
    S.card ≤ (S.filter fun q => 6 ≤ q ∧ q < 2 * m + 6).card + 7 := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := S)
    (fun q => 6 ≤ q ∧ q < 2 * m + 6)
  have hsub : S.filter (fun q => ¬ (6 ≤ q ∧ q < 2 * m + 6)) ⊆ Finset.range 6 ∪ {2 * m + 6} := by
    grind
  have hc := Finset.card_le_card hsub
  have hc2 : (Finset.range 6 ∪ {2 * m + 6}).card ≤ 7 :=
    (Finset.card_union_le _ _).trans by_simp
  omega

/-- **The walk edges scanned for an arc.** -/
theorem scanLen_le (hP : C.P.Simple) (hC : IsCanonicalNF ztc Q N γ 4) {p : ℕ}
    (hp : p < N.arcs.length) :
    scanLenR N ztz N.arcs.length p ≤ γ + 10 ∧
      scanLenR N ztz N.arcs.length p ≤ 2 * C.m + 9 := by
  classical
  zuoj
  have hN := hC.1
  zufwi

  obtain ⟨reg, hR, hA, harc⟩ := isArc_sj hN hp
  have hU : reg (N.arc ztmh).reg ∈ (chainModel C).regions ztwjh :=
    hR.1 _ (hA.1 _ ztctk).1
  have hwt := arcWt_le_gamma hGM hN.1 hsg hU harc
  zubrg
  obtain ⟨⟨hs0, hs1, -⟩, ⟨he0, he1, -⟩⟩ := hpp _ ztctk
  zudvt

  have hsk : sk ztc Q N p = se + (chainModel C).param Q (N.arc ztmh).s := rfl
  have hek : ek ztc Q N p = ee + (chainModel C).param Q (N.arc ztmh).e := rfl
  have hts0 : 0 ≤ (chainModel C).param Q (N.arc ztmh).s := hs0
  have hts1 : (chainModel C).param Q (N.arc ztmh).s < 1 := hs1
  have hte0 : 0 ≤ (chainModel C).param Q (N.arc ztmh).e := he0
  have hte1 : (chainModel C).param Q (N.arc ztmh).e < 1 := he1
  have ha1 := harc.2.1
  have hb1 := harc.2.2.2.1
  rw [hnW] at ha1 hb1
  have hse : se < 2 * C.m + 7 := by
    have : (se : ℝ) < 2 * C.m + 7 := by_grind
    zufc
  have hee : ee < 2 * C.m + 7 := by
    have : (ee : ℝ) < 2 * C.m + 7 := by_grind
    zufc
  have hw := wrap_iff hN hGM hp
  unfold scanLenR
  by_cases hwr : p + 1 < N.arcs.length
  · rw [ite_eq_left hwr]
    have hab := hw.2 hwr
    rw [hsk, hek] at hab
    have hT := card_le_arcWt (M := chainModel C) (a := sk ztc Q N p)
      (b := ek ztc Q N p) ((Finset.Ioo se ee).filter fun q => 6 ≤ q ∧ q < 2 * C.m + 6) (by
        zuco
        rw [Finset.mem_filter, Finset.mem_Ioo] at hq
        refine ztrar
        rw [hsk, hek]; unfold sideInArc; rw [ite_eq_left hab]
        have h1 : ztmsb := by exact_mod_cast hq.1.1
        have h2 : ztmrx := by exact_mod_cast hq.1.2
        grind)
    have hc := card_counted_ge C.m (Finset.Ioo se ee) (fun q hq => by
      grind)
    rw [Nat.card_Ioo] at hc
    omega
  · rw [ite_eq_right hwr]
    have hab : ¬ (sk ztc Q N p < ek ztc Q N p) := fun h => hwr (hw.1 h)
    have hab' := hab
    rw [hsk, hek] at hab'
    have hes : ee ≤ se := by
      have : ztmrj := by_grind
      zuhvg

    have hT := card_le_arcWt (M := chainModel C) (a := sk ztc Q N p)
      (b := ek ztc Q N p) ((Finset.Ioo se ztz ∪ Finset.range ee).filter
      fun q => 6 ≤ q ∧ q < 2 * C.m + 6) (by
        zuco
        rw [Finset.mem_filter, Finset.mem_union, Finset.mem_Ioo, Finset.mem_range] at hq
        refine ztrar
        unfold sideInArc; rw [ite_eq_right hab, hsk, hek]
        rcases hq.1 with h | h
        · left
          have h1 : ztmsb := by exact_mod_cast h.1
          linarith
        · right
          have h2 : ztmrx := by exact_mod_cast h
          linarith)
    have hdis : Disjoint (Finset.Ioo se ztz) (Finset.range ee) := by
      zuzt
      grind
    have hc := card_counted_ge C.m (Finset.Ioo se ztz ∪ Finset.range ee) (fun q hq => by
      grind)
    rw [Finset.card_union_of_disjoint hdis, Nat.card_Ioo, Finset.card_range] at hc
    omega

/-- **A region lists at most five arcs.** -/
theorem region_arcs_le (hP : C.P.Simple) (hC : IsCanonicalNF ztc Q N γ 4) {r : ℕ}
    (hr : r < N.regions.length) : (N.region r).arcs.length ≤ 5 := by
  classical
  zuoj
  zubm
  obtain ⟨hF, -, -, reg, hR, -, hA, hRs, -⟩ := hC.1
  have hU : reg r ∈ (chainModel C).regions ztwjh := hR.1 r hr
  zudhx

  set f : ℕ → ℝ × ℝ := fun j => ((chainModel C).key Q (N.arc j).s, (chainModel C).key Q (N.arc j).e)
  zudht
  have hinj : ztmtv := by
    zukjn
    zuxm

    zuhud
  have hsub : f '' {j | j ∈ L} ⊆ {ab : ℝ × ℝ | (chainModel C).IsArc ztwjh ztcz ab.1 ab.2} := by
    zuczd

    have := (hA.1 j h1).2
    grind
  zufye
  have hdeg := hC.2.1 _ hU
  have hL : ztidp := by
    rw [show ({j | j ∈ L} : Set ℕ) = ↑L.toFinset by ext; simp, Set.ncard_coe_finset,
      List.toFinset_card_of_nodup hnd]
  have h1 : zteea := (Set.InjOn.ncard_image hinj).symm
  zuivh

/-- **At most five arcs per region.** -/
theorem arcs_le_regions (hP : C.P.Simple) (hC : IsCanonicalNF ztc Q N γ 4) :
    N.arcs.length ≤ 5 * N.regions.length := by
  classical
  obtain ⟨reg, hR, hA, -⟩ := NFLoc.isNF_arcs hC.1
  have := Finset.card_le_mul_card_image_of_maps_to (s := Finset.range N.arcs.length)
    (t := Finset.range N.regions.length) (f := fun j => (N.arc j).reg)
    (fun j hj => Finset.mem_range.2 (hA.1 j ztpyw).1) 5 (by
      zuz
      have hr' := Finset.mem_range.1 hr
      calc ((Finset.range N.arcs.length).filter fun j => (N.arc j).reg = r).card
          ≤ (N.region r).arcs.toFinset.card := by
            zulcz
            zun
            rw [Finset.mem_filter, Finset.mem_range] at hj
            rw [List.mem_toFinset]
            exact (hA.2.2.2 r hr' j).2 hj
        _ ≤ (N.region r).arcs.length := List.toFinset_card_le _
        _ ≤ 5 := region_arcs_le hP hC hr')
  zujpk

/-- **The regions of a normal form are one more than its chords.** -/
theorem regions_eq (hP : C.P.Simple) (hN : IsNF ztc Q N) :
    N.regions.length = N.chords.length + 1 := by
  classical
  zuoj
  obtain ⟨hF, hinj, -, reg, hR, -⟩ := hN
  obtain ⟨-, hcard, -⟩ := regionTree ztc Q _ hGM hF
  -- the regions
  have hRn : (chainModel C).regions ztwjh = reg '' Set.Iio N.regions.length := by
    ext U; constructor
    · intro hU; obtain ⟨r, hr, rfl⟩ := hR.2.2 U hU; tauto
    · rintro ⟨r, hr, rfl⟩; exact hR.1 r hr
  have hRc : ((chainModel C).regions ztwjh).ncard = N.regions.length := by
    rw [hRn, Set.InjOn.ncard_image (s := Set.Iio N.regions.length) (f := reg)
      (fun a ha b hb h => hR.2.1 a b ha hb h), ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  -- the chords
  have hFn : N.F ztc Q = ztxbm ''
      Set.Iio N.chords.length := by
    zuitz
    · zuoc
      zuep
      zuifc
      show (N.chord i).toSet _ _ = _
      zuub
    · zuin
      refine ztfju
      zuub
  have hFc : (N.F ztc Q).ncard = N.chords.length := by
    rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length)
      (f := fun i => (N.chord i).toSet ztc Q) ztdul,
      ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]
  omega
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ OracleBook
@[expose] public section
def NCof (w : ℕ) : ℕ := 5 * (1132 * (w + 11) + 40) + 40
variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

/-- The number of arcs of the region of a node, and its arcs. -/
theorem QAt.nodeNa_eq (h : QAt P m O E V H C N B k) {u : ℕ} (hu : u < V.A) :
    nodeNa m V u = (N.region ztoha).arcs.length ∧ rgi N u < N.regions.length ∧
      ∀ t, t < nodeNa m V u → nodeArc m V u t = (N.region ztoha).arcs.getD t 0 := by
  zudnq
  zuiyi
  zubxu
  have huA : u < N.arcs.length := by zunkj; exact hu
  have hj0 : nodeArc0 m V u = sj N u := by
    have := hm.nf.2.2.2.2.2.2.2.2.1 u ztmcu
    zucrf
  have hj0A : sj N u < N.arcs.length := NFLoc.seq_lt hN huA
  have hr : nodeReg m V u = rgi N u := by
    have := (hm.nf.2.2.2.2.2.2.1 _ hj0A).1
    zucag
  have hrR : rgi N u < N.regions.length := (hA.1 _ hj0A).1
  zubhd
  have hna' : nodeNa m V u = (N.region ztoha).arcs.length := by
    zucff
  refine ⟨hna', hrR, fun t ht => ?_⟩
  zugej
  zubiw

/-- The walk edges scanned for an arc record, from the normal form. -/
theorem QAt.arcLen_eq (h : QAt P m O E V H C N B k) {j : ℕ} (hj : j < V.A) :
    arcLenM m V j = scanLenR N zthn N.arcs.length ztdlm ∧
      arcPos m V j < N.arcs.length := by
  zuiyi
  zugpm
  zukfr
  refine ⟨?_, by zunkj; tauto⟩
  zumul
  rw [hsj, ← h.hA, arcSe_eq hm hj, arcEe_eq hm hj]

/-- **The cost of the scan of a node.** -/
theorem QAt.nodeCost_le (h : QAt P m O E V H C N B k) (hP : C.P.Simple) {u : ℕ} :
    nodeCost m V u ≤ NCof ztwwj := by
  zuivt
  have hVm : ztplg := by
    zusz
  unfold nodeCost NCof
  split_ifs with hu
  swap
  · omega
  obtain ⟨hna, hrR, -⟩ := h.nodeNa_eq hu
  have h5 := region_arcs_le hP hC hrR
  have hterm : ∀ i ∈ Finset.Ico 0 (nodeNa m V u),
      1132 * (arcLenM m V (nodeArc m V u i) + 1) + 40 ≤
        1132 * ztyjr + 40 := by
    zug
    rw [Finset.mem_Ico] at hi
    have hjA := ((h.qmem (W := E) le_rfl).node u hu).2.2.2.2 i hi.2
    obtain ⟨e1, e2⟩ := h.arcLen_eq hjA.1
    obtain ⟨b1, b2⟩ := scanLen_le hP hC e2
    grind
  unfold nodeCostFrom
  have := Finset.sum_le_card_nsmul _ _ _ hterm
  zugtw
  have h5' : nodeNa m V u ≤ 5 := by_omega
  have := Nat.mul_le_mul_right (1132 * ztyjr + 40) h5'
  omega

/-- The flagged nodes are at most the length of the list of `D*`. -/
theorem QAt.flagged_le (h : QAt P m O E V H C N B k) :
    ((Finset.range V.μ).filter fun v => m ztdtp = 1).card ≤ V.nD := by
  classical
  calc ((Finset.range V.μ).filter fun v => m ztdtp = 1).card
      ≤ ((Finset.range V.nD).image fun i => m ztdgi).card := by
        zulcz
        zuml
        rw [Finset.mem_filter, Finset.mem_range] at hv
        obtain ⟨i, hi, hiv⟩ := h.dl_all v hv.1 hv.2
        grind
    _ ≤ (Finset.range V.nD).card := Finset.card_image_le
    _ = V.nD := Finset.card_range _

/-- **A cluster has at most `8 k²` nodes.** -/
theorem QAt.clusSize_le (h : QAt P m O E V H C N B k) (l : ℕ) : clusSize m V l ≤ 8 * k ^ 2 := by
  classical
  unfold clusSize
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.range V.μ).filter fun u => lab m V u = l) (fun v => m ztdtp = 1)
  have h1 : (((Finset.range V.μ).filter fun u => lab m V u = l).filter
      fun v => m ztdtp = 1).card ≤ V.nD := by
    refine le_trans ztpyt h.flagged_le
    grind
  have h2 : (((Finset.range V.μ).filter fun u => lab m V u = l).filter
      fun v => ¬ m ztdtp = 1).card ≤ k ^ 2 := by
    refine le_trans ztpyt ztvrs
    intro v hv; simp only [Finset.mem_filter] at hv ⊢; tauto
  have := h.nD_le
  omega

/-- **The cost of the scan of `D*`.** -/
theorem QAt.dstarCost_le (h : QAt P m O E V H C N B k) (hP : C.P.Simple) :
    dstarCost m V ≤ 7 * k ^ 2 * ztbamu + 4 := by
  unfold dstarCost dstarCostFrom
  have := Finset.sum_le_card_nsmul (Finset.Ico 0 V.nD) (fun t => nodeCost m V ztilm + 6)
    ztbamu (fun t _ => by
      have := h.nodeCost_le hP (u := m (V.DL + t)); omega)
  zugtw
  have := Nat.mul_le_mul_right ztbamu h.nD_le
  omega
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open OracleQ OracleBook
@[expose] public section
variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

/-- The chord family has one chord per record. -/
theorem chords_ncard {Q : Polygon} (hN : IsNF ztc Q N) :
    (N.F ztc Q).ncard = N.chords.length := by
  zufru

  have hFn : N.F ztc Q = ztxbm ''
      Set.Iio N.chords.length := by
    zuitz
    · zuoc
      zuep
      zuifc
      show (N.chord i).toSet _ _ = _
      zuub
    · zuin
      refine ztfju
      zuub
  rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length)
    (f := fun i => (N.chord i).toSet ztc Q) ztdul,
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- **Lemma 2.3 for the structure**: `K γ ≤ 60 (2 m + 7)`. -/
theorem QAt.chords_le (h : QAt P m O E V H C N B k) :
    V.K * m ztbpo ≤ 60 * zthn := by
  have hGM : ztycg := Or.inl ztkiq
  zubm
  zuivt
  zuivx
  have := hM.lemma23_walk hF.2.1 hF.1 hC.2.1 hC.2.2.1
  zuhkt
  have hVm : ztplg := by
    zusz
  rw [h.hK, hVm]; linarith

/-- The cost constant of the query. -/
def κq : ℕ := 2 * 10 ^ 12

/-- **The query fits its budget.** -/
theorem QAt.qcost_le (h : QAt P m O E V H C N B k) :
    ((100 + (715 * V.L + 700 + dstarCost m V +
      4 * candCost V (NCof ztwwj) ztpvi + 500) : ℕ) : ℝ) ≤
      (κq : ℝ) * ((m ztbpo : ℝ) ^ ztby * ztbpb ^ ztcd + 1) := by
  zuiws
  zuivt
  have hVm : ztplg := by
    zusz
  set γ := m ztbpo with hγdef
  set w := min γ zthn with hwdef
  have hγ1 : 1 ≤ γ := gamma_pos hP hC
  have hKγ : V.K * γ ≤ 60 * zthn := h.chords_le
  have hK : V.K ≤ 60 * zthn := le_trans (Nat.le_mul_of_pos_right _ hγ1) hKγ
  have hA5 : V.A ≤ 5 * (V.K + 1) := by
    have := arcs_le_regions hP hC
    rw [regions_eq hP hC.1] at this
    rw [h.hA, h.hK]; omega
  have hμ := h.μ_A
  have hL : V.L ≤ Nat.clog 2 ztjnl + 1 := h.L_le
  have hds : dstarCost m V ≤ 7 * k ^ 2 * (NCof w + 6) + 4 := h.dstarCost_le hP
  have hk1 := h.k_pos
  -- the scans
  have hμγ : V.μ * ztgj ≤ 4200 * ztptu + 8 * ztgj := by
    have h1 : V.μ ≤ 5 * V.K + 8 := by_omega
    have h2 : V.K * ztgj ≤ 2 * (V.K * γ) := by_nlinarith
    calc V.μ * ztgj ≤ (5 * V.K + 8) * ztgj := Nat.mul_le_mul_right _ h1
      _ = 5 * (V.K * ztgj) + 8 * ztgj := by_ring
      _ ≤ 4200 * ztptu + 8 * ztgj := by_omega
  have hscan := scan_le_gen (c := 4200) (d := 8) (w := w) hγ1 hμγ h.k_min
    ztff ztgh
  set G := (γ : ℝ) ^ ztby * ztbpb ^ ztcd with hG
  have hG1 : ztbpb ^ ztcd ≤ G := by
    have : (1 : ℝ) ≤ (γ : ℝ) ^ ztby :=
      Real.one_le_rpow (by exact_mod_cast hγ1) by_norm_num
    have h0 : ztykr := by_positivity
    rw [hG]; nlinarith
  have hG0 : (0 : ℝ) ≤ G := by_positivity
  -- the binary searches
  have hAK : V.A + V.K ≤ 2525 * (V.m + 1) := by_omega
  have hlog := Chazelle.Cost.clog_le_eight_rpow ztjnl
  have hpow : ((V.A + V.K : ℕ) : ℝ) ^ ztcd ≤ 2525 * G := by
    have e1 : ((V.A + V.K : ℕ) : ℝ) ^ ztcd ≤ ((2525 : ℝ) * ztbpb) ^ ztcd :=
      Real.rpow_le_rpow by_positivity (by exact_mod_cast hAK) by_norm_num
    rw [Real.mul_rpow by_norm_num by_positivity] at e1
    have e2 : (2525 : ℝ) ^ ztcd ≤ 2525 := by
      have := Real.rpow_le_rpow_of_exponent_le (x := (2525 : ℝ)) by_norm_num
        (show (2 : ℝ) / 3 ≤ 1 by norm_num)
      rwa [Real.rpow_one] at this
    have e3 : ztykr := by_positivity
    nlinarith
  have hLR : (V.L : ℝ) ≤ 20200 * G + 1 := by
    have : (V.L : ℝ) ≤ (Nat.clog 2 ztjnl : ℝ) + 1 := by exact_mod_cast hL
    linarith
  -- the scans in reals
  set X : ℕ := k ^ 2 with hX
  have hX1 : ztphy := Nat.one_le_pow _ _ hk1
  have hscan' : ztbja * (X : ℝ) ≤ 134688 * G := by
    grind
  -- the cost in naturals
  have hNC : NCof w = 5660 * w + 62500 := by unfold NCof; ring
  have hcost : 100 + ztebt ≤
      23424 + 22715 * V.L + 7947142 * (zthkx * X) := by
    unfold candCost
    rw [hNC] at hds ⊢
    have hXw : w ≤ w * X := Nat.le_mul_of_pos_right _ hX1
    grind
  have hcR : ((100 + ztebt :
      ℕ) : ℝ) ≤ 23424 + 22715 * (V.L : ℝ) + 7947142 * (((w : ℝ) + 1) * (X : ℝ)) := by
    exact_mod_cast hcost
  have hκ : (κq : ℝ) = 2 * 10 ^ 12 := by unfold κq; norm_num
  rw [hκ]
  grind
end
end OracleR
end Chazelle.Core
namespace Chazelle.Core
namespace OracleR
open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook NFLoc
@[expose] public section
theorem qOriginIn_unique {c : Config} {r : ℕ} {o o' : QOrigin} (h : QOriginIn c r o)
    (h' : QOriginIn c r o') : o = o' := by
  rcases o with (i | ⟨e, hh⟩) | hh <;> rcases o' with (i' | ⟨e', hh'⟩) | hh' <;>
    simp only [QOriginIn, SymPtIn] at h h' <;>
    first
      | (exfalso; omega)
      | (simp only [QOrigin.sym.injEq, SymPt.vtx.injEq, SymPt.onEdge.injEq, QOrigin.box.injEq]
         omega)

/-- The registers written by the query lie in the bands `bSign`, `bLocate`, `bOQuery`. -/
theorem BQ_band {r : ℕ} (h : BQ r = true) : bandOf r = bSign ∨ bandOf r = bLocate ∨
    bandOf r = bOQuery := by
  unfold bandOf bSign bLocate bOQuery
  simp only [BQ, BLd, BRest, Bk, BCS, BP, BX2, BCP, BDg, BX, BMain, BD, BN, BA, BW, BE, BT, BPo,
    BCa, BL, Bdir, Bloc, Bcmp, BC, Bool.or_eq_true, decide_eq_true_eq] at h
  omega

/-- **The query meets its specification.** -/
theorem query_meets {bands : Finset ℕ} (hb : bSign ∈ bands ∧ bLocate ∈ bands ∧ bOQuery ∈ bands)
    {κ : ℕ} (hκ : κq ≤ κ) :
    Meets qry bands
      (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧ OAt P c.nmem ztdpg ∧
        ∃ o : QOrigin, o.Lt P.n ∧ QOriginIn c ztdtv o)
      (fun P c c' => ∀ H C (o : QOrigin),
        ChainDescAt c.nmem ztbaga zta H C →
        QOriginIn c ztdtv o →
          let z := o.eval zta C ztbqb
          (rd c' bOQuery 5 = 1 → ∃ t, FirstHit C.set z ztbqb t ∧
            rd c' bOQuery 6 < P.n ∧
            Visibility.rayPt z ztbqb t ∈ (Qof P).edge ztrvp) ∧
          ztxxw)
      (fun _ c => ⌈(κ : ℝ) * ((c.nmem ztpde : ℝ) ^ ztby *
        ztxqe ^ ztcd + 1)⌉₊) := by
  intro P W c hw ⟨hG, hHW, ⟨E, hE, hOE, hrob⟩, o, hol, ho⟩ _
  set O := rd c bOQuery 0 with hOdef
  obtain ⟨V, H, C, N, B, k, hA⟩ := hrob.holds
  have hEW : E ≤ W := by rw [← hE]; exact hw.2 _
  have hn : ztgag := by
    have := C.add_one_le; rw [hA.CQ, show (Qof P).n = P.n from shear_n _ _] at this; omega
  have hW : ztiya := by unfold hostWords at hHW; omega
  obtain ⟨c', k', ex, hk, hf, hans⟩ := qry_exec hG hW hA hEW hHW c hw rfl rfl ho hol
    (NC := NCof ztywl) (CS := 8 * k ^ 2)
    (fun u _ => (hA.withQ o _).nodeCost_le hA.simple)
    (fun u _ => (hA.withQ o _).clusSize_le _)
  refine ⟨c', k', ex, ?_, ?_, frame_of_frameB hf (fun r hr => ztcp) k'⟩
  · -- the cost
    beta_reduce
    have hc := hA.qcost_le
    have hk' : (k' : ℝ) ≤ ((100 + (715 * V.L + 700 + dstarCost c.nmem V +
        4 * candCost V (NCof ztywl) ztpvi + 500) : ℕ) : ℝ) := by
      exact_mod_cast hk
    have hD : c.nmem (c.nmem ztdpg + 2) = V.m := by rw [hA.lD, hA.dm]
    rw [hD]
    have hG0 : (0 : ℝ) ≤ (c.nmem ztbpo : ℝ) ^ ztby * ztbpb ^ ztcd + 1 :=
      by positivity
    have hκR : (κq : ℝ) ≤ κ := by exact_mod_cast hκ
    have : (k' : ℝ) ≤ (κ : ℝ) * ((c.nmem ztbpo : ℝ) ^ ztby *
        ztbpb ^ ztcd + 1) := by_nlinarith
    exact_mod_cast this.trans ztvag
  · -- the answer
    intro H' C' o' hC' ho'
    have hCC : ztkzv := NFLoc.chain_eq_of_desc hC' (by rw [hA.lD]; exact hA.desc)
    have hoo : o' = o := qOriginIn_unique ho' ho
    subst hCC hoo
    tauto
  · rcases BQ_band hr with h | h | h <;> zvmwc
    · grind
    · grind
    grind
  · zudsz
end
end OracleR
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
def copyBack : Stmt :=
  .whileLtN 210056 210054
    (block [.addN 210058 30005 210056, .loadN 210059 210058, .addN 210058 210055 210056,
      .storeN 210058 210059, .addN 210056 210056 210034])

/-- **Sort the segment at `X = r210055` of length `r210054` in place.** -/
def sortBack : Stmt :=
  .seq ztksb
    (.seq ztvdh (.seq (.instr (.constN 210056 0)) copyBack))

/-- The registers of band `bDownDrv` the copy-back loop writes. -/
def Bcb (r : ℕ) : Bool := decide (210056 ≤ r ∧ r ≤ 210059)
theorem wrM_cb : wrM Bcb
    (block [.addN 210058 30005 210056, .loadN 210059 210058, .addN 210058 210055 210056,
      .storeN 210058 210059, .addN 210056 210056 210034]) = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 1000000 in
theorem cbBody_exec (d : Config) (hw : WordsBounded W d) {i X src : ℕ}
    (h56 : d.nreg 210056 = i) (h55 : d.nreg 210055 = X) (h05 : d.nreg 30005 = src)
    (h34 : d.nreg 210034 = 1) (hW1 : src + i ≤ W) (hW2 : X + i ≤ W) (hW3 : i + 1 ≤ W) :
    ∃ d' k, Exec P W (block [.addN 210058 30005 210056, .loadN 210059 210058,
      .addN 210058 210055 210056, .storeN 210058 210059, .addN 210056 210056 210034]) d d' k ∧
      k = 5 ∧ d'.nreg 210056 = i + 1 ∧ d'.nmem = upd d.nmem zttec ztpan ∧
      FrameM Bcb d d' := by
  obtain ⟨d', k, ex, hk, h1, h2⟩ : ∃ d' k, Exec P W (block [.addN 210058 30005 210056,
      .loadN 210059 210058, .addN 210058 210055 210056, .storeN 210058 210059,
      .addN 210056 210056 210034]) d d' k ∧ k = 5 ∧ d'.nreg 210056 = i + 1 ∧
      d'.nmem = upd d.nmem zttec ztpan := by
    exec_block
    all_goals try (config_simp; (try simp only [h56, h55, h05, h34]); omega)
    simp_all
  exact ⟨d', k, ex, hk, h1, h2, exec_frameM ex wrM_cb⟩

/-- **The copy-back loop.** -/
theorem copyBack_exec {d : Config} (hw : WordsBounded W d) {X src len : ℕ}
    (h56 : d.nreg 210056 = 0) (h54 : d.nreg 210054 = len) (h55 : d.nreg 210055 = X)
    (h05 : d.nreg 30005 = src) (h34 : d.nreg 210034 = 1) (hsep : X + len ≤ src)
    (hW : src + len + 1 ≤ W) :
    ∃ d' k, Exec P W copyBack d d' k ∧ k ≤ 7 * len + 2 ∧ WordsBounded W d' ∧
      seg d'.nmem X len = seg d.nmem src len ∧
      (∀ a, ztlfv → d'.nmem a = d.nmem a) ∧ FrameM Bcb d d' := by
  let Inv : ℕ → Config → Prop := fun i e => WordsBounded W e ∧ e.nreg 210056 = i ∧
    e.nreg 210054 = len ∧ e.nreg 210055 = X ∧ e.nreg 30005 = src ∧ e.nreg 210034 = 1 ∧
    FrameM Bcb d e ∧
    ∀ a, e.nmem a = if X ≤ a ∧ a < X + i then d.nmem (src + zttel) else d.nmem a
  obtain ⟨d', k, ex, ⟨w', _, _, _, _, _, hf', hm'⟩, hk⟩ := forLoop (P := P) (W := W)
    (ir := 210056) (nr := 210054) Inv 5 len
    ztchw
    (fun i e hi ⟨hw, h1, h2, h3, h4, h5, hf, hm⟩ => by
      obtain ⟨e', k, ex, hk, h1', hm', hf'⟩ := cbBody_exec (P := P) e hw h1 h3 h4 h5
        by_omega by_omega by_omega
      have g : ∀ r, Bcb r = false → e'.nreg r = e.nreg r := hf'.1
      refine ⟨e', k, ex, ⟨ex.wb_right, h1', (g _ by_decide).trans h2, (g _ by_decide).trans h3,
        (g _ by_decide).trans h4, (g _ by_decide).trans h5, hf.trans hf', fun a => ?_⟩,
        by omega⟩
      zugec
      grind)
    (j := 0) ⟨hw, h56, h54, h55, h05, h34, FrameM.refl _ _, fun a => by_simp⟩
    ztbg
  refine ⟨d', k, ex, by_omega, w', ?_, fun a ha => ?_, hf'⟩
  · zumum
  grind
set_option maxHeartbeats 2000000 in
/-- **Sorting a segment of event codes in place.** -/
theorem sortBack_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {X len D T : ℕ} {M : Model} {L : List zte}
    (h55 : c.nreg 210055 = X) (h54 : c.nreg 210054 = len) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L.length)
    (hwf : ModelDescWF P ztm c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hL : ChordTriplesOK M zta L) (hR : RecsAt c.nmem T L)
    (hTA : T + 8 * L.length ≤ c.nreg ALLOC) (hX : X + len ≤ c.nreg ALLOC)
    (hcodes : ∀ x ∈ seg c.nmem X len, x < 2 * L.length)
    (hroom : c.nreg ALLOC + SortR.sortCost 11010 len + 1 ≤ W) :
    ∃ c' k, Exec P W sortBack c c' k ∧ k ≤ SortR.sortCost 11010 len + 7 * len + 5 ∧
      WordsBounded W c' ∧
      (seg c'.nmem X len).Perm ztrws ∧
      (seg c'.nmem X len).Pairwise ztydp ∧
      (∀ a, a < c.nreg ALLOC → ztlfv → c'.nmem a = c.nmem a) ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + SortR.sortCost 11010 len ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bcb r = false → r ≠ ALLOC →
        c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bcb r = false →
        c'.rreg r = c.rreg r) ∧
      ztgo ∧ c'.output = c.output ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L.length ∧
      ztgsd := by
  zudk
  -- the sort's inputs
  obtain ⟨c₁, k₁, e₁, hk₁, v3, v4, g₁, m₁, rr₁, rm₁, o₁⟩ : ∃ c₁ k₁,
      Exec P W ztksb c c₁ k₁ ∧ k₁ = 2 ∧
      c₁.nreg 30003 = X ∧ c₁.nreg 30004 = len ∧
      (∀ r, r ≠ 30003 → r ≠ 30004 → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    exec_block
    simp_all
  zud
  have hA₁ : ztdc := g₁ _ by_decide by_decide
  -- the sort
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (m₀ := c₁.nmem) (A₀ := c₁.nreg ALLOC)
    (D := D) (T := T) (M := M) (L := L) by_omega by_simp_all
    by_simp_all hL by_simp_all by_omega c₁.nreg
  have hJ₁ : EvJ c₁.nmem ztbmq D T ztpu c₁.nreg c₁ :=
    ⟨by_simp_all, by_simp_all,
      by simp_all, fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hseg : seg c₁.nmem (c₁.nreg 30003) (seg c.nmem X len).length = seg c.nmem X len := by
    simp_all
  obtain ⟨c₂, k₂, e₂, hk₂, J₂, F₂, s₁, s₂, Ls, hLs, hperm, hsort⟩ := SortR.sortStmt_exec
    (P := P) (W := W) hcmp by_decide
    ztxgs
    ztxwp w₁ hJ₁ ztnxz
    ztrws hseg by_simp_all by_simp_all
    (by rw [seg_length, hA₁]; omega)
  rw [seg_length] at hk₂ s₂ hLs
  obtain ⟨j1, j2, j3, j4, j5⟩ := J₂
  zue
  -- the counter and the copy back
  have e₃ := Exec.constN (P := P) w₂ 210056 0 ztbg
  set c₃ : Config := { c₂ with nreg := upd c₂.nreg 210056 0 } with hc₃
  have g₃ : ∀ r, r ≠ 210056 → c₃.nreg r = c₂.nreg r := fun r hr => by_simp_all
  have hb2 : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → r ≠ ALLOC →
      c₂.nreg r = c₁.nreg r := fun r hr hra => F₂.1 r (by
        omega) hra
  have b21 : ztbvh :=
    fun r h1 h2 => by zunsf; omega
  have b3 : ∀ r, 30000 ≤ r → r < 40000 → bandOf r = bSort := fun r h1 h2 => by
    simp [bandOf, bSort]; omega
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, hf₄⟩ := copyBack_exec (P := P) e₃.wb_right
    (X := X) (src := c₂.nreg 30005) (len := len) by_rfl
    (by rw [g₃ _ by_decide, hb2 _ ztlgd by_decide,
      g₁ _ by_decide by_decide, h54])
    (by rw [g₃ _ by_decide, hb2 _ ztlgd by_decide,
      g₁ _ by_decide by_decide, h55])
    (g₃ _ by_decide)
    (by rw [g₃ _ by_decide, hb2 _ ztlgd by_decide,
      g₁ _ by_decide by_decide, h34])
    by_omega (by have := F₂.2.2.2.2.2.2; omega)
  have g₄ : ∀ r, Bcb r = false → c₄.nreg r = c₃.nreg r := hf₄.1
  zugll
  have hA₂' := F₂.2.2.2.2.2.2
  rw [hA₁] at hA₂ hA₂'
  refine ⟨c₄, k₁ + (k₂ + (1 + k₄)), .seq e₁ ztcb, by_omega, w₄, ?_, ?_,
    fun a ha hX' => ?_, ?_, ?_, fun r hr hcb hra => ?_, fun r hr hcb => ?_, fun a ha => ?_, ?_,
    ?_, ?_, ?_, fun r h1 h2 => ?_⟩
  · grind
  · rw [hs₄, show c₃.nmem = c₂.nmem from rfl, hLs]
    zuflt
    have ha' := hcodes a ztqql
    have hb' := hcodes b ztqqm
    unfold evLeB at hab; grind
  · grind
  · zufmy
  · zufmy
  · have h56 : r ≠ 210056 := fun h => by subst h; simp [Bcb] at hcb
    rw [g₄ r hcb, g₃ r h56, hb2 r hr hra]
    exact g₁ r ztbay (fun h => by
      grind)
  · rw [hf₄.2.1 r hcb, show c₃.rreg = c₂.rreg from rfl,
      F₂.2.1 r by_omega, rr₁]
  · rw [hf₄.2.2.1, show c₃.rmem = c₂.rmem from rfl, F₂.2.2.2.1 a by_omega, rm₁]
  · rw [hf₄.2.2.2, show c₃.output = c₂.output from rfl, F₂.2.2.2.2.1, o₁]
  · rw [g₄ _ by_decide, g₃ _ by_decide, j1]
  · rw [g₄ _ by_decide, g₃ _ by_decide, j2]
  · rw [g₄ _ by_decide, g₃ _ by_decide, j3]
  · rw [g₄ _ (by zuodw; omega), g₃ _ by_omega,
      j5 r h1 h2, g₁ _ by_omega by_omega]
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
def bsBody : Stmt :=
  .seq (block [.addN 210057 210037 210050, .loadN 210052 210057, .addN 210057 210036 210050,
      .loadN 210053 210057, .subN 210054 210053 210052, .addN 210055 210048 210052])
    (.seq sortBack (.instr (.addN 210050 210050 210034)))

/-- **Sort every bucket.** -/
def bsLoop : Stmt := .whileLtN 210050 210039 bsBody

/-! ## Lists -/

/-- The array split into its buckets. -/
theorem seg_flat (bk m : ℕ → ℕ) (n R : ℕ) :
    ∀ b, seg m R (bstart bk n b) =
      (List.range b).flatMap fun b' => seg m ztoxp ztrkv := by
  intro b
  induction b with
  | zero => rfl
  | succ b ih => rw [bstart_succ, seg_add, ih, List.range_succ, List.flatMap_append]; simp

/-- The bucket segments of `bktList`. -/
theorem seg_bkt {m : ℕ → ℕ} {bk : ℕ → ℕ} {n A base R : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (h : seg m R n = bktList bk n A base) {b : ℕ} (hb : b ≤ A) :
    seg m ztoxq ztbvo = (bfilt bk n b).map ztbtu := by
  have hn := bstart_all hA
  have hl := seg_flat bk m n R ztbo
  rw [hn, h] at hl
  unfold bktList at hl
  have hle : b + 1 ≤ A + 1 := by_omega
  zuhhi
  -- split both sides at bucket `b`
  have hsplit : ∀ (f : ℕ → List ℕ), (List.range ztbo).flatMap f =
      (List.range b).flatMap f ++ f b ++ ((List.range d).map (b + 1 + ·)).flatMap f := by
    intro f
    rw [hd, List.range_add, List.range_succ, List.flatMap_append, List.flatMap_append]
    simp
  rw [hsplit, hsplit] at hl
  have hlen : ((List.range b).flatMap fun b' => (bfilt bk n b').map ztbtu).length =
      ((List.range b).flatMap fun b' => seg m ztoxp ztrkv).length := by
    rw [← seg_flat, seg_length]
    have := bktPre_length (bk := bk) n b base
    tauto
  have hlen2 : (seg m ztoxq ztbvo).length =
      ((bfilt bk n b).map ztbtu).length := by rw [seg_length, List.length_map]; rfl
  rw [List.append_assoc, List.append_assoc] at hl
  have h1 := List.append_inj hl hlen
  exact (List.append_inj h1.2 hlen2.symm).1.symm

/-! ## The loop -/

/-- The band-`bDownDrv` registers the bucket loop writes. -/
def Bbl (r : ℕ) : Bool := decide (210050 ≤ r ∧ r ≤ 210059)
theorem wrM_bs1 : wrM Bbl (block [.addN 210057 210037 210050, .loadN 210052 210057,
    .addN 210057 210036 210050, .loadN 210053 210057, .subN 210054 210053 210052,
    .addN 210055 210048 210052]) = true := by_decide

/-- The fixed data of the bucket loop: the model descriptor, the chord list `L` with its event
records, the arrays of the bucket distribution. -/
structure BsEnv (P : Polygon) (W : ℕ) (m₁ : ℕ → ℕ) (bk : ℕ → ℕ) (n A base Cb Sb Rb D T : ℕ)
    (M : Model) (L : List zte) : Prop where
  good : GoodEnv P
  hw : hostWords P.n ≤ W
  bkA : ∀ q, q < n → bk q ≤ A
  hS : Sb = Cb + ztbo
  hR : Rb = Sb + ztbo
  cnt : ∀ b, b ≤ A → m₁ (Cb + b) = bstart bk n ztds
  st : ∀ b, b ≤ A → m₁ (Sb + b) = bstart bk n b
  wf : ModelDescWF P Cb m₁ D
  desc : ModelDescAt m₁ D zta M
  ok : ChordTriplesOK M zta L
  recs : RecsAt m₁ T L
  hT : T + 8 * L.length ≤ Cb
  codes : base + n ≤ 2 * L.length

/-- The invariant of the bucket loop. -/
structure BsI (P : Polygon) (W : ℕ) (c₀ : Config) (m₁ : ℕ → ℕ) (bk : ℕ → ℕ)
    (n A base Cb Sb Rb D T : ℕ) (M : Model) (L : List zte) (j : ℕ) (d : Config) : Prop where
  wb : WordsBounded W d
  r34 : d.nreg 210034 = 1
  r36 : d.nreg 210036 = Cb
  r37 : d.nreg 210037 = Sb
  r39 : d.nreg 210039 = A + 1
  r48 : d.nreg 210048 = Rb
  r50 : d.nreg 210050 = j
  r40 : d.nreg 40000 = D
  r42 : d.nreg 42000 = T
  r42' : d.nreg 42001 = 2 * L.length
  alloc : Rb + n ≤ d.nreg ALLOC
  low : ∀ a, a < Rb → d.nmem a = m₁ a
  done : ∀ b, b < j → (seg d.nmem ztchb ztbvo).Perm
    ((bfilt bk n b).map ztbtu) ∧
    (seg d.nmem ztchb ztbvo).Pairwise ztydp
  todo : ∀ b, j ≤ b → b ≤ A →
    seg d.nmem ztchb ztbvo = (bfilt bk n b).map ztbtu
  fr : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bbl r = false → r ≠ ALLOC →
    d.nreg r = c₀.nreg r
  r43 : ∀ r, 43000 ≤ r → r < 44000 → d.nreg r = c₀.nreg r
  rr : ∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bbl r = false →
    d.rreg r = c₀.rreg r
  rm : ∀ a, a < Rb + n → d.rmem a = c₀.rmem a
  out : d.output = c₀.output

/-- The cost of one bucket. -/
def bsCost (bk : ℕ → ℕ) (n b : ℕ) : ℕ := SortR.sortCost 11010 ztbvo + 7 * bcnt bk n b + 12
section exec
variable {P : Polygon} {W : ℕ}
variable {c₀ : Config} {m₁ bk : ℕ → ℕ} {n A base Cb Sb Rb D T : ℕ} {M : Model} {L : List (ℕ × ℕ × ℕ)}
set_option maxHeartbeats 2000000 in
theorem bsBody_exec
 (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L) {j : ℕ} (hj : j < A + 1)
    {d : Config} (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L j d)
    (hroom : d.nreg ALLOC + bsCost bk n j + 1 ≤ W) :
    ∃ d' k, Exec P W bsBody d d' k ∧ BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L ztl d' ∧
      k ≤ bsCost bk n j ∧ d'.nreg ALLOC ≤ d.nreg ALLOC + bsCost bk n j := by
  have hst := E.st j by_omega
  have hcn := E.cnt j by_omega
  have hSb : Sb + j < Rb := by rw [E.hR]; omega
  have hCb : Cb + j < Rb := by rw [E.hR, E.hS]; omega
  have hl1 := I.low _ hSb
  have hl2 := I.low _ hCb
  have hbn := bstart_le E.bkA ztkxq
  have hsucc := bstart_succ (bk := bk) n j
  have hW : Rb + n + 1 ≤ W := by have := I.alloc; omega
  -- the bucket's segment
  obtain ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁, hf₁⟩ : ∃ d₁ k₁, Exec P W
      (block [.addN 210057 210037 210050,
      .loadN 210052 210057, .addN 210057 210036 210050, .loadN 210053 210057,
      .subN 210054 210053 210052, .addN 210055 210048 210052]) d d₁ k₁ ∧ k₁ = 6 ∧
      d₁.nreg 210055 = Rb + bstart bk n j ∧ d₁.nreg 210054 = bcnt bk n j ∧
      d₁.nreg 210050 = j ∧ d₁.nmem = d.nmem ∧ FrameM Bbl d d₁ := by
    obtain ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁⟩ : ∃ d₁ k₁, Exec P W
        (block [.addN 210057 210037 210050,
        .loadN 210052 210057, .addN 210057 210036 210050, .loadN 210053 210057,
        .subN 210054 210053 210052, .addN 210055 210048 210052]) d d₁ k₁ ∧ k₁ = 6 ∧
        d₁.nreg 210055 = Rb + bstart bk n j ∧ d₁.nreg 210054 = bcnt bk n j ∧
        d₁.nreg 210050 = j ∧ d₁.nmem = d.nmem := by
      have w := I.wb
      exec_block
      all_goals try (config_simp; (try zundp); omega)
      refine ztdqw <;> config_simp <;>
        zundp; omega
    exact ⟨d₁, k₁, e₁, hk₁, v55, v54, v50, hm₁, exec_frameM e₁ wrM_bs1⟩
  have g₁ := hf₁.1
  zud
  have hlow₁ : ∀ a, a < Rb → d₁.nmem a = m₁ a := fun a ha => by rw [hm₁]; exact I.low a ha
  obtain ⟨hM₁, hwf₁⟩ := desc_agree E.wf E.desc fun a ha => hlow₁ a (by
    omega)
  have hrec₁ : RecsAt d₁.nmem T L := fun c hc => by
    obtain ⟨a1, a2, a3, a4⟩ := E.recs c hc
    have hT := E.hT
    grind
  have hA₁ : ztsib := g₁ _ by_decide
  have hseg₁ : seg d₁.nmem (Rb + bstart bk n j) (bcnt bk n j) = (bfilt bk n j).map ztbtu := by
    rw [hm₁]; exact I.todo j le_rfl by_omega
  -- sort the segment
  obtain ⟨d₂, k₂, e₂, hk₂, w₂, hperm, hsort, hm₂, hA₂, hA₂', g₂, rr₂, rm₂, o₂, v40, v42, v42', v43⟩ :=
    sortBack_exec (P := P) (W := W) E.good E.hw d₁ w₁ (X := Rb + bstart bk n j)
      (len := bcnt bk n j) (D := D) (T := T) (M := M) (L := L) v55 v54
      (by zunct; exact I.r34) (by zunct; exact I.r40)
      (by zunct; exact I.r42) (by zunct; exact I.r42')
      (hwf₁.mono (by have := I.alloc; omega)) hM₁ E.ok hrec₁
      (by have := I.alloc; rw [hA₁]; rw [E.hR, E.hS] at this; have := E.hT; omega)
      (by rw [hA₁]; have := I.alloc; omega)
      (by rw [hseg₁]; intro x hx; rw [List.mem_map] at hx
          obtain ⟨q, hq, rfl⟩ := hx; rw [mem_bfilt] at hq; have := E.codes; omega)
      (by rw [hA₁]; unfold bsCost at hroom; omega)
  -- the next bucket
  have b21 : ztbvh :=
    fun r h1 h2 => by zunsf; omega
  have v50₂ : d₂.nreg 210050 = j := by
    rw [g₂ _ by_grind by_decide by_decide, v50]
  have v34₂ : d₂.nreg 210034 = 1 := by
    rw [g₂ _ by_grind by_decide by_decide, g₁ _ by_decide, I.r34]
  have e₃ := Exec.addN (P := P) w₂ 210050 210050 210034 by_omega
  set d₃ : Config := { d₂ with nreg := upd d₂.nreg 210050 _ }
    with hd₃
  have g₃ : ∀ r, r ≠ 210050 → d₃.nreg r = d₂.nreg r := fun r hr => by rw [hd₃]; zumwy
  have bcb : ∀ r, Bbl r = false → Bcb r = false := fun r hb => by
    simp only [Bbl, decide_eq_false_iff_not] at hb
    zuodw; omega
  -- registers of band `bDownDrv` other than the loop's
  have k21 : ∀ r, 210000 ≤ r → r < 220000 → Bbl r = false → d₃.nreg r = d.nreg r := by
    intro r h1 h2 hb
    rw [g₃ r (by intro h; subst h; simp [Bbl] at hb), g₂ r by_grind by_grind
      ztu, g₁ r hb]
  have hst' : bstart bk n j + bcnt bk n j = bstart bk n _ := hsucc.symm
  refine ⟨d₃, k₁ + ztcaj, .seq e₁ ztcr, ?_, by unfold bsCost; omega,
    by zunjz; unfold bsCost; omega⟩
  refine ⟨e₃.wb_right, by_grind,
    by zunby; exact I.r36,
    by zunby; exact I.r37,
    by zunby; exact I.r39,
    by zunby; exact I.r48, ?_,
    by grind, by_grind,
    by grind,
    by zunjz; have := I.alloc; omega,
    fun a ha => ?_, fun b hb => ?_, fun b hb1 hb2 => ?_, fun r hr hb hra => ?_,
    fun r h1 h2 => ?_, fun r hr hb => ?_, fun a ha => ?_, ?_⟩
  · rw [hd₃]; zumzo
    omega
  · show d₂.nmem a = m₁ a
    rw [hm₂ a (by rw [hA₁]; have := I.alloc; omega) by_omega, hlow₁ a ha]
  · show (seg d₂.nmem _ _).Perm _ ∧ _
    rcases Nat.lt_or_ge b j with hbj | hbj
    · have hcong : seg d₂.nmem ztchb ztbvo =
          seg d.nmem ztchb ztbvo := by
        zujrw
        have h1 := bstart_mono (bk := bk) n (show b + 1 ≤ j by omega)
        rw [bstart_succ] at h1
        have h2 := bstart_le E.bkA ztmoa
        zuftd

      zuowa; exact I.done b hbj
    grind
  · show seg d₂.nmem _ _ = _
    have hcong : seg d₂.nmem ztchb ztbvo =
        seg d.nmem ztchb ztbvo := by
      zujrw
      have h1 := bstart_mono (bk := bk) n (show j + 1 ≤ b by omega)
      have h2 := bstart_le E.bkA (show b + 1 ≤ A + 1 by omega)
      rw [bstart_succ] at h2
      zuftd

    zuowa; exact I.todo b by_omega hb2
  · have hr50 : r ≠ 210050 := fun h => by subst h; simp [Bbl] at hb
    rw [g₃ r hr50, g₂ r hr by_grind hra, g₁ r hb]
    exact I.fr r hr hb hra
  · rw [g₃ r by_omega, v43 r h1 h2, g₁ r (by simp [Bbl]; omega)]; exact I.r43 r h1 h2
  · show d₂.rreg r = _
    rw [rr₂ r hr by_grind, hf₁.2.1 r hb]
    exact I.rr r hr hb
  · show d₂.rmem a = _
    rw [rm₂ a (by rw [hA₁]; have := I.alloc; omega), hf₁.2.2.1]; exact I.rm a ha
  · show d₂.output = _
    rw [o₂, hf₁.2.2.2]; exact I.out

/-- **The bucket loop.** -/
theorem bsLoop_exec
 (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L)
    {d : Config} (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L 0 d)
    (hroom : d.nreg ALLOC + ztyby + 1 ≤ W) :
    ∃ d' k, Exec P W bsLoop d d' k ∧ BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L ztbo d' ∧
      k ≤ (∑ b ∈ Finset.range ztbo, ztfga) + 2 ∧
      d'.nreg ALLOC ≤ d.nreg ALLOC + ∑ b ∈ Finset.range ztbo, bsCost bk n b := by
  obtain ⟨d', k, ex, ⟨hI, hA⟩, hk⟩ := forLoopSum (P := P) (W := W) (ir := 210050) (nr := 210039)
    (fun j e => BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L j e ∧
      e.nreg ALLOC ≤ d.nreg ALLOC + ∑ b ∈ Finset.range j, bsCost bk n b)
    (bsCost bk n) ztbo
    (fun j e ⟨h, _⟩ => ⟨h.wb, h.r50, h.r39⟩)
    (fun j e hj ⟨h, hA⟩ => by
      have hsum : ∑ b ∈ Finset.range ztl, bsCost bk n b ≤
          ∑ b ∈ Finset.range ztbo, bsCost bk n b :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 by_omega)
      rw [Finset.sum_range_succ] at hsum
      obtain ⟨e', k, ex, h', hk, hA'⟩ := bsBody_exec E by_omega h by_omega
      exact ⟨e', k, ex, ⟨h', by rw [Finset.sum_range_succ]; omega⟩, hk⟩)
    (j := 0) ⟨I, by_simp⟩ ztbg
  refine ⟨d', k, ex, hI, by_simp_all, hA⟩

/-- **The sorted new codes**: with the buckets ordered by the comparator, the array is a sorted
permutation of the new codes. -/
theorem bs_result
 (E : BsEnv P W m₁ bk n A base Cb Sb Rb D T M L) {d : Config}
    (I : BsI P W c₀ m₁ bk n A base Cb Sb Rb D T M L ztbo d)
    (hmono : ∀ q q', q < n → q' < n → bk q < bk q' →
      BuildNF.codeLe M zta L zttgr zttgq) :
    (seg d.nmem Rb n).Perm ztxqd ∧
      (seg d.nmem Rb n).Pairwise ztydp := by
  have hn := bstart_all E.bkA
  have hflat := seg_flat bk d.nmem n Rb ztbo
  zvmxq at hflat
  rw [hflat]
  constructor
  · -- permutation
    have h1 : ((List.range _).flatMap fun b => seg d.nmem _ _).Perm
        _ :=
      List.Perm.flatMap_left _ fun b hb => (I.done b ztpzr).1
    refine h1.trans ?_
    -- `bktList` is a permutation of the codes
    have h2 : (bktList bk n A base).Perm ztxqd := by
      refine (List.perm_ext_iff_of_nodup ?_ ?_).2 fun x => ?_
      · unfold bktList
        zujgw
        refine ⟨fun b _ => ?_, ?_⟩
        · exact ((List.nodup_range).filter _).map ztpbe
        · refine List.pairwise_lt_range.imp fun {b b'} hbb => ?_
          show List.Disjoint _ _
          rw [List.disjoint_left]
          zueth
          rw [List.mem_map] at hx hx'
          obtain ⟨q, hq, rfl⟩ := hx
          obtain ⟨q', hq', hqq⟩ := hx'
          zuilm

      · exact (List.nodup_range).map ztpbe
      · unfold bktList
        simp only [List.mem_flatMap, List.mem_range, List.mem_map, mem_bfilt]
        constructor
        · rintro ⟨b, -, q, ⟨hq, -⟩, rfl⟩; simp_all
        · zuecr
          exact ⟨bk q, by have := E.bkA q hq; omega, q, by_omega, rfl⟩
    zucvi
  · -- sortedness
    zumln
    refine ⟨fun b hb => (I.done b ztpzr).2, ?_⟩
    refine List.pairwise_lt_range.imp_of_mem fun {b b'} hb hb' hbb x hx y hy => ?_
    have hx' := (I.done b ztpzr).1.mem_iff.1 hx
    have hy' := (I.done b' (List.mem_range.1 hb')).1.mem_iff.1 hy
    rw [List.mem_map] at hx' hy'
    obtain ⟨q, hq, rfl⟩ := hx'
    obtain ⟨q', hq', rfl⟩ := hy'
    zuilm
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
theorem merge_congr {f g : ℕ → ℕ → Bool} :
    ∀ (l₁ l₂ : List ℕ), (∀ x ∈ l₁, ∀ y ∈ l₂, f x y = g x y) →
      List.merge l₁ l₂ f = List.merge l₁ l₂ g := by
  intro l₁ l₂
  induction l₁ generalizing l₂ with
  | nil => intro _; simp
  | cons x xs ih =>
    induction l₂ with
    | nil => intro _; simp
    | cons y ys ih₂ =>
      zuq
      rw [List.cons_merge_cons, List.cons_merge_cons, h x by_simp y by_simp]
      split_ifs
      · simp_all
      · simp_all

/-- The merge registers. -/
def mgSetup : Stmt :=
  block [.constN 30006 1, .copyN 30007 210070, .copyN 30008 210071, .copyN 30011 210072,
    .copyN 30012 210073, .constN 30013 0, .copyN 30014 210072, .constN 30015 0]

/-- **The merge.** -/
def mergeE : Stmt := .seq mgSetup (SortR.mergeLoop evCmp)
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **Merging two sorted lists of event codes.** -/
theorem mergeE_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {S Dst mid hi D T : ℕ} {M : Model} {L : List zte}
    {E E₂ : List ℕ}
    (h70 : c.nreg 210070 = S) (h71 : c.nreg 210071 = Dst) (h72 : c.nreg 210072 = mid)
    (h73 : c.nreg 210073 = hi) (hmh : mid ≤ hi)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L.length)
    (hwf : ModelDescWF P Dst c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hL : ChordTriplesOK M zta L) (hR : RecsAt c.nmem T L) (hTA : T + 8 * L.length ≤ Dst)
    (hE : seg c.nmem S mid = E) (hE₂ : seg c.nmem (S + mid) ztjxw = E₂)
    (hcodes : ∀ x ∈ E ++ E₂, x < 2 * L.length) (hSD : S + hi ≤ Dst)
    (hroom : Dst + hi + 1 ≤ W) :
    ∃ c' k, Exec P W mergeE c c' k ∧ k ≤ (11010 + 16) * hi + 10 ∧ WordsBounded W c' ∧
      seg c'.nmem Dst hi = List.merge E E₂ (DownDrv.codeLeB M zta L) ∧
      (∀ a, (a < Dst ∨ Dst + hi ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      c'.nreg ALLOC = c.nreg ALLOC ∧
      (∀ r, bandOf r ∉ ({bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L.length ∧
      ztgsd := by
  zudk
  -- the registers
  obtain ⟨c₁, k₁, e₁, hk₁, v6, v7, v8, v11, v12, v13, v14, v15, g₁, m₁, rr₁, rm₁, o₁⟩ :
      ∃ c₁ k₁, Exec P W mgSetup c c₁ k₁ ∧ k₁ = 8 ∧ c₁.nreg 30006 = 1 ∧ c₁.nreg 30007 = S ∧
      c₁.nreg 30008 = Dst ∧ c₁.nreg 30011 = mid ∧ c₁.nreg 30012 = hi ∧ c₁.nreg 30013 = 0 ∧
      c₁.nreg 30014 = mid ∧ c₁.nreg 30015 = 0 ∧
      (∀ r, (r < 30000 ∨ 40000 ≤ r) → c₁.nreg r = c.nreg r) ∧ c₁.nmem = c.nmem ∧
      c₁.rreg = c.rreg ∧ c₁.rmem = c.rmem ∧ c₁.output = c.output := by
    unfold mgSetup
    exec_block
    all_goals try omega
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, rfl, rfl, rfl, rfl⟩ <;>
      config_simp <;> (try simp only [h70, h71, h72, h73])
    zup
  zud
  -- the comparator
  have hcmp := evCmp_ok (P := P) (W := W) hG hWn (m₀ := c₁.nmem) (A₀ := Dst) (D := D) (T := T)
    (M := M) (L := L) by_omega by_simp_all by_simp_all hL
    by_simp_all hTA c₁.nreg
  have hJ₁ : EvJ c₁.nmem Dst D T ztpu c₁.nreg c₁ :=
    ⟨by_simp_all, by_simp_all, by_simp_all,
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hI : SortR.MergeInv W (EvJ c₁.nmem Dst D T ztpu c₁.nreg)
      ztzep {bSign, bBuild} Dst c₁ c₁ S Dst 0 mid hi E E₂ c₁ :=
    { wb := w₁, hJ := hJ₁, loc := SortR.Loc.refl _ _ _, one := v6, rsrc := v7, rdst := v8,
      rmid := v11, rhi := v12, keep := fun _ _ _ _ _ _ _ _ _ _ => rfl,
      lo_i := by rw [v13], i_mid := by_omega, mid_j := by zuowc,
      j_hi := by_omega, rk := by_omega,
      bsrc := by_omega, bdst := by_omega, disj := Or.inl by_omega, dA := le_rfl,
      ma := by_simp_all,
      mb := by_simp_all,
      out := by_simp_all,
      mem := fun _ _ => rfl }
  obtain ⟨c₂, k₂, e₂, I₂, hk₂, hseg⟩ := SortR.mergeLoop_inv (P := P) hcmp
    ztnxz by_decide hI
  rw [v15, Nat.sub_zero] at hk₂
  rw [Nat.add_zero, Nat.sub_zero] at hseg
  obtain ⟨j1, j2, j3, j4, j5⟩ := I₂.hJ
  obtain ⟨l1, l2, l3, l4, l5⟩ := I₂.loc
  refine ⟨c₂, k₁ + k₂, .seq e₁ e₂, by_omega, I₂.wb, ?_, fun a ha => ?_, fun r hr hra => ?_, ?_,
    fun r hr => ?_, by_grind, by_grind, j1, j2, j3, fun r h1 h2 => ?_⟩
  · zumof
    refine merge_congr E E₂ fun x hx y hy => ?_
    have hx' := hcodes x ztszh
    have hy' := hcodes y (List.mem_append_right _ hy)
    unfold evLeB DownDrv.codeLeB; grind
  · zufzt
    · grind
    · rw [I₂.mem a ztbh, m₁]
  · have h1 : bandOf r ∉ ({bSign, bBuild} : Finset ℕ) := fun h => hr (by
      grind)
    have h2 : bandOf r ≠ bSort := fun h => hr ztdmg
    rw [l1 r h1 h2 hra]
    exact g₁ r (by simp only [bandOf, bSort] at h2; omega)
  · rw [I₂.keep ALLOC ztbt by_decide by_decide by_decide by_decide by_decide
      by_decide by_decide by_decide, g₁ _ by_decide]
  · grind
  grind
end exec
def spl0 : Stmt :=
  block [.constN 210034 1, .addN 210025 210003 210021, .copyN 210026 9999,
    .addN 210029 210025 210025, .addN 210027 210003 210003, .addN 210028 210021 210021,
    .addN 210066 210025 210025, .addN 210066 210066 210025, .addN 9999 9999 210066,
    .addN 210067 210003 210003, .addN 210067 210067 210003,
    .copyN 210061 210067, .copyN 210062 210002, .copyN 210063 210026]

/-- The arguments of the second copy. -/
def spl1 : Stmt :=
  block [.addN 210061 210021 210021, .addN 210061 210061 210021, .copyN 210062 210020,
    .addN 210063 210026 210067]

/-- The arguments of the records. -/
def spl2 : Stmt := block [.copyN 40000 210001, .copyN 40001 210026, .copyN 40002 210025]

/-- The arguments of the bucket distribution. -/
def spl3 : Stmt := block [.copyN 210031 210028, .copyN 210032 210023, .copyN 210033 210027]

/-- The merge arrays and the arguments of the copy of `E`. -/
def spl5 : Stmt :=
  block [.copyN 210030 9999, .addN 210071 210030 210029, .addN 9999 210071 210029,
    .copyN 210070 210030, .copyN 210072 210027, .copyN 210073 210029,
    .copyN 210061 210027, .copyN 210062 210004, .copyN 210063 210030]

/-- The arguments of the copy of the sorted new codes. -/
def spl6 : Stmt := block [.copyN 210061 210028, .copyN 210062 210048, .addN 210063 210030 210027]

/-- The arguments of the sorted build. -/
def spl7 : Stmt :=
  block [.copyN 40000 210001, .copyN 40001 210026, .copyN 40002 210025, .copyN 40004 210071]

/-- The outputs. -/
def spl8 : Stmt :=
  block [.copyN 210002 210026, .copyN 210003 210025, .copyN 210004 210071, .copyN 210005 40003]
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
theorem chordListAt_of_seg {m m' : ℕ → ℕ} {B A : ℕ} {L : List zte}
    (h : ChordListAt m B L) (hs : seg m' A ztssw = seg m B ztssw) :
    ChordListAt m' A L := by
  zug
  have e : ∀ q, q < 3 * L.length → m' (A + q) = m (B + q) := fun q hq => by
    have := congrArg ztpbr hs
    zugze

  zufjc
  zusk
  · simp_all
  · rw [show A + 3 * i + 1 = A + ztpuc by ring, e _ by_omega,
      show B + ztpuc = B + 3 * i + 1 by ring]; exact h2
  · rw [show A + 3 * i + 2 = A + ztpud by ring, e _ by_omega,
      show B + ztpud = B + 3 * i + 2 by ring]; exact h3

/-- A chord list is the concatenation of its two parts. -/
theorem chordListAt_append {m : ℕ → ℕ} {A : ℕ} {L L₂ : List zte}
    (h₁ : ChordListAt m A L) (h₂ : ChordListAt m ztgcw L₂) :
    ChordListAt m A ztfi := by
  zug
  zuelb

  · zuela
  · zuets

/-- The registers `spl0 ; cpS ; spl1 ; cpS` writes. -/
def BsA (r : ℕ) : Bool :=
  decide (210025 ≤ r ∧ r ≤ 210029) || decide zttxp || decide (210060 ≤ r ∧ r ≤ 210067) ||
    decide ztyc
theorem wrM_spl0 : wrM BsA spl0 = true := by_decide

/-- The registers `spl1` writes. -/
def Bs1 (r : ℕ) : Bool := decide ztdez
theorem wrM_spl1 : wrM Bs1 spl1 = true := by_decide
variable {c c' : Config}
theorem FrameM.of_s1 (h : FrameM Bs1 c c') : FrameM BsA c c' :=
  h.mono fun r hr => by
    simp only [Bs1, BsA, Bool.or_eq_true, decide_eq_true_eq] at hr ⊢; omega
theorem Bcp_BsA {r : ℕ} (h : Bcp r = true) : BsA r = true := by
  simp only [Bcp, BsA, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem FrameM.of_cp (h : FrameM Bcp c c') : FrameM BsA c c' :=
  h.mono fun _r hr => Bcp_BsA hr
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The new chord list.** -/
theorem splA_exec (c : Config) (hw : WordsBounded W c) {B K B₂ K₂ : ℕ}
    {L L₂ : List (ℕ × ℕ × ℕ)} (h02 : c.nreg 210002 = B) (h03 : c.nreg 210003 = K)
    (h20 : c.nreg 210020 = B₂) (h21 : c.nreg 210021 = K₂) (hK : K = L.length)
    (hK₂ : K₂ = L₂.length) (hL : ChordListAt c.nmem B L) (hL₂ : ChordListAt c.nmem B₂ L₂)
    (hB : B + 3 * K ≤ c.nreg ALLOC) (hB₂ : B₂ + 3 * K₂ ≤ c.nreg ALLOC)
    (hroom : c.nreg ALLOC + 3 * (K + K₂) + 22 ≤ W) :
    ∃ c' k, Exec P W (.seq spl0 (.seq cpS (.seq spl1 cpS))) c c' k ∧
      k ≤ 21 * (K + K₂) + 30 ∧ WordsBounded W c' ∧
      c'.nreg 210025 = K + K₂ ∧ c'.nreg 210026 = c.nreg ALLOC ∧ c'.nreg 210027 = 2 * K ∧
      c'.nreg 210028 = 2 * K₂ ∧ c'.nreg 210029 = 2 * (K + K₂) ∧ c'.nreg 210034 = 1 ∧
      c'.nreg ALLOC = c.nreg ALLOC + 3 * (K + K₂) ∧
      ChordListAt c'.nmem (c.nreg ALLOC) (L ++ L₂) ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧ FrameM BsA c c' ∧ c'.rreg = c.rreg := by
  set A₀ := c.nreg ALLOC with hA₀
  -- sizes and the first copy's arguments
  obtain ⟨c₁, k₁, e₁, hk₁, v25, v26, v27, v28, v29, v34, vA, v67, v61, v62, v63, hm₁⟩ :
      ∃ c₁ k₁, Exec P W spl0 c c₁ k₁ ∧ k₁ = 14 ∧ c₁.nreg 210025 = K + K₂ ∧ c₁.nreg 210026 = A₀ ∧
      c₁.nreg 210027 = 2 * K ∧ c₁.nreg 210028 = 2 * K₂ ∧ c₁.nreg 210029 = 2 * (K + K₂) ∧
      c₁.nreg 210034 = 1 ∧ c₁.nreg ALLOC = A₀ + 3 * (K + K₂) ∧ c₁.nreg 210067 = 3 * K ∧
      c₁.nreg 210061 = 3 * K ∧ c₁.nreg 210062 = B ∧ c₁.nreg 210063 = A₀ ∧ c₁.nmem = c.nmem := by
    unfold spl0
    exec_block
    all_goals try (config_simp; (try simp only [h02, h03, h21, show c.nreg 9999 = A₀ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h02, h03, h21, show c.nreg 9999 = A₀ from rfl]) <;> omega
  have f₁ := exec_frameM e₁ wrM_spl0
  -- copy `L`
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, hs₂, hm₂, f₂⟩ := cpS_exec (P := P) e₁.wb_right v61 v62 v63 v34
    (Or.inl (by omega)) (by omega) (by omega)
  have g₂ : ∀ r, Bcp r = false → c₂.nreg r = c₁.nreg r := f₂.1
  -- the second copy's arguments
  obtain ⟨c₃, k₃, e₃, hk₃, w61, w62, w63, hm₃⟩ : ∃ c₃ k₃, Exec P W spl1 c₂ c₃ k₃ ∧ k₃ = 4 ∧
      c₃.nreg 210061 = 3 * K₂ ∧ c₃.nreg 210062 = B₂ ∧ c₃.nreg 210063 = A₀ + 3 * K ∧
      c₃.nmem = c₂.nmem := by
    have h21' : c₂.nreg 210021 = K₂ := by rw [g₂ _ (by decide), f₁.1 _ (by decide), h21]
    have h20' : c₂.nreg 210020 = B₂ := by rw [g₂ _ (by decide), f₁.1 _ (by decide), h20]
    have h26' : c₂.nreg 210026 = A₀ := by rw [g₂ _ (by decide), v26]
    have h67' : c₂.nreg 210067 = 3 * K := by rw [g₂ _ (by decide), v67]
    unfold spl1
    exec_block
    all_goals try (config_simp; (try simp only [h21', h20', h26', h67']); omega)
    refine ⟨rfl, ?_, ?_, ?_, rfl⟩ <;> config_simp <;> (try simp only [h21', h20', h26', h67']);
      omega
  have f₃ := exec_frameM e₃ wrM_spl1
  have g₃ : ∀ r, Bs1 r = false → c₃.nreg r = c₂.nreg r := f₃.1
  -- copy `L₂`
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, f₄⟩ := cpS_exec (P := P) e₃.wb_right w61 w62 w63
    (by rw [g₃ _ (by decide), g₂ _ (by decide), v34]) (Or.inl (by omega)) (by omega) (by omega)
  have g₄ : ∀ r, Bcp r = false → c₄.nreg r = c₃.nreg r := f₄.1
  have k : ∀ r, Bcp r = false → Bs1 r = false → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    simp_all
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), by omega, w₄,
    by rw [k _ (by decide) (by decide)]; omega, by rw [k _ (by decide) (by decide)]; omega,
    by rw [k _ (by decide) (by decide)]; omega, by rw [k _ (by decide) (by decide)]; omega,
    by rw [k _ (by decide) (by decide)]; omega, by rw [k _ (by decide) (by decide)]; omega,
    by rw [k _ (by decide) (by decide)]; exact vA, ?_, fun a ha => ?_,
    ((f₁.trans (FrameM.of_cp f₂)).trans (FrameM.of_s1 f₃)).trans (FrameM.of_cp f₄), ?_⟩
  · refine chordListAt_append (chordListAt_of_seg hL ?_) (chordListAt_of_seg hL₂ ?_)
    · rw [← hK]
      rw [seg_congr (m := c₄.nmem) (m' := c₂.nmem) fun i hi => by
        grind]
      simp_all
    · rw [← hK, ← hK₂, hs₄, hm₃]
      apply seg_congr; grind
  · grind
  · funext r
    exact exec_frameM2 (.seq e₁ (.seq e₂ (.seq e₃ e₄))) (BN := BsA) (BR := fun _ => false)
      (by decide) r rfl
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
theorem wrM_spl2 : wrM (fun r => decide ztngk) spl2 = true := by_decide
theorem notin_rot {x a b c : ℕ} (h : x ∉ ({a, b, c} : Finset ℕ)) : x ∉ ({c, a, b} : Finset ℕ) := by
  simp_all
theorem band4_notin {r : ℕ} (h : bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ)) :
    r < 40000 ∨ 50000 ≤ r := by
  zvncv at h; omega
theorem wrM_spl3 : wrM (fun r => decide ztnfn) spl3 = true := by_decide
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 2000000 in
/-- **The records of `L'` and the bucket arguments.** -/
theorem splB1_exec (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {D B' K K₂ A : ℕ} {M : Model} {L' : List zte}
    (h01 : c.nreg 210001 = D) (h26 : c.nreg 210026 = B') (h25 : c.nreg 210025 = K + K₂)
    (h27 : c.nreg 210027 = 2 * K) (h28 : c.nreg 210028 = 2 * K₂)
    (h23 : c.nreg 210023 = A) (hlen : L'.length = K + K₂)
    (hok : ChordTriplesOK M zta L') (hCL : ChordListAt c.nmem B' L')
    (hA : c.nreg ALLOC = B' + 3 * ztlc)
    (hroom : c.nreg ALLOC + 32 * ztlc + 22 ≤ W) :
    ∃ c' k, Exec P W ztncw c c' k ∧ k ≤ 32 * ztlc + 24 ∧
      WordsBounded W c' ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = c.nreg ALLOC ∧ c'.nreg 42001 = 2 * ztlc ∧
      c'.nreg 210031 = 2 * K₂ ∧ c'.nreg 210032 = A ∧ c'.nreg 210033 = 2 * K ∧
      c'.nreg ALLOC = c.nreg ALLOC + 10 * ztlc ∧
      RecsAt c'.nmem ztm L' ∧
      zth ∧
      (∀ a, c.nreg ALLOC + 10 * ztlc ≤ a → c'.nmem a = c.nmem a ∨ True) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → ztdia →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      ztego ∧
      ztgo ∧ c'.output = c.output := by
  -- the records' arguments
  obtain ⟨c₁, k₁, e₁, hk₁, v0, v1, v2, hm₁⟩ : ∃ c₁ k₁, Exec P W spl2 c c₁ k₁ ∧ k₁ = 3 ∧
      c₁.nreg 40000 = D ∧ c₁.nreg 40001 = B' ∧ c₁.nreg 40002 = K + K₂ ∧ c₁.nmem = c.nmem := by
    unfold spl2
    exec_block
    simp_all
  have f₁ := exec_frameM e₁ wrM_spl2
  have g₁ : ∀ r, ztoft → c₁.nreg r = c.nreg r := fun r hr =>
    f₁.1 r by_grind
  have hA₁' : ztdc := g₁ _ by_decide
  -- the records
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, F₂, d1, d2, d3, -, -, -, -, hrec, -, hA₂⟩ :=
    DownNF.phaseAS_exec (P := P) hWn c₁ e₁.wb_right (M := M) (L := L') (D := D) (B := B')
      (SE := c₁.nreg 40004) hok by_simp_all by_omega v0 v1
      by_omega rfl by_omega
  rw [hA₁'] at hrec hA₂ d2
  rw [hlen] at hA₂ hk₂ d3
  have b21 : ∀ r, 210000 ≤ r → r < 220000 → bandOf r ∉ ({bBuild, bSort, bSign} : Finset ℕ) := by
    zucxf
    zvncv
    omega
  have g₂ : ∀ r, 210000 ≤ r → r < 220000 → c₂.nreg r = c.nreg r := fun r h1 h2 => by
    rw [F₂.1 r ztlge ztu, g₁ r by_omega]
  -- the bucket arguments
  obtain ⟨c₃, k₃, e₃, hk₃, u31, u32, u33, hm₃⟩ : ∃ c₃ k₃, Exec P W spl3 c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 210031 = 2 * K₂ ∧ c₃.nreg 210032 = A ∧ c₃.nreg 210033 = 2 * K ∧
      c₃.nmem = c₂.nmem := by
    have a28 := g₂ 210028 by_norm_num by_norm_num
    have a23 := g₂ 210023 by_norm_num by_norm_num
    have a27 := g₂ 210027 by_norm_num by_norm_num
    unfold spl3
    exec_block
    simp_all
  have f₃ := exec_frameM e₃ wrM_spl3
  have g₃ : ∀ r, ztdia → c₃.nreg r = c₂.nreg r := fun r hr =>
    f₃.1 r by_grind
  refine ⟨c₃, k₁ + zttl, .seq e₁ ztcr, by_omega, e₃.wb_right,
    by simp_all, by_simp_all,
    by simp_all, u31, u32, u33, by rw [g₃ _ by_decide]; omega,
    by simp_all, fun a ha => ?_, fun _ _ => Or.inr trivial, fun r hr hr' hra => ?_,
    fun r hr => ?_, fun a ha => ?_, ?_⟩
  · rw [hm₃, F₂.2.2.1 a by_omega, hm₁]
  · rw [g₃ r hr', F₂.1 r ztwar hra]
    exact f₁.1 r (by zvnan; have := band4_notin hr; omega)
  · rw [exec_frameM2 e₃ (BN := fun r => decide ztnfn) (BR := fun _ => false)
      by_decide r rfl, F₂.2.1 r ztwar]
    exact f₁.2.1 r (by zvnan; have := band4_notin hr; omega)
  · rw [f₃.2.2.1, F₂.2.2.2.1 a by_omega, f₁.2.2.1]
  · rw [f₃.2.2.2, F₂.2.2.2.2.1, f₁.2.2.2]

/-- The cost of the buckets part. -/
noncomputable def splB2Cost (bk : ℕ → ℕ) (n A : ℕ) : ℕ :=
  21 * ztbo + 21 * n + 31 + ∑ b ∈ Finset.range ztbo, ztfga + 2
set_option maxHeartbeats 4000000 in
/-- **The sorted new codes, from the records.** -/
theorem splB2_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {D T BB n A base : ℕ} {M : Model} {L' : List zte}
    {bk : ℕ → ℕ}
    (h22 : c.nreg 210022 = BB) (h31 : c.nreg 210031 = n) (h32 : c.nreg 210032 = A)
    (h33 : c.nreg 210033 = base) (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T)
    (h42' : c.nreg 42001 = 2 * L'.length)
    (hwf : ModelDescWF P ztm c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hok : ChordTriplesOK M zta L') (hrec : RecsAt c.nmem T L')
    (hT : T + 8 * L'.length ≤ c.nreg ALLOC) (hcodes : base + n ≤ 2 * L'.length)
    (hBB : BB + n ≤ c.nreg ALLOC)
    (hbkd : ∀ q, q < n → c.nmem ztgzy = bk q) (hbk : ∀ q, q < n → bk q ≤ A)
    (hmono : ∀ q q', q < n → q' < n → bk q < bk q' →
      BuildNF.codeLe M zta L' zttgr zttgq)
    (hroom : c.nreg ALLOC + splB2Cost bk n A + 1 ≤ W) :
    ∃ c' k, Exec P W zthqh c c' k ∧
      k ≤ splB2Cost bk n A ∧ WordsBounded W c' ∧
      c'.nreg 210048 = c.nreg ALLOC + ztbo + ztbo ∧
      (seg c'.nmem ztvgh n).Perm ztxqd ∧
      (seg c'.nmem ztvgh n).Pairwise (BuildNF.codeLe M zta L') ∧
      c'.nreg 210048 + n ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ c.nreg ALLOC + splB2Cost bk n A ∧
      zth ∧
      c'.nreg 40000 = D ∧ c'.nreg 42000 = T ∧ c'.nreg 42001 = 2 * L'.length ∧
      c'.nreg 210034 = 1 ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → ztdib →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → ztdib →
        c'.rreg r = c.rreg r) ∧
      ztgo ∧ c'.output = c.output := by
  set A₂ := c.nreg ALLOC with hA₂
  obtain ⟨c₄, k₄, e₄, hk₄, b36, b37, b48, bA, b34, b39, bseg, bst, bcn, blow, bfr, brr', brm, bout⟩ :=
    bktS_exec (P := P) c hw (BB := BB) (n := n) (A := A) (base := base) (bk := bk) h22 h31 h32 h33
      hBB hbkd hbk (by unfold splB2Cost at hroom; omega) by_omega
  zucc
  have e₅ := Exec.constN (P := P) w₄ 210050 0 ztbg
  set c₅ : Config := { c₄ with nreg := upd c₄.nreg 210050 0 } with hc₅
  have g₅ : ∀ r, r ≠ 210050 → c₅.nreg r = c₄.nreg r := fun r hr => by_simp_all
  have bkf : ∀ r, Bbkt r = false → r ≠ 210050 → c₅.nreg r = c.nreg r := fun r hr h50 => by
    simp_all
  have hlow5 : ∀ a, a < A₂ → c₅.nmem a = c.nmem a := fun a ha => blow a ha
  have Ebs : BsEnv P W c₅.nmem bk n A base A₂ ztzsw ztzbk D T M L' :=
    { good := hG, hw := hWn, bkA := hbk, hS := rfl, hR := rfl,
      cnt := fun b hb => bcn b hb, st := fun b hb => bst b hb,
      wf := (desc_agree hwf hM (m' := c₅.nmem) fun a ha => hlow5 a ha).2,
      desc := (desc_agree hwf hM (m' := c₅.nmem) fun a ha => hlow5 a ha).1,
      ok := hok,
      recs := fun q hq => by
        obtain ⟨r1, r2, r3, r4⟩ := hrec q hq
        exact ⟨by zunfy; exact r1, by zunfy; exact r2,
          by zunfy; exact r3, by zunfy; exact r4⟩
      hT := hT, codes := hcodes }
  have Ibs : BsI P W c₅ c₅.nmem bk n A base A₂ ztzsw ztzbk D T M L'
      0 c₅ :=
    { wb := e₅.wb_right, r34 := by_simp_all, r36 := by_simp_all,
      r37 := by_simp_all, r39 := by_simp_all,
      r48 := by_simp_all, r50 := by_rfl,
      r40 := by rw [bkf _ by_decide by_decide, h40],
      r42 := by rw [bkf _ by_decide by_decide, h42],
      r42' := by rw [bkf _ by_decide by_decide, h42'],
      alloc := by zunho,
      low := fun _ _ => rfl, done := fun b hb => absurd hb by_omega,
      todo := fun b _ hb => seg_bkt hbk bseg hb,
      fr := fun _ _ _ _ => rfl, r43 := fun _ _ _ => rfl, rr := fun _ _ _ => rfl,
      rm := fun _ _ => rfl, out := rfl }
  have hle : ∑ b ∈ Finset.range ztbo, bsCost bk n b ≤
      ∑ b ∈ Finset.range ztbo, ztfga :=
    Finset.sum_le_sum fun b _ => by_omega
  have hroom' : c₅.nreg ALLOC + ztyby + 1 ≤ W := by
    zunho; unfold splB2Cost at hroom; omega
  obtain ⟨c₆, k₆, e₆, I₆, hk₆, hA₆⟩ := bsLoop_exec Ebs Ibs hroom'
  obtain ⟨hperm, hsort⟩ := bs_result Ebs I₆ hmono
  have hc5A : c₅.nreg ALLOC = A₂ + ztbo + ztbo + n := by zunho
  refine ⟨c₆, k₄ + (1 + k₆), .seq e₄ ztcsd, by unfold splB2Cost; omega, I₆.wb,
    I₆.r48, by zuoeb; omega, by zuoeb; omega,
    by zuoeb; have := I₆.alloc; omega, by unfold splB2Cost; omega,
    fun a ha => by rw [I₆.low a by_omega, hlow5 a ha], I₆.r40, I₆.r42, I₆.r42', I₆.r34,
    fun r hr hr' hra => ?_, fun r hr hr' => ?_, fun a ha => ?_, ?_⟩
  · zudyt
    rw [I₆.fr r hr hb hra, g₅ r by_omega, bfr r (by
      simp only [Bbkt, Bool.or_eq_false_iff, decide_eq_false_iff_not]; exact ⟨by_omega, hra⟩)]
  · zudyt
    rw [I₆.rr r hr hb, show c₅.rreg = c₄.rreg from rfl, brr']
  · rw [I₆.rm a by_omega, show c₅.rmem = c₄.rmem from rfl, brm]
  · rw [I₆.out, show c₅.output = c₄.output from rfl, bout]
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
@[expose] public section
def splC : Stmt := .seq spl5 (.seq cpS (.seq spl6 (.seq cpS mergeE)))

/-- The registers `spl5`, `spl6` write. -/
def Bs56 (r : ℕ) : Bool :=
  decide (r = 210030) || decide ztdez || decide (210070 ≤ r ∧ r ≤ 210073) ||
    decide ztyc

/-- The registers `spl6` writes. -/
def Bs6 (r : ℕ) : Bool := decide ztdez
theorem wrM2_spl5 : wrM2 Bs56 ztczi spl5 = true := by_decide
theorem wrM2_spl6 : wrM2 Bs6 ztczi spl6 = true := by_decide
theorem wrM2_cpS : wrM2 Bcp ztczi cpS = true := by_decide

/-- The cost of `splC`. -/
def splCCost (K K₂ : ℕ) : ℕ := 14 * K + 7 * ztjfa + 11026 * ztxka + 40
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The merged event list.** -/
theorem splC_exec (hG : GoodEnv P) (hWn : hostWords P.n ≤ W) (c : Config)
    (hw : WordsBounded W c) {D T SE Rb K K₂ : ℕ} {M : Model} {L' : List (ℕ × ℕ × ℕ)}
    {E E₂ : List ℕ}
    (h27 : c.nreg 210027 = 2 * K) (h28 : c.nreg 210028 = 2 * K₂) (h29 : c.nreg 210029 = 2 * (K + K₂))
    (h04 : c.nreg 210004 = SE) (h48 : c.nreg 210048 = Rb) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T) (h42' : c.nreg 42001 = 2 * L'.length)
    (hlen : L'.length = K + K₂)
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem D) (hM : ModelDescAt c.nmem D (Qof P) M)
    (hok : ChordTriplesOK M (Qof P) L') (hrec : RecsAt c.nmem T L')
    (hT : T + 8 * L'.length ≤ c.nreg ALLOC)
    (hE : seg c.nmem SE (2 * K) = E) (hSE : SE + 2 * K ≤ c.nreg ALLOC)
    (hE₂ : seg c.nmem Rb (2 * K₂) = E₂) (hRb : Rb + 2 * K₂ ≤ c.nreg ALLOC)
    (hcodes : ∀ x ∈ E ++ E₂, x < 2 * L'.length)
    (hroom : c.nreg ALLOC + 4 * (2 * (K + K₂)) + splCCost K K₂ + 1 ≤ W) :
    ∃ c' k, Exec P W splC c c' k ∧ k ≤ splCCost K K₂ ∧ WordsBounded W c' ∧
      c'.nreg 210071 = c.nreg ALLOC + 2 * (K + K₂) ∧
      c'.nreg ALLOC = c.nreg ALLOC + 2 * (K + K₂) + 2 * (K + K₂) ∧
      seg c'.nmem (c'.nreg 210071) (2 * (K + K₂)) = List.merge E E₂ (DownDrv.codeLeB M (Qof P) L') ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bs56 r = false → Bcp r = false →
        r ≠ ALLOC → c'.nreg r = c.nreg r) ∧
      (∀ r, bandOf r ∉ ({bSign, bBuild} : Finset ℕ) → c'.rreg r = c.rreg r) ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  set A₃ := c.nreg ALLOC with hA₃
  set h := 2 * (K + K₂) with hh
  -- the arrays and the arguments of the first copy
  obtain ⟨c₁, k₁, e₁, hk₁, v30, v71, vA, v70, v72, v73, v61, v62, v63, hm₁⟩ : ∃ c₁ k₁,
      Exec P W spl5 c c₁ k₁ ∧ k₁ = 9 ∧ c₁.nreg 210030 = A₃ ∧ c₁.nreg 210071 = A₃ + h ∧
      c₁.nreg ALLOC = A₃ + h + h ∧ c₁.nreg 210070 = A₃ ∧ c₁.nreg 210072 = 2 * K ∧
      c₁.nreg 210073 = h ∧ c₁.nreg 210061 = 2 * K ∧ c₁.nreg 210062 = SE ∧ c₁.nreg 210063 = A₃ ∧
      c₁.nmem = c.nmem := by
    unfold spl5
    exec_block
    all_goals try (config_simp; (try simp only [h29, h27, h04, show c.nreg 9999 = A₃ from rfl]); omega)
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩ <;>
      (try simp only [show ALLOC = 9999 from rfl]) <;> config_simp <;>
      (try simp only [h29, h27, h04, show c.nreg 9999 = A₃ from rfl])
  have g₁ : ∀ r, Bs56 r = false → c₁.nreg r = c.nreg r := (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).1
  -- copy `E`
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, hs₂, hm₂, f₂⟩ := cpS_exec (P := P) e₁.wb_right v61 v62 v63
    (by rw [g₁ _ (by decide), h34]) (Or.inl (by omega)) (by omega) (by omega)
  have g₂ : ∀ r, Bcp r = false → c₂.nreg r = c₁.nreg r := f₂.1
  -- the arguments of the second copy
  obtain ⟨c₃, k₃, e₃, hk₃, u61, u62, u63, hm₃⟩ : ∃ c₃ k₃, Exec P W spl6 c₂ c₃ k₃ ∧ k₃ = 3 ∧
      c₃.nreg 210061 = 2 * K₂ ∧ c₃.nreg 210062 = Rb ∧ c₃.nreg 210063 = A₃ + 2 * K ∧
      c₃.nmem = c₂.nmem := by
    have a28 : c₂.nreg 210028 = 2 * K₂ := by rw [g₂ _ (by decide), g₁ _ (by decide), h28]
    have a48 : c₂.nreg 210048 = Rb := by rw [g₂ _ (by decide), g₁ _ (by decide), h48]
    have a30 : c₂.nreg 210030 = A₃ := by rw [g₂ _ (by decide), v30]
    have a27 : c₂.nreg 210027 = 2 * K := by rw [g₂ _ (by decide), g₁ _ (by decide), h27]
    unfold spl6
    exec_block
    all_goals try (config_simp; (try simp only [a28, a48, a30, a27]); omega)
    simp_all
  have g₃ : ∀ r, Bs6 r = false → c₃.nreg r = c₂.nreg r :=
    (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).1
  -- copy the new codes
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, hs₄, hm₄, f₄⟩ := cpS_exec (P := P) e₃.wb_right u61 u62 u63
    (by rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide), h34]) (Or.inl (by omega))
    (by omega) (by omega)
  have g₄ : ∀ r, Bcp r = false → c₄.nreg r = c₃.nreg r := f₄.1
  -- registers before the merge
  have k5 : ∀ r, Bcp r = false → Bs6 r = false → c₄.nreg r = c₁.nreg r := fun r h1 h2 => by
    grind
  have k : ∀ r, Bcp r = false → Bs56 r = false → c₄.nreg r = c.nreg r := fun r h1 h2 => by
    rw [k5 r h1 (by
      simp only [Bs56, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h2
      simp only [Bs6, decide_eq_false_iff_not]; omega), g₁ r h2]
  have hlow4 : ∀ a, a < A₃ → c₄.nmem a = c.nmem a := fun a ha => by
    grind
  have hseg4 : seg c₄.nmem A₃ (2 * K) = E := by
    rw [seg_congr (m' := c₂.nmem) fun i hi => by grind, hs₂, hm₁, hE]
  have hseg4' : seg c₄.nmem (A₃ + 2 * K) (h - 2 * K) = E₂ := by
    rw [show h - 2 * K = 2 * K₂ by omega, hs₄, hm₃]
    rw [seg_congr (m' := c.nmem) fun i hi => by grind, hE₂]
  obtain ⟨hM₄, hwf₄⟩ := desc_agree hwf hM (m' := c₄.nmem) fun a ha => hlow4 a ha
  have hrec4 : RecsAt c₄.nmem T L' := fun q hq => by
    obtain ⟨r1, r2, r3, r4⟩ := hrec q hq
    exact ⟨by rw [hlow4 _ (by omega)]; exact r1, by rw [hlow4 _ (by omega)]; exact r2,
      by rw [hlow4 _ (by omega)]; exact r3, by rw [hlow4 _ (by omega)]; exact r4⟩
  -- the merge
  obtain ⟨c₅, k₅, e₅, hk₅, w₅, hseg5, hm₅, fr₅, hA₅, rr₅, rm₅, o₅, -, -, -, -⟩ :=
    mergeE_exec (P := P) (W := W) hG hWn c₄ w₄ (S := A₃) (Dst := A₃ + h) (mid := 2 * K) (hi := h)
      (D := D) (T := T) (M := M) (L := L') (E := E) (E₂ := E₂)
      (by rw [k5 _ (by decide) (by decide), v70]) (by rw [k5 _ (by decide) (by decide), v71])
      (by rw [k5 _ (by decide) (by decide), v72]) (by rw [k5 _ (by decide) (by decide), v73])
      (by omega) (by rw [k _ (by decide) (by decide), h40])
      (by rw [k _ (by decide) (by decide), h42]) (by rw [k _ (by decide) (by decide), h42'])
      (hwf₄.mono (by omega)) hM₄ hok hrec4 (by omega) hseg4 hseg4' hcodes (by omega) (by omega)
  have hA₄ : c₄.nreg ALLOC = A₃ + h + h := by rw [k5 _ (by decide) (by decide), vA]
  refine ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))),
    by unfold splCCost; omega, w₅, ?_, by grind, ?_, fun a ha => ?_,
    fun r hr h1 h2 hra => ?_, fun r hr => ?_, ?_, ?_⟩
  · rw [fr₅ _ (by decide) (by decide), k5 _ (by decide) (by decide), v71]
  · rw [fr₅ _ (by decide) (by decide), k5 _ (by decide) (by decide), v71]
    omega
  · grind
  · grind
  · rw [rr₅ r hr, exec_frameM2 e₄ wrM2_cpS r rfl, exec_frameM2 e₃ wrM2_spl6 r rfl,
      exec_frameM2 e₂ wrM2_cpS r rfl, exec_frameM2 e₁ wrM2_spl5 r rfl]
  · rw [rm₅, f₄.2.2.1, (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).2.2.1, f₂.2.2.1,
      (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).2.2.1]
  · rw [o₅, f₄.2.2.2, (exec_frameM e₃ (by decide : wrM Bs6 spl6 = true)).2.2.2, f₂.2.2.2,
      (exec_frameM e₁ (by decide : wrM Bs56 spl5 = true)).2.2.2]
end exec
variable {bk : ℕ → ℕ}
/-- The cost of one bucket, against the bucket bound. -/
theorem bsCost_le {n b Mb : ℕ} (h : bcnt bk n b ≤ Mb) :
    bsCost bk n b + 2 ≤ 11047 * bcnt bk n b * ztvg + 11054 := by
  unfold bsCost SortR.sortCost
  have hc := Nat.clog_mono_right 2 h
  have : bcnt bk n b * (Nat.clog 2 ztbvo + 1) ≤ bcnt bk n b * ztvg :=
    Nat.mul_le_mul_left _ by_omega
  grind

/-- **The cost of the bucket part.** -/
theorem splB2Cost_le {n A Mb : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (hM : ∀ b, bcnt bk n b ≤ Mb) :
    splB2Cost bk n A ≤ 11200 * (n + A + 1) * ztvg := by
  unfold splB2Cost
  have hsum : ∑ b ∈ Finset.range ztbo, ztfga ≤
      ∑ b ∈ Finset.range ztbo, ztyal :=
    Finset.sum_le_sum fun b _ => bsCost_le (hM b)
  have e : ∑ b ∈ Finset.range ztbo, ztyal =
      11047 * (∑ b ∈ Finset.range ztbo, bcnt bk n b) * ztvg + 11054 * ztbo := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hb : ∑ b ∈ Finset.range ztbo, bcnt bk n b = n := bstart_all hA
  grind
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
open BuildNF (codeLe)
@[expose] public section
def SortedMeets (sB : Stmt) (κB : ℕ) : Prop :=
  Meets sB {bBuild, bSort, bSign}
    (fun P W c => GoodEnv P ∧ hostWords P.n ≤ W ∧
      ModelDescWF P ztm c.nmem ztue ∧
      ∃ M L E, ModelDescAt c.nmem ztue zta M ∧
      GoodModel M ∧ rd c bBuild 2 = L.length ∧ rd c bBuild 1 + 3 * L.length ≤ c.nreg ALLOC ∧
      ChordListAt c.nmem ztbis L ∧ ChordTriplesOK M zta L ∧
      rd c bBuild 4 + 2 * L.length ≤ c.nreg ALLOC ∧
      seg c.nmem ztcdp ztpu = E ∧
      E.Perm ztct ∧ E.Pairwise ztwqj)
    (fun P c c' => ∀ M L, ModelDescAt c.nmem ztue zta M →
      rd c bBuild 2 = L.length → ChordListAt c.nmem ztbis L →
        c.nreg ALLOC ≤ rd c' bBuild 3 ∧
        NFWithin c'.nmem ztdph ztdo
          ztbaku ∧
        IsNF M zta ztbaku ∧
        (BuildNF.buildNF M zta L ztwsq).chords.map
          ztwma = L ∧
        (BuildNF.buildNF M zta L ztwsq).dec = [])
    (fun _ c => κB * ztpdc)
theorem sortedMeets_of (h : BuildNFSortedSpec) : ∃ sB κB, SortedMeets sB κB := h

/-- The bucket of new event code `2K + q`. -/
def bkOf (c : Config) (q : ℕ) : ℕ := c.nmem (rd c bDownDrv 22 + q)

/-- **The precondition of the splice.** -/
def SplPre (P : Polygon) (W : ℕ) (c : Config) : Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧ ModelDescWF P ztm c.nmem ztfud ∧
  ∃ (M : Model) (L L₂ : List zte) (E : List ℕ),
    ModelDescAt c.nmem ztfud zta M ∧ GoodModel M ∧
    rd c bDownDrv 3 = L.length ∧ rd c bDownDrv 2 + 3 * L.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem zthzx L ∧
    rd c bDownDrv 21 = L₂.length ∧ rd c bDownDrv 20 + 3 * L₂.length ≤ c.nreg ALLOC ∧
    ChordListAt c.nmem ztrvf L₂ ∧
    ChordTriplesOK M zta ztfi ∧
    rd c bDownDrv 4 + 2 * L.length ≤ c.nreg ALLOC ∧
    seg c.nmem ztlsi ztpu = E ∧
    E.Perm ztct ∧ E.Pairwise ztwqj ∧
    rd c bDownDrv 22 + 2 * L₂.length ≤ c.nreg ALLOC ∧
    (∀ q, q < 2 * L₂.length → bkOf c q ≤ rd c bDownDrv 23) ∧
    (∀ q q', q < 2 * L₂.length → q' < 2 * L₂.length → bkOf c q < bkOf c q' →
      codeLe M zta ztfi ztbhj ztekx) ∧
    (∀ b, bcnt (bkOf c) ztssh b ≤ rd c bDownDrv 24)

/-- **The postcondition of the splice.** -/
def SplPost (P : Polygon) (c c' : Config) : Prop :=
  (∀ r, (210000 ≤ r ∧ r < 210002 ∨ 210006 ≤ r ∧ r < 210025 ∨ 210074 ≤ r ∧ r < 220000) →
    c'.nreg r = c.nreg r) ∧
  ∀ (M : Model) (L L₂ : List zte), ModelDescAt c.nmem ztfud zta M →
    rd c bDownDrv 3 = L.length → ChordListAt c.nmem zthzx L →
    rd c bDownDrv 21 = L₂.length → ChordListAt c.nmem ztrvf L₂ →
    rd c' bDownDrv 3 = L.length + L₂.length ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 2 ∧
    rd c' bDownDrv 2 + 3 * ztbtn ≤ c'.nreg ALLOC ∧
    ChordListAt c'.nmem (rd c' bDownDrv 2) ztfi ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 4 ∧
    rd c' bDownDrv 4 + 2 * ztbtn ≤ c'.nreg ALLOC ∧
    (seg c'.nmem ztlso ztxdl).Perm
      (List.range ztxdl) ∧
    (seg c'.nmem ztlso ztxdl).Pairwise
      ztzlg ∧
    c.nreg ALLOC ≤ rd c' bDownDrv 5 ∧
    NFWithin c'.nmem (rd c' bDownDrv 5) ztdo
      (BuildNF.buildNF M zta ztfi
        (seg c'.nmem ztlso ztxdl))

/-- The cost constant of the splice. -/
def κSpl (κB : ℕ) : ℕ := 120000 + κB

/-- **The cost of the splice.** -/
def splCost (κB : ℕ) (c : Config) : ℕ :=
  κSpl κB * (rd c bDownDrv 3 + rd c bDownDrv 21 + rd c bDownDrv 23 + 1) *
    (Nat.clog 2 (rd c bDownDrv 24) + 1)
def splT (sB : Stmt) : Stmt := .seq splC (.seq (padS 210026) (.seq spl7 (.seq sB spl8)))

/-- **The splice** with the sorted build `sB`. -/
def splS (sB : Stmt) : Stmt :=
  .seq (.seq spl0 (.seq cpS (.seq spl1 cpS)))
    (.seq ztncw
      (.seq zthqh ztweo))
theorem wrM_spl7 : wrM ztchz spl7 = true := by_decide
theorem wrM2_spl7 : wrM2 ztchz ztczi spl7 = true := by
  decide
theorem wrM_spl8 : wrM ztijw spl8 = true := by_decide
theorem wrM2_spl8 :
    wrM2 ztijw ztczi spl8 = true := by_decide

/-- Registers of `bDownDrv` are outside the bands of the sorted build. -/
theorem band21_notin {r : ℕ} (h1 : 210000 ≤ r) (h2 : r < 220000) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) := by
  zudlf

/-- The cost of the tail (`A₀` the start of `L'`, `A` the allocation pointer on entry). -/
def splTCost (κB K K₂ A₀ A : ℕ) : ℕ :=
  splCCost K K₂ + 3 * (A - A₀ + 4 * ztlc) + 12 + κB * ztcte
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The tail of the splice.** -/
theorem splT_exec {sB : Stmt} {κB : ℕ} (hB : SortedMeets sB κB) (hG : GoodEnv P)
    (hWn : hostWords P.n ≤ W) (c : Config) (hw : WordsBounded W c)
    {D T SE Rb A₀ : ℕ} {M : Model} {L L₂ : List zte} {E E₂ : List ℕ}
    (h01 : c.nreg 210001 = D) (h25 : c.nreg 210025 = L.length + L₂.length)
    (h26 : c.nreg 210026 = A₀) (h27 : c.nreg 210027 = 2 * L.length)
    (h28 : c.nreg 210028 = 2 * L₂.length) (h29 : c.nreg 210029 = 2 * ztbtn)
    (h04 : c.nreg 210004 = SE) (h48 : c.nreg 210048 = Rb) (h34 : c.nreg 210034 = 1)
    (h40 : c.nreg 40000 = D) (h42 : c.nreg 42000 = T)
    (h42' : c.nreg 42001 = 2 * ztbtn)
    (hA₀ : A₀ + 3 * ztbtn ≤ c.nreg ALLOC)
    (hwf : ModelDescWF P ztm c.nmem D) (hM : ModelDescAt c.nmem D zta M)
    (hgood : GoodModel M) (hok : ChordTriplesOK M zta ztfi)
    (hCL : ChordListAt c.nmem A₀ ztfi) (hrec : RecsAt c.nmem T ztfi)
    (hT : T + 8 * ztbtn ≤ c.nreg ALLOC)
    (hE : seg c.nmem SE ztpu = E) (hSE : SE + 2 * L.length ≤ c.nreg ALLOC)
    (hE₂ : seg c.nmem Rb ztssh = E₂) (hRb : Rb + 2 * L₂.length ≤ c.nreg ALLOC)
    (hperm : E.Perm ztct) (hsort : E.Pairwise ztwqj)
    (hperm₂ : E₂.Perm ztgqh)
    (hsort₂ : E₂.Pairwise ztzlg)
    (hroom : c.nreg ALLOC + 8 * ztbtn + splCCost L.length L₂.length +
      κB * ztpzj + 1 ≤ W) :
    ∃ c' k, Exec P W ztweo c c' k ∧
      k ≤ splTCost κB L.length L₂.length A₀ ztm ∧
      c.nreg ALLOC ≤ c'.nreg ALLOC ∧ c'.nreg ALLOC ≤ A₀ + k ∧
      c'.nreg 210002 = A₀ ∧ c'.nreg 210003 = L.length + L₂.length ∧
      c.nreg ALLOC ≤ c'.nreg 210004 ∧
      c'.nreg 210004 + 2 * ztbtn ≤ c'.nreg ALLOC ∧
      seg c'.nmem (c'.nreg 210004) ztxdl =
        DownDrv.splice M zta ztfi E E₂ ∧
      c.nreg ALLOC ≤ c'.nreg 210005 ∧
      NFWithin c'.nmem (c'.nreg 210005) ztdo
        (BuildNF.buildNF M zta ztfi (DownDrv.splice M zta ztfi E E₂)) ∧
      zth ∧
      (∀ r, bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) → Bs56 r = false → Bcp r = false →
        zthju → r ≠ 210068 → r ≠ 210069 → r ≠ ALLOC →
          c'.nreg r = c.nreg r) ∧
      ztego ∧
      ztgo ∧ c'.output = c.output := by
  zufoz

  set A₃ := c.nreg ALLOC with hA₃
  have hlen : (L ++ L₂).length = K + K₂ := List.length_append
  obtain ⟨hP, hS⟩ := DownDrv.splice_ok hperm hsort hperm₂ hsort₂
  set E' := DownDrv.splice M zta ztfi E E₂ with hE'd
  have hcodes : ∀ x ∈ E ++ E₂, x < 2 * (L ++ L₂).length := by
    zuh
    zujjh
    zucyj
    · grind
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 (hperm₂.mem_iff.1 h)
      grind
  -- the merge
  obtain ⟨c₄, k₄, e₄, hk₄, w₄, m71, mA, mseg, mlow, mfr, mrr, mrm, mout⟩ :=
    splC_exec (P := P) (W := W) hG hWn c hw (D := D) (T := T) (SE := SE) (Rb := Rb) (K := K)
      (K₂ := K₂) (M := M) (L' := L ++ L₂) (E := E) (E₂ := E₂) h27 h28 h29 h04 h48 h34 h40 h42
      by_omega hlen hwf hM hok hrec by_omega hE hSE hE₂ hRb hcodes
      by_omega
  rw [← hA₃] at m71 mA mlow
  have hmseg : seg c₄.nmem (c₄.nreg 210071) ztxka = E' := mseg
  have k4 : ∀ r, 210000 ≤ r → r < 220000 → Bs56 r = false → Bcp r = false →
      c₄.nreg r = c.nreg r := fun r h1 h2 h3 h4 =>
    mfr r (band21_notin h1 h2) h3 h4 ztu
  have b26 : c₄.nreg 210026 = A₀ := by rw [k4 _ by_norm_num by_norm_num by_decide by_decide, h26]
  -- the padding
  obtain ⟨c₅, e₅, pfr, prr, pnm, prm, pout, w₅⟩ :=
    padS_exec (P := P) (src := 210026) w₄ (by rw [b26]; have := mA; unfold ALLOC at this; omega)
      by_omega
  have hp9 : c₄.nreg 9999 = A₃ + 4 * ztlc := by have := mA; unfold ALLOC at this; omega
  have q01 : c₅.nreg 210001 = D := by
    rw [pfr _ by_decide by_decide, k4 _ by_norm_num by_norm_num by_decide by_decide, h01]
  have q25 : c₅.nreg 210025 = K + K₂ := by
    rw [pfr _ by_decide by_decide, k4 _ by_norm_num by_norm_num by_decide by_decide, h25]
  have q26 : c₅.nreg 210026 = A₀ := by_grind
  have q71 : c₅.nreg 210071 = A₃ + 2 * ztlc := by_grind
  have q9 : c₅.nreg 9999 = A₃ + 4 * ztlc := by_grind
  -- the arguments of the sorted build
  obtain ⟨c₆, k₆, e₆, hk₆, v0, v1, v2, v4, hm₆⟩ : ∃ c₆ k₆, Exec P W spl7 c₅ c₆ k₆ ∧ k₆ = 4 ∧
      c₆.nreg 40000 = D ∧ c₆.nreg 40001 = A₀ ∧ c₆.nreg 40002 = K + K₂ ∧
      c₆.nreg 40004 = A₃ + 2 * ztlc ∧ c₆.nmem = c₅.nmem := by
    unfold spl7
    exec_block
    refine ztcby <;> config_simp <;> (try simp only [q01, q25, q26, q71])
  have f₆ := exec_frameM e₆ wrM_spl7
  zujb
  have a6 : c₆.nreg ALLOC = A₃ + 4 * ztlc := by
    rw [f₆.1 _ by_decide]; exact q9
  have hm6 : ∀ a, a < A₃ → c₆.nmem a = c.nmem a := fun a ha => by_grind
  obtain ⟨hM₆, hwf₆⟩ := desc_agree hwf hM (m' := c₆.nmem) hm6
  have hwf₆' : ModelDescWF P zthwe c₆.nmem D := hwf₆.mono by_grind
  have hCL₆ : ChordListAt c₆.nmem A₀ ztfi := fun i hi => by
    obtain ⟨x1, x2, x3⟩ := hCL i hi
    zucpx
    exact ⟨by_grind, by_grind,
      by grind⟩
  have hseg₆ : seg c₆.nmem (A₃ + 2 * ztlc) ztxka = E' := by
    grind
  -- the sorted build
  have H7 := hB P W c₆ w₆
    (by
      zufby
      refine ⟨hG, hWn, by_grind, M, L ++ L₂, E', by_grind, hgood,
        by omega, by_grind, by_grind, hok,
        by grind, by rw [v4, hlen]; omega, hP, hS⟩)
    (by
      zufby
      grind)
  obtain ⟨c₇, k₇, e₇, hk₇, post₇, fr₇⟩ := H7
  simp only [rd, bandReg, bBuild, Nat.reduceMul, Nat.reduceAdd] at hk₇ post₇
  rw [v2] at hk₇
  obtain ⟨o1, o2, -, -, -⟩ := post₇ M ztfi by_grind by_omega
    by_grind
  rw [v4, hlen, hseg₆] at o2
  rw [a6] at o1
  obtain ⟨fr7, rr7, nm7, rm7, out7, al7, au7⟩ := fr₇
  rw [a6] at al7 au7 nm7 rm7
  have k7 : ∀ r, 210000 ≤ r → r < 220000 → c₇.nreg r = c₆.nreg r := fun r h1 h2 =>
    fr7 r (by zvncv; omega)
      ztu
  have r26 : c₇.nreg 210026 = A₀ := by
    rw [k7 _ by_norm_num by_norm_num, f₆.1 _ by_decide, q26]
  have r25 : c₇.nreg 210025 = K + K₂ := by
    rw [k7 _ by_norm_num by_norm_num, f₆.1 _ by_decide, q25]
  have r71 : c₇.nreg 210071 = A₃ + 2 * ztlc := by
    rw [k7 _ by_norm_num by_norm_num, f₆.1 _ by_decide, q71]
  -- the outputs
  zubgp
  obtain ⟨c₈, k₈, e₈, hk₈, u2, u3, u4, u5, hm₈⟩ : ∃ c₈ k₈, Exec P W spl8 c₇ c₈ k₈ ∧ k₈ = 4 ∧
      c₈.nreg 210002 = A₀ ∧ c₈.nreg 210003 = K + K₂ ∧ c₈.nreg 210004 = A₃ + 2 * ztlc ∧
      c₈.nreg 210005 = c₇.nreg 40003 ∧ c₈.nmem = c₇.nmem := by
    unfold spl8
    exec_block
    refine ztcby <;> config_simp <;> (try simp only [r26, r25, r71])
  have f₈ := exec_frameM e₈ wrM_spl8
  have a8 : ztshs := f₈.1 _ by_decide
  have hm8 : ∀ a, a < A₃ + 4 * ztlc → c₈.nmem a = c₆.nmem a := fun a ha => by
    rw [hm₈, nm7 a ha]
  refine ⟨c₈, k₄ + (3 * (c₄.nreg 9999 - c₄.nreg 210026) + 4 + (k₆ + zttrl)),
    .seq e₄ zteka, ?_, ?_, ?_, u2, u3, ?_, ?_, ?_, ?_, ?_,
    fun a ha => ?_, fun r hr h56 hcp hro h68 h69 hra => ?_, fun r hr => ?_, fun a ha => ?_, ?_⟩
  · unfold splTCost
    rw [hp9, b26, hk₆, hk₈]
    omega
  · rw [a8]; omega
  · rw [a8, hp9, b26]; omega
  · rw [u4]; omega
  · rw [u4, a8]; omega
  · rw [u4, seg_congr (m' := c₆.nmem) fun i hi => hm8 _ by_omega, hseg₆]
  · rw [u5]; omega
  · rw [u5, hm₈, a8]; exact o2
  · rw [hm8 a by_omega, hm6 a ha]
  · rw [f₈.1 r ztmz]
    rw [fr7 r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto) hra]
    rw [f₆.1 r (by
      zvncv at hr
      zvnan; omega)]
    rw [pfr r h68 h69, mfr r hr h56 hcp hra]
  · rw [exec_frameM2 e₈ wrM2_spl8 r rfl, rr7 r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto),
      exec_frameM2 e₆ wrM2_spl7 r rfl, prr, mrr r (by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr ⊢; tauto)]
  · rw [f₈.2.2.1, rm7 a by_omega, f₆.2.2.1, prm, mrm]
  · rw [f₈.2.2.2, out7, f₆.2.2.2, pout, mout]
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvR
open Machine Machine.Stmt Programs SortL BuildRam SignK
open BuildNF (codeLe)
@[expose] public section
variable {r : ℕ}
/-- The registers of `bDownDrv` the splice keeps. -/
theorem spl_keep
    (hr : 210000 ≤ r ∧ r < 210002 ∨ 210006 ≤ r ∧ r < 210025 ∨ 210074 ≤ r ∧ r < 220000) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) ∧ Bs56 r = false ∧ Bcp r = false ∧
      zthju ∧ r ≠ 210068 ∧ r ≠ 210069 ∧ r ≠ ALLOC ∧
      ztdib ∧ ztdia ∧ BsA r = false ∧
      210000 ≤ r ∧ r < 220000 := by
  refine ⟨band21_notin by_omega by_omega, ?_, ?_, by_omega, by_omega, by_omega,
    by unfold ALLOC; omega, by_omega, by_omega, ?_, by_omega, by_omega⟩
  · zuggu
  · zuggp
  · zuggv

/-- The registers outside the bands of the splice. -/
theorem spl_out (hr : bandOf r ∉ ({bDownDrv, bBuild, bSort, bSign} : Finset ℕ)) :
    bandOf r ∉ ({bSort, bSign, bBuild} : Finset ℕ) ∧ (r ≠ ALLOC → Bs56 r = false) ∧
      Bcp r = false ∧ zthju ∧ r ≠ 210068 ∧ r ≠ 210069 ∧
      ztdib ∧ ztdia ∧ (r ≠ ALLOC → BsA r = false) := by
  have hb : ¬ (r / 10000 = 21 ∨ r / 10000 = 4 ∨ r / 10000 = 3 ∨ r / 10000 = 1) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton, bandOf, bDownDrv, bBuild, bSort,
      bSign] using hr
  refine ⟨?_, fun hra => ?_, ?_, by_omega, by_omega, by_omega, by_omega, by_omega, fun hra => ?_⟩
  · simp_all
  · zujyu
    zuggu
  · zuggp
  · zujyu
    zuggv
section exec
variable {P : Polygon} {W : ℕ}
set_option maxHeartbeats 4000000 in
/-- **The splice.** -/
theorem splice_meets {sB : Stmt} {κB : ℕ} (hB : SortedMeets sB κB) :
    Meets (splS sB) {bDownDrv, bBuild, bSort, bSign} SplPre SplPost (fun _ c => splCost κB c) := by
  zubgq
  obtain ⟨hG, hWn, hwf, M, L, L₂, E, hM, hgood, hK, hB0, hCL, hK₂, hB₂, hCL₂, hok, hSEb, hSE,
    hperm, hsort, hBBb, hbk, hmono, hMb⟩ := hpre
  zvmyi at hK hB0 hCL hK₂ hB₂ hCL₂ hSEb hSE hBBb hbk hmono hMb hM hwf
  zufoz

  set A := c.nreg 210023 with hAd
  set Mb := c.nreg 210024 with hMbd
  zuce
  set BB := c.nreg 210022 with hBBd
  set bk : ℕ → ℕ := fun q => c.nmem ztgzy with hbkd
  have hcost : splCost κB c = κSpl κB * ztbdy * ztvg := by
    unfold splCost; zvmyi; simp_all
  have hroom' : A₀ + κSpl κB * ztbdy * ztvg ≤ W := by
    simp_all
  have hcl : 1 ≤ Nat.clog 2 Mb + 1 := by_omega
  have hbase : K + K₂ + A + 1 ≤ ztbdy * ztvg :=
    Nat.le_mul_of_pos_right _ by_omega
  have hB2c := splB2Cost_le (bk := bk) (n := 2 * K₂) (A := A) (Mb := Mb) ztnzj
    (fun b => hMb b)
  have hκ : κSpl κB * ztbdy * ztvg =
      120000 * ztxyl +
        κB * ztxyl := by unfold κSpl; ring
  have hB2c' : 11200 * (2 * K₂ + A + 1) * ztvg ≤
      22400 * ztxyl := by
    grind
  have hκB : κB * ztcte ≤ κB * ztxyl :=
    Nat.mul_le_mul_left _ by_omega
  rw [hκ] at hroom'
  -- stage A: the new chord list
  obtain ⟨c₁, k₁, e₁, hk₁, w₁, a25, a26, a27, a28, a29, a34, aA, aCL, alow, af, arr⟩ :=
    splA_exec (P := P) (W := W) c hw (B := c.nreg 210002) (K := K) (B₂ := c.nreg 210020)
      (K₂ := K₂) (L := L) (L₂ := L₂) rfl hK rfl hK₂ rfl rfl hCL hCL₂ hB0 hB₂ by_omega
  have g₁ : ∀ r, BsA r = false → c₁.nreg r = c.nreg r := af.1
  have b21 : ztbvh := by
    zucxf
    zudlf
  set L' := L ++ L₂ with hL'
  have hlen : L'.length = K + K₂ := by rw [hL', List.length_append]
  -- stage B1: the records
  obtain ⟨c₂, k₂, e₂, hk₂, w₂, d40, d42, d421, d31, d32, d33, dA, drec, dlow, -, dfr, drr, drm, dout⟩ :=
    splB1_exec (P := P) (W := W) hWn c₁ w₁ (D := c.nreg 210001) (B' := A₀) (K := K) (K₂ := K₂)
      (A := A) (M := M) (L' := L') ztntj a26 a25 a27 a28
      ztntj hlen hok aCL aA by_omega
  rw [aA] at d42 dA drec dlow drm
  -- registers of band `bDownDrv` kept by stage B1
  have dk : ∀ r, 210000 ≤ r → r < 220000 → ztdia → c₂.nreg r = c₁.nreg r :=
    fun r h1 h2 h3 => dfr r ztlge h3 ztu
  -- memory below `A₀`
  have hlow2 : ztfak := fun a ha => by rw [dlow a by_omega, alow a ha]
  obtain ⟨hM₂, hwf₂⟩ := desc_agree hwf hM (m' := c₂.nmem) fun a ha => hlow2 a ha
  -- stage B2: the sorted new codes
  have hroomB2 : c₂.nreg ALLOC + splB2Cost bk ztjfa A + 1 ≤ W := by_omega
  obtain ⟨c₃, k₃, e₃, hk₃, w₃, f48, fperm, fsort, fRb, fA, flow, f40, f42, f421, f34, ffr, frr, frm,
    fout⟩ := splB2_exec (P := P) (W := W) hG hWn c₂ w₂ (D := c.nreg 210001) (T := A₀ + 3 * (K + K₂))
      (BB := BB) (n := 2 * K₂) (A := A) (base := 2 * K) (M := M) (L' := L') (bk := bk)
      (by rw [dk _ by_norm_num by_norm_num by_norm_num, g₁ _ by_decide]) d31 d32 d33 d40
      d42 by_omega (hwf₂.mono by_omega) hM₂ hok drec
      by_omega by_omega by_omega
      (fun q hq => by rw [hlow2 _ by_omega]) ztnzj
      (fun q q' hq hq' h => hmono q q' hq hq' h) hroomB2
  rw [dA] at f48 fA flow frm
  -- registers of band `bDownDrv` kept by stage B2
  have fk : ∀ r, 210000 ≤ r → r < 220000 → ztdib → c₃.nreg r = c₂.nreg r :=
    fun r h1 h2 h3 => ffr r ztlge h3 ztu
  have hlow3 : ∀ a, a < A₀ + 3 * ztlc + 10 * ztlc → c₃.nmem a = c₂.nmem a := flow
  have hA₃lo : A₀ + 13 * ztlc ≤ c₃.nreg ALLOC := by have := fRb; rw [f48] at this; omega
  have hCC : splCCost K K₂ ≤ 22066 * ztlc + 40 := by unfold splCCost; omega
  -- the registers at `c₃`
  have t01 : c₃.nreg 210001 = c.nreg 210001 := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      g₁ _ by_decide]
  have t04 : c₃.nreg 210004 = c.nreg 210004 := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      g₁ _ by_decide]
  have t25 : c₃.nreg 210025 = K + K₂ := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      a25]
  have t26 : c₃.nreg 210026 = A₀ := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      a26]
  have t27 : c₃.nreg 210027 = 2 * K := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      a27]
  have t28 : c₃.nreg 210028 = 2 * K₂ := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      a28]
  have t29 : c₃.nreg 210029 = 2 * ztlc := by
    rw [fk _ by_norm_num by_norm_num by_norm_num, dk _ by_norm_num by_norm_num by_norm_num,
      a29]
  -- the memory at `c₃`
  have hm3 : ztfal := fun a ha => by
    rw [hlow3 a by_omega, hlow2 a ha]
  obtain ⟨hM₃, hwf₃⟩ := desc_agree hwf hM (m' := c₃.nmem) hm3
  have hCL₃ : ChordListAt c₃.nmem A₀ ztfi := fun i hi => by
    obtain ⟨x1, x2, x3⟩ := aCL i hi
    zucpx
    exact ⟨by zundr; exact x1,
      by zundr; exact x2,
      by zundr; exact x3⟩
  have hrec₃ : RecsAt c₃.nmem (A₀ + 3 * ztlc) L' := fun q hq => by
    obtain ⟨r1, r2, r3, r4⟩ := drec q hq
    rw [hlen] at hq
    exact ⟨by zunga; exact r1, by zunga; exact r2,
      by zunga; exact r3, by zunga; exact r4⟩
  have hE₃ : seg c₃.nmem (c.nreg 210004) ztbds = E := by
    rw [seg_congr (m' := c.nmem) fun i hi => hm3 _ by_omega]; omega
  -- the tail
  obtain ⟨c₄, k₄, e₄, hk₄, tAlo, tAhi, t2, t3, t4lo, t4hi, tseg, t5lo, tnf, tlow, tfr, trr, trm,
    tout⟩ := splT_exec (P := P) (W := W) hB hG hWn c₃ w₃ (D := c.nreg 210001)
      (T := A₀ + 3 * ztlc) (SE := c.nreg 210004) (Rb := c₃.nreg 210048) (A₀ := A₀) (M := M)
      (L := L) (L₂ := L₂) (E := E) (E₂ := seg c₃.nmem (c₃.nreg 210048) ztjfa)
      t01 t25 t26 t27 t28 t29 t04 rfl f34 f40 f42 by_omega by_omega
      (hwf₃.mono by_omega) hM₃ hgood hok hCL₃ hrec₃ by_omega hE₃ by_omega rfl by_omega
      hperm hsort fperm fsort (by rw [← hKd, ← hK₂d]; omega)
  obtain ⟨sP, sS⟩ := DownDrv.splice_ok hperm hsort fperm fsort
  rw [List.length_append] at sP
  refine ⟨c₄, k₁ + zttk, .seq e₁ ztcb, ?_, zthna,
    fun r hr hra => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_, by_omega, by_omega⟩
  · -- the cost
    show k₁ + zttk ≤ splCost κB c
    rw [hcost]
    unfold splTCost at hk₄
    rw [← hKd, ← hK₂d] at hk₄
    omega
  · -- the registers kept
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12⟩ := spl_keep hr
    rw [tfr r x1 x2 x3 x4 x5 x6 x7, fk r x11 x12 x8, dk r x11 x12 x9, g₁ r x10]
  · -- the outputs
    intro M₀ L₀ L₂₀ hM₀ hK₀ hCL₀ hK₂₀ hCL₂₀
    zvmyi at hM₀ hK₀ hCL₀ hK₂₀ hCL₂₀ ⊢
    have e1 : M₀ = M := NFLoc.modelDesc_unique hM₀ hM
    have e2 : L₀ = L := BuildNF.chordListAt_unique hCL₀ hCL by_omega
    have e3 : L₂₀ = L₂ := BuildNF.chordListAt_unique hCL₂₀ hCL₂ by_omega
    rw [e1, e2, e3, t2, t3, tseg]
    refine ⟨rfl, le_refl _, by_omega, fun i hi => ?_, by_omega, t4hi, sP, sS, by_omega, tnf⟩
    obtain ⟨x1, x2, x3⟩ := hCL₃ i hi
    rw [List.length_append] at hi
    exact ⟨by zunon; exact x1, by zunon; exact x2,
      by zunon; exact x3⟩
  · -- the frame: registers
    obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, x9⟩ := spl_out hr
    rw [tfr r x1 (x2 hra) x3 x4 x5 x6 hra, ffr r x1 x7 hra, dfr r x1 x8 hra, g₁ r (x9 hra)]
  · -- real registers
    obtain ⟨x1, -, -, -, -, -, x7, -, -⟩ := spl_out hr
    rw [trr r x1, frr r x1 x7, drr r x1, arr]
  · rw [tlow a by_omega, hm3 a ha]
  · rw [trm a by_omega, frm a by_omega, drm a by_omega, af.2.2.1]
  · rw [tout, fout, dout, af.2.2.2]
end exec
end
end DrvR
end Chazelle.Core
namespace Chazelle.Core
namespace DrvD
open Machine Machine.Stmt Programs SignK
@[expose] public section
def initS : Stmt := block [.constN 216002 1, .constN 216003 0, .constN 216004 4,
  .constN 216005 2, .constN 216006 5, .constN 216010 0]

/-- The header of the current normal form; the bases of `L₂`. -/
def hdS : Stmt := block [.copyN 216012 210005, .addN 216033 216012 216002, .loadN 216017 216033,
  .addN 216033 216033 216002, .loadN 216013 216033, .addN 216033 216033 216005,
  .loadN 216014 216033, .addN 216033 216033 216002, .loadN 216015 216033,
  .addN 216033 216033 216005, .loadN 216016 216033, .copyN 216018 9999, .copyN 216021 9999,
  .constN 216020 0, .constN 216023 0]

/-- Reserve five words. -/
def resBody : Stmt := block [.addN 9999 9999 216002, .addN 9999 9999 216002,
  .addN 9999 9999 216002, .addN 9999 9999 216002, .addN 9999 9999 216002,
  .addN 216023 216023 216002]

/-- The reservation loop (`5 R` words). -/
def resS : Stmt := .whileLtN 216023 216013 resBody

/-- The bucket base `L₂ base + 3 R`; the region loop set-up. -/
def midS : Stmt := block [.addN 216033 216013 216013, .addN 216033 216033 216013,
  .addN 216019 216018 216033, .copyN 216022 216019, .constN 216030 0, .addN 216031 216015 216005]

/-! ## The arc scan -/

/-- Load arc `j` (the `t`-th arc of the region) and the end `x` into the key-decision registers. -/
def ldArc : Stmt := block [.addN 216055 216043 216044, .loadN 216045 216055,
  .addN 216046 216045 216045, .addN 216046 216046 216046, .addN 216046 216046 216045,
  .addN 216046 216046 216014, .addN 216055 216046 216002, .loadN 42102 216055,
  .addN 216055 216055 216002, .loadN 42103 216055, .addN 216055 216055 216002,
  .loadN 42104 216055, .addN 216055 216055 216002, .loadN 42105 216055, .copyN 42100 216040,
  .copyN 42101 216041, .addN 216054 216045 216002]

/-- The decision on arc `j`: `t₁ = r42107`, `t₂ = r42109` (`DrvD.matchB`, `DrvD.bktB`). -/
def decS : Stmt :=
  .ifLtN 216054 216017
    (.ifLtN 216003 42107 (.ifLtN 216003 42109 (.instr (.copyN 216053 216054)) .skip) .skip)
    (.ifLtN 216003 42109 ztotx
      (.ifLtN 216003 42107 (.instr (.copyN 216053 216017)) .skip))

/-- One arc of the scan. -/
def scanBody : Stmt :=
  .seq ldArc (.seq (BuildRam.halfS 42100 42101 42102 42103 42106 42107)
    (.seq (BuildRam.halfS 42104 42105 42100 42101 42108 42109)
      (.seq decS (block [.addN 216044 216044 216002]))))

/-- **The arc scan** of the end `x = (r216040, r216041)` over the arcs of the region. -/
def scanS : Stmt := .seq (.instr (.constN 216044 0)) (.whileLtN 216044 216042 scanBody)

/-! ## The call of the splitting step -/

/-- The arguments of the splitting step. -/
def argS : Stmt := block [.copyN 81000 210001, .copyN 81001 216012, .copyN 81002 216030,
  .copyN 81003 216001, .copyN 81004 230001, .copyN 81005 216000, .copyN 81006 216004]

/-- Append the triple; the region data of the scans; the left end. -/
def appT : Stmt := block [.storeN 216021 81008, .addN 216021 216021 216002,
  .storeN 216021 81009, .addN 216021 216021 216002, .storeN 216021 81010,
  .addN 216021 216021 216002, .addN 216020 216020 216002, .subN 216033 216031 216005,
  .loadN 216042 216033, .addN 216033 216033 216002, .loadN 216034 216033,
  .addN 216043 216016 216034, .addN 216041 81008 216002, .copyN 40000 210001,
  .copyN 216040 81009]

/-- Store a bucket. -/
def stB : Stmt := block [.storeN 216022 216053, .addN 216022 216022 216002]

/-- Append the chord and the buckets of its two ends. -/
def appS : Stmt :=
  .seq appT (.seq scanS (.seq stB (.seq ztovg (.seq scanS stB))))

/-- Call the splitting step on region `r` and append its chord, if any. -/
def callS (sF : Stmt) : Stmt := .seq argS (.seq sF (.ifLtN 216003 81007 appS .skip))

/-- The step of the region loop. -/
def regBody (sF : Stmt) : Stmt :=
  .seq (.instr (.loadN 216032 216031)) (.seq (.ifLtN 216004 216032 ztvkx .skip)
    ztiqn)

/-- The region loop. -/
def regS (sF : Stmt) : Stmt := .whileLtN 216030 216013 ztwcn

/-! ## A round, and the rounds -/

/-- The arguments of the splice. -/
def splArgs : Stmt := block [.copyN 210020 216018, .copyN 210021 216020, .copyN 210022 216019,
  .copyN 210023 216017, .copyN 210024 216005]

/-- One round. -/
def roundBody (sF sB : Stmt) : Stmt :=
  .seq hdS (.seq resS (.seq midS (.seq ztwcq (.seq splArgs (.seq ztpxg
    ztnsb)))))

/-- **The restoration rounds.** -/
def roundsS (sF sB : Stmt) : Stmt := .seq initS (.whileLtN 216010 216000 zttyy)

/-! ## Write sets -/

/-- The registers the arc scan writes. -/
def Bscan (r : ℕ) : Bool :=
  decide (216044 ≤ r ∧ r < 216060) || decide (42100 ≤ r ∧ r < 42110) || BuildRam.Bhalf r

/-- A register frame for fewer registers is one for more. -/
theorem fbMono {B B' : ℕ → Bool} {c c' : Config} (h : FrameB B c c')
    (hB : ∀ r, B r = true → B' r = true) : FrameB B' c c' :=
  ⟨fun r hr => h.1 r by_grind,
    fun r hr => h.2.1 r by_grind,
    h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- The registers `ldArc` writes. -/
def BldArc (r : ℕ) : Bool :=
  decide (r = 216045) || decide (r = 216046) || decide (r = 216054) || decide (r = 216055) ||
    decide (42100 ≤ r ∧ r ≤ 42105)
theorem wr_ldArc : wr BldArc ldArc = true := by_decide
theorem wr_decS : wr ztlos decS = true := by_decide
variable (r : ℕ)
theorem bldArc_scan (h : BldArc r = true) : Bscan r = true := by
  simp only [BldArc, Bscan, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem b53_scan (h : decide (r = 216053) = true) : Bscan r = true := by
  simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq] at h ⊢; omega
theorem bhalf_scan {dd dst : ℕ} (hdd : 42100 ≤ dd ∧ dd < 42110) (hdst : 42100 ≤ dst ∧ dst < 42110)
    (r : ℕ) (h : BuildRam.BhalfS dd dst r = true) : Bscan r = true := by
  simp only [BuildRam.BhalfS, Bool.or_eq_true, decide_eq_true_eq] at h
  simp only [Bscan, Bool.or_eq_true, decide_eq_true_eq]
  grind
end
end DrvD
end Chazelle.Core
namespace Chazelle.Core
namespace DrvLT
open Machine Machine.Stmt Programs
@[expose] public section
def ltInit : Stmt := block [.constN 211100 1, .constN 211101 3, .constN 210034 1,
  .copyN 211110 9999, .constN 211111 0]

/-- Reserve five words. -/
def ltResBody : Stmt := block [.addN 9999 9999 211100, .addN 9999 9999 211100,
  .addN 9999 9999 211100, .addN 9999 9999 211100, .addN 9999 9999 211100,
  .addN 211111 211111 211100]

/-- The reservation loop (`5 K₂` words). -/
def ltRes : Stmt := .whileLtN 211111 211012 ltResBody

/-- The bucket base, the write pointers, the region loop set-up. -/
def ltMid : Stmt := block [.addN 211147 211012 211012, .addN 211147 211147 211012,
  .addN 211112 211110 211147, .copyN 211113 211110, .copyN 211114 211112, .constN 211130 0,
  .copyN 211131 211009]

/-- Read the table entry; the arguments of the triple copy. -/
def ltB1 : Stmt := block [.loadN 211140 211131, .addN 211141 211131 211100,
  .loadN 211142 211141, .addN 211141 211141 211100, .loadN 211143 211141,
  .addN 211144 211142 211142, .addN 211144 211144 211142, .addN 211145 211142 211142,
  .copyN 210061 211144, .copyN 210062 211140, .copyN 210063 211113]

/-- Advance the triple pointer; the arguments of the bucket copy. -/
def ltB2 : Stmt := block [.addN 211113 211113 211144, .copyN 210061 211145,
  .copyN 210062 211143, .copyN 210063 211114]

/-- Advance the bucket pointer, the table pointer and the region. -/
def ltB3 : Stmt := block [.addN 211114 211114 211145, .addN 211131 211131 211101,
  .addN 211130 211130 211100]

/-- One region of the gather. -/
def ltBody : Stmt := .seq ltB1 (.seq DrvR.cpS (.seq ltB2 (.seq DrvR.cpS ltB3)))

/-- The gather loop over the regions. -/
def ltLoop : Stmt := .whileLtN 211130 211011 ltBody

/-- The arguments of the splice. -/
def ltArgs : Stmt := block [.copyN 210020 211110, .copyN 210021 211012, .copyN 210022 211112,
  .addN 211150 210003 210003, .addN 211150 211150 211150, .addN 211150 211150 211101,
  .copyN 210023 211150, .addN 211151 211013 211013, .addN 211151 211151 211151,
  .copyN 210024 211151]

/-- The arguments of the rounds. -/
def ltRd : Stmt := block [.constN 216000 134, .copyN 216001 211007]

/-- **The gather.** -/
def gatherS : Stmt := .seq ltInit (.seq ltRes (.seq ltMid (.seq ltLoop ltArgs)))

/-- **The tail of a level** with the sorted build `sB` and the rounds `sRd`. -/
def tailS (sB sRd : Stmt) : Stmt := .seq gatherS (.seq ztpxg (.seq ltRd sRd))

/-- The registers the gather writes (besides the allocator). -/
def BL (r : ℕ) : Bool :=
  decide (211100 ≤ r ∧ r < 211200) || decide ztcku || decide zttxp ||
    decide (210060 ≤ r ∧ r ≤ 210065)
end
end DrvLT
end Chazelle.Core
namespace Chazelle.Core.L41
open Chazelle Chazelle.Merge
@[expose] public section
variable (J : Junction)
variable (k : ℕ)
theorem left_vertex : J.left.vertex k = J.whole.vertex k := rfl
theorem right_vertex : J.right.vertex k = J.whole.vertex (J.m₁ + k) := by
  simp only [Chain.vertex, Chain.edgeIdx, Junction.right, Junction.whole,
    Nat.add_assoc]

/-- **The top index of the union.** -/
theorem whole_topIdx : J.whole.topIdx =
    if (J.right.top).2 ≤ (J.left.top).2 then J.left.topIdx else J.m₁ + J.right.topIdx := by
  zufd
  zunc
  zucz
  have hLt := J.left.topIdx_le; have hRt := J.right.topIdx_le
  have hWt := J.whole.topIdx_le
  -- every vertex of the union is a vertex of a part
  have hsplit : ∀ i, i ≤ J.whole.m → (i ≤ J.m₁ ∧ J.whole.vertex i = J.left.vertex i) ∨
      (∃ t, t ≤ J.m₂ ∧ i = J.m₁ + t ∧ J.whole.vertex i = J.right.vertex t) := by
    zug
    rcases le_or_gt i J.m₁ with h | h
    · tauto
    · refine Or.inr ⟨i - J.m₁, by_omega, by_omega, ?_⟩
      zuoyn; grind
  zugif
  · zudmc
    · apply J.whole.topIdx_min by_omega
      zug
      show (J.whole.vertex i).2 ≤ (J.left.vertex J.left.topIdx).2
      zuctj
      · zvmwe; exact J.left.vertex_snd_le_top by_omega
      · zvmwe; exact (J.right.vertex_snd_le_top by_omega).trans hc
    · zube

      have := J.left.topIdx_min (j := J.whole.topIdx) by_omega (fun i hi => by
        rw [left_vertex, left_vertex]; exact J.whole.vertex_snd_le_top by_omega)
      omega
  · zumik
    zudmc
    · apply J.whole.topIdx_min by_omega
      zug
      rw [← right_vertex]
      show (J.whole.vertex i).2 ≤ (J.right.vertex J.right.topIdx).2
      zuctj
      · zvmwe; exact (J.left.vertex_snd_le_top by_omega).trans hc.le
      · zvmwe; exact J.right.vertex_snd_le_top by_omega
    · have hT : ztsbt := by_omega
      have hge : (J.right.top).2 ≤ (J.whole.top).2 := by
        show (J.right.vertex J.right.topIdx).2 ≤ _
        zuoyn; exact J.whole.vertex_snd_le_top hT
      rcases hsplit _ hWt with ⟨h1, e⟩ | ⟨t, ht, e1, e⟩
      · exfalso
        have := J.left.vertex_snd_le_top (j := J.whole.topIdx) by_omega
        have e' : (J.whole.top).2 = (J.left.vertex J.whole.topIdx).2 := by
          rfl
        linarith
      · zukd
        have := J.right.topIdx_min (j := t) ht (fun i hi => by
          rw [right_vertex, ← e]
          exact J.whole.vertex_snd_le_top by_omega)
        omega

/-- **The orientation bit of the union** is the bit of the part holding the top. -/
theorem whole_sideBeta : J.whole.sideBeta =
    if (J.right.top).2 ≤ (J.left.top).2 then J.left.sideBeta else J.right.sideBeta := by
  have hT := whole_topIdx J
  split_ifs at hT ⊢ with hc
  · zultp
    zvncs; rfl
  · zumik
    -- the top of `C₂` is not its first vertex (the shared vertex is a vertex of `C₁`)
    have h0 : 0 < J.right.topIdx := by
      zumv
      have e : J.right.topIdx = 0 := by_omega
      have : (J.right.top).2 ≤ (J.left.top).2 := by
        show (J.right.vertex J.right.topIdx).2 ≤ _
        rw [e, right_vertex, Nat.add_zero, ← left_vertex]
        exact J.left.vertex_snd_le_top ztbhw
      linarith
    zultp
    rw [hT, right_vertex, right_vertex, right_vertex]
    have e1 : J.m₁ + J.right.topIdx + 1 = J.m₁ + (J.right.topIdx + 1) := by_omega
    have e2 : J.m₁ + J.right.topIdx - 1 = J.m₁ + (J.right.topIdx - 1) := by_omega
    zuihn
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
@[expose] public section
theorem whole_pts_getD {n i : ℕ} (hi : i < n) :
    ((Host.whole n).pts n).getD i ztga = .vtx i := by
  simp only [Host.whole, Host.pts, HostItem.pts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, zero_add]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range by_omega]
  simp [Nat.mod_eq_of_lt hi]
variable {n : ℕ}
/-- **The whole host is regular.** -/
theorem hostRegular_whole (hn : 1 ≤ n) : HostRegular n ztjja := by
  zug
  rw [Host.whole_pts_length n hn] at hi ⊢
  rw [whole_pts_getD hi, whole_pts_getD ztcv]
  tauto

/-- The whole host is well formed. -/
theorem hostWF_whole (hn : 1 ≤ n) : HostWF n ztjja := by
  zujbe
  simp only [Host.whole, List.mem_singleton] at hit
  grind

/-- The whole host describes the polygon. -/
theorem poly_whole (Q : Polygon) (hQ : 1 ≤ Q.n) : (Host.whole Q.n).poly Q = Q := by
  cases Q with
  | mk l =>
    zudgn

    zucr
    zuehb

    zubdb
    zuhrr
    · simp_all
    · zusx
      zudgm

      zuey
      zuipd
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Chazelle Chazelle.Merge
@[expose] public section
theorem chain_eq {C C' : Chain} (h1 : C.P = C'.P) (h2 : C.s = C'.s) (h3 : C.m = C'.m) : C = C' := by
  cases C; simp_all

/-- The junction of two chains, `C₂` following `C₁`. -/
def jOf (C₁ C₂ : Chain) (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) : Junction := Junction.ofChains C₁ C₂ h
theorem jOf_left (C₁ C₂ : Chain) (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) : (jOf C₁ C₂ h).left = C₁ :=
  chain_eq rfl rfl rfl
variable {C₁ C₂ : Chain}
theorem jOf_right (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) (hP : C₂.P = C₁.P)
    (hs : C₂.s = C₁.s + C₁.m) : (jOf C₁ C₂ h).right = C₂ :=
  chain_eq hP.symm hs.symm rfl
theorem jOf_whole_s (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.s = C₁.s := rfl
theorem jOf_whole_m (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.m = C₁.m + C₂.m := rfl
theorem jOf_whole_P (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) :
    (jOf C₁ C₂ h).whole.P = C₁.P := rfl

/-- **The descriptor of the union.** -/
theorem descWhole {m : ℕ → ℕ} {Q : Polygon} {H : Host} {C₁ C₂ : Chain} {B₁ B₂ B : ℕ}
    (h : C₁.m + C₂.m + 1 ≤ C₁.P.n) (hP : C₂.P = C₁.P) (hs : C₂.s = C₁.s + C₁.m)
    (h1 : ChainDescAt m B₁ Q H C₁) (h2 : ChainDescAt m B₂ Q H C₂)
    (e0 : m B = m B₁) (e1 : m ztvf = C₁.s) (e2 : m zthb = C₁.m + C₂.m)
    (e3 : m ztkh = if (C₂.top).2 ≤ (C₁.top).2 then C₁.topIdx else C₁.m + C₂.topIdx)
    (e4 : m ztow = if (C₂.top).2 ≤ (C₁.top).2 then m (B₁ + 4) else m (B₂ + 4)) :
    ChainDescAt m B Q H (jOf C₁ C₂ h).whole := by
  set J := jOf C₁ C₂ h with hJ
  have hl : J.left = C₁ := jOf_left C₁ C₂ h
  have hr : J.right = C₂ := jOf_right h hP hs
  obtain ⟨a0, a1, -, -, -, a5⟩ := h1
  obtain ⟨-, -, -, -, -, b5⟩ := h2
  refine ⟨by_simp_all, by_tauto, e1, e2, ?_, ?_⟩
  · rw [e3, whole_topIdx J, hl, hr]; rfl
  · rw [e4, whole_sideBeta J, hl, hr]
    grind
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine Machine.Stmt Programs SweepPrim SignK WalkKey
@[expose] public section
def descLoadB : Stmt := block [
  .addN 160038 160035 160024, .loadN 160050 160038,
  .addN 160038 160038 160024, .loadN 160051 160038,
  .addN 160038 160038 160024, .loadN 160052 160038,
  .addN 160038 160038 160024, .loadN 160053 160038,
  .addN 160038 160036 160024, .addN 160038 160038 160024, .loadN 160054 160038,
  .addN 160038 160038 160024, .loadN 160055 160038,
  .addN 160038 160038 160024, .loadN 160056 160038,
  .constN 160040 0, .addN 160041 160050 160052,
  .constN 160043 0, .addN 160044 160050 160051, .addN 160044 160044 160055,
  .constN 160046 0, .constN 160047 0]

/-- The first three descriptor words. -/
def descHeadB : Stmt := block [.loadN 160038 160035, .storeN 160037 160038,
  .addN 160038 160037 160024, .storeN 160038 160050,
  .addN 160039 160051 160054, .addN 160038 160038 160024, .storeN 160038 160039]

/-- The top word and the bit: of the left part (flag `0`) or of the right part. -/
def descTopS : Stmt := .ifLtN 160049 160024
  (block [.addN 160038 160038 160024, .storeN 160038 160052,
    .addN 160038 160038 160024, .storeN 160038 160053])
  (block [.addN 160039 160051 160055, .addN 160038 160038 160024, .storeN 160038 160039,
    .addN 160038 160038 160024, .storeN 160038 160056])

/-- **The descriptor of the union.** -/
def descS : Stmt := .seq descLoadB (.seq (kbit 160040 160043 160046 1 160049)
  (.seq descHeadB descTopS))

/-- The registers written by `descS` in band `bL41`. -/
def DescRG (r : ℕ) : Prop := (160038 ≤ r ∧ r ≤ 160056)
section proofs
variable {P : Polygon} {W : ℕ}
variable {c : Config}
set_option maxHeartbeats 16000000 in
theorem descLoadB_exec (hw : WordsBounded W c) {pl pr : ℕ}
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h24 : c.nreg 160024 = 1)
    (hW1 : pl + 4 ≤ W) (hW2 : pr + 4 ≤ W)
    (hW3 : c.nmem zthjg + c.nmem ztoel ≤ W)
    (hW4 : c.nmem zthjg + c.nmem ztoek + c.nmem ztoen ≤ W) :
    ∃ c' k, Exec P W descLoadB c c' k ∧ k = 22 ∧ WordsBounded W c' ∧
      c'.nreg 160050 = c.nmem zthjg ∧ c'.nreg 160051 = c.nmem ztoek ∧
      c'.nreg 160052 = c.nmem ztoel ∧ c'.nreg 160053 = c.nmem ztoem ∧
      c'.nreg 160054 = c.nmem (pr + 2) ∧ c'.nreg 160055 = c.nmem ztoen ∧
      c'.nreg 160056 = c.nmem ztoeo ∧
      c'.nreg 160040 = 0 ∧ c'.nreg 160041 = c.nmem zthjg + c.nmem ztoel ∧
      c'.nreg 160043 = 0 ∧ c'.nreg 160044 = c.nmem zthjg + c.nmem ztoek + c.nmem ztoen ∧
      c'.nreg 160046 = 0 ∧ c'.nreg 160047 = 0 ∧
      (∀ r, ¬ DescRG r → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧ c'.rreg = c.rreg ∧
      c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descLoadB
  exec_block
  all_goals try (config_simp; zunkh; omega)
  zubqj
  refine ⟨rfl, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => by
      unfold DescRG at hr
      zubi
      repeat (rw [Machine.upd_other _ _ _ (by omega)]),
    rfl, rfl, rfl, rfl⟩
  all_goals (config_simp; try zunkh)
set_option maxHeartbeats 8000000 in
theorem descHeadB_exec (hw : WordsBounded W c) {pl TD sl ml mr : ℕ}
    (h35 : c.nreg 160035 = pl) (h37 : c.nreg 160037 = TD) (h24 : c.nreg 160024 = 1)
    (h50 : c.nreg 160050 = sl) (h51 : c.nreg 160051 = ml) (h54 : c.nreg 160054 = mr)
    (hW : TD + 5 ≤ W) (hWm : ml + mr ≤ W) :
    ∃ c' k, Exec P W descHeadB c c' k ∧ k = 7 ∧ WordsBounded W c' ∧
      c'.nmem TD = c.nmem pl ∧ c'.nmem ztjni = sl ∧ c'.nmem ztnpx = ml + mr ∧
      (∀ a, a ≠ TD → a ≠ TD + 1 → a ≠ TD + 2 → c'.nmem a = c.nmem a) ∧
      c'.nreg 160038 = TD + 2 ∧
      ztbvb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descHeadB
  exec_block
  all_goals try (config_simp; simp only [h35, h37, h24, h50, h51, h54]; omega)
  refine ⟨rfl, by_omega, ?_, ?_, ?_, fun a a1 a2 a3 => ?_, ?_, fun r a1 a2 => ?_, rfl, rfl, rfl⟩
  · config_simp; simp only [h35, h37, h24, Machine.upd_apply]
    grind
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  simp_all
set_option maxHeartbeats 8000000 in
theorem descTopS_exec (hw : WordsBounded W c) {TD f tl bl ml tr br : ℕ}
    (h38 : c.nreg 160038 = TD + 2) (h24 : c.nreg 160024 = 1) (h49 : c.nreg 160049 = f)
    (h52 : c.nreg 160052 = tl) (h53 : c.nreg 160053 = bl) (h51 : c.nreg 160051 = ml)
    (h55 : c.nreg 160055 = tr) (h56 : c.nreg 160056 = br) (hW : TD + 5 ≤ W)
    (hWm : ml + tr ≤ W) :
    ∃ c' k, Exec P W descTopS c c' k ∧ k ≤ 7 ∧ WordsBounded W c' ∧
      c'.nmem zthcw = (if f < 1 then tl else ml + tr) ∧
      c'.nmem zthcx = (if f < 1 then bl else br) ∧
      ztcjg ∧
      ztbvb ∧
      c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
  unfold descTopS
  by_cases hf : c.nreg 160049 < c.nreg 160024
  · zuiii
    obtain ⟨c', k, e, hk, hw', r1, r2, r3, r4, r5, r6, r7⟩ : ∃ c' k, Exec P W
        (block [.addN 160038 160038 160024, .storeN 160038 160052,
          .addN 160038 160038 160024, .storeN 160038 160053]) c c' k ∧ k = 4 ∧
        WordsBounded W c' ∧ c'.nmem zthcw = tl ∧ c'.nmem zthcx = bl ∧
        ztcjg ∧
        ztbvb ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try (config_simp; simp only [h38, h24]; omega)
      simp_all
    refine ⟨c', k + 1, .ifLtN_true by_omega e, by_omega, hw',
      by simp_all, by_simp_all, r3, r4, r5, r6, r7⟩
  · zuiii
    obtain ⟨c', k, e, hk, hw', r1, r2, r3, r4, r5, r6, r7⟩ : ∃ c' k, Exec P W
        (block [.addN 160039 160051 160055, .addN 160038 160038 160024, .storeN 160038 160039,
          .addN 160038 160038 160024, .storeN 160038 160056]) c c' k ∧ k = 5 ∧
        WordsBounded W c' ∧ c'.nmem zthcw = ml + tr ∧ c'.nmem zthcx = br ∧
        ztcjg ∧
        ztbvb ∧
        c'.rreg = c.rreg ∧ c'.rmem = c.rmem ∧ c'.output = c.output := by
      exec_block
      all_goals try (config_simp; simp only [h38, h24, h51, h55]; omega)
      simp_all
    refine ⟨c', k + 2, .ifLtN_false by_omega e, by_omega, hw',
      by simp_all, by_simp_all, r3, r4, r5, r6, r7⟩
theorem top_eq {P : Polygon} {C : Chain} (hC : C.P = Qof P) (hn : C.s + C.m < P.n) :
    C.top = (Qof P).vtx ztwi := by
  have := C.topIdx_le
  zuc
  show C.vertex C.topIdx = _
  zugil
  rw [hC, hQn, Nat.mod_eq_of_lt by_omega]
set_option maxHeartbeats 16000000 in
/-- **The descriptor of the union on the RAM.** -/
theorem descS_exec (hG : GoodEnv P) (hWn : P.n + 3 ≤ W) {c : Config} (hw : WordsBounded W c)
    {pl pr TD : ℕ} {H : Host} {C₁ C₂ : Chain}
    (h35 : c.nreg 160035 = pl) (h36 : c.nreg 160036 = pr) (h37 : c.nreg 160037 = TD)
    (h24 : c.nreg 160024 = 1)
    (hd1 : ChainDescAt c.nmem pl zta H C₁) (hd2 : ChainDescAt c.nmem pr zta H C₂)
    (hP1 : C₁.P = Qof P) (hP2 : C₂.P = Qof P) (hs : C₂.s = C₁.s + C₁.m)
    (hn : C₁.s + C₁.m + C₂.m + 1 ≤ P.n) (hlo : pl + 5 ≤ TD) (hlo' : pr + 5 ≤ TD)
    (hW : TD + 5 ≤ W) :
    ∃ c' k, Exec P W descS c c' k ∧ k ≤ 300 ∧ WordsBounded W c' ∧
      (∀ _hj : C₁.m + C₂.m + 1 ≤ C₁.P.n, ∀ a, a < TD → c'.nmem a = c.nmem a) ∧
      c'.nmem TD = c.nmem pl ∧ c'.nmem ztjni = C₁.s ∧ c'.nmem ztnpx = C₁.m + C₂.m ∧
      c'.nmem zthcw = (if (C₂.top).2 ≤ (C₁.top).2 then C₁.topIdx else C₁.m + C₂.topIdx) ∧
      c'.nmem zthcx = (if (C₂.top).2 ≤ (C₁.top).2 then c.nmem ztoem else c.nmem ztoeo) ∧
      ztzu ∧
      (∀ r, ¬ DescRG r → Bk r = false → c'.nreg r = c.nreg r) ∧
      ztcxk ∧ c'.rmem = c.rmem ∧
      c'.output = c.output := by
  obtain ⟨-, -, d1s, d1m, d1t, -⟩ := hd1
  obtain ⟨-, -, d2s, d2m, d2t, -⟩ := hd2
  have ht1 := C₁.topIdx_le; have ht2 := C₂.topIdx_le
  -- loads
  obtain ⟨c1, k1, e1, hk1, hw1, l50, l51, l52, l53, l54, l55, l56, l40, l41, l43, l44, l46, l47,
    fr1, hm1, hrr1, hrm1, ho1⟩ := descLoadB_exec (P := P) hw h35 h36 h24 by_omega by_omega
    by_omega by_omega
  rw [d1s] at l50 l41 l44; rw [d1m] at l51 l44; rw [d1t] at l52 l41; rw [d2m] at l54
  rw [d2t] at l55 l44
  -- the sign test
  obtain ⟨c2, k2, e2, hk2, fb2, hf2, hiff2⟩ := kbit_exec (P := P) hG hWn c1 hw1
    (a := 160040) (b := 160043) (d := 160046) (op := 1) (dst := 160049) by_omega by_omega
    by_omega by_omega by_omega (sa := .vtx (C₁.s + C₁.topIdx))
    (sb := .vtx (C₁.s + C₁.m + C₂.topIdx)) (sd := .vtx 0)
    (show C₁.s + C₁.topIdx < P.n by omega) (show C₁.s + C₁.m + C₂.topIdx < P.n by omega)
    ztdwe ⟨l40, l41⟩ ⟨l43, l44⟩ ⟨l46, l47⟩
  zueik
  zump
  have k2r : ∀ r, Bk r = false → r ≠ 160049 → c2.nreg r = c1.nreg r := fun r h1 h2 =>
    fr2 r ztljl
  have hflag : c2.nreg 160049 = 1 ↔ (C₁.top).2 < (C₂.top).2 := by
    rw [hiff2]
    simp only [SignTest, SymPt.eval]
    rw [top_eq hP1 by_omega, top_eq hP2 by_omega, hs]
  zudmv
  -- the head words
  obtain ⟨c3, k3, e3, hk3, hw3, m0, m1', m2', mout3, h38, fr3, hrr3, hrm3, ho3⟩ :=
    descHeadB_exec (P := P) hw2 (pl := pl) (TD := TD) (sl := C₁.s) (ml := C₁.m) (mr := C₂.m)
    ztwum
    ztwum
    ztwum
    by_simp_all
    by_simp_all
    by_simp_all hW by_omega
  -- the top word and the bit
  obtain ⟨c4, k4, e4, hk4, hw4, m3', m4', mout4, fr4, hrr4, hrm4, ho4⟩ :=
    descTopS_exec (P := P) hw3 (TD := TD) (f := c2.nreg 160049) (tl := C₁.topIdx)
    (bl := c.nmem ztoem) (ml := C₁.m) (tr := C₂.topIdx) (br := c.nmem ztoeo) h38
    (by rw [fr3 _ by_omega by_omega, k2r _ by_grind by_omega,
      fr1 _ ztzc]; omega)
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    by_grind
    hW by_omega
  have hfle : c2.nreg 160049 < 1 ↔ (C₂.top).2 ≤ (C₁.top).2 := by
    have := hf2
    constructor
    · grind
    grind
  have mem4 : ∀ a, ztlfu → c4.nmem a = c.nmem a := fun a ha => by
    rw [mout4 a by_omega by_omega, mout3 a by_omega by_omega by_omega, hm2, hm1]
  refine ⟨c4, k1 + ztbqj, .seq e1 ztbal, by_omega, hw4,
    by grind, ?_, ?_, ?_, ?_, ?_, mem4, fun r h1 h2 => ?_, fun r hr hr' => ?_,
    by grind, by_grind⟩
  · grind
  · grind
  · grind
  · rw [m3']; split_ifs with a1 a2 a2 <;> first | rfl | (exfalso; exact by_grind) |
      (exfalso; exact by_grind)
  · rw [m4']; split_ifs with a1 a2 a2 <;> first | rfl | (exfalso; exact by_grind) |
      (exfalso; exact by_grind)
  · unfold DescRG at h1
    rw [fr4 r by_omega by_omega, fr3 r by_omega by_omega, k2r r h2 by_omega,
      fr1 r ztzc]
  · rw [hrr4, hrr3, frr2 r (by simp [Bkb, hr, hr']), hrr1]
end proofs
end
end Chazelle.Core.L41
namespace Chazelle.Core.L41
open Machine
@[expose] public section
def MergePre (X : MemCtx) (Ok : Polygon → Model → Prop) (P : Polygon) (W : ℕ) (c : Config) :
    Prop :=
  GoodEnv P ∧ hostWords P.n ≤ W ∧
    X.holds P c.nmem ztdab ztm ∧
    rd c bMerge 5 + fuseLoss ≤ X.cap P c.nmem ztdab ∧ 4 ≤ rd c bMerge 7 ∧
    rd c bMerge 5 + fuseLoss ≤ rd c bMerge 6 ∧
    JunctionWF P ztm c.nmem ztefr ztefs zteft ∧
    ∃ Hs J N₁ N₂, JunctionAt c.nmem ztefr ztefs zteft zta Hs J ∧
      J.P.Simple ∧ SharedGeneric J ∧
      Ok P ztbw ∧ Ok P ztj ∧
      Ok P ztbm ∧ (chainModel J.whole).FullDegLe zta ztbnk ∧
      NFWithin c.nmem ztefu ztm N₁ ∧
      NFWithin c.nmem ztefv ztm N₂ ∧
      (∃ γ₁, γ₁ ≤ rd c bMerge 5 ∧
        IsCanonicalNF ztbw zta N₁ γ₁ ztbnk) ∧
      (∃ γ₂, γ₂ ≤ rd c bMerge 5 ∧
        IsCanonicalNF ztj zta N₂ γ₂ ztbnk)

/-- The postcondition of a merge. -/
def MergePost (P : Polygon) (c c' : Config) : Prop :=
  ∀ Hs J N₁ N₂,
    JunctionAt c.nmem ztefr ztefs zteft zta Hs J →
    NFAt c.nmem ztefu N₁ → NFAt c.nmem ztefv N₂ →
    ∃ N, c.nreg ALLOC ≤ rd c' bMerge 8 ∧ NFWithin c'.nmem ztrvo ztdo N ∧
      IsCanonicalNF ztbm zta N ztrvl ztbnk

/-- The cost of a merge. -/
def mergeCost (κ F G H : ℕ → ℕ) (c : Config) : ℕ :=
  κ ztbnk * ztyqe *
    F ztdaa * G ztdaa *
    ztxqq

/-- **One merge program** meets the contract of `MergeSpec`. -/
def MergeMeets (s : Stmt) (κ F G H : ℕ → ℕ) (X : MemCtx) (Ok : Polygon → Model → Prop) : Prop :=
  Meets s ztodk (fun P W c => MergePre X Ok P W c)
    (fun P c c' => MergePost P c c') (fun _ c => mergeCost κ F G H c)

/-- **The merge contract of `MergeSpec`.** -/
theorem mergeMeets_of (hM : MergeSpec) : ∃ (mk : Stmt → Stmt → Stmt) (κ : ℕ → ℕ),
    ∀ (sh cu : Stmt) (Bs Bc : Finset ℕ) (F G H : ℕ → ℕ) (X : MemCtx)
      (Ok : Polygon → Model → Prop), X.CapLocal → X.Halves → ztcxi →
      Monotone F → Monotone G → Monotone H →
      Bs ⊆ oracleBands → Bc ⊆ oracleBands →
      ShooterOK sh Bs F X Ok → CutterOK cu Bc G H X Ok → MergeMeets ztdvk κ F G H X Ok := by
  tauto
