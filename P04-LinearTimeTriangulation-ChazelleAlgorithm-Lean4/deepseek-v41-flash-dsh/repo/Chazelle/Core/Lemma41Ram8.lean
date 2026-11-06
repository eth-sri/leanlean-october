module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Ram7
public import Chazelle.Core.FactsL23
public import Chazelle.Core.FactsInterior

/-!
# WP-J, part 16: the pair loop of a level

* shapes: a node of the merge tree is described by `(start, length, granularity)` (`Shp`); a
  level is a list of shapes, stored as an array of `[descriptor, NF]` entries (`LevelAt`);
* `NodeOK.chords_le`: Lemma 2.3 for a node, `K γ ≤ 60 (2 m + 7)`, so `K ≤ kb` (`NodeOK.chords_kb`);
* `forStep2`: a loop over pairs with per-iteration costs;
* `pairL_exec`: the pair loop of a level merges entries `2q, 2q + 1` for all `q < j / 2`, leaving
  a back-linked list of cells of the new nodes (`PairSt`).
-/

namespace Chazelle.Core.L41

open Machine Machine.Stmt Programs Chazelle.Merge Finset

@[expose] public section

/-- A node of the merge tree in shape: start, length, granularity. -/
abbrev Shp := ℕ × ℕ × ℕ

/-- The node `k` of a level (in shape). -/
def nd (ns : List Shp) (k : ℕ) : Shp := ns.getD k (0, 0, 0)

/-- The chord bound of a node from Lemma 2.3. -/
def kb (x : Shp) : ℕ := 60 * (2 * x.2.1 + 7) / x.2.2

/-- **A level in memory**: entry `k` of the array at `B` is a node of shape `nd ns k`. -/
def LevelAt (P : Polygon) (m : ℕ → ℕ) (A B hp : ℕ) (ns : List Shp) : Prop :=
  ∀ k, k < ns.length → ∃ C : Chain, C.s = (nd ns k).1 ∧ C.m = (nd ns k).2.1 ∧
    NodeOK P m A hp (m (B + 2 * k)) (m (B + 2 * k + 1)) C (nd ns k).2.2

/-- Consecutive shapes. -/
def Consec (ns : List Shp) : Prop :=
  ∀ k, k + 1 < ns.length → (nd ns (k + 1)).1 = (nd ns k).1 + (nd ns k).2.1

/-- The chord family of a normal form has one chord per record. -/
theorem nf_chords_ncard {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N) :
    (N.F (chainModel C) Q).ncard = N.chords.length := by
  classical
  obtain ⟨-, hinj, -⟩ := hN
  have hFn : N.F (chainModel C) Q = (fun i => (N.chord i).toSet (chainModel C) Q) ''
      Set.Iio N.chords.length := by
    ext c; constructor
    · rintro ⟨r, hr, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      refine ⟨i, hi, ?_⟩
      show (N.chord i).toSet _ _ = _
      unfold NF.chord; Ξ NFLoc.getD_of_lt _ hi
    · rintro ⟨i, hi, rfl⟩
      refine ⟨N.chord i, ?_, rfl⟩
      unfold NF.chord; rw [NFLoc.getD_of_lt _ hi]; exact List.getElem_mem hi
  rw [hFn, Set.InjOn.ncard_image (s := Set.Iio N.chords.length)
    (f := fun i => (N.chord i).toSet (chainModel C) Q) (fun a ha b hb h => hinj a b ha hb h),
    ← Finset.coe_range, Set.ncard_coe_finset, Finset.card_range]

/-- **Lemma 2.3 for a node**: `K γ ≤ 60 (2 m + 7)`. -/
theorem NodeOK.chords_le {P : Polygon} {m : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {γ : ℕ}
    (hG : GoodEnv P) (h : NodeOK P m A hp d f C γ) : m f * γ ≤ 60 * (2 * C.m + 7) := by
  obtain ⟨-, hCP, -, -, -, -, N, hN, hc⟩ := h
  have hQ : (Qof P).Simple := (shearInvariance (epsOf P) P).1 hG.1
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, by rw [hCP]; exact hQ, rfl⟩
  have hM := walkAx_of_goodModel hGM
  have hF := hc.1.1
  have := hM.lemma23_walk hF.2.1 hF.1 hc.2.1 hc.2.2.1
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n C.sideBeta
  Ξ' nf_chords_ncard hc.1, hn at this
  rw [hN.holds.1]; omega

theorem NodeOK.chords_kb {P : Polygon} {m : ℕ → ℕ} {A hp d f : ℕ} {C : Chain} {x : Shp}
    (hG : GoodEnv P) (h : NodeOK P m A hp d f C x.2.2) (hm : C.m = x.2.1) (hγ : 1 ≤ x.2.2) :
    m f ≤ kb x := by
  have := h.chords_le hG
  Ξ' hm at this
  unfold kb
  exact (Nat.le_div_iff_mul_le hγ).mpr this

theorem mergeCostV_mono (κ F G H : ℕ → ℕ) {x x' y y' : ℕ} (γ M : ℕ) (hx : x ≤ x') (hy : y ≤ y') :
    mergeCostV κ F G H x y γ M ≤ mergeCostV κ F G H x' y' γ M := by
  unfold mergeCostV
  gcongr

section proofs

variable {P : Polygon} {W : ℕ}

/-- **A loop over pairs** (`ri` counts by `2`, up to `N`) with per-iteration costs `b p`. -/
theorem forStep2 {ri rn : ℕ} {body : Stmt} (I : ℕ → Config → Prop) (N : ℕ) (b : ℕ → ℕ)
    (hI : ∀ p c, I p c → WordsBounded W c ∧ c.nreg ri = 2 * p ∧ c.nreg rn = N)
    (hbody : ∀ p c, 2 * p < N → I p c → ∃ c' k, Exec P W body c c' k ∧ k ≤ b p ∧ I (p + 1) c' ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k)
    {c : Config} (hc : I 0 c) :
    ∃ c' k, Exec P W (.whileLtN ri rn body) c c' k ∧
      k ≤ (∑ q ∈ range ((N + 1) / 2), (b q + 2)) + 2 ∧ I ((N + 1) / 2) c' ∧
      c'.nreg ALLOC ≤ c.nreg ALLOC + k := by
  obtain ⟨c', k, e, ⟨p', hIp, hp'⟩, htest, hk, hψ⟩ := whileLtN_potential_lb' (P := P) (W := W)
    (a := ri) (b := rn) (body := body) (fun c => ∃ p, I p c ∧ p ≤ (N + 1) / 2)
    (fun c => ∑ q ∈ Ico (c.nreg ri / 2) ((N + 1) / 2), (b q + 2)) (fun c => c.nreg ALLOC)
    (fun c ⟨p, h, _⟩ => (hI p c h).1)
    (fun c ⟨p, h, hpn⟩ htest => by
      obtain ⟨-, hri, hrn⟩ := hI p c h
      Ξ' hri, hrn at htest
      obtain ⟨c', k, e, hk, h', hA'⟩ := hbody p c htest h
      obtain ⟨-, hri', -⟩ := hI (p + 1) c' h'
      refine ⟨c', k, e, ⟨p + 1, h', ⋄⟩, ?_, hA'⟩
      rw [hri, hri', show 2 * (p + 1) / 2 = p + 1 by omega, show 2 * p / 2 = p by omega,
        Finset.sum_eq_sum_Ico_succ_bot (show p < (N + 1) / 2 by omega)]
      omega) ⟨0, hc, Nat.zero_le _⟩
  obtain ⟨-, hri, hrn⟩ := hI p' c' hIp
  have hpn : p' = (N + 1) / 2 := by rw [hri, hrn] at htest; omega
  subst hpn
  refine ⟨c', k, e, ?_, hIp, hψ⟩
  obtain ⟨-, hri0, -⟩ := hI 0 c hc
  Ξ' hri0, show 2 * 0 / 2 = 0 by rfl, ← Finset.range_eq_Ico at hk
  exact hk

end proofs

/-- The per-pair cost bound of a level. -/
def pairCost (κ F G H : ℕ → ℕ) (ns : List Shp) (γ₀ q : ℕ) : ℕ :=
  mergeCostV κ F G H (kb (nd ns (2 * q))) (kb (nd ns (2 * q + 1))) γ₀
    ((nd ns (2 * q)).2.1 + (nd ns (2 * q + 1)).2.1)

/-- The pair loop. -/
def pairL (sM : Stmt) : Stmt := .whileLtN 160062 160067 (pairS sM)

/-- **The state of the pair loop** after `p` merges. -/
def PairSt (P : Polygon) (W : ℕ) (X : MemCtx) (c0 : Config) (A0 B hp hX tgt : ℕ) (ns : List Shp)
    (pcs : ℕ → ℕ) (p : ℕ) (c : Config) : Prop :=
  WordsBounded W c ∧ c.nreg 160062 = 2 * p ∧ c.nreg 160065 = B + 4 * p ∧ c.nreg 160064 = p ∧
    A0 ≤ c.nreg ALLOC ∧ c.nreg ALLOC ≤ A0 + ∑ q ∈ range p, (pcs q + 8) ∧
    (∀ a, a < A0 → c.nmem a = c0.nmem a) ∧ (∀ a, a < A0 → c.rmem a = c0.rmem a) ∧
    c.output = c0.output ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → r ≠ ALLOC → c.nreg r = c0.nreg r) ∧
    (∀ r, bandOf r ∉ mergeBands ∪ oracleBands → ¬ PairRG r → c.rreg r = c0.rreg r) ∧
    X.holds P c.nmem hX (c.nreg ALLOC) ∧ X.cap P c.nmem hX = X.cap P c0.nmem hX ∧
    ∃ e : ℕ → ℕ, (∀ q, q < p → A0 ≤ e q ∧ e q + 3 ≤ c.nreg ALLOC ∧
      (1 ≤ q → c.nmem (e q + 2) = e (q - 1)) ∧
      ∃ C : Chain, C.s = (nd ns (2 * q)).1 ∧
        C.m = (nd ns (2 * q)).2.1 + (nd ns (2 * q + 1)).2.1 ∧
        NodeOK P c.nmem (c.nreg ALLOC) hp (c.nmem (e q)) (c.nmem (e q + 1)) C tgt) ∧
      (1 ≤ p → c.nreg 160063 = e (p - 1))

section proofs

variable {P : Polygon} {W : ℕ}

theorem not_pairRG {r : ℕ} (h : r < 160035 ∨ (160056 < r ∧ r < 160062) ∨ (160065 < r ∧ r < 160090)
    ∨ 160093 < r) : ¬ PairRG r := by
  unfold PairRG DescRG; omega

theorem bandOK_l41 {r : ℕ} (h1 : 160000 ≤ r) (h2 : r < 170000) :
    bandOf r ∉ mergeBands ∪ oracleBands := by
  rw [bandOf_l41 h1 h2]; exact band_l41_notin

set_option maxHeartbeats 16000000 in
/-- **The pair loop of a level.** -/
theorem pairL_exec (hG : GoodEnv P) (hWh : hostWords P.n ≤ W) (hWn : P.n + 3 ≤ W)
    {sM : Stmt} {κ F G H : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
    (hMM : MergeMeets sM κ F G H X Ok) (hXc : X.CapLocal)
    (hOk : ∀ C : Chain, C.P = Qof P → Ok P (chainModel C))
    {c0 : Config} (hw : WordsBounded W c0) {A0 B hp hX γ₀ tgt : ℕ} {ns : List Shp}
    (hj : 1 ≤ ns.length)
    (hA : c0.nreg ALLOC = A0) (h62 : c0.nreg 160062 = 0) (h65 : c0.nreg 160065 = B)
    (h64 : c0.nreg 160064 = 0) (h67 : c0.nreg 160067 = ns.length - 1)
    (h33 : c0.nreg 160033 = γ₀) (h34 : c0.nreg 160034 = tgt) (h00 : c0.nreg 160000 = hX)
    (h24 : c0.nreg 160024 = 1) (h80 : c0.nreg 160080 = 2) (h81 : c0.nreg 160081 = 5)
    (h83 : c0.nreg 160083 = 3) (h84 : c0.nreg 160084 = 4)
    (hL : LevelAt P c0.nmem A0 B hp ns) (hc : Consec ns) (hB : B + 2 * ns.length ≤ A0)
    (hγ : ∀ k, k < ns.length → (nd ns k).2.2 ≤ γ₀)
    (hγ1 : ∀ k, k < ns.length → 1 ≤ (nd ns k).2.2)
    (hXh : X.holds P c0.nmem hX A0) (hcap : γ₀ + fuseLoss ≤ X.cap P c0.nmem hX)
    (htg : γ₀ + fuseLoss ≤ tgt)
    (hbud : A0 + ∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 8) ≤ W) :
    ∃ c' k, Exec P W (pairL sM) c0 c' k ∧
      k ≤ (∑ q ∈ range (ns.length / 2), (pairCost κ F G H ns γ₀ q + 331)) + 2 ∧
      c'.nreg ALLOC ≤ A0 + k ∧ PairSt P W X c0 A0 B hp hX tgt ns (pairCost κ F G H ns γ₀) (ns.length / 2) c' := by
  have hAl : ALLOC = 9999 := rfl
  set j := ns.length with hjdef
  set pcs := pairCost κ F G H ns γ₀ with hpcs
  have hnp : (j - 1 + 1) / 2 = j / 2 := by congr 1; omega
  have hsum_mono : ∀ p, p ≤ j / 2 → ∑ q ∈ range p, (pcs q + 8) ≤
      ∑ q ∈ range (j / 2), (pcs q + 8) := fun p hp =>
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr hp)
  obtain ⟨c', k, e, hk, hI, hψ⟩ := forStep2 (P := P) (W := W) (ri := 160062) (rn := 160067)
    (body := pairS sM) (PairSt P W X c0 A0 B hp hX tgt ns pcs) (j - 1) (fun q => pcs q + 329)
    (fun p c h => ⟨h.1, h.2.1, by
      rw [h.2.2.2.2.2.2.2.2.2.1 _ (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega))
        (by rw [hAl]; omega)]; exact h67⟩)
    (fun p c hp h => by
      obtain ⟨hwc, c62, c65, c64, cA0, cA1, cm, crm, co, cr, crr, cX, ccap, ee, hee, hprev⟩ := h
      have cr' : ∀ r, 160000 ≤ r → r < 160035 → c.nreg r = c0.nreg r := fun r a b =>
        cr r (bandOK_l41 a (by omega)) (not_pairRG (by omega)) (by rw [hAl]; omega)
      have cr'' : ∀ r, 160065 < r → r < 160090 → c.nreg r = c0.nreg r := fun r a b =>
        cr r (bandOK_l41 (by omega) (by omega)) (not_pairRG (by omega)) (by rw [hAl]; omega)
      set A := c.nreg ALLOC with hAdef
      have hp1 : 2 * p + 1 < j := by omega
      obtain ⟨C1, s1, m1', n1⟩ := hL (2 * p) (by omega)
      obtain ⟨C2, s2, m2', n2⟩ := hL (2 * p + 1) hp1
      have cmA : ∀ a, a < A0 → c.nmem a = c0.nmem a := cm
      have n1c := (n1.agree cmA).mono cA0
      have n2c := (n2.agree cmA).mono cA0
      have hcons : C2.s = C1.s + C1.m := by rw [s1, s2, m1', hc (2 * p) hp1]
      have kb1 : c.nmem (c0.nmem (B + 2 * (2 * p) + 1)) ≤ kb (nd ns (2 * p)) :=
        n1c.chords_kb hG m1' (hγ1 _ (by omega))
      have kb2 : c.nmem (c0.nmem (B + 2 * (2 * p + 1) + 1)) ≤ kb (nd ns (2 * p + 1)) :=
        n2c.chords_kb hG m2' (hγ1 _ hp1)
      have hmc : mergeCostV κ F G H (c.nmem (c0.nmem (B + 2 * (2 * p) + 1)))
          (c.nmem (c0.nmem (B + 2 * (2 * p + 1) + 1))) γ₀ (C1.m + C2.m) ≤ pcs p := by
        have := mergeCostV_mono κ F G H γ₀ (C1.m + C2.m) kb1 kb2
        rw [m1', m2'] at this ⊢; exact this
      have hbp : A + 5 + pcs p + 3 ≤ W := by
        have := hsum_mono (p + 1) (by omega)
        rw [Finset.sum_range_succ] at this
        omega
      obtain ⟨c'', k'', e'', hk'', hw'', hAk'', E, TD, f, C, hE1, hE2, hA'', w0, w1, w2, hCs, hCm,
          hN,
          q63, q65, q62, q64, mem'', rmem'', out'', hX'', cap'', fr'', frr''⟩ :=
        pairS_exec hG hWh hWn hMM hXc hOk hwc (A := A) (ptr := B + 4 * p)
          (d1 := c0.nmem (B + 2 * (2 * p))) (f1 := c0.nmem (B + 2 * (2 * p) + 1))
          (d2 := c0.nmem (B + 2 * (2 * p + 1))) (f2 := c0.nmem (B + 2 * (2 * p + 1) + 1))
          (prev := c.nreg 160063) (i := 2 * p) (j := p) (hX := hX) (γ₀ := γ₀) (tgt := tgt)
          rfl c65 rfl c62 c64 (by rw [cr' _ (by omega) (by omega)]; exact h33)
          (by rw [cr' _ (by omega) (by omega)]; exact h34)
          (by rw [cr' _ (by omega) (by omega)]; exact h00)
          (by rw [cr' _ (by omega) (by omega)]; exact h24)
          (by rw [cr'' _ (by omega) (by omega)]; exact h80)
          (by rw [cr'' _ (by omega) (by omega)]; exact h81)
          (by rw [cr'' _ (by omega) (by omega)]; exact h83)
          (by rw [cr'' _ (by omega) (by omega)]; exact h84)
          (by rw [cmA _ (by omega)]; congr 1; omega)
          (by rw [cmA _ (by omega)]; congr 1; omega)
          (by rw [cmA _ (by omega)]; congr 1; omega)
          (by rw [cmA _ (by omega)]; congr 1; omega)
          n1c n2c (by rw [← s1] at *; exact hγ _ (by omega)) (hγ _ hp1) hcons cX
          (by rw [ccap]; exact hcap) htg (by omega) (by omega) (by omega) (by omega)
      refine ⟨c'', k'', e'', by omega, ?_, hAk''⟩
      refine ⟨hw'', by rw [q62]; ring, by rw [q65]; ring, q64, by omega, ?_,
        fun a ha => by rw [mem'' a (by omega)]; exact cm a ha,
        fun a ha => by rw [rmem'' a (by omega)]; exact crm a ha, by rw [out'']; exact co,
        fun r h1 h2 h3 => by rw [fr'' r h1 h2 h3]; exact cr r h1 h2 h3,
        fun r h1 h2 => by rw [frr'' r h1 h2]; exact crr r h1 h2,
        by rw [hA'']; exact hX'', by rw [cap'']; exact ccap,
        fun q => if q = p then E else ee q, fun q hq => ?_, fun _ => by simp [q63]⟩
      · rw [hA'', Finset.sum_range_succ]; omega
      · rcases Nat.lt_or_ge q p with hqp | hqp
        · obtain ⟨a1, a2, a3, C', b1, b2, b3⟩ := hee q hqp
          simp only [show q ≠ p by omega, ite_false]
          refine ⟨a1, by omega, fun hq1 => ?_, C', b1, b2, ?_⟩
          · simp only [show q - 1 ≠ p by omega, ite_false]
            rw [mem'' _ (by omega)]; exact a3 hq1
          · rw [mem'' _ (by omega), mem'' _ (by omega), hA'']
            exact (b3.agree mem'').mono (by omega)
        · have hqe : q = p := by omega
          subst hqe
          simp only [ite_true]
          refine ⟨by omega, by omega, fun hq1 => ?_, C, ?_, ?_, ?_⟩
          · simp only [show q - 1 ≠ q by omega, ite_false]
            rw [w2, hprev hq1]
          · rw [hCs, s1]
          · rw [hCm, m1', m2']
          · rw [w0, w1, hA'']; exact hN)
    (⟨hw, by rw [h62], by rw [h65]; ring, h64, by omega, by rw [hA]; simp,
      fun _ _ => rfl, fun _ _ => rfl, rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl,
      by rw [hA]; exact hXh, rfl, fun _ => 0, fun q hq => by omega, fun h => by omega⟩)
  rw [hnp] at hk hI
  refine ⟨c', k, e, ?_, by rw [← hA]; exact hψ, hI⟩
  have : ∑ q ∈ range (j / 2), (pcs q + 329 + 2) = ∑ q ∈ range (j / 2), (pcs q + 331) :=
    Finset.sum_congr rfl fun _ _ => by ring
  omega

end proofs

end

end Chazelle.Core.L41
