module

public import Chazelle.Core.RestoreFRef
public import Chazelle.Core.RestoreFKind0
public import Chazelle.Core.RestoreFSide
public import Chazelle.Core.RestoreLeafMath

/-!
# WP-E, the search on the RAM (`FindOK`), part 21: the leaf of the descent

At the leaf region `r` (`81121`) of the piece's normal form (handle `81134`), visit the arcs of
`r` one by one; on an arc, visit `arcCnt` walk vertices of `Cα`'s walk from the start edge, and
test (both directions) the host vertex of every visited vertex strictly inside the stretch.

* `arcLoad`: the arc `j = arcs(r)[t]` (`81102`) and its ends `(81103, 81106)`, `(81107, 81108)`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs NFLoc

/-- The reads of the arc index `j = arcs(r)[t]`. -/
def arcL1 : List Instr :=
  [.addN 81114 81134 81015, .loadN 81114 81114, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81012, .loadN 81114 81114,
    .addN 81115 81134 81016, .loadN 81115 81115, .addN 81114 81115 81114,
    .addN 81114 81114 81100, .loadN 81102 81114]

/-- The reads of the ends of the arc `j`. -/
def arcL2 : List Instr :=
  [.addN 81114 81134 81014, .addN 81114 81114 81012, .loadN 81114 81114,
    .addN 81114 81114 81102, .addN 81114 81114 81102, .addN 81114 81114 81102,
    .addN 81114 81114 81102, .addN 81114 81114 81102, .addN 81114 81114 81012,
    .loadN 81103 81114, .addN 81114 81114 81012, .loadN 81106 81114,
    .addN 81114 81114 81012, .loadN 81107 81114, .addN 81114 81114 81012, .loadN 81108 81114]

/-- **The arc of the leaf at index `t`.** -/
def arcLoad : Stmt := .seq (Stmt.block arcL1) (Stmt.block arcL2)

variable {E : FEnv} {c₀ c : Config}

theorem arcLoad_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N)
    (hr : c.nreg 81121 < N.nRegions) (ht : c.nreg 81100 < (N.region (c.nreg 81121)).arcs.length)
    (hj : (N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0 < N.arcs.length) :
    FRS B E.P E.W c₀ arcLoad c 30 (fun c' =>
      c'.nreg 81102 = (N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0 ∧
      c'.nreg 81103 = (N.arc ((N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0)).s.edge ∧
      c'.nreg 81106 = (N.arc ((N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0)).s.hgt ∧
      c'.nreg 81107 = (N.arc ((N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0)).e.edge ∧
      c'.nreg 81108 = (N.arc ((N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0)).e.hgt ∧
      ∀ q, q ≠ 81102 → q ≠ 81103 → q ≠ 81106 → q ≠ 81107 → q ≠ 81108 → q ≠ 81114 →
        q ≠ 81115 → c'.nreg q = c.nreg q) := by
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  obtain ⟨hB7, -, hab, hrb, hlb, -⟩ := nf_bounds hN'
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hrl : c.nreg 81121 < N.regions.length := hr
  obtain ⟨-, -, -, hl, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  have rj := hl _ ht
  obtain ⟨-, s1, s2, s3, s4⟩ := hNA.2.2.2.2.2.2.1 _ hj
  have b1 := hrb _ hr
  have b2 := hlb _ hr _ ht
  have b3 := hab _ hj
  have fx : ∀ c', FInv E.W c₀ c' → c'.nreg 81015 = 5 ∧ c'.nreg 81016 = 7 ∧ c'.nreg 81014 = 3 ∧
      c'.nreg 81012 = 1 := fun c' h =>
    ⟨by rw [h.hin _ (by unfold FFix; omega), hE.k5], by rw [h.hin _ (by unfold FFix; omega), hE.k7],
      by rw [h.hin _ (by unfold FFix; omega), hE.k3], by rw [h.hin _ (by unfold FFix; omega), hE.k1]⟩
  obtain ⟨k5, k7, k3, k1⟩ := fx c hI
  have e5 : c.nmem (c.nreg 81134 + 5) + c.nreg 81121 + c.nreg 81121 + c.nreg 81121 +
      c.nreg 81121 + c.nreg 81121 + 1 = c.nmem (c.nreg 81134 + 5) + 5 * c.nreg 81121 + 1 := by ring
  -- stage 1
  have ok1 : okB E.W c.nmem arcL1 c.nreg := by
    simp only [arcL1, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k7, k1]
    norm_num
    try rw [e5]
    (repeat' apply And.intro) <;> omega
  refine FRS.seq (K₂ := 16) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem arcL1 c.nreg q := fun q => by rw [h₁]
  have m₁ : c₁.nmem = c.nmem := by rw [h₁]
  have v02 : c₁.nreg 81102 = (N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0 := by
    rw [e₁]; simp [arcL1, regB, regI, upd, k5, k7, k1]
    rw [e5]; rw [List.getD_eq_getElem?_getD] at rj; exact rj
  have f₁ : ∀ q, q ≠ 81102 → q ≠ 81114 → q ≠ 81115 → c₁.nreg q = c.nreg q := fun q h1 h2 h3 => by
    rw [e₁]; refine regB_other _ _ _ (fun i hi => ?_)
    simp only [arcL1, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp only [dstI] <;> omega
  obtain ⟨-, -, k3₁, k1₁⟩ := fx c₁ hI₁
  have w34 := f₁ 81134 (by norm_num) (by norm_num) (by norm_num)
  have e4 : c.nreg 81134 + 3 + 1 = c.nreg 81134 + 4 := by ring
  generalize hjdef : (N.region (c.nreg 81121)).arcs.getD (c.nreg 81100) 0 = j at v02 b3 s1 s2 s3 s4 ⊢
  -- stage 2
  have ok2 : okB E.W c₁.nmem arcL2 c₁.nreg := by
    simp only [arcL2, okB, okI, regI, upd]
    simp only [FScr, FOut, k3₁, k1₁, w34, v02, m₁]
    norm_num
    rw [e4]
    (repeat' apply And.intro) <;> omega
  refine (FRS.block hB _ hI₁ ok2).mono (by simp [arcL2]) (fun c₂ h₂ => ?_)
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem arcL2 c₁.nreg q := fun q => by rw [h₂]
  have ea : c.nmem (c.nreg 81134 + 4) + j + j + j + j + j + 1 =
      c.nmem (c.nreg 81134 + 4) + 5 * j + 1 := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  · rw [e₂, regB_other _ _ _ (fun i hi => ?_), v02]
    simp only [arcL2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp only [dstI] <;> omega
  · rw [e₂]; simp [arcL2, regB, regI, upd, k3₁, k1₁, w34, v02, m₁, e4]; rw [ea, s1]
  · rw [e₂]; simp [arcL2, regB, regI, upd, k3₁, k1₁, w34, v02, m₁, e4]
    rw [ea, show c.nmem (c.nreg 81134 + 4) + 5 * j + 1 + 1 = c.nmem (c.nreg 81134 + 4) + 5 * j + 2
      by ring, s2]
  · rw [e₂]; simp [arcL2, regB, regI, upd, k3₁, k1₁, w34, v02, m₁, e4]
    rw [ea, show c.nmem (c.nreg 81134 + 4) + 5 * j + 1 + 1 + 1 =
      c.nmem (c.nreg 81134 + 4) + 5 * j + 3 by ring, s3]
  · rw [e₂]; simp [arcL2, regB, regI, upd, k3₁, k1₁, w34, v02, m₁, e4]
    rw [ea, show c.nmem (c.nreg 81134 + 4) + 5 * j + 1 + 1 + 1 + 1 =
      c.nmem (c.nreg 81134 + 4) + 5 * j + 4 by ring, s4]
  · rw [e₂, regB_other _ _ _ (fun i hi => ?_), f₁ q h1 h6 h7]
    simp only [arcL2, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> simp only [dstI] <;> omega

/-- Run `S` if `a = b`. -/
def ifEq (a b : ℕ) (S : Stmt) : Stmt := .ifLtN a b .skip (.ifLtN b a .skip S)

theorem FRS.ifEq_eq {B : Finset ℕ} {P : Polygon} {W : ℕ} {a b : ℕ} {S : Stmt} {K : ℕ}
    {Q : Config → Prop} (h : c.nreg a = c.nreg b) (hS : FRS B P W c₀ S c K Q) :
    FRS B P W c₀ (ifEq a b S) c (K + 4) Q :=
  (FRS.ifF (by omega) (FRS.ifF (by omega) hS)).mono (by omega) (fun _ h => h)

theorem FRS.ifEq_ne {B : Finset ℕ} {P : Polygon} {W : ℕ} {a b : ℕ} {S : Stmt} {K : ℕ}
    {Q : Config → Prop} (hI : FInv W c₀ c) (h : c.nreg a ≠ c.nreg b) (hq : Q c) :
    FRS B P W c₀ (ifEq a b S) c (K + 4) Q := by
  by_cases h1 : c.nreg a < c.nreg b
  · exact (FRS.ifT h1 (FRS.skip (K := 0) hI hq)).mono (by omega) (fun _ h => h)
  · exact (FRS.ifF h1 (FRS.ifT (by omega) (FRS.skip (K := 0) hI hq))).mono (by omega)
      (fun _ h => h)

/-- **The count of an arc**: `w` (`81110`), the count (`81104`), the next arc index. -/
def cntS : Stmt :=
  .seq (Stmt.block [.constN 81110 0, .loadN 81111 81134])
    (.seq (.ifLtN 81011 81111 (ifEq 81103 81107
        (.seq (cmpA 81112 81103 81106 81107 81108) (Stmt.block [.copyN 81110 81112]))) .skip)
      (.seq (Stmt.block [.addN 81104 81107 81105, .subN 81104 81104 81103])
        (.seq (.ifLtN 81104 81105 .skip (Stmt.block [.subN 81104 81104 81105]))
          (.seq (Stmt.block [.addN 81104 81104 81012])
            (.seq (ifEq 81103 81107 (.ifLtN 81011 81110 .skip
                (Stmt.block [.addN 81104 81104 81105])))
              (Stmt.block [.addN 81100 81100 81012]))))))

/-- The cost bound of `cntS`. -/
def csK : ℕ := 11040

/-- The bit `w` of an arc with ends `(se, sh)`, `(ee, eh)` (normal form with `nc` chords). -/
noncomputable def wBit (Cα : Chain) (Q : Polygon) (nc se sh ee eh : ℕ) : ℕ := by
  classical
  exact if 0 < nc ∧ se = ee ∧ (chainModel Cα).key Q ⟨se, sh⟩ < (chainModel Cα).key Q ⟨ee, eh⟩
    then 1 else 0

theorem wBit_spec {Cα : Chain} {Q : Polygon} {nc se sh ee eh : ℕ} :
    wBit Cα Q nc se sh ee eh = 0 ∨
      (chainModel Cα).key Q ⟨se, sh⟩ < (chainModel Cα).key Q ⟨ee, eh⟩ := by
  unfold wBit; split_ifs with h
  · exact Or.inr h.2.2
  · exact Or.inl rfl

/-- The registers `cntS` writes. -/
def CsW (q : ℕ) : Prop := KeyW q ∨ q = 81100 ∨ q = 81104 ∨ (81110 ≤ q ∧ q ≤ 81113)

theorem cntS_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N)
    {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c.nreg 81133))
    (hC : ChainDescAt c₀.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W)
    (hse : c.nreg 81103 < c.nreg 81105) (hee : c.nreg 81107 < c.nreg 81105)
    (hNW : 2 * c.nreg 81105 ≤ E.W)
    (hpos : 0 < N.nChords → PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81103, c.nreg 81106⟩ ∧
      PosOK Cα (Qof E.P) E.P.n ⟨c.nreg 81107, c.nreg 81108⟩)
    (htW : c.nreg 81100 + 1 ≤ E.W)
    (hroom : c.nreg ALLOC + csK ≤ E.W) :
    FRS B E.P E.W c₀ cntS c csK (fun c' =>
      c'.nreg 81104 = arcCnt (c.nreg 81105) (c.nreg 81103) (c.nreg 81107) (c'.nreg 81110) ∧
      c'.nreg 81110 = wBit Cα (Qof E.P) N.nChords (c.nreg 81103) (c.nreg 81106) (c.nreg 81107)
        (c.nreg 81108) ∧
      c'.nreg 81100 = c.nreg 81100 + 1 ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ CsW q → c'.nreg q = c.nreg q) := by
  have k0 := k0_of hE hI
  have k1 : c.nreg 81012 = 1 := by rw [hI.hin _ (by unfold FFix; omega), hE.k1]
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  -- stage 1
  have ok1 : okB E.W c.nmem [.constN 81110 0, .loadN 81111 81134] c.nreg := by
    simp only [okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₂ := csK - 2) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
    (by simp [csK]) (fun _ h => h)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.constN 81110 0, .loadN 81111 81134] c.nreg q :=
    fun q => by rw [h₁]
  have v10 : c₁.nreg 81110 = 0 := by rw [e₁]; simp [regB, regI, upd]
  have v11 : c₁.nreg 81111 = N.nChords := by rw [e₁]; simp [regB, regI, upd]; exact hNA.1
  have f₁ : ∀ q, q ≠ 81110 → q ≠ 81111 → c₁.nreg q = c.nreg q := fun q h1 h2 => by
    rw [e₁]; simp [regB, regI, upd, h1, h2]
  have hA₁' : c₁.nreg ALLOC = c.nreg ALLOC := f₁ _ (by unfold ALLOC; omega) (by unfold ALLOC; omega)
  have r := fun q (h : 81100 ≤ q ∧ q ≤ 81109) => f₁ q (by omega) (by omega)
  have w33 : c₁.nreg 81133 = c.nreg 81133 := f₁ _ (by norm_num) (by norm_num)
  -- stage 2: the bit `w`
  have k0₁ := k0_of hE hI₁
  refine FRS.seq (K₁ := 11017) (K₂ := 18) (Q₁ := fun c' =>
      c'.nreg 81110 = wBit Cα (Qof E.P) N.nChords (c.nreg 81103) (c.nreg 81106) (c.nreg 81107)
        (c.nreg 81108) ∧
      ∀ q, 80000 ≤ q → q < 90000 → ¬ KeyW q → q ≠ 81110 → q ≠ 81112 → q ≠ 81113 →
        c'.nreg q = c₁.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨hw₂, f₂⟩ => ?_) |>.mono
    (by unfold csK; omega) (fun _ h => h)
  · by_cases a1 : c₁.nreg 81011 < c₁.nreg 81111
    swap
    · refine (FRS.ifF a1 (FRS.skip (K := 0) hI₁ ⟨?_, fun _ _ _ _ _ _ _ => rfl⟩)).mono
        (by omega) (fun _ h => h)
      rw [v10]; unfold wBit; rw [ite_eq_right (fun h => a1 (by rw [k0₁, v11]; exact h.1))]
    refine (FRS.ifT a1 ?_).mono (K := 11017) (by omega) (fun _ h => h)
    have hpos' := hpos (by rw [v11, k0₁] at a1; exact a1)
    by_cases e : c₁.nreg 81103 = c₁.nreg 81107
    swap
    · refine FRS.ifEq_ne hI₁ e ⟨?_, fun _ _ _ _ _ _ _ => rfl⟩
      rw [v10]; unfold wBit
      rw [ite_eq_right (fun h => e (by rw [r 81103 ⟨by norm_num, by norm_num⟩,
        r 81107 ⟨by norm_num, by norm_num⟩]; exact h.2.1))]
    refine FRS.ifEq_eq e ((FRS.seq (K₂ := 1) (cmpA_fs₀ hE hB hI₁ (r := 81112) (a := 81103) (b := 81106) (d := 81107) (e := 81108) ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ⟨by norm_num, by norm_num⟩ (by unfold KeyW; omega) (by unfold KeyW; omega)
      (by unfold KeyW; omega) (by unfold KeyW; omega) (by rw [w33]; exact hwf)
      (by rw [w33]; exact hC) hWm
      (by rw [r 81103 ⟨by norm_num, by norm_num⟩, r 81106 ⟨by norm_num, by norm_num⟩]; exact hpos'.1)
      (by rw [r 81107 ⟨by norm_num, by norm_num⟩, r 81108 ⟨by norm_num, by norm_num⟩]; exact hpos'.2)
      (by rw [hA₁']; unfold csK at hroom; omega)) (fun c' hI' _ ⟨b12, _, f'⟩ => ?_)).mono (by norm_num) (fun _ h => h))
    have okc : okB E.W c'.nmem [.copyN 81110 81112] c'.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine (FRS.block hB _ hI' okc).mono (by simp) (fun c'' h'' => ?_)
    have e' : ∀ q, c''.nreg q = regB c'.nmem [.copyN 81110 81112] c'.nreg q := fun q => by rw [h'']
    refine ⟨?_, fun q a b hk h1 h2 h3 => ?_⟩
    · rw [e']; simp only [regB, regI, upd, ite_true]
      have hb := b12
      rw [r 81103 ⟨by norm_num, by norm_num⟩, r 81106 ⟨by norm_num, by norm_num⟩,
        r 81107 ⟨by norm_num, by norm_num⟩, r 81108 ⟨by norm_num, by norm_num⟩] at hb
      have hpc : 0 < N.nChords := by rw [v11, k0₁] at a1; exact a1
      have he : c.nreg 81103 = c.nreg 81107 := by
        rw [r 81103 ⟨by norm_num, by norm_num⟩, r 81107 ⟨by norm_num, by norm_num⟩] at e; exact e
      unfold wBit
      by_cases hk : (chainModel Cα).key (Qof E.P) ⟨c.nreg 81103, c.nreg 81106⟩ <
          (chainModel Cα).key (Qof E.P) ⟨c.nreg 81107, c.nreg 81108⟩
      · rw [ite_eq_left ⟨hpc, he, hk⟩]; exact hb.2.2 hk
      · rw [ite_eq_right (fun h => hk h.2.2)]
        have := hb.1; have h2 : c'.nreg 81112 ≠ 1 := fun h => hk (hb.2.1 h); omega
    · rw [e']; simp only [regB, regI, upd, ite_eq_right h1]; exact f' q a b hk h2 h3
  -- stage 3 on: the count
  have r₂ : ∀ q, 81100 ≤ q → q ≤ 81109 → c₂.nreg q = c.nreg q := fun q a b => by
    rw [f₂ q (by omega) (by omega) (by unfold KeyW; omega) (by omega) (by omega) (by omega),
      f₁ q (by omega) (by omega)]
  have k1₂ : c₂.nreg 81012 = 1 := by rw [hI₂.hin _ (by unfold FFix; omega), hE.k1]
  have k0₂ := k0_of hE hI₂
  have x03 := r₂ 81103 (by norm_num) (by norm_num)
  have x05 := r₂ 81105 (by norm_num) (by norm_num)
  have x07 := r₂ 81107 (by norm_num) (by norm_num)
  have x00 := r₂ 81100 (by norm_num) (by norm_num)
  have ok3 : okB E.W c₂.nmem [.addN 81104 81107 81105, .subN 81104 81104 81103] c₂.nreg := by
    simp only [okB, okI, FScr, FOut, x05, x07]; norm_num; omega
  refine FRS.seq (K₂ := 16) (FRS.block hB _ hI₂ ok3) (fun c₃ hI₃ hA₃ h₃ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem [.addN 81104 81107 81105, .subN 81104 81104 81103]
      c₂.nreg q := fun q => by rw [h₃]
  have u04 : c₃.nreg 81104 = c.nreg 81107 + c.nreg 81105 - c.nreg 81103 := by
    rw [e₃]; simp [regB, regI, upd, x03, x05, x07]
  have f₃ : ∀ q, q ≠ 81104 → c₃.nreg q = c₂.nreg q := fun q h => by
    rw [e₃]; simp [regB, regI, upd, h]
  have u05 : c₃.nreg 81105 = c.nreg 81105 := by rw [f₃ _ (by norm_num), x05]
  -- the modulus
  refine FRS.seq (K₁ := 3) (K₂ := 13) (Q₁ := fun c' =>
      c'.nreg 81104 = (c.nreg 81107 + c.nreg 81105 - c.nreg 81103) % c.nreg 81105 ∧
      ∀ q, q ≠ 81104 → c'.nreg q = c₃.nreg q) ?_ (fun c₄ hI₄ hA₄ ⟨u04', f₄⟩ => ?_) |>.mono
    (by omega) (fun _ h => h)
  · by_cases a : c₃.nreg 81104 < c₃.nreg 81105
    · refine (FRS.ifT a (FRS.skip (K := 0) hI₃ ⟨?_, fun _ _ => rfl⟩)).mono (by omega)
        (fun _ h => h)
      rw [u04] at a ⊢; rw [u05] at a; rw [Nat.mod_eq_of_lt a]
    · have okm : okB E.W c₃.nmem [.subN 81104 81104 81105] c₃.nreg := by
        simp only [okB, okI, FScr, FOut]; norm_num
      refine (FRS.ifF a (FRS.block hB _ hI₃ okm)).mono (by simp) (fun c' h' => ?_)
      have e' : ∀ q, c'.nreg q = regB c₃.nmem [.subN 81104 81104 81105] c₃.nreg q :=
        fun q => by rw [h']
      refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
      rw [e']; simp only [regB, regI, upd, ite_true]
      rw [u04, u05] at *
      have h2 : c.nreg 81107 + c.nreg 81105 - c.nreg 81103 - c.nreg 81105 < c.nreg 81105 := by
        omega
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
  have hN0 : 0 < c.nreg 81105 := by omega
  have hml := Nat.mod_lt (c.nreg 81107 + c.nreg 81105 - c.nreg 81103) hN0
  have k1₄ : c₄.nreg 81012 = 1 := by rw [hI₄.hin _ (by unfold FFix; omega), hE.k1]
  have g4 : ∀ q, q ≠ 81104 → c₄.nreg q = c₂.nreg q := fun q h => by rw [f₄ q h, f₃ q h]
  have ok5 : okB E.W c₄.nmem [.addN 81104 81104 81012] c₄.nreg := by
    simp only [okB, okI, FScr, FOut, k1₄, u04']; norm_num; omega
  refine FRS.seq (K₂ := 12) (FRS.block hB _ hI₄ ok5) (fun c₅ hI₅ hA₅ h₅ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₅ : ∀ q, c₅.nreg q = regB c₄.nmem [.addN 81104 81104 81012] c₄.nreg q := fun q => by
    rw [h₅]
  have v₅ : c₅.nreg 81104 = (c.nreg 81107 + c.nreg 81105 - c.nreg 81103) % c.nreg 81105 + 1 := by
    rw [e₅]; simp [regB, regI, upd, k1₄, u04']
  have f₅ : ∀ q, q ≠ 81104 → c₅.nreg q = c₂.nreg q := fun q h => by
    rw [e₅]; simp [regB, regI, upd, h]; exact g4 q h
  have y03 : c₅.nreg 81103 = c.nreg 81103 := by rw [f₅ _ (by norm_num), x03]
  have y05 : c₅.nreg 81105 = c.nreg 81105 := by rw [f₅ _ (by norm_num), x05]
  have y07 : c₅.nreg 81107 = c.nreg 81107 := by rw [f₅ _ (by norm_num), x07]
  have y10 : c₅.nreg 81110 = c₂.nreg 81110 := f₅ _ (by norm_num)
  have k0₅ := k0_of hE hI₅
  refine FRS.seq (K₁ := 7) (K₂ := 5) (Q₁ := fun c' =>
      c'.nreg 81104 = arcCnt (c.nreg 81105) (c.nreg 81103) (c.nreg 81107) (c₂.nreg 81110) ∧
      ∀ q, q ≠ 81104 → c'.nreg q = c₅.nreg q) ?_ (fun c₆ hI₆ hA₆ ⟨v₆, f₆⟩ => ?_) |>.mono
    (by omega) (fun _ h => h)
  · unfold arcCnt
    by_cases e : c₅.nreg 81103 = c₅.nreg 81107
    · refine FRS.ifEq_eq (K := 3) e ?_
      rw [y03, y07] at e
      by_cases a : c₅.nreg 81011 < c₅.nreg 81110
      · refine (FRS.ifT a (FRS.skip (K := 0) hI₅ ⟨?_, fun _ _ => rfl⟩)).mono (by omega)
          (fun _ h => h)
        rw [v₅, ite_eq_right (by rw [k0₅, y10] at a; omega)]
      · have oka : okB E.W c₅.nmem [.addN 81104 81104 81105] c₅.nreg := by
          simp only [okB, okI, FScr, FOut, v₅, y05]; norm_num; omega
        refine (FRS.ifF a (FRS.block hB _ hI₅ oka)).mono (by simp) (fun c' h' => ?_)
        have e' : ∀ q, c'.nreg q = regB c₅.nmem [.addN 81104 81104 81105] c₅.nreg q :=
          fun q => by rw [h']
        refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]⟩
        rw [e']; simp only [regB, regI, upd, ite_true]
        rw [v₅, y05, ite_eq_left ⟨e, by rw [k0₅, y10] at a; omega⟩]
    · refine FRS.ifEq_ne (K := 3) hI₅ e ⟨?_, fun _ _ => rfl⟩
      rw [v₅, ite_eq_right (fun h => e (by rw [y03, y07]; exact h.1))]
  have k1₆ : c₆.nreg 81012 = 1 := by rw [hI₆.hin _ (by unfold FFix; omega), hE.k1]
  have z00 : c₆.nreg 81100 = c.nreg 81100 := by rw [f₆ _ (by norm_num), f₅ _ (by norm_num), x00]
  have ok7 : okB E.W c₆.nmem [.addN 81100 81100 81012] c₆.nreg := by
    simp only [okB, okI, FScr, FOut, k1₆, z00]; norm_num; omega
  refine (FRS.block hB _ hI₆ ok7).mono (by simp) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₆.nmem [.addN 81100 81100 81012] c₆.nreg q := fun q => by
    rw [h']
  have f' : ∀ q, q ≠ 81100 → c'.nreg q = c₆.nreg q := fun q hq => by
    rw [e']; simp [regB, regI, upd, hq]
  have w' : c'.nreg 81110 = c₂.nreg 81110 := by
    rw [f' _ (by norm_num), f₆ _ (by norm_num), y10]
  refine ⟨by rw [f' _ (by norm_num), v₆, w'], by rw [w']; exact hw₂, ?_, fun q a b hq => ?_⟩
  · rw [e']; simp [regB, regI, upd, k1₆, z00]
  · unfold CsW at hq
    rw [f' q (by omega), f₆ q (by omega), f₅ q (by omega),
      f₂ q a b (fun h => hq (Or.inl h)) (by omega) (by omega) (by omega), f₁ q (by omega) (by omega)]

/-- **A vertex step of the leaf**: test the host vertex of `v` (`81103`) if `v` is strictly inside
the stretch, then `v ← v + 1 mod N`, `cnt ← cnt - 1`. -/
def vStep (sT : Stmt) : Stmt :=
  .seq (.ifLtN 81131 81103 (.ifLtN 81103 81135
      (.seq (Stmt.block [.subN 81071 81103 81131, .addN 81071 81071 81130])
        (.seq (.ifLtN 81071 81017 .skip (Stmt.block [.subN 81071 81071 81017])) (vTest sT)))
      .skip) .skip)
    (.seq (Stmt.block [.addN 81103 81103 81012, .subN 81104 81104 81012])
      (.ifLtN 81103 81105 .skip (Stmt.block [.constN 81103 0])))

/-- The cost bound of `vStep`. -/
def vsK (E : FEnv) : ℕ := tvK E + 20

theorem vStep_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    (hv : c.nreg 81103 < c.nreg 81105) (hNW : 2 * c.nreg 81105 ≤ E.W)
    (hg : c.nreg 81130 < E.M.W.n) (hL : c.nreg 81135 - c.nreg 81131 ≤ E.M.W.n)
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + vsK E ≤ E.W) :
    FRS B E.P E.W c₀ (vStep E.sT) c (vsK E) (fun c' => FWin E c' ∧
      c'.nreg 81103 = (c.nreg 81103 + 1) % c.nreg 81105 ∧ c'.nreg 81104 = c.nreg 81104 - 1 ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81103 → q ≠ 81104 →
        c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) → ∀ σb, σb ≤ 1 →
          GoodAt E reg ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) σb →
          c'.nreg 81007 = 1)) := by
  have n17 : c.nreg 81017 = E.M.W.n := by rw [hI.hin _ (by unfold FFix; omega), hE.wn]
  have hn : 0 < E.M.W.n := by omega
  -- the test
  refine FRS.seq (K₁ := tvK E + 15) (K₂ := 5) (Q₁ := fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) → ∀ σb, σb ≤ 1 →
          GoodAt E reg ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) σb →
          c'.nreg 81007 = 1)) ?_ (fun c₁ hI₁ hA₁ ⟨hw₁, f₁, m₁, g₁⟩ => ?_) |>.mono
    (by unfold vsK; omega) (fun _ h => h)
  · by_cases a1 : c.nreg 81131 < c.nreg 81103
    swap
    · exact (FRS.ifF a1 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ _ => rfl, id,
        fun h => absurd h a1⟩)).mono (by omega) (fun _ h => h)
    refine (FRS.ifT a1 ?_).mono (K := tvK E + 15) le_rfl (fun _ h => h)
    by_cases a2 : c.nreg 81103 < c.nreg 81135
    swap
    · exact (FRS.ifF a2 (FRS.skip (K := 0) hI ⟨hw, fun _ _ _ _ _ => rfl, id,
        fun _ h => absurd h a2⟩)).mono (by omega) (fun _ h => h)
    refine (FRS.ifT a2 ?_).mono (K := tvK E + 13) le_rfl (fun _ h => h)
    have ok1 : okB E.W c.nmem [.subN 81071 81103 81131, .addN 81071 81071 81130] c.nreg := by
      simp only [okB, okI, regI, upd, FScr, FOut]; norm_num; omega
    refine FRS.seq (K₂ := tvK E + 9) (FRS.block hB _ hI ok1) (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono
      (by simp only [List.length_cons, List.length_nil]; omega) (fun _ h => h)
    simp only [List.length_cons, List.length_nil] at hA₁
    have e₁ : ∀ q, c₁.nreg q = regB c.nmem [.subN 81071 81103 81131, .addN 81071 81071 81130]
        c.nreg q := fun q => by rw [h₁]
    have v71 : c₁.nreg 81071 = c.nreg 81103 - c.nreg 81131 + c.nreg 81130 := by
      rw [e₁]; simp [regB, regI, upd]
    have f₁ : ∀ q, q ≠ 81071 → c₁.nreg q = c.nreg q := fun q h => by
      rw [e₁]; simp [regB, regI, upd, h]
    have n17₁ : c₁.nreg 81017 = E.M.W.n := by rw [f₁ _ (by norm_num), n17]
    have hlt : c.nreg 81103 - c.nreg 81131 + c.nreg 81130 < 2 * E.M.W.n := by omega
    refine FRS.seq (K₁ := 3) (K₂ := tvK E + 4) (Q₁ := fun c' =>
        c'.nreg 81071 = (c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n ∧
        ∀ q, q ≠ 81071 → c'.nreg q = c.nreg q) ?_ (fun c₂ hI₂ hA₂ ⟨v₂, f₂⟩ => ?_) |>.mono
      (by omega) (fun _ h => h)
    · by_cases a : c₁.nreg 81071 < c₁.nreg 81017
      · refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨?_, f₁⟩)).mono (by omega) (fun _ h => h)
        rw [v71, n17₁] at *
        rw [Nat.mod_eq_of_lt (by omega)]; ring
      · have okm : okB E.W c₁.nmem [.subN 81071 81071 81017] c₁.nreg := by
          simp only [okB, okI, FScr, FOut]; norm_num
        refine (FRS.ifF a (FRS.block hB _ hI₁ okm)).mono (by simp) (fun c' h' => ?_)
        have e' : ∀ q, c'.nreg q = regB c₁.nmem [.subN 81071 81071 81017] c₁.nreg q :=
          fun q => by rw [h']
        refine ⟨?_, fun q hq => by rw [e']; simp [regB, regI, upd, hq]; exact f₁ q hq⟩
        rw [e']; simp only [regB, regI, upd, ite_true]
        rw [v71, n17₁] at *
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega
    have hv2 : c₂.nreg 81071 < E.M.W.n := by rw [v₂]; exact Nat.mod_lt _ hn
    have hw₂ : FWin E c₂ := hw.congr' (fun q a b => f₂ q (by omega))
    refine (vTest_fs hE hB hBT hI₂ hw₂ hv2 (by unfold vsK at hroom; omega)).mono le_rfl
      (fun c' ⟨w', fr', m', g'⟩ => ⟨w', fun q a b h1 h2 => by rw [fr' q a b h1, f₂ q h2],
        fun h => m' (by rw [f₂ _ (by norm_num)]; exact h), fun _ _ reg hr hch hs σb hσb hg => ?_⟩)
    rw [v₂] at g'
    exact g' reg hr hch hs σb hσb hg
  -- the step
  have k1₁ : c₁.nreg 81012 = 1 := by rw [hI₁.hin _ (by unfold FFix; omega), hE.k1]
  have z03 := f₁ 81103 (by norm_num) (by norm_num) (by unfold VertW; omega) (by norm_num)
  have z04 := f₁ 81104 (by norm_num) (by norm_num) (by unfold VertW; omega) (by norm_num)
  have z05 := f₁ 81105 (by norm_num) (by norm_num) (by unfold VertW; omega) (by norm_num)
  have ok2 : okB E.W c₁.nmem [.addN 81103 81103 81012, .subN 81104 81104 81012] c₁.nreg := by
    simp only [okB, okI, FScr, FOut, k1₁, z03]; norm_num; omega
  refine FRS.seq (K₂ := 3) (FRS.block hB _ hI₁ ok2) (fun c₂ hI₂ hA₂ h₂ => ?_) |>.mono
    (by simp) (fun _ h => h)
  have e₂ : ∀ q, c₂.nreg q = regB c₁.nmem [.addN 81103 81103 81012, .subN 81104 81104 81012]
      c₁.nreg q := fun q => by rw [h₂]
  have v03 : c₂.nreg 81103 = c.nreg 81103 + 1 := by rw [e₂]; simp [regB, regI, upd, k1₁, z03]
  have v04 : c₂.nreg 81104 = c.nreg 81104 - 1 := by rw [e₂]; simp [regB, regI, upd, k1₁, z04]
  have f₂ : ∀ q, q ≠ 81103 → q ≠ 81104 → c₂.nreg q = c₁.nreg q := fun q h1 h2 => by
    rw [e₂]; simp [regB, regI, upd, h1, h2]
  have v05 : c₂.nreg 81105 = c.nreg 81105 := by rw [f₂ _ (by norm_num) (by norm_num), z05]
  have hw₂ : FWin E c₂ := hw₁.congr' (fun q a b => f₂ q (by omega) (by omega))
  have fin : ∀ c' : Config, (∀ q, q ≠ 81103 → c'.nreg q = c₂.nreg q) →
      c'.nreg 81103 = (c.nreg 81103 + 1) % c.nreg 81105 →
      FWin E c' ∧ c'.nreg 81103 = (c.nreg 81103 + 1) % c.nreg 81105 ∧
      c'.nreg 81104 = c.nreg 81104 - 1 ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ VertW q → q ≠ 81071 → q ≠ 81103 → q ≠ 81104 →
        c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      (c.nreg 81131 < c.nreg 81103 → c.nreg 81103 < c.nreg 81135 →
        ∀ reg, NFRegs E.M (Qof E.P) E.N reg → (E.N.region E.r).chords ≠ [] →
          VSet E ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) → ∀ σb, σb ≤ 1 →
          GoodAt E reg ((c.nreg 81130 + (c.nreg 81103 - c.nreg 81131)) % E.M.W.n) σb →
          c'.nreg 81007 = 1) := by
    intro c' hf h3
    have e07 : c'.nreg 81007 = c₁.nreg 81007 := by
      rw [hf _ (by norm_num), f₂ _ (by norm_num) (by norm_num)]
    refine ⟨hw₂.congr' (fun q a b => hf q (by omega)), h3, by rw [hf _ (by norm_num), v04],
      fun q a b h1 h2 h3 h4 => by rw [hf q h3, f₂ q h3 h4, f₁ q a b h1 h2], fun h => by
        rw [e07]; exact m₁ h, fun a b reg hr hch hs σb hσb hg => by
        rw [e07]; exact g₁ a b reg hr hch hs σb hσb hg⟩
  by_cases a : c₂.nreg 81103 < c₂.nreg 81105
  · refine (FRS.ifT a (FRS.skip (K := 0) hI₂ (fin c₂ (fun _ _ => rfl) ?_))).mono (by omega)
      (fun _ h => h)
    rw [v03] at a ⊢; rw [v05] at a; rw [Nat.mod_eq_of_lt a]
  · have okz : okB E.W c₂.nmem [.constN 81103 0] c₂.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine (FRS.ifF a (FRS.block hB _ hI₂ okz)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₂.nmem [.constN 81103 0] c₂.nreg q := fun q => by rw [h']
    refine fin c' (fun q hq => by rw [e']; simp [regB, regI, upd, hq]) ?_
    rw [e']; simp only [regB, regI, upd, ite_true]
    rw [v03, v05] at a
    rw [show c.nreg 81103 + 1 = c.nreg 81105 by omega, Nat.mod_self]

/-! ## The leaf loop -/

/-- The arc of index `t` of the region `r`. -/
def lj (N : NF) (r t : ℕ) : ℕ := (N.region r).arcs.getD t 0

/-- The count of the arc of index `t` of the region `r`. -/
noncomputable def lcnt (Cα : Chain) (Q : Polygon) (N : NF) (r nα t : ℕ) : ℕ :=
  arcCnt nα (N.arc (lj N r t)).s.edge (N.arc (lj N r t)).e.edge
    (wBit Cα Q N.nChords (N.arc (lj N r t)).s.edge (N.arc (lj N r t)).s.hgt
      (N.arc (lj N r t)).e.edge (N.arc (lj N r t)).e.hgt)

/-- The arc of index `t` covers `x₀` (for every admissible bit). -/
def Covered (Cα : Chain) (Q : Polygon) (N : NF) (r nα t x₀ : ℕ) : Prop :=
  ∀ w, (w = 0 ∨ (chainModel Cα).key Q (N.arc (lj N r t)).s <
      (chainModel Cα).key Q (N.arc (lj N r t)).e) →
    ∃ i, i < arcCnt nα (N.arc (lj N r t)).s.edge (N.arc (lj N r t)).e.edge w ∧
      ((N.arc (lj N r t)).s.edge + i) % nα = x₀

/-- A good vertex of the stretch for the leaf: strictly inside, with a good host candidate. -/
def LGood (E : FEnv) (g g' L x₀ : ℕ) : Prop :=
  g' < x₀ ∧ x₀ < g' + L ∧ ∃ reg, NFRegs E.M (Qof E.P) E.N reg ∧ (E.N.region E.r).chords ≠ [] ∧
    VSet E ((g + (x₀ - g')) % E.M.W.n) ∧ ∃ σb, σb ≤ 1 ∧
      GoodAt E reg ((g + (x₀ - g')) % E.M.W.n) σb

/-- The setup of the leaf. -/
def leafInitL : List Instr :=
  [.addN 81114 81134 81015, .loadN 81114 81114, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .loadN 81101 81114, .constN 81100 0, .constN 81104 0,
    .addN 81115 81133 81013, .loadN 81115 81115, .addN 81105 81115 81115,
    .addN 81105 81105 81016, .subN 81109 81101 81100]

/-- The loop guard: `cnt + (na - t)`. -/
def guardL : List Instr := [.subN 81109 81101 81100, .addN 81109 81109 81104]

/-- **The leaf.** -/
def leafS (sT : Stmt) : Stmt :=
  .seq (Stmt.block leafInitL) (.whileLtN 81011 81109
    (.seq (.ifLtN 81011 81104 (vStep sT) (.seq arcLoad cntS)) (Stmt.block guardL)))

/-- The cost of a loop body of the leaf. -/
def lbK (E : FEnv) : ℕ := vsK E + csK + 34

/-- The registers the leaf writes. -/
def LeafW (q : ℕ) : Prop := KeyW q ∨ VertW q ∨ q = 81071 ∨ (81100 ≤ q ∧ q ≤ 81115)

theorem arc_edges {Cα : Chain} {Q : Polygon} {N : NF} (hNF : IsNF (chainModel Cα) Q N) {j : ℕ}
    (hj : j < N.arcs.length) :
    (N.arc j).s.edge < (chainModel Cα).W.n ∧ (N.arc j).e.edge < (chainModel Cα).W.n := by
  obtain ⟨-, -, -, reg, -, -, harcs, -, -, -, hpp⟩ := hNF
  obtain ⟨hs, he⟩ := hpp j hj
  have harc := (harcs.1 j hj).2
  have h1 : ((N.arc j).s.edge : ℝ) < (chainModel Cα).W.n := by
    have := harc.2.1; have := hs.1
    show ((N.arc j).s.edge : ℝ) < _
    unfold Model.key at *; linarith
  have h2 : ((N.arc j).e.edge : ℝ) < (chainModel Cα).W.n := by
    have := harc.2.2.2.1; have := he.1
    unfold Model.key at *; linarith
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

theorem leafInit_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {N : NF} (hN : NFWithin c₀.nmem (c.nreg 81134) (c₀.nreg ALLOC) N)
    (hr : c.nreg 81121 < N.nRegions) {H : Host} {Cα : Chain}
    (hwf : ChainWF E.P (c₀.nreg ALLOC) c₀.nmem (c.nreg 81133))
    (hC : ChainDescAt c₀.nmem (c.nreg 81133) (Qof E.P) H Cα) (hWm : 2 * Cα.m + 7 ≤ E.W) :
    FRS B E.P E.W c₀ (Stmt.block leafInitL) c 15 (fun c' =>
      c'.nreg 81101 = (N.region (c.nreg 81121)).arcs.length ∧ c'.nreg 81100 = 0 ∧
      c'.nreg 81104 = 0 ∧ c'.nreg 81105 = 2 * Cα.m + 7 ∧
      c'.nreg 81109 = (N.region (c.nreg 81121)).arcs.length ∧
      ∀ q, q ≠ 81100 → q ≠ 81101 → q ≠ 81104 → q ≠ 81105 → q ≠ 81109 → q ≠ 81114 →
        q ≠ 81115 → c'.nreg q = c.nreg q) := by
  have hN' : NFWithin c.nmem (c.nreg 81134) (c₀.nreg ALLOC) N :=
    Robust.transport hN (fun a ha => hI.hm a ha)
  have hNA := hN'.nfAt
  obtain ⟨hB7, -, -, hrb, -, -⟩ := nf_bounds hN'
  obtain ⟨hC', hwf'⟩ := chain_keep hwf hC (fun a ha => hI.hm a ha) hI.hA
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hD5 := hwf.1
  have hrl : c.nreg 81121 < N.regions.length := hr
  obtain ⟨hna, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  have b1 := hrb _ hr
  have hm : c.nmem (c.nreg 81133 + 2) = Cα.m := hC'.2.2.2.1
  have k5 : c.nreg 81015 = 5 := by rw [hI.hin _ (by unfold FFix; omega), hE.k5]
  have k7 : c.nreg 81016 = 7 := by rw [hI.hin _ (by unfold FFix; omega), hE.k7]
  have k2 : c.nreg 81013 = 2 := by rw [hI.hin _ (by unfold FFix; omega), hE.k2]
  have e5 : c.nmem (c.nreg 81134 + 5) + c.nreg 81121 + c.nreg 81121 + c.nreg 81121 +
      c.nreg 81121 + c.nreg 81121 = c.nmem (c.nreg 81134 + 5) + 5 * c.nreg 81121 := by ring
  have ok : okB E.W c.nmem leafInitL c.nreg := by
    simp only [leafInitL, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k7, k2]
    norm_num
    try rw [e5]
    try rw [hm]
    (repeat' apply And.intro) <;> omega
  refine (FRS.block hB _ hI ok).mono (by simp [leafInitL]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem leafInitL c.nreg q := fun q => by rw [h']
  refine ⟨?_, ?_, ?_, ?_, ?_, fun q h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  · rw [e']; simp [leafInitL, regB, regI, upd, k5]; rw [e5]; exact hna
  · rw [e']; simp [leafInitL, regB, regI, upd]
  · rw [e']; simp [leafInitL, regB, regI, upd]
  · rw [e']; simp [leafInitL, regB, regI, upd, k2, k7, hm]; ring
  · rw [e']; simp [leafInitL, regB, regI, upd, k5]; rw [e5]; exact hna
  · rw [e', regB_other _ _ _ (fun i hi => ?_)]
    simp only [leafInitL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> simp only [dstI] <;> omega

/-- The total number of loop steps of the leaf. -/
noncomputable def lmu (Cα : Chain) (Q : Polygon) (N : NF) (r nα : ℕ) : ℕ :=
  ∑ t ∈ Finset.range (N.region r).arcs.length, (lcnt Cα Q N r nα t + 1)

/-- The remaining loop steps of the leaf in the configuration `d`. -/
noncomputable def lmuAt (Cα : Chain) (Q : Polygon) (N : NF) (r nα : ℕ) (d : Config) : ℕ :=
  d.nreg 81104 + ∑ t ∈ Finset.Ico (d.nreg 81100) (N.region r).arcs.length, (lcnt Cα Q N r nα t + 1)

theorem arcCnt_pos {N se ee w : ℕ} : 1 ≤ arcCnt N se ee w := by unfold arcCnt; omega

theorem arcCnt_le {N se ee w : ℕ} (hN : 0 < N) : arcCnt N se ee w ≤ 2 * N := by
  unfold arcCnt
  have := Nat.mod_lt (ee + N - se) hN
  split_ifs <;> omega

/-- **The invariant of the leaf loop** without the guard (from the leaf's start `c`). -/
def LInv0 (E : FEnv) (c : Config) (Cα : Chain) (Nα : NF) (r g g' L : ℕ) (d : Config) : Prop :=
  FWin E d ∧ (∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → d.nreg q = c.nreg q) ∧
  (c.nreg 81007 = 1 → d.nreg 81007 = 1) ∧
  d.nreg 81101 = (Nα.region r).arcs.length ∧ d.nreg 81105 = 2 * Cα.m + 7 ∧
  d.nreg 81100 ≤ (Nα.region r).arcs.length ∧
  (d.nreg 81100 = 0 → d.nreg 81104 = 0) ∧
  (0 < d.nreg 81100 →
    d.nreg 81104 ≤ lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (d.nreg 81100 - 1) ∧
    d.nreg 81103 = ((Nα.arc (lj Nα r (d.nreg 81100 - 1))).s.edge +
      (lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (d.nreg 81100 - 1) - d.nreg 81104)) %
        (2 * Cα.m + 7)) ∧
  (∀ t', (t' + 1 < d.nreg 81100 ∨ (t' + 1 = d.nreg 81100 ∧ d.nreg 81104 = 0)) →
    ∀ x₀, LGood E g g' L x₀ → Covered Cα (Qof E.P) Nα r (2 * Cα.m + 7) t' x₀ →
      d.nreg 81007 = 1) ∧
  (0 < d.nreg 81100 → ∀ x₀, LGood E g g' L x₀ → ∀ i,
    i < lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (d.nreg 81100 - 1) - d.nreg 81104 →
    ((Nα.arc (lj Nα r (d.nreg 81100 - 1))).s.edge + i) % (2 * Cα.m + 7) = x₀ →
      d.nreg 81007 = 1)

/-- **The invariant of the leaf loop.** -/
def LInv (E : FEnv) (c : Config) (Cα : Chain) (Nα : NF) (r g g' L : ℕ) (d : Config) : Prop :=
  LInv0 E c Cα Nα r g g' L d ∧
    d.nreg 81109 = d.nreg 81104 + ((Nα.region r).arcs.length - d.nreg 81100)

theorem LInv0.congr {cs d d' : Config} {Cα : Chain} {Nα : NF} {r g g' L : ℕ}
    (h : LInv0 E cs Cα Nα r g g' L d) (he : ∀ q, q ≠ 81109 → d'.nreg q = d.nreg q) :
    LInv0 E cs Cα Nα r g g' L d' := by
  obtain ⟨hw, fr, mo, l01, l05, l00, l0, lc, ldone, lcur⟩ := h
  have e00 := he 81100 (by norm_num)
  have e01 := he 81101 (by norm_num)
  have e03 := he 81103 (by norm_num)
  have e04 := he 81104 (by norm_num)
  have e05 := he 81105 (by norm_num)
  have e07 := he 81007 (by norm_num)
  refine ⟨hw.congr' (fun q a b => he q (by omega)), fun q a b hq => by
    rw [he q (fun e => hq (Or.inr (Or.inr (Or.inr (by omega))))), fr q a b hq],
    fun h => by rw [e07]; exact mo h, by rw [e01]; exact l01, by rw [e05]; exact l05,
    by rw [e00]; exact l00, by rw [e00, e04]; exact l0, by rw [e00, e04, e03]; exact lc,
    by rw [e00, e04, e07]; exact ldone, by rw [e00, e04, e07]; exact lcur⟩

/-- The guard keeps the invariant. -/
theorem guard_fs {B : Finset ℕ} (hB : dBands ⊆ B) {cs : Config} {Cα : Chain} {Nα : NF}
    {r g g' L : ℕ} (hI : FInv E.W c₀ c) (h : LInv0 E cs Cα Nα r g g' L c)
    (hW : c.nreg 81104 + (Nα.region r).arcs.length ≤ E.W) :
    FRS B E.P E.W c₀ (Stmt.block guardL) c 2 (fun c' => LInv E cs Cα Nα r g g' L c' ∧
      lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c' = lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c) := by
  have l01 := h.2.2.2.1
  have ok : okB E.W c.nmem guardL c.nreg := by
    simp only [guardL, okB, okI, regI, upd, FScr, FOut]; norm_num; omega
  refine (FRS.block hB _ hI ok).mono (by simp [guardL]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c.nmem guardL c.nreg q := fun q => by rw [h']
  have f' : ∀ q, q ≠ 81109 → c'.nreg q = c.nreg q := fun q hq => by
    rw [e']; simp [guardL, regB, regI, upd, hq]
  refine ⟨⟨h.congr f', ?_⟩, ?_⟩
  · rw [f' 81104 (by norm_num), f' 81100 (by norm_num), e']
    simp [guardL, regB, regI, upd, l01]; omega
  · unfold lmuAt; rw [f' _ (by norm_num), f' _ (by norm_num)]

/-- The body of the leaf loop. -/
def leafBody (sT : Stmt) : Stmt :=
  .seq (.ifLtN 81011 81104 (vStep sT) (.seq arcLoad cntS)) (Stmt.block guardL)

/-- **One step of the leaf loop** keeps the invariant and decreases the remaining steps. -/
theorem leaf_body (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) {cs : Config}
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs cs g g' L Dα Bα) {r : ℕ}
    (hr : cs.nreg 81121 = r) (hrn : r < Nα.nRegions) (hnW : 2 * E.M.W.n ≤ E.W)
    (h2α : 2 * (2 * Cα.m + 7) ≤ E.W)
    (hWa : 2 * (2 * Cα.m + 7) + (Nα.region r).arcs.length ≤ E.W)
    (hI : FInv E.W c₀ c) (hL : LInv E cs Cα Nα r g g' L c) (hg : c.nreg 81011 < c.nreg 81109)
    (hroom : c.nreg ALLOC + lbK E ≤ E.W) :
    FRS B E.P E.W c₀ (leafBody E.sT) c (lbK E) (fun c' => LInv E cs Cα Nα r g g' L c' ∧
      lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c' < lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c) := by
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  obtain ⟨⟨hw, fr, mo, l01, l05, l00, l0, lc, ldone, lcur⟩, l09⟩ := hL
  have hS := hP.hS
  have hsimp : Cα.P.Simple := by rw [hP.hQ]; exact (shearInvariance (epsOf E.P) E.P).1 hE.hG.1
  have hNα := hP.hNα
  have hnα : (chainModel Cα).W.n = 2 * Cα.m + 7 := Stretch.nα Cα
  obtain ⟨-, -, -, regα, -, -, harcs, -, -, -, -⟩ := id hNα
  have hj : ∀ t, t < (Nα.region r).arcs.length → lj Nα r t < Nα.arcs.length := fun t ht =>
    ((harcs.2.2.2 r hrn (lj Nα r t)).1 (by
      unfold lj; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]
      exact List.getElem_mem ht)).1
  have k0 := k0_of hE hI
  have nl : ∀ q, ¬ (81100 ≤ q ∧ q ≤ 81115) → q ≠ 81071 → ¬ VertW q → ¬ KeyW q → ¬ LeafW q :=
    fun q a b d e h => by
      rcases h with h | h | h | h
      · exact e h
      · exact d h
      · exact b h
      · exact a h
  have rg : ∀ q, 81116 ≤ q → q < 82000 → c.nreg q = cs.nreg q := fun q a b =>
    fr q (by omega) (by omega) (nl q (by omega) (by omega) (by unfold VertW; omega)
      (by unfold KeyW; omega))
  have x30 : c.nreg 81130 = g := by rw [rg _ (by norm_num) (by norm_num), r30]
  have x31 : c.nreg 81131 = g' := by rw [rg _ (by norm_num) (by norm_num), r31]
  have x33 : c.nreg 81133 = Dα := by rw [rg _ (by norm_num) (by norm_num), r33]
  have x34 : c.nreg 81134 = Bα := by rw [rg _ (by norm_num) (by norm_num), r34]
  have x35 : c.nreg 81135 = g' + L := by rw [rg _ (by norm_num) (by norm_num), r35]
  have x21 : c.nreg 81121 = r := by rw [rg _ (by norm_num) (by norm_num), hr]
  have hna : (Nα.region r).arcs.length ≤ E.W := by rw [← l01]; exact hI.hw.1 81101
  refine FRS.seq (K₁ := vsK E + csK + 32) (K₂ := 2) (Q₁ := fun d =>
      LInv0 E cs Cα Nα r g g' L d ∧ d.nreg 81104 ≤ 2 * (2 * Cα.m + 7) ∧
      lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) d < lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c) ?_
    (fun d hId _ ⟨h0, hb, hμ⟩ => (guard_fs hB hId h0 (by omega)).mono le_rfl
      (fun d' ⟨h1, h2⟩ => ⟨h1, h2 ▸ hμ⟩)) |>.mono (by unfold lbK; omega) (fun _ h => h)
  by_cases hcnt : c.nreg 81011 < c.nreg 81104
  · -- a vertex step
    have hc0 : 0 < c.nreg 81104 := by rw [k0] at hcnt; exact hcnt
    have ht0 : 0 < c.nreg 81100 := by
      by_contra h; have := l0 (by omega); omega
    obtain ⟨lcle, lv⟩ := lc ht0
    have hnα0 : 0 < 2 * Cα.m + 7 := by omega
    have hv : c.nreg 81103 < c.nreg 81105 := by rw [lv, l05]; exact Nat.mod_lt _ hnα0
    refine (FRS.ifT hcnt (vStep_fs hE hB hBT hI hw hv (by rw [l05]; exact h2α)
      (by rw [x30]; exact hS.hg) (by rw [x35, x31]; have := hS.hLn; omega) hnW
      (by unfold lbK at hroom; omega))).mono (by omega)
      (fun c₂ ⟨w₂, v₂, n₂, f₂, m₂, g₂⟩ => ?_)
    have fq : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₂.nreg q = c.nreg q := fun q a b hq =>
      f₂ q a b (fun h => hq (Or.inr (Or.inl h))) (fun h => hq (Or.inr (Or.inr (Or.inl h))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega))))) 
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
    have y00 : c₂.nreg 81100 = c.nreg 81100 := f₂ _ (by norm_num) (by norm_num)
      (by unfold VertW; omega) (by norm_num) (by norm_num) (by norm_num)
    have y01 : c₂.nreg 81101 = c.nreg 81101 := f₂ _ (by norm_num) (by norm_num)
      (by unfold VertW; omega) (by norm_num) (by norm_num) (by norm_num)
    have y05 : c₂.nreg 81105 = c.nreg 81105 := f₂ _ (by norm_num) (by norm_num)
      (by unfold VertW; omega) (by norm_num) (by norm_num) (by norm_num)
    rw [l05] at v₂
    have cur' : ∀ x₀, LGood E g g' L x₀ → ∀ i,
        i < lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (c.nreg 81100 - 1) - c₂.nreg 81104 →
        ((Nα.arc (lj Nα r (c.nreg 81100 - 1))).s.edge + i) % (2 * Cα.m + 7) = x₀ →
          c₂.nreg 81007 = 1 := by
      intro x₀ hx i hi he
      rw [n₂] at hi
      by_cases hlt : i < lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (c.nreg 81100 - 1) - c.nreg 81104
      · exact m₂ (lcur ht0 x₀ hx i hlt he)
      · have hieq : i = lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (c.nreg 81100 - 1) - c.nreg 81104 := by
          omega
        rw [hieq, ← lv] at he
        subst he
        obtain ⟨a, b, reg, hreg, hch, hvs, σb, hσb, hgd⟩ := hx
        rw [x30, x31, x35] at g₂
        exact g₂ a b reg hreg hch hvs σb hσb hgd
    refine ⟨⟨w₂, fun q a b hq => by rw [fq q a b hq, fr q a b hq], fun h => m₂ (mo h),
      by rw [y01, l01], by rw [y05, l05], by rw [y00]; exact l00, fun h => by omega,
      fun _ => ⟨by rw [n₂, y00]; omega, ?_⟩, ?_, fun _ => by rw [y00]; exact cur'⟩, ?_, ?_⟩
    · rw [v₂, lv, y00, n₂, Nat.mod_add_mod]
      congr 1; omega
    · intro t' ht' x₀ hx hcov
      rw [y00] at ht'
      rcases ht' with h | ⟨h, h0⟩
      · exact m₂ (ldone t' (Or.inl h) x₀ hx hcov)
      · obtain ⟨i, hi, he⟩ := hcov _ wBit_spec
        rw [show t' = c.nreg 81100 - 1 by omega] at hi he
        exact cur' x₀ hx i (by rw [h0]; exact hi) he
    · rw [n₂]; have := arcCnt_le (N := 2 * Cα.m + 7) (se := (Nα.arc (lj Nα r (c.nreg 81100 - 1))).s.edge)
        (ee := (Nα.arc (lj Nα r (c.nreg 81100 - 1))).e.edge)
        (w := wBit Cα (Qof E.P) Nα.nChords (Nα.arc (lj Nα r (c.nreg 81100 - 1))).s.edge
          (Nα.arc (lj Nα r (c.nreg 81100 - 1))).s.hgt (Nα.arc (lj Nα r (c.nreg 81100 - 1))).e.edge
          (Nα.arc (lj Nα r (c.nreg 81100 - 1))).e.hgt) hnα0
      unfold lcnt at lcle; omega
    · unfold lmuAt; rw [n₂, y00]; omega
  · -- an arc step
    have hc0 : c.nreg 81104 = 0 := by rw [k0] at hcnt; omega
    have htn : c.nreg 81100 < (Nα.region r).arcs.length := by
      rw [k0, l09, hc0] at hg; omega
    have hjt := hj _ htn
    obtain ⟨ese, eee⟩ := arc_edges hNα hjt
    rw [hnα] at ese eee
    refine (FRS.ifF hcnt (FRS.seq (K₂ := csK) (arcLoad_fs hE hB hI (N := Nα)
      (by rw [x34]; exact hP.hNW) (by rw [x21]; exact hrn) (by rw [x21]; exact htn)
      (by rw [x21]; exact hjt)) (fun c₂ hI₂ hA₂ ⟨a02, a03, a06, a07, a08, af⟩ => ?_))).mono
      (by unfold vsK; omega) (fun _ h => h)
    rw [x21] at a02 a03 a06 a07 a08
    have af' : ∀ q, 81116 ≤ q → c₂.nreg q = c.nreg q := fun q a => af q (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
    have z05 : c₂.nreg 81105 = 2 * Cα.m + 7 := by
      rw [af _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num), l05]
    have z00 : c₂.nreg 81100 = c.nreg 81100 := af _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have hne : 0 < Nα.nChords → (Nα.F (chainModel Cα) (Qof E.P)).Nonempty := fun h =>
      ⟨_, _, Dec.chord_mem h, rfl⟩
    refine (cntS_fs hE hB hI₂ (N := Nα) (by rw [af' _ (by norm_num), x34]; exact hP.hNW)
      (by rw [af' _ (by norm_num), x33]; exact hP.hwf)
      (by rw [af' _ (by norm_num), x33]; exact hP.hD) hP.hWm (by rw [a03, z05]; exact ese) (by rw [a07, z05]; exact eee)
      (by rw [z05]; exact h2α)
      (fun h => by rw [a03, a06, a07, a08]; exact arc_posOK hsimp hNα (hne h) hjt)
      (by rw [z00]; omega) (by unfold lbK at hroom; omega)).mono le_rfl
      (fun c₃ ⟨b04, b10, b00, bf⟩ => ?_)
    have bf' : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₃.nreg q = c.nreg q := fun q a b hq => by
      have h1 : ¬ CsW q := fun h => by
        rcases h with h | h | h | h
        · exact hq (Or.inl h)
        all_goals exact hq (Or.inr (Or.inr (Or.inr (by omega))))
      rw [bf q (by omega) (by omega) h1, af q (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))]
    have nCs : ∀ q, (q = 81007 ∨ q = 81008 ∨ q = 81009 ∨ q = 81010 ∨ q = 81101 ∨ q = 81103 ∨
        q = 81105) → c₃.nreg q = c₂.nreg q := fun q hq =>
      bf q (by omega) (by omega) (by unfold CsW KeyW; omega)
    have c07 : c₃.nreg 81007 = c.nreg 81007 := by
      rw [nCs _ (by omega), af _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)]
    have hw₃ : FWin E c₃ := hw.congr' (fun q a b => by
      rw [nCs q (by omega), af q (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega)])
    have hlc : c₃.nreg 81104 = lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (c.nreg 81100) := by
      rw [b04, b10, a03, a06, a07, a08, z05]; rfl
    have hv3 : c₃.nreg 81103 = (Nα.arc (lj Nα r (c.nreg 81100))).s.edge := by
      rw [nCs _ (by omega), a03]; rfl
    rw [z00] at b00
    have hlpos : 1 ≤ lcnt Cα (Qof E.P) Nα r (2 * Cα.m + 7) (c.nreg 81100) := arcCnt_pos
    refine ⟨⟨hw₃, fun q a b hq => by rw [bf' q a b hq, fr q a b hq], fun h => by
      rw [c07]; exact mo h, by rw [nCs _ (by omega), af _ (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num), l01],
      by rw [nCs _ (by omega), z05], by rw [b00]; omega, fun h => by omega,
      fun _ => ⟨by rw [b00, hlc]; simp, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · rw [b00, hlc, hv3, Nat.add_sub_cancel, Nat.sub_self, Nat.add_zero,
        Nat.mod_eq_of_lt ese]
    · intro t' ht' x₀ hx hcov
      rw [b00, hlc] at ht'
      rw [c07]
      rcases ht' with h | ⟨h, h0⟩
      · rcases Nat.lt_or_ge (t' + 1) (c.nreg 81100) with h' | h'
        · exact ldone t' (Or.inl h') x₀ hx hcov
        · exact ldone t' (Or.inr ⟨by omega, hc0⟩) x₀ hx hcov
      · omega
    · intro _ x₀ _ i hi
      rw [b00, hlc] at hi
      simp at hi
    · rw [hlc]; unfold lcnt; exact arcCnt_le (by omega)
    · unfold lmuAt
      rw [b00, hlc, hc0, Finset.sum_eq_sum_Ico_succ_bot htn]
      omega

/-- **The leaf**: every good vertex of the stretch covered by an arc of the leaf region sets the
success flag. -/
theorem leaf_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c)
    {Cα : Chain} {Hα : Host} {Nα : NF} {g g' L Dα Bα : ℕ}
    (hP : PCtx E c₀ Cα Hα Nα g g' L Dα Bα) (hR : SRegs c g g' L Dα Bα) {r : ℕ}
    (hr : c.nreg 81121 = r) (hrn : r < Nα.nRegions) (hnW : 2 * E.M.W.n ≤ E.W)
    (h2α : 2 * (2 * Cα.m + 7) ≤ E.W)
    (hWa : 2 * (2 * Cα.m + 7) + (Nα.region r).arcs.length ≤ E.W)
    (hroom : c.nreg ALLOC + 15 + (lbK E + 2) * lmu Cα (Qof E.P) Nα r (2 * Cα.m + 7) ≤ E.W) :
    FRS B E.P E.W c₀ (leafS E.sT) c
      (15 + ((lbK E + 2) * lmu Cα (Qof E.P) Nα r (2 * Cα.m + 7) + 2)) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∀ t', t' < (Nα.region r).arcs.length → ∀ x₀, LGood E g g' L x₀ →
        Covered Cα (Qof E.P) Nα r (2 * Cα.m + 7) t' x₀ → c'.nreg 81007 = 1) := by
  have hR' := hR
  obtain ⟨r30, r31, r32, r33, r34, r35⟩ := hR
  refine FRS.seq (K₁ := 15) (leafInit_fs hE hB hI (N := Nα) (by rw [r34]; exact hP.hNW)
    (by rw [hr]; exact hrn) (by rw [r33]; exact hP.hwf) (by rw [r33]; exact hP.hD) hP.hWm)
    (fun c₁ hI₁ hA₁ ⟨i01, i00, i04, i05, i09, fi⟩ => ?_)
  rw [hr] at i01 i09
  have fr₁ : ∀ q, 81011 ≤ q → q < 83000 → ¬ LeafW q → c₁.nreg q = c.nreg q := fun q a b hq =>
    fi q (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
      (fun h => hq (Or.inr (Or.inr (Or.inr (by omega)))))
  have e07 : c₁.nreg 81007 = c.nreg 81007 := fi _ (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hL₁ : LInv E c Cα Nα r g g' L c₁ := by
    refine ⟨⟨hw.congr' (fun q a b => fi q (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega)), fr₁, fun h => by rw [e07]; exact h, i01, i05,
      by rw [i00]; omega, fun _ => i04, fun h => by omega, fun t' h => by omega,
      fun h => by omega⟩, by rw [i09, i04, i00]; simp⟩
  have hμ₁ : lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7) c₁ = lmu Cα (Qof E.P) Nα r (2 * Cα.m + 7) := by
    unfold lmuAt lmu; rw [i04, i00, Finset.range_eq_Ico]; simp
  have k0 := k0_of hE hI₁
  refine (FRS.while (a := 81011) (b := 81109) (body := leafBody E.sT) (LInv E c Cα Nα r g g' L)
    (lmuAt Cα (Qof E.P) Nα r (2 * Cα.m + 7)) (lbK E) (fun d hd hgd => ?_)
    (fun d hId hd hgd hroomd => leaf_body hE hB hBT hP hR' hr hrn hnW h2α hWa hId hd hgd hroomd)
    hI₁ hL₁ (by rw [hμ₁]; omega)).mono (by rw [hμ₁]) (fun c' ⟨hL', hex⟩ => ?_)
  · obtain ⟨⟨-, -, -, -, -, l00, -, -, -, -⟩, l09⟩ := hd
    unfold lmuAt
    by_cases hc : 0 < d.nreg 81104
    · omega
    · have htn : d.nreg 81100 < (Nα.region r).arcs.length := by omega
      rw [Finset.sum_eq_sum_Ico_succ_bot htn]
      omega
  · obtain ⟨⟨hw', fr', mo', l01, l05, l00, l0, lc, ldone, lcur⟩, l09⟩ := hL'
    have z11 : c'.nreg 81011 = 0 := by
      rw [fr' _ (by norm_num) (by norm_num) (by unfold LeafW KeyW VertW; omega)]
      exact k0_of hE hI
    refine ⟨hw', fr', mo', fun t' ht' x₀ hx hcov => ldone t' ?_ x₀ hx hcov⟩
    rw [z11] at hex
    omega

end

end Restore

end Chazelle.Core
