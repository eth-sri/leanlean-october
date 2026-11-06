module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFPair

/-!
# WP-E, the search on the RAM (`FindOK`), part 26: the run of an ordered pair of arcs

For the pair `(i, j)` (`81030`, `81031`) of arcs of region `r`: read the ends of arc `i` and the
start of arc `j` (the target, `81140`, `81141`), normalise the ends of arc `i`, cut arc `i` with
the cutter, and run the piece loop over its list (rebased after the cutter's allocations).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

variable {E : FEnv} {c₀ c : Config}

/-- **A call with a frame**: the search's registers (band `bRestore`) survive any call whose bands
avoid `bRestore`. -/
theorem FRS.callF {B : Finset ℕ} {P : Polygon} {W : ℕ} {s : Stmt} {B' : Finset ℕ}
    {Pre : Polygon → ℕ → Config → Prop} {Post : Polygon → Config → Config → Prop}
    {cost : Polygon → Config → ℕ}
    (hs : Meets s B' Pre Post cost) (hB : B' ⊆ B) (hI : FInv W c₀ c) (hpre : Pre P W c)
    (hroom : c.nreg ALLOC + cost P c ≤ W) (h8 : bRestore ∉ B') :
    FRS B P W c₀ s c (cost P c) (fun c' => Post P c c' ∧ c.nreg ALLOC ≤ c'.nreg ALLOC ∧
      (∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) ∧
      ∀ r, bandOf r ∉ B' → r ≠ ALLOC → c'.nreg r = c.nreg r) := by
  obtain ⟨c', k, ex, hk, hpost, hfr⟩ := hs P W c hI.hw hpre hroom
  have hp : ∀ q, FFix q → c'.nreg q = c.nreg q := fun q hq => hfr.1 q (by
      grind [bandOf, bRestore, FFix]) (by omega_nf)
  exact ⟨c', k, ex, hk, ⟨ex.wb_right, fun q hq => (hp q hq).trans (hI.hin q hq),
    le_trans hI.hA hfr.2.2.2.2.2.1,
    fun a ha => (hfr.2.2.1 a (lt_of_lt_of_le ha hI.hA)).trans (hI.hm a ha)⟩,
    (RF.of_frame hfr hI.hA).mono hB le_rfl, hpost, hfr.2.2.2.2.2.1, hfr.2.2.1, hfr.1⟩

/-- Arc `t` of region `r`. -/
def arcOf (N : NF) (r t : ℕ) : ARec := N.arc ((N.region r).arcs.getD t 0)

/-- **The facts about arc `t` of region `r`** the pair run needs (from the normal form). -/
structure ArcOK (E : FEnv) (t : ℕ) : Prop where
  ht : t < (E.N.region E.r).arcs.length
  hj : (E.N.region E.r).arcs.getD t 0 < E.N.arcs.length
  se : (arcOf E.N E.r t).s.edge < E.M.W.n
  ee : (arcOf E.N E.r t).e.edge < E.M.W.n
  sp : ProperPos E.M (Qof E.P) E.P.n (arcOf E.N E.r t).s
  ep : ProperPos E.M (Qof E.P) E.P.n (arcOf E.N E.r t).e
  sy : ∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) (arcOf E.N E.r t).s).2| < C.radius
  ey : ∀ C : Chain, E.M = chainModel C → |(E.M.pos (Qof E.P) (arcOf E.N E.r t).e).2| < C.radius
  sI : (normOf E.M (Qof E.P) (arcOf E.N E.r t).s).hgt = 0 ∨
    E.M.InnerPt (E.M.pos (Qof E.P) (arcOf E.N E.r t).s)
  eI : (normOf E.M (Qof E.P) (arcOf E.N E.r t).e).hgt = 0 ∨
    E.M.InnerPt (E.M.pos (Qof E.P) (arcOf E.N E.r t).e)
  wt : E.M.arcWt (E.M.key (Qof E.P) (arcOf E.N E.r t).s) (E.M.key (Qof E.P) (arcOf E.N E.r t).e)
    ≤ E.γ

/-! ## The reads -/

def prL1 : List Instr := [.copyN 81134 81001, .copyN 81121 81002, .copyN 81100 81030]
def prL2 : List Instr := [.copyN 81035 81103, .copyN 81036 81106, .copyN 81037 81107,
  .copyN 81038 81108, .copyN 81100 81031]
def prL3 : List Instr := [.copyN 81140 81103, .copyN 81141 81106]

/-- **The reads** of the pair: the ends of arc `i` in `81035 … 81038`, the start of arc `j` in
`81140`, `81141`. -/
def prReads : Stmt := .seq (Stmt.block prL1) (.seq arcLoad (.seq (Stmt.block prL2)
  (.seq arcLoad (Stmt.block prL3))))

/-- The registers the reads write. -/
def RdW (q : ℕ) : Prop :=
  LeafW q ∨ (81035 ≤ q ∧ q ≤ 81038) ∨ q = 81121 ∨ q = 81134 ∨ q = 81140 ∨ q = 81141

theorem prReads_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c)
    {i j : ℕ} (hi : c.nreg 81030 = i) (hj : c.nreg 81031 = j) (hAi : ArcOK E i)
    (hAj : ArcOK E j) :
    FRS B E.P E.W c₀ prReads c 70 (fun c' =>
      c'.nreg 81035 = (arcOf E.N E.r i).s.edge ∧ c'.nreg 81036 = (arcOf E.N E.r i).s.hgt ∧
      c'.nreg 81037 = (arcOf E.N E.r i).e.edge ∧ c'.nreg 81038 = (arcOf E.N E.r i).e.hgt ∧
      c'.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c'.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
      ∀ q, ¬ RdW q → c'.nreg q = c.nreg q) := by
  have hN : NFWithin c₀.nmem E.NH (c₀.nreg ALLOC) E.N := by rw [hE.m0, hE.a0]; exact hE.hNW
  have e01 : c.nreg 81001 = E.NH := by rw [hI.hin _ (by omega_nf), hE.i1]
  have e02 : c.nreg 81002 = E.r := by rw [hI.hin _ (by omega_nf), hE.i2]
  have ok1 : okB E.W c.nmem prL1 c.nreg := by
    simp only [prL1, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₁ := 3) (K₂ := 67) (FRS.block hB _ hI ok1) (fun c₁ hI₁ _ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem prL1 c.nreg q := fun q => by rw [h₁]
  have v34 : c₁.nreg 81134 = E.NH := by aesop
  have v21 : c₁.nreg 81121 = E.r := by aesop
  have v00 : c₁.nreg 81100 = i := by aesop
  have f₁ : ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81100 → c₁.nreg q = c.nreg q := fun q a b d => by
    rw [e₁]; simp [prL1, regB, regI, upd, a, b, d]
  refine FRS.seq (K₁ := 30) (K₂ := 37) (arcLoad_fs hE hB hI₁ (N := E.N) (by simp_all)
    (by rw [v21]; exact hE.hr) (by rw [v21, v00]; exact hAi.ht) (by rw [v21, v00]; exact hAi.hj))
    (fun c₂ hI₂ _ h₂ => ?_)
  obtain ⟨-, a03, a06, a07, a08, f₂⟩ := h₂
  rw [v21, v00] at a03 a06 a07 a08
  have j₂ : c₂.nreg 81031 = j := by
    rw [f₂ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num), f₁ _ (by norm_num) (by norm_num) (by norm_num), hj]
  have ok2 : okB E.W c₂.nmem prL2 c₂.nreg := by
    simp only [prL2, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₁ := 5) (K₂ := 32) (FRS.block hB _ hI₂ ok2) (fun c₃ hI₃ _ h₃ => ?_)
  have e₃ : ∀ q, c₃.nreg q = regB c₂.nmem prL2 c₂.nreg q := fun q => by rw [h₃]
  have v35 : c₃.nreg 81035 = (arcOf E.N E.r i).s.edge := by
    rw [e₃]; simp [prL2, regB, regI, upd]; rw [a03]; rfl
  have v36 : c₃.nreg 81036 = (arcOf E.N E.r i).s.hgt := by
    rw [e₃]; simp [prL2, regB, regI, upd]; rw [a06]; rfl
  have v37 : c₃.nreg 81037 = (arcOf E.N E.r i).e.edge := by
    rw [e₃]; simp [prL2, regB, regI, upd]; rw [a07]; rfl
  have v38 : c₃.nreg 81038 = (arcOf E.N E.r i).e.hgt := by
    rw [e₃]; simp [prL2, regB, regI, upd]; rw [a08]; rfl
  have w00 : c₃.nreg 81100 = j := by rw [e₃]; simp [prL2, regB, regI, upd, j₂]
  have f₃ : ∀ q, ¬ (81035 ≤ q ∧ q ≤ 81038) → q ≠ 81100 → c₃.nreg q = c₂.nreg q := fun q a b => by
    rw [e₃]; simp [prL2, regB, regI, upd, b, show q ≠ 81035 by omega, show q ≠ 81036 by omega,
      show q ≠ 81037 by omega, show q ≠ 81038 by omega]
  have w34 : c₃.nreg 81134 = E.NH := by
    rw [f₃ _ (by omega) (by norm_num), f₂ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), v34]
  have w21 : c₃.nreg 81121 = E.r := by
    rw [f₃ _ (by omega) (by norm_num), f₂ _ (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num), v21]
  refine FRS.seq (K₁ := 30) (K₂ := 2) (arcLoad_fs hE hB hI₃ (N := E.N) (by rw [w34]; exact hN)
    (by rw [w21]; exact hE.hr) (by rw [w21, w00]; exact hAj.ht) (by rw [w21, w00]; exact hAj.hj))
    (fun c₄ hI₄ _ h₄ => ?_)
  obtain ⟨-, b03, b06, -, -, f₄⟩ := h₄
  rw [w21, w00] at b03 b06
  have ok3 : okB E.W c₄.nmem prL3 c₄.nreg := by
    simp only [prL3, okB, okI, FScr, FOut]; norm_num
  refine (FRS.block hB _ hI₄ ok3).mono (by simp [prL3]) (fun c' h' => ?_)
  have e' : ∀ q, c'.nreg q = regB c₄.nmem prL3 c₄.nreg q := fun q => by rw [h']
  have f' : ∀ q, q ≠ 81140 → q ≠ 81141 → c'.nreg q = c₄.nreg q := fun q a b => by
    rw [e']; simp [prL3, regB, regI, upd, a, b]
  have g4 : ∀ q, ¬ LeafW q → q ≠ 81140 → q ≠ 81141 → c'.nreg q = c₃.nreg q := fun q h a b => by
    rw [f' q a b, f₄ q (fun e => h (by unfold LeafW; omega)) (fun e => h (by unfold LeafW; omega))
      (fun e => h (by unfold LeafW; omega)) (fun e => h (by unfold LeafW; omega))
      (fun e => h (by unfold LeafW; omega)) (fun e => h (by unfold LeafW; omega))
      (fun e => h (by unfold LeafW; omega))]
  have nL : ∀ q, 81035 ≤ q → q ≤ 81038 → ¬ LeafW q := fun q a b => by
    unfold LeafW KeyW VertW; omega
  refine ⟨by rw [g4 _ (nL _ le_rfl (by norm_num)) (by norm_num) (by norm_num), v35],
    by rw [g4 _ (nL _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num), v36],
    by rw [g4 _ (nL _ (by norm_num) (by norm_num)) (by norm_num) (by norm_num), v37],
    by rw [g4 _ (nL _ (by norm_num) le_rfl) (by norm_num) (by norm_num), v38],
    by rw [e']; simp [prL3, regB, regI, upd]; rw [b03]; rfl,
    by rw [e']; simp [prL3, regB, regI, upd]; rw [b06]; rfl, fun q hq => ?_⟩
  have hL : ¬ LeafW q := fun h => hq (Or.inl h)
  rw [g4 q hL (fun h => hq (by unfold RdW; omega)) (fun h => hq (by unfold RdW; omega)),
    f₃ q (fun h => hq (Or.inr (Or.inl h))) (fun h => hL (by unfold LeafW; omega)),
    f₂ q (fun h => hL (by unfold LeafW; omega)) (fun h => hL (by unfold LeafW; omega))
      (fun h => hL (by unfold LeafW; omega)) (fun h => hL (by unfold LeafW; omega))
      (fun h => hL (by unfold LeafW; omega)) (fun h => hL (by unfold LeafW; omega))
      (fun h => hL (by unfold LeafW; omega)),
    f₁ q (fun h => hq (by unfold RdW; omega)) (fun h => hq (by unfold RdW; omega))
      (fun h => hL (by unfold LeafW; omega))]


/-! ## The cutter and the pieces -/

/-- **The cutter's contract** at the input positions `u`, `v` (memory `m`, allocator `A`, list
at `L`). -/
def CutPost (E : FEnv) (u v : WPos) (m : ℕ → ℕ) (A L : ℕ) : Prop :=
  let q := m L
  let pc := fun (i j : ℕ) => m (L + 1 + 7 * i + j)
  let key := fun (e h : ℕ) => E.M.key (Qof E.P) ⟨e, h⟩
  L + 1 + 7 * q ≤ A ∧ q ≤ E.G E.γ ∧ 1 ≤ q ∧
  key (pc 0 0) (pc 0 1) = key u.edge u.hgt ∧
  key (pc (q - 1) 2) (pc (q - 1) 3) = key v.edge v.hgt ∧
  (∀ i, i + 1 < q → key (pc i 2) (pc i 3) = key (pc (i + 1) 0) (pc (i + 1) 1)) ∧
  (∀ i, i + 1 < q → Chain.sideInArc (key (pc i 0) (pc i 1)) (key v.edge v.hgt)
    (key (pc i 2) (pc i 3))) ∧
  (∀ i, i < q → pc i 4 = 0 → E.M.arcWt (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) ≤ 1) ∧
  (∀ i, i < q → pc i 4 = 1 → ChainWF E.P A m (pc i 5) ∧
    ∃ Hs Cα N, ChainDescAt m (pc i 5) (Qof E.P) Hs Cα ∧
    NFWithin m (pc i 6) A N ∧
    (∃ γ', γ' ≤ E.H E.γ ∧ IsCanonicalNF (chainModel Cα) (Qof E.P) N γ' 4) ∧
    E.M.arcSet (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) = Cα.set ∧
    E.M.arcWt (key (pc i 0) (pc i 1)) (key (pc i 2) (pc i 3)) = Cα.m ∧
    PieceWalk E.M Cα ⟨pc i 0, pc i 1⟩ ⟨pc i 2, pc i 3⟩ ∧ Cα.P = Qof E.P ∧
    ((∀ d, d ≤ Cα.m → E.M.W.vtx ((pc i 0 + d) % E.M.W.n) = Cα.vertex d) ∨
      (∀ d, d ≤ Cα.m → E.M.W.vtx ((pc i 0 + d) % E.M.W.n) = Cα.vertex (Cα.m - d)))) ∧
  (∀ i, i < q → ProperPos E.M (Qof E.P) E.P.n ⟨pc i 0, pc i 1⟩ ∧
    ProperPos E.M (Qof E.P) E.P.n ⟨pc i 2, pc i 3⟩ ∧ pc i 0 < E.M.W.n ∧ pc i 2 < E.M.W.n) ∧
  (∀ i, i < q → pc i 4 ≤ 1)

/-- The arguments of the cutter (band `bCut`). -/
def cutL : List Instr := [.copyN 150000 81000, .copyN 150001 81035, .copyN 150002 81036,
  .copyN 150003 81037, .copyN 150004 81038, .copyN 150009 81003, .copyN 150013 81004]

/-- The piece loop's start: the list `81076`, its length `81078`, the index `81079`. -/
def plL : List Instr := [.copyN 81076 150010, .loadN 81078 81076, .constN 81079 0]

/-- **One ordered pair of arcs.** -/
def pairBody (cu sT : Stmt) : Stmt := .seq prReads (.seq (aNorm 81035) (.seq (aNorm 81037)
  (.seq (Stmt.block cutL) (.seq cu (.seq (Stmt.block plL) (pieceLoop sT))))))

/-- The registers the pair writes. -/
def PairW (q : ℕ) : Prop := PW q ∨ RdW q ∨ (81035 ≤ q ∧ q ≤ 81047) ∨ q = 81076 ∨ q = 81078

/-- The cost bound of a pair (`Kp`: the bound of a piece). -/
def pairK (E : FEnv) (Kp : ℕ) : ℕ :=
  70 + anK + anK + 7 + E.G E.γ + 3 + ((Kp + 22) * E.G E.γ + 2)

theorem pairBody_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B)
    (hBT : restoreBands ∪ E.Bo ⊆ B) (hI : FInv E.W c₀ c) (hw : FWin E c) {i j Kp : ℕ}
    (hi : c.nreg 81030 = i) (hj : c.nreg 81031 = j) (hAi : ArcOK E i) (hAj : ArcOK E j)
    (hPG : ∀ c', FInv E.W c₀ c' → CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r i).s)
      (normOf E.M (Qof E.P) (arcOf E.N E.r i).e) c'.nmem (c'.nreg ALLOC) (c'.nreg 81076) →
      ∀ i', i' < c'.nmem (c'.nreg 81076) → PieceGood (E.re c') c' (c'.nreg 81076) Kp i')
    (hnW : 2 * E.M.W.n ≤ E.W) (hroom : c.nreg ALLOC + pairK E Kp ≤ E.W) :
    FRS B E.P E.W c₀ (pairBody E.cu E.sT) c (pairK E Kp) (fun c' => FWin E c' ∧
      (∀ q, 81011 ≤ q → q < 83000 → ¬ PairW q → c'.nreg q = c.nreg q) ∧
      (c.nreg 81007 = 1 → c'.nreg 81007 = 1) ∧
      ∃ c₃ : Config, FInv E.W c₀ c₃ ∧ CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r i).s)
        (normOf E.M (Qof E.P) (arcOf E.N E.r i).e) c₃.nmem (c₃.nreg ALLOC) (c₃.nreg 81076) ∧
        c₃.nreg 81140 = (arcOf E.N E.r j).s.edge ∧ c₃.nreg 81141 = (arcOf E.N E.r j).s.hgt ∧
        ∀ i', i' < c₃.nmem (c₃.nreg 81076) →
          PieceDone (E.re c₃) c₃ c₃ (c₃.nreg 81076) i' (c'.nreg 81007)) := by
  obtain ⟨-, ue, upos, ukey, -⟩ := normOf_facts hAi.sp
  obtain ⟨-, ve, vpos, vkey, -⟩ := normOf_facts hAi.ep
  have hGW := hroom
  unfold pairK at hGW
  -- the reads
  refine FRS.seq (K₁ := 70) (K₂ := pairK E Kp - 70) (prReads_fs hE hB hI hi hj hAi hAj)
    (fun c₁ hI₁ hA₁ h₁ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨r35, r36, r37, r38, r40, r41, f₁⟩ := h₁
  -- normalise the start of arc `i`
  refine FRS.seq (K₁ := anK) (K₂ := pairK E Kp - 70 - anK) (aNorm_fs hE hB hI₁ (s := 81035)
    ⟨by norm_num, by norm_num⟩
    (by rw [show (81035 : ℕ) + 1 = 81036 from rfl, r35, r36]; exact hAi.sp)
    (by rw [r35]; exact hAi.se)
    (fun C hC => by rw [show (81035 : ℕ) + 1 = 81036 from rfl, r35, r36]; exact hAi.sy C hC)
    (by omega)) (fun c₂ hI₂ hA₂ h₂ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨n35, n36, f₂⟩ := h₂
  rw [show (81035 : ℕ) + 1 = 81036 from rfl, r35, r36] at n36
  have m37 : c₂.nreg 81037 = c₁.nreg 81037 :=
    f₂ _ (by norm_num) (by norm_num) (by unfold KeyW; omega) (by norm_num) (by omega)
  have m38 : c₂.nreg 81038 = c₁.nreg 81038 :=
    f₂ _ (by norm_num) (by norm_num) (by unfold KeyW; omega) (by norm_num) (by omega)
  -- normalise its end
  refine FRS.seq (K₁ := anK) (K₂ := pairK E Kp - 70 - anK - anK) (aNorm_fs hE hB hI₂ (s := 81037)
    ⟨by norm_num, by norm_num⟩
    (by rw [show (81037 : ℕ) + 1 = 81038 from rfl, m37, m38, r37, r38]; exact hAi.ep)
    (by rw [m37, r37]; exact hAi.ee)
    (fun C hC => by
      rw [show (81037 : ℕ) + 1 = 81038 from rfl, m37, m38, r37, r38]; exact hAi.ey C hC)
    (by omega)) (fun c₃ hI₃ hA₃ h₃ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨o37, o38, f₃⟩ := h₃
  rw [show (81037 : ℕ) + 1 = 81038 from rfl, m37, m38, r37, r38] at o38
  have x35 : c₃.nreg 81035 = (arcOf E.N E.r i).s.edge := by
    rw [f₃ _ (by norm_num) (by norm_num) (by unfold KeyW; omega) (by norm_num) (by omega), n35, r35]
  have x36 : c₃.nreg 81036 = (normOf E.M (Qof E.P) (arcOf E.N E.r i).s).hgt := by
    rw [f₃ _ (by norm_num) (by norm_num) (by unfold KeyW; omega) (by norm_num) (by omega), n36]
  have x37 : c₃.nreg 81037 = (arcOf E.N E.r i).e.edge := by rw [o37, m37, r37]
  -- the cutter's arguments
  have ok4 : okB E.W c₃.nmem cutL c₃.nreg := by
    simp [cutL, okB, okI, FScr, FOut, bandOf, oracleBands, kernelBands, bCut]
  refine FRS.seq (K₁ := 7) (K₂ := pairK E Kp - 70 - anK - anK - 7) (FRS.block hB _ hI₃ ok4)
    (fun c₄ hI₄ hA₄ h₄ => ?_) |>.mono (by unfold pairK; omega) (fun _ h => h)
  have e₄ : ∀ q, c₄.nreg q = regB c₃.nmem cutL c₃.nreg q := fun q => by rw [h₄]
  have f₄ : ∀ q, q < 150000 → c₄.nreg q = c₃.nreg q := fun q hq => by
    rw [e₄, regB_other _ _ _ (fun i hi => ?_)]
    simp only [cutL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [dstI] <;> omega
  have rd0 : rd c₄ bCut 0 = E.MD := by
    show c₄.nreg 150000 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [hI₃.hin _ (by unfold FFix; omega), hE.i0]
  have rd1 : rd c₄ bCut 1 = (normOf E.M (Qof E.P) (arcOf E.N E.r i).s).edge := by
    show c₄.nreg 150001 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [x35, ue]
  have rd2 : rd c₄ bCut 2 = (normOf E.M (Qof E.P) (arcOf E.N E.r i).s).hgt := by
    show c₄.nreg 150002 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [x36]
  have rd3 : rd c₄ bCut 3 = (normOf E.M (Qof E.P) (arcOf E.N E.r i).e).edge := by
    show c₄.nreg 150003 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [x37, ve]
  have rd4 : rd c₄ bCut 4 = (normOf E.M (Qof E.P) (arcOf E.N E.r i).e).hgt := by
    show c₄.nreg 150004 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [o38]
  have rd9 : rd c₄ bCut 9 = E.γ := by
    show c₄.nreg 150009 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [hI₃.hin _ (by unfold FFix; omega), hE.i3]
  have rd13 : rd c₄ bCut 13 = E.g := by
    show c₄.nreg 150013 = _
    rw [e₄]; simp [cutL, regB, regI, upd]; rw [hI₃.hin _ (by unfold FFix; omega), hE.i4]
  have pu : (⟨rd c₄ bCut 1, rd c₄ bCut 2⟩ : WPos) =
      normOf E.M (Qof E.P) (arcOf E.N E.r i).s := by rw [rd1, rd2]
  have pv : (⟨rd c₄ bCut 3, rd c₄ bCut 4⟩ : WPos) =
      normOf E.M (Qof E.P) (arcOf E.N E.r i).e := by rw [rd3, rd4]
  have hEb := hE.rebase hI₄
  -- the cutter
  have hcall := FRS.callF (B := B) (P := E.P) (W := E.W) (c₀ := c₀) (c := c₄) hE.hcu
    (hE.hBc.trans (Finset.subset_union_right.trans hBT)) hI₄
    ⟨hE.hG, hE.hWh, by rw [rd13]; exact hEb.hX, by rw [rd9, rd13]; exact hEb.hcap,
      by rw [rd0]; exact hEb.hwf, E.M, by rw [rd0]; exact hEb.hMD, hE.hOk,
      by rw [pu]; exact (normOf_facts hAi.sp).1.1, by rw [pv]; exact (normOf_facts hAi.ep).1.1,
      by rw [rd1, ue]; exact hAi.se, by rw [rd3, ve]; exact hAi.ee,
      by rw [pu, rd2, upos]; exact hAi.sI, by rw [pv, rd4, vpos]; exact hAi.eI,
      by rw [pu, pv, ukey, vkey, rd9]; exact hAi.wt⟩
    (by rw [rd9]; omega) (fun h => hE.hB8 (hE.hBc h))
  refine FRS.seq (K₁ := E.G E.γ) (K₂ := 3 + ((Kp + 22) * E.G E.γ + 2))
    (hcall.mono (by rw [rd9]) (fun _ h => h)) (fun c₅ hI₅ hA₅ h₅ => ?_) |>.mono
    (by unfold pairK; omega) (fun _ h => h)
  obtain ⟨hpost, -, -, f₅⟩ := h₅
  -- the piece loop's start
  have ok6 : okB E.W c₅.nmem plL c₅.nreg := by
    simp only [plL, okB, okI, FScr, FOut]; norm_num
  refine FRS.seq (K₁ := 3) (K₂ := (Kp + 22) * E.G E.γ + 2) (FRS.block hB _ hI₅ ok6)
    (fun c₆ hI₆ hA₆ h₆ => ?_)
  have e₆ : ∀ q, c₆.nreg q = regB c₅.nmem plL c₅.nreg q := fun q => by rw [h₆]
  have nm6 : c₆.nmem = c₅.nmem := by rw [h₆]
  have s76 : c₆.nreg 81076 = rd c₅ bCut 10 := by rw [e₆]; simp [plL, regB, regI, upd]; rfl
  have s78 : c₆.nreg 81078 = c₆.nmem (c₆.nreg 81076) := by
    rw [nm6, s76, e₆]; simp [plL, regB, regI, upd]; rfl
  have s79 : c₆.nreg 81079 = 0 := by rw [e₆]; simp [plL, regB, regI, upd]
  have a6 : c₆.nreg ALLOC = c₅.nreg ALLOC := by rw [e₆]; simp [plL, regB, regI, upd, ALLOC]
  have f₆ : ∀ q, q ≠ 81076 → q ≠ 81078 → q ≠ 81079 → c₆.nreg q = c₅.nreg q := fun q a b d => by
    rw [e₆]; simp [plL, regB, regI, upd, a, b, d]
  -- the frame so far
  have g6 : ∀ q, 80000 ≤ q → q < 83000 → ¬ PairW q → c₆.nreg q = c.nreg q := fun q a b hq => by
    have h8 : bandOf q = bRestore := by unfold bandOf bRestore; omega
    rw [f₆ q (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        (fun h => hq (Or.inr (Or.inr (Or.inr (Or.inr h)))))
        (fun h => hq (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))),
      f₅ q (by rw [h8]; exact fun h => hE.hB8 (hE.hBc h)) (by unfold ALLOC; omega),
      f₄ q (by omega),
      f₃ q a (by omega) (by unfold KeyW; omega)
        (fun h => hq (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
        (fun h => hq (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))),
      f₂ q a (by omega) (by unfold KeyW; omega)
        (fun h => hq (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))))
        (fun h => hq (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))),
      f₁ q (fun h => hq (Or.inr (Or.inl h)))]
  have nP : ∀ q, 81007 ≤ q → q ≤ 81010 → ¬ PairW q := fun q a b => by
    unfold PairW RdW PW K1W DescW NodeW LeafW KeyW VertW; omega
  have hw₆ : FWin E c₆ := hw.congr' (fun q a b => g6 q (by omega) (by omega) (nP q a b))
  -- through the cutter, from the reads
  have g16 : ∀ q, 81140 ≤ q → q ≤ 81141 → c₆.nreg q = c₁.nreg q := fun q a b => by
    have h8 : bandOf q = bRestore := by unfold bandOf bRestore; omega
    rw [f₆ q (by omega) (by omega) (by omega),
      f₅ q (by rw [h8]; exact fun h => hE.hB8 (hE.hBc h)) (by unfold ALLOC; omega),
      f₄ q (by omega), f₃ q (by omega) (by omega) (by unfold KeyW; omega) (by omega) (by omega),
      f₂ q (by omega) (by omega) (by unfold KeyW; omega) (by omega) (by omega)]
  have t40 : c₆.nreg 81140 = (arcOf E.N E.r j).s.edge := by rw [g16 _ le_rfl (by norm_num), r40]
  have t41 : c₆.nreg 81141 = (arcOf E.N E.r j).s.hgt := by rw [g16 _ (by norm_num) le_rfl, r41]
  -- the cutter's contract
  have hcp : CutPost E (normOf E.M (Qof E.P) (arcOf E.N E.r i).s)
      (normOf E.M (Qof E.P) (arcOf E.N E.r i).e) c₆.nmem (c₆.nreg ALLOC) (c₆.nreg 81076) := by
    have hp := hpost E.M (by rw [rd0]; exact hEb.hMD)
    rw [rd1, rd2, rd3, rd4, rd9] at hp
    rw [nm6, a6, s76]
    exact hp.2
  have hq₆ : c₆.nmem (c₆.nreg 81076) ≤ E.G E.γ := hcp.2.1
  -- the piece loop, rebased
  have hE₆ := hE.rebase hI₆
  have hloop := pieceLoop_fs hE₆ hB hBT ⟨hI₆.hw, fun _ _ => rfl, le_rfl, fun _ _ => rfl⟩ hw₆
    rfl s78 s79 (hPG c₆ hI₆ hcp) (by rw [t40, t41]; exact ⟨hAj.se, hAj.sp⟩) hnW
    (by
      have := Nat.mul_le_mul_left (Kp + 22) hq₆
      show c₆.nreg ALLOC + _ ≤ E.W
      omega)
  refine ((FRS.restrict hI₆ hloop hI₆.hA).mono (by
    have := Nat.mul_le_mul_left (Kp + 22) hq₆; omega) (fun c₇ h₇ => ?_))
  obtain ⟨w₇, f₇, m₇, d₇⟩ := h₇
  have nPW : ∀ q, ¬ PairW q → ¬ PW q := fun q h h' => h (Or.inl h')
  refine ⟨w₇, fun q a b hq => (f₇ q a b (nPW q hq)).trans (g6 q (by omega) b hq),
    fun h => m₇ (by rw [g6 _ (by norm_num) (by norm_num) (nP _ le_rfl (by norm_num))]; exact h),
    c₆, hI₆, hcp, t40, t41, d₇⟩

end

end Restore

end Chazelle.Core
