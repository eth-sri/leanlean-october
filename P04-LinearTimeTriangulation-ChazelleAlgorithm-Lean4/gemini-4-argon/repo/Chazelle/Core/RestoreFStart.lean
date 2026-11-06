module

public import Chazelle.Core.RestoreFInit

/-!
# WP-E, the search on the RAM (`FindOK`), part 29: the run facts after the initialisation

The walk data of a chain model (vertices `6 … 2m + 6` on the chain, edges `6 … 2m + 5` counted,
box points off the chain), and `FGood` for the configuration reached by `fInit`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-! ## The walk of a chain model -/

theorem chain_vtx_mem (C : Chain) (Q : Polygon) {v : ℕ} (h6 : 6 ≤ v) (hv : v ≤ 2 * C.m + 6) :
    (chainModel C).pos Q ⟨v, 0⟩ ∈ C.set := by
  rw [pos_eq_sidePt, param_vtx]
  show Chazelle.Chain.sidePt (C.sideWalk C.sideBeta) v 0 ∈ C.set
  have := C.sideWalk_tour_pt_mem C.sideBeta (i := v - 6) (t := 0) (by omega) (fun _ => rfl)
    le_rfl one_pos
  rwa [show v - 6 + 6 = v by omega] at this

theorem chain_vtx_six (C : Chain) (Q : Polygon) {v : ℕ}
    (hv : (chainModel C).pos Q ⟨v, 0⟩ ∈ C.set) : 6 ≤ v := by
  by_contra h
  rw [pos_eq_sidePt, param_vtx] at hv
  exact IOrc.box_pos_not_mem C (by show v < 6; omega) le_rfl one_pos hv

theorem chain_edge_mem (C : Chain) (Q : Polygon) {n e h : ℕ} (h6 : 6 ≤ e) (he : e < 2 * C.m + 6)
    (hp : ProperPos (chainModel C) Q n ⟨e, h⟩) : (chainModel C).pos Q ⟨e, h⟩ ∈ C.set := by
  rw [pos_eq_sidePt]
  show Chazelle.Chain.sidePt (C.sideWalk C.sideBeta) e _ ∈ C.set
  have := C.sideWalk_tour_pt_mem C.sideBeta (i := e - 6)
    (t := (chainModel C).param Q ⟨e, h⟩) (by omega) (fun h' => absurd h' (by omega)) hp.1 hp.2.1
  rwa [show e - 6 + 6 = e by omega] at this

theorem chain_m_eq {C C' : Chain} (h : chainModel C = chainModel C') : C.m = C'.m := by
  have := congrArg (fun M : Model => M.W.n) h
  simp only [chainModel_n] at this
  omega

theorem interiorWalk_n' (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  unfold interiorWalk; split_ifs
  · rfl
  · simp [Polygon.n]

/-! ## The environment of a run -/

/-- The environment of the search started in `c` (model `M`, normal form `N`). -/
def fEnv (P : Polygon) (W : ℕ) (M : Model) (N : NF) (X : MemCtx) (Ok : Polygon → Model → Prop)
    (cu sT : Stmt) (Bc Bo : Finset ℕ) (F G H κt : ℕ → ℕ) (c : Config) : FEnv where
  P := P
  W := W
  M := M
  N := N
  X := X
  Ok := Ok
  cu := cu
  sT := sT
  Bc := Bc
  Bo := Bo
  F := F
  G := G
  H := H
  κt := κt
  A₀ := c.nreg ALLOC
  m₀ := c.nmem
  MD := c.nreg 81000
  NH := c.nreg 81001
  r := c.nreg 81002
  γ := c.nreg 81003
  g := c.nreg 81004
  d := c.nreg 81005
  D := c.nreg 81006


/-- **The start of the search**: the initialisation runs, and the run facts hold after it. -/
theorem find_start {P : Polygon} {W : ℕ} {c : Config} {M : Model} {N : NF} {X : MemCtx}
    {Ok : Polygon → Model → Prop} {cu sh : Stmt} {Bs Bc Bo : Finset ℕ} {F G H : ℕ → ℕ}
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hcu : CutterOK cu Bc G H X Ok)
    (hBc : Bc ⊆ Bo) (hBo : oracleBands ⊆ Bo) (hB8 : bRestore ∉ Bo) (hloc : X.CapLocal)
    (hhalf : X.Halves) (hOkM : ∀ P M, Ok P M → OkModel P M ∨ M = interiorModel (Qof P))
    (hw : WordsBounded W c) (hG : GoodEnv P) (hWh : hostWords P.n ≤ W)
    (hX : X.holds P c.nmem (c.nreg 81004) (c.nreg ALLOC))
    (hcap : c.nreg 81003 ≤ X.cap P c.nmem (c.nreg 81004))
    (hwf : ModelDescWF P (c.nreg ALLOC) c.nmem (c.nreg 81000))
    (hreg : c.nmem (c.nreg 81000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 81000 + 1) (Qof P) H C →
      HostRegular (Qof P).n H)
    (hsimp : c.nmem (c.nreg 81000) = 0 → ∀ H C, ChainDescAt c.nmem (c.nreg 81000 + 1) (Qof P) H C →
      C.P.Simple)
    (hMD : ModelDescAt c.nmem (c.nreg 81000) (Qof P) M) (hGM : GoodModel M) (hOk : Ok P M)
    (hNW : NFWithin c.nmem (c.nreg 81001) (c.nreg ALLOC) N) (hNF : IsNF M (Qof P) N)
    (hdeg : M.DegLe (N.F M (Qof P)) (c.nreg 81005))
    (hsg : M.Semigranular (N.F M (Qof P)) (c.nreg 81003)) (hr : c.nreg 81002 < N.nRegions) :
    ∃ c₀ k, Exec P W fInit c c₀ k ∧ k ≤ 30 ∧ c₀.nmem = c.nmem ∧ c₀.rreg = c.rreg ∧
      c₀.rmem = c.rmem ∧ c₀.output = c.output ∧
      (∀ q, ¬ IniW q → c₀.nreg q = c.nreg q) ∧ c₀.nreg 81007 = 0 ∧
      FGood (fEnv P W M N X Ok cu (testS sh) Bc Bo F G H testκ c) c₀ := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hk : c.nmem (c.nreg 81000) = 0 → 2 * c.nmem (c.nreg 81000 + 3) + 7 ≤ W := fun h0 => by
    rcases hMD with ⟨-, H', C', hC, hM⟩ | ⟨h1, -⟩
    · have := walk_le_W (P := P) (M := M) (W := W) (Or.inl ⟨h0, H', C', hC, hM⟩) hwf hWh hM
      have hm : c.nmem (c.nreg 81000 + 1 + 2) = C'.m := hC.2.2.2.1
      rw [show c.nreg 81000 + 1 + 2 = c.nreg 81000 + 3 by omega] at hm
      omega
    · omega
  obtain ⟨c₀, k, ex, hk30, nm, rr, rm, ro, fr, v07, v11, v12, v13, v14, v15, v16, v24, v20, v23, v22, vch,
    vin⟩ := fInit_exec hw (by unfold hostWords at hWh; omega) (by unfold hostWords at hWh; omega)
      hX hhalf hwf.1 hk
  have fx : ∀ q, q < 81007 → c₀.nreg q = c.nreg q := fun q h => fr q (by unfold IniW; omega)
  have hA : c₀.nreg ALLOC = c.nreg ALLOC := fx _ (by unfold ALLOC; omega)
  refine ⟨c₀, k, ex, hk30, nm, rr, rm, ro, fr, v07, ?_⟩
  -- the walk data, by the kind of the model
  have hdata : c₀.nreg 81017 = M.W.n ∧
      (∀ v, v < M.W.n → c₀.nreg 81021 ≤ v → v ≤ c₀.nreg 81019 →
        ∀ C : Chain, M = chainModel C → M.pos (Qof P) ⟨v, 0⟩ ∈ C.set) ∧
      (∀ v, v < M.W.n → (∀ C : Chain, M = chainModel C → M.pos (Qof P) ⟨v, 0⟩ ∈ C.set) →
        c₀.nreg 81021 ≤ v ∧ v ≤ c₀.nreg 81019) ∧
      (∀ C : Chain, M = chainModel C → 6 ≤ c₀.nreg 81021) ∧
      (∀ e h, e < M.W.n → c₀.nreg 81021 ≤ e → e < c₀.nreg 81025 →
        ProperPos M (Qof P) P.n ⟨e, h⟩ →
        ∀ C : Chain, M = chainModel C → M.pos (Qof P) ⟨e, h⟩ ∈ C.set) ∧
      (∀ e, e < M.W.n → M.counted e → c₀.nreg 81021 ≤ e ∧ e < c₀.nreg 81025) := by
    rcases hMD with ⟨h0, H', C', hC, hM⟩ | ⟨h1, -, hM⟩
    · obtain ⟨d21, d19, d25, d17⟩ := vch h0
      have hm : c.nmem (c.nreg 81000 + 1 + 2) = C'.m := hC.2.2.2.1
      rw [show c.nreg 81000 + 1 + 2 = c.nreg 81000 + 3 by omega] at hm
      rw [hm] at d19 d25 d17
      have hn : M.W.n = 2 * C'.m + 7 := by rw [hM]; exact chainModel_n C'
      refine ⟨by rw [d17, hn], fun v hv a b C hC' => ?_, fun v hv h => ?_, fun _ _ => by omega,
        fun e h he a b hp C hC' => ?_, fun e he hc => ?_⟩
      · rw [hC']
        have := chain_m_eq (hC'.symm.trans hM)
        exact chain_vtx_mem C _ (by omega) (by omega)
      · have h6 := chain_vtx_six C' (Qof P) (by rw [← hM]; exact h C' hM)
        omega
      · rw [hC'] at hp ⊢
        have := chain_m_eq (hC'.symm.trans hM)
        exact chain_edge_mem C _ (by omega) (by omega) hp
      · rw [hM] at hc
        obtain ⟨c1, c2⟩ := hc
        omega
    · have h1' : c.nmem (c.nreg 81000) ≠ 0 := by omega
      obtain ⟨d21, d19, d25, d17⟩ := vin h1'
      have hn : M.W.n = P.n := by
        rw [hM]; show (interiorWalk (Qof P)).n = _; rw [interiorWalk_n', hQn]
      refine ⟨by rw [d17, hn], fun v _ _ _ C hC => absurd (hC.symm.trans hM)
          (chainModel_ne_interior C _),
        fun v hv _ => by omega, fun C hC => absurd (hC.symm.trans hM) (chainModel_ne_interior C _),
        fun e h _ _ _ _ C hC => absurd (hC.symm.trans hM) (chainModel_ne_interior C _),
        fun e he _ => by omega⟩
  obtain ⟨wn, hvr, hvc, vlo6, ehr, ehc⟩ := hdata
  exact {
    hT := testOK hsh hBs hloc hB8 hBo, hcu := hcu, hBc := hBc, hBo := hBo, hB8 := hB8,
    hloc := hloc, hhalf := hhalf, hOkM := hOkM, hG := hG, hWh := hWh, hX := hX, hcap := hcap,
    hwf := hwf, hreg := hreg, hsimp := hsimp, hMD := hMD, hGM := hGM, hOk := hOk, hNW := hNW,
    hNF := hNF, hdeg := hdeg, hsg := hsg, hr := hr, a0 := hA, m0 := nm,
    i0 := fx _ (by norm_num), i1 := fx _ (by norm_num), i2 := fx _ (by norm_num),
    i3 := fx _ (by norm_num), i4 := fx _ (by norm_num), i5 := fx _ (by norm_num),
    i6 := fx _ (by norm_num), k0 := v11, k1 := v12, k2 := v13, k3 := v14, k5 := v15, k7 := v16,
    pn := v20, nE := v22, hE2 := v23, wn := wn, k10 := v24, hvr := hvr, hvc := hvc,
    vlo6 := vlo6, ehr := ehr, ehc := ehc }


/-! ## The number of arcs -/

/-- The reads of the arc count `k` (`81032`) of region `r` (`0` if the region has no exit chord),
and `i = 0` (`81030`). -/
def aCntL : List Instr :=
  [.copyN 81134 81001, .copyN 81121 81002, .addN 81114 81134 81015, .loadN 81114 81114,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .addN 81114 81114 81121,
    .addN 81114 81114 81121, .addN 81114 81114 81121, .loadN 81032 81114,
    .addN 81115 81114 81013, .loadN 81115 81115, .constN 81030 0]

/-- **The arc count.** -/
def aCntS : Stmt := .seq (Stmt.block aCntL) (.ifLtN 81011 81115 .skip (Stmt.block [.constN 81032 0]))

/-- The arc count of the search. -/
def kOf (E : FEnv) : ℕ :=
  if (E.N.region E.r).chords = [] then 0 else (E.N.region E.r).arcs.length

variable {E : FEnv} {c₀ c : Config}

theorem cnt_fs (hE : FGood E c₀) {B : Finset ℕ} (hB : dBands ⊆ B) (hI : FInv E.W c₀ c) :
    FRS B E.P E.W c₀ aCntS c 17 (fun c' => c'.nreg 81030 = 0 ∧ c'.nreg 81032 = kOf E ∧
      ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81114 → q ≠ 81115 → q ≠ 81030 → q ≠ 81032 →
        c'.nreg q = c.nreg q) := by
  have hN : NFWithin c.nmem E.NH (c₀.nreg ALLOC) E.N := by
    have h0 : NFWithin c₀.nmem E.NH (c₀.nreg ALLOC) E.N := by rw [hE.m0, hE.a0]; exact hE.hNW
    exact Robust.transport h0 (fun a ha => hI.hm a ha)
  have hNA := hN.nfAt
  obtain ⟨hB7, -, -, hrb, -, -⟩ := nf_bounds hN
  have hA0 : c₀.nreg ALLOC ≤ c.nreg ALLOC := hI.hA
  have hAW : c.nreg ALLOC ≤ E.W := hI.hw.1 ALLOC
  have hrl : E.r < E.N.regions.length := hE.hr
  obtain ⟨hna, hnc, -⟩ := hNA.2.2.2.2.2.2.2.1 _ hrl
  have b1 := hrb _ hE.hr
  have e01 : c.nreg 81001 = E.NH := by rw [hI.hin _ (by unfold FFix; omega), hE.i1]
  have e02 : c.nreg 81002 = E.r := by rw [hI.hin _ (by unfold FFix; omega), hE.i2]
  have k5 : c.nreg 81015 = 5 := by rw [hI.hin _ (by unfold FFix; omega), hE.k5]
  have k2 : c.nreg 81013 = 2 := by rw [hI.hin _ (by unfold FFix; omega), hE.k2]
  have e5 : c.nmem (E.NH + 5) + E.r + E.r + E.r + E.r + E.r = c.nmem (E.NH + 5) + 5 * E.r := by
    ring
  have ok : okB E.W c.nmem aCntL c.nreg := by
    simp only [aCntL, okB, okI, regI, upd]
    simp only [FScr, FOut, k5, k2, e01, e02]
    norm_num
    try rw [e5]
    (repeat' apply And.intro) <;> omega
  refine FRS.seq (K₁ := 13) (K₂ := 4) (FRS.block hB _ hI ok) (fun c₁ hI₁ _ h₁ => ?_)
  have e₁ : ∀ q, c₁.nreg q = regB c.nmem aCntL c.nreg q := fun q => by rw [h₁]
  have v30 : c₁.nreg 81030 = 0 := by rw [e₁]; simp [aCntL, regB, regI, upd]
  have v32 : c₁.nreg 81032 = (E.N.region E.r).arcs.length := by
    rw [e₁]; simp [aCntL, regB, regI, upd, k5, e01, e02]; rwa [e5]
  have v15 : c₁.nreg 81115 = (E.N.region E.r).chords.length := by
    rw [e₁]; simp [aCntL, regB, regI, upd, k5, k2, e01, e02]; rwa [e5]
  have f₁ : ∀ q, q ≠ 81134 → q ≠ 81121 → q ≠ 81114 → q ≠ 81115 → q ≠ 81030 → q ≠ 81032 →
      c₁.nreg q = c.nreg q := fun q a b d e f g => by
    rw [e₁, regB_other _ _ _ (fun i hi => ?_)]
    simp only [aCntL, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> omega
  have k0 := k0_of hE hI₁
  by_cases a : c₁.nreg 81011 < c₁.nreg 81115
  · have hne : (E.N.region E.r).chords ≠ [] := by
      intro h; rw [v15, h, k0] at a; simp at a
    refine (FRS.ifT a (FRS.skip (K := 0) hI₁ ⟨v30, ?_, f₁⟩)).mono (by omega) (fun _ h => h)
    rw [v32]; unfold kOf; rw [ite_eq_right hne]
  · have he : (E.N.region E.r).chords = [] := by
      rw [v15, k0] at a; exact List.length_eq_zero_iff.1 (by omega)
    have ok2 : okB E.W c₁.nmem [.constN 81032 0] c₁.nreg := by
      simp only [okB, okI, FScr, FOut]; norm_num
    refine (FRS.ifF a (FRS.block hB _ hI₁ ok2)).mono (by simp) (fun c' h' => ?_)
    have e' : ∀ q, c'.nreg q = regB c₁.nmem [.constN 81032 0] c₁.nreg q := fun q => by rw [h']
    refine ⟨by rw [e']; simp [regB, regI, upd, v30], by rw [e']; simp [regB, regI, upd, kOf, he],
      fun q a b d e f g => by rw [e']; simp [regB, regI, upd, g]; exact f₁ q a b d e f g⟩

end

end Restore

end Chazelle.Core
