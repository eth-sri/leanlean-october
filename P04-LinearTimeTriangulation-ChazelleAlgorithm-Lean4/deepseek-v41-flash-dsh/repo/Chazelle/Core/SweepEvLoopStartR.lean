module

public import Chazelle.Core.SweepEvLoopStartM

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0, RAM part 1: the stops)

`stStep`: if the stop `sP` lies at the current key (offset comparison `callOff`), append the
labels of its auxiliary record if it is anchored (`addLab`), set the anchored flag `aF`, and
advance `sP`.  Run twice from `sP = 0` at the start key, it skips exactly the stops at the start
key (at most two, `stops_two`).

The state of the label list and of the pointer: `StI`.
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

/-! ## Registers -/

def zE : ℕ := sw 2480
def zH : ℕ := sw 2481
def zO : ℕ := sw 2482
def aF : ℕ := sw 2484
def zX : ℕ := sw 2485
def zA : ℕ := sw 2486
def zN : ℕ := sw 2487
def zL : ℕ := sw 2488
def zM : ℕ := sw 2489
def zT : ℕ := sw 2490

/-! ## The code -/

/-- Load the position of stop `sP`. -/
def lsStLoad : List Instr :=
  [.addN zX sP sP, .addN zX zX zX, .addN zX zX sP, .addN zX zX sB, .loadN zE zX,
    .addN zX zX K1, .loadN zH zX]

/-- Load the auxiliary record of stop `sP`: anchored flag, count, two labels. -/
def stAux : List Instr :=
  [.addN zX sP sP, .addN zX zX zX, .addN zX zX sP, .addN zX zX aB, .loadN zA zX,
    .addN zX zX K1, .loadN zN zX, .addN zX zX K1, .loadN zL zX, .addN zX zX K1, .loadN zM zX]

/-- The labels of an anchored stop. -/
def stLabs : Stmt :=
  .ifLtN zA K1 .skip (.seq (.instr (.constN aF 1))
    (.seq (.ifLtN K0 zN (addLab kN kL zL) .skip) (.ifLtN K1 zN (addLab kN kL zM) .skip)))

/-- Take the stop `sP`. -/
def stTake : Stmt := .seq (block stAux) (.seq stLabs (.instr (.addN sP sP K1)))

/-- **One stop step.** -/
def stStep : Stmt :=
  .ifLtN sP sC (.seq (block lsStLoad) (.seq (callOff (sw 2) kE kH zE zH cGW zO)
    (.ifLtN K0 zO .skip stTake))) .skip

/-- The cost of a stop step. -/
def stStepK : ℕ := 12000

/-! ## The blocks -/

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

theorem stLoad_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m lsStLoad f zE = m (f sB + 5 * f sP) ∧ regB m lsStLoad f zH = m (f sB + 5 * f sP + 1) := by
  have e1 : f 240611 = 1 := hk1
  ϴ lsStLoad, regB, regI, upd, zX, zE, zH, sP, sB, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  exact ⟨congrArg m (⋆), congrArg m (⋆)⟩

theorem stLoad_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ zX) (h2 : q ≠ zE) (h3 : q ≠ zH) :
    regB m lsStLoad f q = f q :=
  regB_other m lsStLoad f (fun i hi => by
    ϴ' lsStLoad, List.mem_cons, List.not_mem_nil, or_false at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro h <;> subst h <;> simp_all)

theorem stLoad_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f sB + 5 * f sP + 1 ≤ W) :
    okB W m lsStLoad f := by
  have e1 : f 240611 = 1 := hk1
  have hb' : f 242600 + 5 * f 242450 + 1 ≤ W := hb
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (⋄) (⋄)
  ϴ lsStLoad, okB, okI, regI, upd, zX, zE, zH, sP, sB, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  exact ⟨⟨s 2485 (⊛) (⊛), ⋄⟩, ⟨s 2485 (⊛) (⊛),
    ⋄⟩, ⟨s 2485 (⊛) (⊛), ⋄⟩,
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2480 (⊛) (⊛),
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2481 (⊛) (⊛), trivial⟩

theorem stAux_val (m f : ℕ → ℕ) (hk1 : f K1 = 1) :
    regB m stAux f zA = m (f aB + 5 * f sP) ∧ regB m stAux f zN = m (f aB + 5 * f sP + 1) ∧
    regB m stAux f zL = m (f aB + 5 * f sP + 2) ∧ regB m stAux f zM = m (f aB + 5 * f sP + 3) := by
  have e1 : f 240611 = 1 := hk1
  ϴ stAux, regB, regI, upd, zX, zA, zN, zL, zM, sP, aB, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  exact ⟨congrArg m (⋆), congrArg m (⋆), congrArg m (⋆), congrArg m (⋆)⟩

theorem stAux_other (m f : ℕ → ℕ) {q : ℕ} (h1 : q ≠ zX) (h2 : q ≠ zA) (h3 : q ≠ zN)
    (h4 : q ≠ zL) (h5 : q ≠ zM) : regB m stAux f q = f q :=
  regB_other m stAux f (fun i hi => by
    ϴ' stAux, List.mem_cons, List.not_mem_nil, or_false at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [dstI] <;> intro h <;> subst h <;> simp_all)

theorem stAux_ok (m f : ℕ → ℕ) (hk1 : f K1 = 1) (hb : f aB + 5 * f sP + 3 ≤ W) :
    okB W m stAux f := by
  have e1 : f 240611 = 1 := hk1
  have hb' : f 242602 + 5 * f 242450 + 3 ≤ W := hb
  have s : ∀ j, 700 ≤ j → j < 10000 → IScr (240000 + j) := fun j h1 h2 =>
    iscr_sw (⋄) (⋄)
  ϴ stAux, okB, okI, regI, upd, zX, zA, zN, zL, zM, sP, aB, K1, sw
  ϴ Nat.reduceAdd, Nat.reduceEqDiff, ite_true, ite_false, e1
  exact ⟨⟨s 2485 (⊛) (⊛), ⋄⟩, ⟨s 2485 (⊛) (⊛),
    ⋄⟩, ⟨s 2485 (⊛) (⊛), ⋄⟩,
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2486 (⊛) (⊛),
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2487 (⊛) (⊛),
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2488 (⊛) (⊛),
    ⟨s 2485 (⊛) (⊛), ⋄⟩, s 2489 (⊛) (⊛), trivial⟩

/-! ## Label lists -/

/-- The labels appended for an anchored stop with `n` labels `a`, `b`. -/
def labAdd (l : List ℕ) (n a b : ℕ) : List ℕ :=
  if 1 < n then addL (if 0 < n then addL l a else l) b else (if 0 < n then addL l a else l)

/-- The labels of an auxiliary record (if anchored). -/
def axLabs (x : ℕ × ℕ × ℕ × ℕ × ℕ) : List ℕ :=
  if x.1 = 1 then (if 0 < x.2.1 then [x.2.2.1] else []) ++ (if 1 < x.2.1 then [x.2.2.2.1] else [])
  else []

theorem st_addL_self {l : List ℕ} (h : l.length < 4) (v : ℕ) : v ∈ addL l v := by
  unfold addL; split_ifs with h1
  · rcases h1 with h1 | h1
    · exact h1
    · omega
  · simp

theorem st_addL_len (l : List ℕ) (v : ℕ) : (addL l v).length ≤ l.length + 1 := by
  unfold addL; split_ifs <;> simp

theorem labAdd_len (l : List ℕ) (n a b : ℕ) : (labAdd l n a b).length ≤ l.length + 2 := by
  unfold labAdd
  have h1 := st_addL_len l a
  split_ifs with h2 h3
  · have := st_addL_len (addL l a) b; omega
  · have := st_addL_len l b; omega
  · omega
  · omega

theorem labAdd_old {l : List ℕ} {n a b x : ℕ} (h : x ∈ l) : x ∈ labAdd l n a b := by
  unfold labAdd
  split_ifs <;> first | exact mem_addL_of_mem (mem_addL_of_mem h) | exact mem_addL_of_mem h | exact h

theorem labAdd_mem {l : List ℕ} {n a b x : ℕ} (h : x ∈ labAdd l n a b) :
    x ∈ l ∨ (0 < n ∧ x = a) ∨ (1 < n ∧ x = b) := by
  unfold labAdd at h
  by_cases h1 : 1 < n
  · Ξ' ite_eq_left h1, ite_eq_left (⋄) at h
    rcases mem_addL h with h | h
    · rcases mem_addL h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨⋄, h⟩)
    · exact Or.inr (Or.inr ⟨h1, h⟩)
  · Ξ' ite_eq_right h1 at h
    by_cases h0 : 0 < n
    · Ξ' ite_eq_left h0 at h
      rcases mem_addL h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨h0, h⟩)
    · Ξ' ite_eq_right h0 at h
      exact Or.inl h

theorem labAdd_new {l : List ℕ} (hl : l.length ≤ 2) {n a b x : ℕ}
    (h : (0 < n ∧ x = a) ∨ (1 < n ∧ x = b)) : x ∈ labAdd l n a b := by
  unfold labAdd
  have hla := st_addL_len l a
  rcases h with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · Ξ ite_eq_left h1
    split_ifs
    · exact mem_addL_of_mem (st_addL_self (⋄) x)
    · exact st_addL_self (⋄) x
  · Ξ ite_eq_left h1, ite_eq_left (⋄)
    exact st_addL_self (⋄) x

theorem lblR_facts : IScr kN ∧ (∀ i, i < 4 → IScr (kL + i)) ∧ (∀ i, i < 4 → kN ≠ kL + i) ∧
    (∀ k, k = K1 ∨ k = K2 ∨ k = K3 ∨ k = K4 → ¬ LblR kN kL k) :=
  ⟨iscr_sw (by unfold kN sw; norm_num) (by unfold kN sw; norm_num),
    fun i hi => iscr_sw (by unfold kL sw; omega) (by unfold kL sw; omega),
    fun i hi => by unfold kN kL sw; omega,
    by rintro k (rfl | rfl | rfl | rfl) <;> simp [LblR, kN, kL, K1, K2, K3, K4, sw]⟩


/-- A conditional label: append the value of `r` if `g < zN`. -/
theorem condLab_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hN : c.nreg kN ≤ 4) {g r : ℕ}
    (hrN : r ≠ kN) (hrL : ∀ i, i < 4 → r ≠ kL + i) (hW : 4 ≤ W) :
    IRS P W c₀ (.ifLtN g zN (addLab kN kL r) .skip) c 32 (fun c' => c'.nreg kN ≤ 4 ∧
      lblOf c' kN kL = (if c.nreg g < c.nreg zN then addL (lblOf c kN kL) (c.nreg r)
        else lblOf c kN kL) ∧
      (∀ q, ¬ LblR kN kL q → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  obtain ⟨hsN, hsL, hNL, hKN⟩ := lblR_facts
  refine IRS.ite (K := 30) (fun h => ?_) (fun h => ?_)
  · refine (addLab_irs hI (hK.fix hI) hsN hsL hNL hrN hrL hKN hN hW).mono le_rfl ?_
    rintro c' ⟨h1, h2, h3, h4⟩
    exact ⟨h1, by rw [ite_eq_left h]; exact h2, h3, h4⟩
  · exact IRS.skip hI ⟨hN, by rw [ite_eq_right h], fun _ _ => rfl, rfl⟩



/-- **The labels of the loaded auxiliary record.** -/
theorem stLabs_irs (hI : IInv W c₀ c) (hK : Consts c₀) (hN : c.nreg kN ≤ 4)
    (hA1 : c.nreg zA ≤ 1) (hW : 4 ≤ W) :
    IRS P W c₀ stLabs c 70 (fun c' => c'.nreg kN ≤ 4 ∧
      lblOf c' kN kL = (if c.nreg zA = 1 then
        labAdd (lblOf c kN kL) (c.nreg zN) (c.nreg zL) (c.nreg zM) else lblOf c kN kL) ∧
      c'.nreg aF = (if c.nreg zA = 1 then 1 else c.nreg aF) ∧
      (∀ q, ¬ LblR kN kL q → q ≠ aF → c'.nreg q = c.nreg q) ∧ c'.nmem = c.nmem) := by
  have k1 := (hK.fix hI).2.1
  unfold stLabs
  by_cases hz : c.nreg zA < c.nreg K1
  · refine (IRS.ifT hz (IRS.skip (K := 68) hI ⟨hN, ?_, ?_, fun _ _ _ => rfl, rfl⟩)).mono
      (⋄) (fun _ h => h)
    · Ξ ite_eq_right (by rw [k1] at hz; omega)
    · Ξ ite_eq_right (by rw [k1] at hz; omega)
  · have hz1 : c.nreg zA = 1 := by rw [k1] at hz; omega
    refine (IRS.ifF hz ?_).mono (K := 68 + 2) le_rfl (fun _ h => h)
    ϴ hz1, ite_true
    -- set the flag
    refine IRS.seq (K₁ := 1) (K₂ := 67) (IRS.instr1 (i := .constN aF 1) hI
      ⟨iscr_sw (by unfold aF sw; norm_num) (by unfold aF sw; norm_num), ⋄⟩) ?_
    rintro c₁ hI₁ - - hc₁
    have f1 : ∀ q, q ≠ aF → c₁.nreg q = c.nreg q := fun q hq => by
      rw [hc₁]; Θ regI, upd_other _ _ _ hq
    have v1 : c₁.nreg aF = 1 := by rw [hc₁]; Θ regI
    have m1 : c₁.nmem = c.nmem := Ρ hc₁
    have nN : kN ≠ aF := by unfold kN aF sw; omega
    have hlbl1 : lblOf c₁ kN kL = lblOf c kN kL := by
      unfold lblOf
      Ξ f1 _ nN
      refine List.map_congr_left fun i hi => f1 _ ?_
      ϴ' List.mem_range at hi
      unfold kL aF sw; omega
    have zN1 : c₁.nreg zN = c.nreg zN := f1 _ (by unfold zN aF sw; omega)
    have zL1 : c₁.nreg zL = c.nreg zL := f1 _ (by unfold zL aF sw; omega)
    have zM1 : c₁.nreg zM = c.nreg zM := f1 _ (by unfold zM aF sw; omega)
    have k0₁ := (hK.fix hI₁).1
    -- the first label
    refine IRS.seq (K₁ := 32) (K₂ := 32 + 3) (condLab_irs (g := K0) (r := zL) hI₁ hK
      (by rw [f1 _ nN]; exact hN) (by unfold zL kN sw; omega)
      (fun i hi => by unfold zL kL sw; omega) hW) ?_ |>.mono (⋄) (fun _ h => h)
    rintro c₂ hI₂ - - ⟨n2, l2, f2, m2⟩
    have nL : ∀ q, (q = zN ∨ q = zM ∨ q = aF ∨ q = K1) → ¬ LblR kN kL q := by
      rintro q (rfl | rfl | rfl | rfl) <;> Θ LblR, kN, kL, zN, zM, aF, K1, sw
    have k1₂ := (hK.fix hI₂).2.1
    refine (condLab_irs (g := K1) (r := zM) hI₂ hK n2 (by unfold zM kN sw; omega)
      (fun i hi => by unfold zM kL sw; omega) hW).mono (⋄) ?_
    rintro c₃ ⟨n3, l3, f3, m3⟩
    refine ⟨n3, ?_, ?_, fun q hq hqa => ?_, Ρ m3, m2, m1⟩
    · rw [l3, l2, hlbl1, f2 _ (nL _ (Or.inl rfl)), f2 _ (nL _ (Or.inr (Or.inl rfl))), k1₂, k0₁,
        zN1, zL1, zM1]
      unfold labAdd
      rfl
    · rw [f3 _ (nL _ (Or.inr (Or.inr (Or.inl rfl)))), f2 _ (nL _ (Or.inr (Or.inr (Or.inl rfl)))),
        v1]
    · Ξ f3 _ hq, f2 _ hq, f1 _ hqa

/-! ## The state of the stop steps -/

/-- The default record. -/
def d5 : ℕ × ℕ × ℕ × ℕ × ℕ := (0, 0, 0, 0, 0)

/-- **The state of the stop steps**: the stops before `sP` lie at the start key, the label list
holds the labels of the anchored ones (at most two per stop), `aF` says whether one is anchored. -/
def StI (P : Polygon) (J : Merge.Junction) (N₂ : NF) (rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ))
    (c : Config) : Prop :=
  c.nreg kN ≤ 4 ∧ c.nreg sP ≤ 2 ∧ c.nreg sP ≤ rs.length ∧
    (∀ i (hi : i < rs.length), i < c.nreg sP → soff P J rs[i] = Lst J) ∧
    (lblOf c kN kL).length ≤ 2 * c.nreg sP ∧
    (∀ i, i < c.nreg sP → ∀ v ∈ axLabs (ax.getD i d5), v ∈ lblOf c kN kL) ∧
    (∀ v ∈ lblOf c kN kL, v < N₂.nRegions) ∧
    c.nreg aF ≤ 1 ∧ (c.nreg aF = 1 ↔ ∃ i, i < c.nreg sP ∧ (ax.getD i d5).1 = 1)

/-- The registers written by a stop step. -/
def WS (q : ℕ) : Prop :=
  q = zX ∨ q = zE ∨ q = zH ∨ q = zO ∨ q = zO + 1 ∨ q = zA ∨ q = zN ∨ q = zL ∨ q = zM ∨
    LblR kN kL q ∨ q = aF ∨ q = sP

theorem ws_stR {q : ℕ} (h : WS q) : StR q := by
  unfold WS LblR at h
  unfold StR
  ϴ' zX, zE, zH, zO, zA, zN, zL, zM, aF, sP, kE, kH, kN, kL, gN, gR, dF, lC, sw at h ⊢
  omega

theorem lblOf_congrK {c c' : Config} (h : ∀ q, LblR kN kL q → c'.nreg q = c.nreg q) :
    lblOf c' kN kL = lblOf c kN kL := by
  unfold lblOf
  Ξ h kN (Or.inl rfl)
  refine List.map_congr_left fun i hi => h _ (Or.inr ?_)
  ϴ' List.mem_range at hi
  omega

theorem stI_congr {P : Polygon} {J : Merge.Junction} {N₂ : NF} {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)}
    {c c' : Config} (h : StI P J N₂ rs ax c)
    (hr : ∀ q, (LblR kN kL q ∨ q = aF ∨ q = sP) → c'.nreg q = c.nreg q) : StI P J N₂ rs ax c' := by
  have hl := lblOf_congrK (c := c) (c' := c') fun q hq => hr q (Or.inl hq)
  have hN := hr kN (Or.inl (Or.inl rfl))
  have hA := hr aF (Or.inr (Or.inl rfl))
  have hP := hr sP (Or.inr (Or.inr rfl))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨by rw [hN]; exact h1, by rw [hP]; exact h2, by rw [hP]; exact h3,
    fun i hi hi' => h4 i hi (by rw [hP] at hi'; exact hi'), by rw [hl, hP]; exact h5,
    fun i hi v hv => by rw [hl]; exact h6 i (by rw [hP] at hi; exact hi) v hv,
    fun v hv => h7 v (by rw [hl] at hv; exact hv), by rw [hA]; exact h8, by rw [hA, hP]; exact h9⟩

end

end SweepEv

end Chazelle.Core
