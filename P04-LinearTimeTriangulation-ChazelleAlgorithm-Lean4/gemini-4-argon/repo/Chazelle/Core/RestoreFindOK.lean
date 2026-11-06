module

public import Chazelle.Core.RestoreFCostB
public import Chazelle.Core.RestoreFComplete3
public import Chazelle.Core.RestoreDrvPos

/-!
# WP-E, the search on the RAM: `FindOK`

`findS sh cu`: the initialisation, the arc count, and the loops over the ordered pairs of arcs of
the region.  It meets `FindOK` with the cost function `findκ`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim

/-- **The search** (Lemma 3.2). -/
def findS (sh cu : Stmt) : Stmt := .seq fInit (.seq aCntS (outerLoop cu (testS sh)))

/-- The cost function of the search. -/
def findκ (d : ℕ) : ℕ := 10 ^ 10 * (testκ d + 21) * (d + 2) ^ 2

variable {E : FEnv} {c₀ : Config}

/-- The doubled walk length fits the word bound. -/
theorem hnW_of (hE : FGood E c₀) : 2 * E.M.W.n ≤ E.W := by
  have hWh := hE.hWh
  unfold hostWords at hWh
  have hQn : (Qof E.P).n = E.P.n := shear_n _ _
  rcases hE.kind with ⟨C, -, hM⟩ | hM
  · obtain ⟨hz, H, C', hC, hM'⟩ := chainDesc_of hE.hMD hM
    obtain ⟨hl, hHW, -, -⟩ := (hE.hwf.2 hz).2 H C' hC
    have hN := NFLoc.chain_n_le hC hl hHW
    have hm := C'.m_lt
    have hn : E.M.W.n = 2 * C'.m + 7 := by rw [hM']; exact chainModel_n C'
    omega
  · have hn : E.M.W.n = E.P.n := by
      rw [hM]; show (interiorWalk (Qof E.P)).n = _; rw [interiorWalk_n', hQn]
    omega

/-- The arc count is at most the degree bound plus one. -/
theorem kOf_le (hE : FGood E c₀) : kOf E ≤ E.d + 1 := by
  unfold kOf
  split_ifs
  · omega
  · exact region_arcs_le (walkAx_of_goodModel hE.hGM) hE.hNF hE.hdeg hE.hr

/-- **The cost of the search** fits `findκ`. -/
theorem find_cost {t f g h a d k : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g) (hk : k ≤ d + 1) :
    30 + (17 + (((((70 + 11040 + 11040 + 7 + g + 3 +
      ((10 ^ 9 * ((t * (f + 1) + 20) * (h + a + 1)) + 22) * g + 2)) + 3) * k + 4) + 2) * k + 2)) ≤
      10 ^ 10 * (t + 21) * (d + 2) ^ 2 * f * g * (h + a + 1) := by
  set S := h + a + 1 with hS
  have hS1 : 1 ≤ S := by omega
  set T := t * (f + 1) + 20 with hT
  -- the piece bound
  have hTf : T ≤ 2 * (t + 20) * f := by
    rw [hT]; nlinarith
  have hKp : 10 ^ 9 * (T * S) + 22 ≤ 10 ^ 9 * 2 * (t + 21) * f * S := by
    have : T * S ≤ 2 * (t + 20) * f * S := Nat.mul_le_mul_right _ hTf
    nlinarith
  -- the pair bound
  set P := 10 ^ 9 * 2 * (t + 21) * f * S with hP
  have hP1 : 1 ≤ P := by
    rw [hP]; have : 1 ≤ (t + 21) * f * S := Nat.one_le_iff_ne_zero.2 (by positivity)
    nlinarith
  have hpair : 70 + 11040 + 11040 + 7 + g + 3 + ((10 ^ 9 * (T * S) + 22) * g + 2) + 3 ≤
      (P + 22200) * g := by
    have : (10 ^ 9 * (T * S) + 22) * g ≤ P * g := Nat.mul_le_mul_right _ hKp
    nlinarith
  have hk1 : k + 1 ≤ d + 2 := by omega
  -- the loops
  have hloop : 30 + (17 + (((((70 + 11040 + 11040 + 7 + g + 3 +
      ((10 ^ 9 * (T * S) + 22) * g + 2)) + 3) * k + 4) + 2) * k + 2)) ≤
      (P + 22300) * g * (d + 2) ^ 2 := by
    generalize hX : 70 + 11040 + 11040 + 7 + g + 3 + ((10 ^ 9 * (T * S) + 22) * g + 2) = X at hpair ⊢
    set Q := (P + 22200) * g with hQ
    have h1 : (X + 3) * k ≤ Q * k := Nat.mul_le_mul_right _ hpair
    have h2 : ((X + 3) * k + 4 + 2) * k ≤ (Q * k + 6) * k := Nat.mul_le_mul_right _ (by omega)
    have h3 : (Q * k + 6) * k ≤ (Q * (d + 1) + 6) * (d + 1) :=
      Nat.mul_le_mul (by have := Nat.mul_le_mul_left Q hk; omega) hk
    have h4 : (Q * (d + 1) + 6) * (d + 1) + 49 ≤ (P + 22300) * g * (d + 2) ^ 2 := by
      have e : (P + 22300) * g * (d + 2) ^ 2 = Q * (d + 2) ^ 2 + 100 * g * (d + 2) ^ 2 := by
        rw [hQ]; ring
      rw [e]
      have : Q * (d + 1) * (d + 1) ≤ Q * (d + 2) ^ 2 := by
        rw [mul_assoc, ← pow_two]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
      nlinarith
    omega
  calc _ ≤ (P + 22300) * g * (d + 2) ^ 2 := hloop
    _ ≤ 10 ^ 10 * (t + 21) * (d + 2) ^ 2 * f * g * (h + a + 1) := by
      have : P + 22300 ≤ 10 ^ 10 * (t + 21) * f * S := by
        rw [hP]; have : 1 ≤ (t + 21) * f * S := Nat.one_le_iff_ne_zero.2 (by positivity)
        nlinarith
      calc (P + 22300) * g * (d + 2) ^ 2 ≤ 10 ^ 10 * (t + 21) * f * S * g * (d + 2) ^ 2 := by
            gcongr
        _ = _ := by rw [hS]; ring


/-- **The search meets `FindOK`.** -/
theorem findOK_of {sh cu : Stmt} {Bs Bc Bo : Finset ℕ} {F G H : ℕ → ℕ} {X : MemCtx}
    {Ok : Polygon → Model → Prop} (hBo : oracleBands ⊆ Bo) (hB8 : bRestore ∉ Bo)
    (hloc : X.CapLocal) (hhalf : X.Halves)
    (hOkM : ∀ P M, Ok P M → OkModel P M ∨ M = interiorModel (Qof P)) (hBs : Bs ⊆ Bo)
    (hBc : Bc ⊆ Bo) (hsh : ShooterOK sh Bs F X Ok) (hcu : CutterOK cu Bc G H X Ok) :
    FindOK (findS sh cu) findκ F G H X Ok Bo := by
  intro P W c hw pre hroom
  obtain ⟨hG, hWh, hX, hcap, hwf, hreg, hsimp, M, N, hMD, hGM, hOk, hNW, hNF, hdeg, hsg, hr⟩ := pre
  obtain ⟨c₀, k₀, ex₀, hk₀, nm, rr, rm, ro, fr, f07, hE⟩ := find_start hsh hBs hcu hBc hBo hB8
    hloc hhalf hOkM hw hG hWh hX hcap hwf hreg hsimp hMD hGM hOk hNW hNF hdeg hsg hr
  set E := fEnv P W M N X Ok cu (testS sh) Bc Bo F G H testκ c with hEdef
  have hA0 : c₀.nreg ALLOC = c.nreg ALLOC := fr _ (by unfold IniW ALLOC; omega)
  -- the oracles cost at least one step
  have hγ1 : 1 ≤ c.nreg 81003 := one_le_gamma hGM hNF.1 hsg
  obtain ⟨hF1, hG1⟩ := oracle_pos hsh hcu hw hG hWh hX hcap hwf hreg hMD hGM hOk hγ1
    (hw.1 _) (hw.1 _) (hw.1 _)
  -- the bands
  set B := restoreBands ∪ Bo with hBdef
  have hB : dBands ⊆ B := Finset.union_subset_union subset_rfl hBo
  have hBT : restoreBands ∪ E.Bo ⊆ B := subset_rfl
  -- the run from the initialised configuration
  have hI0 : FInv W c₀ c₀ := ⟨ex₀.wb_right, fun _ _ => rfl, le_rfl, fun _ _ => rfl⟩
  have hw0 : FWin E c₀ := ⟨by omega, fun h => absurd h (by omega)⟩
  set k := kOf E with hkdef
  set Kp := pK E with hKpdef
  have hkd : k ≤ c.nreg 81005 + 1 := kOf_le hE
  have hcost := find_cost (t := testκ (c.nreg 81005)) (h := H (c.nreg 81003))
    (a := Nat.clog 2 (c.nreg 81003)) hF1 hG1 hkd
  have hc1 : 30 + (17 + ((outerK E Kp k + 2) * k + 2)) ≤ findκ (c.nreg 81005) *
      F (c.nreg 81003) * G (c.nreg 81003) * (H (c.nreg 81003) + Nat.clog 2 (c.nreg 81003) + 1) :=
    hcost
  have hc2 : c.nreg ALLOC + findκ (c.nreg 81005) * F (c.nreg 81003) * G (c.nreg 81003) *
      (H (c.nreg 81003) + Nat.clog 2 (c.nreg 81003) + 1) ≤ W := hroom
  have hA : ∀ t, t < k → ArcOK E t := fun t ht => by
    have hch : (E.N.region E.r).chords ≠ [] := fun h => by
      rw [hkdef] at ht; unfold kOf at ht; rw [ite_eq_left h] at ht; omega
    have hk' : k = (E.N.region E.r).arcs.length := by rw [hkdef]; unfold kOf; rw [ite_eq_right hch]
    exact hE.arcOK hch (by rw [← hk']; exact ht)
  have hPG : ∀ t, t < k → PGood E c₀ Kp t := fun t ht => by
    have hch : (E.N.region E.r).chords ≠ [] := fun h => by
      rw [hkdef] at ht; unfold kOf at ht; rw [ite_eq_left h] at ht; omega
    have hk' : k = (E.N.region E.r).arcs.length := by rw [hkdef]; unfold kOf; rw [ite_eq_right hch]
    exact pgood_of hE hch (by rw [← hk']; exact ht) k0K_le
      (fun Cα N γ' hQ hcan hγ' hm => k1K_le hE hQ hcan hγ' hm)
  have hrun : FRS B P W c₀ (.seq aCntS (outerLoop cu (testS sh))) c₀
      (17 + ((outerK E Kp k + 2) * k + 2)) (fun c' => FWin E c' ∧
        ∀ i, i < k → ∀ j, j < k → PairDone E c₀ i j (c'.nreg 81007)) := by
    refine FRS.seq (K₁ := 17) (cnt_fs hE hB hI0) (fun c₁ hI₁ hA₁ h₁ => ?_)
    obtain ⟨h30, h32, f₁⟩ := h₁
    have hw₁ : FWin E c₁ := hw0.congr' (fun q a b => f₁ q (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    exact (outerLoop_fs (k := k) hE hB hBT hI₁ hw₁ h32 h30 hA hPG (hnW_of hE)
      (by show c₁.nreg ALLOC + _ ≤ W; rw [hA0] at hA₁; omega)).mono le_rfl
      (fun c' h' => ⟨h'.1, h'.2.2.2⟩)
  obtain ⟨c', k₁, ex₁, hk₁, hI', hrf, hw', hpd⟩ := hrun
  refine ⟨c', k₀ + k₁, .seq ex₀ ex₁, ?_, ⟨fun q h8 hq => ?_, hw'.1, ?_⟩, ?_⟩
  · -- the cost
    show k₀ + k₁ ≤ findκ (c.nreg 81005) * F (c.nreg 81003) * G (c.nreg 81003) *
      (H (c.nreg 81003) + Nat.clog 2 (c.nreg 81003) + 1)
    omega
  · -- the caller's registers
    have h80 : 80000 ≤ q := by unfold bandOf bRestore at h8; omega
    rw [hI'.hin q (by unfold FFix; omega), fr q (by unfold IniW; omega)]
  · -- soundness and completeness
    intro M' N' reg hMD' hNA' hNF' hregs'
    have hMM : M' = M := NFLoc.modelDesc_unique hMD' hMD
    subst hMM
    have hNp : patch N N' = N := nf_patch hNW.nfAt hNA'
    have hregs : NFRegs M' (Qof P) N reg := by
      have : NFRegs M' (Qof P) (patch N N') reg := hregs'
      rwa [hNp] at this
    have hF : N'.F M' (Qof P) = N.F M' (Qof P) := by
      have : (patch N N').F M' (Qof P) = N'.F M' (Qof P) := rfl
      rw [← this, hNp]
    rw [hF]
    exact ⟨fun h1 => hw'.2 h1 reg hregs, fun hfull hdg =>
      find_complete hE hpd hregs hfull hdg⟩
  · -- the frame
    have hf0 : Frame B c c₀ k₀ := ⟨fun r hr _ => fr r (fun h => hr (by
        unfold IniW at h; rw [hBdef]; apply Finset.mem_union_left
        have : bandOf r = bRestore := by unfold bandOf bRestore; omega
        rw [this]; decide)), fun r _ => by rw [rr], fun a _ => by rw [nm],
      fun a _ => by rw [rm], ro, by rw [hA0], by omega⟩
    have hf1 : Frame B c₀ c' k₁ := RF.to_frame hrf
    have := hf0.trans hf1
    rwa [Finset.union_self] at this


/-- **WP-E: the splitting step of Lemma 3.2 exists** (`FindSpec`). -/
theorem findSpec : FindSpec :=
  ⟨findS, findκ, fun _ _ _ _ _ _ _ _ _ _ hBo hB8 hloc hhalf hOkM hBs hBc hsh hcu =>
    findOK_of hBo hB8 hloc hhalf hOkM hBs hBc hsh hcu⟩

end

end Restore

end Chazelle.Core
