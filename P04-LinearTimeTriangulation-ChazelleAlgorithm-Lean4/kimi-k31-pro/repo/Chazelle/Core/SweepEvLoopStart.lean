module

public import Chazelle.Core.SweepEvLoopStartQ
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.ChainTactics
set_option maxHeartbeats 32000000
set_option maxRecDepth 20000

/-!
# The sweep (WP-D), stage 3: the start of the event loop (task L0)

**`loopStartTask : LoopStartTask`**: the program `start` (`SweepEvLoopStartP`), cost
`200000 (TLR + 1)`.  The invariant `LoopInv` at the start key `(cGL, 0)` (offset `Lst`): the stops
of stage 2 (sorted, at most two per offset: `stops_sorted`, `stops_two`), the layout (`PrepOut`,
`StopOut`), the label set (`evInv_start`), the gap regions (`stGap`), the stop pointer past the
stops at the start key (`ptr_char`), the first log record (`LogPre` of one record, `LabIn` by
`labIn_of_evInv`), the measure (`countTask`), the empty table (`PrepOut`).
-/

namespace Chazelle.Core

namespace SweepEv

open Set
open Machine Machine.Stmt Programs SweepIo SweepPrim WalkEmbed SweepRam Sweep
open Chazelle.Chain (SideAttach sidePt)

@[expose] public section

theorem stopData_transport' {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c c' : Config}
    {rs ax : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (h : StopData P J N₂ c rs ax)
    (hsC : c'.nreg sC = c.nreg sC) (hsB : c'.nreg sB = c.nreg sB) (haB : c'.nreg aB = c.nreg aB)
    (hm : ∀ a, ((c.nreg sB ≤ a ∧ a < c.nreg sB + 5 * c.nreg sC) ∨
      (c.nreg aB ≤ a ∧ a < c.nreg aB + 5 * c.nreg sC)) → c'.nmem a = c.nmem a) :
    StopData P J N₂ c' rs ax := by
  obtain ⟨hl, hlax, hSR, hAR, h5, h6, h7, h8⟩ := h
  refine ⟨by rwx [hsC], hlax, fun i hi => ?_, fun i hi => ?_, h5, h6, h7, h8⟩
  · rw [hsB, hm _ (Or.inl (by omega)), hm _ (Or.inl (by omega)), hm _ (Or.inl (by omega)),
      hm _ (Or.inl (by omega)), hm _ (Or.inl (by omega))]
    exact hSR i hi
  · rw [haB, hm _ (Or.inr (by omega)), hm _ (Or.inr (by omega)), hm _ (Or.inr (by omega)),
      hm _ (Or.inr (by omega)), hm _ (Or.inr (by omega))]
    exact hAR i hi

theorem stopOff_eq {P : Polygon} {J : Merge.Junction} {c : Config}
    {rs : List (ℕ × ℕ × ℕ × ℕ × ℕ)} (hSR : StopRecsAt c.nmem (c.nreg sB) rs) {i : ℕ}
    (hi : i < rs.length) : stopOff P J c i = soff P J rs[i] := by
  obtain ⟨h1, h2, -⟩ := hSR i hi
  rw [List.getD_eq_getElem _ _ hi] at h1 h2
  unfold stopOff stopE stopH offK soff oW
  rw [h1, h2]
  rfl

theorem lblOf_mem {c : Config} {v : ℕ} (h : v ∈ lblOf c kN kL) :
    ∃ t, t < min (c.nreg kN) 4 ∧ v = c.nreg (kL + t) := by
  unfold lblOf at h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact ⟨t, List.mem_range.1 ht, rfl⟩

theorem mem_curLab {P : Polygon} {J : Merge.Junction} {N₂ : NF} {c : Config} {v : ℕ}
    (h : v ∈ lblOf c kN kL) : regOf (chainModel J.right) (Qof P) N₂ v ∈ curLab P J N₂ c := by
  obtain ⟨t, ht, rfl⟩ := lblOf_mem h
  refine ⟨c.nreg (kL + t), ?_, rfl⟩
  have : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · left; exact ⟨by omega, rfl⟩
  · right; left; exact ⟨by omega, rfl⟩
  · right; right; left; exact ⟨by omega, rfl⟩
  · right; right; right; exact ⟨by omega, rfl⟩

/-- **Task L0: the start of the event loop.** -/
theorem loopStartTask : LoopStartTask := by
  refine ⟨start, fun _ => 200000, ?_⟩
  intro sh Bs F X Ok P W c₀ c₁ c J N₁ N₂ E hPrep hStop hI hroom
  obtain ⟨rs, ax, hl, hlax, hSR, hAR, hst, hw, haux, hlen, hsB1, hsB2, haB1, haB2, hm1, hfr1⟩ :=
    hStop
  obtain ⟨hflag, hlay1, hlC, hlay2, hm0, hfr0⟩ := hPrep
  have hSD : StopData P J N₂ c rs ax := ⟨hl, hlax, hSR, hAR, hst, hw, haux, hlen⟩
  have hP := E.hP
  have hNF := E.hNF₂
  set S₂ := N₂.F (chainModel J.right) (Qof P) with hS₂d
  have hS₂ : S₂ ⊆ Merge.augChords J.right := hNF.1.2.1
  have hS₂f : S₂.Finite := hNF.1.1
  -- registers of `c`
  have hlBc : c.nreg lB = c₁.nreg lB := hfr1 _ (not_oracle_sw (by simp [lB, sw])
    (by simp [lB, sw])) (by unfold S2R; simp [lB, sw]) (by simp [lB, ALLOC, sw])
  have hTB : c.nreg cTB = c₀.nreg cTB := hI.hin _ (by ufo IFix cTB sw)
  have hTB₀ : c₀.nreg cTB = c₀.nreg ALLOC := E.hTA
  have hlay : c.nreg sB + 5 * c.nreg sC ≤ c.nreg ALLOC ∧
      c.nreg aB + 5 * c.nreg sC ≤ c.nreg ALLOC := by rw [← hl]; exact ⟨hsB2, haB2⟩
  have hlB : c₀.nreg ALLOC ≤ c.nreg lB := by rwo [hlBc]
  have hlogB : c.nreg lB + 7 * logCap N₁ N₂ ≤ c₁.nreg ALLOC := by ruo [hlBc] logCap
  have hcap7 : 7 ≤ 7 * logCap N₁ N₂ := by ufo logCap
  have hlB7 : c.nreg lB + 7 ≤ c.nreg ALLOC := by omega
  -- the run
  have hroom' : c.nreg ALLOC + 200000 * (c₀.nreg TLR + 1) ≤ W := hroom
  refine (start_irs E hI hSD hlay hlB hlB7 (by have := startK_le (c₀.nreg TLR); omega)).mono
    (startK_le _) ?_
  rintro c' ⟨kE', kH', dF', lC', sPl, hptr, kN4, lreg, hΛ, hB, gN2, gR', gap, r0, r1, r2, r3, mem,
    fr, hA⟩
  -- registers kept
  have keep : ∀ j, j < 10000 → ¬ StR (sw j) → c'.nreg (sw j) = c.nreg (sw j) := by
    intro j hj h
    have h1 : 240000 ≤ sw j := by unfold sw; exact Nat.le_add_right _ _
    have h2 : sw j < 250000 := by ufo sw
    have h3 : sw j ≠ ALLOC := by ufo ALLOC
    exact fr (sw j) (not_oracle_sw h1 h2) h h3
  have nS : ∀ j, (j = 2600 ∨ j = 2601 ∨ j = 2602 ∨ j = 2430 ∨ j = 661) → ¬ StR (sw j) := by
    rintro j (rfl | rfl | rfl | rfl | rfl) <;> unfold StR <;>
      simp [kE, kH, kN, kL, gN, gR, sP, dF, lC, sw]
  have sB' : c'.nreg sB = c.nreg sB := keep 2600 (by norm_num) (nS _ (by norm_num))
  have sC' : c'.nreg sC = c.nreg sC := keep 2601 (by norm_num) (nS _ (by norm_num))
  have aB' : c'.nreg aB = c.nreg aB := keep 2602 (by norm_num) (nS _ (by norm_num))
  have lB' : c'.nreg lB = c.nreg lB := keep 2430 (by norm_num) (nS _ (by norm_num))
  have TB' : c'.nreg cTB = c.nreg cTB := keep 661 (by norm_num) (nS _ (by norm_num))
  -- the stop data
  have hSD' : StopData P J N₂ c' rs ax := stopData_transport' hSD sC' sB' aB' (fun a ha =>
    mem a (by omega) (Or.inr (by omega)))
  have hSR' : StopRecsAt c'.nmem (c'.nreg sB) rs := hSD'.2.2.1
  have hlen' : rs.length = c'.nreg sC := hSD'.1
  -- the start key
  obtain ⟨hpw, hoK, -⟩ := startMathTask P J N₂ hP hNF
  have hkey : keyOff P J c' = Lst J := by
    unfold keyOff
    rw [kE', kH']
    have : offK P J (pK0 J) 0 = oW J (((pK0 J : ℕ) : ℝ) + 0) := by ufr offK oW
    rw [this]; unfold pK0; exact_mod_cast hoK
  have hge : ∀ i (hi : i < rs.length), (Lst J : ℝ) ≤ soff P J rs[i] := fun i hi =>
    (stop_facts hst hi).2.2.2
  -- the label set
  obtain ⟨hRC, -⟩ := regOf_spec hNF
  have hinv : EvInv J S₂ (Lst J) (curLab P J N₂ c') := by
    refine evInv_start hP hNF hlax hst (fun i hi => ?_) (fun i hi hik hia => ?_) (fun hall => ?_)
    · have := haux i hi
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at this
      exact this
    · rintro _ ⟨l, hl', rfl⟩
      have hx := haux i hi
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at hx
      have hnl : (ax[i]'(by omega)).2.1 ≤ 2 := hx.2.2.1
      have hl'' : l ∈ axLabs (ax.getD i d5) := by
        rw [List.getD_eq_getElem _ _ (show i < ax.length by omega)]
        unfold axLabs
        rw [ite_eq_left hia]
        rcases hl' with ⟨h0, rfl⟩ | ⟨h1, rfl⟩ | ⟨h2, rfl⟩ | ⟨h3, rfl⟩
        · simp [h0]
        · simp [h1]
        · omega
        · omega
      exact mem_curLab (hΛ i hi hik (by rwx [List.getD_eq_getElem _ _ (by omega)]) l hl'')
    · obtain ⟨h1, h2, h3⟩ := hB (fun i hi hik => by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact hall i hi hik)
      refine ⟨regOf (chainModel J.right) (Qof P) N₂ (c'.nreg kL), hRC.1 _ h2, h3, ?_⟩
      ext V
      simp only [curLab, labSet, h1, Set.mem_image, mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨l, hl', rfl⟩
        rcases hl' with ⟨-, rfl⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
        · rfl
        all_goals omega
      · rintro rfl; exact ⟨c'.nreg kL, Or.inl ⟨by omega, rfl⟩, rfl⟩
  have hinv' : EvInv J S₂ (keyOff P J c') (curLab P J N₂ c') := by rwx [hkey]
  -- the labels are region indices
  have hlabR : ∀ i, i < c'.nreg kN → c'.nreg (kL + i) < N₂.nRegions := fun i hi =>
    lreg _ (List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩)
  -- the log record
  set rec : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ := (c'.nreg kE, c'.nreg kH, c'.nreg kN, c'.nreg kL,
    c'.nreg (kL + 1), c'.nreg (kL + 2), c'.nreg (kL + 3)) with hrec
  have hpar0 : (chainModel J.whole).param (Qof P) ⟨pK0 J, 0⟩ = 0 := rfl
  have hoW : oW J (((pK0 J : ℕ) : ℝ) + (chainModel J.whole).param (Qof P) ⟨pK0 J, 0⟩) = Lst J := by
    rw [hpar0]; unfold pK0; exact_mod_cast hoK
  refine ⟨⟨⟨rs, ax, hSD'⟩, fun i i' hii hi' => ?_, fun i hi => ?_, by rw [TB', hTB, hTB₀],
    by rwx [TB', lB', hTB, hlBc], ?_, ?_, ?_, ?_,
    by rwx [kE', kH'], by rw [hkey], kN4, hlabR, hinv', gN2, gR', gap,
    by rw [sC', ← hl]; exact sPl, fun i hi => ?_, ⟨[rec], by rwr [lC'],
      ?_, ?_, ?_, rfl⟩, ?_, ?_, dF'⟩, fr, fun x hx hx' => mem x hx hx'⟩
  · rw [stopOff_eq hSR' (by omega), stopOff_eq hSR' (by omega)]
    exact stops_sorted hst hii (by omega)
  · rw [stopOff_eq hSR' (by omega), stopOff_eq hSR' (by omega)]
    exact stops_two hP hNF hst (by omega)
  · ruo [lB', sB', hlBc] logCap
  · ruo [lB', aB', hlBc] logCap
  · rwo [sB', sC', ← hl]
  · rwo [aB', sC', ← hl]
  · have hi' : i < rs.length := by omega
    rw [stopOff_eq hSR' hi', hkey, hptr i hi']
    have := hge i hi'
    constructor
    · intro h; rw [h]
    · intro h; linarith
  · -- the record in memory
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst hi0
    rw [lB']
    simp only [List.getD_cons_zero, Nat.mul_zero, Nat.add_zero, hrec]
    refine ⟨r0, r1, r2, ?_, ?_, ?_, ?_⟩
    · have := r3 0 (by norm_num); simpa using this
    · have := r3 1 (by norm_num); rw [show c.nreg lB + 3 + 1 = c.nreg lB + 4 by omega] at this
      exact this
    · have := r3 2 (by norm_num); rw [show c.nreg lB + 3 + 2 = c.nreg lB + 5 by omega] at this
      exact this
    · have := r3 3 (by norm_num); rw [show c.nreg lB + 3 + 3 = c.nreg lB + 6 by omega] at this
      exact this
  · -- the word facts
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    simp only [hrec]
    refine ⟨by rwx [kE', kH'], kN4, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · simpa using hlabR 0 h
    · exact hlabR 1 h
    · exact hlabR 2 h
    · exact hlabR 3 h
  · -- the log so far
    have hlog : logOf J (Qof P) N₂ [rec] = [((pK0 J : ℕ), (chainModel J.whole).param (Qof P)
        ⟨pK0 J, 0⟩, curLab P J N₂ c')] := by
      simp only [logOf, List.map_cons, List.map_nil, hrec, kE', kH']
      rfl
    rw [hlog]
    refine ⟨by simp, ?_, ?_, List.pairwise_singleton _ _, fun i hi => by simp at hi, ?_⟩
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      refine ⟨hpw.1, hpw.2.1.1, hpw.2.1.2.1, ?_⟩
      simp only
      rw [hoW]
    · intro x hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hx
      subst hx
      exact hoW
    · intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      exact labIn_of_evInv hP hS₂ hS₂f hpw.1 hpw.2.1.1 hpw.2.1.2.1 (by rwx [hoW])
  · -- the measure
    rw [lC']
    have hfin := (countTask P J N₁ N₂ hP E.hNF₁ hNF).1
    have := Set.ncard_le_ncard (Set.inter_subset_left (s := keyS P J N₁ N₂)
      (t := Ioi (keyOff P J c'))) hfin
    omega
  · -- the table
    intro j hj
    have hz : c'.nmem (c'.nreg cTB + 3 * j) = 0 := by
      rw [TB', hTB, mem _ (by omega) (Or.inl (by rwo [hlBc])), hm1 _ (by omega)]
      exact hflag j hj
    rw [hz]
    refine ⟨by norm_num, fun h => absurd h (by norm_num), fun _ _ p t _ _ hlt hle => ?_⟩
    rw [hkey] at hle
    exact absurd hlt (not_lt.2 hle)

end

end SweepEv

end Chazelle.Core
