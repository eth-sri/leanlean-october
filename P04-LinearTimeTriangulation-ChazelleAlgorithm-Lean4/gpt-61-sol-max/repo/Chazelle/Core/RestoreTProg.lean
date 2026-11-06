module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreTRunB
public import Chazelle.Core.RestoreTCount
public import Chazelle.Core.RestoreTValid2
public import Chazelle.Core.RestoreTLeft
public import Chazelle.Core.RestoreTDir
public import Chazelle.Core.RestoreTSetup

/-!
# WP-E, the candidate test on the RAM: the program

```
testS sh = tSetup; tInit; validS;
           if valid then (arcBuild; holeS; shPrep; shot; hitCp;
                          if hit then (tArr; countS; if succ then writeT))
```

This file defines the program and proves the run lemmas of its stages.

* `postHit_rs`: after a hit, the arrival step, the count test and the chord triple.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim SignK NFLoc ShotList ShotListG

/-! ## The program -/

/-- The output bits `hit` and `succ` start at `0`. -/
def tInit : Stmt := .seq (.instr (.constN 83011 0)) (.instr (.constN 83014 0))

/-- The chord triple: the height vertex, then the left and the right walk edge (the candidate's
edge first for a ray to the right). -/
def writeT : Stmt := .seq (.instr (.copyN 83015 83007))
  (.ifLtN 83022 83008 (.seq (.instr (.copyN 83016 83005)) (.instr (.copyN 83017 83012)))
    (.seq (.instr (.copyN 83016 83012)) (.instr (.copyN 83017 83005))))

/-- After a hit: the arrival position, the count test, the chord triple. -/
def postHit : Stmt := .seq tArr (.seq (countS gKey) (.ifLtN 83022 83014 writeT .skip))

/-- The hit bit and the arrival position of the wrapper. -/
def hitCp : Stmt := .seq (.instr (.copyN 83011 84020))
  (.seq (.instr (.copyN 83012 84021)) (.instr (.copyN 83013 84022)))

/-- The shot part of the test. -/
def shotA (sh : Stmt) : Stmt :=
  .seq arcBuild (.seq holeS (.seq shPrep (.seq (shotListG gKey xcR sh RS0) hitCp)))

/-- **The candidate test.** -/
def testS (sh : Stmt) : Stmt :=
  .seq tSetup (.seq tInit (.seq (validS gKey gLeft tTurnN tTurnP)
    (.ifLtN 83022 83010 (.seq (shotA sh) (.ifLtN 83022 83011 postHit .skip)) .skip)))

variable {P : Polygon} {W : ℕ} {M : Model} {N : NF} {c₀ c : Config}

/-! ## The chord triple -/

theorem scr_out {r : ℕ} (h1 : 83010 ≤ r) (h2 : r < 83020) : Scr r := by omega_nf

/-- **The chord triple.** -/
theorem writeT_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ writeT c 6 (fun c' => c'.nreg 83015 = c₀.nreg 83007 ∧
      (c₀.nreg 83008 = 1 → c'.nreg 83016 = c₀.nreg 83005 ∧ c'.nreg 83017 = c.nreg 83012) ∧
      (c₀.nreg 83008 ≠ 1 → c'.nreg 83016 = c.nreg 83012 ∧ c'.nreg 83017 = c₀.nreg 83005) ∧
      Agr c c' [83015, 83016, 83017]) := by
  have i05 : c.nreg 83005 = c₀.nreg 83005 := hI.hin _ (by norm_num) (by norm_num)
  have i07 : c.nreg 83007 = c₀.nreg 83007 := hI.hin _ (by norm_num) (by norm_num)
  have i08 : c.nreg 83008 = c₀.nreg 83008 := hI.hin _ (by norm_num) (by norm_num)
  have hσ := hE.hσ
  refine RS.seq (K₂ := 5) (RS.copy hI (r := 83015) (a := 83007)
    (scr_out (by norm_num) (by norm_num))) (fun c₁ hI₁ _ h₁ => ?_)
  
  have k₁ : ∀ r, r ≠ 83015 → c₁.nreg r = c.nreg r := fun r hr => by simp_all
  by_cases hs : c₀.nreg 83008 = 1
  · have g : c₁.nreg 83022 < c₁.nreg 83008 := by
      rw [k₁ _ (by norm_num), k₁ _ (by norm_num), hI.h22, i08, hs]; omega
    refine (RS.ifT g (RS.seq (K₂ := 1) (RS.copy hI₁ (r := 83016) (a := 83005)
      (scr_out (by norm_num) (by norm_num))) (fun c₂ hI₂ _ h₂ => ?_))).mono (by norm_num)
      (fun _ h => h)
    refine (RS.copy hI₂ (r := 83017) (a := 83012) (scr_out (by norm_num) (by norm_num))).mono
      le_rfl (fun c₃ h₃ => ?_)
    have k₂ : ∀ r, r ≠ 83016 → c₂.nreg r = c₁.nreg r := fun r hr => by simp_all
    refine ⟨by simp_all, fun _ => ⟨?_, ?_⟩,
      fun h => absurd hs h, fun q _ _ hq => ?_⟩
    · simp_all
    · simp_all
    simp_all
  · have g : ¬ c₁.nreg 83022 < c₁.nreg 83008 := by
      grind
    refine (RS.ifF g (RS.seq (K₂ := 1) (RS.copy hI₁ (r := 83016) (a := 83012)
      (scr_out (by norm_num) (by norm_num))) (fun c₂ hI₂ _ h₂ => ?_))).mono (by norm_num)
      (fun _ h => h)
    refine (RS.copy hI₂ (r := 83017) (a := 83005) (scr_out (by norm_num) (by norm_num))).mono
      le_rfl (fun c₃ h₃ => ?_)
    have k₂ : ∀ r, r ≠ 83016 → c₂.nreg r = c₁.nreg r := fun r hr => by simp_all
    refine ⟨by simp_all, fun h => absurd h hs,
      fun _ => ⟨?_, ?_⟩, fun q _ _ hq => ?_⟩
    · simp_all
    · simp_all
    simp_all


/-! ## After a hit -/

/-- The cost bound of the post-hit stage for a region with `D` exit chords. -/
def postHitK (D : ℕ) : ℕ := 35012 + (countK 11010 D + 8)

/-- **After a hit**: from the returned position of the far end, the arrival position (chain
models), the count test at it, and the chord triple on success.  Registers `83010`, `83011` are
unchanged. -/
theorem postHit_rs (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hp : ProperPos M (Qof P) P.n ⟨c.nreg 83012, c.nreg 83013⟩) (he : c.nreg 83012 < M.W.n)
    (hy : ∀ C : Chain, M = chainModel C →
      |(M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩).2| < C.radius)
    (hex : ∀ C : Chain, M = chainModel C → ∃ p t, Sweep.Arrival M.W
      (M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩) (dirOf (c₀.nreg 83008)) p t)
    (hroom : c.nreg ALLOC + postHitK (N.region (c₀.nreg 83002)).chords.length ≤ W) :
    RS P W c₀ postHit c (postHitK (N.region (c₀.nreg 83002)).chords.length) (fun c' =>
      ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧ c'.nreg 83012 < M.W.n ∧
      M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ = M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩ ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        (M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩) (dirOf (c₀.nreg 83008)) (c'.nreg 83012)
        (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)) ∧
      (M = interiorModel (Qof P) → c'.nreg 83012 = c.nreg 83012 ∧ c'.nreg 83013 = c.nreg 83013) ∧
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀))
          (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)
          (M.key (Qof P) (xOf c₀)) (chordAt N (c₀.nreg 83002) t))
          (N.region (c₀.nreg 83002)).chords.length) ∧
      (c'.nreg 83014 = 1 → c'.nreg 83015 = c₀.nreg 83007 ∧
        (c₀.nreg 83008 = 1 → c'.nreg 83016 = c₀.nreg 83005 ∧ c'.nreg 83017 = c'.nreg 83012) ∧
        (c₀.nreg 83008 ≠ 1 → c'.nreg 83016 = c'.nreg 83012 ∧ c'.nreg 83017 = c₀.nreg 83005)) ∧
      c'.nreg 83010 = c.nreg 83010 ∧ c'.nreg 83011 = c.nreg 83011) := by
  unfold postHitK at hroom ⊢
  refine RS.seq (tArr_rs hE hI hp he hy hex (by omega)) (fun c₁ hI₁ hA₁ h₁ => ?_)
  obtain ⟨p₁, e₁, q₁, arr₁, int₁, ag₁⟩ := h₁
  have hf : PosG M (Qof P) P.n ⟨c₁.nreg 83012, c₁.nreg 83013⟩ :=
    posG_of_band e₁ p₁ (fun C hM => by simp_all +arith)
  refine RS.seq (count_rs gKey_ok hE hf hI₁ rfl rfl (by omega)) (fun c₂ hI₂ hA₂ h₂ => ?_)
  obtain ⟨b14, i14, ag₂⟩ := h₂
  have k₂ : ∀ r, r ∈ [83010, 83011, 83012, 83013] → c₂.nreg r = c₁.nreg r := fun r hr =>
    ag₂ r (by grind) (by grind) (by simp [countW] at hr ⊢; omega)
  have k₁ : ∀ r, r ∈ [83010, 83011] → c₁.nreg r = c.nreg r := fun r hr =>
    ag₁ r (by grind) (by grind) (by grind)
  have r12 : c₂.nreg 83012 = c₁.nreg 83012 := k₂ _ (by simp)
  have r13 : c₂.nreg 83013 = c₁.nreg 83013 := k₂ _ (by simp)
  have r10 : c₂.nreg 83010 = c.nreg 83010 := by grind
  have r11 : c₂.nreg 83011 = c.nreg 83011 := by grind
  -- the facts of the far end at `c₂`
  have F : ∀ c' : Config, (∀ r, r ∈ [83010, 83011, 83012, 83013, 83014] → c'.nreg r = c₂.nreg r) →
      ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧ c'.nreg 83012 < M.W.n ∧
      M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ = M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩ ∧
      (∀ C : Chain, M = chainModel C → Sweep.Arrival M.W
        (M.pos (Qof P) ⟨c.nreg 83012, c.nreg 83013⟩) (dirOf (c₀.nreg 83008)) (c'.nreg 83012)
        (M.param (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)) ∧
      (M = interiorModel (Qof P) → c'.nreg 83012 = c.nreg 83012 ∧
        c'.nreg 83013 = c.nreg 83013) ∧
      c'.nreg 83014 ≤ 1 ∧
      (c'.nreg 83014 = 1 ↔
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) (xOf c₀))
          (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩) (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length ∧
        2 ≤ cntP (fun t => SideHit M P N (M.key (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩)
          (M.key (Qof P) (xOf c₀)) (chordAt N (c₀.nreg 83002) t)) (N.region (c₀.nreg 83002)).chords.length) ∧
      c'.nreg 83010 = c.nreg 83010 ∧ c'.nreg 83011 = c.nreg 83011 := by
    intro c' hc
    rw [hc 83012 (by simp), hc 83013 (by simp), hc 83014 (by simp), hc 83010 (by simp),
      hc 83011 (by simp), r12, r13, r10, r11]
    grind
  by_cases hs : c₂.nreg 83014 = 1
  · have g : c₂.nreg 83022 < c₂.nreg 83014 := by
      rw [hI₂.h22, hs]; omega
    refine (RS.ifT g (writeT_rs hE hI₂)).mono (by omega) (fun c₃ h₃ => ?_)
    obtain ⟨w15, w1, w2, ag₃⟩ := h₃
    have k₃ : ∀ r, r ∈ [83010, 83011, 83012, 83013, 83014] → c₃.nreg r = c₂.nreg r :=
      fun r hr => ag₃ r (by simp at hr; omega) (by simp at hr; omega) (by simp at hr ⊢; omega)
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := F c₃ k₃
    have e12 : c₃.nreg 83012 = c₂.nreg 83012 := k₃ _ (by simp)
    refine ⟨f1, f2, f3, f4, f5, f6, f7, fun _ => ⟨w15, fun h => ?_, fun h => ?_⟩, f8, f9⟩
    · omega
    grind
  · have g : ¬ c₂.nreg 83022 < c₂.nreg 83014 := by
      omega
    refine (RS.ifF g (RS.skip (K := 0) (Q := fun c' => c' = c₂) hI₂ rfl)).mono (by omega)
      (fun c₃ h₃ => ?_)
    rw [h₃]
    grind


/-! ## The start -/

theorem tInit_rs (_hE : TGood P W M N c₀) (hI : TInv W c₀ c) :
    RS P W c₀ tInit c 2 (fun c' => c'.nreg 83011 = 0 ∧ c'.nreg 83014 = 0 ∧
      Agr c c' [83011, 83014]) := by
  refine RS.seq (K₂ := 1) (RS.const hI (r := 83011) (scr_out (by norm_num) (by norm_num))
    (Nat.zero_le _))
    (fun c₁ hI₁ _ h₁ => ?_)
  refine (RS.const hI₁ (r := 83014) (scr_out (by norm_num) (by norm_num)) (Nat.zero_le _)).mono
    le_rfl (fun c₂ h₂ => ⟨?_, ?_, fun q _ _ hq => ?_⟩)
  all_goals simp_all

/-! ## The shot stage -/

theorem holeList_congr {c c' : Config} (h : ∀ r, 84009 ≤ r → r ≤ 84015 → c'.nreg r = c.nreg r) :
    ShotList.holeList c' 84000 = ShotList.holeList c 84000 := by
  unfold ShotList.holeList
  rw [show c'.nreg (84000 + 9) = c.nreg (84000 + 9) from h _ (by norm_num) (by norm_num)]
  apply List.map_congr_left
  grind [List.mem_range, ShotList.holeAt]

theorem holeOut_congr {Q : Polygon} {z : Point} {c c' : Config}
    (h : ∀ r, 84009 ≤ r → r ≤ 84015 → c'.nreg r = c.nreg r) (ho : HoleOut M Q c z) :
    HoleOut M Q c' z := by
  obtain ⟨h9, hb, hcov, hnear⟩ := ho
  have hl := holeList_congr h
  refine ⟨by simp_all, fun j hj => ?_, by simp_all,
    by simp_all⟩
  grind

/-- The registers `hitCp` writes. -/
def hitW : List ℕ := [83011, 83012, 83013]

theorem hitCp_rs (hI : TInv W c₀ c) :
    RS P W c₀ hitCp c 3 (fun c' => c'.nreg 83011 = c.nreg 84020 ∧ c'.nreg 83012 = c.nreg 84021 ∧
      c'.nreg 83013 = c.nreg 84022 ∧ Out c c' hitW) := by
  obtain ⟨c₁, e₁, v₁, o₁⟩ := out_instr (P := P) (Exec.copyN hI.hw 83011 84020)
  obtain ⟨c₂, e₂, v₂, o₂⟩ := out_instr (P := P) (Exec.copyN e₁.wb_right 83012 84021)
  obtain ⟨c₃, e₃, v₃, o₃⟩ := out_instr (P := P) (Exec.copyN e₂.wb_right 83013 84022)
  have ho : Out c c₃ hitW := ((o₁.trans o₂).trans o₃).mono (fun r hr => by
    simp_all [hitW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] )
  refine RS.out hI (fun r hr => by
      simp_all [hitW, List.mem_cons, List.not_mem_nil, or_false, Scr] <;> omega_nf)
    (.seq e₁ (.seq e₂ e₃)) (by omega) ho ⟨?_, ?_, ?_, ho⟩
  · rw [o₃.1 _ (by simp), o₂.1 _ (by simp), v₁]
  · rw [o₃.1 _ (by simp), v₂, o₁.1 _ (by simp)]
  · rw [v₃, o₂.1 _ (by simp), o₁.1 _ (by simp)]

/-- The cost bound of the shot stage. -/
def shotAK (Fg A : ℕ) : ℕ := buildK A + (100 + (9 + (shotCostG Fg shK A + 3)))

/-- **The result of the shot stage** from the start `c₀`, at `c'`: the hit bit, and a set `A`
between the arc points outside the holes and all arc points (for an array listing the arcs of
the region and holes near the candidate) on which the ray first hits at the arrival position, or
which it misses. -/
def ShotRes (P : Polygon) (M : Model) (N : NF) (c₀ c' : Config) : Prop :=
  c'.nreg 83011 ≤ 1 ∧
    ∃ (m : ℕ → ℕ) (B : ℕ) (hs : List (WPos × WPos)) (A : Set Point),
      (∀ j, j < (N.region (c₀.nreg 83002)).arcs.length →
        ShotList.arcAt m B j = nArc M (Qof P) N (c₀.nreg 83002) j) ∧
      Near M (Qof P) hs (M.pos (Qof P) (xOf c₀)) ∧
      loSet M (Qof P) m B (N.region (c₀.nreg 83002)).arcs.length hs ⊆ A ∧
      A ⊆ hiSet M (Qof P) m B (N.region (c₀.nreg 83002)).arcs.length ∧
      (c'.nreg 83011 = 1 → ∃ t, FirstHit A (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t ∧
        ProperPos M (Qof P) P.n ⟨c'.nreg 83012, c'.nreg 83013⟩ ∧ c'.nreg 83012 < M.W.n ∧
        M.pos (Qof P) ⟨c'.nreg 83012, c'.nreg 83013⟩ =
          Visibility.rayPt (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)) t) ∧
      (c'.nreg 83011 ≠ 1 → NoHit A (M.pos (Qof P) (xOf c₀)) (dirOf (c₀.nreg 83008)))

/-- **The shot stage.** -/
theorem shotA_rsb {X : MemCtx} {Ok : Polygon → Model → Prop} {sh : Stmt} {Bs Bo : Finset ℕ}
    {F : ℕ → ℕ} (hE : TGood P W M N c₀) (hI : TInv W c₀ c)
    (hX : X.holds P c₀.nmem (c₀.nreg 83004) (c₀.nreg ALLOC))
    (hcap : c₀.nreg 83003 ≤ X.cap P c₀.nmem (c₀.nreg 83004)) (hXl : X.CapLocal) (hOk : Ok P M)
    (hne : (N.F M (Qof P)).Nonempty) (hsg : M.Semigranular (N.F M (Qof P)) (c₀.nreg 83003))
    (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ Bo) (hB8 : bRestore ∉ Bo)
    (hBo : oracleBands ⊆ Bo)
    (hroom : c.nreg ALLOC +
      shotAK (F (c₀.nreg 83003)) (N.region (c₀.nreg 83002)).arcs.length ≤ W) :
    RSB (dBands ∪ Bo) P W c₀ (shotA sh) c
      (shotAK (F (c₀.nreg 83003)) (N.region (c₀.nreg 83002)).arcs.length)
      (fun c' => ShotRes P M N c₀ c' ∧ c'.nreg 83010 = c.nreg 83010 ∧
        c'.nreg 83014 = c.nreg 83014) := by
  set K := (N.region (c₀.nreg 83002)).arcs.length with hK
  have h4K : 4 * K ≤ buildK K := by omega_nf
  unfold shotAK at hroom ⊢
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (arcBuild_rs hE hne hI (by grind)))
    (fun c₁ hI₁ hA₁ h₁ => ?_)
  obtain ⟨b81, bA, b31, barr, ag₁⟩ := h₁
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (holeS_rs hE hI₁))
    (fun c₂ hI₂ hA₂ h₂ => ?_)
  obtain ⟨hho, o₂⟩ := h₂
  refine RSB.seq (RSB.of_RS Finset.subset_union_left (shPrep_rs hE hI₂))
    (fun c₃ hI₃ hA₃ h₃ => ?_)
  obtain ⟨hcp, h03, o₃⟩ := h₃
  -- the registers of the shot block
  have cp : ∀ p ∈ shL, c₃.nreg p.1 = c₂.nreg p.2 := hcp
  have in2 : ∀ q, 80000 ≤ q → q < 83010 → c₂.nreg q = c₀.nreg q := hI₂.hin
  have k12 : ∀ r, r ∉ holeL → c₂.nreg r = c₁.nreg r := o₂.1
  have hA21 : c₂.nreg ALLOC = c₁.nreg ALLOC := k12 _ (by simp [holeL, chainHL, ALLOC])
  have hA32 : c₃.nreg ALLOC = c₂.nreg ALLOC := o₃.1 _ (by simp [shW, ALLOC])
  have hm21 : c₂.nmem = c₁.nmem := o₂.2.2.1
  have hm32 : c₃.nmem = c₂.nmem := o₃.2.2.1
  have h00 : c₃.nreg 84000 = c₀.nreg 83000 := by
    rw [cp (84000, 83000) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have h01 : c₃.nreg 84001 = c.nreg ALLOC := by
    rw [cp (84001, 83081) (by simp [shL]), k12 _ (by simp [holeL, chainHL]), b81]
  have h02 : c₃.nreg 84002 = K := by
    rw [cp (84002, 83031) (by simp [shL]), k12 _ (by simp [holeL, chainHL]), b31]
  have h04 : c₃.nreg 84004 = c₀.nreg 83005 := by
    rw [cp (84004, 83005) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have h05 : c₃.nreg 84005 = c₀.nreg 83006 := by
    rw [cp (84005, 83006) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have h06 : c₃.nreg 84006 = c₀.nreg 83008 := by
    rw [cp (84006, 83008) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have h07 : c₃.nreg 84007 = c₀.nreg 83003 := by
    rw [cp (84007, 83003) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have h08 : c₃.nreg 84008 = c₀.nreg 83004 := by
    rw [cp (84008, 83004) (by simp [shL]), in2 _ (by norm_num) (by norm_num)]
  have hB : c.nreg ALLOC + 4 * K ≤ c₃.nreg ALLOC := by omega
  have harr : ∀ j, j < K → ShotList.arcAt c₃.nmem (c.nreg ALLOC) j =
      nArc M (Qof P) N (c₀.nreg 83002) j := fun j hj => by grind
  have hho₃ : HoleOut M (Qof P) c₃ (M.pos (Qof P) ⟨c₀.nreg 83005, c₀.nreg 83006⟩) :=
    holeOut_congr (fun r h1 h2 => o₃.1 r (by simp [shW]; omega)) hho
  have hpre := shotPre_of (X := X) (Ok := Ok) hE hI₃ hX hcap hXl hOk hne hsg h00 h01 h02 h03 h04
    h05 h07 h08 hB harr hho₃
  have hroom₃ : c₃.nreg ALLOC + shotCostG (F (c₃.nreg 84007)) shK (c₃.nreg 84002) ≤ W := by
    grind
  refine RSB.seq ((shot_rsb hE hI₃ hsh hBs hXl hB8 hBo hpre hroom₃).mono
    (le_of_eq (by grind)) (fun _ h => h)) (fun c₄ hI₄ hA₄ h₄ => ?_)
  obtain ⟨hpost, keep⟩ := h₄
  refine RSB.of_RS Finset.subset_union_left ((hitCp_rs hI₄).mono le_rfl (fun c₅ h₅ => ?_))
  obtain ⟨v11, v12, v13, o₅⟩ := h₅
  -- the wrapper's postcondition at the model and the candidate
  have hMD : ModelDescAt c₃.nmem (c₃.nreg RS0) (Qof P) M := hpre.2.2.2.2.2.1
  have hOI : OriginIn c₃ (RS0 + 3) (.walk (xOf c₀)) := ⟨h03, h04, h05⟩
  obtain ⟨hfl, A, hlo, hhi, hyes, hno⟩ := hpost M (.walk (xOf c₀)) hMD hOI
  have hdir : dirOf (c₃.nreg (RS0 + 6)) = dirOf (c₀.nreg 83008) := by
    show dirOf (c₃.nreg 84006) = _; rw [h06]
  rw [hdir] at hyes hno
  have hl3 : ShotList.holeList c₃ RS0 = ShotList.holeList c₂ 84000 :=
    holeList_congr (fun r h1 h2 => o₃.1 r (by simp [shW]; omega))
  refine ⟨⟨by rw [v11]; exact hfl, c₃.nmem, c.nreg ALLOC, ShotList.holeList c₃ RS0, A, harr, ?_,
    ?_, ?_, fun h => ?_, fun h => ?_⟩, ?_, ?_⟩
  · rw [hl3]; exact hho.2.2.2
  · have := hlo; rw [show c₃.nreg (RS0 + 1) = c.nreg ALLOC from h01,
      show c₃.nreg (RS0 + 2) = K from h02] at this; exact this
  · have := hhi; rw [show c₃.nreg (RS0 + 1) = c.nreg ALLOC from h01,
      show c₃.nreg (RS0 + 2) = K from h02] at this; exact this
  · obtain ⟨t, hfh, hpp, hpe, hpos⟩ := hyes (by show c₄.nreg 84020 = 1; omega)
    exact ⟨t, hfh, by rw [v12, v13]; exact hpp, by rw [v12]; exact hpe, by rw [v12, v13]; exact hpos⟩
  · exact hno (by ram_simp <;> omega_nf)
  · rw [o₅.1 _ (by simp [hitW]), keep _ (by norm_num) (by norm_num), o₃.1 _ (by simp [shW]),
      k12 _ (by simp [holeL, chainHL]), ag₁ _ (by norm_num) (by norm_num) (by simp [buildL])]
  · rw [o₅.1 _ (by simp [hitW]), keep _ (by norm_num) (by norm_num), o₃.1 _ (by simp [shW]),
      k12 _ (by simp [holeL, chainHL]), ag₁ _ (by norm_num) (by norm_num) (by simp [buildL])]

end

end Restore

end Chazelle.Core
