module

public import Chazelle.Golf

public import Chazelle.Core.OracleRamTop

/-!
# Lemma 3.6 (WP-H), RAM part 16: the query after loading, as a trace

`restS_exec`: the execution of the query after loading its constants ends in one of three
recorded situations (`RestTrace`): the ray above the top (answer `0`); a degenerate start along
the chord next to the origin (answer the chord's far end); or the main phase, with the facts of
the scans of `D*` and of the clusters of the candidates at the stopping point.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK SearchR WalkKey NFLoc
open OracleQ

@[expose] public section

open Classical in
/-- **The trace of the query after loading.** -/
def RestTrace (P : Polygon) (C : Chain) (V : QV) (N : NF) (z : Point) (m : ℕ → ℕ)
    (c' : Config) : Prop :=
  (((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ c'.nreg 120005 = 0) ∨
  (¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ ∃ t, PartC P C V m t ∧ FoundC V m t ∧
    DegC P C V m t ∧
    (xpClass (farC V m t) = 1 → c'.nreg 120005 = 1 ∧
      c'.nreg 120006 = symIdx (xpSym C V P.n (farC V m t) V.hz)) ∧
    (xpClass (farC V m t) ≠ 1 → c'.nreg 120005 = 0)) ∨
  (¬ ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2 ∧ ∃ t, PartC P C V m t ∧
    ¬ (FoundC V m t ∧ DegC P C V m t) ∧ ∃ bD,
    Sweep.FirstHitOpt (dstarPts m V C V.nD) z (sgnOf V.σb)
      (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD) ∧ (∀ cb, bD = some cb → cb < V.m) ∧
    ∃ pk : ℕ → ℕ, (∀ k, k < 4 → pk k < V.A ∧
        LocFacts P (chainModel C) N V.hz (posK (mainPos P C V m t bD) k) (pk k)) ∧
      Sweep.FirstHitOpt (dstarPts m V C V.nD ∪ clusPts3 m V C (pk 0) ∪ clusPts3 m V C (pk 1) ∪
          clusPts3 m V C (pk 2) ∪ clusPts3 m V C (pk 3))
        z (sgnOf V.σb) (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z (bestOf c')) ∧
      BestOK P.n V.s V.m c' ∧ c'.nreg 120005 = c'.nreg 120050 ∧ c'.nreg 120006 = c'.nreg 120051)

open Classical in
/-- **The query after loading.** -/
theorem restS_exec (hcov : ArcCoverSpec) {P : Polygon} {W : ℕ} (hG : GoodEnv P)
    (hW : 8 * P.n + 32 ≤ W) {C : Chain} {V : QV} {z : Point} (hs : SemOK P C V z) (c : Config)
    (hw : WordsBounded W c) (hq : QConst P V c) (hm : QMem V c.nmem W) (hO : OrdOK c.nmem V W)
    (hCM : ChordMemOK V c.nmem W) (hCT : ChordTabOK V c.nmem W)
    {N : NF} (hL : LocMemOK P V c.nmem W (chainModel C) N) (hDL : V.DL + V.nD ≤ W)
    (htv : V.tv < P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost c.nmem V u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize c.nmem V (lab c.nmem V u) ≤ CS)
    (hmono : ∀ i j, i ≤ j → j < V.K → chPr P C V c.nmem (chAt c.nmem V j) = true →
      chPr P C V c.nmem (chAt c.nmem V i) = true)
    (hvalid : ∀ t, PartC P C V c.nmem t → ¬ (FoundC V c.nmem t ∧ DegC P C V c.nmem t) →
      ∀ bD : Option ℕ,
        Sweep.FirstHitOpt (dstarPts c.nmem V C V.nD) z (sgnOf V.σb)
          (bestVal (Qof P) V.s V.hz (sgnOf V.σb) z bD) → (∀ cb, bD = some cb → cb < V.m) →
        ∀ k, k < 4 → posK (mainPos P C V c.nmem t bD) k < (chainModel C).W.n ∧
          ProperPos (chainModel C) (Qof P) P.n ⟨posK (mainPos P C V c.nmem t bD) k, V.hz + 1⟩) :
    ∃ c' k, Exec P W restS c c' k ∧
      k ≤ 715 * V.L + 700 + dstarCost c.nmem V + 4 * candCost V NC CS + 500 ∧
      FrameB BRest c c' ∧ RestTrace P C V N z c.nmem c' := by
  have hv := hs.hv
  -- 1. the top test
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, b₁, t₁, z₁⟩ := topS_exec (P := P) hG hW hv htv c hw hq
  have hq₁ : QConst P V c₁ := hq.frame f₁ fun r h1 h2 => by
    simp only [Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₁ : c₁.nmem = c.nmem := f₁.2.2.1
  have g₁ : FrameB BRest c c₁ := FrameB.mono f₁ fun r hr => by
    simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
    rcases hr with (hr | hr) | hr <;> simp [BRest, hr]
  by_cases hab : ((Qof P).vtx V.tv).2 < ((Qof P).vtx V.hz).2
  · have hd : c₁.nreg 120053 = 1 := t₁.2 hab
    refine ⟨c₁, _, .seq e₁ (.ifLtN_false (by rw [hd, hq₁.one]; omega) (.skip e₁.wb_right)),
      ⋄, g₁, Or.inl ⟨hab, z₁ hd⟩⟩
  have hd : c₁.nreg 120053 = 0 := by have := mt t₁.1 hab; omega
  -- 2. the chord search
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, ht₂, hpre₂, hpost₂⟩ := chordSearch_exec (P := P) hG hW hv htv c₁
    e₁.wb_right hq₁ (by rw [m₁]; exact hCM) (by rw [m₁]; exact hmono)
  rw [m₁] at hpre₂ hpost₂
  have hq₂ : QConst P V c₂ := hq₁.frame f₂ fun r h1 h2 => by
    simp only [BCS, BP, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₂ : c₂.nmem = c.nmem := f₂.2.2.1.trans m₁
  obtain ⟨t, htd⟩ : ∃ t, c₂.nreg 50105 = t := ⟨_, rfl⟩
  rw [htd] at ht₂ hpre₂ hpost₂
  have hpart : PartC P C V c.nmem t := ⟨ht₂, hpre₂, hpost₂⟩
  -- 3. the chord next to the origin
  obtain ⟨c₃, k₃, e₃, hk₃, f₃, b₃, fd₃, nf₃⟩ := chordPost_exec (P := P) hG hW hv htv c₂
    e₂.wb_right hq₂ (by rw [m₂]; exact hCT) (by rw [htd]; exact ht₂)
  rw [htd, m₂] at fd₃ nf₃
  have hq₃ : QConst P V c₃ := hq₂.frame f₃ fun r h1 h2 => by
    simp only [BCP, BX2, Bk, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₃ : c₃.nmem = c.nmem := f₃.2.2.1.trans m₂
  -- 4. a degenerate start
  obtain ⟨c₄, k₄, e₄, hk₄, f₄, nd₄, d₄⟩ := degS_exec (P := P) hW hv c₃ e₃.wb_right hq₃
    (found := FoundC V c.nmem t) (deg := DegC P C V c.nmem t) (far := farC V c.nmem t) b₃ fd₃
    (fun h => (nf₃ h).2.1) (fun h => (nf₃ h).2.2.1) (fun h => (nf₃ h).2.2.2)
  have hq₄ : QConst P V c₄ := hq₃.frame f₄ fun r h1 h2 => by
    simp only [BDg, BX, Bool.or_eq_false_iff, decide_eq_false_iff_not]; omega
  have m₄ : c₄.nmem = c.nmem := f₄.2.2.1.trans m₃
  have x53 : c₃.nreg 120053 = 0 := by
    rw [f₃.1 _ (⌖), f₂.1 _ (⌖)]; exact hd
  have g₂ : FrameB BRest c₁ c₂ := FrameB.mono f₂ fun r hr => ⊚ BRest, hr
  have g₃ : FrameB BRest c₂ c₃ := FrameB.mono f₃ fun r hr => ⊚ BRest, hr
  have g₄ : FrameB BRest c₃ c₄ := FrameB.mono f₄ fun r hr => ⊚ BRest, hr
  by_cases hdg : FoundC V c.nmem t ∧ DegC P C V c.nmem t
  · obtain ⟨h53, hA, hB⟩ := d₄ hdg
    refine ⟨c₄, _, .seq e₁ (.ifLtN_true (by rw [hd, hq₁.one]; omega) (.seq e₂ (.seq e₃ (.seq e₄
      (.ifLtN_false (by rw [h53, hq₄.one]; omega) (.skip e₄.wb_right)))))), ⋄,
      g₁.trans (g₂.trans (g₃.trans g₄)), Or.inr (Or.inl ⟨hab, t, hpart, hdg.1, hdg.2, hA, hB⟩)⟩
  -- 5. the main phase
  have x53' : c₄.nreg 120053 = 0 := by rw [nd₄ hdg]; exact x53
  have x140 : c₄.nreg 120140 = c₃.nreg 120140 := nd₄ hdg _
  have x141 : c₄.nreg 120141 = c₃.nreg 120141 := nd₄ hdg _
  obtain ⟨c₅, k₅, bD, e₅, hk₅, f₅, hD₅, hbD₅, pk, hloc₅, hit₅, hb₅, o5, o6⟩ :=
    mainS_exec hcov (P := P) hG hW hs c₄ e₄.wb_right hq₄ (by rw [m₄]; exact hm)
      (by rw [m₄]; exact hO) (by rw [m₄]; exact hL) hDL htv (NC := NC) (CS := CS)
      (fun u hu => by rw [m₄]; exact hNC u hu) (fun u hu => by rw [m₄]; exact hCS u hu)
      (by rw [x140]; exact b₃) (by
        intro bD hbD hbm k hk
        rw [m₄] at hbD
        have := hvalid t hpart hdg bD hbD hbm k hk
        unfold mainPos at this
        rwa [selOf_congr (C := C) (V := V) (bD := bD) (f := c₄.nreg 120140 = 1)
          (f' := FoundC V c.nmem t) (w := c₄.nreg 120141) (w' := nearC V c.nmem t)
          (cb := CBof P C V bD (c₄.nreg 120141)) (cb' := CBof P C V bD (nearC V c.nmem t))
          (by rw [x140]; exact fd₃) (fun h => by rw [x141]; exact (nf₃ (fd₃.1 (by rw [← x140]; exact h))).1)
          (fun h => Ρ x141, (nf₃ (fd₃.1 (by rw [← x140]; exact h))).1)])
  rw [m₄] at hD₅ hit₅ hk₅
  have hsel : selOf C V bD (c₄.nreg 120140 = 1) (c₄.nreg 120141) (CBof P C V bD (c₄.nreg 120141)) =
      selOf C V bD (FoundC V c.nmem t) (nearC V c.nmem t) (CBof P C V bD (nearC V c.nmem t)) :=
    selOf_congr (by rw [x140]; exact fd₃)
      (fun h => by rw [x141]; exact (nf₃ (fd₃.1 (by rw [← x140]; exact h))).1)
      (fun h => Ρ x141, (nf₃ (fd₃.1 (by rw [← x140]; exact h))).1)
  rw [hsel] at hloc₅
  have g₅ : FrameB BRest c₄ c₅ := FrameB.mono f₅ fun r hr => ⊚ BRest, hr
  refine ⟨c₅, _, .seq e₁ (.ifLtN_true (by rw [hd, hq₁.one]; omega) (.seq e₂ (.seq e₃ (.seq e₄
    (.ifLtN_true (by rw [x53', hq₄.one]; omega) e₅))))), ⋄,
    g₁.trans (g₂.trans (g₃.trans (g₄.trans g₅))),
    Or.inr (Or.inr ⟨hab, t, hpart, hdg, bD, hD₅, hbD₅, pk, fun k hk => ?_, hit₅, hb₅, o5, o6⟩)⟩
  unfold mainPos; exact hloc₅ k hk

end

end OracleR

end Chazelle.Core
