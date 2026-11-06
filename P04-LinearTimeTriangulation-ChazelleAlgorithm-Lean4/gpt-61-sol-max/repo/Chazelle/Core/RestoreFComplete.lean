module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.RestoreFPGood

/-!
# WP-E, the search: completeness (part 1)

The arcs of the region as list places (`arc_index`), closed cyclic intervals unwrapped
(`closedArc_unwrap`), and the count test failing on two keys of one closed arc
(`not_countOK_same_arc`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Machine Machine.Stmt Programs SweepPrim
open Chazelle.Chain (sideInArc SideAttach sidePt)
open DownHost ArcT

variable {E : FEnv} {c₀ : Config}

/-- **An arc of the region is an arc record of its list.** -/
theorem arc_index (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) {a b : ℝ}
    (h : E.M.IsArc (E.N.F E.M (Qof E.P)) (reg E.r) a b) :
    ∃ t, t < (E.N.region E.r).arcs.length ∧ E.M.key (Qof E.P) (arcOf E.N E.r t).s = a ∧
      E.M.key (Qof E.P) (arcOf E.N E.r t).e = b := by
  obtain ⟨-, -, hArcs, -⟩ := hregs
  have hr : E.r < E.N.nRegions := hE.hr
  obtain ⟨j, hj, hjr, hs, he⟩ := hArcs.2.2.1 E.r hr a b h
  have hjm : j ∈ (E.N.region E.r).arcs := (hArcs.2.2.2 E.r hr j).2 ⟨hj, hjr⟩
  obtain ⟨t, ht, htj⟩ := List.mem_iff_getElem.1 hjm
  refine ⟨t, ht, ?_, ?_⟩ <;>
  simp_all [arcOf, List.getD_eq_getElem?_getD, Option.getD_some] 

/-- **Closed cyclic intervals unwrapped.** -/
theorem closedArc_unwrap {n a b x : ℝ} (ha : 0 ≤ a ∧ a < n) (hb : 0 ≤ b ∧ b < n)
    (hx : 0 ≤ x ∧ x < n) (hab : a ≠ b) :
    ClosedArc a b x ↔ a ≤ unwrapK n a x ∧ unwrapK n a x ≤ unwrapK n a b := by
  have hub : a < unwrapK n a b := by
    core_grind
  have hc := cyc_unwrap ha ha hb hx (by core_grind)
  rw [unwrapK_self] at hc
  constructor
  · rintro (h | rfl | rfl)
    all_goals core_grind
  · rintro ⟨h1, h2⟩
    rcases h1.lt_or_eq with h1 | h1
    · rcases h2.lt_or_eq with h2 | h2
      · core_grind
      · right; right
        have e1 := wrapK_unwrapK (n := n) (l := a) hx
        have e2 := wrapK_unwrapK (n := n) (l := a) hb
        simp_all
    · right; left
      
      core_grind

/-- **Two distinct keys of one closed arc fail the count test.** -/
theorem not_countOK_same_arc {M : Model} {S : Set (Set Point)} {R : Set Point} {a b x y : ℝ}
    (hA : M.IsArc S R a b) (hab : a ≠ b) (hx : 0 ≤ x ∧ x < M.W.n) (hy : 0 ≤ y ∧ y < M.W.n)
    (hxy : x ≠ y) (hxA : ClosedArc a b x) (hyA : ClosedArc a b y) : ¬ CountOK M S R x y := by
  obtain ⟨ha0, ha1, hb0, hb1, -, hnc, -⟩ := hA
  have ha : 0 ≤ a ∧ a < (M.W.n : ℝ) := ⟨ha0, ha1⟩
  have hb : 0 ≤ b ∧ b < (M.W.n : ℝ) := ⟨hb0, hb1⟩
  obtain ⟨x1, x2⟩ := (closedArc_unwrap ha hb hx hab).1 hxA
  obtain ⟨y1, y2⟩ := (closedArc_unwrap ha hb hy hab).1 hyA
  have hux : unwrapK M.W.n a x ≠ unwrapK M.W.n a y := by
    intro h; apply hxy
    rw [← wrapK_unwrapK (n := (M.W.n : ℝ)) (l := a) hx, h, wrapK_unwrapK hy]
  -- the keys strictly between the two keys (upwards from the lower) are inside the arc
  have hempty : ∀ k₁ k₂ : ℝ, (0 ≤ k₁ ∧ k₁ < M.W.n) → (0 ≤ k₂ ∧ k₂ < M.W.n) →
      a ≤ unwrapK M.W.n a k₁ → unwrapK M.W.n a k₁ < unwrapK M.W.n a k₂ →
      unwrapK M.W.n a k₂ ≤ unwrapK M.W.n a b → (sideExits M S R k₁ k₂).ncard = 0 := by
    intro k₁ k₂ hk₁ hk₂ h1 h2 h3
    suffices hE0 : sideExits M S R k₁ k₂ = ∅ by simp_all
    ext c
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hc, p, t, hat, hin⟩
    have hpt : 0 ≤ (p : ℝ) + t ∧ (p : ℝ) + t < M.W.n := by
      obtain ⟨hp, ht0, ht1, -⟩ := hat
      have : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp
      ram_grind
    have hk := (cyc_unwrap ha hk₁ hk₂ hpt h2).1 hin
    
    have : sideInArc a b ((p : ℝ) + t) :=
      (cyc_unwrap ha ha hb hpt (by grind [unwrapK_self])).2
        ⟨by grind [unwrapK_self], by linarith⟩
    exact hnc _ this ⟨c, hc.1, p, t, hat, rfl⟩
  rintro ⟨c1, c2⟩
  grind


/-! ## The setup of completeness -/

section
variable (E : FEnv) (t : ℕ)
include E t
/-- The key of the start of arc `t` of the region. -/
noncomputable def aK : ℝ := E.M.key (Qof E.P) (arcOf E.N E.r t).s

/-- The key of the end of arc `t` of the region. -/
noncomputable def bK : ℝ := E.M.key (Qof E.P) (arcOf E.N E.r t).e


end

/-- **The good chord of a region with too many exits**, its attachments and their arcs. -/
structure GoodSet (E : FEnv) (reg : ℕ → Set Point) (X : WPos) (σ T : ℝ) (po : ℕ) (tq : ℝ)
    (ti tj : ℕ) : Prop where
  hch : (E.N.region E.r).chords ≠ []
  hgc : GoodCand E.M (Qof E.P) (E.N.F E.M (Qof E.P)) (reg E.r) X σ T
  hXA : SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) X) σ T) X.edge 0
  hOA : SideAttach E.M.W (chordOf (E.M.pos (Qof E.P) X) σ T) po tq
  hne : sidePt E.M.W X.edge 0 ≠ sidePt E.M.W po tq
  hVX : VSet E X.edge
  hti : ti < (E.N.region E.r).arcs.length
  htj : tj < (E.N.region E.r).arcs.length
  hXi : ClosedArc (aK E ti) (bK E ti) ((X.edge : ℝ) + 0)
  hXj : ClosedArc (aK E tj) (bK E tj) ((po : ℝ) + tq)
  hij : aK E ti ≠ aK E tj
  hcnt : CountOK E.M (E.N.F E.M (Qof E.P)) (reg E.r) ((X.edge : ℝ) + 0) ((po : ℝ) + tq)

theorem key_attach_ne {W : Polygon} {p p' : ℕ} {t t' : ℝ} (ht : 0 ≤ t ∧ t < 1) (ht' : 0 ≤ t' ∧ t' < 1)
    (hne : sidePt W p t ≠ sidePt W p' t') : (p : ℝ) + t ≠ p' + t' := by
  intro h
  have hp : p = p' := by
    have h1 : (p : ℝ) < p' + 1 := by linarith
    have h2 : (p' : ℝ) < p + 1 := by linarith
    have h1' : p < p' + 1 := by exact_mod_cast h1
    have h2' : p' < p + 1 := by exact_mod_cast h2
    omega
  simp_all

/-- **The setup of completeness.** -/
theorem good_set (hE : FGood E c₀) {reg : ℕ → Set Point}
    (hregs : NFRegs E.M (Qof E.P) E.N reg) (hfull : E.M.FullDegLe (Qof E.P) E.D)
    (hdeg : E.D < E.M.deg (E.N.F E.M (Qof E.P)) (reg E.r)) :
    ∃ X σ T po tq ti tj, GoodSet E reg X σ T po tq ti tj := by
  have hM := walkAx_of_goodModel hE.hGM
  obtain ⟨hFam, -, -, -⟩ := hE.hNF
  have hregs' := hregs
  obtain ⟨hRC, -, hArcs, hRg⟩ := hregs'
  have hr : E.r < E.N.nRegions := hE.hr
  have hU := hRC.1 E.r hr
  set S := E.N.F E.M (Qof E.P)
  -- the region has an exit chord
  have hch : (E.N.region E.r).chords ≠ [] := by
    intro h0
    have : E.M.deg S (reg E.r) = 0 := by
      unfold Model.deg
      rw [Set.ncard_eq_zero (hs := (hFam.1.subset fun c hc => hc.1))]
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      rintro ⟨r', hr', rfl⟩ htc
      obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.1 hr'
      have hci : E.N.chord i = r' := by
        simp_all [NF.chord, List.getD_eq_getElem?_getD, Option.getD_some] 
      have := ((hRg E.r hr).1 i).2 ⟨hi, by simp_all⟩
      simp_all
    omega
  have hne : S.Nonempty := by
    obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ hch
    obtain ⟨hi', -⟩ := ((hRg E.r hr).1 i).1 hi
    have hmem : E.N.chord i ∈ E.N.chords := by
      unfold NF.chord
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
      grind
    exact ⟨_, E.N.chord i, hmem, rfl⟩
  -- the good chord
  obtain ⟨X, σ, T, hgc, hXA, ⟨po, tq, hOA, hne'⟩, p, hpr, hpos⟩ :=
    exists_good' hE.hGM hfull hFam hU hdeg
  obtain ⟨hX0, hXe, hσ, hT, -, -, -, hadm, hsw⟩ := id hgc
  obtain ⟨heS, heR, -⟩ := hsw
  set ex := chordOf (E.M.pos (Qof E.P) X) σ T
  obtain ⟨a₁, b₁, hA₁, hX₁⟩ := attach_closedArc hM hFam.2.1 hFam.1 hne hU hadm heS heR hXA
  obtain ⟨a₂, b₂, hA₂, hX₂⟩ := attach_closedArc hM hFam.2.1 hFam.1 hne hU hadm heS heR hOA
  obtain ⟨ti, hti, hai, hbi⟩ := arc_index hE hregs hA₁
  obtain ⟨tj, htj, haj, hbj⟩ := arc_index hE hregs hA₂
  have hcnt := counts_of_splitsWell hM hFam.2.1 hFam.1 hU hadm hXA hOA hne' hgc.2.2.2.2.2.2.2.2
  have hXk : 0 ≤ (X.edge : ℝ) + 0 ∧ (X.edge : ℝ) + 0 < E.M.W.n := by
    simp_all
  have hOk : 0 ≤ (po : ℝ) + tq ∧ (po : ℝ) + tq < E.M.W.n := by
    obtain ⟨hp, ht0, ht1, -⟩ := hOA
    have : (po : ℝ) + 1 ≤ E.M.W.n := by exact_mod_cast hp
    grind
  have hkne : (X.edge : ℝ) + 0 ≠ (po : ℝ) + tq :=
    key_attach_ne ⟨le_rfl, one_pos⟩ ⟨hOA.2.1, hOA.2.2.1⟩ hne'
  refine ⟨X, σ, T, po, tq, ti, tj, ⟨hch, hgc, hXA, hOA, hne', fun C hC => ?_, hti, htj,
    by grind [aK, bK], by simp_all [aK, bK] , ?_,
    hcnt⟩⟩
  · have hXX : X = ⟨X.edge, 0⟩ := by cases X; simp_all
    have h1 := hpr C hC
    rw [← hXX, hpos]
    have h2 := chain_vtx_mem C (Qof E.P) h1.1 h1.2
    grind [pos_eq_sidePt, param_vtx, Chazelle.Chain.sidePt_zero]
  · intro hab
    unfold aK at hab
    rw [hai, haj] at hab
    subst hab
    -- the two arcs are one record
    have hr' : E.r < E.N.nRegions := hr
    have mem : ∀ t, t < (E.N.region E.r).arcs.length →
        (E.N.region E.r).arcs.getD t 0 < E.N.arcs.length ∧
          (E.N.arc ((E.N.region E.r).arcs.getD t 0)).reg = E.r := fun t ht => by
      apply (hArcs.2.2.2 E.r hr' _).1
      simp_all
    obtain ⟨m1, r1⟩ := mem ti hti
    obtain ⟨m2, r2⟩ := mem tj htj
    have hjj := hArcs.2.1 _ _ m1 m2 (by rw [r1, r2]) (by
      grind [arcOf])
    have hb : b₁ = b₂ := by grind [arcOf]
    subst hb
    exact not_countOK_same_arc hA₁ (by rw [← hai, ← hbi]; exact arc_ne hE hch hti) hXk hOk
      hkne hX₁ hX₂ hcnt

end

end Restore

end Chazelle.Core
