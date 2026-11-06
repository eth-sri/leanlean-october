module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.MergeAsmDesc

/-!
# The sweep RAM (WP-D), answers: shots from a symbolic point, the mathematics

The brute-force shot (`BruteSpec`) and the label shots (`Lab0Spec`) shoot from the query point
`z`, a point strictly inside the box that is not a walk point of the chain model, at lists of arcs
of a normal form.

* `key_in_arc`: every positive walk key lies in the closed arc of an arc record (a cut key starts
  the arc of the region faced just after it, `WalkAx.attach_face`; another key is inside the arc
  of some region, `exists_arc_around`).
* `exit_in_arcs`: the exit point of a free ray (below the top) is a walk point whose key lies in
  the closed arc of an arc record (the walk position is found as in `Sweep.local_shoot`).
* `mem_dom_of`, `walk_ne_of_dom`, `innerPt_box`: a point strictly inside the box, below the top
  and off the chain is in the domain, is not a walk point, and is an inner point of the model.
* `walk_hit_onCB`: a walk position at a height not above the top is a point of the chain or of the box.
* `AEnv.ctxL`, `AEnv.ctxR`, `AEnv.mdL`, `AEnv.mdR`: the chain descriptors at `sw 20`, `sw 21`
  and the model descriptors at `sw 30`, `sw 31` of the answer phase.
-/

namespace Chazelle.Core

namespace SweepIo

open Set Filter Topology
open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)
open Chazelle.Chain (sidePt sideLeft sideInArc)
open Chazelle.Geometry (lerp point_ext)
open Chazelle.Merge (FreeAt)

@[expose] public section

/-! ## Walk keys and arcs -/

/-- **Every positive walk key lies in the closed arc of an arc record** of a valid normal form of
a chain model. -/
theorem key_in_arc (C : Chain) (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel C) Q N) {p : ℕ} {t : ℝ} (hkey : 0 < (p : ℝ) + t) :
    ∃ j < N.arcs.length, ShotList.CIn ((chainModel C).key Q (N.arc j).s)
      ((chainModel C).key Q (N.arc j).e) (p + t) := by
  set M := chainModel C with hMd
  set F := N.F M Q with hFd
  have hGM : GoodModel M := Or.inl ⟨C, hP, rfl⟩
  have hM : WalkAx M := walkAx_of_goodModel hGM
  have hFam : M.ChordFamily Q F := hN.1
  obtain ⟨hRC, -, hArcs, -⟩ := regOf_spec hN
  have ofArc : ∀ U ∈ M.regions F, ∀ a b, M.IsArc F U a b →
      ∃ j < N.arcs.length, M.key Q (N.arc j).s = a ∧ M.key Q (N.arc j).e = b := by
    intro U hU a b harc
    obtain ⟨r, hr, hrU⟩ := hRC.2.2 U hU
    rw [← hrU] at harc
    obtain ⟨j, hj, -, hs, he⟩ := hArcs.2.2.1 r hr a b harc
    grind
  by_cases hcut : M.IsCut F ((p : ℝ) + t)
  · obtain ⟨c, hc, p', t', hAc, hk⟩ := hcut
    obtain ⟨U, -, -, r, hU, -, -, harc, -, -⟩ := hM.attach_face hFam.2.1 hFam.1 hc hAc
    obtain ⟨j, hj, hs, -⟩ := ofArc U hU _ _ harc
    refine ⟨j, hj, Or.inr (Or.inl ?_)⟩
    rw [hs, hk]
  · obtain ⟨U, hU, l, r, harc, hin⟩ := exists_arc_around hGM hFam hkey hcut
    obtain ⟨j, hj, hs, he⟩ := ofArc U hU _ _ harc
    exact ⟨j, hj, Or.inl (by ram_grind)⟩

section
variable (C : Chain)
/-- **The exit point of a free ray** (at a height not above the top) is a walk point whose key
lies in the closed arc of an arc record. -/
theorem exit_in_arcs (hP : C.P.Simple) {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel C) Q N) {z : Point} {σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hz : z.2 ≤ C.top.2) (hf : FreeAt C z σ) :
    ∃ p : ℕ, ∃ t : ℝ, p < (chainModel C).W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
      (∃ j < N.arcs.length, ShotList.CIn ((chainModel C).key Q (N.arc j).s)
        ((chainModel C).key Q (N.arc j).e) (p + t)) ∧
      lerp ((chainModel C).wa p) ((chainModel C).wb p) t = rayPt z σ (C.hitParam z σ) := by
  obtain ⟨hT, hwD, hdom⟩ := Merge.hit_of_freeAt C hz hσ hf
  set T := C.hitParam z σ with hTdef
  set w := rayPt z σ T with hw
  -- the height is inside the box
  have hzR : |z.2| < C.radius := by
    have := C.dom_subset_box (hdom (T / 2) (by linarith) (by linarith))
    simpa [rayPt] using this.2
  -- the hit point is on the chain or on a vertical side of the box
  have he : w ∈ C.set ∨ (|w.1| = C.radius ∧ |w.2| < C.radius) := by
    rcases (Merge.not_mem_dom_iff C (p := w) (by simp_all)).1 hwD with h | h
    · right
      refine ⟨le_antisymm ?_ ?_, by simp_all⟩
      · by_contra hgt
        push Not at hgt
        set ε := min (T / 2) ((|w.1| - C.radius) / 2) with hε
        have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
        have hεT : ε < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
        have hbox := C.dom_subset_box (hdom (T - ε) (by linarith) (by linarith))
        have h1 : |(rayPt z σ (T - ε)).1| < C.radius := hbox.1
        have h2 : |w.1| ≤ |(rayPt z σ (T - ε)).1| + ε := by
          have e : w.1 = (rayPt z σ (T - ε)).1 + σ * ε := by core_grind
          rw [e]
          refine (abs_add_le _ _).trans ?_
          rcases hσ with rfl | rfl <;> grind
        ram_grind
      · by_contra hlt
        push Not at hlt
        exact h ⟨hlt, by simp_all⟩
    simp_all
  -- a walk position at the hit point
  
  have hee : w ≠ rayPt w (-σ) (T / 2) := by
    grind [rayPt_fst]
  have hopen : ∀ s ∈ Ioo (0 : ℝ) 1, lerp w (rayPt w (-σ) (T / 2)) s ∈ C.dom := by
    intro s hs
    have e : lerp w (rayPt w (-σ) (T / 2)) s = rayPt z σ (T - s * (T / 2)) := by
      grind [lerp, rayPt]
    rw [e]
    exact hdom _ (by nlinarith [hs.2]) (by nlinarith [hs.1])
  obtain ⟨p, t, hp, ht, ht1, hpt, -⟩ :=
    C.sideSees_chordEnd hP C.sideBeta hee (by simp [rayPt]) hopen he
  have hpt' : sidePt (chainModel C).W p t = w := hpt
  have hkey : 0 < (p : ℝ) + t := by
    by_contra hle
    push Not at hle
    have hp0 : p = 0 := by
      have : (p : ℝ) ≤ 0 := by linarith
      exact_mod_cast le_antisymm (by exact_mod_cast this) (Nat.zero_le p)
    have ht0 : t = 0 := by
      linarith
    subst hp0 ht0
    have h0 : sidePt (chainModel C).W 0 0 = C.slitTop := by
      rw [Chazelle.Chain.sidePt_zero]; rfl
    grind [rayPt_snd, Chain.slitTop]
  obtain ⟨j, hj, hin⟩ := key_in_arc C hP hN (Q := Q) hkey
  exact ⟨p, t, hp, ht, ht1.le, ⟨j, hj, hin⟩, hpt'⟩

/-! ## A point strictly inside the box -/

/-- A point strictly inside the box, not above the top and off the chain is in the domain. -/
theorem mem_dom_of {z : Point} (hz : z.2 ≤ C.top.2) (h1 : |z.1| < C.radius)
    (h2 : |z.2| < C.radius) (hzC : z ∉ C.set) : z ∈ C.dom := by
  by_contra h
  rcases (Merge.not_mem_dom_iff C hz).1 h with h' | h'
  · exact h' ⟨h1, h2⟩
  simp_all

/-- A point of the domain is not a walk point. -/
theorem walk_ne_of_dom (hP : C.P.Simple) {z : Point} (hz : z ∈ C.dom) {p : ℕ}
    (hp : p < (chainModel C).W.n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    lerp ((chainModel C).wa p) ((chainModel C).wb p) t ≠ z := fun h =>
  (FactsChain.walkAx C hP).trace p hp t ht0 ht1
    (by aesop)

/-- **A point strictly inside the box is an inner point** of the chain model. -/
theorem innerPt_box {z : Point} (h1 : |z.1| < C.radius) (h2 : |z.2| < C.radius) :
    (chainModel C).InnerPt z := by
  have hx := abs_lt.1 h1
  have hy := abs_lt.1 h2
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  have v1 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
  have v2 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
  have v3 : (chainModel C).W.vtx 3 = (C.radius, -C.radius) := rfl
  refine ⟨⟨2, 1, by omega, by omega, ?_, ?_⟩, ⟨1, 3, by omega, by omega, ?_, ?_⟩⟩
  all_goals ram_grind

/-- **A walk position not above the top** is a point of the chain or of the box. -/
theorem walk_hit_onCB (Q : Polygon) {n : ℕ} {x : WPos}
    (he : x.edge < (chainModel C).W.n) (hp : ProperPos (chainModel C) Q n x)
    (hy : ((chainModel C).pos Q x).2 ≤ C.top.2) : OnCB C ((chainModel C).pos Q x) := by
  refine walk_pos_good C Q he hp (fun h5 => ?_) (fun h6 => ?_)
  · exact absurd hy (not_le.2 (slit_above C Q hp (Or.inl h5)))
  · by_contra h0
    exact absurd hy (not_le.2 (slit_above C Q hp (Or.inr ⟨h6, lt_of_le_of_ne hp.1 (Ne.symm h0)⟩)))

/-! ## Descriptors of the answer phase -/


end

section Env

variable {P : Polygon} {W : ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop} {J : Merge.Junction}
  {H : Host} {N₁ N₂ : NF} {E : ℕ} {c₀ c : Config}

section
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀)
include hA
/-- The host of the junction is regular. -/
theorem AEnv.hostReg : HostRegular P.n H := by
  obtain ⟨-, -, -, -, hJ, hwf, -⟩ := hA.hst
  exact hwf.2.2.2 H hJ.2.2.1

section
variable (hI : IInv W c₀ c)
include hI
/-- **The chain descriptor of `C₁`** at `sw 20`. -/
theorem AEnv.ctxL :
    ChainCtx P W c (sw 20) J.left := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -⟩ := hA.hst
  have hWm := hA.hWm
  change 2 * (J.m₁ + J.m₂) + 7 ≤ W at hWm
  have h0 : ChainCtx P W c₀ (sw 20) J.left :=
    ⟨hA.hG, hA.hWh, w20, ⟨H, d20, hA.hostReg⟩, hA.hP, by aesop (add safe (by omega))⟩
  exact h0.transport (hI.hin _ (by omega_nf)) hI.hm hI.hA

/-- **The chain descriptor of `C₂`** at `sw 21`. -/
theorem AEnv.ctxR :
    ChainCtx P W c (sw 21) J.right := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -⟩ := hA.hst
  have hWm := hA.hWm
  change 2 * (J.m₁ + J.m₂) + 7 ≤ W at hWm
  have h0 : ChainCtx P W c₀ (sw 21) J.right :=
    ⟨hA.hG, hA.hWh, w21, ⟨H, d21, hA.hostReg⟩, hA.hP, by aesop (add safe (by omega))⟩
  exact h0.transport (hI.hin _ (by omega_nf)) hI.hm hI.hA



end

end

/-- The facts about a copied model descriptor at a run configuration. -/
def MdFacts (P : Polygon) (c : Config) (B : ℕ) (H : Host) (C : Chain) : Prop :=
  c.nmem B = 0 ∧ ChainDescAt c.nmem (B + 1) (Qof P) H C ∧
    ModelDescWF P (c.nreg ALLOC) c.nmem B ∧ ModelDescAt c.nmem B (Qof P) (chainModel C)

/-- A model descriptor copied from a chain descriptor, transported to a run configuration. -/
theorem mdFacts_of {B d : ℕ} {C : Chain} (hI : IInv W c₀ c)
    (hd : ChainDescAt c₀.nmem d (Qof P) H C) (hwf : ChainWF P (c₀.nreg ALLOC) c₀.nmem d)
    (hmd : ModelDescAt c₀.nmem B (Qof P) (chainModel C))
    (hmw : ModelDescWF P (c₀.nreg ALLOC) c₀.nmem B)
    (hcp : ∀ j, j < 5 → c₀.nmem (B + 1 + j) = c₀.nmem (d + j)) : MdFacts P c B H C := by
  obtain ⟨h0, -⟩ := Restore.chainDesc_of hmd rfl
  obtain ⟨-, -, hEb, -⟩ := hwf.2 H C hd
  have hC : ChainDescAt c₀.nmem (B + 1) (Qof P) H C :=
    MergeAsm.chainDescAt_copy hd hEb (fun _ _ => rfl) hcp
  obtain ⟨hmd', hmw', hC', h0'⟩ := MergeAsm.modelDesc_agree hmw h0 hC hI.hm
  exact ⟨h0', hC', hmw'.mono hI.hA, hmd'⟩

section
variable (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c)
include hA hI
/-- **The model descriptor of `C₁`** at `sw 30`. -/
theorem AEnv.mdL :
    MdFacts P c (c.nreg (sw 30)) H J.left := by
  obtain ⟨-, -, -, -, -, -, d20, w20, -, -, -, -, -, -, -, -, -, d30, w30, -, -⟩ := hA.hst
  rw [hI.hin _ (by omega_nf)]
  exact mdFacts_of hI d20 w20 d30 w30 hA.hmd₁

/-- **The model descriptor of `C₂`** at `sw 31`. -/
theorem AEnv.mdR :
    MdFacts P c (c.nreg (sw 31)) H J.right := by
  obtain ⟨-, -, -, -, -, -, -, -, d21, w21, -, -, -, -, -, -, -, -, -, d31, w31⟩ := hA.hst
  rw [hI.hin _ (by omega_nf)]
  exact mdFacts_of hI d21 w21 d31 w31 hA.hmd₂


end

end Env

end

end SweepIo

end Chazelle.Core
