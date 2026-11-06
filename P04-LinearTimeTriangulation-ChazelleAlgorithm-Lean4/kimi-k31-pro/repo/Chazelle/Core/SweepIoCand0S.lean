module

public import Chazelle.Core.SweepIoCand0L
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics

/-!
# The sweep RAM (WP-D), answers: the candidate step of side `0`, first steps

* `AccSt`: the accumulator with good candidates (relative to the start `c` of the step);
* `CandFr.trans`, `candFr_of_lh`, `candFr_of_part`: frames;
* `Q0`: the facts of a side-0 query (`q0_of`);
* `start_irs`: the local hit in the model of `C₁` at the query position;
* `box_irs`: the local hit in the model of `C₂` at the box twin (query on a vertical side of the
  box, `bR = 1`);
* `above_out`: the output above the top of `C₂` (`bR = 0`).
-/

namespace Chazelle.Core

namespace SweepIo

open Machine Machine.Stmt Programs SweepRam SweepPrim WalkEmbed Sweep
open Chazelle.Visibility (rayPt)
open Chazelle.Merge (FreeAt)

@[expose] public section

variable {P : Polygon} {W : ℕ} {c₀ c : Config}

/-! ## The accumulator and the frames -/

/-- **The accumulator holds good candidates** (tags under the bits of `c`). -/
def AccSt (P : Polygon) (J : Merge.Junction) (z : Point) (c : Config) (L : Set ℝ)
    (c' : Config) : Prop :=
  AccOK P accA (ModB J (c.nreg bL) (c.nreg bR)) J.whole.radius z (dirOf (c.nreg qD)) L c' ∧
    ∀ τ ∈ L, 0 < τ ∧ OnCB J.whole (rayPt z (dirOf (c.nreg qD)) τ)

theorem CandFr.trans {c₁ c₂ c₃ : Config} (h₁ : CandFr c₁ c₂) (h₂ : CandFr c₂ c₃) :
    CandFr c₁ c₃ :=
  ⟨fun r a b d e f => (h₂.1 r a b d e f).trans (h₁.1 r a b d e f), h₁.2.1.trans h₂.2.1,
    fun a ha => (h₂.2.2 a (lt_of_lt_of_le ha h₁.2.1)).trans (h₁.2.2 a ha)⟩

/-- The pipeline registers survive. -/
theorem CandFr.pipe {c c' : Config} (h : CandFr c c') {r : ℕ} (h1 : sw 3200 ≤ r)
    (h2 : r < sw 3230) : c'.nreg r = c.nreg r :=
  h.1 r (not_oracle_sw (by ufo sw at *) (by ufo sw at *))
    (by ufo sw at *) (by ufo sw at *) (by ufo sw at *)
    (by ufo ALLOC sw at *)

/-- The frame of a local hit is a frame of a candidate step. -/
theorem candFr_of_lh {c c' : Config}
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ LHW r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 h2 _ _ h5 => h r h1 (fun h' => h2 (by unfold LHW sw at h'; ufo sw)) h5,
    hA, hm⟩

/-- The frame of a part is a frame of a candidate step. -/
theorem candFr_of_part {c c' : Config} (h : PartFr c c') : CandFr c c' :=
  ⟨fun r h1 h2 h3 h4 h5 => h.1 r h1 h2 (fun h' => h3 (by ufo sw at *))
    (fun h' => h4 (by ufo sw at *)) h5, h.2.1, h.2.2⟩

/-- A frame keeping all registers but a set `S` of scratch registers of the candidate step. -/
theorem candFr_of_set {c c' : Config} {S : ℕ → Prop}
    (hS : ∀ r, S r → (sw 3230 ≤ r ∧ r < sw 3400) ∨ (sw 4000 ≤ r ∧ r < sw 5000))
    (h : ∀ r, bandOf r ∉ oracleBands → ¬ S r → r ≠ ALLOC → c'.nreg r = c.nreg r)
    (hA : c.nreg ALLOC ≤ c'.nreg ALLOC) (hm : ∀ a, a < c.nreg ALLOC → c'.nmem a = c.nmem a) :
    CandFr c c' :=
  ⟨fun r h1 _ h3 h4 h5 => h r h1 (fun h' => by rcases hS r h' with h'' | h'' <;> tauto) h5,
    hA, hm⟩

theorem modB_left (J : Merge.Junction) (r : ℕ) : ModB J 1 r 0 = J.left := by simp [ModB]

theorem modB_right (J : Merge.Junction) : ModB J 1 1 1 = J.right := by simp [ModB]

/-! ## The facts of a side-0 query -/

section Q

variable {J : Merge.Junction} {z : Point}

/-- **The facts of a side-0 query** used by the steps. -/
structure Q0 (P : Polygon) (J : Merge.Junction) (z : Point) (c : Config) : Prop where
  hσ : dirOf (c.nreg qD) = 1 ∨ dirOf (c.nreg qD) = -1
  hz1 : z.2 ≤ J.left.top.2
  hbL : c.nreg bL = 1
  hy : |z.2| < J.left.radius
  hgeo : LHGeo P J.left ⟨c.nreg qE, c.nreg qH⟩ (c.nreg qD)
  hpos : (chainModel J.left).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z
  hcls : PosClass J.left (Qof P) ⟨c.nreg qE, c.nreg qH⟩
  he : c.nreg qE < (chainModel J.left).W.n
  hpp : ProperPos (chainModel J.left) (Qof P) P.n ⟨c.nreg qE, c.nreg qH⟩
  hh1 : 1 ≤ c.nreg qH
  hhn : c.nreg qH ≤ P.n
  hzh : ((Qof P).vtx (c.nreg qH - 1)).2 = z.2
  hfree : FreeAt J.whole z (dirOf (c.nreg qD))
  hP0 : 0 ≤ (chainModel J.left).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩
  hP1 : (chainModel J.left).param (Qof P) ⟨c.nreg qE, c.nreg qH⟩ < 1

theorem q0_of (hQ : QState P J 0 z c) : Q0 P J z c := by
  have hQn : (Qof P).n = P.n := shear_n _ _
  have hq := hQ.hq
  have hgeo := lhGeo_query hq (by
    have := hQ.hht; simp [sideChain_zero'] at this; exact this)
  have hpos : (chainModel J.left).pos (Qof P) ⟨c.nreg qE, c.nreg qH⟩ = z := by
    have := hQ.hz; simp [sideChain_zero'] at this; exact this
  obtain ⟨he, hh1, hh2, h0, h1, htop, -⟩ := hq
  simp [sideChain_zero'] at he h0 h1 htop
  have hσ := SweepPrim.dirOf_cases (c.nreg qD)
  have ⟨_, _, _, _, hsec, _⟩ := hgeo
  have hy := query_abs he h0 h1 htop hσ hsec
  have hcls := posClass_of he h0 h1 hy (Or.inl htop)
  rw [hpos] at hy htop
  have hht := hQ.hht
  simp [sideChain_zero'] at hht
  rw [hpos] at hht
  exact ⟨hσ, htop, (hQ.hbL.2).2 htop, hy, hgeo, hpos, hcls, he, ⟨h0, h1, by rwx [← hQn]⟩,
    hh1, by rwx [← hQn], hht.symm, hQ.hfree, h0, h1⟩

end Q

/-! ## The first local hit and the box twin -/

section Steps

variable {sh : Stmt} {Bs : Finset ℕ} {F : ℕ → ℕ} {X : MemCtx} {Ok : Polygon → Model → Prop}
  {J : Merge.Junction} {H : Host} {N₁ N₂ : NF} {E : ℕ} {z : Point}

/-- The cost of a local hit of the step. -/
abbrev Klh (c₀ : Config) (F : ℕ → ℕ) : ℕ :=
  lhsK (c₀.nreg TLR) (F (c₀.nreg (sw 5))) (c₀.nreg (sw 6))

/-- **The local hit in the model of `C₁`** at the query position, from a cleared accumulator. -/
theorem start_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) (hI : IInv W c₀ c) (hQ : QState P J 0 z c)
    (h0 : c.nreg accA = 0) (hroom : c.nreg ALLOC + Klh c₀ F ≤ W) :
    IRS P W c₀ (lhs (sw 30) (sw 3) (sw 33) qE 0 sh) c (Klh c₀ F) (fun c' =>
      ∃ L, AccSt P J z c L c' ∧ J.left.hitParam z (dirOf (c.nreg qD)) ∈ L ∧ CandFr c c') := by
  have q := q0_of hQ
  have hloc : (c.nreg qE = 1 ∨ c.nreg qE = 3) ∨ (6 ≤ c.nreg qE ∧ z ∈ J.left.set) := by
    rcases q.hcls with h | ⟨h6, -⟩ | ⟨h6, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨h6, q.hpos ▸ posClass_mem q.hcls h6 q.hP0 q.hP1⟩
    · have h6' : c.nreg qE = 2 * J.left.m + 6 := h6
      exact Or.inr ⟨by omega, q.hpos ▸ posClass_mem q.hcls (by show 6 ≤ c.nreg qE; omega)
        q.hP0 q.hP1⟩
  refine (lhs_irs hsh hBs hXl hA (sideD₁ hA) ⟨by ufo IFix sw, by ufo IFix sw,
    by ufo IFix sw⟩ (by ufo OutL qE sw) hI (L := ∅)
    (Mod := ModB J (c.nreg bL) (c.nreg bR)) (R₀ := J.whole.radius) (t := 0) q.he q.hpp q.hpos q.hy
    hloc (accOK_init _ _ _ _ _ h0) (by norm_num) (by rw [q.hbL]; exact modB_left J _) rfl
    hroom).mono le_rfl ?_
  rintro c' ⟨⟨L', a', -, g', geo'⟩, fr, hA', hm'⟩
  refine ⟨L', ⟨a', fun τ hτ => ?_⟩, geo' q.hgeo, candFr_of_lh fr hA' hm'⟩
  rcases g' τ hτ with h | ⟨h1, h2⟩
  · exact absurd h (Set.notMem_empty τ)
  · exact ⟨h1, onCB_left h2⟩

/-- **The box twin** (`bR = 1`, the query on a vertical side of the box): the local hit in the
model of `C₂` at the same position completes the candidates. -/
theorem box_irs (hsh : ShooterOK sh Bs F X Ok) (hBs : Bs ⊆ oracleBands) (hXl : X.CapLocal)
    (hA : AEnv P W X Ok J H N₁ N₂ E c₀) {c' : Config} (hI : IInv W c₀ c') (hQ : QState P J 0 z c)
    (hfr : CandFr c c') {L : Set ℝ} (hst : AccSt P J z c L c')
    (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L) (hbR : c.nreg bR = 1)
    (hbox : c.nreg qE < 4) (hroom : c'.nreg ALLOC + Klh c₀ F ≤ W) :
    IRS P W c₀ (lhs (sw 31) (sw 4) (sw 34) qE 1 sh) c' (Klh c₀ F) (fun c'' =>
      CandOut P J z c c'' ∧ CandFr c c'') := by
  have q := q0_of hQ
  have eE : c'.nreg qE = c.nreg qE := hfr.pipe (by ufo qE sw) (by ufo qE sw)
  have eH : c'.nreg qH = c.nreg qH := hfr.pipe (by ufo qH sw) (by ufo qH sw)
  have eD : c'.nreg qD = c.nreg qD := hfr.pipe (by ufo qD sw) (by ufo qD sw)
  have h13 : c.nreg qE = 1 ∨ c.nreg qE = 3 := by
    rcases q.hcls with h | ⟨h6, -⟩ | ⟨h6, -⟩
    · exact h
    · have h6' : 6 ≤ c.nreg qE := h6; omega
    · have h6' : c.nreg qE = 2 * J.left.m + 6 := h6; omega
  have hz2  := (hQ.hbR.2).1 hbR
  obtain ⟨hg₂, hpos₂⟩ := lhGeo_box h13 q.hgeo (by rw [q.hpos]; exact q.hy)
    (by rwx [q.hpos])
  rw [q.hpos] at hpos₂
  obtain ⟨-, -, hpar, -⟩ := boxTwin_pos (C₁ := J.left) (C₂ := J.right) rfl h13 (Qof P) (c.nreg qH)
  have hn₂ : c.nreg qE < (chainModel J.right).W.n := by rwo [cm_n]
  refine (lhs_irs hsh hBs hXl hA (sideD₂ hA) ⟨by ufo IFix sw, by ufo IFix sw,
    by ufo IFix sw⟩ (by ufo OutL qE sw) hI (L := L)
    (Mod := ModB J (c.nreg bL) (c.nreg bR)) (R₀ := J.whole.radius) (t := 1) (z := z)
    (by rwx [eE])
    (by rw [eE, eH]; exact ⟨hpar ▸ q.hpp.1, hpar ▸ q.hpp.2.1, q.hpp.2.2⟩)
    (by rwx [eE, eH]) q.hy (by rw [eE]; exact Or.inl h13)
    (by rw [eD]; exact hst.1) (by norm_num) (by rw [q.hbL, hbR]; exact modB_right J) rfl
    hroom).mono le_rfl ?_
  rintro c'' ⟨⟨L', a', s', g', geo'⟩, fr, hA', hm'⟩
  rw [eD] at a' g' geo'
  rw [eE, eH] at geo'
  have hr := geo' hg₂
  refine ⟨⟨L', a', fun τ hτ => ?_, whole_mem_of_both q.hz1 hz2 q.hσ (s' hl) hr⟩,
    hfr.trans (candFr_of_lh fr hA' hm')⟩
  rcases g' τ hτ with h | ⟨h1, h2⟩
  · exact hst.2 τ h
  · exact ⟨h1, onCB_right h2⟩

/-- **Above the top of `C₂`** (`bR = 0`): the local hit in the model of `C₁` completes the
candidates. -/
theorem above_out (hQ : QState P J 0 z c) {c' : Config} (hfr : CandFr c c') {L : Set ℝ}
    (hst : AccSt P J z c L c') (hl : J.left.hitParam z (dirOf (c.nreg qD)) ∈ L)
    (hbR : ¬ c.nreg bR = 1) : CandOut P J z c c' ∧ CandFr c c' := by
  have q := q0_of hQ
  have hz2 : J.right.top.2 < z.2 := by
    by_contra h; exact hbR ((hQ.hbR.2).2 (not_lt.1 h))
  refine ⟨⟨L, hst.1, hst.2, ?_⟩, hfr⟩
  rwx [whole_eq_left q.hz1 hz2 q.hσ]

end Steps

end

end SweepIo

end Chazelle.Core
