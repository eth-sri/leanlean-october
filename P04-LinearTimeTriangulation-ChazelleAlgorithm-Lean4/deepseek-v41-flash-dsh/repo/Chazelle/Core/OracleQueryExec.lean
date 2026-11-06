module

public import Chazelle.Golf

public import Chazelle.Core.OracleQFacts

/-!
# Lemma 3.6 (WP-H), part 24: the query of Lemma 3.6

`qry` loads the constants (`qLoad`) and runs the phases (`restS`).  `qry_exec`: from the
structure in memory (`QAt`), a query origin and a direction, the query answers (`Answer`: the
first hit of the ray on the chain and its edge, or no hit) within the cost of its phases, writing
only registers of the bands `bSign`, `bLocate`, `bOQuery`, no memory, and not the allocator.
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ OracleBook

@[expose] public section

/-- **The query of Lemma 3.6.** -/
def qry : Stmt := .seq qLoad restS

/-- The registers written by the query. -/
def BQ (r : ℕ) : Bool := BLd r || BRest r

variable {P : Polygon} {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF}
  {B : BookData} {k : ℕ}

theorem sgnOf_σbOf (d : ℕ) : sgnOf (σbOf d) = dirOf d := by
  unfold sgnOf σbOf dirOf; split_ifs <;> simp_all

/-- **The origin of the query**, semantically. -/
theorem semOK_of (h : QAt P m O E V H C N B k) (hG : GoodEnv P) {o : QOrigin} (hol : o.Lt P.n)
    (d : ℕ) : SemOK P C (qV V P o d) (o.eval (Qof P) C (dirOf d)) := by
  have hv := h.qvok hol d
  refine ⟨hv, distinctHeights_of_goodEnv hG, ?_, ?_, ?_⟩
  · show _ = ((Qof P).vtx (qhzOf o)).2
    rcases o with (i | ⟨e, hh⟩) | hh <;> rfl
  · show sgnOf (σbOf d) = 1 ∨ sgnOf (σbOf d) = -1
    exact sgnOf_cases _
  · show ZoOK C (sgnOf (σbOf d)) _ (qzoOf (Qof P) o)
    Ξ sgnOf_σbOf
    rcases o with p | hh
    · exact Or.inl rfl
    · exact Or.inr ⟨rfl, rfl⟩

/-- **The query of Lemma 3.6 runs and answers.** -/
theorem qry_exec {P : Polygon} {W : ℕ} (hG : GoodEnv P) (hW : 8 * P.n + 32 ≤ W)
    {m : ℕ → ℕ} {O E : ℕ} {V : QV} {H : Host} {C : Chain} {N : NF} {B : BookData} {k : ℕ}
    (hA : QAt P m O E V H C N B k) (hEW : E ≤ W) (hHW : hostWords P.n ≤ W)
    (c : Config) (hw : WordsBounded W c) (hm : c.nmem = m) (hO : c.nreg 120000 = O)
    {o : QOrigin} (ho : QOriginIn c (bandReg bOQuery 1) o) (hol : o.Lt P.n) {NC CS : ℕ}
    (hNC : ∀ u, u < V.μ → nodeCost m (qV V P o (c.nreg 120004)) u ≤ NC)
    (hCS : ∀ u, u < V.μ → clusSize m (qV V P o (c.nreg 120004))
      (lab m (qV V P o (c.nreg 120004)) u) ≤ CS) :
    ∃ c' k', Exec P W qry c c' k' ∧
      k' ≤ 100 + (715 * V.L + 700 + dstarCost m (qV V P o (c.nreg 120004)) +
        4 * candCost (qV V P o (c.nreg 120004)) NC CS + 500) ∧
      FrameB BQ c c' ∧
      Answer P C (o.eval (Qof P) C (dirOf (c.nreg 120004))) (dirOf (c.nreg 120004))
        (c'.nreg 120005) (c'.nreg 120006) := by
  set V' := qV V P o (c.nreg 120004) with hV'
  have hA' : QAt P m O E V' H C N B k := hA.withQ o _
  have hv := hA.qvok hol (c.nreg 120004)
  have hT := hA'.topOK hG hv
  have hs := semOK_of hA hG hol (c.nreg 120004)
  obtain ⟨c₁, k₁, e₁, hk₁, f₁, hq₁⟩ := qLoad_exec hA hEW c hw hm hO hW ho hol
  have m₁ : c₁.nmem = m := Ρ f₁.2.2.1, hm
  have hDL : V'.DL + V'.nD ≤ W := by have := hA'.DL_le; omega
  obtain ⟨c₂, k₂, e₂, hk₂, f₂, tr⟩ := restS_exec arcCover hG hW hs c₁ e₁.wb_right hq₁
    (by rw [m₁]; exact hA'.qmem hEW) (by rw [m₁]; exact hA'.ordOK hEW)
    (by rw [m₁]; exact hA'.chordMem hEW) (by rw [m₁]; exact hA'.chordTab hEW)
    (by rw [m₁]; exact hA'.locMem hEW hHW) hDL hT.tv_lt (NC := NC) (CS := CS)
    (by rw [m₁]; exact hNC) (by rw [m₁]; exact hCS)
    (by rw [m₁]; exact chPr_mono (hA'.chordRec hT))
    (by
      Ξ m₁
      intro t hpart hnd bD hD hbD kk hkk
      obtain ⟨X, hX⟩ := sel_facts (hA'.chordRec hT) hs hA.simple hpart hnd hD hbD
      obtain ⟨h1, h2⟩ := hX.stop.1 kk hkk
      exact ⟨by rw [walk_n]; exact h1, h2⟩)
  rw [m₁] at hk₂ tr
  have hk₂' : k₂ ≤ 715 * V.L + 700 + dstarCost m V' + 4 * candCost V' NC CS + 500 := hk₂
  refine ⟨c₂, _, .seq e₁ e₂, ⋄, ?_, ?_⟩
  · refine ⟨fun r hr => ?_, fun r hr => ?_, f₂.2.2.1.trans f₁.2.2.1,
      f₂.2.2.2.1.trans f₁.2.2.2.1, f₂.2.2.2.2.trans f₁.2.2.2.2⟩
    · simp only [BQ, Bool.or_eq_false_iff] at hr
      Ξ f₂.1 r hr.2, f₁.1 r hr.1
    · simp only [BQ, Bool.or_eq_false_iff] at hr
      Ξ f₂.2.1 r hr.2, f₁.2.1 r hr.1
  · have := rest_answer (hA'.mainCtx hT) hs tr
    rwa [show sgnOf V'.σb = dirOf (c.nreg 120004) from sgnOf_σbOf _] at this

end

end OracleR

end Chazelle.Core
