module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

theorem parafermionicCoverFiniteOrdinaryFace_has_cycle
    (n : ℕ) (v : ParafermionicCoverVertex)
    (hbox : v ∈ parafermionicCoverBoxFinset n)
    (hv : v ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∃ w : (parafermionicCoverBoxGraph n).Walk
        ⟨v, by change v ∈ parafermionicCoverBoxVertices n; exact hbox⟩
        ⟨v, by change v ∈ parafermionicCoverBoxVertices n; exact hbox⟩,
      w.IsCycle ∧ w.length = 4 ∧
        w.support.map Subtype.val = [v, parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2, v] := by
  classical
  rcases v with ⟨⟨x, y⟩, k⟩
  have hface := (parafermionicCoverFaceIntermediateBounds_iff n ((x, y), k)).2
    ((parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x, y), k)).1 hv)
  let s : ParafermionicCoverBoxVertex n := ⟨((x, y), k), hbox⟩
  let r : ParafermionicCoverBoxVertex n := ⟨parafermionicCoverFaceRightLift x y k, hface.2.1⟩
  let u : ParafermionicCoverBoxVertex n := ⟨parafermionicCoverFaceRightUpLift x y k, hface.2.2.1⟩
  let l : ParafermionicCoverBoxVertex n := ⟨parafermionicCoverFaceRightUpLeftLift x y k, hface.2.2.2⟩
  have hsteps := parafermionicCoverFaceLift_steps_adj x y k
  rw [parafermionicCoverFaceLiftEndpoint_eq_start] at hsteps
  have h1 : (parafermionicCoverBoxGraph n).Adj s r := hsteps.1
  have h2 : (parafermionicCoverBoxGraph n).Adj r u := hsteps.2.1
  have h3 : (parafermionicCoverBoxGraph n).Adj u l := hsteps.2.2.1
  have h4 : (parafermionicCoverBoxGraph n).Adj l s := hsteps.2.2.2
  let tail : (parafermionicCoverBoxGraph n).Walk s l :=
    SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 .nil))
  have hsr : s ≠ r := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h; simp [s, r] at this
  have hsu : s ≠ u := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h; simp [s, u] at this
  have hsl : s ≠ l := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.2) h; simp [s, l] at this
  have hru : r ≠ u := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.2) h; simp [r, u] at this
  have hrl : r ≠ l := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h; simp [r, l] at this
  have hul : u ≠ l := by intro h; have := congrArg (fun z : ParafermionicCoverBoxVertex n => z.1.1.1) h; simp [u, l] at this
  have hpath : tail.IsPath := by rw [SimpleGraph.Walk.isPath_def]; simp [tail, hsr, hsu, hsl, hru, hrl, hul]
  let p : (parafermionicCoverBoxGraph n).Path s l := ⟨tail, hpath⟩
  have hclose : s(s, l) ∉ (p.reverse : (parafermionicCoverBoxGraph n).Walk l s).edges := by
    change s(s, l) ∉ (SimpleGraph.Walk.reverse (p : (parafermionicCoverBoxGraph n).Walk s l)).edges
    rw [SimpleGraph.Walk.edges_reverse]
    simp [p, tail, SimpleGraph.Walk.edges_cons, Sym2.eq, hsr, hsu, hsl]; aesop
  let cyc := SimpleGraph.Walk.cons h4.symm (p.reverse : (parafermionicCoverBoxGraph n).Walk l s)
  have hcyc : cyc.IsCycle := p.reverse.cons_isCycle h4.symm hclose
  exact ⟨cyc.reverse, hcyc.reverse, by simp [cyc, p, tail], by simp [cyc, p, tail, s, r, u, l]⟩

end PottsDiscontinuity.TorusTopology.Planar.Medial
