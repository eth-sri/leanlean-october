/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFiniteFaces

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

theorem parafermionicCoverFiniteOrdinaryFace_has_cycle
    (n : ℕ) (v : ParafermionicCoverVertex)
    (hbox : v ∈ parafermionicCoverBoxFinset n)
    (hv : v ∈ parafermionicCoverFiniteOrdinaryFaces n) :
    ∃ w : (parafermionicCoverBoxGraph n).Walk
        ⟨v, by omega⟩
        ⟨v, by omega⟩,
      w.IsCycle ∧ w.length = 4 ∧
        w.support.map Subtype.val = [v, parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2,
          parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2, v] := by
  rcases v with ⟨⟨x,y⟩,k⟩
  have hcrit := (parafermionicCoverFiniteOrdinaryFaces_mem_iff n ((x,y),k)).mp hv
  rcases hcrit with ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
  have hface := (parafermionicCoverFaceIntermediateBounds_iff n ((x,y),k)).mpr
    ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
  have hloop :=
    parafermionicCoverFaceLiftEndpoint_eq_start_of_not_branch x y k hnot
  let s : ParafermionicCoverBoxVertex n := ⟨((x,y),k), by
    omega⟩
  let r : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightLift x y k, by simp_all⟩
  let u : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLift x y k, by grind⟩
  let l : ParafermionicCoverBoxVertex n :=
    ⟨parafermionicCoverFaceRightUpLeftLift x y k, by grind⟩
  have hsval : s.1 = ((x,y),k) := rfl
  have hrval : r.1 = ((x+1,y), k + if x = 0 ∧ y < 0 then 1 else 0) := by aesop
  have huval : u.1 = ((x+1,y+1), k + if x = 0 ∧ y < 0 then 1 else 0) := by aesop
  have hsum : (if x = 0 ∧ y < 0 then 1 else 0) +
      (if x = 0 ∧ y+1 < 0 then -1 else 0) = 0 := by
      grind
  have hlval : l.1 = ((x,y+1), k) := by
    change parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1), k)
    simp
    grind
  have hsheet : (k + (if x = 0 ∧ y < 0 then 1 else 0)) +
      (if x = 0 ∧ y + 1 < 0 then -1 else 0) = k := by omega
  have hsteps := parafermionicCoverFaceLift_steps_adj x y k
  have h1 : (parafermionicCoverBoxGraph n).Adj s r := by
    change parafermionicCoverGraph.Adj s.1 r.1
    simp_all
  have h2 : (parafermionicCoverBoxGraph n).Adj r u := by
    change parafermionicCoverGraph.Adj r.1 u.1
    simp_all
  have h3 : (parafermionicCoverBoxGraph n).Adj u l := by
    change parafermionicCoverGraph.Adj u.1 l.1
    simp_all
  have h4 : (parafermionicCoverBoxGraph n).Adj l s := by
    change parafermionicCoverGraph.Adj l.1 s.1
    simp_all
  let tail : (parafermionicCoverBoxGraph n).Walk s l :=
    SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 (SimpleGraph.Walk.cons h3 .nil))
  have hsr : s ≠ r := by
    grind

  have hsu : s ≠ u := by
    grind

  have hsl : s ≠ l := by
    grind

  have hru : r ≠ u := by
    grind

  have hrl : r ≠ l := by
    grind

  have hul : u ≠ l := by
    grind

  have hpath : tail.IsPath := by
    simp [tail, hsr, hsu, hsl, hru, hrl, hul]
  let p : (parafermionicCoverBoxGraph n).Path s l := ⟨tail, hpath⟩
  have hclose : s(s,l) ∉ (p.reverse : (parafermionicCoverBoxGraph n).Walk l s).edges := by
    aesop
  let cyc := SimpleGraph.Walk.cons h4.symm (p.reverse : (parafermionicCoverBoxGraph n).Walk l s)
  have hcyc :=
    p.reverse.cons_isCycle h4.symm hclose
  refine ⟨cyc.reverse, hcyc.reverse, ?_, ?_⟩ <;> rfl

end PottsDiscontinuity.TorusTopology.Planar.Medial
