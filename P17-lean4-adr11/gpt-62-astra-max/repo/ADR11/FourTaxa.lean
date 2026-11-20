module
public import ADR11.Nonbinary.FourTaxa

@[expose] public section
namespace ADR11
open Finset Real Quartet Skeleton _root_.ADR11.Computation

local notation "quartet[" i "," j "," k "]" =>
  {{0,i},{j,k},{0},{1},{2},{3},{1,2,3},{0,2,3},{0,1,3},{0,1,2}}
local notation "quartets[" σ "," t "]" =>
  SpeciesTree.unrootedDist σ id quartet[1,2,3] = 1 - 2/3 * exp (-t) ∧
  SpeciesTree.unrootedDist σ id quartet[2,1,3] = 1/3 * exp (-t) ∧
  SpeciesTree.unrootedDist σ id quartet[3,1,2] = 1/3 * exp (-t)

private theorem view (σ : Quartet.Tree) (t : ℝ) (h : weight σ 0 = exp (-t))
    (h₁ : weight σ 1 = 1) (h₂ : weight σ 2 = 1) : quartets[σ,t] := by
  simp only [show quartet[1,2,3] = gene 0 by decide,
    show quartet[2,1,3] = gene 1 by decide,
    show quartet[3,1,2] = gene 2 by decide, at_gene, output, background,h,h₁,h₂]
  exact ⟨by ring, by ring, by ring⟩

private theorem d3 : decC 4 3 = {0,1} := by decide
private theorem d12 : decC 4 12 = {2,3} := by decide

macro "quartet_view" h:ident : tactic => `(tactic| (
  apply view
  all_goals simp +decide [sides,side,Sparse.branch,SpeciesTree.edge,($h),d3,d12,neg_add,exp_add] <;> ring))

theorem Challenge.fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ,{0,1},{2,3},{0},{1},{2},{3}}) :
    quartets[σ,σ.length {0,1} + σ.length {2,3}] := by quartet_view hσ

theorem Challenge.fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ,{0,1},{0,1,2},{0},{1},{2},{3}}) :
    quartets[σ,σ.length {0,1}] := by quartet_view hσ

end ADR11
