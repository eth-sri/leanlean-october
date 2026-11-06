module

public import PottsDiscontinuity.PottsThm.LatticeColorNoise
public import PottsDiscontinuity.PottsThm.ProductErgodicity
public import PottsDiscontinuity.RCInfinite.ClusterEvents
public import Mathlib.Data.Prod.Lex

@[expose] public section

namespace PottsDiscontinuity.PottsThm

open MeasureTheory Set
open PottsDiscontinuity.FK
open PottsDiscontinuity.RCInfinite

noncomputable section

abbrev Vertex := ℤ × ℤ

def vertexLex : Vertex → ℤ ×ₗ ℤ := toLex

theorem vertexLex_translate_le_iff (a x y : Vertex) :
    vertexLex (latticeTranslate a x) ≤ vertexLex (latticeTranslate a y) ↔
      vertexLex x ≤ vertexLex y := by
  simp only [vertexLex, Prod.Lex.toLex_le_toLex, latticeTranslate]
  omega

section
variable (ω : LatticeConfiguration)
/-- The distinguished representative records absence explicitly on infinite
clusters. Finite nonempty clusters are represented by their lexicographic
minimum. -/
def clusterRepresentative (x : Vertex) : Option Vertex := by
  classical
  exact if h : (cluster ω x).Finite then
    some (Classical.choose (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
      tauto⟩))
  else
    none

theorem clusterRepresentative_spec (x y : Vertex) :
    clusterRepresentative ω x = some y ↔
      (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z := by
  unfold clusterRepresentative
  split_ifs with h
  · constructor
    · grind
    · rintro ⟨_, hy, hmin⟩
      have hspec := Classical.choose_spec
        (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
          tauto⟩)
      have heq : Classical.choose
          (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
            tauto⟩) = y := by
        apply toLex_inj.mp
        apply le_antisymm <;> tauto
      simp_all
  · simp_all

theorem cluster_eq_of_reachable {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) : cluster ω x = cluster ω y := by
  ext z
  constructor
  · intro hz
    exact hxy.symm.trans hz
  · intro hz
    exact hxy.trans hz

/-- Canonical finite-cluster representatives agree exactly on connected
vertices. -/
theorem clusterRepresentative_eq_iff_reachable (x y : Vertex) (hfiniteX : (cluster ω x).Finite)
    (hfiniteY : (cluster ω y).Finite) :
    clusterRepresentative ω x = clusterRepresentative ω y ↔
      (rcInfiniteOpenGraph ω).Reachable x y := by
  constructor
  · intro heq
    have hne : clusterRepresentative ω x ≠ none := by
      simp_all [clusterRepresentative]
    have hsome : ∃ z, clusterRepresentative ω x = some z := by
      cases h : clusterRepresentative ω x with
      | none =>
        simp_all
      | some z => simp
    obtain ⟨z, hz⟩ := hsome
    have hxz := (clusterRepresentative_spec ω x z).mp hz |>.2.1
    have hyz := (clusterRepresentative_spec ω y z).mp (by simp_all) |>.2.1
    exact hxz.trans hyz.symm
  · intro hxy
    have hclusters := cluster_eq_of_reachable ω hxy
    obtain ⟨a, ha, hminA⟩ := Set.exists_min_image (cluster ω x) vertexLex hfiniteX
      ⟨x, by tauto⟩
    have hrepA := (clusterRepresentative_spec ω x a).2 ⟨hfiniteX, ha, hminA⟩
    grind [clusterRepresentative_spec]
end

theorem clusterRepresentative_covariant (a : Vertex) (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) =
      Option.map (latticeTranslate a) (clusterRepresentative ω x) := by
  by_cases hfin : (cluster ω x).Finite
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (cluster ω x) vertexLex hfin
      ⟨x, by tauto⟩
    have himage : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Finite := by
      rw [cluster_translation]
      exact hfin.image _
    have hyspec : latticeTranslate a y ∈
        cluster (edgeTranslate a ω) (latticeTranslate a x) := by
      rw [cluster_translation]
      grind
    have hminspec : ∀ z ∈ cluster (edgeTranslate a ω) (latticeTranslate a x),
        vertexLex (latticeTranslate a y) ≤ vertexLex z := by
      intro z hz
      rw [cluster_translation] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      simp_all [vertexLex_translate_le_iff]
    have hold := (clusterRepresentative_spec ω x y).2 ⟨hfin, hy, hmin⟩
    have hnew := (clusterRepresentative_spec (edgeTranslate a ω)
      (latticeTranslate a x) (latticeTranslate a y)).2 ⟨himage, hyspec, hminspec⟩
    simp_all
  · have hnewInf : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Infinite := by
      rw [cluster_translation]
      exact (Set.infinite_image_iff
        (show Set.InjOn (latticeTranslate a) (cluster ω x) from
          (latticeTranslationIso a).injective.injOn)).2 hfin
    simp_all [clusterRepresentative, edgeTranslate, latticeTranslate, Option.map]

theorem clusterRepresentative_none_iff (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative ω x = none ↔ (cluster ω x).Infinite := by
  by_cases h : (cluster ω x).Finite <;> simp [clusterRepresentative]

/-- Colour finite clusters from the iid coordinate of their canonical
representative and pin infinite clusters to `c₀`. -/
def clusterColoring {C : Type*} (c₀ : C)
    (z : LatticeConfiguration × (Vertex → C)) : Vertex → C :=
  fun x => (clusterRepresentative z.1 x).elim c₀ z.2

theorem measurableSet_clusterRepresentative (x y : Vertex) :
    MeasurableSet {ω : LatticeConfiguration | clusterRepresentative ω x = some y} := by
  have hfinite : MeasurableSet {ω : LatticeConfiguration | (cluster ω x).Finite} := by
    have heq : {ω : LatticeConfiguration | (cluster ω x).Finite} = (infiniteAt x)ᶜ := by
      ext ω
      change (cluster ω x).Finite ↔ ¬¬(cluster ω x).Finite
      simp
    rw [heq]
    exact (measurableSet_infiniteAt x).compl
  have hmem :=
    measurableSet_open_reachable x y
  have hmin : MeasurableSet {ω : LatticeConfiguration |
      ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
    have heq : {ω : LatticeConfiguration |
        ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} =
        ⋂ z : Vertex, {ω : LatticeConfiguration |
          z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
      aesop
    rw [heq]
    apply MeasurableSet.iInter
    intro z
    by_cases hle : vertexLex y ≤ vertexLex z
    · simp_all
    · rw [show {ω : LatticeConfiguration | z ∈ cluster ω x →
          vertexLex y ≤ vertexLex z} =
          {ω : LatticeConfiguration | z ∉ cluster ω x} by
            ext ω
            grind]
      exact (measurableSet_open_reachable x z).compl
  rw [show {ω : LatticeConfiguration | clusterRepresentative ω x = some y} =
      {ω | (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} by
        grind [clusterRepresentative, clusterRepresentative_spec]]
  exact hfinite.inter (hmem.inter hmin)

section
variable {C : Type*}
theorem measurable_clusterColoring [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (c₀ : C) :
    Measurable (clusterColoring c₀ :
      LatticeConfiguration × (Vertex → C) → Vertex → C) := by
  apply measurable_pi_iff.mpr
  intro x s hs
  have hdecomp : s = ⋃ c : {c : C // c ∈ s}, ({c.1} : Set C) := by
    simp
  rw [hdecomp, Set.preimage_iUnion]
  apply MeasurableSet.iUnion
  intro c
  have hpre : {z : LatticeConfiguration × (Vertex → C) |
      clusterColoring c₀ z x = c.1} =
      (infiniteAt x ×ˢ {u : Vertex → C | c₀ = c.1}) ∪
        ⋃ y : Vertex,
          ({ω : LatticeConfiguration | clusterRepresentative ω x = some y} ×ˢ
            {u : Vertex → C | u y = c.1}) := by
    ext z
    rcases z with ⟨ω, u⟩
    rw [Set.mem_union, Set.mem_prod, Set.mem_iUnion]
    constructor
    · intro hz
      cases hr : clusterRepresentative ω x with
      | none =>
        exact Or.inl ⟨((clusterRepresentative_none_iff ω x).mp hr), by grind [clusterColoring]⟩
      | some y =>
        apply Or.inr
        exact ⟨y, ⟨hr, by grind [clusterColoring]⟩⟩
    · rintro (⟨hinf, hc⟩ | ⟨y, hr, hc⟩)
      · have hr := (clusterRepresentative_none_iff ω x).2 hinf
        grind [clusterColoring]
      grind [clusterRepresentative, clusterColoring]
  change MeasurableSet {z : LatticeConfiguration × (Vertex → C) |
    clusterColoring c₀ z x = c.1}
  rw [hpre]
  apply MeasurableSet.union
  · apply (measurableSet_infiniteAt x).prod
    simp
  · exact MeasurableSet.iUnion fun y =>
      (measurableSet_clusterRepresentative x y).prod <| by
        have heval : Measurable (fun u : Vertex → C => u y) := measurable_pi_apply y
        exact heval (measurableSet_singleton c.1)

theorem clusterColoring_equivariant (c₀ : C) (a : Vertex)
    (z : LatticeConfiguration × (Vertex → C)) (x : Vertex) :
    clusterColoring c₀
        (productShift (fun a ω => edgeTranslate a ω)
          (fun a u => iidFieldShift (latticeShiftEquiv a) u) a z) x =
      clusterColoring c₀ z (x - a) := by
  rcases z with ⟨ω, u⟩
  have hrep := clusterRepresentative_covariant a ω (latticeTranslate (-a) x)
  have hcancel : latticeTranslate a (latticeTranslate (-a) x) = x := by
    simpa using (latticeTranslate_neg_cancel (-a) x)
  have hcoord : latticeTranslate (-a) x = x - a := by
    rfl
  cases hr : clusterRepresentative ω (x - a) with
  | none =>
    simp_all [clusterColoring, productShift, latticeShiftEquiv]
  | some y =>
    have harg : (latticeTranslate a y) - a = y := by
      ext <;> dsimp [latticeTranslate] <;> omega
    simp_all [iidFieldShift, latticeShiftEquiv, latticeTranslate, clusterColoring, productShift]
end

end
end PottsDiscontinuity.PottsThm
