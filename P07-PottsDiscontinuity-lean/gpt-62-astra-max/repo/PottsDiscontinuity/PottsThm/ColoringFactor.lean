module

public import PottsDiscontinuity.PottsThm.LatticeColorNoise
public import PottsDiscontinuity.PottsThm.ColorNoiseMixing
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

private theorem vertexLex_translate_le_iff (a x y : Vertex) :
    vertexLex (latticeTranslate a x) ≤ vertexLex (latticeTranslate a y) ↔
      vertexLex x ≤ vertexLex y := by
  simp [vertexLex, Prod.Lex.toLex_le_toLex, latticeTranslate]

section
variable (a : Vertex) (ω : LatticeConfiguration) (x : Vertex)

include ω x in
/-- The distinguished representative records absence explicitly on infinite
clusters. Finite nonempty clusters are represented by their lexicographic
minimum. -/
def clusterRepresentative : Option Vertex := by
  classical
  exact if h : (cluster ω x).Finite then
    some (Classical.choose (Set.exists_min_image _ vertexLex h ⟨x, by
      exact SimpleGraph.Reachable.refl x⟩))
  else
    none

theorem clusterRepresentative_spec (x y : Vertex) :
    clusterRepresentative ω x = some y ↔
      (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z := by
  classical
  unfold clusterRepresentative
  split_ifs with h
  · constructor
    · grind
    · rintro ⟨_, hy, hmin⟩
      have hspec := Classical.choose_spec
        (Set.exists_min_image _ vertexLex h ⟨x, SimpleGraph.Reachable.refl x⟩)
      have heq : Classical.choose
          (Set.exists_min_image _ vertexLex h ⟨x, SimpleGraph.Reachable.refl x⟩) = y := by
        apply toLex_inj.mp
        apply le_antisymm
        · exact hspec.2 _ hy
        · exact hmin _ hspec.1
      grind
  · grind

private theorem cluster_eq_of_reachable {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) : cluster ω x = cluster ω y := by
  ext z
  solve_by_elim [hxy.symm.trans, hxy.trans]

/-- Canonical finite-cluster representatives agree exactly on connected
vertices. -/
theorem clusterRepresentative_eq_iff_reachable
    {x y : Vertex} (hfiniteX : (cluster ω x).Finite)
    (hfiniteY : (cluster ω y).Finite) :
    clusterRepresentative ω x = clusterRepresentative ω y ↔
      (rcInfiniteOpenGraph ω).Reachable x y := by
  classical
  constructor
  · intro heq
    have hne : clusterRepresentative ω x ≠ none := by
      simp [clusterRepresentative, hfiniteX]
    have hsome : ∃ z, clusterRepresentative ω x = some z := by
      cases h : clusterRepresentative ω x with
      | none =>
        grind
      | some z => grind
    obtain ⟨z, hz⟩ := hsome
    exact (clusterRepresentative_spec ω x z).mp hz |>.2.1.trans ((clusterRepresentative_spec ω y z).mp (by grind) |>.2.1).symm
  · intro hxy
    have hclusters := cluster_eq_of_reachable ω hxy
    obtain ⟨a, ha, hminA⟩ := Set.exists_min_image _ vertexLex hfiniteX
      ⟨x, SimpleGraph.Reachable.refl x⟩
    obtain ⟨b, hb, hminB⟩ := Set.exists_min_image _ vertexLex hfiniteY
      ⟨y, SimpleGraph.Reachable.refl y⟩
    have hab' := toLex_inj.mp (le_antisymm (hminA b (by grind)) (hminB a (by grind)))
    have hrepA := (clusterRepresentative_spec ω x a).2 ⟨hfiniteX, ha, hminA⟩
    have hrepB := (clusterRepresentative_spec ω y b).2 ⟨hfiniteY, hb, hminB⟩
    grind

theorem clusterRepresentative_covariant :
    clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) =
      Option.map (latticeTranslate a) (clusterRepresentative ω x) := by
  classical
  by_cases hfin : (cluster ω x).Finite
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image _ vertexLex hfin
      ⟨x, SimpleGraph.Reachable.refl x⟩
    have hyspec : latticeTranslate a y ∈
        cluster (edgeTranslate a ω) (latticeTranslate a x) := by
      grind [cluster_translation]
    have hold := (clusterRepresentative_spec ω x y).2 ⟨hfin, hy, hmin⟩
    have hnew := (clusterRepresentative_spec _
      _ _).2 ⟨(by
        rw [cluster_translation]
        exact hfin.image _), hyspec, (by
        intro z hz
        rw [cluster_translation] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        exact (vertexLex_translate_le_iff a y w).2 (hmin w hw))⟩
    grind
  · have hnewInf : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Infinite := by
      rw [cluster_translation]
      exact (Set.infinite_image_iff
        (show Set.InjOn (latticeTranslate a) (cluster ω x) from
          (latticeTranslationIso a).injective.injOn)).2 hfin
    simp_all [clusterRepresentative]

theorem clusterRepresentative_none_iff :
    clusterRepresentative ω x = none ↔ (cluster ω x).Infinite := by
  simp_all [clusterRepresentative]

/-- Colour finite clusters from the iid coordinate of their canonical
representative and pin infinite clusters to `c₀`. -/
def clusterColoring {C : Type*} (c₀ : C)
    (z : LatticeConfiguration × (Vertex → C)) : Vertex → C :=
  fun x => (clusterRepresentative z.1 x).elim c₀ z.2

end

theorem measurableSet_clusterRepresentative (x y : Vertex) :
    MeasurableSet {ω : LatticeConfiguration | clusterRepresentative ω x = some y} := by
  have hfinite : MeasurableSet {ω : LatticeConfiguration | (cluster ω x).Finite} := by
    have heq : {ω : LatticeConfiguration | (cluster ω x).Finite} = (infiniteAt x)ᶜ := by
      ext ω
      change _ ↔ ¬¬(cluster ω x).Finite
      classical
      tauto
    rw [heq]
    exact (measurableSet_infiniteAt x).compl
  have hmin : MeasurableSet {ω : LatticeConfiguration |
      ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
    have heq : {ω : LatticeConfiguration |
        ∀ z, z ∈ cluster ω x → vertexLex y ≤ vertexLex z} =
        ⋂ z : Vertex, {ω : LatticeConfiguration |
          z ∈ cluster ω x → vertexLex y ≤ vertexLex z} := by
      ext ω
      simp
    rw [heq]
    apply MeasurableSet.iInter
    intro z
    by_cases hle : vertexLex y ≤ vertexLex z
    · simp_all
    · rw [show {ω : LatticeConfiguration | z ∈ cluster ω x →
          vertexLex y ≤ vertexLex z} =
          {ω : LatticeConfiguration | z ∉ cluster ω x} by
            simp [hle]]
      exact (measurableSet_open_reachable x z).compl
  rw [show {ω : LatticeConfiguration | clusterRepresentative ω x = some y} =
      {ω | (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} by
        ext ω
        exact clusterRepresentative_spec ω x y]
  exact hfinite.inter ((measurableSet_open_reachable x y).inter hmin)

theorem measurable_clusterColoring {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (c₀ : C) :
    Measurable (clusterColoring c₀) := by
  classical
  apply measurable_pi_iff.mpr
  intro x s hs
  have hdecomp : s = ⋃ c : {c : C // c ∈ s}, {c.1} := by
    ext c
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
        exact Or.inl ⟨((clusterRepresentative_none_iff ω x).mp hr), by simpa [clusterColoring, hr] using hz⟩
      | some y =>
        apply Or.inr
        exact ⟨y, ⟨hr, by simpa [clusterColoring, hr] using hz⟩⟩
    · rintro (⟨hinf, hc⟩ | ⟨y, hr, hc⟩)
      · simpa [clusterColoring, ((clusterRepresentative_none_iff ω x).2 hinf)] using hc
      · change _ = some y at hr
        simpa [clusterColoring, hr] using hc
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

theorem clusterColoring_equivariant {C : Type*} (c₀ : C) (a : Vertex)
    (z : LatticeConfiguration × (Vertex → C)) (x : Vertex) :
    clusterColoring c₀
        (Prod.map (edgeTranslate a) (iidFieldShift (latticeShiftEquiv a)) z) x =
      clusterColoring c₀ z (x - a) := by
  rcases z with ⟨ω, u⟩
  have hrep := clusterRepresentative_covariant a ω (latticeTranslate (-a) x)
  have hcancel : latticeTranslate a (latticeTranslate (-a) x) = x := by
    simpa using (latticeTranslate_neg_cancel (-a) x)
  rw [hcancel] at hrep
  have hcoord : latticeTranslate (-a) x = x - a := rfl
  cases hr : clusterRepresentative ω (x - a) with
  | none =>
    rw [← hcoord] at hr
    have hnone := hr
    have hnone' : clusterRepresentative ω (x - a) = none := hnone
    simp [clusterColoring, latticeShiftEquiv, *]
  | some y =>
    rw [← hcoord] at hr
    have hsome := hr
    have hsome' : clusterRepresentative ω (x - a) = some y := hsome
    have harg : (latticeTranslate a y) - a = y := by
      ext <;> simp [latticeTranslate]
    simp only [clusterColoring, Prod.map, hrep, hsome, hsome', Option.map_some,
      Option.elim_some]
    exact (by
      change u ((latticeTranslate a y) - a) = u y
      grind)

end
end PottsDiscontinuity.PottsThm
