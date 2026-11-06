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

private theorem vertexLex_translate_le_iff (a x y : Vertex) :
    vertexLex (latticeTranslate a x) ≤ vertexLex (latticeTranslate a y) ↔
      vertexLex x ≤ vertexLex y := by
  simp only [vertexLex, Prod.Lex.toLex_le_toLex, latticeTranslate]
  omega

/-- The distinguished representative records absence explicitly on infinite
clusters. Finite nonempty clusters are represented by their lexicographic
minimum. -/
def clusterRepresentative (ω : LatticeConfiguration) (x : Vertex) : Option Vertex := by
  classical
  exact if h : (cluster ω x).Finite then
    some (Classical.choose (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, by
      change (rcInfiniteOpenGraph ω).Reachable x x
      exact SimpleGraph.Reachable.refl x⟩))
  else
    none

theorem clusterRepresentative_spec (ω : LatticeConfiguration) (x y : Vertex) :
    clusterRepresentative ω x = some y ↔
      (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z := by
  classical
  unfold clusterRepresentative
  split_ifs with h
  · have hspec := Classical.choose_spec
      (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, SimpleGraph.Reachable.refl x⟩)
    exact ⟨by rintro ⟨⟩; exact ⟨h, hspec.1, hspec.2⟩, fun ⟨_, hy, hmin⟩ =>
      congrArg some (toLex_inj.mp (le_antisymm (hspec.2 _ hy) (hmin _ hspec.1)))⟩
  · exact ⟨by simp, fun ⟨hfinite, _, _⟩ => (h hfinite).elim⟩

private theorem cluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) : cluster ω x = cluster ω y :=
  Set.ext fun _ => ⟨fun hz => hxy.symm.trans hz, fun hz => hxy.trans hz⟩

theorem clusterRepresentative_eq_iff_reachable (ω : LatticeConfiguration)
    (x y : Vertex) (hfiniteX : (cluster ω x).Finite)
    (hfiniteY : (cluster ω y).Finite) :
    clusterRepresentative ω x = clusterRepresentative ω y ↔
      (rcInfiniteOpenGraph ω).Reachable x y := by
  classical
  refine ⟨fun heq => ?_, fun hxy => ?_⟩
  · obtain ⟨z, hz⟩ := Option.ne_none_iff_exists'.mp
      (show clusterRepresentative ω x ≠ none by simp [clusterRepresentative, hfiniteX])
    have hzy : clusterRepresentative ω y = some z := heq ▸ hz
    exact ((clusterRepresentative_spec ω x z).mp hz).2.1.trans
      ((clusterRepresentative_spec ω y z).mp hzy).2.1.symm
  · have hclusters := cluster_eq_of_reachable ω hxy
    obtain ⟨a, ha, hminA⟩ := Set.exists_min_image (cluster ω x) vertexLex hfiniteX
      ⟨x, SimpleGraph.Reachable.refl x⟩
    obtain ⟨b, hb, hminB⟩ := Set.exists_min_image (cluster ω y) vertexLex hfiniteY
      ⟨y, SimpleGraph.Reachable.refl y⟩
    have hab' : a = b := toLex_inj.mp (le_antisymm
      (hminA b (hclusters ▸ hb)) (hminB a (hclusters.symm ▸ ha)))
    rw [(clusterRepresentative_spec ω x a).2 ⟨hfiniteX, ha, hminA⟩,
      (clusterRepresentative_spec ω y b).2 ⟨hfiniteY, hb, hminB⟩, hab']

theorem clusterRepresentative_covariant (a : Vertex) (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) =
      Option.map (latticeTranslate a) (clusterRepresentative ω x) := by
  classical
  by_cases hfin : (cluster ω x).Finite
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (cluster ω x) vertexLex hfin
      ⟨x, SimpleGraph.Reachable.refl x⟩
    have hold := (clusterRepresentative_spec ω x y).2 ⟨hfin, hy, hmin⟩
    have hnew := (clusterRepresentative_spec (edgeTranslate a ω)
      (latticeTranslate a x) (latticeTranslate a y)).2
      ⟨by rw [cluster_translation]; exact hfin.image _,
       by rw [cluster_translation]; exact ⟨y, hy, rfl⟩,
       by rintro z hz; rw [cluster_translation] at hz; rcases hz with ⟨w, hw, rfl⟩
          exact (vertexLex_translate_le_iff a y w).2 (hmin w hw)⟩
    simp [hold, hnew]
  · have hnewInf : (cluster (edgeTranslate a ω) (latticeTranslate a x)).Infinite := by
      rw [cluster_translation]
      exact (Set.infinite_image_iff (latticeTranslationIso a).injective.injOn).2 hfin
    simp [clusterRepresentative, hnewInf, show ¬(cluster ω x).Finite from hfin]

theorem clusterRepresentative_none_iff (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative ω x = none ↔ (cluster ω x).Infinite := by
  classical
  by_cases h : (cluster ω x).Finite <;> simp [clusterRepresentative, h, Set.Infinite]

def clusterColoring {C : Type*} (c₀ : C)
    (z : LatticeConfiguration × (Vertex → C)) : Vertex → C :=
  fun x => (clusterRepresentative z.1 x).elim c₀ z.2

theorem measurableSet_clusterRepresentative (x y : Vertex) :
    MeasurableSet {ω : LatticeConfiguration | clusterRepresentative ω x = some y} := by
  have hfinite : MeasurableSet {ω : LatticeConfiguration | (cluster ω x).Finite} := by
    rw [show {ω : LatticeConfiguration | (cluster ω x).Finite} = (infiniteAt x)ᶜ by
      ext ω; change (cluster ω x).Finite ↔ ¬¬(cluster ω x).Finite; tauto]
    exact (measurableSet_infiniteAt x).compl
  have hmin : MeasurableSet {ω : LatticeConfiguration |
      ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} := by
    rw [show {ω : LatticeConfiguration | ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} =
        ⋂ z : Vertex, {ω | z ∈ cluster ω x → vertexLex y ≤ vertexLex z} by ext; simp]
    refine MeasurableSet.iInter fun z => ?_
    by_cases hle : vertexLex y ≤ vertexLex z
    · simp [hle]
    · rw [show {ω : LatticeConfiguration | z ∈ cluster ω x → vertexLex y ≤ vertexLex z} =
        {ω | ¬(rcInfiniteOpenGraph ω).Reachable x z} by ext ω; simp [hle]; rfl]
      exact (measurableSet_open_reachable x z).compl
  rw [show {ω : LatticeConfiguration | clusterRepresentative ω x = some y} =
      {ω | (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} by
    ext ω; exact clusterRepresentative_spec ω x y]
  exact hfinite.inter ((measurableSet_open_reachable x y).inter hmin)

theorem measurable_clusterColoring {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (c₀ : C) :
    Measurable (clusterColoring c₀ :
      LatticeConfiguration × (Vertex → C) → Vertex → C) := by
  classical
  refine measurable_pi_iff.mpr fun x s _ => ?_
  rw [show s = ⋃ c : {c : C // c ∈ s}, ({c.1} : Set C) by ext; simp, Set.preimage_iUnion]
  refine MeasurableSet.iUnion fun c => ?_
  have hpre : (fun z : LatticeConfiguration × (Vertex → C) => clusterColoring c₀ z x) ⁻¹' {c.1} =
      (infiniteAt x ×ˢ {u : Vertex → C | c₀ = c.1}) ∪
        ⋃ y : Vertex,
          ({ω : LatticeConfiguration | clusterRepresentative ω x = some y} ×ˢ
            ((fun u : Vertex → C => u y) ⁻¹' {c.1})) := by
    ext ⟨ω, u⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_union, Set.mem_prod,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    cases hr : clusterRepresentative ω x with
    | none =>
      simp [clusterColoring, hr, (clusterRepresentative_none_iff ω x).mp hr, infiniteAt]
    | some y =>
      have hninf : ¬ ω ∈ infiniteAt x := fun hinf => by
        rw [(clusterRepresentative_none_iff ω x).2 hinf] at hr; cases hr
      simp [clusterColoring, hr, hninf]
  rw [hpre]
  refine MeasurableSet.union ((measurableSet_infiniteAt x).prod (by by_cases h : c₀ = c.1 <;> simp [h]))
    (MeasurableSet.iUnion fun y => (measurableSet_clusterRepresentative x y).prod
      (measurable_pi_apply y (measurableSet_singleton c.1)))

theorem clusterColoring_equivariant {C : Type*} (c₀ : C) (a : Vertex)
    (z : LatticeConfiguration × (Vertex → C)) (x : Vertex) :
    clusterColoring c₀
        (productShift (fun a ω => edgeTranslate a ω)
          (fun a u => iidFieldShift (latticeShiftEquiv a) u) a z) x =
      clusterColoring c₀ z (x - a) := by
  rcases z with ⟨ω, u⟩
  have hrep := clusterRepresentative_covariant a ω (latticeTranslate (-a) x)
  rw [show latticeTranslate a (latticeTranslate (-a) x) = x by
    simpa using latticeTranslate_neg_cancel (-a) x,
    show latticeTranslate (-a) x = x - a by ext <;> simp [latticeTranslate, sub_eq_add_neg]] at hrep
  cases hr : clusterRepresentative ω (x - a) with
  | none => simp [clusterColoring, productShift, hrep, hr]
  | some y =>
    simp only [clusterColoring, productShift, hrep, hr, Option.map_some, Option.elim_some,
      iidFieldShift]
    exact congrArg u (by ext <;> dsimp [latticeTranslate, latticeShiftEquiv] <;> omega)

end
end PottsDiscontinuity.PottsThm
