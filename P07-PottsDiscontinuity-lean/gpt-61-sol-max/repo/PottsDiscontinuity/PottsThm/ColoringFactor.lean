module
public import Mathlib

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
    some (Classical.choose (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, SimpleGraph.Reachable.refl x⟩))
  else
    none

theorem clusterRepresentative_spec (ω : LatticeConfiguration) (x y : Vertex) :
    clusterRepresentative ω x = some y ↔
      (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z := by
  
  unfold clusterRepresentative
  split_ifs with h
  · constructor
    · grind
    · rintro ⟨_, hy, hmin⟩
      have hspec := Classical.choose_spec
        (Set.exists_min_image (cluster ω x) vertexLex h ⟨x, SimpleGraph.Reachable.refl x⟩)
      
      exact congrArg some (by
                             apply toLex_inj.mp
                             apply le_antisymm
                             · exact hspec.2 _ hy
                             · exact hmin _ hspec.1)
  · simp_all

private theorem cluster_eq_of_reachable (ω : LatticeConfiguration) {x y : Vertex}
    (hxy : (rcInfiniteOpenGraph ω).Reachable x y) : cluster ω x = cluster ω y := ext fun z =>
                                                                                   { mp := SimpleGraph.Reachable.trans (SimpleGraph.Reachable.symm hxy), mpr := SimpleGraph.Reachable.trans hxy }

/-- Canonical finite-cluster representatives agree exactly on connected
vertices. -/
theorem clusterRepresentative_eq_iff_reachable (ω : LatticeConfiguration)
    (x y : Vertex) (hfiniteX : (cluster ω x).Finite)
    (hfiniteY : (cluster ω y).Finite) :
    clusterRepresentative ω x = clusterRepresentative ω y ↔
      (rcInfiniteOpenGraph ω).Reachable x y := by
  
  constructor
  · intro heq
    
    have hsome : ∃ z, clusterRepresentative ω x = some z := by
      grind +locals
    obtain ⟨z, hz⟩ := hsome
    
    
    have hyz  := (clusterRepresentative_spec ω y z).mp (by rw [← heq, hz]) |>.2.1
    
    
    exact ((clusterRepresentative_spec ω x z).mp hz |>.2.1).trans hyz.symm
  · intro hxy
    have hclusters := cluster_eq_of_reachable ω hxy
    obtain ⟨a, ha, hminA⟩ := Set.exists_min_image (cluster ω x) vertexLex hfiniteX
      ⟨x, SimpleGraph.Reachable.refl x⟩
    obtain ⟨b, hb, hminB⟩ := Set.exists_min_image (cluster ω y) vertexLex hfiniteY
      ⟨y, SimpleGraph.Reachable.refl y⟩
    
    
    
    
    
    
    
    rw [ (clusterRepresentative_spec ω x a).2 ⟨hfiniteX, ha, hminA⟩ ,  (clusterRepresentative_spec ω y b).2 ⟨hfiniteY, hb, hminB⟩ ,  toLex_inj.mp (le_antisymm (hminA b (by rw [hclusters]; exact hb)) (hminB a (by rw [← hclusters]; exact ha))) ]

theorem clusterRepresentative_covariant (a : Vertex) (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) =
      Option.map (latticeTranslate a) (clusterRepresentative ω x) := by
  
  by_cases hfin : (cluster ω x).Finite
  · obtain ⟨y, hy, hmin⟩ := Set.exists_min_image (cluster ω x) vertexLex hfin
      ⟨x, SimpleGraph.Reachable.refl x⟩
    
    
    
    
    have hnew := (clusterRepresentative_spec (edgeTranslate a ω)
      (latticeTranslate a x) (latticeTranslate a y)).2 ⟨ by
                                                           rw [cluster_translation]
                                                           exact hfin.image _ ,  by
                                                                   rw [cluster_translation]
                                                                   all_goals aesop ,  by
                                                                           intro z hz
                                                                           rw [cluster_translation] at hz
                                                                           obtain ⟨w, hw, rfl⟩ := hz
                                                                           exact (vertexLex_translate_le_iff a y w).2 (hmin w hw) ⟩
    simp [ (clusterRepresentative_spec ω x y).2 ⟨hfin, hy, hmin⟩ , hnew]
  · 
    have hleft : clusterRepresentative (edgeTranslate a ω) (latticeTranslate a x) = none := by
      simp [clusterRepresentative,  Eq.mpr (congrArg Set.Infinite (cluster_translation a ω x))
                                                                                                                      ((infinite_image_iff (Function.Injective.injOn (RelIso.injective (latticeTranslationIso a)))).mpr hfin) ]
    have hright : Option.map (latticeTranslate a) (clusterRepresentative ω x) = none := by
      simp [clusterRepresentative, hfin]
    exact hleft.trans hright.symm

theorem clusterRepresentative_none_iff (ω : LatticeConfiguration) (x : Vertex) :
    clusterRepresentative ω x = none ↔ (cluster ω x).Infinite := by
  classical
  simp_all [clusterRepresentative]

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
    · simp [hle]
    · 
      rw [show {ω : LatticeConfiguration | z ∈ cluster ω x →
          vertexLex y ≤ vertexLex z} =
          {ω : LatticeConfiguration | z ∉ cluster ω x} by
            
            simp [hle]]
      
      
      exact (measurableSet_open_reachable x z).compl
  rw [show {ω : LatticeConfiguration | clusterRepresentative ω x = some y} =
      {ω | (cluster ω x).Finite ∧ y ∈ cluster ω x ∧
        ∀ z ∈ cluster ω x, vertexLex y ≤ vertexLex z} by
        grind [clusterRepresentative_spec]]
  exact hfinite.inter ((measurableSet_open_reachable x y).inter hmin)

theorem measurable_clusterColoring {C : Type*} [MeasurableSpace C]
    [MeasurableSingletonClass C] [Fintype C] (c₀ : C) :
    Measurable (clusterColoring c₀ :
      LatticeConfiguration × (Vertex → C) → Vertex → C) := by
  
  apply measurable_pi_iff.mpr
  intro x
  
  intro s hs
  have hdecomp : s = ⋃ c : {c : C // c ∈ s},  {c.1}  := by
    
    simp
  rw [hdecomp, Set.preimage_iUnion]
  apply MeasurableSet.iUnion
  intro c
  have hpre : {z : LatticeConfiguration × (Vertex → C) |
      clusterColoring c₀ z x = c.1} =
       infiniteAt x ×ˢ {u : Vertex → C | c₀ = c.1}  ∪
        ⋃ y : Vertex,
           {ω : LatticeConfiguration | clusterRepresentative ω x = some y} ×ˢ
            {u : Vertex → C | u y = c.1}  := by
    ext z
    rcases z with ⟨ω, u⟩
    rw [Set.mem_union, Set.mem_iUnion]
    constructor
    · intro hz
      cases hr : clusterRepresentative ω x with
      | none =>
        
        exact Or.inl ⟨((clusterRepresentative_none_iff ω x).mp hr), by simpa [clusterColoring, hr] using hz⟩
      | some y =>
        apply Or.inr
        exact ⟨y, ⟨hr, by simpa [clusterColoring, hr] using hz⟩⟩
    · rintro (⟨hinf, hc⟩ | ⟨y, hr, hc⟩)
      · 
        simpa [clusterColoring, ((clusterRepresentative_none_iff ω x).2 hinf)] using hc
      · grind +locals
  change MeasurableSet {z : LatticeConfiguration × (Vertex → C) |
    clusterColoring c₀ z x = c.1}
  rw [hpre]
  apply MeasurableSet.union
  · apply (measurableSet_infiniteAt x).prod
    by_cases h : c₀ = c.1 <;> simp 
  · exact MeasurableSet.iUnion fun y =>
      (measurableSet_clusterRepresentative x y).prod <| by
        
        have hset : {u : Vertex → C | u y = c.1} =
            (fun u  => u y) ⁻¹' {c.1} := by
          ext u
          simp
        rw [hset]
        exact (measurable_pi_apply y) (measurableSet_singleton c.1)

theorem clusterColoring_equivariant {C : Type*} (c₀ : C) (a : Vertex)
    (z : LatticeConfiguration × (Vertex → C)) (x : Vertex) :
    clusterColoring c₀
        (productShift (fun a ω => edgeTranslate a ω)
          (fun a u => iidFieldShift (latticeShiftEquiv a) u) a z) x =
      clusterColoring c₀ z (x - a) := by
  rcases z with ⟨ω, u⟩
  have hrep := clusterRepresentative_covariant a ω (latticeTranslate (-a) x)
  have hcancel : latticeTranslate a (latticeTranslate (-a) x) = x := by
    simpa using  latticeTranslate_neg_cancel (-a) x 
  rw [hcancel] at hrep
  have hcoord : latticeTranslate (-a) x = x - a := by
    ext <;> simp [latticeTranslate, sub_eq_add_neg]
  cases hr : clusterRepresentative ω (x - a) with
  | none =>
    simp_all [clusterColoring, productShift] <;>
      solve_by_elim (maxDepth := 5) [_root_.PottsDiscontinuity.PottsThm.latticeShiftEquiv._proof_1,
        _root_.PottsDiscontinuity.PottsThm.latticeShiftEquiv._proof_2, _root_.of_eq_true, _root_.Eq.trans, _root_.congr,
        _root_.congrArg, _root_.congrFun', _root_.eq_self]
  | some y =>
    rw [← hcoord] at hr
    
    have hsome' : clusterRepresentative ω (x - a) = some y := by
      
      exact  hr 
    have harg :  latticeTranslate a y  - a = y := by
      ext <;> dsimp [latticeTranslate] <;> omega
    
    simp only [clusterColoring, productShift, hrep, hr, hsome']
    exact  by
             
             change u ( latticeTranslate a y  - a) = u y
             rw [harg] 

end
end PottsDiscontinuity.PottsThm
