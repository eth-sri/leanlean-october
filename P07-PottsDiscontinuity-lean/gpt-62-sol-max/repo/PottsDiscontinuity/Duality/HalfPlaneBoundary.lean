module

public import PottsDiscontinuity.Duality.FiniteClusterBoundary
public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration

/-! Cutting the boundary graph at the horizontal axis leaves odd-degree vertices
exactly at the crossings of the axis. The crossings to the right of a finite
primal segment have odd total degree, so they connect to the crossings on the left. -/

@[expose] public section

namespace PottsDiscontinuity.Duality

open FK FK.Medial Finset SimpleGraph
open scoped Classical
noncomputable section

variable (C : Finset LatticeVertex)

local notation "S" => vertexCellBases C
local notation "G" => latticeCellBoundaryGraph S

private theorem adj_down (x : ℤ) : (G).Adj (x,0) (x,-1) ↔
    ((x+1,0) ∈ C) ≠ ((x,0) ∈ C) := by
  simpa [mem_vertexCellBases] using (boundaryAdj_down S x 0)

private def boundaryVertices : Finset LatticeVertex :=
  (latticeCellBoundaryBonds S).biUnion fun b => {b.source, b.target}

private theorem right_neighbor_mem {u v : LatticeVertex} (h : (G).Adj u v) :
    v ∈ boundaryVertices C := by
  obtain ⟨_, b, he, hb⟩ := (latticeCellBoundaryGraph_adj_iff _ _ _).1 h
  refine mem_biUnion.2 ⟨b, (mem_latticeCellBoundaryBonds _ _).2 hb, ?_⟩
  rcases Sym2.eq_iff.1 he with ⟨_,he⟩ | ⟨he,_⟩ <;> simp [← he]

/-- The only lost edge at a vertex above the cut is the edge down from row zero. -/
private theorem upper_degree {V : Finset LatticeVertex}
    (hv : ∀ z ∈ V, 0 ≤ z.2)
    (hV : ∀ z ∈ boundaryVertices C, 0 ≤ z.2 → z ∈ V)
    (u : V) :
    ((((G).induce (V : Set LatticeVertex)).degree u : ℕ) : ZMod 2) =
      if u.val.2 = 0 ∧ (G).Adj u.val (u.val.1,-1) then 1 else 0 := by
  let H := (G).induce (V : Set LatticeVertex)
  let p (v : LatticeVertex) := 0 ≤ v.2
  let N := boundaryNeighborFinset S u.val
  have hN (z : LatticeVertex) : z ∈ N ↔ (G).Adj u.val z := by
    rw [← mem_coe, ← latticeBoundary_neighborSet_eq_finset]
    rfl
  have he : (H.neighborFinset u).map (Function.Embedding.subtype _) = N.filter p := by
    ext z
    simp only [mem_map, mem_neighborFinset, Function.Embedding.subtype_apply, mem_filter, hN]
    constructor
    · rintro ⟨w, h, rfl⟩
      exact ⟨h, hv _ w.property⟩
    · rintro ⟨h, hp⟩
      exact ⟨⟨z, hV _ (right_neighbor_mem C h) hp⟩, h, rfl⟩
  have hcard := congrArg card he
  rw [card_map, card_neighborFinset_eq_degree] at hcard
  have hz : 0 ≤ u.val.2 := hv _ u.property
  let down : LatticeVertex := (u.val.1, -1)
  let q := u.val.2 = 0 ∧ (G).Adj u.val down
  have hlower : N.filter (fun v => ¬p v) = if q then {down} else ∅ := by
    ext z
    simp only [mem_filter, hN]
    constructor
    · rintro ⟨ha, hp⟩
      have hs := (squareLattice_adj_iff _ _).mp (latticeCellBoundaryGraph_le _ ha)
      have hh : z = down ∧ u.val.2 = 0 := by
        dsimp [p] at hp
        simp only [down, Prod.ext_iff]
        omega
      obtain ⟨rfl, hh⟩ := hh
      simp [q, hh, ha]
    · by_cases hq : q <;> simp [hq]
      rintro rfl
      exact ⟨hq.2, by simp [p, down]⟩
  have hsum := N.card_filter_add_card_filter_not p
  rw [← hcard, hlower] at hsum
  have hEven := latticeCellBoundaryGraph_even_degree S u.val
  rw [latticeBoundary_neighborSet_eq_finset, Set.ncard_coe_finset, ← ZMod.natCast_eq_zero_iff_even] at hEven
  change (N.card : ZMod 2) = 0 at hEven
  change (H.degree u : ZMod 2) = if q then 1 else 0
  by_cases hq : q
  · simp [hq] at hsum ⊢
    have hn := congrArg (fun n : ℕ => (n : ZMod 2)) hsum
    simp at hn
    rw [hEven] at hn
    exact eq_neg_of_add_eq_zero_left hn |>.trans (by decide)
  · simpa [hq, show H.degree u = N.card by simpa [hq] using hsum] using hEven

/-- An axis segment in a finite set forces a dual boundary path across it. -/
private theorem boundary_connects (r : ℕ) (hr : ∀ x : ℤ, 0 ≤ x → x ≤ r → (x,0) ∈ C) :
    ∃ b t : LatticeVertex, b.2 = 0 ∧ (r : ℤ) ≤ b.1 ∧ t.1 < 0 ∧ (G).Reachable b t := by
  obtain ⟨u, hu, hmax⟩ := C.exists_max_image Prod.fst ⟨_, hr r (by positivity) le_rfl⟩
  let k := u.1 + 1
  have hK : ∀ z ∈ C, z.1 < k := fun z hz => by have := hmax z hz; omega
  have hrk : (r : ℤ) < k := hK _ (hr r (by positivity) le_rfl)
  let l := k.toNat
  have hl : (l : ℤ) = k := Int.toNat_of_nonneg (by omega)
  let I := Ico r l
  let V := ((boundaryVertices C).filter fun z => 0 ≤ z.2) ∪ I.image (fun x : ℕ => ((x : ℤ),0))
  let H := (G).induce (V : Set LatticeVertex)
  have hv : ∀ z ∈ V, 0 ≤ z.2 := by aesop
  have hV : ∀ z ∈ boundaryVertices C, 0 ≤ z.2 → z ∈ V := by aesop
  let b : I ↪ V := ⟨fun x => ⟨(x.val, 0), mem_union_right _
      (mem_image_of_mem (fun i : ℕ => ((i : ℤ), 0)) x.property)⟩,
    fun x y h => Subtype.ext (Int.ofNat.inj (congrArg (fun z : V => z.val.1) h))⟩
  let B := I.attach.map b
  let T := (univ : Finset V).filter fun z => z.val.2 = 0 ∧ z.val.1 < 0
  have hB (z : V) : z ∈ B ↔ z.val.2 = 0 ∧ (r : ℤ) ≤ z.val.1 ∧ z.val.1 < k := by
    simp only [B, mem_map, mem_attach, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      obtain ⟨h₁,h₂⟩ := mem_Ico.1 i.property
      change (0 : ℤ) = 0 ∧ (r : ℤ) ≤ (i.val : ℤ) ∧ (i.val : ℤ) < k
      omega
    · rintro ⟨hy, h₁, h₂⟩
      refine ⟨⟨z.val.1.toNat, mem_Ico.2 ⟨by omega, by omega⟩⟩, Subtype.ext (Prod.ext ?_ hy.symm)⟩
      exact Int.toNat_of_nonneg (by omega)
  have hT (z : V) : z ∈ T ↔ z.val.2 = 0 ∧ z.val.1 < 0 := by simp [T]
  obtain ⟨v, hb, t, ht, hvt⟩ := exists_reachable_between_of_odd_degree_sum H B T
    (by
      intro z hz
      rw [← ZMod.natCast_eq_zero_iff_even]
      rw [upper_degree C hv hV]
      split_ifs with h
      · obtain ⟨hh, hadj⟩ := h
        have he := adj_down C z.val.1 |>.1 (by simpa [← hh] using hadj)
        simp only [mem_union, hB, hT, hh, true_and, not_or] at hz
        obtain ⟨hnI, hnonneg⟩ := hz
        by_cases hx : z.val.1 < r
        · exact (he (propext (iff_of_true (hr _ (by omega) (by omega)) (hr _ (by omega) (by omega))))).elim
        · have h₁ : (z.val.1 + 1, (0 : ℤ)) ∉ C := fun h => by have := hK _ h; omega
          have h₂ : (z.val.1, (0 : ℤ)) ∉ C := fun h => by have := hK _ h; omega
          exact (he (propext (iff_of_false h₁ h₂))).elim
      · rfl)
    (by
      rw [← ZMod.natCast_eq_one_iff_odd, Nat.cast_sum, show B = I.attach.map b from rfl, sum_map]
      let f (x : ℕ) : ZMod 2 := if ((x : ℤ),0) ∈ C then 1 else 0
      have he (i : I) : (H.degree (b i) : ZMod 2) = f (i.val+1) - f i.val := by
        rw [upper_degree C hv hV]
        change (if (0 : ℤ) = 0 ∧ (G).Adj (i.val,0) (i.val,-1) then 1 else 0) = _
        rw [adj_down]
        by_cases h₁ : ((i.val : ℤ)+1,(0:ℤ)) ∈ C <;> by_cases h₂ : ((i.val : ℤ),(0:ℤ)) ∈ C <;>
          simp [f, h₁, h₂] <;> decide
      simp_rw [he]
      rw [sum_attach I (fun i => f (i+1) - f i)]
      change (∑ i ∈ Ico r l, (f (i+1) - f i)) = 1
      refine (Finset.sum_Ico_sub f (by omega : r ≤ l)).trans ?_
      have hk : (k,(0:ℤ)) ∉ C := fun h => (lt_irrefl k) (hK _ h)
      simp [f, hl, hk, hr r (by positivity) le_rfl] <;> decide)
  obtain ⟨hy, hi, _⟩ := (hB v).1 hb
  exact ⟨v.val, t.val, hy, hi, (hT t |>.1 ht).2,
    hvt.map ⟨Subtype.val, fun h => h⟩⟩

/-- If all primal clusters are finite, take the union of the clusters meeting
an axis segment. Its boundary is dual-open. -/
theorem no_infinite_cluster_implies_opposite_connections (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) (R : ℕ) :
    ∃ k : ℕ, ∃ w : LatticeVertex, R ≤ k ∧ w.1 < 0 ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ connectionEvent ((k : ℤ), 0) w := by
  have hf (k : ℕ) : (cluster ω (k,0)).Finite := Set.not_infinite.1 fun h => hno ⟨(k,0), h⟩
  let C := (range (R+1)).biUnion fun k => (hf k).toFinset
  have hC (x : LatticeVertex) : x ∈ C ↔ ∃ k : ℕ, k ≤ R ∧ (rcInfiniteOpenGraph ω).Reachable (k,0) x := by
    simp [C, cluster]
  have hrow (x : ℤ) (h₁ : 0 ≤ x) (h₂ : x ≤ R) : (x,0) ∈ C := by
    refine (hC _).2 ⟨x.toNat, by omega, ?_⟩
    rw [Int.toNat_of_nonneg h₁]
  have hclosed {u v : LatticeVertex} (h : (rcInfiniteOpenGraph ω).Adj u v) : u ∈ C ↔ v ∈ C := by
    rw [hC, hC]
    constructor <;> rintro ⟨k, hk, hr⟩
    · exact ⟨k, hk, hr.trans h.reachable⟩
    · exact ⟨k, hk, hr.trans h.symm.reachable⟩
  obtain ⟨b, t, hy, hx, ht, hp⟩ := boundary_connects C R hrow
  refine ⟨b.1.toNat, t, by omega, ht, ?_⟩
  rw [show ((b.1.toNat : ℤ), (0 : ℤ)) = b by
    exact Prod.ext (Int.toNat_of_nonneg (by omega)) hy.symm]
  exact hp.mono (clusterCellBoundary_le_dualOpen ω C fun {_ _} h => hclosed h)

end
end PottsDiscontinuity.Duality
