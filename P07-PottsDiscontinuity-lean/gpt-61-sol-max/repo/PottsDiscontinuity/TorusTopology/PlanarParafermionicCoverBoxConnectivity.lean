/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar

noncomputable section

def coverBoxPoint (n : ℕ) (x y k : ℤ)
    (h : -(n : ℤ) ≤ x ∧ x ≤ n ∧ -(n : ℤ) ≤ y ∧ y ≤ n ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ (n ^ 5 : ℤ)) :
    ParafermionicCoverBoxVertex n :=
  ⟨((x, y), k), (parafermionicCoverBoxVertices_mem n ((x,y),k)).2 h⟩

 theorem cover_vertical_up_adj (x y k : ℤ) :
    parafermionicCoverGraph.Adj ((x,y),k) ((x,y+1),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  exact Or.inl ⟨rfl, rfl, rfl⟩

 theorem cover_vertical_down_adj (x y k : ℤ) :
    parafermionicCoverGraph.Adj ((x,y+1),k) ((x,y),k) := by
                                                           solve_by_elim [_root_.SimpleGraph.adj_symm, _root_.PottsDiscontinuity.TorusTopology.Planar.cover_vertical_up_adj]

private theorem cover_horizontal_right_adj (x k : ℤ) :
    parafermionicCoverGraph.Adj ((x,0),k) ((x+1,0),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  by_cases hx : x = 0
  · subst x
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, by norm_num, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hx⟩))

 theorem cover_horizontal_left_adj (x k : ℤ) :
    parafermionicCoverGraph.Adj ((x+1,0),k) ((x,0),k) := SimpleGraph.adj_symm parafermionicCoverGraph (cover_horizontal_right_adj x k)

 theorem box_vertical_down_adj (n : ℕ) (x k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ))
    (m : ℕ) (hm : m+1 ≤ n) :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n x (m+1) k
        ⟨hx.1, hx.2, by omega, by exact_mod_cast hm, hk.1, hk.2⟩)
      (coverBoxPoint n x m k
        ⟨hx.1, hx.2, by omega, by exact_mod_cast  Nat.le_trans (Nat.le_succ m) hm , hk.1, hk.2⟩) := cover_vertical_down_adj x  ↑m  k

noncomputable def box_vertical_down_walk (n : ℕ) (x k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    ∀ m : ℕ, ∀ (hm : m ≤ n),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxPoint n x m k
          ⟨hx.1, hx.2, by omega, by exact_mod_cast hm, hk.1, hk.2⟩)
        (coverBoxPoint n x 0 k
          ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩) := by
  intro m
  induction m with
  | zero =>
      intro hm
      exact SimpleGraph.Walk.nil
  | succ m ih =>
      intro hm
      
      
      exact SimpleGraph.Walk.cons (box_vertical_down_adj n x k hx hk m (by omega)) (ih (by omega))

noncomputable def box_vertical_negative_up_walk (n : ℕ) (x k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    ∀ m : ℕ, ∀ (hm : m ≤ n),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxPoint n x (-(m:ℤ)) k
          ⟨hx.1, hx.2, by omega, by omega, hk.1, hk.2⟩)
        (coverBoxPoint n x 0 k
          ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩) := by
  intro m
  induction m with
  | zero =>
      intro hm
      exact SimpleGraph.Walk.nil
  | succ m ih =>
      intro hm
      let pStart := coverBoxPoint n x (-((m+1:ℕ):ℤ)) k
        ⟨hx.1, hx.2, by omega, by omega, hk.1, hk.2⟩
      let pNext := coverBoxPoint n x (-(m:ℤ)) k
        ⟨hx.1, hx.2, by omega, by omega, hk.1, hk.2⟩
      
      
      exact SimpleGraph.Walk.cons (by
                                     change parafermionicCoverGraph.Adj pStart.1 pNext.1
                                     dsimp [pStart, pNext, coverBoxPoint]
                                     simpa [sub_eq_add_neg, add_assoc] using
                                       cover_vertical_up_adj x (-1 - (m:ℤ)) k) (ih (by omega))

 section

variable (n : ℕ) (k : ℤ) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) (m : ℕ) (hm : m+1 ≤ n)
include hk hm

theorem box_horizontal_left_adj  :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n (m+1) 0 k (by omega))
      (coverBoxPoint n m 0 k (by omega)) := cover_horizontal_left_adj  ↑m  k

 theorem box_horizontal_right_adj  :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n (-(m+1:ℤ)) 0 k (by omega))
      (coverBoxPoint n (-(m:ℤ)) 0 k (by omega)) := by
  change parafermionicCoverGraph.Adj _ _
  dsimp [coverBoxPoint]
  have h := cover_horizontal_right_adj (-(m+1)) k
  simp_all

end

noncomputable def box_horizontal_nonnegative_left_walk (n : ℕ) (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    ∀ m : ℕ, ∀ (hm : m ≤ n),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxPoint n m 0 k (by omega))
        (coverBoxPoint n 0 0 k (by omega)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      exact SimpleGraph.Walk.nil
  | succ m ih =>
      intro hm
      exact SimpleGraph.Walk.cons
        (box_horizontal_left_adj n k hk m (by omega)) (ih (by omega))

noncomputable def box_horizontal_negative_right_walk (n : ℕ) (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    ∀ m : ℕ, ∀ (hm : m ≤ n),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxPoint n (-(m:ℤ)) 0 k (by omega))
        (coverBoxPoint n 0 0 k (by omega)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      exact SimpleGraph.Walk.nil
  | succ m ih =>
      intro hm
      exact SimpleGraph.Walk.cons
        (box_horizontal_right_adj n k hk m (by omega)) (ih (by omega))

noncomputable def box_vertical_to_zero (n : ℕ) (x y k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n)
    (hy : -(n:ℤ) ≤ y ∧ y ≤ n)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n x y k ⟨hx.1, hx.2, hy.1, hy.2, hk.1, hk.2⟩)
      (coverBoxPoint n x 0 k ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩) := by
  cases y with
  | ofNat m =>
      
      
      simpa [coverBoxPoint] using box_vertical_down_walk n x k hx hk m (Int.ofNat_le.mp (by simpa using hy.2))
  | negSucc m =>
      
      
      simpa [coverBoxPoint, Int.negSucc_eq, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using box_vertical_negative_up_walk n x k hx hk (m+1) (Int.ofNat_le.mp (by
                                                                                                                        omega))

noncomputable def box_horizontal_to_zero (n : ℕ) (x k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n x 0 k ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩)
      (coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, hk.2⟩) := by
  cases x with
  | ofNat m =>
      
      
      simpa [coverBoxPoint] using box_horizontal_nonnegative_left_walk n k hk m (Int.ofNat_le.mp (by simpa using hx.2))
  | negSucc m =>
      
      
      simpa [coverBoxPoint, Int.negSucc_eq, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using box_horizontal_negative_right_walk n k hk (m+1) (Int.ofNat_le.mp (by
                                                                                                                        omega))

noncomputable def box_vertex_to_anchor (n : ℕ)
    (u : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverBoxGraph n).Walk u
      (coverBoxPoint n 0 0 u.1.2
        ⟨by omega, by omega, by omega, by simp,
          (parafermionicCoverBoxVertices_mem n u.1).mp u.2 |>.2.2.2.2.1,
          (parafermionicCoverBoxVertices_mem n u.1).mp u.2 |>.2.2.2.2.2⟩) := by
  have hu := (parafermionicCoverBoxVertices_mem n u.1).mp u.2
  let hx : -(n:ℤ) ≤ u.1.1.1 ∧ u.1.1.1 ≤ n := ⟨hu.1, hu.2.1⟩
  let hy : -(n:ℤ) ≤ u.1.1.2 ∧ u.1.1.2 ≤ n := ⟨hu.2.2.1, hu.2.2.2.1⟩
  let hk : -((n^5:ℕ):ℤ) ≤ u.1.2 ∧ u.1.2 ≤ (n^5:ℤ) :=
    ⟨hu.2.2.2.2.1, hu.2.2.2.2.2⟩
  
  
  have hstart : u = coverBoxPoint n u.1.1.1 u.1.1.2 u.1.2
      ⟨hx.1, hx.2, hy.1, hy.2, hk.1, hk.2⟩ := by
    apply Subtype.ext
    rfl
  rw [hstart]
  exact SimpleGraph.Walk.append (box_vertical_to_zero n u.1.1.1 u.1.1.2 u.1.2 hx hy hk) (box_horizontal_to_zero n u.1.1.1 u.1.2 hx hk)

 theorem cover_lower_seam_adj (k : ℤ) :
    parafermionicCoverGraph.Adj ((0,-1),k) ((1,-1),k+1) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, rfl, by norm_num, rfl⟩))))))

noncomputable def box_anchor_step (n : ℕ) (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k+1 ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, by omega⟩)
      (coverBoxPoint n 0 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩) := by
  
  let b := coverBoxPoint n 0 (-1) k ⟨by omega, by omega, by omega, by omega, hk.1, by omega⟩
  let c := coverBoxPoint n 1 (-1) (k+1) ⟨by omega, by omega, by omega, by omega, by omega, hk.2⟩
  let d := coverBoxPoint n 1 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩
  
  have hab : (parafermionicCoverBoxGraph n).Adj (coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, by omega⟩) b := cover_vertical_down_adj 0 (-1) k
  have hbc : (parafermionicCoverBoxGraph n).Adj b c := cover_lower_seam_adj k
  have hcd : (parafermionicCoverBoxGraph n).Adj c d := cover_vertical_up_adj 1 (-1) (k + 1)
  have hde : (parafermionicCoverBoxGraph n).Adj d (coverBoxPoint n 0 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩) := cover_horizontal_left_adj 0 (k + 1)
  exact .cons hab (.cons hbc (.cons hcd (.cons hde .nil)))

def coverBoxAnchor (n : ℕ) (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) : ParafermionicCoverBoxVertex n :=
  coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, hk.2⟩



 theorem coverBoxAnchor_zero_bounds (n : ℕ) :
    -((n^5:ℕ):ℤ) ≤ 0 ∧ 0 ≤ ((n^5:ℕ):ℤ) := by
                                            simp_all

 theorem coverBoxAnchor_pos_bounds (n m : ℕ) (hm : m ≤ n^5) :
    -((n^5:ℕ):ℤ) ≤ (m:ℤ) ∧ (m:ℤ) ≤ ((n^5:ℕ):ℤ) := by
                                                    omega

 theorem coverBoxAnchor_neg_bounds (n m : ℕ) (hm : m+1 ≤ n^5) :
    -((n^5:ℕ):ℤ) ≤ -((m+1:ℕ):ℤ) ∧
      -((m+1:ℕ):ℤ) ≤ ((n^5:ℕ):ℤ) := by
                                      omega

noncomputable def box_anchor_nat_to_zero (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, ∀ (hm : m ≤ n^5),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxAnchor n (m:ℤ) (coverBoxAnchor_pos_bounds n m hm))
        (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      exact SimpleGraph.Walk.nil
  | succ m ih =>
      intro hm
      have hk : -((n^5:ℕ):ℤ) ≤ (m:ℤ) ∧ (m+1:ℤ) ≤ ((n^5:ℕ):ℤ) := by
        omega
      
      exact SimpleGraph.Walk.append (by
                                       simpa [coverBoxAnchor] using (box_anchor_step n hn (m:ℤ) hk).reverse) (ih (by omega))

noncomputable def box_anchor_negative_to_zero (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, ∀ (hm : m+1 ≤ n^5),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxAnchor n (-((m+1:ℕ):ℤ)) (coverBoxAnchor_neg_bounds n m hm))
        (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  intro m
  induction m with
  | zero =>
      intro hm
      have hk : -((n^5:ℕ):ℤ) ≤ (-1:ℤ) ∧ (-1:ℤ)+1 ≤ ((n^5:ℕ):ℤ) := by
        omega
      simpa [coverBoxAnchor, Int.negSucc_eq] using box_anchor_step n hn (-1) hk
  | succ m ih =>
      intro hm
      
      have hk : -((n^5:ℕ):ℤ) ≤ -((m+2:ℕ):ℤ) ∧
          -((m+2:ℕ):ℤ)+1 ≤ ((n^5:ℕ):ℤ) := by
        omega
      have hstep : (parafermionicCoverBoxGraph n).Walk
          (coverBoxAnchor n (-((m+2:ℕ):ℤ))
            (coverBoxAnchor_neg_bounds n (m+1) (by omega)))
          (coverBoxAnchor n (-((m+1:ℕ):ℤ))
            (coverBoxAnchor_neg_bounds n m (Nat.le_trans (Nat.le_succ (m+1)) (by omega)))) := by
        have hcoord : (-2:ℤ) + -(m:ℤ) + 1 = -1 + -(m:ℤ) := by omega
        simpa [coverBoxAnchor, hcoord, Int.negSucc_eq] using
          box_anchor_step n hn (-((m+2:ℕ):ℤ)) hk
      exact SimpleGraph.Walk.append hstep (ih (by omega))

noncomputable def box_anchor_to_zero (n : ℕ) (hn : 1 ≤ n)
    (k : ℤ) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
          (coverBoxAnchor n k hk) (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  cases k with
  | ofNat m =>
      
      simpa [coverBoxAnchor] using box_anchor_nat_to_zero n hn m (Int.ofNat_le.mp hk.2)
  | negSucc m =>
      
      have hm : m+1 ≤ n^5 := Int.ofNat_le.mp (Int.neg_le_neg_iff.mp (by
                                                                       simpa [Int.negSucc_eq] using hk.1))
      simpa [Int.negSucc_eq, coverBoxAnchor] using
        box_anchor_negative_to_zero n hn m hm

noncomputable def box_vertex_to_zero_anchor_walk (n : ℕ) (hn : 1 ≤ n)
    (u : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverBoxGraph n).Walk u
      (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  have hu := (parafermionicCoverBoxVertices_mem n u.1).mp u.2
  
  
  exact SimpleGraph.Walk.append (by
                                   simpa [coverBoxAnchor] using box_vertex_to_anchor n u) (box_anchor_to_zero n hn u.1.2  ⟨hu.2.2.2.2.1, hu.2.2.2.2.2⟩ )

/-- The actual induced finite cover graph is connected: every vertex reaches
its sheet-zero anchor by coordinate steps, and adjacent anchors are linked by
the literal lower-seam path. -/
theorem parafermionicCoverBoxGraph_connected (n : ℕ) (hn : 1 ≤ n) :
    (parafermionicCoverBoxGraph n).Connected := {
                                                  preconnected := fun u v =>
                                                    Nonempty.intro ((box_vertex_to_zero_anchor_walk n hn u).append (box_vertex_to_zero_anchor_walk n hn v).reverse),
                                                  nonempty := Nonempty.intro (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) }

end
end PottsDiscontinuity.TorusTopology.Planar
