/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar

noncomputable section

def coverBoxPoint (n : ℕ) (x y k : ℤ)
    (h : -(n : ℤ) ≤ x ∧ x ≤ n ∧ -(n : ℤ) ≤ y ∧ y ≤ n ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ (n ^ 5 : ℤ)) :
    ParafermionicCoverBoxVertex n :=
  ⟨((x, y), k), (parafermionicCoverBoxVertices_mem n ((x,y),k)).2 h⟩

 section
variable (x y k : ℤ)
theorem cover_vertical_up_adj  :
    parafermionicCoverGraph.Adj ((x,y),k) ((x,y+1),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  tauto

 theorem cover_vertical_down_adj  :
    parafermionicCoverGraph.Adj ((x,y+1),k) ((x,y),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  tauto
end

section
variable (x k : ℤ)
theorem cover_horizontal_right_adj  :
    parafermionicCoverGraph.Adj ((x,0),k) ((x+1,0),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  by_cases hx : x = 0
  · subst x
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, by norm_num, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hx⟩))

 theorem cover_horizontal_left_adj  :
    parafermionicCoverGraph.Adj ((x+1,0),k) ((x,0),k) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  by_cases hx : x = 0
  · subst x
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, by norm_num, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hx⟩)))
end

 section
variable (n : ℕ) (x k : ℤ) (hx : -(n:ℤ) ≤ x ∧ x ≤ n) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ))
include hx hk
theorem box_vertical_down_adj (m : ℕ) (hm : m+1 ≤ n) :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n x (m+1) k
        ⟨hx.1, hx.2, by omega, by omega, hk.1, hk.2⟩)
      (coverBoxPoint n x m k
        ⟨hx.1, hx.2, by omega, by omega, hk.1, hk.2⟩) :=
  cover_vertical_down_adj x m k

noncomputable def box_vertical_down_walk  :
    ∀ m : ℕ, ∀ (hm : m ≤ n),
      (parafermionicCoverBoxGraph n).Walk
        (coverBoxPoint n x m k
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
      have hAdj := box_vertical_down_adj n x k hx hk m (by omega)
      have tail := ih (by omega)
      exact SimpleGraph.Walk.cons hAdj tail
end

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
      have hAdj : (parafermionicCoverBoxGraph n).Adj pStart pNext := by
        change parafermionicCoverGraph.Adj pStart.1 pNext.1
        dsimp [pStart, pNext, coverBoxPoint]
        simpa [sub_eq_add_neg, add_assoc] using
          cover_vertical_up_adj x (-1 - (m:ℤ)) k
      have tail := ih (by omega)
      exact SimpleGraph.Walk.cons hAdj tail

 section
variable (n : ℕ) (k : ℤ) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ))
include hk
theorem box_horizontal_left_adj (m : ℕ) (hm : m+1 ≤ n) :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n (m+1) 0 k (by omega))
      (coverBoxPoint n m 0 k (by omega)) :=
  cover_horizontal_left_adj m k

 theorem box_horizontal_right_adj (m : ℕ) (hm : m+1 ≤ n) :
    (parafermionicCoverBoxGraph n).Adj
      (coverBoxPoint n (-(m+1:ℤ)) 0 k (by omega))
      (coverBoxPoint n (-(m:ℤ)) 0 k (by omega)) := by
  change parafermionicCoverGraph.Adj _ _
  dsimp [coverBoxPoint]
  grind [cover_horizontal_right_adj]

noncomputable def box_horizontal_nonnegative_left_walk  :
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

noncomputable def box_horizontal_negative_right_walk  :
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
end

section
variable (n : ℕ)
noncomputable def box_vertical_to_zero (x y k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n)
    (hy : -(n:ℤ) ≤ y ∧ y ≤ n)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n x y k ⟨hx.1, hx.2, hy.1, hy.2, hk.1, hk.2⟩)
      (coverBoxPoint n x 0 k ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩) := by
  cases y with
  | ofNat m =>
      have hmCast : (m:ℤ) ≤ (n:ℤ) := by simp_all
      have hm := Int.ofNat_le.mp hmCast
      simpa [coverBoxPoint] using box_vertical_down_walk n x k hx hk m hm
  | negSucc m =>
      have hmCast : (↑(m+1):ℤ) ≤ (n:ℤ) := by
        omega
      have hm := Int.ofNat_le.mp hmCast
      simpa [coverBoxPoint, Int.negSucc_eq, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using box_vertical_negative_up_walk n x k hx hk (m+1) hm

noncomputable def box_horizontal_to_zero (x k : ℤ)
    (hx : -(n:ℤ) ≤ x ∧ x ≤ n)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n x 0 k ⟨hx.1, hx.2, by omega, by simp, hk.1, hk.2⟩)
      (coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, hk.2⟩) := by
  cases x with
  | ofNat m =>
      have hmCast : (m:ℤ) ≤ (n:ℤ) := by simp_all
      have hm := Int.ofNat_le.mp hmCast
      simpa [coverBoxPoint] using box_horizontal_nonnegative_left_walk n k hk m hm
  | negSucc m =>
      have hmCast : (↑(m+1):ℤ) ≤ (n:ℤ) := by
        omega
      have hm := Int.ofNat_le.mp hmCast
      simpa [coverBoxPoint, Int.negSucc_eq, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm] using box_horizontal_negative_right_walk n k hk (m+1) hm

noncomputable def box_vertex_to_anchor (u : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverBoxGraph n).Walk u
      (coverBoxPoint n 0 0 u.1.2
        ⟨by omega, by omega, by omega, by simp,
          (parafermionicCoverBoxVertices_mem n u.1).mp u.2 |>.2.2.2.2.1,
          (parafermionicCoverBoxVertices_mem n u.1).mp u.2 |>.2.2.2.2.2⟩) := by
  have hu := (parafermionicCoverBoxVertices_mem n u.1).mp u.2
  let hx : -(n:ℤ) ≤ u.1.1.1 ∧ u.1.1.1 ≤ n := by omega
  let hy : -(n:ℤ) ≤ u.1.1.2 ∧ u.1.1.2 ≤ n := by omega
  let hk : -((n^5:ℕ):ℤ) ≤ u.1.2 ∧ u.1.2 ≤ (n^5:ℤ) :=
    by grind
  have pv := box_vertical_to_zero n u.1.1.1 u.1.1.2 u.1.2 hx hy hk
  have ph := box_horizontal_to_zero n u.1.1.1 u.1.2 hx hk
  have hstart : u = coverBoxPoint n u.1.1.1 u.1.1.2 u.1.2
      ⟨hx.1, hx.2, hy.1, hy.2, hk.1, hk.2⟩ := by
    rfl
  rw [hstart]
  exact SimpleGraph.Walk.append pv ph
end

 theorem cover_lower_seam_adj (k : ℤ) :
    parafermionicCoverGraph.Adj ((0,-1),k) ((1,-1),k+1) := by
  rw [parafermionicCoverGraph_adj_iff_cases]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨rfl, rfl, rfl, by norm_num, rfl⟩))))))

section
variable (n : ℕ)
noncomputable def box_anchor_step (hn : 1 ≤ n) (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k+1 ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
      (coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, by omega⟩)
      (coverBoxPoint n 0 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩) := by
  let a := coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, by omega⟩
  let b := coverBoxPoint n 0 (-1) k ⟨by omega, by omega, by omega, by omega, hk.1, by omega⟩
  let c := coverBoxPoint n 1 (-1) (k+1) ⟨by omega, by omega, by omega, by omega, by omega, hk.2⟩
  let d := coverBoxPoint n 1 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩
  let e := coverBoxPoint n 0 0 (k+1) ⟨by omega, by omega, by omega, by simp, by omega, hk.2⟩
  have hab : (parafermionicCoverBoxGraph n).Adj a b := by
    change parafermionicCoverGraph.Adj a.1 b.1
    dsimp [a,b,coverBoxPoint]
    exact cover_vertical_down_adj 0 (-1) k
  have hbc : (parafermionicCoverBoxGraph n).Adj b c := by
    change parafermionicCoverGraph.Adj b.1 c.1
    dsimp [b,c,coverBoxPoint]
    exact cover_lower_seam_adj k
  have hcd : (parafermionicCoverBoxGraph n).Adj c d := by
    change parafermionicCoverGraph.Adj c.1 d.1
    dsimp [c,d,coverBoxPoint]
    exact cover_vertical_up_adj 1 (-1) (k+1)
  have hde : (parafermionicCoverBoxGraph n).Adj d e := by
    change parafermionicCoverGraph.Adj d.1 e.1
    dsimp [d,e,coverBoxPoint]
    exact cover_horizontal_left_adj 0 (k+1)
  exact .cons hab (.cons hbc (.cons hcd (.cons hde .nil)))

def coverBoxAnchor (k : ℤ)
    (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) : ParafermionicCoverBoxVertex n :=
  coverBoxPoint n 0 0 k ⟨by omega, by omega, by omega, by simp, hk.1, hk.2⟩


 theorem coverBoxAnchor_zero_bounds  :
    -((n^5:ℕ):ℤ) ≤ 0 ∧ 0 ≤ ((n^5:ℕ):ℤ) := by
  omega
end

 section
variable (n m : ℕ)
theorem coverBoxAnchor_pos_bounds (hm : m ≤ n^5) :
    -((n^5:ℕ):ℤ) ≤ (m:ℤ) ∧ (m:ℤ) ≤ ((n^5:ℕ):ℤ) := by
  omega

 theorem coverBoxAnchor_neg_bounds (hm : m+1 ≤ n^5) :
    -((n^5:ℕ):ℤ) ≤ -((m+1:ℕ):ℤ) ∧
      -((m+1:ℕ):ℤ) ≤ ((n^5:ℕ):ℤ) := by
  omega
end

section
variable (n : ℕ) (hn : 1 ≤ n)
include hn
noncomputable def box_anchor_nat_to_zero  :
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
      have hstep : (parafermionicCoverBoxGraph n).Walk
          (coverBoxAnchor n ((m+1:ℕ):ℤ) (coverBoxAnchor_pos_bounds n (m+1) hm))
          (coverBoxAnchor n (m:ℤ)
            (coverBoxAnchor_pos_bounds n m (Nat.le_trans (Nat.le_succ m) hm))) := by
        simpa [coverBoxAnchor] using (box_anchor_step n hn (m:ℤ) hk).reverse
      exact SimpleGraph.Walk.append hstep (ih (by omega))

noncomputable def box_anchor_negative_to_zero  :
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
      have hm' : m+2 ≤ n^5 := by omega
      have hk : -((n^5:ℕ):ℤ) ≤ -((m+2:ℕ):ℤ) ∧
          -((m+2:ℕ):ℤ)+1 ≤ ((n^5:ℕ):ℤ) := by
        omega
      have hstep : (parafermionicCoverBoxGraph n).Walk
          (coverBoxAnchor n (-((m+2:ℕ):ℤ))
            (coverBoxAnchor_neg_bounds n (m+1) hm'))
          (coverBoxAnchor n (-((m+1:ℕ):ℤ))
            (coverBoxAnchor_neg_bounds n m (Nat.le_trans (Nat.le_succ (m+1)) hm'))) := by
        have hcoord : (-2:ℤ) + -(m:ℤ) + 1 = -1 + -(m:ℤ) := by omega
        simpa [coverBoxAnchor, hcoord, Int.negSucc_eq] using
          box_anchor_step n hn (-((m+2:ℕ):ℤ)) hk
      exact SimpleGraph.Walk.append hstep (ih (by omega))

noncomputable def box_anchor_to_zero (k : ℤ) (hk : -((n^5:ℕ):ℤ) ≤ k ∧ k ≤ (n^5:ℤ)) :
    (parafermionicCoverBoxGraph n).Walk
          (coverBoxAnchor n k hk) (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  cases k with
  | ofNat m =>
      have hm := Int.ofNat_le.mp hk.2
      simpa [coverBoxAnchor] using box_anchor_nat_to_zero n hn m hm
  | negSucc m =>
      have hlo : -((n^5:ℕ):ℤ) ≤ -((m+1:ℕ):ℤ) := by
        omega
      have hm : m+1 ≤ n^5 := by omega
      simpa [Int.negSucc_eq, coverBoxAnchor] using
        box_anchor_negative_to_zero n hn m hm

noncomputable def box_vertex_to_zero_anchor_walk (u : ParafermionicCoverBoxVertex n) :
    (parafermionicCoverBoxGraph n).Walk u
      (coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)) := by
  have hu := (parafermionicCoverBoxVertices_mem n u.1).mp u.2
  have hk : -((n^5:ℕ):ℤ) ≤ u.1.2 ∧ u.1.2 ≤ ((n^5:ℕ):ℤ) :=
    by omega
  have p : (parafermionicCoverBoxGraph n).Walk u
      (coverBoxAnchor n u.1.2 hk) := by
    simpa [coverBoxAnchor] using box_vertex_to_anchor n u
  exact SimpleGraph.Walk.append p (box_anchor_to_zero n hn u.1.2 hk)

/-- The actual induced finite cover graph is connected: every vertex reaches
its sheet-zero anchor by coordinate steps, and adjacent anchors are linked by
the literal lower-seam path. -/
theorem parafermionicCoverBoxGraph_connected  :
    (parafermionicCoverBoxGraph n).Connected := by
  let : Nonempty (ParafermionicCoverBoxVertex n) :=
    ⟨coverBoxAnchor n 0 (coverBoxAnchor_zero_bounds n)⟩
  refine ⟨?_⟩
  intro u v
  exact ⟨SimpleGraph.Walk.append
    (box_vertex_to_zero_anchor_walk n hn u)
    (box_vertex_to_zero_anchor_walk n hn v).reverse⟩
end

end
end PottsDiscontinuity.TorusTopology.Planar
