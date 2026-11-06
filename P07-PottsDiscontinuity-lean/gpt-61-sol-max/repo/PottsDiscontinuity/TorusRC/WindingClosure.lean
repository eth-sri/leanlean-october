module
public import Mathlib

public import PottsDiscontinuity.TorusRC.BoundedChain
public import PottsDiscontinuity.TorusRC.ColumnZigzag

/-! # The finite terminal zigzag and the source winding event -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength

variable {N M : ℕ}

/-- The source's primal winding event, with an explicit integer lift and a
single open seam edge. The width K is an honest geometric parameter. -/
def primalWindingSingleSeam (hNp : 0 < N) (hMp : 0 < M) (hM : Even M)
    (K : ℕ) : Set (RCConfig N M) :=
  {A | ∃ x : ℤ, ∃ hx : Even x, 0 ≤ x ∧ x ≤ (K : ℤ) ∧
    liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM)) ∧
    ∃ i₀ : Fin N, A (i₀,⟨0,hMp⟩) = true ∧
      ∀ i : Fin N, i ≠ i₀ → A (i,⟨0,hMp⟩) = false}

/-- Indexed edges of the terminal zigzag from height H to M. -/
def terminalZigzagEdges (hNp : 0 < N) (hMp : 0 < M) (x : ℤ) (H : ℕ) :
    Finset (Fin N × Fin M) :=
  (Finset.Ico H M).image  fun k : ℕ =>
    (periodicCoordinate hNp (x + 1),periodicCoordinate hMp ((k : ℤ) + 1)) 

section

variable (hNp : 0 < N) (hMp : 0 < M)
include hNp hMp

section

variable (x : ℤ) (H : ℕ)


theorem terminalZigzagEdges_card_le   :
    (terminalZigzagEdges hNp hMp x H).card ≤ M - H :=
  Finset.card_image_le.trans_eq (Nat.card_Ico H M)

theorem terminalZigzagEdges_column  
    (e : Fin N × Fin M) (he : e ∈ terminalZigzagEdges hNp hMp x H) :
    e.1 = periodicCoordinate hNp (x + 1) := by
  grind +locals

theorem terminalZigzagEdges_contains_seam   (hH : H < M) :
    (periodicCoordinate hNp (x + 1),(⟨0,hMp⟩ : Fin M)) ∈
      terminalZigzagEdges hNp hMp x H := by
  apply Finset.mem_image.mpr
  refine ⟨M - 1, Finset.mem_Ico.mpr ⟨by omega,by omega⟩,?_⟩
  apply Prod.ext
  · rfl
  apply Fin.ext
  change (( (M - 1 : ℕ)  + 1) % (M : ℤ)).toNat = 0
  simp_all

end

/-- The terminal zigzag with its precise vertical range, rather than just a
box localization. -/
theorem columnZigzag_bounded_connection 
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x) (s t : ℕ)
    (hst : s ≤ t) (ha : a ≤ x) (hb : x + 1 ≤ b)
    (hopen : ∀ k, s ≤ k → k < t →
      A (periodicCoordinate hNp (x + 1),periodicCoordinate hMp ((k : ℤ) + 1)) = true) :
    liftedBoundedConnection hNp hMp A a b s t
      (columnZigzagSite x hx s) (columnZigzagSite x hx t) := by
  have hwalk (d : ℕ) (hd : s + d ≤ t) :
      ∃ w : (liftedStripGraph hNp hMp A a b).Walk
        (columnZigzagSite x hx s) (columnZigzagSite x hx (s + d)),
        ∀ z ∈ w.support,  s  ≤ z.val.2 ∧ z.val.2 ≤  t  := by
    induction d with
    | zero =>
      refine ⟨.nil,?_⟩
      intro z hz
      simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
      subst z
      dsimp [columnZigzagSite]
      constructor <;> omega
    | succ d ih =>
      obtain ⟨w,hw⟩ := ih (by omega)
      have hadj : (liftedStripGraph hNp hMp A a b).Adj
          (columnZigzagSite x hx (s + d)) (columnZigzagSite x hx (s + (d + 1))) := by
        refine ⟨columnZigzagSite_adj x hx (s + d),?_,?_,?_⟩
        · rw [← Nat.add_assoc,columnZigzagSite_index]
          all_goals grind
        · grind [columnZigzagSite]
        · grind [columnZigzagSite]
      refine ⟨w.append (.cons hadj .nil),?_⟩
      intro z hz
      rw [SimpleGraph.Walk.support_append] at hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · simp only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
          List.tail_cons,List.mem_singleton] at hz
        subst z
        dsimp [columnZigzagSite]
        constructor <;> omega
  have h := hwalk (t-s) (by omega)
  rw [Nat.add_sub_of_le hst] at h
  exact h

/-- Closing all other seam edges preserves the bounded chain and the chosen
terminal zigzag, which together produce the source's primal winding event. -/
theorem boundedChain_terminal_implies_winding 
    (hM : Even M) (n : ℕ) (i : Fin (3 * n + 1)) (hi : Even (i.val : ℤ))
    (k : ℕ) (hheight : 2 * n * k < M) (A : RCConfig N M)
    (hchain : A ∈ boundedRectangleChain hNp hMp n i hi k)
    (hterminal : ∀ e ∈ terminalZigzagEdges hNp hMp i.val (2 * n * k), A e = true)
    (hclosed : ∀ j : Fin N, j ≠ periodicCoordinate hNp ((i.val : ℤ) + 1) →
      A (j,⟨0,hMp⟩) = false) :
    A ∈ primalWindingSingleSeam hNp hMp hM (3 * n + 1) := by
  obtain ⟨w,hw⟩ := hchain
  let F : liftedStripGraph hNp hMp A 0 (3 *  n ) →g
      liftedStripGraph hNp hMp A 0  (3 * n + 1 )  :=
    ⟨id,fun h => ⟨h.1,h.2.1,
      ⟨h.2.2.1.1,by have hh := h.2.2.1.2
                    grind⟩,
      ⟨h.2.2.2.1,by have hh := h.2.2.2.2
                    grind⟩⟩⟩
  have hz0 : liftedChainSite i.val hi n 0 = liftedColumnSite i.val 0 hi ⟨0,rfl⟩ := rfl
  
  have hzH : columnZigzagSite i.val hi (2 * n * k) = liftedChainSite i.val hi n k := by
    rw [columnZigzagSite_even _ _ _  ⟨n*k,by ring⟩ ]
    
    simp [liftedChainSite]
  have htail := columnZigzag_bounded_connection hNp hMp A 0 (3 * n + 1 )
    i.val hi (2*n*k) M hheight.le (by omega) (by   omega)
     fun j hj hjM => hterminal _ (Finset.mem_image.mpr
      ⟨j,Finset.mem_Ico.mpr ⟨hj,hjM⟩,rfl⟩) 
  rw [hzH,columnZigzagSite_even _ _ _ hM] at htail
  obtain ⟨p,hp⟩ := htail
  refine ⟨i.val,hi,by omega,by have hh := i.isLt; exact_mod_cast Nat.le_of_lt hh,?_,
    periodicCoordinate hNp ((i.val )+1),?_,hclosed⟩
  · rw [← hz0]
    refine ⟨(w.map F).append p,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz | hz
    · rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨z',hz',heq⟩ := List.mem_map.mp hz
      change z' = z at heq
      grind
    · have h := hp z (List.mem_of_mem_tail hz)
      constructor <;> omega
  · grind [terminalZigzagEdges_contains_seam]

end

end PottsDiscontinuity.TorusRC
