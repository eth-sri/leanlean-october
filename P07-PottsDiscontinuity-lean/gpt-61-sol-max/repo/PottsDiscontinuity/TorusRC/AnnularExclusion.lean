module
public import Mathlib

public import PottsDiscontinuity.Duality.RectanglePathIntersection
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.DualPathSeparation
public import PottsDiscontinuity.TorusRC.WindingClosure
public import PottsDiscontinuity.TorusRC.WindingPeriods

/-! # A genuine dual vertical winding blocks primal strip crossings -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology SixVertex

variable {N M : ℕ}

private theorem stripWalk_horizontal (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b : ℤ) {u v : RotatedVertex}
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) :
     a ≤ u.val.1 ∧ u.val.1 ≤ b  → ∀ z ∈ p.support, a ≤ z.val.1 ∧ z.val.1 ≤ b := by
  induction p with
  | nil =>
    simp_all
  | @cons u v z hadj p ih =>
    intro hu w hw
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hu
    · exact ih hadj.2.2.2 w hw

section

variable (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)


/-- A vertical primal period in A, shifted into the odd cells of its
complementary translated dual, blocks every left-to-right crossing. The
one-unit horizontal margin accounts for the exact dual translation. -/
theorem winding_blocks_dual_strip_crossing  (A : RCConfig N M)
    (K n : ℕ) (hmargin : K+1 ≤ 3*n) (x : ℤ) (hx : Even x)
    (hx0 : 0 ≤ x) (hxK : x ≤ K)
    (hpath : liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) :
    ¬ torusRCLeftStripCrossing hNp hMp (translatedDualConfig A) n := by
  rintro ⟨u,v,hu,hv,⟨p⟩⟩
  obtain ⟨L,hL⟩ := walk_between_periods hMp p
  have hrepeat := winding_path_repeat hM hNp hMp A 0 K x hx hpath (- L ) (2*L)
  have hupper : - L +((2*L:ℕ):ℤ) = L := by push_cast; ring
  have hlower :  M * - L   = -(M:ℤ)*L := by ring
  rw [hupper,hlower] at hrepeat
  obtain ⟨q,hq⟩ := hrepeat
  let f : RotatedVertex → ℝ × ℝ := fun z => cellEmbed z.val
  let g  := fun z => cellEmbed (dualShiftCell z)
  let P := polygonWalkPath f p
  let Q := polygonWalkPath g q
  let a : ℝ × ℝ := (0,(- M *L:ℤ))
  let b  := (((3*n:ℕ):ℝ), (( M * L :ℤ):ℝ))
  
  
  
  
  
  
  
  
  
  obtain ⟨s,t,hst⟩ := FK.Curves.pathRectangle_crossing_intersection P Q (by
                                                                           intro t
                                                                           have h := polygonWalkPath_mem_Icc f p a b (fun z hz => by
                                                                             have hX := (stripWalk_horizontal hNp hMp (translatedDualConfig A) 0 ((3*n:ℕ):ℤ) p
                                                                                           ⟨by omega,by omega⟩) z hz
                                                                             have hY := hL z hz
                                                                             dsimp only [f, cellEmbed, a, b]
                                                                             constructor <;> constructor <;> simp only
                                                                             · exact_mod_cast hX.1
                                                                             · exact_mod_cast hY.1
                                                                             · exact_mod_cast hX.2
                                                                             · exact_mod_cast hY.2) t
                                                                           exact ⟨h.1.1,h.2.1,h.1.2,h.2.2⟩) (by
                                                                                 intro t
                                                                                 have h := polygonWalkPath_mem_Icc g q a b (fun z hz => by
                                                                                   have hX := (stripWalk_horizontal hNp hMp A 0 K q ⟨hx0,hxK⟩) z hz
                                                                                   have hY := hq z hz
                                                                                   dsimp only [f,g,cellEmbed,dualShiftCell,a,b,Prod.fst,Prod.snd]
                                                                                   constructor <;> constructor <;> simp only
                                                                                   · exact_mod_cast  by omega 
                                                                                   · exact_mod_cast hY.1
                                                                                   · exact_mod_cast  by omega 
                                                                                   · exact_mod_cast hY.2) t
                                                                                 exact ⟨h.1.1,h.2.1,h.1.2,h.2.2⟩)
    (by
       calc
         (P 0).1 = (f u).1 := congrArg Prod.fst P.source'
         _ = a.1 := ?_
       change (u.val.1:ℝ) = 0
       exact_mod_cast hu) (by
              calc
                (P 1).1 = (f v).1 := congrArg Prod.fst P.target'
                _ = b.1 := ?_
              change  v.val.1  = ((3*n:ℕ):ℝ)
              exact_mod_cast hv) (by
                      calc
                        (Q 0).2 = (g (periodColumnSite hM x hx (- L ))).2 := congrArg Prod.snd Q.source'
                        _ = a.2 := ?_
                      change  ( M * - L  :ℤ)  = ((- M *L:ℤ):ℝ)
                      congr 1) (by
                                                             exact Trans.trans (congrArg Prod.snd Q.target') rfl)
  exact Set.disjoint_left.mp (opposite_open_walks_disjoint hNp hMp A 0  (3*n:ℕ)  0 K p q)
    ⟨s,rfl⟩ ⟨t,hst.symm⟩

/-- The actual winding-and-single-open-seam event transfers into the source
barrier B under translated complementary duality. -/
theorem primalWinding_translatedDual_mem_barrier  (K n : ℕ) (hmargin : K+1 ≤ 3*n)
    (A : RCConfig N M) (hA : A ∈ primalWindingSingleSeam hNp hMp hM K) :
    translatedDualConfig A ∈ torusRCBarrier hNp hMp n := by
  obtain ⟨x,hx,hx0,hxK,hpath,i₀,hopen,hclosed⟩ := hA
  refine ⟨winding_blocks_dual_strip_crossing hM hNp hMp A K n hmargin x hx hx0 hxK hpath,
    nxt i₀,?_,?_⟩
  · change shiftRCConfig (dualConfig A) (nxt i₀,⟨0,hMp⟩) = false
    rw [shiftRCConfig_nxt (dualConfig A) (i₀, ⟨0,hMp⟩ )]
    change Bool.not (A (i₀,⟨0,hMp⟩)) = false
    rw [hopen]
    rfl
  · intro i hi
    
    change Bool.not (A (prv i,⟨0,hMp⟩)) = true
    rw [hclosed (prv i) (by
                           grind)]
    rfl

end

end PottsDiscontinuity.TorusRC
