module
public import Mathlib

public import FixedPointTheorems.brouwer
public import PottsDiscontinuity.TorusRC.BoundedChain

/-! # Repeating a genuine lifted vertical period -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology

variable {N M : ℕ}

abbrev verticalDeckStripHom (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b l : ℤ) :
    liftedStripGraph hNp hMp A a b →g liftedStripGraph hNp hMp A a b where
  toFun := verticalDeck hM l
  map_rel' := by
    intro u v h
    exact ⟨verticalDeck_adj hM l h.1,by rw [verticalDeck_index]; exact h.2.1,h.2.2⟩

def periodColumnSite (hM : Even M) (x : ℤ) (hx : Even x) (l : ℤ) : RotatedVertex :=
  liftedColumnSite x ((M:ℤ)*l) hx ((show Even (M:ℤ) by exact_mod_cast hM).mul_right l)

/-- A vertical winding path can be repeated over any finite range of deck
periods, retaining both actual open edges and precise vertical bounds. -/
theorem winding_path_repeat (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b x : ℤ) (hx : Even x)
    (hpath : liftedBoundedConnection hNp hMp A a b 0 M
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) (l : ℤ) (k : ℕ) :
    liftedBoundedConnection hNp hMp A a b ((M:ℤ)*l) ((M:ℤ)*(l+k))
      (periodColumnSite hM x hx l) (periodColumnSite hM x hx (l+k)) := by
  obtain ⟨w,hw⟩ := hpath
  
  induction k with
  | zero =>
    simp only [Nat.cast_zero,add_zero]
    refine ⟨.nil,?_⟩
    intro z hz
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hz
    subst z
    exact ⟨le_rfl,le_rfl⟩
  | succ k ih =>
    obtain ⟨p,hp⟩ := ih
    obtain ⟨q,hq⟩ := (fun (j : ℤ) => by
                        let F := verticalDeckStripHom hM hNp hMp A a b j
                        have hstart : F (liftedColumnSite x 0 hx ⟨0,rfl⟩) = periodColumnSite hM x hx j := by
                          apply Subtype.ext
                          change (x,0+(M:ℤ)*j) = (x,(M:ℤ)*j)
                          simp
                        have hend : F (liftedColumnSite x M hx (by exact_mod_cast hM)) =
                            periodColumnSite hM x hx (j+1) := by
                          apply Subtype.ext
                          change (x,(M:ℤ)+(M:ℤ)*j) = (x,(M:ℤ)*(j+1))
                          ext <;> ring
                        have hconn : liftedBoundedConnection hNp hMp A a b ((M:ℤ)*j) ((M:ℤ)*(j+1))
                            (F (liftedColumnSite x 0 hx ⟨0,rfl⟩))
                            (F (liftedColumnSite x M hx (by exact_mod_cast hM))) := by
                          refine ⟨w.map F,?_⟩
                          intro z hz
                          rw [SimpleGraph.Walk.support_map] at hz
                          obtain ⟨z',hzmem,heq⟩ := List.mem_map.mp hz
                          subst z
                          have h := hw z' hzmem
                          change (M:ℤ)*j ≤ z'.val.2 + (M:ℤ)*j ∧
                            z'.val.2 + (M:ℤ)*j ≤ (M:ℤ)*(j+1)
                          constructor <;> nlinarith
                        simpa only [hstart,hend] using hconn) (l+k)
    have heq : l +  (k+1:ℕ)  =  l+k +1 := by push_cast; ring
    rw [heq]
    refine ⟨p.append q,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_append] at hz
    rcases List.mem_append.mp hz with hz | hz
    · grind
    · have h := hq z (List.mem_of_mem_tail hz)
      grind

/-- Any finite lifted walk fits between a pair of integral vertical periods. -/
theorem walk_between_periods (hMp : 0 < M) {G : SimpleGraph RotatedVertex}
    {u v : RotatedVertex} (p : G.Walk u v) :
    ∃ L : ℕ, ∀ z ∈ p.support, -(M:ℤ)*L ≤ z.val.2 ∧ z.val.2 ≤ (M:ℤ)*L := by
  
  let S := p.support.toFinset
  let L := ∑ z ∈ S, z.val.2.natAbs
  refine ⟨L,?_⟩
  intro z hz
  
  have hcast : (z.val.2.natAbs:ℤ) ≤ L := by exact_mod_cast  Finset.single_le_sum (f := fun z  => z.val.2.natAbs)
                                                                (fun _ _ => Nat.zero_le _) (List.mem_toFinset.mpr hz) 
  have hlo : -z.val.2 ≤  (-z.val.2).natAbs  := Int.le_natAbs
  rw [Int.natAbs_neg] at hlo
  have hhi : z.val.2 ≤  z.val.2.natAbs  := Int.le_natAbs
  
  
  constructor <;> nlinarith

end PottsDiscontinuity.TorusRC
