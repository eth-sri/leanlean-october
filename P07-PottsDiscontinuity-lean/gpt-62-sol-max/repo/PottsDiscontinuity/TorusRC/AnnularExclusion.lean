module

public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.DualPathSeparation
public import PottsDiscontinuity.TorusRC.WindingClosure
public import PottsDiscontinuity.TorusRC.WindingPeriods

/-! # A genuine dual vertical winding blocks primal strip crossings -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength TorusTopology SixVertex Duality SimpleGraph

variable {N M : ℕ}

private theorem stripWalk_horizontal (hNp : 0 < N) (hMp : 0 < M)
    (A : RCConfig N M) (a b : ℤ) {u v : RotatedVertex}
    (p : (liftedStripGraph hNp hMp A a b).Walk u v) :
    (a ≤ u.val.1 ∧ u.val.1 ≤ b) → ∀ z ∈ p.support, a ≤ z.val.1 ∧ z.val.1 ≤ b := by
  induction p with
  | nil => simp
  | cons h p ih =>
    simp only [Walk.support_cons, List.mem_cons]
    intro hu z hz
    exact hz.elim (fun e => e ▸ hu) (ih h.2.2.2 z)

section

variable
  (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M)

/-- A vertical primal period in A, shifted into the odd cells of its
complementary translated dual, blocks every left-to-right crossing. The
one-unit horizontal margin accounts for the exact dual translation. -/
theorem winding_blocks_dual_strip_crossing (A : RCConfig N M)
    (K n : ℕ) (hmargin : K+1 ≤ 3*n) (x : ℤ) (hx : Even x)
    (hx0 : 0 ≤ x) (hxK : x ≤ K)
    (hpath : liftedBoundedConnection hNp hMp A 0 K 0 M
      (liftedColumnSite x 0 hx ⟨0,rfl⟩)
      (liftedColumnSite x M hx (by exact_mod_cast hM))) :
    ¬ torusRCLeftStripCrossing hNp hMp (translatedDualConfig A) n := by
  rintro ⟨u,v,hu,hv,⟨p⟩⟩
  obtain ⟨L,hL⟩ := walk_between_periods hMp p
  let T := L + 3*n + K + 3
  have hgap : (M : ℤ)*L + (3*n+K+3 : ℤ) ≤ (M : ℤ)*T := by
    dsimp [T]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ (M : ℤ)-1 by omega)
      (show (0 : ℤ) ≤ 3*n+K+3 by positivity)]
  have hrepeat := winding_path_repeat hM hNp hMp A 0 K x hx hpath (-(T:ℤ)) (2*T)
  rw [show -(T:ℤ)+((2*T:ℕ):ℤ) = T by push_cast; ring] at hrepeat
  obtain ⟨q,_⟩ := hrepeat
  let Q := q.map (stripSquareHom hNp hMp A 0 K (-1))
  have hX := stripWalk_horizontal hNp hMp (translatedDualConfig A) 0 ((3*n:ℕ):ℤ) p
    ⟨by omega,by omega⟩
  have hlevels (z : RotatedVertex) (hz : z ∈ p.support) :
      (squareLift (-1) (periodColumnSite hM x hx (-(T:ℤ)))).2 < (squareLift 0 z).2 ∧
      (squareLift 0 z).2 ≤ (squareLift (-1) (periodColumnSite hM x hx (T:ℤ))).2 := by
    have hcoord (t : ℤ) : 2 * (squareLift (-1) (periodColumnSite hM x hx t)).2 =
        (M : ℤ) * t - x - 2 := by
      have h := squareLift_coordinates (-1) (periodColumnSite hM x hx t)
      change _ = x - (-1) ∧ _ = (M : ℤ) * t + (-1) at h
      omega
    have hlow := hcoord (-(T : ℤ))
    have hhigh := hcoord T
    rw [mul_neg] at hlow
    have hz' := squareLift_coordinates 0 z
    have hx' := hX z hz
    have hy' := hL z hz
    push_cast at hx'
    rw [neg_mul] at hy'
    omega
  have hindex := rayIndex_eq_of_walk_between Q (squareLift 0) p
    (fun h => stripStep_avoids_shiftedDual hNp hMp A h q) hlevels
  -- A vertical dual step straddling the ray level has its rightmost
  -- original column one past the intersection column.
  have hcol (d : FK.squareLattice.Dart) (hd : d ∈ Q.darts) (row : ℤ)
      (hs : ¬ (d.fst.2 < row ↔ d.snd.2 < row)) : 1 ≤ d.fst.1-row ∧ d.fst.1-row ≤ (K : ℤ) := by
    have hadj := (FK.squareLattice_adj_iff _ _).mp d.adj
    have hb : (1 ≤ d.fst.1-d.fst.2 ∧ d.fst.1-d.fst.2 ≤ (K:ℤ)+1) ∧
        (1 ≤ d.snd.1-d.snd.2 ∧ d.snd.1-d.snd.2 ≤ (K:ℤ)+1) := by
      dsimp only [Q] at hd
      rw [Walk.darts_map] at hd
      obtain ⟨e,_,rfl⟩ := List.mem_map.mp hd
      have h₁ := (squareLift_coordinates (-1) e.fst).1
      have h₂ := (squareLift_coordinates (-1) e.snd).1
      have hE := e.adj.2.2
      change (1 ≤ (squareLift (-1) e.fst).1 - (squareLift (-1) e.fst).2 ∧
        (squareLift (-1) e.fst).1 - (squareLift (-1) e.fst).2 ≤ (K : ℤ) + 1) ∧
        (1 ≤ (squareLift (-1) e.snd).1 - (squareLift (-1) e.snd).2 ∧
        (squareLift (-1) e.snd).1 - (squareLift (-1) e.snd).2 ≤ (K : ℤ) + 1)
      omega
    omega
  have hleft : rayIndex (squareLift 0 u) Q = 1 := by
    rw [rayIndex_eq_scaled_heightDiff _ Q 1 (fun d hd hs => by
      have hc := hcol d hd _ hs
      have hu' := (squareLift_coordinates 0 u).1
      rw [ite_eq_left (by omega)])]
    obtain ⟨hl, hr⟩ := hlevels u (by simp)
    rw [mul_one]
    change (if (squareLift (-1) (periodColumnSite hM x hx (-(T : ℤ)))).2 <
        (squareLift 0 u).2 then (1 : ℤ) else 0) -
      (if (squareLift (-1) (periodColumnSite hM x hx T)).2 <
        (squareLift 0 u).2 then 1 else 0) = 1
    simp [if_pos hl, if_neg hr.not_gt]
  have hright : rayIndex (squareLift 0 v) Q = 0 := by
    rw [rayIndex_eq_scaled_heightDiff _ Q 0 (fun d hd hs => by
      have hc := hcol d hd _ hs
      have hv' := (squareLift_coordinates 0 v).1
      rw [ite_eq_right (by omega)]), mul_zero]
  rw [hleft, hright] at hindex
  omega

/-- The actual winding-and-single-open-seam event transfers into the source
barrier B under translated complementary duality. -/
theorem primalWinding_translatedDual_mem_barrier (K n : ℕ) (hmargin : K+1 ≤ 3*n)
    (A : RCConfig N M) (hA : A ∈ primalWindingSingleSeam hNp hMp hM K) :
    translatedDualConfig A ∈ torusRCBarrier hNp hMp n := by
  obtain ⟨x,hx,hx0,hxK,hpath,i₀,hopen,hclosed⟩ := hA
  refine ⟨winding_blocks_dual_strip_crossing hM hNp hMp A K n hmargin x hx hx0 hxK hpath,
    nxt i₀,?_,?_⟩
  · change shiftRCConfig (dualConfig A) (nxt i₀, ⟨0, hMp⟩) = false
    rw [shiftRCConfig_nxt (dualConfig A) (i₀, ⟨0, hMp⟩)]
    change Bool.not (A (i₀, ⟨0, hMp⟩)) = false
    simp [hopen]
  · intro i hi
    have hprv : prv i ≠ i₀ := fun e => hi (by simpa only [Equiv.apply_symm_apply] using congrArg nxt e)
    change Bool.not (A (prv i, ⟨0, hMp⟩)) = true
    rw [hclosed _ hprv]
    rfl

end

end PottsDiscontinuity.TorusRC
