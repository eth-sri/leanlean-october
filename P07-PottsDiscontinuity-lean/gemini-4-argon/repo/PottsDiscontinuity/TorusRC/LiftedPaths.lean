module

public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.Torus.DiamondGraph

/-!
# The lifted local connection event used in the corrected lower-bound proof

The cover is the rotated lattice of `CorrLength/RotatedLattice.lean`. The diamond edge
joining two neighbours is indexed by the coordinatewise maximum of its endpoints, reduced
modulo the torus periods. This is exactly the index in `Torus.faceEndpointRaw`.
Unlike a torus connection, a cover connection retains the specified lifts.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open Torus CorrLength PottsDiscontinuity.SixVertex

variable {N M : ℕ}

/-- Reduction of an integer coordinate modulo a positive period. -/
def periodicCoordinate (h : 0 < N) (z : ℤ) : Fin N :=
  ⟨(z % (N : ℤ)).toNat, by
    have hnonneg := Int.emod_nonneg z (by omega : (N : ℤ) ≠ 0)
    have hlt := Int.emod_lt_of_pos z (by omega : (0 : ℤ) < N)
    omega⟩

theorem periodicCoordinate_val (h : 0 < N) (z : ℤ) :
    ((periodicCoordinate h z).val : ℤ) = z % (N : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

private theorem periodicCoordinate_parity (h : Even N) (hp : 0 < N) (z : ℤ) :
    ((periodicCoordinate hp z).val : ℤ) % 2 = z % 2 := by
  rw [periodicCoordinate_val]
  exact Int.emod_emod_of_dvd z (Int.natCast_dvd_natCast.mpr h.two_dvd)

private theorem checker_periodicCoordinate (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (x y : ℤ) :
    checker (periodicCoordinate hN x, periodicCoordinate hM y) =
      decide ((x + y) % 2 = 0) := by
  unfold checker
  have hx := periodicCoordinate_parity hNeven hN x
  have hy := periodicCoordinate_parity hMeven hM y
  have hsum : (((periodicCoordinate hN x).val + (periodicCoordinate hM y).val : ℕ) : ℤ) % 2 =
      (x + y) % 2 := by
    rw [Nat.cast_add, Int.add_emod, hx, hy]; omega
  by_cases hp : ((periodicCoordinate hN x).val + (periodicCoordinate hM y).val) % 2 = 0 <;>
    simp [hp, show ((x + y) % 2 = 0) ↔ ((periodicCoordinate hN x).val + (periodicCoordinate hM y).val) % 2 = 0 by omega]

private theorem int_abs_eq_one_iff (z : ℤ) : |z| = 1 ↔ z = 1 ∨ z = -1 := by
  by_cases hz : 0 ≤ z <;> [rw [abs_of_nonneg hz]; rw [abs_of_neg (lt_of_not_ge hz)]] <;> omega

private theorem periodicCoordinate_prev (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z - 1) = prv (periodicCoordinate hp z) := by
  have : NeZero N := ⟨Nat.ne_of_gt hp⟩
  apply Fin.ext; apply Int.ofNat.inj
  change ((periodicCoordinate hp (z - 1)).val : ℤ) = ((finRotate N).symm (periodicCoordinate hp z)).val
  rw [periodicCoordinate_val, ((Int.mod_modEq z (N : ℤ)).sub_right 1).eq.symm,
    finRotate_symm_apply, Fin.coe_int_sub_eq_mod, periodicCoordinate_val]
  norm_num

private theorem periodicCoordinate_add_one_prev (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp z = prv (periodicCoordinate hp (z + 1)) := by
  simpa using periodicCoordinate_prev hp (z + 1)

/-- A lifted vertex projects to the primal face carrier of the diamond torus graph
(`Torus/DiamondGraph.lean`). -/
def liftedFaceVertex (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (u : RotatedVertex) : FaceVertex N M true :=
  ⟨(periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2), by
    rw [checker_periodicCoordinate hNeven hMeven hN hM]
    rcases u.property with ⟨k, hk⟩
    simp [hk]; omega⟩

/-- The indexed edge at the midpoint of a lifted diamond edge. -/
def liftedEdgeIndex (hN : 0 < N) (hM : 0 < M) (u v : RotatedVertex) : Fin N × Fin M :=
  (periodicCoordinate hN (max u.val.1 v.val.1),
    periodicCoordinate hM (max u.val.2 v.val.2))

theorem liftedEdgeIndex_comm (hN : 0 < N) (hM : 0 < M) (u v : RotatedVertex) :
    liftedEdgeIndex hN hM u v = liftedEdgeIndex hN hM v u := by
  simp only [liftedEdgeIndex, max_comm]

/-- Every lifted diagonal edge projects to the corresponding indexed primal
edge of the diamond torus (`Torus/DiamondGraph.lean`). -/
theorem liftedFaceEndpoints_eq (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (u v : RotatedVertex)
    (huv : rotatedLattice.Adj u v) :
    s(liftedFaceVertex hNeven hMeven hN hM u,
        liftedFaceVertex hNeven hMeven hN hM v) =
      s(faceEndpoint hNeven hMeven true (liftedEdgeIndex hN hM u v) false,
        faceEndpoint hNeven hMeven true (liftedEdgeIndex hN hM u v) true) := by
  have hdx := (int_abs_eq_one_iff (u.val.1 - v.val.1)).mp huv.1
  have hdy := (int_abs_eq_one_iff (u.val.2 - v.val.2)).mp huv.2
  have hx : u.val.1 < v.val.1 ∨ v.val.1 < u.val.1 := by omega
  have hy : u.val.2 < v.val.2 ∨ v.val.2 < u.val.2 := by omega
  rw [Sym2.eq_iff]
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hux : v.val.1 = u.val.1 + 1 := by omega
    have huy : v.val.2 = u.val.2 + 1 := by omega
    have hchk : checker (liftedEdgeIndex hN hM u v) = true := by
      rcases v.property with ⟨k, hk⟩
      simp [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_right_of_lt hy,
        checker_periodicCoordinate hNeven hMeven hN hM]; omega
    exact Or.inr ⟨Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_right_of_lt hy]
        simp only [hux, huy, ← periodicCoordinate_add_one_prev]),
      Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_right_of_lt hy])⟩
  · have hux : v.val.1 = u.val.1 + 1 := by omega
    have huy : u.val.2 = v.val.2 + 1 := by omega
    have hchk : checker (liftedEdgeIndex hN hM u v) = false := by
      rcases u.property with ⟨k, hk⟩
      simp [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_left_of_lt hy,
        checker_periodicCoordinate hNeven hMeven hN hM]; omega
    exact Or.inl ⟨Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_left_of_lt hy]
        simp only [hux, ← periodicCoordinate_add_one_prev]),
      Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_left_of_lt hy]
        simp only [huy, ← periodicCoordinate_add_one_prev])⟩
  · have hux : u.val.1 = v.val.1 + 1 := by omega
    have huy : v.val.2 = u.val.2 + 1 := by omega
    have hchk : checker (liftedEdgeIndex hN hM u v) = false := by
      rcases v.property with ⟨k, hk⟩
      simp [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_right_of_lt hy,
        checker_periodicCoordinate hNeven hMeven hN hM]; omega
    exact Or.inr ⟨Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_right_of_lt hy]
        simp only [huy, ← periodicCoordinate_add_one_prev]),
      Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_right_of_lt hy]
        simp only [hux, ← periodicCoordinate_add_one_prev])⟩
  · have hux : u.val.1 = v.val.1 + 1 := by omega
    have huy : u.val.2 = v.val.2 + 1 := by omega
    have hchk : checker (liftedEdgeIndex hN hM u v) = true := by
      rcases u.property with ⟨k, hk⟩
      simp [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_left_of_lt hy,
        checker_periodicCoordinate hNeven hMeven hN hM]; omega
    exact Or.inl ⟨Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, Bool.false_eq_true, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_left_of_lt hy]),
      Subtype.ext (by
        simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hchk, ↓reduceIte]
        simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_left_of_lt hy]
        simp only [hux, huy, ← periodicCoordinate_add_one_prev])⟩

/-- Open lifted diamond edges with both endpoints in a horizontal strip.
The strip bounds are in the integer cover, not reduced modulo N. -/
def liftedStripGraph (hN : 0 < N) (hM : 0 < M) (A : RCConfig N M)
    (a b : ℤ) : SimpleGraph RotatedVertex where
  Adj u v := rotatedLattice.Adj u v ∧ A (liftedEdgeIndex hN hM u v) = true ∧
    (a ≤ u.val.1 ∧ u.val.1 ≤ b) ∧ (a ≤ v.val.1 ∧ v.val.1 ≤ b)
  symm.symm u v h := ⟨h.1.symm, (liftedEdgeIndex_comm hN hM v u).symm ▸ h.2.1, h.2.2.2, h.2.2.1⟩
  loopless.irrefl u h := rotatedLattice.loopless.irrefl u h.1

theorem liftedStripGraph_mono (hN : 0 < N) (hM : 0 < M)
    {A B : RCConfig N M} (a b : ℤ) (hAB : A ≤ B) :
    liftedStripGraph hN hM A a b ≤ liftedStripGraph hN hM B a b := by
  intro u v huv
  have hval := hAB (liftedEdgeIndex hN hM u v)
  rw [huv.2.1] at hval
  exact ⟨huv.1, eq_top_iff.mpr hval, huv.2.2⟩

private theorem walk_mono_support {V : Type*} {G H : SimpleGraph V}
    (hGH : G ≤ H) {u v : V} (w : G.Walk u v) :
    ∃ w' : H.Walk u v, w'.support = w.support := by
  induction w with
  | nil => exact ⟨.nil, rfl⟩
  | @cons u v w hadj p ih =>
    obtain ⟨p', hp⟩ := ih
    exact ⟨.cons (hGH hadj) p', by simp [hp]⟩

/-- Membership of a lifted vertex in a square centred at a specified lift. -/
def inLiftedBox (R : ℕ) (c z : RotatedVertex) : Prop :=
  |z.val.1 - c.val.1| ≤ (R : ℤ) ∧ |z.val.2 - c.val.2| ≤ (R : ℤ)

/-- Connection inside a finite box in the specified horizontal strip. -/
def liftedBoxConnection (hN : 0 < N) (hM : 0 < M) (A : RCConfig N M)
    (a b : ℤ) (R : ℕ) (u v : RotatedVertex) : Prop :=
  ∃ w : (liftedStripGraph hN hM A a b).Walk u v,
    ∀ z ∈ w.support, inLiftedBox R u z

theorem liftedBoxConnection_mono (hN : 0 < N) (hM : 0 < M)
    {A B : RCConfig N M} (a b : ℤ) (R : ℕ) (u v : RotatedVertex)
    (hAB : A ≤ B) (hconn : liftedBoxConnection hN hM A a b R u v) :
    liftedBoxConnection hN hM B a b R u v := by
  obtain ⟨w, hw⟩ := hconn
  obtain ⟨w', hsupport⟩ := walk_mono_support (liftedStripGraph_mono hN hM a b hAB) w
  exact ⟨w', hsupport ▸ hw⟩

/-- Corrected proof-internal chain event: every adjacent pair uses its prescribed lifts. -/
def liftedChainEvent (hN : 0 < N) (hM : 0 < M) (a b : ℤ)
    (R : ℕ) (y : ℕ → RotatedVertex) (k : ℕ) : Set (RCConfig N M) :=
  {A | ∀ j < k, liftedBoxConnection hN hM A a b R (y j) (y (j + 1))}

/-- Concatenating the actual lifted local paths preserves their lifted endpoints. -/
theorem liftedChainEvent_reachable (hN : 0 < N) (hM : 0 < M) (a b : ℤ)
    (R : ℕ) (y : ℕ → RotatedVertex) (k : ℕ) (A : RCConfig N M)
    (hA : A ∈ liftedChainEvent hN hM a b R y k) :
    (liftedStripGraph hN hM A a b).Reachable (y 0) (y k) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    obtain ⟨w, _⟩ := hA k (Nat.lt_succ_self k)
    exact (ih fun j hj => hA j (Nat.lt_succ_of_lt hj)).trans ⟨w⟩

/-- The even-column lifted point `(x,t)`. -/
def liftedColumnSite (x t : ℤ) (hx : Even x) (ht : Even t) : RotatedVertex :=
  ⟨(x, t), hx.add ht⟩

/-- A lifted vertical period closes at the same finite primal face vertex. -/
theorem liftedFaceVertex_vertical_period (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (x : ℤ) (hx : Even x) :
    liftedFaceVertex hNeven hMeven hN hM (liftedColumnSite x 0 hx ⟨0, rfl⟩) =
      liftedFaceVertex hNeven hMeven hN hM
        (liftedColumnSite x (M : ℤ) hx (by exact_mod_cast hMeven)) := by
  refine Subtype.ext (Prod.ext rfl (Fin.ext ?_))
  simp [liftedFaceVertex, liftedColumnSite, periodicCoordinate]

/-- The actual sites y_j=(x,2nj), before projection to the torus. -/
def liftedChainSite (x : ℤ) (hx : Even x) (n j : ℕ) : RotatedVertex :=
  liftedColumnSite x (2 * (n : ℤ) * j) hx ⟨(n : ℤ) * j, by ring⟩

end PottsDiscontinuity.TorusRC
