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
    simp_all [Int.emod_lt_of_pos]⟩

theorem periodicCoordinate_val (h : 0 < N) (z : ℤ) :
    ((periodicCoordinate h z).val : ℤ) = z % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

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
  grind

private theorem int_abs_eq_one_iff (z : ℤ) : |z| = 1 ↔ z = 1 ∨ z = -1 := by
  grind

private theorem periodicCoordinate_prev (hp : 0 < N) (z : ℤ) :
    periodicCoordinate hp (z - 1) = prv (periodicCoordinate hp z) := by
  have : NeZero N := ⟨Nat.ne_of_gt hp⟩
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hp (z - 1)).val : ℤ) =
    ((prv (periodicCoordinate hp z)).val : ℤ)
  rw [periodicCoordinate_val]
  have hmod : (z - 1) % (N : ℤ) = (z % (N : ℤ) - 1) % (N : ℤ) := by
    simp
  rw [hmod]
  have hprv : prv (periodicCoordinate hp z) = periodicCoordinate hp z - 1 := by
    simp
  rw [hprv, Fin.coe_int_sub_eq_mod, periodicCoordinate_val]
  norm_num


/-- A lifted vertex projects to the primal face carrier of the diamond torus graph
(`Torus/DiamondGraph.lean`). -/
def liftedFaceVertex (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (u : RotatedVertex) : FaceVertex N M true :=
  ⟨(periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2), by simp [checker_periodicCoordinate hNeven hMeven,
    Int.even_iff.mp u.property]⟩

section

variable (hN : 0 < N) (hM : 0 < M) (u v : RotatedVertex)

/-- The indexed edge at the midpoint of a lifted diamond edge. -/
def liftedEdgeIndex : Fin N × Fin M :=
  (periodicCoordinate hN (max u.val.1 v.val.1),
    periodicCoordinate hM (max u.val.2 v.val.2))

theorem liftedEdgeIndex_comm :
    liftedEdgeIndex hN hM u v = liftedEdgeIndex hN hM v u := by
  simp only [liftedEdgeIndex, max_comm]

end

/-- Every lifted diagonal edge projects to the corresponding indexed primal
edge of the diamond torus (`Torus/DiamondGraph.lean`). -/
theorem liftedFaceEndpoints_eq (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (u v : RotatedVertex)
    (huv : rotatedLattice.Adj u v) :
    s(liftedFaceVertex hNeven hMeven hN hM u,
        liftedFaceVertex hNeven hMeven hN hM v) =
      s(faceEndpoint hNeven hMeven true (liftedEdgeIndex hN hM u v) false,
        faceEndpoint hNeven hMeven true (liftedEdgeIndex hN hM u v) true) := by
  have hdx := (int_abs_eq_one_iff _).mp huv.1
  wlog hx : u.val.1 ≤ v.val.1 generalizing u v
  · rw [Sym2.eq_swap (a := liftedFaceVertex hNeven hMeven hN hM u),
      liftedEdgeIndex_comm hN hM u v]
    exact this v u huv.symm (by omega) (by omega)
  have ex : v.val.1 - 1 = u.val.1 := by omega
  rcases (int_abs_eq_one_iff _).mp huv.2 with hy | hy
  · have ey : u.val.2 - 1 = v.val.2 := by omega
    have hi : liftedEdgeIndex hN hM u v =
        (periodicCoordinate hN v.val.1, periodicCoordinate hM u.val.2) := by
      simp [liftedEdgeIndex, max_eq_right hx, max_eq_left (show v.val.2 ≤ u.val.2 by omega)]
    have hc : checker (liftedEdgeIndex hN hM u v) = false := by
      rw [hi, checker_periodicCoordinate hNeven hMeven]
      have := Int.even_iff.mp u.property
      simp only [decide_eq_false_iff_not]
      omega
    simp only [hi] at hc
    rw [Sym2.eq_iff]
    left
    constructor <;> apply Subtype.ext <;>
      simp only [liftedFaceVertex, faceEndpoint, faceEndpointRaw, hi, hc, Bool.false_eq_true,
        ite_true, ite_false, ← periodicCoordinate_prev, ex, ey]
  · have ey : v.val.2 - 1 = u.val.2 := by omega
    have hi : liftedEdgeIndex hN hM u v = (liftedFaceVertex hNeven hMeven hN hM v).val := by
      simp [liftedEdgeIndex, liftedFaceVertex, max_eq_right hx, max_eq_right (show u.val.2 ≤ v.val.2 by omega)]
    have hc : checker (liftedEdgeIndex hN hM u v) = true := hi ▸ (liftedFaceVertex hNeven hMeven hN hM v).property
    simp only [hi, liftedFaceVertex] at hc
    rw [Sym2.eq_iff]
    right
    constructor <;> apply Subtype.ext <;>
      simp only [faceEndpoint, faceEndpointRaw, hi, liftedFaceVertex, hc, Bool.false_eq_true, ite_true, ite_false,
        ← periodicCoordinate_prev, ex, ey]

/-- Open lifted diamond edges with both endpoints in a horizontal strip.
The strip bounds are in the integer cover, not reduced modulo N. -/
def liftedStripGraph (hN : 0 < N) (hM : 0 < M) (A : RCConfig N M)
    (a b : ℤ) : SimpleGraph RotatedVertex where
  Adj u v := rotatedLattice.Adj u v ∧ A (liftedEdgeIndex hN hM u v) = true ∧
    (a ≤ u.val.1 ∧ u.val.1 ≤ b) ∧ (a ≤ v.val.1 ∧ v.val.1 ≤ b)
  symm.symm u v h := by
    exact ⟨h.1.symm, (liftedEdgeIndex_comm hN hM v u).symm ▸ h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless.irrefl u h := by
    simp_all

theorem liftedStripGraph_mono (hN : 0 < N) (hM : 0 < M)
    {A B : RCConfig N M} (a b : ℤ) (hAB : A ≤ B) :
    liftedStripGraph hN hM A a b ≤ liftedStripGraph hN hM B a b := by
  intro u v huv
  have hval := hAB (liftedEdgeIndex hN hM u v)
  rw [huv.2.1] at hval
  have hout : B (liftedEdgeIndex hN hM u v) = true := by
    aesop
  exact ⟨huv.1, hout, huv.2.2⟩

/-- Membership of a lifted vertex in a square centred at a specified lift. -/
def inLiftedBox (R : ℕ) (c z : RotatedVertex) : Prop :=
  |z.val.1 - c.val.1| ≤ (R : ℤ) ∧ |z.val.2 - c.val.2| ≤ (R : ℤ)

section

variable (hN : 0 < N) (hM : 0 < M)

/-- Connection inside a finite box in the specified horizontal strip. -/
def liftedBoxConnection (A : RCConfig N M)
    (a b : ℤ) (R : ℕ) (u v : RotatedVertex) : Prop :=
  ∃ w : (liftedStripGraph hN hM A a b).Walk u v,
    ∀ z ∈ w.support, inLiftedBox R u z

theorem liftedBoxConnection_mono
    {A B : RCConfig N M} (a b : ℤ) (R : ℕ) (u v : RotatedVertex)
    (hAB : A ≤ B) (hconn : liftedBoxConnection hN hM A a b R u v) :
    liftedBoxConnection hN hM B a b R u v := by
  obtain ⟨w, hw⟩ := hconn
  exact ⟨w.mapLe (liftedStripGraph_mono hN hM a b hAB), by simpa using hw⟩

/-- Corrected proof-internal chain event: every adjacent pair uses its prescribed lifts. -/
def liftedChainEvent (a b : ℤ)
    (R : ℕ) (y : ℕ → RotatedVertex) (k : ℕ) : Set (RCConfig N M) :=
  {A | ∀ j < k, liftedBoxConnection hN hM A a b R (y j) (y (j + 1))}

/-- Concatenating the actual lifted local paths preserves their lifted endpoints. -/
theorem liftedChainEvent_reachable (a b : ℤ)
    (R : ℕ) (y : ℕ → RotatedVertex) (k : ℕ) (A : RCConfig N M)
    (hA : A ∈ liftedChainEvent hN hM a b R y k) :
    (liftedStripGraph hN hM A a b).Reachable (y 0) (y k) := by
  induction k with
  | zero => exact SimpleGraph.Reachable.refl _
  | succ k ih =>
    have hprev :=
      fun j hj => hA j (Nat.lt_succ_of_lt hj)
    obtain ⟨w, _⟩ := hA k (Nat.lt_succ_self k)
    exact (ih hprev).trans ⟨w⟩

end

/-- The even-column lifted point `(x,t)`. -/
def liftedColumnSite (x t : ℤ) (hx : Even x) (ht : Even t) : RotatedVertex :=
  ⟨(x, t), hx.add ht⟩

/-- A lifted vertical period closes at the same finite primal face vertex. -/
theorem liftedFaceVertex_vertical_period (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (x : ℤ) (hx : Even x) :
    liftedFaceVertex hNeven hMeven hN hM (liftedColumnSite x 0 hx ⟨0, rfl⟩) =
      liftedFaceVertex hNeven hMeven hN hM
        (liftedColumnSite x (M : ℤ) hx (by exact_mod_cast hMeven)) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    simp [liftedFaceVertex, liftedColumnSite, periodicCoordinate]

/-- The actual sites y_j=(x,2nj), before projection to the torus. -/
def liftedChainSite (x : ℤ) (hx : Even x) (n j : ℕ) : RotatedVertex :=
  liftedColumnSite x (2 * (n : ℤ) * j) hx (by
    use (n : ℤ) * j
    ring)

end PottsDiscontinuity.TorusRC
