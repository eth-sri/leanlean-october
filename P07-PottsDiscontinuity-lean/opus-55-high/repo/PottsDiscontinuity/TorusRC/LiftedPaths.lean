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
    ((periodicCoordinate h z).val : ℤ) = z % (N : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

theorem periodicCoordinate_parity (h : Even N) (hp : 0 < N) (z : ℤ) :
    ((periodicCoordinate hp z).val : ℤ) % 2 = z % 2 := by
  rw [periodicCoordinate_val]
  exact Int.emod_emod_of_dvd z (Int.natCast_dvd_natCast.mpr h.two_dvd)

theorem checker_periodicCoordinate (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (x y : ℤ) :
    checker (periodicCoordinate hN x, periodicCoordinate hM y) =
      decide ((x + y) % 2 = 0) := by
  grind [checker, periodicCoordinate_parity, periodicCoordinate]

section
variable (hp : 0 < N) (z : ℤ)
theorem periodicCoordinate_sub_one  :
    periodicCoordinate hp (z - 1) = prv (periodicCoordinate hp z) := by
  have : NeZero N := ⟨Nat.ne_of_gt hp⟩
  apply Fin.ext
  apply Int.ofNat.inj
  change ((periodicCoordinate hp (z - 1)).val : ℤ) =
    ((prv (periodicCoordinate hp z)).val : ℤ)
  have hprv : prv (periodicCoordinate hp z) = periodicCoordinate hp z - 1 := by
    simp
  rw [hprv, Fin.coe_int_sub_eq_mod]
  simp [periodicCoordinate_val]

theorem periodicCoordinate_add_one_prev  :
    periodicCoordinate hp z = prv (periodicCoordinate hp (z + 1)) := by
  simpa using periodicCoordinate_sub_one hp (z + 1)

theorem periodicCoordinate_add_one  :
    periodicCoordinate hp (z + 1) = nxt (periodicCoordinate hp z) := by
  have hh := periodicCoordinate_sub_one hp (z + 1)
  grind
end

/-- A lifted vertex projects to the primal face carrier of the diamond torus graph
(`Torus/DiamondGraph.lean`). -/
def liftedFaceVertex (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (u : RotatedVertex) : FaceVertex N M true :=
  ⟨(periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2), by
    grind [periodicCoordinate, checker, periodicCoordinate_parity, ZMod]⟩

section
variable (hN : 0 < N) (hM : 0 < M)
/-- The indexed edge at the midpoint of a lifted diamond edge. -/
def liftedEdgeIndex (u v : RotatedVertex) : Fin N × Fin M :=
  (periodicCoordinate hN (max u.val.1 v.val.1),
    periodicCoordinate hM (max u.val.2 v.val.2))

theorem liftedEdgeIndex_comm (u v : RotatedVertex) :
    liftedEdgeIndex hN hM u v = liftedEdgeIndex hN hM v u := by
  grind [liftedEdgeIndex]
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
  have hdx := (abs_eq zero_le_one).1 huv.1
  have hdy := (abs_eq zero_le_one).1 huv.2
  have hx : u.val.1 < v.val.1 ∨ v.val.1 < u.val.1 := by omega
  have hy : u.val.2 < v.val.2 ∨ v.val.2 < u.val.2 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hchecker :
        checker (periodicCoordinate hN (max u.val.1 v.val.1),
          periodicCoordinate hM (max u.val.2 v.val.2)) = true := by
      grind [checker_periodicCoordinate]
    have hcheckerIdx : checker (liftedEdgeIndex hN hM u v) = true := by
      tauto
    simp
    right
    constructor
    · apply Subtype.ext
      change (periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) true
      grind [faceEndpointRaw, liftedEdgeIndex, periodicCoordinate_add_one_prev]
    · apply Subtype.ext
      change (periodicCoordinate hN v.val.1, periodicCoordinate hM v.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) false
      simp only [faceEndpointRaw, hcheckerIdx]
      simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_right_of_lt hy]
      rfl
  · have hchecker :
        checker (periodicCoordinate hN (max u.val.1 v.val.1),
          periodicCoordinate hM (max u.val.2 v.val.2)) = false := by
      grind [checker_periodicCoordinate]
    have hcheckerIdx : checker (liftedEdgeIndex hN hM u v) = false := by
      tauto
    simp
    left
    constructor
    · apply Subtype.ext
      change (periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) false
      simp only [faceEndpointRaw, hcheckerIdx]
      simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_left_of_lt hy]
      apply Prod.ext
      · grind [periodicCoordinate_add_one_prev]
      rfl
    · apply Subtype.ext
      change (periodicCoordinate hN v.val.1, periodicCoordinate hM v.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) true
      simp only [faceEndpointRaw, hcheckerIdx]
      simp only [liftedEdgeIndex, max_eq_right_of_lt hx, max_eq_left_of_lt hy]
      apply Prod.ext
      · rfl
      grind [periodicCoordinate_add_one_prev]
  · have hchecker :
        checker (periodicCoordinate hN (max u.val.1 v.val.1),
          periodicCoordinate hM (max u.val.2 v.val.2)) = false := by
      grind [checker_periodicCoordinate]
    have hcheckerIdx : checker (liftedEdgeIndex hN hM u v) = false := by
      tauto
    simp
    right
    constructor
    · apply Subtype.ext
      change (periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) true
      simp only [faceEndpointRaw, hcheckerIdx]
      simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_right_of_lt hy]
      apply Prod.ext
      · rfl
      grind [periodicCoordinate_add_one_prev]
    · apply Subtype.ext
      change (periodicCoordinate hN v.val.1, periodicCoordinate hM v.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) false
      simp only [faceEndpointRaw, hcheckerIdx]
      simp only [liftedEdgeIndex, max_eq_left_of_lt hx, max_eq_right_of_lt hy]
      apply Prod.ext
      · grind [periodicCoordinate_add_one_prev]
      rfl
  · have hux : u.val.1 = v.val.1 + 1 := by omega
    have huy : u.val.2 = v.val.2 + 1 := by omega
    have hchecker :
        checker (periodicCoordinate hN (max u.val.1 v.val.1),
          periodicCoordinate hM (max u.val.2 v.val.2)) = true := by
      grind [checker_periodicCoordinate]
    simp
    left
    constructor
    · apply Subtype.ext
      change (periodicCoordinate hN u.val.1, periodicCoordinate hM u.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) false
      simp_all [faceEndpointRaw, liftedEdgeIndex]
    · apply Subtype.ext
      change (periodicCoordinate hN v.val.1, periodicCoordinate hM v.val.2) =
        faceEndpointRaw true (liftedEdgeIndex hN hM u v) true
      grind [faceEndpointRaw, liftedEdgeIndex, periodicCoordinate_add_one_prev]

section
variable (hN : 0 < N) (hM : 0 < M)
/-- Open lifted diamond edges with both endpoints in a horizontal strip.
The strip bounds are in the integer cover, not reduced modulo N. -/
def liftedStripGraph (A : RCConfig N M)
    (a b : ℤ) : SimpleGraph RotatedVertex where
  Adj u v := rotatedLattice.Adj u v ∧ A (liftedEdgeIndex hN hM u v) = true ∧
    (a ≤ u.val.1 ∧ u.val.1 ≤ b) ∧ (a ≤ v.val.1 ∧ v.val.1 ≤ b)
  symm.symm u v h :=
    ⟨h.1.symm, (liftedEdgeIndex_comm hN hM v u).symm ▸ h.2.1,
      h.2.2.2, h.2.2.1⟩
  loopless.irrefl u h := by
    simp_all

theorem liftedStripGraph_mono {A B : RCConfig N M} (a b : ℤ) (hAB : A ≤ B) :
    liftedStripGraph hN hM A a b ≤ liftedStripGraph hN hM B a b := by
  intro u v huv
  have hval := hAB (liftedEdgeIndex hN hM u v)
  rw [huv.2.1] at hval
  have hout : B (liftedEdgeIndex hN hM u v) = true := by
    tauto
  exact ⟨huv.1, hout, huv.2.2⟩
end

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

theorem liftedBoxConnection_mono {A B : RCConfig N M} (a b : ℤ) (R : ℕ) (u v : RotatedVertex)
    (hAB : A ≤ B) (hconn : liftedBoxConnection hN hM A a b R u v) :
    liftedBoxConnection hN hM B a b R u v := by
  obtain ⟨w, hw⟩ := hconn
  exact ⟨w.mapLe (liftedStripGraph_mono hN hM a b hAB), by simpa using hw⟩
end

section
variable (hN : 0 < N) (hM : 0 < M) (a b : ℤ) (R : ℕ) (y : ℕ → RotatedVertex) (k : ℕ)
/-- Corrected proof-internal chain event: every adjacent pair uses its prescribed lifts. -/
def liftedChainEvent  : Set (RCConfig N M) :=
  {A | ∀ j < k, liftedBoxConnection hN hM A a b R (y j) (y (j + 1))}

/-- Concatenating the actual lifted local paths preserves their lifted endpoints. -/
theorem liftedChainEvent_reachable (A : RCConfig N M)
    (hA : A ∈ liftedChainEvent hN hM a b R y k) :
    (liftedStripGraph hN hM A a b).Reachable (y 0) (y k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨w, _⟩ := hA k (Nat.lt_succ_self k)
    exact (ih (by tauto)).trans ⟨w⟩
end

/-- The even-column lifted point `(x,t)`. -/
def liftedColumnSite (x t : ℤ) (hx : Even x) (ht : Even t) : RotatedVertex :=
  ⟨(x, t), hx.add ht⟩

/-- A lifted vertical period closes at the same finite primal face vertex. -/
theorem liftedFaceVertex_vertical_period (hNeven : Even N) (hMeven : Even M)
    (hN : 0 < N) (hM : 0 < M) (x : ℤ) (hx : Even x) :
    liftedFaceVertex hNeven hMeven hN hM (liftedColumnSite x 0 hx ⟨0, rfl⟩) =
      liftedFaceVertex hNeven hMeven hN hM
        (liftedColumnSite x (M : ℤ) hx (by simp_all)) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  simp [liftedFaceVertex, liftedColumnSite, periodicCoordinate]

/-- The actual sites y_j=(x,2nj), before projection to the torus. -/
def liftedChainSite (x : ℤ) (hx : Even x) (n j : ℕ) : RotatedVertex :=
  liftedColumnSite x (2 * (n : ℤ) * j) hx (by
    simp)

end PottsDiscontinuity.TorusRC
