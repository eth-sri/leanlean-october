module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleRamB
public import Chazelle.Core.ShootCutWalk
public import Chazelle.Core.ShootCutGrade

/-!
# WP-M (E7-B, part 7): the top of a chain from the grade table (mathematics of O5)

The top of the chain `C_A` of a subarc is read from the grade table, without scanning the chain:
the aligned blocks of a dyadic cover of its edges are grade chains, whose descriptors hold their
tops (`block_top`: the top of the block `(g, b)` is at least as high as every vertex of the
block).  The running maximum over the covered vertices then is the top (`topIdx_of_max`: the
topmost vertex of a chain of `Q` is unique, by distinct heights).
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

variable {O : OracleIface} {P : Polygon}

/-- The descriptor handle of the grade chain `(g, b)` in the memory `m`. -/
def blkD (m : ℕ → ℕ) (h g b : ℕ) : ℕ := m (m (m (h + 2) + g) + 3 * b)

/-- **The top of a block of the grade table.**  For a full block `(g, b)` (`g ≥ 1` processed,
`(b + 1) 2^g ≤ n - 1`), the words read lie below the bound of the table, the top index `T` read
from the descriptor is at most `2^g`, and the vertex `b 2^g + T` of `Q` is at least as high as
every vertex of the block. -/
theorem block_top {m : ℕ → ℕ} {h A : ℕ} (hR : Robust A m fun m' => GradeRaw O P m' h A) {g b : ℕ}
    (hg : g < m h) (hb : (b + 1) * 2 ^ g ≤ P.n - 1) :
    h + 2 < A ∧ m (h + 2) + g < A ∧ m (m (h + 2) + g) + 3 * b < A ∧ blkD m h g b + 3 < A ∧
      m (blkD m h g b + 3) ≤ 2 ^ g ∧
      ∀ k, k ≤ 2 ^ g → ((Qof P).vtx (b * 2 ^ g + k)).2 ≤
        ((Qof P).vtx (b * 2 ^ g + m (blkD m h g b + 3))).2 := by
  have hp : 0 < 2 ^ g := Nat.two_pow_pos g
  have hbc : b < gradeCount P.n g := by
    unfold gradeCount
    have : b * 2 ^ g ≤ P.n - 2 := by
      grind
    have := Nat.div_le_div_right (c := 2 ^ g) this
    simp_all
  obtain ⟨h2, hr, hE⟩ := ShootCut.grade_entry hR hg hbc
  obtain ⟨H, C, N, hC, hwf, hP, -, -, hs, hmm, -⟩ := hR.holds.2.2.2 g b hg hbc
  have hD5 : blkD m h g b + 5 ≤ A := hwf.1
  have hQ : (Qof P).n = P.n := shear_n _ _
  have hlen : C.m = 2 ^ g := by
    grind [gradeLen]
  have hsC : C.s = b * 2 ^ g := hs
  have hT : m (blkD m h g b + 3) = C.topIdx := hC.2.2.2.2.1
  have hx : C.s + C.m < (Qof P).n := by
    grind
  refine ⟨h2, hr, by omega_nf, by omega, ?_, fun k hk => ?_⟩
  · rw [hT, ← hlen]; exact C.topIdx_le
  · have hk' : k ≤ C.m := by omega
    have h1 := C.vertex_snd_le_top hk'
    rw [ShootCut.grade_vertex hP hx hk', hsC] at h1
    rw [hT]
    show _ ≤ ((Qof P).vtx (b * 2 ^ g + C.topIdx)).2
    have := ShootCut.grade_vertex hP hx C.topIdx_le
    rw [hsC] at this
    rw [← this]
    exact h1

/-- **The top of a chain is its unique highest vertex** (distinct heights): a chain vertex at
least as high as all chain vertices is the top. -/
theorem topIdx_of_max {C : Chain} (hD : DistinctHeights C.P) {j : ℕ} (hj : j ≤ C.m)
    (hmax : ∀ k, k ≤ C.m → (C.vertex k).2 ≤ (C.vertex j).2) : C.topIdx = j := by
  have h1 := C.topIdx_min hj hmax
  have h2 := C.vertex_snd_le_top hj
  have h3 := hmax C.topIdx C.topIdx_le
  have heq : (C.vertex j).2 = (C.vertex C.topIdx).2 := le_antisymm h2 h3
  by_contra hne
  have hlt : C.topIdx < j := lt_of_le_of_ne h1 hne
  refine hD _ _ (C.edgeIdx_lt j) (C.edgeIdx_lt C.topIdx) ?_ heq
  intro he
  have := C.sideEdgeIdx_inj hj C.topIdx_le he
  omega

end

end IOrc

end Chazelle.Core
