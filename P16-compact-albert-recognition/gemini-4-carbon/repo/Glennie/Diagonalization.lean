module
public import Glennie.Compactness
public import Glennie.Native.Triality

@[expose] public section
namespace Glennie
noncomputable section

private theorem rot_improve (a b n : ℝ) (hn : 0 < n) :
    ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      a ^ 2 + b ^ 2 < (c ^ 2 * a + s ^ 2 * b + 2 * c * s * n) ^ 2 + (s ^ 2 * a + c ^ 2 * b - 2 * c * s * n) ^ 2 := by
  have hpos (x y : ℝ) (hd : 0 ≤ x - y) : ∃ c s : ℝ, c ^ 2 + s ^ 2 = 1 ∧
      x ^ 2 + y ^ 2 < (c ^ 2 * x + s ^ 2 * y + 2 * c * s * n) ^ 2 + (s ^ 2 * x + c ^ 2 * y - 2 * c * s * n) ^ 2 := by
    let d := x - y; let p := 2 * (d + n); let r := p ^ 2 + n ^ 2
    have hd0 : 0 ≤ d := hd
    have hp : n < p := by dsimp [p]; linarith
    have hr : 0 < r := by positivity
    let c := (p ^ 2 - n ^ 2) / r; let s := 2 * p * n / r
    have hcs : c ^ 2 + s ^ 2 = 1 := by dsimp [c, s, r]; field_simp; ring
    have hc : 0 < c := div_pos (by nlinarith) hr
    have hs : 0 < s := div_pos (by positivity) hr
    have h1 : 0 < 2 * c * n - s * d := (mul_pos_iff_of_pos_right hr).mp <| by
      rw [show (2 * c * n - s * d) * r = 2 * n * (2 * d ^ 2 + 6 * d * n + 3 * n ^ 2) by dsimp [c, s, r, p]; field_simp; ring]
      positivity
    refine ⟨c, s, hcs, ?_⟩
    rw [show (c ^ 2 * x + s ^ 2 * y + 2 * c * s * n) ^ 2 + (s ^ 2 * x + c ^ 2 * y - 2 * c * s * n) ^ 2 =
      (c ^ 2 + s ^ 2) ^ 2 * (x ^ 2 + y ^ 2) + 2 * c * s * (2 * c * n - s * d) * (c * d + 2 * s * n) by dsimp [d]; ring,
      hcs, one_pow, one_mul]
    linarith [show 0 < 2 * c * s * (2 * c * n - s * d) * (c * d + 2 * s * n) by positivity]
  rcases le_total b a with h | h
  · exact hpos a b (sub_nonneg.mpr h)
  · obtain ⟨c, s, hcs, hi⟩ := hpos b a (sub_nonneg.mpr h)
    refine ⟨c, -s, by linear_combination hcs, ?_⟩
    linarith [show (c ^ 2 * a + (-s) ^ 2 * b + 2 * c * (-s) * n) ^ 2 + ((-s) ^ 2 * a + c ^ 2 * b - 2 * c * (-s) * n) ^ 2 =
      (c ^ 2 * b + s ^ 2 * a + 2 * c * s * n) ^ 2 + (s ^ 2 * b + c ^ 2 * a - 2 * c * s * n) ^ 2 by ring]

def HasMaximalDiagonalEnergy (x : Albert) : Prop :=
  ∀ g : CompactAutomorphism, diagonalEnergy (g.equiv x) ≤ diagonalEnergy x

theorem maximalDiagonalEnergy_after (x : Albert) (hx : HasMaximalDiagonalEnergy x)
    (g : CompactAutomorphism) (hg : diagonalEnergy (g.equiv x) = diagonalEnergy x) :
    HasMaximalDiagonalEnergy (g.equiv x) := fun h => hg ▸ hx (h.comp g)

theorem maximalDiagonalEnergy_slot12_zero (x : Albert) (hx : HasMaximalDiagonalEnergy x) : x.o12 = 0 := by
  by_contra hn
  obtain ⟨g, n, hn, h0, h1, h2, hslot⟩ := OctRelatedTriple.make_slot12_real x hn
  obtain ⟨c, s, hcs, he⟩ := rot_improve x.d1 x.d2 n hn
  have hmax := hx ((realRotation12Automorphism c s hcs).comp g)
  change diagonalEnergy (rot12Apply c s (g.equiv x)) ≤ diagonalEnergy x at hmax
  unfold diagonalEnergy rot12Apply at hmax
  rw [h0, h1, h2, hslot, octRe_scalar] at hmax
  linarith

theorem maximalDiagonalEnergy_isDiagonal (x : Albert) (hx : HasMaximalDiagonalEnergy x) : IsDiagonal x := by
  have hs01 : diagonalEnergy (realSwap01Automorphism.equiv x) = diagonalEnergy x := by
    change x.d1 ^ 2 + x.d0 ^ 2 + x.d2 ^ 2 = _; simp only [diagonalEnergy]; ring
  have hs02 : diagonalEnergy (realSwap02Automorphism.equiv x) = diagonalEnergy x := by
    change x.d2 ^ 2 + x.d1 ^ 2 + x.d0 ^ 2 = _; simp only [diagonalEnergy]; ring
  have h12 := maximalDiagonalEnergy_slot12_zero x hx
  have h02 : x.o02 = 0 := maximalDiagonalEnergy_slot12_zero _ (maximalDiagonalEnergy_after x hx _ hs01)
  have h01 : octConj x.o01 = 0 := maximalDiagonalEnergy_slot12_zero _ (maximalDiagonalEnergy_after x hx _ hs02)
  refine ⟨?_, h02, h12⟩
  simpa only [octConj_conj, show octConj (0 : Octonion) = 0 from Prod.ext (by simp [octConj]) (by simp [octConj])] using congrArg octConj h01

theorem native_diagonalization (x : Albert) : ∃ g : CompactAutomorphism, IsDiagonal (g.equiv x) := by
  obtain ⟨g, hg⟩ := exists_diagonalEnergy_maximum x
  exact ⟨g, maximalDiagonalEnergy_isDiagonal _ fun h => hg (h.comp g)⟩

end
end Glennie
