module

public import Glennie.Compact.NearbyOrbits
public import Glennie.Native.FirstPairNormalization
public import Glennie.UnitShifts

/- Nearby pair normalization. `native_ordered_positive_pair` carries an arbitrary genuine frame onto the
diagonal frame `flatFrameP` and the second frame's encoder into the complex sector with slots 01
and 12 nonnegative real; it has no `1/3` and no `flatScale` in it, so it survives perturbation
untouched. The nine pairwise overlaps -- the P block -- then determine the three
diagonal entries AND the three square-diagonal entries of that encoder by subtraction and
addition (section 4), hence by `fe_complex_square_d0/d1/d2` the three complex slot norms, hence
by `fe_complex_cubic` with `frame_encoder_cubicNorm` the real part of the triangle, hence the
whole normalised second frame up to the sign of one imaginary part, which one constructed
octonion automorphism flips (sections 6, 7). The residual group is the colour SU(3) of
`sectorLeftSU3Automorphism`, which fixes the whole complex sector; the third frame's encoder
splits as `complexProjection` plus `hiddenAlbert (hiddenMatrix _)`, the ledger determines the
sector projection of that encoder and of its square (section 8), those determine the hidden Gram
matrix and -- through Newton's cubic norm and `inner_jordan_associative` -- the real part of the
hidden determinant (section 9), and `phi_of_diagonal_complex` says Phi is a nonzero multiple of
its imaginary part (section 11), so one shrink by the sign of Phi pins that too and the matrix
transport closes (sections 10, 12).

Providers and conventions.

  `Glennie.Native`: `inner_coordinates` :345, `inner_comm` :351, `jordan_comm` :296,
    `jordan_d0` :300, `jordan_d1` :306, `jordan_d2` :312, `jordan_o01` :318, `jordan_o02` :327,
    `jordan_o12` :336, `octMul` :32, `octConj` :35, `octRe` :36, `octScalar` :37, `octDot` :38,
    `octNormSq` :39, `octDot_coordinates` :67, `octDot_comm` :74, the `@[simp]` field
    projections of `+`/`-`/`•`/`0`/`1` :162-195, `phi` :221, `trace` :215, `inner` :216,
    `encoder` :235, `ledger` :236, `Frame` :228
  `Glennie.Native.AlgebraLaws`: `octDot_add_left` :79, `octDot_smul_left` :84,
    `jordan_add_left` :89, `jordan_add_right` :100, `jordan_smul_left` :103,
    `jordan_sub_left` :125, `jordan_sub_right` :128, `jordan_unit_left` :131,
    `jordan_unit_right` :138, `inner_add_left` :147, `inner_add_right` :150,
    `inner_smul_left` :153, `inner_smul_right` :156, `inner_sub_left` :165,
    `inner_sub_right` :168, `inner_jordan_associative` :172
  `Glennie.Native.Triality`: `octDot_sub_left` :23, `OctRelatedTriple` :133
  `Glennie.Sector`: `complexPart` :13, `complexOct` :15, `hiddenMatrix` :24, `hiddenAlbert` :27,
    `complexProjection` :31, `diagonalAlbert` :34, `complexAlbert` :36,
    `complex_hidden_decomposition` :45, `complex_hidden_orthogonal` :52, `hiddenAlbert_norm` :57,
    `sectorColumnGram` :65, `sectorFrobeniusSq` :68, `hidden_square_complexProjection` :72
  `Glennie.SectorModel`: `hiddenMatrix_hiddenAlbert` :60
  `Glennie.SectorSubspace`: `complexProjection_mem` :50, `complexProjection_eq_self` :53,
    `complexSector_mem_iff` :59, `complexSector_jordan` :67, `complexProjection_zero_of_perp` :84
  `Glennie.Obligations`: `IsDiagonal` :16, `OctInComplex` :19, `InComplexSector` :21
  `Glennie.Theorems.CubicNorm`: `newtonCubicNorm` (Newton's TRACE form) :15,
    `frame_encoder_cubicNorm` :31
  `Glennie.Theorems.Frames`: `frame_encoder_trace` :13, `frame_encoder_square` :18,
    `frame_encoder_norm` :30, `frame_projector_first` :36 with `_middle` and `_last`,
    `uniformLedger_pair_overlap` :65
  `Glennie.Theorems.ProjectorFrame`: `projectorFrame` :16
  `Glennie.Theorems.FrameSaturation`: `fe_complex_cubic` :17,
    `fe_complex_square_d0/d1/d2` :27,33,39
  `Glennie.Theorems.DiagonalFrames`: `frame_projectors_diagonal` :26
  `Glennie.Theorems.ComplexSectorSpan`: `complexProjection_sub` :20, `complexProjection_add` :24,
    `complexProjection_smul` :28, `complexProjection_unit` :32, `frame_in_complexSector` :36
  `Glennie.Theorems.OctonionAutomorphisms`: `DiagonalOctTriple` :68,
    `exists_octAutomorphism_to_i` :209
  `Glennie.Native.PairReduction`: `octInComplex_scalar` :18, `diagonalOctTriple_scalar` :25
  `Glennie.Theorems.SectorTransport`: `SectorMatrix` :16, `SectorUnitary` :17,
    `hiddenMatrix_of_inComplex` :290
  `Glennie.SectorFactor`: `phi_diagonal_complex_factor` :21, consumed through `UnitShifts`.
  `Glennie.UnitShifts`: `diagonalAlbert_eq` :18, `complexAlbert_eq` :22,
    `phi_of_diagonal_complex` :27, `diagonal_inComplex` :47.
  `Glennie.Automorphism`: `CompactAutomorphism.refl` :11, `.comp` :17, `comp_apply` :22,
    `.symm` :25, `symm_apply` :32, `map_unit` :35, `inner_map` :40, `phi_map` :49,
    `map_frame` :63, `encoder_map` :70, `ledger_map` :74
  `Glennie.Compactness`: `CompactAutomorphism` (NO `Group`/`Monoid`/`Mul`/`One`/`Inv`/
    `MulAction` instance and NO topology -- hence no continuity in the group variable is used
    anywhere below, and all composition is through `.comp`/`.symm` by hand)
  `Glennie.Compact.FlatBase`: `flatScale` :53, `flatXN` :61, `flatY1` :64, `reverseFrame` :183,
    `projectorFrame_neg_one_smul` :190, `flatFrameP` :207, `flatFrameQ` :208, `flatFrameR` :209,
    `flatFrameP_frame` :231, `flatFrameQ_frame` :236, `flatFrameP_encoder` :250,
    `flat_uniform` :272
  `Glennie.Compact.Affine20.Relabel`: `Triple` :47, `Ledger54` :51, `ledger54` :56,
    `mapAtoms` :142, `mapAtoms_apply` :145, `ledger54_C/P/Q/R` :157,160,164,167,
    `ledger54_map` :169, `fin3_cases` :61
  `Glennie.Compact.Sections.Reversal`: `phiOf` :267, `phiOf_apply` :269, `continuous_phiOf` :372

  `Glennie.NativeOrderedPositivePair.native_ordered_positive_pair` normalizes the first pair.
  `Glennie.sectorLeftSU3Automorphism`, `sectorLeftSU3_complex`, `sectorLeftSU3_hidden`,
    `sectorLeftSU3_fixes_complex`, and `compactAutomorphism_projectorFrame` supply the colour action.
  `NativeFixedPairHidden.native_fixed_pair_hidden_gram_phase` and
    `NativeFixedPairNormalization.native_fixed_pair_third_frame_normalization` concern the exact
    uniform ledger; the nearby argument uses general forms of their ingredients.
    `scaled_transport` is re-proved in general form in section 10.
  `Glennie.Compact.FrameTopology` supplies `flatBaseTriple`, `flatBaseTriple_frames`,
    `continuous_entry`, and `continuous_ledger54`.
  `Glennie.Compact.FlatOrbit` supplies `flatBaseRev3` and `flatBaseRev3_frames`.
  `Glennie.Compact.NearbyOrbits` supplies `LocalOrbitCompleteness`, `phiOf_mapAtoms`,
    `phiOf_flatBaseTriple_neg`, and `phiOf_flatBaseRev3_pos`.
  `Glennie.Native.FirstPairNormalization.native_flat_pair_normalization` is not invoked:
    section 7 generalizes its argument by removing the exact values. Its private helpers
    `frame_as_projector`, `frame_eq_of_encoder_eq`, `nonneg_sq_flatScale`,
    `complex_slot_data_of_square`, `uniform_complex_slot_data`, `flatQ_slots`,
    `encoder_to_flatQ`, `relatedTriple_flatXN`, `relatedTriple_fixes_flatFrameP`, and
    `real_real_conj_re` are re-derived or replaced here.

Neighbourhoods are shrunk by an explicit epsilon box on the P block, open by
`continuous_ledger54`, and one half-space of `phiOf`, open by `continuous_phiOf`.
The two sign sheets remain separate. The action is the diagonal `mapAtoms`;
no topology on `CompactAutomorphism`, continuity in a group variable, or derivative
of the existential sections of `native_flat_two_sections_full54` is used.

ON `octConj`. It is never APPLIED by this file, never composed with an automorphism and never
used to correct a sign -- the sign correction is the genuine automorphism of
`exists_octAutomorphism_to_i`. It occurs as a simp-lemma NAME in four places (the three
`fe_complex_square_o*` of section 5 and `octMul_zero_*`/`octConj_zero` of section 1a), because
the right-hand sides of the package's own `jordan_o01/o02/o12` literally contain
`octMul _ (octConj _)`. That is the same usage as in the `fe_complex_square_d0/d1/d2`
and `fe_complex_cubic`, whose simp sets also list `octConj`.
-/

@[expose] public section
namespace Glennie.Compact.PairNormNearby

open Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology Glennie.Compact.FlatOrbit
open Glennie.Compact.Sections Glennie.Compact.NearbyOrbits
open Glennie.NativeOrderedPositivePair


/-! ## 1. Pure arithmetic on reals and matrices

The arithmetic for `slot_nondegenerate` and `sector_slot_recovery` is isolated from
contexts carrying `Albert`, `Octonion` and `Complex.normSq (complexPart _)` atoms.
The lemmas use `linarith`, `linear_combination`, `calc` or a single `nlinarith` over
at most four hypotheses, and are called with explicit arguments. -/

theorem im_sq_eq_of_normSq_eq (z w : ℂ) (hn : Complex.normSq z = Complex.normSq w)
    (hr : z.re = w.re) : z.im ^ 2 = w.im ^ 2 := by
  rw [Complex.normSq_apply, Complex.normSq_apply, hr] at hn
  linear_combination hn

theorem two_by_two (A B C D X Y : ℝ)
    (h1 : A * X + B * Y = 0) (h2 : C * X + D * Y = 0)
    (hdet : A * D - B * C ≠ 0) : X = 0 ∧ Y = 0 :=
  ⟨(mul_eq_zero.mp (by linear_combination D * h1 - B * h2 :
      (A * D - B * C) * X = 0)).resolve_left hdet,
    (mul_eq_zero.mp (by linear_combination A * h2 - C * h1 :
      (A * D - B * C) * Y = 0)).resolve_left hdet⟩

theorem normSq_det_eq_gram_det_re (M : Matrix (Fin 3) (Fin 3) ℂ) :
    Complex.normSq M.det = (M.conjTranspose * M).det.re := by aesop

theorem nondegenerate_core (a b D0 D1 D2 v R Sg : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hD0 : |D0| < 1 / 25) (hD1 : |D1| < 1 / 25) (hD2 : |D2| < 1 / 25)
    (he0 : |D0 ^ 2 + a ^ 2 + v - 2 / 3| < 1 / 25) (he1 : |D1 ^ 2 + a ^ 2 + b ^ 2 - 2 / 3| < 1 / 25)
    (he2 : |D2 ^ 2 + v + b ^ 2 - 2 / 3| < 1 / 25) (hv0 : 0 ≤ v)
    (C : D0 * D1 * D2 - D0 * b ^ 2 - D1 * v - D2 * a ^ 2 + 2 * (a * b * R) = 0)
    (hsplit : v = R * R + Sg * Sg) :
    1 / 2 < a ∧ 1 / 2 < b ∧ Sg ≠ 0 := by
  have q0 := sq_lt_sq' (abs_lt.mp hD0).1 (abs_lt.mp hD0).2
  have q1 := sq_lt_sq' (abs_lt.mp hD1).1 (abs_lt.mp hD1).2
  have q2 := sq_lt_sq' (abs_lt.mp hD2).1 (abs_lt.mp hD2).2
  rw [abs_lt] at he0 he1 he2
  have := sq_nonneg D0; have := sq_nonneg D1; have := sq_nonneg D2
  have ha2 : 1 / 4 < a ^ 2 := by linarith
  have hb2 : 1 / 4 < b ^ 2 := by linarith
  have hv : 1 / 4 < v := by linarith
  have t1 : |D0 * b ^ 2| < 1 / 25 * (1 / 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg b)]
    exact mul_lt_mul'' hD0 (by linarith) (abs_nonneg _) (sq_nonneg _)
  have t2 : |D1 * v| < 1 / 25 * (1 / 2) := by
    rw [abs_mul, abs_of_nonneg hv0]
    exact mul_lt_mul'' hD1 (by linarith) (abs_nonneg _) hv0
  have t3 : |D2 * a ^ 2| < 1 / 25 * (1 / 2) := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg a)]
    exact mul_lt_mul'' hD2 (by linarith) (abs_nonneg _) (sq_nonneg _)
  have t4 : |D0 * D1 * D2| < 1 / 25 * (1 / 25) * (1 / 25) := by
    rw [abs_mul, abs_mul]
    exact mul_lt_mul'' (mul_lt_mul'' hD0 hD1 (abs_nonneg _) (abs_nonneg _)) hD2
      (by positivity) (abs_nonneg _)
  rw [abs_lt] at t1 t2 t3 t4
  refine ⟨lt_of_pow_lt_pow_left₀ 2 ha (by linarith), lt_of_pow_lt_pow_left₀ 2 hb (by linarith), fun h => ?_⟩
  have := sq_lt_sq' (by linarith : -(1 / 32) < a * b * R) (by linarith : a * b * R < 1 / 32)
  have := mul_lt_mul'' (mul_lt_mul'' ha2 hb2 (by norm_num) (by norm_num)) hv
    (by norm_num) (by norm_num)
  have : (a * b * R) ^ 2 = a ^ 2 * b ^ 2 * v := by rw [hsplit, h]; ring
  linarith

/-! ## 3. The exact diagonal probes of the normalised first frame -/

theorem inner_flatFrameP (x : Albert) : inner (flatFrameP 0) x = x.d2 ∧
    inner (flatFrameP 1) x = x.d1 ∧ inner (flatFrameP 2) x = x.d0 := by
  norm_num [flatFrameP, projectorFrame, inner_coordinates, flatXN, oct_simps]

theorem flatFrameP_isDiagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) :=
  diagonal_inComplex _ (flatFrameP_isDiagonal i)

/-! ## 4. The P block determines six numbers, by subtraction and addition

These six replace the three exact values `1/3` of `uniform_complex_slot_data`. Nothing here
needs the overlaps to be uniform or even near uniform; `hPQ` is naming, not a hypothesis on the
values. There are exactly four independent numbers,
matching the four free parameters of a 3x3 matrix whose rows and columns all sum to one. -/

theorem normalised_diag_data (q : Fin 3 → Albert) (hq : Frame q) (P : Fin 3 → Fin 3 → ℝ)
    (hPQ : ∀ i j : Fin 3, inner (flatFrameP i) (q j) = P i j) :
    (encoder q).d0 = P 2 2 - P 2 0 ∧ (encoder q).d1 = P 1 2 - P 1 0 ∧
      (encoder q).d2 = P 0 2 - P 0 0 ∧
      (jordan (encoder q) (encoder q)).d0 = P 2 2 + P 2 0 ∧
      (jordan (encoder q) (encoder q)).d1 = P 1 2 + P 1 0 ∧
      (jordan (encoder q) (encoder q)).d2 = P 0 2 + P 0 0 := by
  have := hPQ 2 0; have := hPQ 2 2; have := hPQ 1 0; have := hPQ 1 2; have := hPQ 0 0
  have := hPQ 0 2
  simp [inner_flatFrameP] at *
  rw [frame_encoder_square q hq]
  simp [encoder, *]

/-! ## 5. The three complex-square SLOT formulas

The package has `fe_complex_square_d0/d1/d2` (`Theorems/FrameSaturation.lean`) for the
three DIAGONAL entries of a complex-sector square, fully general in `(d,e,f,u,v,w)`, but no slot
companions. These are the companions. The convention is pinned, not guessed: `fe_complex_cubic`
(`:17`) reads `d*e*f - d*normSq w - e*normSq v - f*normSq u + 2*(u*w*star v).re`, which is
exactly the determinant of the Hermitian matrix `[[d,u,v],[star u,e,w],[star v,star w,f]]`, so
`(u,v,w)` are the `(01,02,12)` entries with no conjugation and these three are that matrix
squared. Each also matches `jordan_o01/o02/o12` (`Native.lean`) specialised to
`x = y`. -/

theorem fe_complex_square_o (d e f : ℝ) (u v w : ℂ) :
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o01 =
      u * (d + e) + v * star w ∧
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o02 =
      v * (d + f) + u * w ∧
    complexPart (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).o12 =
      w * (e + f) + star u * v := by
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;>
    simp [oct_simps, complexAlbert, complexOct, complexPart, Complex.mul_re, Complex.mul_im] <;> ring

/-! ### 5a. The three slot readers of `complexAlbert`

Each is `rfl` componentwise: `complexAlbert` is a plain constructor application, so `.o01`
iota-reduces to `complexOct u`, and `complexPart (complexOct u) = ⟨u.re, u.im⟩`. The componentwise
`Complex.ext` form is used rather than a bare `rfl` on the whole equation so that the proof does
not lean on structure eta. -/

theorem complexPart_complexAlbert (a b c : ℝ) (u v w : ℂ) :
    complexPart (complexAlbert a b c u v w).o01 = u ∧ complexPart (complexAlbert a b c u v w).o02 = v ∧
      complexPart (complexAlbert a b c u v w).o12 = w := ⟨rfl, rfl, rfl⟩

/-! ### 5b. Octonion bookkeeping inside the standard complex line -/

theorem normSq_complexPart_octScalar (a : ℝ) :
    Complex.normSq (complexPart (octScalar a)) = a ^ 2 := by
  rw [complexPart_octScalar, Complex.normSq_ofReal]; ring

/-- Two elements of the standard complex line with the same complex part are equal. The
chain used `octInComplex_slot_eq` (`FirstPairNormalization.lean`) instead, which additionally
required the real part to VANISH -- true on the flat fibre, false nearby, which is the precise
point at which step 5 of that proof breaks. -/
theorem octInComplex_ext (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x')
    (h : complexPart x = complexPart x') : x = x' :=
  Prod.ext (Quaternion.ext _ _ (congrArg Complex.re h) (congrArg Complex.im h) (hx.1.trans hx'.1.symm)
    (hx.2.1.trans hx'.2.1.symm)) (hx.2.2.trans hx'.2.2.symm)

theorem octInComplex_eq_zero (x : Octonion) (hx : OctInComplex x)
    (h : (complexPart x).re = 0 ∧ (complexPart x).im = 0) : x = 0 :=
  octInComplex_ext x 0 hx ⟨rfl, rfl, rfl⟩ (Complex.ext h.1 h.2)

theorem octInComplex_decomp (x : Octonion) (hx : OctInComplex x) :
    x = octScalar (complexPart x).re + (complexPart x).im • octI := by
  obtain ⟨hj, hk, hz⟩ := hx
  apply Prod.ext
  · ext <;> simp [octScalar, octI, quatI, complexPart, hj, hk]
  · simp [octScalar, octI, quatI, hz]

theorem octDot_inComplex (x x' : Octonion) (hx : OctInComplex x) (hx' : OctInComplex x') :
    octDot x x' = (complexPart x).re * (complexPart x').re +
      (complexPart x).im * (complexPart x').im := by
  obtain ⟨hj, hk, hz⟩ := hx
  obtain ⟨hj', hk', hz'⟩ := hx'
  rw [octDot_coordinates]
  simp [complexPart, hj, hk, hz, hj', hk', hz']

/-- `real_real_conj_re` of `FirstPairNormalization.lean`, which is `private` there. -/
theorem real_real_conj_re (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).re = a * b * z.re := by simp

theorem real_real_conj_im (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).im = -(a * b * z.im) := by simp

/-! ## 6. The slot data of a complex-sector frame encoder, with symbols for the numerals

This is `uniform_complex_slot_data` (`FirstPairNormalization.lean`) and
`complex_slot_data_of_square` (`:87`) with `0`, `2/3` and `1/3` replaced by variables. The
interior of both is `linarith` over `fe_complex_square_d*` and `fe_complex_cubic`, all of which
are already general in `(d,e,f,u,v,w)`; only the SUBSTITUTED VALUES broke. Stated as a
comparison, which is all the route consumes, so no formula has to be written down and no square
root is ever taken. -/

theorem slot_data_eq_of_diag_eq (y y' : Albert)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (hs0 : (jordan y y).d0 = (jordan y' y').d0)
    (hs1 : (jordan y y).d1 = (jordan y' y').d1)
    (hs2 : (jordan y y).d2 = (jordan y' y').d2)
    (hcub : newtonCubicNorm y = newtonCubicNorm y') :
    Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) ∧
      Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) ∧
      Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) ∧
      (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re =
        (complexPart y'.o01 * complexPart y'.o12 * star (complexPart y'.o02)).re := by
  rw [← complexAlbert_eq y hc, ← complexAlbert_eq y' hc'] at hs0 hs1 hs2 hcub
  simp only [fe_complex_square_d0, fe_complex_square_d1, fe_complex_square_d2, fe_complex_cubic,
    hd0, hd1, hd2] at hs0 hs1 hs2 hcub
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  linear_combination (hcub + y'.d0 * (hs1 + hs2 - hs0) / 2 + y'.d1 * (hs0 - hs1 + hs2) / 2 +
    y'.d2 * (hs0 + hs1 - hs2) / 2) / 2

/-! ### 6a. The nondegeneracy supplied by the neighbourhood

Nothing in section 6 needs the overlaps to be near uniform. The epsilon box is needed in exactly
three places: `0 < a`, `0 < b` and `(complexPart y.o02).im /= 0`.
The four algebraic identities here supply the nine real numbers to `nondegenerate_core`
(section 1). The triangle term is rewritten in a separate `have` so the norm-square
atoms remain in the form used by the goal. -/

theorem slot_nondegenerate (y : Albert) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : InComplexSector y)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hcub : newtonCubicNorm y = 0)
    (hc0 : |y.d0| < 1 / 25) (hc1 : |y.d1| < 1 / 25) (hc2 : |y.d2| < 1 / 25)
    (he0 : |(jordan y y).d0 - 2 / 3| < 1 / 25)
    (he1 : |(jordan y y).d1 - 2 / 3| < 1 / 25)
    (he2 : |(jordan y y).d2 - 2 / 3| < 1 / 25) :
    1 / 2 < a ∧ 1 / 2 < b ∧ (complexPart y.o02).im ≠ 0 := by
  rw [← complexAlbert_eq y hc] at hcub he0 he1 he2
  simp only [fe_complex_square_d0, fe_complex_square_d1, fe_complex_square_d2, fe_complex_cubic,
    h01, h12, complexPart_octScalar, Complex.normSq_ofReal, real_real_conj_re, ← sq] at hcub he0 he1 he2
  exact nondegenerate_core a b y.d0 y.d1 y.d2 _ _ _ ha hb hc0 hc1 hc2 he0 he1 he2
    (Complex.normSq_nonneg _) hcub (Complex.normSq_apply _)

/-! ## 7. The pair, perturbed: pair normalization

Step 5 of the proof -- `flatQ_slots` (`FirstPairNormalization.lean`) and
`encoder_to_flatQ` (`:244`) -- is what breaks hardest: both name the target
`flatScale • flatY1`. Nearby there is no canonical target, so "normalise onto a fixed element"
becomes "two normal forms with the same P data are related". The sign branch is still resolved by
`exists_octAutomorphism_to_i (-octI)`, exactly as at `:283`, but that automorphism must now act
on a GENERAL complex slot `rho + sigma*octI`, not just on `sigma*octI`; that is the one place
where the whole of `DiagonalOctTriple` is needed. `octConj` is NOT used: octonion conjugation is
an anti-automorphism and can never be a sign corrector. -/

/-- The sign-flip automorphism conjugates the whole complex line, not merely its imaginary
axis. `DiagonalOctTriple` (`Theorems/OctonionAutomorphisms.lean`) says `B = A`, `C = A` and
`A (octScalar 1) = octScalar 1`; with `A octI = -octI` and real linearity that is all that is
needed. -/
theorem octInComplex_conj_slot (k : OctRelatedTriple) (hk : DiagonalOctTriple k)
    (hkI : k.A octI = -octI) (x : Octonion) (hx : OctInComplex x) :
    OctInComplex (k.A x) ∧ complexPart (k.A x) = star (complexPart x) := by
  have : k.A x = octScalar (complexPart x).re - (complexPart x).im • octI := by
    conv_lhs => rw [octInComplex_decomp x hx]
    rw [map_add, map_smul, diagonalOctTriple_scalar k hk, hkI, smul_neg, ← sub_eq_add_neg]
  rw [this]
  refine ⟨⟨?_, ?_, ?_⟩, Complex.ext ?_ ?_⟩ <;> simp [complexPart, octScalar, octI, quatI]

/-- The automorphism built from `exists_octAutomorphism_to_i (-octI)`: it fixes `flatFrameP`
pointwise, fixes every real slot and conjugates every complex slot. -/
theorem exists_slot_conjugator :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧
      (∀ y : Albert, InComplexSector y →
        (m.equiv y).d0 = y.d0 ∧ (m.equiv y).d1 = y.d1 ∧ (m.equiv y).d2 = y.d2 ∧
        complexPart (m.equiv y).o01 = star (complexPart y.o01) ∧
        complexPart (m.equiv y).o02 = star (complexPart y.o02) ∧
        complexPart (m.equiv y).o12 = star (complexPart y.o12) ∧
        InComplexSector (m.equiv y)) := by
  obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI)
    (by simp [octRe, octI, quatI]) (by norm_num [oct_simps, octI, quatI])
  have hkIneg : k.A octI = -octI := by rw [← neg_neg (k.A octI), ← map_neg, hkI]
  refine ⟨k.compactAutomorphism, frame_eq_of_encoder_eq _ _ flatFrameP_frame flatFrameP_frame _ (by
    rw [flatFrameP_encoder]
    change (⟨flatXN.d0, flatXN.d1, flatXN.d2, k.A flatXN.o01, k.C flatXN.o02, k.B flatXN.o12⟩ :
      Albert) = flatXN
    simp [flatXN]), fun y hy => ?_⟩
  have h1 := octInComplex_conj_slot k hk hkIneg y.o01 hy.1
  have h2 := hk.2.1 y.o02 ▸ octInComplex_conj_slot k hk hkIneg y.o02 hy.2.1
  have h3 := hk.1 y.o12 ▸ octInComplex_conj_slot k hk hkIneg y.o12 hy.2.2
  exact ⟨rfl, rfl, rfl, h1.2, h2.2, h3.2, h1.1, h2.1, h3.1⟩

/-- Two Step-A normal forms with the same P data are equal, or are carried to one another by one
automorphism that fixes `flatFrameP` pointwise. This is the perturbed `encoder_to_flatQ`. -/
theorem pair_normal_form_rel (y y' : Albert) (a b a' b' : ℝ)
    (hc : InComplexSector y) (hc' : InComplexSector y')
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (h01' : y'.o01 = octScalar a') (h12' : y'.o12 = octScalar b')
    (hd0 : y.d0 = y'.d0) (hd1 : y.d1 = y'.d1) (hd2 : y.d2 = y'.d2)
    (haa : a = a') (hbb : b = b')
    (hre : (complexPart y.o02).re = (complexPart y'.o02).re)
    (himsq : (complexPart y.o02).im ^ 2 = (complexPart y'.o02).im ^ 2) :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧ m.equiv y = y' := by
  subst haa hbb
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
  · exact ⟨CompactAutomorphism.refl, fun _ => rfl, Albert.ext hd0 hd1 hd2 (h01.trans h01'.symm)
      (octInComplex_ext _ _ hc.2.1 hc'.2.1 (Complex.ext hre him)) (h12.trans h12'.symm)⟩
  · obtain ⟨m, hmP, hmslots⟩ := exists_slot_conjugator
    obtain ⟨e0, e1, e2, c01, c02, c12, hsec⟩ := hmslots y hc
    refine ⟨m, hmP, Albert.ext (e0.trans hd0) (e1.trans hd1) (e2.trans hd2)
      (octInComplex_ext _ _ hsec.1 hc'.1 ?_) (octInComplex_ext _ _ hsec.2.1 hc'.2.1 ?_)
      (octInComplex_ext _ _ hsec.2.2 hc'.2.2 ?_)⟩
    · rw [c01, h01, h01', complexPart_octScalar]
      exact Complex.conj_ofReal a
    · rw [c02]
      exact Complex.ext hre (by change -_ = _; linarith)
    · rw [c12, h12, h12', complexPart_octScalar]
      exact Complex.conj_ofReal b

/-! ## 8. The ledger sees the third frame's sector data, slot by slot

This replaces `uniformLedger_complexProjection_encoder(_square)`
(`Theorems/ComplexSectorSpan.lean`), which recover the sector projection by declaring the
nine mixed products `jordan (p i) (q j)` a BASIS -- which needs
`uniform_pair_mixed_linearIndependent` and so the EXACT uniform P block. Linear independence is
an open condition, so a perturbation of that route would need an openness proof for a 9x9
determinant in a variable produced by an existential. The route below avoids spanning
altogether: it extracts the nine sector coordinates one at a time, at the cost of three 2x2
determinants, each of which is `a*b*sigma` up to sign and so nonzero by section 6a. -/

theorem inner_sector_hiddenAlbert (v : Albert) (hv : InComplexSector v)
    (M : Matrix (Fin 3) (Fin 3) ℂ) : inner v (hiddenAlbert M) = 0 := by
  rw [← complexProjection_eq_self v hv]
  exact complex_hidden_orthogonal v M

theorem inner_sector_complexProjection (v W : Albert) (hv : InComplexSector v) :
    inner v W = inner v (complexProjection W) := by
  conv_lhs => rw [← complex_hidden_decomposition W]
  rw [inner_add_right, inner_sector_hiddenAlbert v hv, add_zero]

/-- With a diagonal left factor and a diagonal-free right factor, the ledger probe is exactly
three slot pairings with rational coefficients. `jordan_o01/o02/o12` collapse because every slot
of the left factor is zero.

The four section-1a lemmas simplify the octonion zero terms. -/
theorem inner_diag_jordan_slots (x z E : Albert) (hxd : IsDiagonal x)
    (hE0 : E.d0 = 0) (hE1 : E.d1 = 0) (hE2 : E.d2 = 0) :
    inner (jordan x z) E =
      (x.d0 + x.d1) * octDot z.o01 E.o01 + (x.d0 + x.d2) * octDot z.o02 E.o02 +
        (x.d1 + x.d2) * octDot z.o12 E.o12 := by
  obtain ⟨hx01, hx02, hx12⟩ := hxd
  simp [inner_coordinates, hE0, hE1, hE2, jordan_o01, jordan_o02, jordan_o12, hx01, hx02, hx12,
    octConj, octMul, Prod.mk_zero_zero, octDot_smul_left]
  ring

theorem sector_slot_recovery (Q : Fin 3 → Albert) (hQ : Frame Q) (D : Albert) (a b : ℝ)
    (hcy : InComplexSector (encoder Q))
    (h01 : (encoder Q).o01 = octScalar a) (h12 : (encoder Q).o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b)
    (hsigma : (complexPart (encoder Q).o02).im ≠ 0)
    (hR : ∀ i, inner (flatFrameP i) D = 0)
    (hC : ∀ i j, inner (jordan (flatFrameP i) (Q j)) D = 0) :
    complexProjection D = 0 := by
  set E := complexProjection D
  set y := encoder Q
  have hcE : InComplexSector E := (complexSector_mem_iff _).mp (complexProjection_mem _)
  have hCE i j : inner (jordan (flatFrameP i) (Q j)) E = 0 := by
    rw [← inner_sector_complexProjection _ _ (complexSector_jordan _ _ (flatFrameP_inComplexSector i)
      ((complexSector_mem_iff _).mp (frame_in_complexSector _ hQ hcy j)))]
    exact hC i j
  have hE i : inner (flatFrameP i) E = 0 := by
    rw [← inner_sector_complexProjection _ _ (flatFrameP_inComplexSector i)]; exact hR i
  have hE0 := (inner_flatFrameP E).2.2.symm.trans (hE 2)
  have hE1 := (inner_flatFrameP E).2.1.symm.trans (hE 1)
  have hE2 := (inner_flatFrameP E).1.symm.trans (hE 0)
  have sp (z : Albert) (h : ∀ i, inner (jordan (flatFrameP i) z) E = 0) :
      octDot z.o01 E.o01 = 0 ∧ octDot z.o02 E.o02 = 0 ∧ octDot z.o12 E.o12 = 0 := by
    have h0 := h 0; have h1 := h 1; have h2 := h 2
    rw [inner_diag_jordan_slots _ z E (flatFrameP_isDiagonal _) hE0 hE1 hE2] at h0 h1 h2
    norm_num [flatFrameP, projectorFrame, flatXN, jordan_d0, jordan_d1, jordan_d2, octNormSq] at h0 h1 h2
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨p1, p2, p3⟩ := sp y fun i => by
    rw [show y = Q 2 - Q 0 from rfl, jordan_sub_right, inner_sub_left, hCE, hCE, sub_zero]
  obtain ⟨q1, q2, q3⟩ := sp (jordan y y) fun i => by
    rw [frame_encoder_square _ hQ, jordan_add_right, inner_add_left, hCE, hCE, add_zero]
  have hcsq := complexSector_jordan y y hcy hcy
  simp [octDot_inComplex _ _ hcy.1 hcE.1, octDot_inComplex _ _ hcy.2.1 hcE.2.1,
    octDot_inComplex _ _ hcy.2.2 hcE.2.2, octDot_inComplex _ _ hcsq.1 hcE.1,
    octDot_inComplex _ _ hcsq.2.1 hcE.2.1, octDot_inComplex _ _ hcsq.2.2 hcE.2.2] at p1 p2 p3 q1 q2 q3
  refine Albert.ext hE0 hE1 hE2 (octInComplex_eq_zero _ hcE.1 (two_by_two _ _ _ _ _ _ p1 q1 ?_))
    (octInComplex_eq_zero _ hcE.2.1 (two_by_two _ _ _ _ _ _ p2 q2 ?_))
    (octInComplex_eq_zero _ hcE.2.2 (two_by_two _ _ _ _ _ _ p3 q3 ?_)) <;>
  · rw [← complexAlbert_eq y hcy]
    simp [fe_complex_square_o, complexPart_complexAlbert, h01, h12, complexPart_octScalar]
    ring_nf
    simp [hapos.ne', hbpos.ne', hsigma]

/-! ## 9. The Gram matrix and the real part of the hidden determinant, from the sector data

This is `gram_phase_of_projections` (`FixedPairHidden.lean`) with the numerals removed and one
new ingredient: the exact-ledger version assumed `complexProjection (encoder r) = 0`, an exact-ledger
fact, so it had NO cross term. Nearby the sector part is small but nonzero and the cross term
must be handled -- abstractly, by trace associativity, never by a coordinate expansion. -/

/-- The sector/hidden cross term has no sector part. Three lines from
`complexProjection_zero_of_perp` (`SectorSubspace.lean`) and `inner_jordan_associative`
(`Native/AlgebraLaws.lean`).

`inner_jordan_associative` reads `inner (jordan x y) z = inner x (jordan y z)`;
the calculation uses its symmetric form. -/
theorem sector_hidden_cross_perp (x : Albert) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    complexProjection (jordan (complexProjection x) (hiddenAlbert M)) = 0 := by
  apply complexProjection_zero_of_perp
  intro v hv
  rw [← inner_jordan_associative]
  exact inner_sector_hiddenAlbert _ (complexSector_jordan _ _ ((complexSector_mem_iff v).mp hv)
    ((complexSector_mem_iff _).mp (complexProjection_mem x))) M

/-- The pure-algebra half of the sector/hidden square expansion, stated on `S + H` so that no
`rw` ever has to touch the right-hand side.

The right-hand side is written in the EXACT associativity that the four rewrites produce, with
the cross term appearing twice rather than as `(2:ℝ) • jordan S H`, so that the proof is the four
rewrites and nothing else -- `rw` closes the goal by `rfl`. -/
theorem jordan_add_self_split (S H : Albert) :
    jordan (S + H) (S + H) =
      jordan S S + jordan S H + (jordan S H + jordan H H) := by
  rw [jordan_add_left, jordan_add_right, jordan_add_right, jordan_comm H S]

/-- The sector part of a square splits, with no cross term. -/
theorem complexProjection_square_split (z : Albert) :
    complexProjection (jordan z z) =
      jordan (complexProjection z) (complexProjection z) +
        complexProjection (jordan (hiddenAlbert (hiddenMatrix z))
          (hiddenAlbert (hiddenMatrix z))) := by
  have hsec := (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hcross : complexProjection
      (jordan (hiddenAlbert (hiddenMatrix z)) (complexProjection z)) = 0 := by
    rw [jordan_comm]
    exact sector_hidden_cross_perp z (hiddenMatrix z)
  conv_lhs => rw [← complex_hidden_decomposition z]
  rw [jordan_add_left, jordan_add_right, jordan_add_right,
    complexProjection_add, complexProjection_add, complexProjection_add,
    complexProjection_eq_self _ (complexSector_jordan _ _ hsec hsec),
    sector_hidden_cross_perp z (hiddenMatrix z), hcross, add_zero, zero_add]

/-- Equal sector data force an equal hidden Gram matrix. `hidden_square_complexProjection`
(`Sector.lean`) reads `M^H M` off the sector part of the hidden square entry by entry,
and is fully general in `M`.

The off-diagonal extraction uses the three slot readers from section 5a:
`simpa only [complexPart_complexAlbert_o01]` produces `-G 0 1 = -G' 0 1`,
and `neg_inj` removes the negatives; the other slots use their corresponding readers.
The diagonal probes use `simp only [complexAlbert]` to unfold the constructor.

`Affine20.fin3_cases` (`Relabel.lean`) with `rcases ... with rfl | rfl | rfl`
keeps literal indices matching hypotheses stated at `0`, `1`, and `2`. -/
theorem gram_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z')) :
    sectorColumnGram (hiddenMatrix z) = sectorColumnGram (hiddenMatrix z') := by
  have h := complexProjection_square_split z
  rw [hS, hT, complexProjection_square_split z', hidden_square_complexProjection,
    hidden_square_complexProjection] at h
  replace h := (add_left_cancel h).symm
  have hF (M : Matrix (Fin 3) (Fin 3) ℂ) :
      (sectorColumnGram M 0 0).re + (sectorColumnGram M 1 1).re +
        (sectorColumnGram M 2 2).re = sectorFrobeniusSq M := by
    simp [sectorColumnGram, sectorFrobeniusSq, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hH : (sectorColumnGram (hiddenMatrix z)).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  have hH' : (sectorColumnGram (hiddenMatrix z')).IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_self _
  have hdiag (i : Fin 3) (hi : (sectorColumnGram (hiddenMatrix z) i i).re =
      (sectorColumnGram (hiddenMatrix z') i i).re) :
      sectorColumnGram (hiddenMatrix z) i i = sectorColumnGram (hiddenMatrix z') i i := by
    rw [← hH.coe_re_apply_self, ← hH'.coe_re_apply_self]; exact congrArg _ hi
  have e0 := congrArg Albert.d0 h
  have e1 := congrArg Albert.d1 h
  have e2 := congrArg Albert.d2 h
  have := hF (hiddenMatrix z)
  have := hF (hiddenMatrix z')
  simp [complexAlbert] at e0 e1 e2
  have := hdiag 0 (by linarith)
  have := hdiag 1 (by linarith)
  have := hdiag 2 (by linarith)
  have : sectorColumnGram (hiddenMatrix z) 0 1 = sectorColumnGram (hiddenMatrix z') 0 1 := by
    simpa [complexPart_complexAlbert, neg_inj] using
      congrArg (fun x => complexPart x.o01) h
  have : sectorColumnGram (hiddenMatrix z) 0 2 = sectorColumnGram (hiddenMatrix z') 0 2 := by
    simpa [complexPart_complexAlbert, neg_inj] using
      congrArg (fun x => complexPart x.o02) h
  have : sectorColumnGram (hiddenMatrix z) 1 2 = sectorColumnGram (hiddenMatrix z') 1 2 := by
    simpa [complexPart_complexAlbert, neg_inj] using
      congrArg (fun x => complexPart x.o12) h
  ext i j
  rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
    first | assumption | (rw [← hH.apply, ← hH'.apply]; exact congrArg star (by assumption))

theorem newtonCubicNorm_sector_split (z : Albert) :
    newtonCubicNorm z =
      ((trace (complexProjection z)) ^ 3
        - 3 * trace (complexProjection z) * trace (complexProjection (jordan z z))
        + 2 * (3 * inner (complexProjection z) (complexProjection (jordan z z))
              - 2 * inner (complexProjection z)
                  (jordan (complexProjection z) (complexProjection z))
              + 6 * (hiddenMatrix z).det.re)) / 6 := by
  have hsec : InComplexSector (complexProjection z) :=
    (complexSector_mem_iff _).mp (complexProjection_mem z)
  have hSX := inner_sector_complexProjection _ (jordan z z) hsec
  have hcube := hiddenAlbert_cubicNorm (hiddenMatrix z)
  have ht1 : trace z = trace (complexProjection z) := rfl
  have ht2 : trace (jordan z z) = trace (complexProjection (jordan z z)) := rfl
  set S := complexProjection z
  set H := hiddenAlbert (hiddenMatrix z)
  have hdec : S + H = z := complex_hidden_decomposition z
  have hSS := complexSector_jordan _ _ hsec hsec
  have hHtr : trace H = 0 := by simp [H, hiddenAlbert, trace]
  have hc1 : inner S (jordan S H) = 0 := by
    rw [← inner_jordan_associative]; exact inner_sector_hiddenAlbert _ hSS _
  have hc2 : inner H (jordan S S) = 0 := by
    rw [inner_comm]; exact inner_sector_hiddenAlbert _ hSS _
  have hc3 : inner H (jordan S H) = inner S (jordan H H) := by
    rw [inner_comm H, inner_jordan_associative]
  have key : inner (S + H) (jordan (S + H) (S + H)) =
      inner S (jordan S S) + 3 * inner S (jordan H H) + inner H (jordan H H) := by
    rw [jordan_add_self_split]
    simp [inner_add_left, inner_add_right, hc1, hc2, hc3]
    ring
  have hmix : inner S (jordan (S + H) (S + H)) = inner S (jordan S S) + inner S (jordan H H) := by
    rw [jordan_add_self_split]; simp only [inner_add_right, hc1]; ring
  rw [hdec] at key hmix
  rw [newtonCubicNorm, hHtr] at hcube
  rw [newtonCubicNorm, ht1, ht2]
  unfold inner at *
  linear_combination key / 3 - hmix + hSX + hcube

theorem det_re_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z'))
    (hcub : newtonCubicNorm z = newtonCubicNorm z') :
    (hiddenMatrix z).det.re = (hiddenMatrix z').det.re := by
  rw [newtonCubicNorm_sector_split z, newtonCubicNorm_sector_split z', hS, hT] at hcub
  linarith 

/-! ## 10. The colour SU(3) transport, with the exact Gram removed

`scaled_transport` (`FixedPairNormalization.lean`) builds the explicit left inverse
`A := 3 * M^H` out of `M^H M = diag(1/3)`. The argument needs only SOME left inverse, so
`A := G^{-1} M^H` with `G := M^H M` invertible does the same work and names no value. It is
`private` there, so it has to be re-proved in any case. -/

theorem su3_transport_general (M N : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : sectorColumnGram M = sectorColumnGram N)
    (hUnit : IsUnit (sectorColumnGram M).det)
    (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  have hGdef : sectorColumnGram M = M.conjTranspose * M := rfl
  have hGdef' : sectorColumnGram N = N.conjTranspose * N := rfl
  have hAM : ((sectorColumnGram M)⁻¹ * M.conjTranspose) * M = 1 := by
    rw [Matrix.mul_assoc, ← hGdef, Matrix.nonsing_inv_mul _ hUnit]
  have hMA : M * ((sectorColumnGram M)⁻¹ * M.conjTranspose) = 1 := mul_eq_one_comm.mp hAM
  have hUnitary :
      (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
        (N * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) = 1 := by
    have hstep :
        ((sectorColumnGram M)⁻¹ * M.conjTranspose).conjTranspose * (N.conjTranspose * N) *
            ((sectorColumnGram M)⁻¹ * M.conjTranspose) =
          (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)).conjTranspose *
            (M * ((sectorColumnGram M)⁻¹ * M.conjTranspose)) := by
      rw [← hGdef', ← hG, hGdef]
      simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc N.conjTranspose N ((sectorColumnGram M)⁻¹ * M.conjTranspose),
      ← Matrix.mul_assoc, hstep, hMA, Matrix.conjTranspose_one, Matrix.one_mul]
  refine ⟨⟨N * ((sectorColumnGram M)⁻¹ * M.conjTranspose),
    Matrix.mem_unitaryGroup_iff'.mpr hUnitary⟩, ?_, ?_⟩
  · simp_all
  · grind

theorem su3_maps_sector_hidden (s : SectorUnitary) (hs : (s : SectorMatrix).det = 1)
    (z : Albert) :
    (sectorLeftSU3Automorphism s hs).equiv z =
      complexProjection z + hiddenAlbert ((s : SectorMatrix) * hiddenMatrix z) := by rfl

/-! ## 11. The separator: Phi is a nonzero multiple of the hidden determinant's imaginary part

`phi_of_diagonal_complex` (`UnitShifts.lean`) holds for an
ARBITRARY third argument, with hypotheses `IsDiagonal x` and `InComplexSector y` -- exactly what
`native_ordered_positive_pair` delivers. At `x = flatXN = diag(1,0,-1)` the pair factor is
`2 * 1 * 1 * (-2) * (a*b*star v).im = 4*a*b*v.im`. Only `a*b*v.im /= 0` and "the same for both
candidates" are used downstream, so an overall sign error here would be harmless; it is spelled
out anyway. -/

theorem phi_normalized (y z : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b) :
    phi flatXN y z =
      4 * a * b * (complexPart y.o02).im * (hiddenMatrix z).det.im := by
  have hdiag : IsDiagonal flatXN := by simp [IsDiagonal, flatXN]
  rw [phi_of_diagonal_complex flatXN y z hdiag hcy]
  have hd0 : flatXN.d0 = (1 : ℝ) := rfl
  have hd1 : flatXN.d1 = (0 : ℝ) := rfl
  have hd2 : flatXN.d2 = (-1 : ℝ) := rfl
  rw [hd0, hd1, hd2, h01, h12, complexPart_octScalar, complexPart_octScalar,
    real_real_conj_im]
  ring

/-! ## 12. Assembly -/

/-- **The core**, at normalised position: the first frames are `flatFrameP`, the second frames
coincide. Equal ledgers give Phi equal up to sign, and an automorphism as soon as the signs agree. -/
theorem nearby_normal (T S : Triple) (hT : ∀ a : Fin 3, Frame (T a))
    (hS : ∀ a : Fin 3, Frame (S a)) (hP : T 0 = flatFrameP) (hP' : S 0 = flatFrameP)
    (hQ : T 1 = S 1) (a b : ℝ) (hcy : InComplexSector (encoder (S 1)))
    (h01 : (encoder (S 1)).o01 = octScalar a) (h12 : (encoder (S 1)).o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b) (hsig : (complexPart (encoder (S 1)).o02).im ≠ 0)
    (hL : ledger54 T = ledger54 S) (hTne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧
      (phiOf T = phiOf S → ∃ k : CompactAutomorphism, mapAtoms k S = T) := by
  have hatom k : complexProjection (T 2 k) = complexProjection (S 2 k) := by
    rw [← sub_eq_zero, ← complexProjection_sub]
    refine sector_slot_recovery _ (hS 1) _ a b hcy h01 h12 hapos hbpos hsig (fun i => ?_)
      fun i j => ?_
    · have := congrArg (fun L : Ledger54 => L.2.2.2 k i) hL
      simp [ledger54_R, hP, hP'] at this
      rw [inner_sub_right, inner_comm, this, inner_comm, sub_self]
    · have := congrArg (fun L : Ledger54 => L.1 i j k) hL
      simp [ledger54_C, hP, hP', hQ] at this
      rw [inner_sub_right, sub_eq_zero]
      exact this
  have hSigma : complexProjection (encoder (T 2)) = complexProjection (encoder (S 2)) := by simp [encoder, complexProjection_sub, hatom]
  have hTheta : complexProjection (jordan (encoder (T 2)) (encoder (T 2))) =
      complexProjection (jordan (encoder (S 2)) (encoder (S 2))) := by
    simp [frame_encoder_square _ (hT 2), frame_encoder_square _ (hS 2),
      complexProjection_add, hatom]
  have hGram := gram_eq_of_sector_data _ _ hSigma hTheta
  have hdetre := det_re_eq_of_sector_data _ _ hSigma hTheta
    (by rw [frame_encoder_cubicNorm _ (hT 2), frame_encoder_cubicNorm _ (hS 2)])
  have hdetim := im_sq_eq_of_normSq_eq _ _ (by
    rw [normSq_det_eq_gram_det_re, normSq_det_eq_gram_det_re]
    exact congrArg (fun G : Matrix (Fin 3) (Fin 3) ℂ => G.det.re) hGram) hdetre
  have hphi (U : Triple) (h0 : U 0 = flatFrameP) (h1 : U 1 = S 1) : phiOf U =
      4 * a * b * (complexPart (encoder (S 1)).o02).im * (hiddenMatrix (encoder (U 2))).det.im := by
    rw [phiOf_apply, h0, h1, flatFrameP_encoder, phi_normalized _ _ a b hcy h01 h12]
  rw [hphi T hP hQ, hphi S hP' rfl] at *
  refine ⟨by simp [mul_pow, hdetim], fun hsame => ?_⟩
  have hdetne : (hiddenMatrix (encoder (T 2))).det ≠ 0 := fun h =>
    right_ne_zero_of_mul hTne (by rw [h]; rfl)
  obtain ⟨s, hs, hsM⟩ := su3_transport_general _ _ hGram
    (isUnit_iff_ne_zero.mpr (by simp [sectorColumnGram, Matrix.det_mul, hdetne]))
    (Complex.ext hdetre (mul_left_cancel₀ (left_ne_zero_of_mul hTne) hsame)).symm
  have key c i : (sectorLeftSU3Automorphism s hs).equiv (T c i) = S c i := by
    rcases fin3_cases c with rfl | rfl | rfl
    · rw [hP, hP']; exact sectorLeftSU3_fixes_complex s hs _ (flatFrameP_inComplexSector i)
    · rw [hQ]; exact sectorLeftSU3_fixes_complex s hs _
        ((complexSector_mem_iff _).mp (frame_in_complexSector _ (hS 1) hcy i))
    · refine frame_eq_of_encoder_eq _ _ (hT 2) (hS 2) _ ?_ i
      rw [su3_maps_sector_hidden s hs, hsM, hSigma]
      exact complex_hidden_decomposition _
  refine ⟨(sectorLeftSU3Automorphism s hs).symm, funext fun c => funext fun i => ?_⟩
  rw [mapAtoms_apply, ← key c i]
  exact (sectorLeftSU3Automorphism s hs).equiv.symm_apply_apply _

/-- **`LocalOrbitCompleteness`** at a triple with uniform P block, on the sheet of one sign of
Phi. The open set is an epsilon box on the P block intersected with a half-space of Phi. -/
theorem localOrbitCompleteness_of (T0 : Triple) (σ : ℝ)
    (hP : ∀ i j : Fin 3, inner (T0 0 i) (T0 1 j) = 1 / 3) (h0 : 0 < σ * phiOf T0) :
    LocalOrbitCompleteness T0 := by
  refine ⟨{T : Triple | ∀ i j : Fin 3, |(ledger54 T).2.1 i j - 1 / 3| < 1 / 50} ∩
      {T | 0 < σ * phiOf T}, ?_, ⟨fun i j => ?_, h0⟩, fun T S hT hS hTU hSU hL => ?_⟩
  · simp [Set.setOf_forall]
    exact (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      isOpen_lt (((continuous_apply j).comp ((continuous_apply i).comp
        continuous_ledger54.snd.fst)).sub continuous_const).abs continuous_const).inter
      (isOpen_lt continuous_const (continuous_const.mul continuous_phiOf))
  · rw [ledger54_P, hP]; norm_num
  obtain ⟨g, a, b, ha, hb, hgp, h01g, h12g, hsecg⟩ :=
    native_ordered_positive_pair (T 0) (hT 0) (encoder (T 1))
  obtain ⟨g', a', b', ha', hb', hgp', h01g', h12g', hsecg'⟩ :=
    native_ordered_positive_pair (S 0) (hS 0) (encoder (S 1))
  have hQframe := g.map_frame _ (hT 1)
  have hQframe' := g'.map_frame _ (hS 1)
  rw [← g.encoder_map] at hsecg h01g h12g
  rw [← g'.encoder_map] at hsecg' h01g' h12g'
  obtain ⟨d0, d1, d2, e0, e1, e2⟩ :=
    normalised_diag_data _ hQframe (fun i j => inner (T 0 i) (T 1 j)) fun i j => by
      rw [← hgp i]; exact g.inner_map _ _
  obtain ⟨d0', d1', d2', e0', e1', e2'⟩ :=
    normalised_diag_data _ hQframe' (fun i j => inner (T 0 i) (T 1 j)) fun i j => by
      rw [← hgp' i, g'.inner_map]; exact (congrArg (fun L => L.2.1 i j) hL).symm
  have hB := fun i j => abs_lt.mp (show |inner (T 0 i) (T 1 j) - 1 / 3| < 1 / 50 from hTU.1 i j)
  obtain ⟨x1, x2⟩ := hB 2 2; obtain ⟨x3, x4⟩ := hB 2 0; obtain ⟨x5, x6⟩ := hB 1 2
  obtain ⟨x7, x8⟩ := hB 1 0; obtain ⟨x9, x10⟩ := hB 0 2; obtain ⟨x11, x12⟩ := hB 0 0
  have hl := slot_nondegenerate _ a b ha hb hsecg h01g h12g (frame_encoder_cubicNorm _ hQframe)
  simp only [d0, d1, d2, e0, e1, e2, abs_lt] at hl
  obtain ⟨hapos, hbpos, hsigma⟩ := hl (by constructor <;> linarith) (by constructor <;> linarith)
    (by constructor <;> linarith) (by constructor <;> linarith) (by constructor <;> linarith)
    (by constructor <;> linarith)
  obtain ⟨hn01, hn02, hn12, htri⟩ :=
    slot_data_eq_of_diag_eq _ _ hsecg hsecg' (d0.trans d0'.symm) (d1.trans d1'.symm)
      (d2.trans d2'.symm) (e0.trans e0'.symm) (e1.trans e1'.symm) (e2.trans e2'.symm)
      ((frame_encoder_cubicNorm _ hQframe).trans (frame_encoder_cubicNorm _ hQframe').symm)
  rw [h01g, h01g', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn01
  rw [h12g, h12g', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn12
  have haa := (pow_left_inj₀ ha ha' two_ne_zero).mp hn01
  have hbb := (pow_left_inj₀ hb hb' two_ne_zero).mp hn12
  rw [h01g, h12g, h01g', h12g', complexPart_octScalar, complexPart_octScalar,
    complexPart_octScalar, complexPart_octScalar, real_real_conj_re,
    real_real_conj_re, ← haa, ← hbb] at htri
  have hre := mul_left_cancel₀ (mul_pos (by linarith)
    (by linarith)).ne' htri
  have himsq := im_sq_eq_of_normSq_eq _ _ hn02 hre
  obtain ⟨m, hmP, hmy⟩ :=
    pair_normal_form_rel _ _ a b a' b' hsecg hsecg' h01g h12g h01g' h12g'
      (d0.trans d0'.symm) (d1.trans d1'.symm) (d2.trans d2'.symm) haa hbb hre himsq
  obtain ⟨hsq, himp⟩ := nearby_normal (mapAtoms (m.comp g) T) (mapAtoms g' S)
    (frame_mapAtoms _ T hT) (frame_mapAtoms g' S hS)
    (funext fun i => by rw [mapAtoms_apply, CompactAutomorphism.comp_apply, hgp i]; exact hmP i)
    (funext hgp') (funext fun i => frame_eq_of_encoder_eq _ _ (hT 1) hQframe' (m.comp g)
      (by rw [CompactAutomorphism.comp_apply, ← g.encoder_map, hmy]) i)
    a' b' hsecg' h01g' h12g' (by linarith) (by linarith) (fun h => hsigma (by simpa using himsq.trans (congrArg (· ^ 2) h)))
    (by rw [ledger54_map, ledger54_map, hL])
    (by rw [phiOf_mapAtoms]; exact right_ne_zero_of_mul hTU.2.ne')
  rw [phiOf_mapAtoms, phiOf_mapAtoms] at hsq himp
  obtain ⟨k, hk⟩ := himp (sub_eq_zero.mp ((mul_eq_zero.mp (show (phiOf T - phiOf S) *
    (σ * phiOf T + σ * phiOf S) = 0 by linear_combination σ * hsq)).resolve_right
      (by linarith [show 0 < σ * phiOf T from hTU.2, show 0 < σ * phiOf S from hSU.2])))
  exact ⟨(m.comp g).symm.comp (k.comp g'), by rw [← mapAtoms_comp, ← mapAtoms_comp, hk,
    mapAtoms_symm_mapAtoms]⟩

theorem flat_pair_overlap (i j : Fin 3) : inner (flatFrameP i) (flatFrameQ j) = 1 / 3 :=
  uniformLedger_pair_overlap flatFrameP flatFrameQ flatFrameR flatFrameR_frame flat_uniform i j

/-- **`LocalOrbitCompleteness` at the original flat ordered triple, with no premise.** -/
theorem localOrbitCompleteness_flatBaseTriple : LocalOrbitCompleteness flatBaseTriple :=
  localOrbitCompleteness_of _ (-1) flat_pair_overlap (by linarith [phiOf_flatBaseTriple_neg])

/-- **`LocalOrbitCompleteness` at the third-frame reversal, with no premise.** -/
theorem localOrbitCompleteness_flatBaseRev3 : LocalOrbitCompleteness flatBaseRev3 :=
  localOrbitCompleteness_of _ 1 flat_pair_overlap (by linarith [phiOf_flatBaseRev3_pos])

end Glennie.Compact.PairNormNearby
