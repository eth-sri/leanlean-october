module
public import Mathlib.Tactic
public import Glennie.Native.CoordinateSimp
public import Glennie.LinearSimp
public import AlbertGeometry.LinearSimp

public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.GRewrite
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Bound
public import Mathlib.Tactic.NormNum
public import Aesop

public import Glennie.Compact.FrameTopology
public import Glennie.Compact.Sections.Reversal
public import Glennie.Theorems.ComplexSectorSpan
public import Glennie.Theorems.CubicNorm
public import Glennie.Native.OrderedPositivePair
public import Glennie.UnitShifts

/- Pair normalization on the nonzero-Phi locus. Phi nonvanishing itself gives
all required slot nondegeneracy; equal ledgers then give squared-Phi rigidity,
and equal Phi gives diagonal automorphism transport. -/

@[expose] public section
namespace Glennie.Compact.PairNormNearby

open Glennie Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.Compact.FrameTopology
open Glennie.Compact.Sections
open Glennie.NativeOrderedPositivePair

noncomputable section
set_option maxHeartbeats 2000000

/-! ## 1. Pure arithmetic on reals and matrices

The arithmetic for `slot_nondegenerate` and `sector_slot_recovery` is isolated from
contexts carrying `Albert`, `Octonion` and `Complex.normSq (complexPart _)` atoms.
The lemmas use `linarith`, `linear_combination`, `calc` or a single `nlinarith` over
at most four hypotheses, and are called with explicit arguments. -/

theorem ne_zero_of_sq_eq_of_ne_zero (x x' : ℝ) (h : x ^ 2 = x' ^ 2) (hx : x ≠ 0) : x' ≠ 0 := by
  contrapose! hx
  simpa [hx] using h

/- Equal norms and equal real parts give equal squared imaginary parts. Squaring the
real-part equality is not a linear step. -/
theorem im_sq_eq_of_normSq_eq (z w : ℂ) (hn : Complex.normSq z = Complex.normSq w)
    (hr : z.re = w.re) : z.im ^ 2 = w.im ^ 2 := by
  simp only [Complex.normSq_apply, hr] at hn
  nlinarith

/- `MatrixDetEstimate.determinant_gram_real` (`:21`) with `columnGram` unfolded.
`columnGram` lives in the sub-namespace `Glennie.MatrixDetEstimate`. -/

/-! ## 1a. Four octonion facts about zero

These lemmas simplify `octMul 0 (octConj 0)` and related zero terms in
`jordan_flatXN` and `inner_diag_jordan_slots`. They follow from the definitions
(`Native.lean`). -/

/-! ## 2. Two re-derivations of `private` lemmas

`frame_as_projector` and `frame_eq_of_encoder_eq` are `private` in `FirstPairNormalization`
(`:32`, `:41`) and again in `FixedPairNormalization` (`:51`). They contain no values, survive
perturbation untouched. -/

theorem frame_eq_of_encoder_eq (q s : Fin 3 → Albert) (hq : Frame q) (hs : Frame s)
    (m : CompactAutomorphism) (hEnc : m.equiv (encoder q) = encoder s) (i : Fin 3) :
    m.equiv (q i) = s i := by
  rw [frame_as_projector q hq, compactAutomorphism_projectorFrame, hEnc,
    ← frame_as_projector s hs]

/-! ## 3. The exact diagonal probes of the normalised first frame

This replaces `diagonal_frame_uniform_coordinates` (`Theorems/DiagonalFrames.lean`), the ONE
line of `uniform_complex_slot_data` that breaks: it needs `inner (p i) (q j) = 1/3` exactly, to
conclude `(q j).d_m = 1/3`. Because `native_ordered_positive_pair` lands the first frame on
`flatFrameP` EXACTLY, overlaps with `flatFrameP` ARE the diagonal entries, with no hypothesis at
all. Its underlying `diagonal_test_inner` is `private` there, so it is re-derived.

Note the index reversal, the easiest thing in the file to get wrong:
`flatXN = diag(1,0,-1)` and `projectorFrame`'s first slot is the `(-1)`-eigenprojector, so
`flatFrameP 0` probes `d2` and `flatFrameP 2` probes `d0`. -/

theorem inner_flatFrameP (x : Albert) (i : Fin 3) :
    inner (flatFrameP i) x = ![x.d2, x.d1, x.d0] i := by
  fin_cases i <;> simp [FlatBase.flatFrameP_literal, inner_coordinates,
    diagonalAlbert, octDot_coordinates]

theorem flatFrameP_inComplexSector (i : Fin 3) : InComplexSector (flatFrameP i) :=
  diagonal_inComplex _ (frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i)

/-! ## 4. The P block determines six numbers, by subtraction and addition

These six replace the three exact values `1/3` of `uniform_complex_slot_data`. Nothing here
needs the overlaps to be uniform or even near uniform; `hPQ` is naming, not a hypothesis on the
values. There are exactly four independent numbers,
matching the four free parameters of a 3x3 matrix whose rows and columns all sum to one. -/

/-! ## 5. The three complex-square SLOT formulas

The package has `fe_complex_square_d0/d1/d2` (`Theorems/FrameSaturation.lean`) for the
three DIAGONAL entries of a complex-sector square, fully general in `(d,e,f,u,v,w)`, but no slot
companions. These are the companions. The convention is pinned, not guessed: `fe_complex_cubic`
(`:17`) reads `d*e*f - d*normSq w - e*normSq v - f*normSq u + 2*(u*w*star v).re`, which is
exactly the determinant of the Hermitian matrix `[[d,u,v],[star u,e,w],[star v,star w,f]]`, so
`(u,v,w)` are the `(01,02,12)` entries with no conjugation and these three are that matrix
squared. Each also matches `jordan_o01/o02/o12` (`Native.lean`) specialised to
`x = y`. -/

/-! ### 5a. The three slot readers of `complexAlbert`

Each is `rfl` componentwise: `complexAlbert` is a plain constructor application, so `.o01`
iota-reduces to `complexOct u`, and `complexPart (complexOct u) = ⟨u.re, u.im⟩`. The componentwise
`Complex.ext` form is used rather than a bare `rfl` on the whole equation so that the proof does
not lean on structure eta. -/

/-! ### 5b. Octonion bookkeeping inside the standard complex line -/

theorem complexPart_octScalar (a : ℝ) : complexPart (octScalar a) = (a : ℂ) := rfl

theorem normSq_complexPart_octScalar (a : ℝ) :
    Complex.normSq (complexPart (octScalar a)) = a ^ 2 := by
  rw [complexPart_octScalar, Complex.normSq_ofReal]; ring

/- `real_real_conj_re` of `FirstPairNormalization.lean`, which is `private` there. -/
theorem real_real_conj_re (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).re = a * b * z.re := by norm_num

theorem real_real_conj_im (a b : ℝ) (z : ℂ) :
    ((a : ℂ) * (b : ℂ) * star z).im = -(a * b * z.im) := by norm_num

/-! ## 6. The slot data of a complex-sector frame encoder, with symbols for the numerals

This is `uniform_complex_slot_data` (`FirstPairNormalization.lean`) and
`complex_slot_data_of_square` (`:87`) with `0`, `2/3` and `1/3` replaced by variables. The
interior of both is `linarith` over `fe_complex_square_d*` and `fe_complex_cubic`, all of which
are already general in `(d,e,f,u,v,w)`; only the SUBSTITUTED VALUES broke. Stated as a
comparison, which is all the route consumes, so no formula has to be written down and no square
root is ever taken. -/

/-! ### 6a. The nondegeneracy supplied by the neighbourhood

Nothing in section 6 needs the overlaps to be near uniform. The epsilon box is needed in exactly
three places: `0 < a`, `0 < b` and `(complexPart y.o02).im /= 0`.
The four algebraic identities here supply the nine real numbers to `nondegenerate_core`
(section 1). The triangle term is rewritten in a separate `have` so the norm-square
atoms remain in the form used by the goal. -/

/-! ## 7. The pair, perturbed: pair normalization

Step 5 of the proof -- `flatQ_slots` (`FirstPairNormalization.lean`) and
`encoder_to_flatQ` (`:244`) -- is what breaks hardest: both name the target
`flatScale • flatY1`. Nearby there is no canonical target, so "normalise onto a fixed element"
becomes "two normal forms with the same P data are related". The sign branch is still resolved by
`exists_octAutomorphism_to_i (-octI)`, exactly as at `:283`, but that automorphism must now act
on a GENERAL complex slot `rho + sigma*octI`, not just on `sigma*octI`; that is the one place
where the whole of `DiagonalOctTriple` is needed. `octConj` is NOT used: octonion conjugation is
an anti-automorphism and can never be a sign corrector. -/

theorem relatedTriple_fixes_flatFrameP (t : OctRelatedTriple) (i : Fin 3) :
    t.compactAutomorphism.equiv (flatFrameP i) = flatFrameP i := by
  fin_cases i <;> simp [FlatBase.flatFrameP_literal, OctRelatedTriple.compactAutomorphism,
    OctRelatedTriple.albertEquiv, diagonalAlbert]

/- The sign-flip automorphism conjugates the whole complex line, not merely its imaginary
axis. `DiagonalOctTriple` (`Theorems/OctonionAutomorphisms.lean`) says `B = A`, `C = A` and
`A (octScalar 1) = octScalar 1`; with `A octI = -octI` and real linearity that is all that is
needed. -/

theorem octInComplex_conj_slot (k : OctRelatedTriple) (hk : DiagonalOctTriple k)
    (hkI : k.A octI = -octI) (x : Octonion) (hx : OctInComplex x) :
    OctInComplex (k.A x) ∧ complexPart (k.A x) = star (complexPart x) := by
  have he : x = octScalar (complexPart x).re + (complexPart x).im • octI := by
    obtain ⟨hj, hk, hz⟩ := hx
    apply Prod.ext
    · apply Quaternion.ext <;> simp [octScalar, octI, quatI, complexPart, hj, hk]
    · simp [octScalar, octI, quatI, hz]
  rw [he, map_add, map_smul, diagonalOctTriple_scalar k hk, hkI]
  simp [OctInComplex, complexPart, octScalar, octI, quatI, Complex.ext_iff]

/- The automorphism built from `exists_octAutomorphism_to_i (-octI)`: it fixes `flatFrameP`
pointwise, fixes every real slot and conjugates every complex slot. -/
/- Two Step-A normal forms with the same P data are equal, or are carried to one another by one
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
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himsq with him | him
  · refine ⟨CompactAutomorphism.refl, fun _ => rfl, ?_⟩
    show y = y'
    ext <;> simp_all [InComplexSector, OctInComplex, complexPart, octScalar]
  · obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI)
      (by simp [octRe, octI, quatI]) (by simp [octI, quatI, octNormSq, Quaternion.normSq_def'])
    have hkIneg : k.A octI = -octI := by
      simpa only [map_neg, neg_eq_iff_eq_neg] using hkI
    refine ⟨k.compactAutomorphism, relatedTriple_fixes_flatFrameP k, ?_⟩
    have hA01 := octInComplex_conj_slot k hk hkIneg y.o01 hc.1
    have hC02 := octInComplex_conj_slot k hk hkIneg y.o02 hc.2.1
    have hB12 := octInComplex_conj_slot k hk hkIneg y.o12 hc.2.2
    dsimp [OctRelatedTriple.compactAutomorphism, OctRelatedTriple.albertEquiv]
    rw [hk.1, hk.2.1]
    ext <;> simp_all [InComplexSector, OctInComplex, complexPart, octScalar, Complex.ext_iff]

/- **THE EXTENSION OF `native_flat_pair_normalization` (`FirstPairNormalization.lean`).**

Two genuine frame pairs whose nine overlaps AGREE, and are within `1/50` of uniform, are carried
onto ONE AND THE SAME normalised pair by two actual product automorphisms, and that common
normal form is exhibited with its two positive real slots and its nonvanishing imaginary slot.

At the exact value `1/3` this specialises to the theorem, with `flatFrameQ` as the
common target. Away from it, the common target is the P-block-determined normal form and is NOT
named -- which is why the proof's `flatQ_slots` and `encoder_to_flatQ` had to be
replaced rather than reused. -/
theorem phi_normalized (y z : Albert) (a b : ℝ)
    (hcy : InComplexSector y) (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b) :
    phi flatXN y z =
      4 * a * b * (complexPart y.o02).im * (hiddenMatrix z).det.im := by
  rw [phi_of_diagonal_complex flatXN y z (by simp [IsDiagonal, flatXN]) hcy,
    h01, h12, complexPart_octScalar, complexPart_octScalar, real_real_conj_im]
  norm_num [flatXN] <;> ring_nf <;> simp

theorem nearby_pair_normalization
    (p q p' q' : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hp' : Frame p') (hq' : Frame q')
    (z : Albert) (hphi : phi (encoder p) (encoder q) z ≠ 0)
    (hEq : ∀ i j : Fin 3, inner (p i) (q j) = inner (p' i) (q' j)) :
    ∃ (g g' : CompactAutomorphism) (a b : ℝ),
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g'.equiv (p' i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = g'.equiv (q' i)) ∧
      InComplexSector (encoder fun i => g'.equiv (q' i)) ∧
      (encoder fun i => g'.equiv (q' i)).o01 = octScalar a ∧
      (encoder fun i => g'.equiv (q' i)).o12 = octScalar b ∧
      0 < a ∧ 0 < b ∧
      (complexPart (encoder fun i => g'.equiv (q' i)).o02).im ≠ 0 := by
  -- Step A on each pair.  No `1/3` enters here: `native_ordered_positive_pair`
  -- (`OrderedPositivePair.lean`) takes an ARBITRARY Albert element.
  obtain ⟨g, a, b, ha, hb, hgp, hy01, hy12, hcy⟩ :=
    native_ordered_positive_pair p hp (encoder q)
  obtain ⟨g', a', b', ha', hb', hgp', hy01', hy12', hcy'⟩ :=
    native_ordered_positive_pair p' hp' (encoder q')
  let y := encoder fun i => g.equiv (q i)
  let y' := encoder fun i => g'.equiv (q' i)
  have hQframe := g.map_frame q hq
  have hQframe' := g'.map_frame q' hq'
  have hyg := g.encoder_map q
  have hyg' := g'.encoder_map q'
  rw [← hyg] at hcy hy01 hy12
  rw [← hyg'] at hcy' hy01' hy12'
  -- the normalised overlaps ARE the P block
  have hPQ : ∀ i j : Fin 3,
      inner (flatFrameP i) (g.equiv (q j)) = inner (flatFrameP i) (g'.equiv (q' j)) := by
    intro i j
    calc
      _ = inner (p i) (q j) := by rw [← hgp i, g.inner_map]
      _ = inner (p' i) (q' j) := hEq i j
      _ = _ := by rw [← hgp' i, g'.inner_map]
  obtain ⟨hd0, hd1, hd2, hs0, hs1, hs2⟩ :
      y.d0 = y'.d0 ∧ y.d1 = y'.d1 ∧ y.d2 = y'.d2 ∧
      (jordan y y).d0 = (jordan y' y').d0 ∧
      (jordan y y).d1 = (jordan y' y').d1 ∧
      (jordan y y).d2 = (jordan y' y').d2 := by
    dsimp only [y, y']
    rw [frame_encoder_square _ hQframe, frame_encoder_square _ hQframe']
    have h := hPQ
    norm_num [Fin.forall_fin_succ, inner_flatFrameP] at h
    simp_all [encoder]
  have hcubeq := (frame_encoder_cubicNorm _ hQframe).trans
    (frame_encoder_cubicNorm _ hQframe').symm
  have hX : g.equiv (encoder p) = flatXN := by
    rw [← g.encoder_map p, funext hgp, flatFrameP_encoder]
  have hn : phi flatXN y (g.equiv z) ≠ 0 := by
    dsimp only [y]
    rwa [hyg, ← hX, g.phi_map]
  rw [phi_normalized _ _ a b hcy hy01 hy12] at hn
  simp only [ne_eq, mul_eq_zero, not_or] at hn
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm hn.1.1.1.2)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hn.1.1.2)
  have hsigma : (complexPart y.o02).im ≠ 0 := hn.1.2
  -- the slot data of the two normal forms agree
  obtain ⟨hn01, hn02, hn12, htri⟩ :
      Complex.normSq (complexPart y.o01) = Complex.normSq (complexPart y'.o01) ∧
      Complex.normSq (complexPart y.o02) = Complex.normSq (complexPart y'.o02) ∧
      Complex.normSq (complexPart y.o12) = Complex.normSq (complexPart y'.o12) ∧
      (complexPart y.o01 * complexPart y.o12 * star (complexPart y.o02)).re =
        (complexPart y'.o01 * complexPart y'.o12 * star (complexPart y'.o02)).re := by
    have hc : InComplexSector y := hcy
    have hc' : InComplexSector y' := hcy'
    have hcub : newtonCubicNorm y = newtonCubicNorm y' := hcubeq
    clear * - y y' hc hc' hd0 hd1 hd2 hs0 hs1 hs2 hcub
    clear_value y y'
    simp only [InComplexSector, OctInComplex] at hc hc'
    simp_all [albert_coords, newtonCubicNorm_coordinates, complexPart,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first
    | nlinarith only [hs0, hs1, hs2]
    | linear_combination hcub / 2 + (y'.d1 + y'.d2 - y'.d0) / 4 * hs0 +
        (y'.d0 + y'.d2 - y'.d1) / 4 * hs1 +
        (y'.d0 + y'.d1 - y'.d2) / 4 * hs2
  dsimp only [y, y'] at hn01 hn02 hn12 htri
  have haa : a = a' := by
    rw [hy01, hy01', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn01
    exact (sq_eq_sq₀ ha ha').mp hn01
  have hbb : b = b' := by
    rw [hy12, hy12', normSq_complexPart_octScalar, normSq_complexPart_octScalar] at hn12
    exact (sq_eq_sq₀ hb hb').mp hn12
  have hre : (complexPart y.o02).re =
      (complexPart y'.o02).re := by
    rw [hy01, hy12, hy01', hy12', complexPart_octScalar, complexPart_octScalar,
      complexPart_octScalar, complexPart_octScalar, real_real_conj_re,
      real_real_conj_re, ← haa, ← hbb] at htri
    exact mul_left_cancel₀ (ne_of_gt (mul_pos hapos hbpos)) htri
  have himsq :=
    im_sq_eq_of_normSq_eq _ _ hn02 hre
  have hsigma' :=
    ne_zero_of_sq_eq_of_ne_zero _ _ himsq hsigma
  -- compare the two normal forms and absorb the sign
  obtain ⟨m, hmP, hmy⟩ :=
    pair_normal_form_rel _ _ a b a' b' hcy hcy' hy01 hy12 hy01' hy12'
      hd0 hd1 hd2 haa hbb hre himsq
  refine ⟨m.comp g, g', a', b', ?_, hgp', ?_, hcy', hy01', hy12', ?_, ?_, hsigma'⟩
  · intro i
    rw [CompactAutomorphism.comp_apply, hgp i]
    exact hmP i
  · intro i
    refine frame_eq_of_encoder_eq q (fun i => g'.equiv (q' i)) hq hQframe' (m.comp g) ?_ i
    rw [CompactAutomorphism.comp_apply, ← hyg, hmy]
  · linarith [haa, hapos]
  · linarith [hbb, hbpos]

/-! ## 8. The ledger sees the third frame's sector data, slot by slot

This replaces `uniformLedger_complexProjection_encoder(_square)`
(`Theorems/ComplexSectorSpan.lean`), which recover the sector projection by declaring the
nine mixed products `jordan (p i) (q j)` a BASIS -- which needs
`uniform_pair_mixed_linearIndependent` and so the EXACT uniform P block. Linear independence is
an open condition, so a perturbation of that route would need an openness proof for a 9x9
determinant in a variable produced by an existential. The route below avoids spanning
altogether: it extracts the nine sector coordinates one at a time, at the cost of three 2x2
determinants, each of which is `a*b*sigma` up to sign and so nonzero by section 6a. -/

theorem sector_slot_recovery (y E : Albert) (a b : ℝ)
    (hcy : InComplexSector y)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hapos : 0 < a) (hbpos : 0 < b)
    (hsigma : (complexPart y.o02).im ≠ 0)
    (hd : ∀ i, inner (flatFrameP i) E = 0)
    (hp : ∀ i, inner (jordan (flatFrameP i) y) E = 0)
    (hq : ∀ i, inner (jordan (flatFrameP i) (jordan y y)) E = 0) :
    complexProjection E = 0 := by
  have ha := ne_of_gt hapos
  have hb := ne_of_gt hbpos
  norm_num [Fin.forall_fin_succ] at hd hp hq
  ext <;> simp_all [InComplexSector, OctInComplex, albert_coords, complexProjection, complexOct, complexPart,
    FlatBase.flatFrameP_literal, diagonalAlbert,
    mul_eq_zero] <;> grind

/-! ## 9. The Gram matrix and the real part of the hidden determinant, from the sector data

This is `gram_phase_of_projections` (`FixedPairHidden.lean`) with the numerals removed and one
new ingredient: the exact-ledger version assumed `complexProjection (encoder r) = 0`, an exact-ledger
fact, so it had NO cross term. Nearby the sector part is small but nonzero and the cross term
must be handled -- abstractly, by trace associativity, never by a coordinate expansion. -/

/- The sector/hidden cross term has no sector part. Three lines from
`complexProjection_zero_of_perp` (`SectorSubspace.lean`) and `inner_jordan_associative`
(`Native/AlgebraLaws.lean`).

`inner_jordan_associative` reads `inner (jordan x y) z = inner x (jordan y z)`;
the calculation uses its symmetric form. -/

/- The sector part of a square splits, with no cross term. -/

/- Equal sector data force an equal hidden Gram matrix. `hidden_square_complexProjection`
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
  simp [Albert.ext_iff, albert_coords, complexProjection, complexOct, complexPart] at hS hT
  rcases hS with ⟨h0, h1, h2, ⟨h01r, h01i⟩, ⟨h02r, h02i⟩, h12r, h12i⟩
  simp only [h0, h1, h2, h01r, h01i, h02r, h02i, h12r, h12i] at hT
  ring_nf at hT
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext
  all_goals simp [sectorColumnGram, hiddenMatrix, hiddenColumn, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im]
  all_goals ring_nf
  all_goals linarith only [hT]

theorem newtonCubicNorm_sector_split (z : Albert) :
    newtonCubicNorm z =
      ((trace (complexProjection z)) ^ 3
        - 3 * trace (complexProjection z) * trace (complexProjection (jordan z z))
        + 2 * (3 * inner (complexProjection z) (complexProjection (jordan z z))
              - 2 * inner (complexProjection z)
                  (jordan (complexProjection z) (complexProjection z))
              + 6 * (hiddenMatrix z).det.re)) / 6 := by
  simp [albert_coords, newtonCubicNorm_coordinates, trace, complexProjection,
    complexOct, complexPart, hiddenMatrix, hiddenColumn, Matrix.det_fin_three,
    Complex.mul_re, Complex.mul_im]
  ring

theorem det_re_eq_of_sector_data (z z' : Albert)
    (hS : complexProjection z = complexProjection z')
    (hT : complexProjection (jordan z z) = complexProjection (jordan z' z'))
    (hcub : newtonCubicNorm z = newtonCubicNorm z') :
    (hiddenMatrix z).det.re = (hiddenMatrix z').det.re := by
  rw [newtonCubicNorm_sector_split z, newtonCubicNorm_sector_split z', hS, hT] at hcub
  linarith [hcub]

/-! ## 10. The colour SU(3) transport, with the exact Gram removed

`scaled_transport` (`FixedPairNormalization.lean`) builds the explicit left inverse
`A := 3 * M^H` out of `M^H M = diag(1/3)`. The argument needs only SOME left inverse, so
`A := G^{-1} M^H` with `G := M^H M` invertible does the same work and names no value. It is
`private` there, so it has to be re-proved in any case. -/

theorem su3_transport_general (M N : Matrix (Fin 3) (Fin 3) ℂ)
    (hG : sectorColumnGram M = sectorColumnGram N)
    (hM : M.det ≠ 0)
    (hdet : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  change M.conjTranspose * M = N.conjTranspose * N at hG
  have hm := isUnit_iff_ne_zero.mpr hM
  have hMA := Matrix.mul_nonsing_inv M hm
  have hAM := Matrix.nonsing_inv_mul M hm
  have hUnitary : (N * M⁻¹).conjTranspose * (N * M⁻¹) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc N.conjTranspose N M⁻¹, ← hG,
      Matrix.mul_assoc, hMA, Matrix.mul_one, ← Matrix.conjTranspose_mul,
      hMA, Matrix.conjTranspose_one]
  refine ⟨⟨N * M⁻¹, Matrix.mem_unitaryGroup_iff'.mpr hUnitary⟩, ?_, ?_⟩
  · change (N * M⁻¹).det = 1
    rw [Matrix.det_mul, hdet, ← Matrix.det_mul, hMA, Matrix.det_one]
  · change N * M⁻¹ * M = N
    rw [Matrix.mul_assoc, hAM, Matrix.mul_one]

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

/-! ## 12. Assembly

Equal ledgers determine the normalized sector and hidden Gram data. Nonzero Phi
supplies all slot and determinant nondegeneracy needed for transport. -/

/- **The core.** Two nearby frame triples with the same ledger have Phi equal up to sign, and
are automorphism related as soon as the signs agree. No premise; the only shrink is the box. -/
theorem nearby_core (T S : Triple)
    (hT : ∀ a : Fin 3, Frame (T a)) (hS : ∀ a : Fin 3, Frame (S a))
    (hL : ledger54 T = ledger54 S) (hTne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧
      (phiOf T = phiOf S → ∃ k : CompactAutomorphism, mapAtoms k S = T) := by
  -- the two P blocks agree, and T's is in the box
  have hPeq : ∀ i j : Fin 3, inner (T 0 i) (T 1 j) = inner (S 0 i) (S 1 j) := fun i j =>
    congrArg (fun L : Ledger54 => L.2.1 i j) hL
  -- normalise both pairs onto a common normal form
  obtain ⟨g, g', a, b, hgp, hgp', hqq, hcy, h01, h12, hapos, hbpos, hsig⟩ :=
    nearby_pair_normalization (T 0) (T 1) (S 0) (S 1) (hT 0) (hT 1) (hS 0) (hS 1) (encoder (T 2)) hTne hPeq
  let q := fun i => g'.equiv (S 1 i)
  let rT := fun k => g.equiv (T 2 k)
  let rS := fun k => g'.equiv (S 2 k)
  let y := encoder q
  let z := encoder rT
  let z' := encoder rS
  have hQframe : Frame q := g'.map_frame (S 1) (hS 1)
  have hrTframe : Frame rT := g.map_frame (T 2) (hT 2)
  have hrSframe : Frame rS := g'.map_frame (S 2) (hS 2)
  have hLT : mapAtoms g T = ![flatFrameP, q, rT] := by
    funext a i
    fin_cases a
    · exact hgp i
    · exact hqq i
    · rfl
  have hLS : mapAtoms g' S = ![flatFrameP, q, rS] := by
    funext a i
    fin_cases a
    · exact hgp' i
    · rfl
    · rfl
  have hL' : ledger54 ![flatFrameP, q, rT] = ledger54 ![flatFrameP, q, rS] := by
    rw [← hLT, ← hLS, ledger54_map, ledger54_map, hL]
  -- every atom of the common normalised second frame lies in the sector, because its encoder
  -- does (`frame_in_complexSector`, `Theorems/ComplexSectorSpan.lean`)
  have hQsec : ∀ j : Fin 3, InComplexSector (q j) := fun j =>
    (complexSector_mem_iff _).mp (frame_in_complexSector _ hQframe hcy j)
  -- STEP C: the ledger pins the sector data of the third frame, atom by atom
  have hatom : ∀ k : Fin 3,
      complexProjection (g.equiv (T 2 k)) = complexProjection (g'.equiv (S 2 k)) := by
    intro k
    -- R block gives the three diagonal entries
    have hR : ∀ i : Fin 3,
        inner (flatFrameP i) (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i
      have h := congrArg (fun L : Ledger54 => L.2.2.2 k i) hL'
      change inner (rT k) (flatFrameP i) = inner (rS k) (flatFrameP i) at h
      simpa only [inner_sub_right, sub_eq_zero, inner_comm] using h
    -- C block gives the nine mixed probes
    have hC : ∀ i j : Fin 3,
        inner (jordan (flatFrameP i) (q j))
          (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i j
      have h := congrArg (fun L : Ledger54 => L.1 i j k) hL'
      change inner (jordan (flatFrameP i) (q j)) (rT k) =
        inner (jordan (flatFrameP i) (q j)) (rS k) at h
      simpa only [inner_sub_right, sub_eq_zero] using h
    -- push onto the sector projection, then take the two j-combinations
    have hyc : ∀ i : Fin 3,
        inner (jordan (flatFrameP i) y)
          (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i
      change inner (jordan _ (q 2 - q 0)) _ = 0
      simp only [jordan_sub_right, inner_sub_left, hC i 2, hC i 0, sub_self]
    have hsqc : ∀ i : Fin 3,
        inner (jordan (flatFrameP i)
            (jordan y
              y))
          (g.equiv (T 2 k) - g'.equiv (S 2 k)) = 0 := by
      intro i
      rw [frame_encoder_square _ hQframe, jordan_add_right, inner_add_left, hC i 2, hC i 0]
      ring
    have hzero := sector_slot_recovery y _ a b hcy h01 h12
      hapos hbpos hsig hR hyc hsqc
    rw [complexProjection_sub] at hzero
    exact sub_eq_zero.mp hzero
  -- the encoder-level sector data
  have hSigma : complexProjection z =
      complexProjection z' := by
    simp only [z, z', encoder, complexProjection_sub, rT, rS, hatom]
  have hTheta : complexProjection (jordan z
        z) =
      complexProjection (jordan z'
        z') := by
    rw [frame_encoder_square _ hrTframe, frame_encoder_square _ hrSframe,
      complexProjection_add, complexProjection_add, hatom 2, hatom 0]
  -- STEP D: Gram and the real part of the determinant agree
  have hGram
                                         :=
    gram_eq_of_sector_data _ _ hSigma hTheta
  have hdetre
                               :=
    det_re_eq_of_sector_data _ _ hSigma hTheta
      (by rw [frame_encoder_cubicNorm _ hrTframe, frame_encoder_cubicNorm _ hrSframe])
  have hnorm : Complex.normSq (hiddenMatrix z).det =
      Complex.normSq (hiddenMatrix z').det := by
    simpa [sectorColumnGram, Matrix.det_mul, Matrix.det_conjTranspose, Complex.mul_re, Complex.normSq_apply]
      using congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M.det.re) hGram
  have hdetim
                                   :=
    im_sq_eq_of_normSq_eq _ _ hnorm hdetre
  -- Phi at normalised position
  have hcoef : 4 * a * b * (complexPart y.o02).im ≠ 0 := by positivity
  have hphi (r : Fin 3 → Albert) : phiOf ![flatFrameP, q, r] =
      4 * a * b * (complexPart y.o02).im * (hiddenMatrix (encoder r)).det.im := by
    simpa [Glennie.Compact.Sections.phiOf, flatFrameP_encoder] using phi_normalized y (encoder r) a b hcy h01 h12
  have hphiT := congrArg phiOf hLT
  have hphiS := congrArg phiOf hLS
  rw [phiOf_mapAtoms, hphi] at hphiT hphiS
  refold_let z at hphiT
  refold_let z' at hphiS
  refine ⟨?_, ?_⟩
  · rw [hphiT, hphiS]
    simp only [mul_pow, hdetim]
  · intro hsame
    rw [hphiT, hphiS] at hsame
    have him
                                 :=
      mul_left_cancel₀ hcoef hsame
    have hdeteq
                              := Complex.ext hdetre him
    -- nonvanishing determinant, from Phi alone
    have hdetne : (hiddenMatrix z).det ≠ 0 := by
      contrapose! hTne
      simp [hphiT, hTne]
    obtain ⟨s, hs, hsM⟩ :=
      su3_transport_general (hiddenMatrix z)
        (hiddenMatrix z') hGram hdetne hdeteq.symm
    -- transport the third encoder, then the three atoms
    have hmap : (sectorLeftSU3Automorphism s hs).equiv
        z = z' := by
      rw [su3_maps_sector_hidden s hs, hsM, hSigma]
      exact complex_hidden_decomposition _
    have hatoms
                                                                                    :=
      frame_eq_of_encoder_eq _ _ hrTframe hrSframe (sectorLeftSU3Automorphism s hs) hmap
    refine ⟨g.symm.comp ((sectorLeftSU3Automorphism s hs).symm.comp g'), ?_⟩
    funext c i
    apply g.equiv.symm_apply_eq.mpr
    apply (sectorLeftSU3Automorphism s hs).equiv.symm_apply_eq.mpr
    symm
    rcases fin3_cases c with rfl | rfl | rfl
    · change (sectorLeftSU3Automorphism s hs).equiv (g.equiv (T 0 i)) = g'.equiv (S 0 i)
      rw [hgp i, hgp' i]
      exact sectorLeftSU3_fixes_complex s hs _ (flatFrameP_inComplexSector i)
    · rw [hqq]
      exact sectorLeftSU3_fixes_complex s hs _ (hQsec i)
    · exact hatoms i

/-! ### The two endpoints -/

end
end Glennie.Compact.PairNormNearby
