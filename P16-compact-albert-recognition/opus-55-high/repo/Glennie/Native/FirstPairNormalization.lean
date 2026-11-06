module

public import Glennie.Native.OrderedPositivePair
public import Glennie.Native.FixedPairNormalization

/- Arbitrary genuine first-pair normalization and the ordered base fibre.

Route. `native_ordered_positive_pair` puts the first frame onto the ORIGINAL ordered
flat frame `flatFrameP` and makes the second element's encoder slots 01 and 12
NONNEGATIVE reals with slot 02 in the actual complex sector. The nine p-q pair
overlaps then force every complex slot norm to 1/3, so the two nonnegative reals are
exactly `flatScale`, and the vanishing cubic norm forces the real part of slot 02 to
zero, leaving slot 02 at `±flatScale*i`. One constructed scalar-fixing octonion
automorphism flips `+i` to `-i` when needed, landing on the ORIGINAL `flatY1`
convention `(1, -i, 1)`. A frame equals its own projector frame, so the encoder
equality gives all three same-index atom equalities with no reversal disjunction:
nonnegativity of the two real slots is what pins the encoder's overall sign, since a
negated encoder would give slot 01 the value `-flatScale < 0`. Composing the fixed-pair third-frame normalizer then classifies the third frame as the original R or
its ordered reversal. -/

@[expose] public section
namespace Glennie.NativeFirstPairNormalization
open Glennie.Compact.FlatBase Glennie.Compact.Affine20
open Glennie.NativeOrderedPositivePair Glennie.NativeFixedPairNormalization

/-! ## Scalar slots -/

theorem flatScale_pos : 0 < flatScale :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

/-- The nine-entry P block of a genuine frame pair, with the first frame diagonal and
the second encoder in the complex sector, saturates every complex slot at 1/3 and kills
the real part of the triangle. -/
theorem uniform_complex_slot_data (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hpd : ∀ i, IsDiagonal (p i))
    (hPQ : ∀ i j : Fin 3, inner (p i) (q j) = 1/3)
    (hqc : InComplexSector (encoder q)) :
    (encoder q).d0 = 0 ∧ (encoder q).d1 = 0 ∧ (encoder q).d2 = 0 ∧
      Complex.normSq (complexPart (encoder q).o01) = 1/3 ∧
      Complex.normSq (complexPart (encoder q).o02) = 1/3 ∧
      Complex.normSq (complexPart (encoder q).o12) = 1/3 ∧
      (complexPart (encoder q).o01 * complexPart (encoder q).o12 *
        star (complexPart (encoder q).o02)).re = 0 := by
  obtain ⟨a0, a1, a2⟩ := diagonal_frame_uniform_coordinates p hp hpd (q 0) (hPQ · 0)
  obtain ⟨b0, b1, b2⟩ := diagonal_frame_uniform_coordinates p hp hpd (q 2) (hPQ · 2)
  have hy : complexAlbert _ _ _ _ _ _ = encoder q := complexProjection_eq_self _ hqc
  have hs := frame_encoder_square q hq
  have hc := frame_encoder_cubicNorm q hq
  have e0 : (encoder q).d0 = 0 := by simp [encoder, a0, b0]
  have e1 : (encoder q).d1 = 0 := by simp [encoder, a1, b1]
  have e2 : (encoder q).d2 = 0 := by simp [encoder, a2, b2]
  have s0 := congrArg Albert.d0 hs
  have s1 := congrArg Albert.d1 hs
  have s2 := congrArg Albert.d2 hs
  rw [← hy, fe_complex_square_d0] at s0
  rw [← hy, fe_complex_square_d1] at s1
  rw [← hy, fe_complex_square_d2] at s2
  rw [← hy, fe_complex_cubic] at hc
  simp only [Albert.add_d0, Albert.add_d1, Albert.add_d2, e0, e1, e2,
    a0, a1, a2, b0, b1, b2] at s0 s1 s2 hc
  refine ⟨e0, e1, e2, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## The original second-frame encoder, slot by slot -/

/-- A complex-sector octonion slot with vanishing real part is a real multiple of the
standard imaginary unit. -/
theorem octInComplex_slot_eq (x : Octonion) (hx : OctInComplex x) (c : ℝ)
    (hre : (complexPart x).re = 0) (him : (complexPart x).im = c) :
    x = c • octI := by
  obtain ⟨hj, hk, hz⟩ := hx
  ext <;> simp_all [octI, quatI, complexPart]

/-- The ORIGINAL convention: `flatY1` upper slots are `(1, -i, 1)`. -/
theorem flatQ_slots :
    (flatScale • flatY1).d0 = 0 ∧ (flatScale • flatY1).d1 = 0 ∧
      (flatScale • flatY1).d2 = 0 ∧
      (flatScale • flatY1).o01 = octScalar flatScale ∧
      (flatScale • flatY1).o02 = (-flatScale) • octI ∧
      (flatScale • flatY1).o12 = octScalar flatScale := by
  simp [flatY1, octScalar_smul]

/-! ## The imaginary sign correction -/

theorem neg_octI_re : octRe (-octI) = 0 := by simp [octRe, octI, quatI]

theorem neg_octI_normSq : octNormSq (-octI) = 1 := by
  simp [octNormSq, octI, quatI, Quaternion.normSq_def']

theorem relatedTriple_fixes_flatFrameP (t : OctRelatedTriple) (i : Fin 3) :
    t.compactAutomorphism.equiv (flatFrameP i) = flatFrameP i :=
  frame_eq_of_encoder_eq flatFrameP flatFrameP flatFrameP_frame flatFrameP_frame
    t.compactAutomorphism
    (by rw [flatFrameP_encoder]; exact relatedTriple_flatXN t) i

theorem flatFrameP_diagonal (i : Fin 3) : IsDiagonal (flatFrameP i) :=
  frame_projectors_diagonal flatFrameP flatFrameP_frame
    (by rw [flatFrameP_encoder]; simp [IsDiagonal, flatXN]) i

/-! ## Landing exactly on the original second-frame encoder -/

/-- With the saturated slot data and the two nonnegative real slots, one constructed
automorphism fixing the original first frame carries the element to the ORIGINAL
`encoder flatFrameQ = flatScale • flatY1`. Nonnegativity of `a` is what rules out the
negated encoder, since `a = flatScale > 0`. -/
theorem encoder_to_flatQ (y : Albert) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h01 : y.o01 = octScalar a) (h12 : y.o12 = octScalar b)
    (hc : InComplexSector y)
    (hd0 : y.d0 = 0) (hd1 : y.d1 = 0) (hd2 : y.d2 = 0)
    (hn01 : Complex.normSq (complexPart y.o01) = 1/3)
    (hn02 : Complex.normSq (complexPart y.o02) = 1/3)
    (hn12 : Complex.normSq (complexPart y.o12) = 1/3)
    (htri : (complexPart y.o01 * complexPart y.o12 *
      star (complexPart y.o02)).re = 0) :
    ∃ m : CompactAutomorphism,
      (∀ i : Fin 3, m.equiv (flatFrameP i) = flatFrameP i) ∧
      m.equiv y = flatScale • flatY1 := by
  obtain ⟨hQ0, hQ1, hQ2, hQ01, hQ02, hQ12⟩ := flatQ_slots
  rw [h01, complexPart_octScalar, Complex.normSq_ofReal] at hn01
  rw [h12, complexPart_octScalar, Complex.normSq_ofReal] at hn12
  have := flatScale_sq; have := flatScale_pos
  have ha' : a = flatScale := by nlinarith
  have hb' : b = flatScale := by nlinarith
  have hy01 : y.o01 = octScalar flatScale := by rw [h01, ha']
  have hy12 : y.o12 = octScalar flatScale := by rw [h12, hb']
  have hvre : (complexPart y.o02).re = 0 := by
    simpa [h01, h12, complexPart_octScalar, ha', hb', flatScale_pos.ne'] using htri
  rw [Complex.normSq_apply, hvre] at hn02
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (show (complexPart y.o02).im ^ 2 = flatScale ^ 2 by
    linarith) with him | him
  · -- slot 02 carries `+flatScale*i`; the constructed automorphism flips the sign
    have hy02 := octInComplex_slot_eq y.o02 hc.2.1 flatScale hvre him
    obtain ⟨k, hk, hkI⟩ := exists_octAutomorphism_to_i (-octI) neg_octI_re neg_octI_normSq
    have hkIneg : k.A octI = -octI := by grind
    refine ⟨k.compactAutomorphism, relatedTriple_fixes_flatFrameP k, ?_⟩
    refine Albert.ext (hd0.trans hQ0.symm) (hd1.trans hQ1.symm) (hd2.trans hQ2.symm) ?_ ?_ ?_
    · show k.A y.o01 = (flatScale • flatY1).o01
      rw [hy01, hQ01, diagonalOctTriple_scalar k hk]
    · show k.C y.o02 = (flatScale • flatY1).o02
      rw [hk.2.1, hy02, hQ02, LinearEquiv.map_smul, hkIneg, smul_neg, neg_smul]
    · show k.B y.o12 = (flatScale • flatY1).o12
      rw [hk.1, hy12, hQ12, diagonalOctTriple_scalar k hk]
  · -- slot 02 already carries `-flatScale*i`: the original `flatY1` convention
    have hy02 := octInComplex_slot_eq y.o02 hc.2.1 (-flatScale) hvre him
    refine ⟨CompactAutomorphism.refl, fun _ => rfl, ?_⟩
    exact Albert.ext (hd0.trans hQ0.symm) (hd1.trans hQ1.symm) (hd2.trans hQ2.symm)
      (hy01.trans hQ01.symm) (hy02.trans hQ02.symm) (hy12.trans hQ12.symm)

/-! ## The public endpoints -/

/-- The nine-entry P block alone normalizes an arbitrary genuine frame pair to the
ORIGINAL ordered flat pair. No third frame and no triple traces are involved. The
conclusion is same-index equality with no reversal disjunction. -/
theorem native_flat_pair_normalization (p q : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hPQ : ∀ i j : Fin 3, inner (p i) (q j) = 1/3) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) := by
  obtain ⟨g, a, b, ha, hb, hgp, h01, h12, hsec⟩ := native_ordered_positive_pair p hp (encoder q)
  have hqe := g.encoder_map q
  obtain ⟨hd0, hd1, hd2, hn01, hn02, hn12, htri⟩ :=
    uniform_complex_slot_data flatFrameP _ flatFrameP_frame (g.map_frame q hq)
      flatFrameP_diagonal (fun i j => by rw [← hgp i, g.inner_map]; exact hPQ i j) (hqe ▸ hsec)
  rw [hqe] at hd0 hd1 hd2 hn01 hn02 hn12 htri
  obtain ⟨m, hmP, hmy⟩ := encoder_to_flatQ _ a b ha hb h01 h12 hsec hd0 hd1 hd2 hn01 hn02
    hn12 htri
  exact ⟨m.comp g, fun i => by rw [CompactAutomorphism.comp_apply, hgp i, hmP i],
    frame_eq_of_encoder_eq q flatFrameQ hq flatFrameQ_frame (m.comp g)
      (by rw [CompactAutomorphism.comp_apply, hmy, flatFrameQ_encoder])⟩

/-- ORDERED BASE FIBRE: every genuine frame triple with the original complete
54-entry flat ledger is carried by ONE actual product automorphism to the original
ordered flat triple or to its ordered third-frame reversal. -/
theorem native_flat_full54_ordered_base_fibre
    (p q r : Fin 3 → Albert) (hp : Frame p) (hq : Frame q) (hr : Frame r)
    (hL : ledger54 ![p, q, r] = ledger54 ![flatFrameP, flatFrameQ, flatFrameR]) :
    ∃ g : CompactAutomorphism,
      (∀ i : Fin 3, g.equiv (p i) = flatFrameP i) ∧
      (∀ i : Fin 3, g.equiv (q i) = flatFrameQ i) ∧
      ((∀ i : Fin 3, g.equiv (r i) = flatFrameR i) ∨
        (∀ i : Fin 3, g.equiv (r i) = reverseFrame flatFrameR i)) := by
  have hu := fun i j k =>
    (congrArg (fun L => L.1 i j k) hL).trans (flat_uniform i j k)
  obtain ⟨g, hgp, hgq⟩ := native_flat_pair_normalization p q hp hq
    (uniformLedger_pair_overlap p q r hr hu)
  have hpf := funext hgp
  have hqf := funext hgq
  obtain ⟨h, hhp, hhq, hcase⟩ :=
    native_fixed_pair_third_frame_normalization (fun i => g.equiv (r i))
      (g.map_frame r hr) fun i j k => by rw [← hpf, ← hqf, g.ledger_map]; exact hu i j k
  refine ⟨h.comp g, ?_, ?_, ?_⟩ <;> simp_all

end Glennie.NativeFirstPairNormalization
