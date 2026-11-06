module

public import Glennie.SectorBudgets
public import Glennie.Theorems.DiagonalFrames
public import Glennie.Theorems.ComplexSectorSpan
public import Glennie.Theorems.SectorCubicNorm

/- Concrete saturation and reconstruction for actual native compact frames.
The intermediate reductions below are proved from native definitions. -/

@[expose] public section
namespace Glennie


theorem fe_complex_cubic (d e f : ℝ) (u v w : ℂ) :
    newtonCubicNorm (complexAlbert d e f u v w) = d*e*f-
      d*Complex.normSq w-e*Complex.normSq v-f*Complex.normSq u+
      2*(u*w*star v).re := by
  rw [newtonCubicNorm_coordinates]
  simp [complexAlbert, complexOct, oct_simps, octRe, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem fe_complex_square_d0 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d0 =
      d^2+Complex.normSq u+Complex.normSq v := by
  simp [oct_simps, complexAlbert, complexOct, Complex.normSq_apply]
  ring
theorem fe_complex_square_d1 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d1 =
      e^2+Complex.normSq u+Complex.normSq w := by
  simp [oct_simps, complexAlbert, complexOct, Complex.normSq_apply]
  ring
theorem fe_complex_square_d2 (d e f : ℝ) (u v w : ℂ) :
    (jordan (complexAlbert d e f u v w) (complexAlbert d e f u v w)).d2 =
      f^2+Complex.normSq v+Complex.normSq w := by
  simp [oct_simps, complexAlbert, complexOct, Complex.normSq_apply]
  ring

theorem fe_triangle_norm (u v w : ℂ) :
    Complex.normSq (u*w*star v) = Complex.normSq u*Complex.normSq v*Complex.normSq w := by
  simp [map_mul,Complex.normSq_conj]
  ring

/-- Saturation forces all actual diagonal and off-diagonal energies. -/
theorem fe_complex_saturation (d e f : ℝ) (u v w : ℂ)
    (hn : inner (complexAlbert d e f u v w) (complexAlbert d e f u v w) = 2)
    (ht : (u*w*star v).im^2 = 1/27) :
    d = 0 ∧ e = 0 ∧ f = 0 ∧ Complex.normSq u = 1/3 ∧
      Complex.normSq v = 1/3 ∧ Complex.normSq w = 1/3 := by
  let S := Complex.normSq u+Complex.normSq v+Complex.normSq w
  have hs0 : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (add_nonneg (Complex.normSq_nonneg u) (Complex.normSq_nonneg v))
      (Complex.normSq_nonneg w)
  have hs1 : S ≤ 1 := by
    rw [complexAlbert_inner] at hn
    dsimp [S]
    nlinarith 
  have him : 1/27 ≤ Complex.normSq u*Complex.normSq v*Complex.normSq w := by
    have hi := fe_triangle_norm u v w
    rw [Complex.normSq_apply] at hi
    nlinarith 
  have ham := ScalarEstimates.amgm_three (Complex.normSq u) (Complex.normSq v)
    (Complex.normSq w) (Complex.normSq_nonneg u) (Complex.normSq_nonneg v)
    (Complex.normSq_nonneg w)
  have hs3 : S^3 = 1 := by
    have hpow := pow_le_pow_left₀ hs0 hs1 3
    dsimp [S] at *
    nlinarith
  have hs := (pow_left_inj₀ hs0 zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (by simpa using hs3)
  have hp : 27*(Complex.normSq u*Complex.normSq v*Complex.normSq w) = S^3 := by linarith
  have heq := (ScalarEstimates.amgm_three_eq_iff (Complex.normSq u) (Complex.normSq v)
    (Complex.normSq w) (Complex.normSq_nonneg u) (Complex.normSq_nonneg v)
    (Complex.normSq_nonneg w)).mp hp
  rw [complexAlbert_inner] at hn
  have hd : d = 0 := by nlinarith 
  have he : e = 0 := by nlinarith 
  have hf : f = 0 := by nlinarith 
  refine ⟨hd,he,hf,?_,?_,?_⟩ <;> dsimp [S] at hs <;> linarith 

theorem fe_encoder_atoms_diagonal (q : Fin 3 → Albert) (hq : Frame q)
    (h0 : (encoder q).d0=0) (h1 : (encoder q).d1=0) (h2 : (encoder q).d2=0)
    (hs0 : (jordan (encoder q) (encoder q)).d0=2/3)
    (hs1 : (jordan (encoder q) (encoder q)).d1=2/3)
    (hs2 : (jordan (encoder q) (encoder q)).d2=2/3) :
    ∀ j, (q j).d0=1/3 ∧ (q j).d1=1/3 ∧ (q j).d2=1/3 := by
  intro j
  fin_cases j <;> simp [Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, ← frame_projector_first q hq,
    ← frame_projector_middle q hq, ← frame_projector_last q hq] <;> norm_num [h0,h1,h2,hs0,hs1,hs2]

theorem fe_diagonal_overlap (p x : Albert) (hp : IsDiagonal p)
    (ht : trace p = 1) (hx : x.d0=1/3 ∧ x.d1=1/3 ∧ x.d2=1/3) : inner p x = 1/3 := by
  rw [inner_coordinates]
  simp [hp.1,hp.2.1,hp.2.2,hx.1,hx.2.1,hx.2.2,octDot_coordinates]
  change p.d0+p.d1+p.d2 = 1 at ht
  linarith

theorem fe_square_projection_from_gram (z : Albert)
    (hz : complexProjection z=0) (hS : sectorFrobeniusSq (hiddenMatrix z)=1)
    (hG : sectorColumnGram (hiddenMatrix z) = Matrix.diagonal (fun _ => (1/3 : ℂ))) :
    complexProjection (jordan z z) = (2/3 : ℝ) • (1 : Albert) := by
  have hh := complex_hidden_decomposition z
  rw [hz,zero_add] at hh
  rw [← hh,hidden_square_complexProjection,hS,hG]
  ext <;> norm_num [complexAlbert,complexOct]

theorem fe_hidden_saturation (z : Albert) (hn : inner z z = 2)
    (ht : (hiddenMatrix z).det.im^2 = 1/27) :
    complexProjection z=0 ∧ complexProjection (jordan z z)=(2/3 : ℝ) • (1 : Albert) := by
  let M := hiddenMatrix z
  let S := sectorFrobeniusSq M
  have hs0 : 0 ≤ S := by
    dsimp [S,sectorFrobeniusSq]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Complex.normSq_nonneg _
  have hs1 : S ≤ 1 := by have h := hidden_energy_le z; rw [hn] at h; linarith
  have hd := MatrixDetEstimate.normSq_det_le M
  have hi := MatrixDetEstimate.im_det_sq_le_normSq M
  rw [← sectorFrobeniusSq_eq] at hd
  have hs3 : S^3 = 1 := by
    have hpow := pow_le_pow_left₀ hs0 hs1 3
    nlinarith
  have hs := (pow_left_inj₀ hs0 zero_le_one (by decide : (3 : ℕ) ≠ 0)).mp
    (by simpa using hs3)
  have heq : 27*Complex.normSq M.det = MatrixDetEstimate.frobeniusSq M^3 := by
    rw [← sectorFrobeniusSq_eq]
    nlinarith
  have hg := MatrixDetEstimate.normSq_det_equality_gram M heq
  rw [← sectorFrobeniusSq_eq] at hg
  have hG : sectorColumnGram M = Matrix.diagonal (fun _ => (1/3 : ℂ)) := by aesop
  have hz : complexProjection z=0 := by
    have he := inner_hidden_decomposition z
    rw [hn,show sectorFrobeniusSq (hiddenMatrix z)=1 from hs] at he
    exact (inner_self_eq_zero _).mp (by linarith)
  exact ⟨hz,fe_square_projection_from_gram z hz hs hG⟩

theorem fe_hidden_determinant_of_projections (r : Fin 3 → Albert) (hr : Frame r)
    (he : complexProjection (encoder r)=0)
    (hsq : complexProjection (jordan (encoder r) (encoder r))=
      (2/3 : ℝ) • (1 : Albert)) : (hiddenMatrix (encoder r)).det.im^2 = 1/27 := by
  let M := hiddenMatrix (encoder r)
  let G := sectorColumnGram M
  let S := sectorFrobeniusSq M
  have hrep : hiddenAlbert M=encoder r := by
    have h := complex_hidden_decomposition (encoder r)
    simpa [he,zero_add] using h
  have hS : S=1 := by
    have h := hiddenAlbert_norm M
    rw [hrep,frame_encoder_norm r hr] at h
    change 2=2*S at h
    linarith
  rw [← hrep,hidden_square_complexProjection] at hsq
  have hh : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  have hd (i : Fin 3) : G i i = 1/3 := by
    have h := congrArg Complex.im (hh.apply i i)
    simp [Complex.conj_im] at h
    apply Complex.ext
    · fin_cases i
      · have := congrArg Albert.d0 hsq; change S-(G 0 0).re=(2/3 : ℝ)*1 at this; simp; linarith
      · have := congrArg Albert.d1 hsq; change S-(G 1 1).re=(2/3 : ℝ)*1 at this; simp; linarith
      · have := congrArg Albert.d2 hsq; change S-(G 2 2).re=(2/3 : ℝ)*1 at this; simp; linarith
    · simp; linarith
  have hoff : G 0 1=0 ∧ G 0 2=0 ∧ G 1 2=0 := by
    have := congrArg (fun x => (complexPart x.o01, complexPart x.o02, complexPart x.o12)) hsq
    simpa [complexAlbert,complexOct,complexPart,unit,octScalar,Complex.ext_iff] using this
  have hG : G=Matrix.diagonal (fun _ => (1/3 : ℂ)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, hd, hoff, ← hh.apply 1 0, ← hh.apply 2 0, ← hh.apply 2 1]
  have hnorm : Complex.normSq M.det=1/27 := by
    rw [← MatrixDetEstimate.determinant_gram_real]
    change G.det.re=1/27
    rw [hG,Matrix.det_diagonal]
    norm_num 
  have hreal : M.det.re=0 := by
    have h := frame_encoder_cubicNorm r hr
    rw [← hrep,hiddenAlbert_cubicNorm] at h
    linarith
  simpa [Complex.normSq_apply,hreal,pow_two] using hnorm

theorem fe_uniform_complex_triangle (p q r : Fin 3 → Albert)
    (hp : Frame p) (hq : Frame q) (hr : Frame r) (hu : UniformLedger p q r)
    (hpd : ∀ i, IsDiagonal (p i)) (hqc : InComplexSector (encoder q)) :
    (complexPart (encoder q).o01*complexPart (encoder q).o12*
      star (complexPart (encoder q).o02)).im^2=1/27 := by
  let y := encoder q
  let u := complexPart y.o01
  let v := complexPart y.o02
  let w := complexPart y.o12
  have hqd (j : Fin 3) : (q j).d0=1/3 ∧ (q j).d1=1/3 ∧ (q j).d2=1/3 :=
    diagonal_frame_uniform_coordinates p hp hpd (q j)
      (fun i => uniformLedger_pair_overlap p q r hr hu i j)
  obtain ⟨h0, h1, h2, hs0, hs1, hs2⟩ : y.d0=0 ∧ y.d1=0 ∧ y.d2=0 ∧ (jordan y y).d0=2/3 ∧
      (jordan y y).d1=2/3 ∧ (jordan y y).d2=2/3 := by
    simp [y, frame_encoder_square q hq]
    norm_num [encoder, hqd]
  have hy : complexAlbert y.d0 y.d1 y.d2 u v w=y := complexProjection_eq_self y hqc
  have hsum0 := fe_complex_square_d0 y.d0 y.d1 y.d2 u v w
  have hsum1 := fe_complex_square_d1 y.d0 y.d1 y.d2 u v w
  have hsum2 := fe_complex_square_d2 y.d0 y.d1 y.d2 u v w
  rw [hy] at hsum0 hsum1 hsum2
  have huN : Complex.normSq u=1/3 := by nlinarith
  have hvN : Complex.normSq v=1/3 := by nlinarith
  have hwN : Complex.normSq w=1/3 := by nlinarith
  have hreal : (u*w*star v).re=0 := by
    have h := frame_encoder_cubicNorm q hq
    change newtonCubicNorm y=0 at h
    rw [← hy,fe_complex_cubic,h0,h1,h2] at h
    linarith
  have h := fe_triangle_norm u v w
  rw [Complex.normSq_apply,hreal,huN,hvN,hwN] at h
  nlinarith

end Glennie
