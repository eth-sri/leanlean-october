module
public import Glennie.Compact.NearbyOrbits
public import Glennie.Native.OrderedPositivePair
public import Glennie.UnitShifts
public import Glennie.Theorems.CubicNorm

/-! Ordered pair normal form and the signed orbit test. Normalize the second
encoder with two nonnegative real slots and a third slot in the closed upper
half plane. In this gauge the first pair is uniquely determined by its ledger. -/
@[expose] public section
namespace Glennie.Compact.PairNormNearby
open FlatBase Affine20 FlatOrbit Sections NearbyOrbits NativeOrderedPositivePair
noncomputable section
set_option maxHeartbeats 2000000

private def diag (x : Albert) := (x.d0,x.d1,x.d2)
private def flatAtom : Fin 3 → Albert := ![diagonalAlbert 0 0 1, diagonalAlbert 0 1 0, diagonalAlbert 1 0 0]
private theorem flat_atoms : flatFrameP = flatAtom := by
  have e := jordan_diagonalAlbert 1 0 (-1) 1 0 (-1)
  change jordan flatXN flatXN = _ at e
  funext i; fin_cases i <;> apply Albert.ext <;> simp only [flatFrameP,projectorFrame,e] <;> norm_num [flatAtom,flatXN,diagonalAlbert]
private theorem diagonal_read {x y : Albert} (h : ∀ i, inner (flatFrameP i) x = inner (flatFrameP i) y) : diag x = diag y := by
  have a := h 0; have b := h 1; have c := h 2
  simpa [flat_atoms,flatAtom,inner_coordinates,diagonalAlbert,octDot_coordinates,diag] using And.intro c (And.intro b a)

private structure Normal where
  d : ℝ
  e : ℝ
  f : ℝ
  a : ℝ
  b : ℝ
  r : ℝ
  s : ℝ
private def Normal.y (m : Normal) := complexAlbert m.d m.e m.f m.a ⟨m.r,m.s⟩ m.b
private def Normal.weight (m : Normal) := 4*m.a*m.b*m.s
private theorem Normal.square (m : Normal) : jordan m.y m.y =
    complexAlbert (m.d^2+m.a^2+(m.r^2+m.s^2)) (m.e^2+m.a^2+m.b^2) (m.f^2+(m.r^2+m.s^2)+m.b^2)
      ⟨m.a*(m.d+m.e)+m.r*m.b,m.s*m.b⟩ ⟨m.r*(m.d+m.f)+m.a*m.b,m.s*(m.d+m.f)⟩
      ⟨m.b*(m.e+m.f)+m.a*m.r,m.a*m.s⟩ := by
  ext <;> simp [y,complexAlbert,complexOct,jordan_d0,jordan_d1,jordan_d2,jordan_o01,jordan_o02,jordan_o12,
    octNormSq,Quaternion.normSq_def',octMul,octConj,Quaternion.re_mul,Quaternion.imI_mul,
    Quaternion.imJ_mul,Quaternion.imK_mul,smul_eq_mul] <;> ring
private theorem Normal.cubic (m : Normal) : newtonCubicNorm m.y =
    m.d*m.e*m.f - m.d*m.b^2 - m.e*(m.r^2+m.s^2) - m.f*m.a^2 + 2*m.a*m.b*m.r := by
  simp [newtonCubicNorm_coordinates,y,complexAlbert,complexOct,octNormSq,Quaternion.normSq_def',
    octMul,octRe,octConj,Quaternion.re_mul,Quaternion.imI_mul]; ring
private theorem Normal.sec (m : Normal) : InComplexSector m.y := by
  exact ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩⟩
private theorem Normal.phi_eq (m : Normal) (z : Albert) : phi flatXN m.y z = m.weight * (hiddenMatrix z).det.im := by
  rw [phi_of_diagonal_complex _ _ _ ⟨rfl,rfl,rfl⟩ m.sec]
  simp [flatXN,y,weight,complexPart,complexAlbert,complexOct,Complex.mul_re,Complex.mul_im]; ring

private structure PairForm (T : Triple) where
  m : Normal
  ha : 0 ≤ m.a
  hb : 0 ≤ m.b
  hs : 0 ≤ m.s
  first : T 0 = flatFrameP
  second : encoder (T 1) = m.y
private theorem normalize (T : Triple) (h : Frame (T 0)) : ∃ g : CompactAutomorphism, Nonempty (PairForm (mapAtoms g T)) := by
  obtain ⟨g,a,b,ha,hb,hp,h1,h2,h3,h4⟩ := native_ordered_positive_pair _ h (encoder (T 1))
  let y := g.equiv (encoder (T 1)); let v := complexPart y.o02
  refine ⟨g,⟨⟨⟨y.d0,y.d1,y.d2,a,b,v.re,v.im⟩,ha,hb,h4,funext hp,?_⟩⟩⟩
  rw [show encoder (mapAtoms g T 1) = y from g.encoder_map _]
  change y = complexAlbert _ _ _ _ v _
  simpa only [show complexPart y.o01 = (a:ℂ) from congrArg complexPart h1,
    show complexPart y.o12 = (b:ℂ) from congrArg complexPart h2] using (complexAlbert_eq y h3).symm
private theorem PairForm.phi_eq {T : Triple} (n : PairForm T) : phiOf T = n.m.weight * (hiddenMatrix (encoder (T 2))).det.im := by
  rw [phiOf_apply,n.first,flatFrameP_encoder,n.second,n.m.phi_eq]

private theorem normal_unique (m n : Normal) (ha : 0 ≤ m.a) (hb : 0 ≤ m.b) (hs : 0 ≤ m.s)
    (ha' : 0 ≤ n.a) (hb' : 0 ≤ n.b) (hs' : 0 ≤ n.s) (hw : m.weight ≠ 0)
    (hd : diag m.y = diag n.y) (hq : diag (jordan m.y m.y) = diag (jordan n.y n.y))
    (hc : newtonCubicNorm m.y = newtonCubicNorm n.y) : m = n := by
  rw [m.square,n.square] at hq; rw [m.cubic,n.cubic] at hc
  simp only [diag,Normal.y,complexAlbert,Prod.mk.injEq] at hd hq
  have a : m.a^2 = n.a^2 := by grind
  have b : m.b^2 = n.b^2 := by grind
  have r : m.r^2 + m.s^2 = n.r^2 + n.s^2 := by grind
  have A := (sq_eq_sq₀ ha ha').mp a; have B := (sq_eq_sq₀ hb hb').mp b
  rw [A,B,r,hd.1,hd.2.1,hd.2.2] at hc
  have re : m.r = n.r := by unfold Normal.weight at hw; grind
  have im : m.s = n.s := (sq_eq_sq₀ hs hs').mp (by grind)
  cases m; cases n; congr <;> tauto
private theorem align {T S : Triple} (n : PairForm T) (m : PairForm S) (ht : Frame (T 1))
    (hs : Frame (S 1)) (hL : fullLedger T = fullLedger S) (hne : phiOf T ≠ 0) : S 0 = T 0 ∧ S 1 = T 1 := by
  have P (i j : Fin 3) := congrArg (fun L : Ledger54 => L.2.1 i j) hL
  change ∀ i j, inner (T 0 i) (T 1 j) = inner (S 0 i) (S 1 j) at P
  rw [m.first,n.first] at P
  have h : n.m = m.m := by
    apply normal_unique _ _ n.ha n.hb n.hs m.ha m.hb m.hs (left_ne_zero_of_mul (n.phi_eq ▸ hne))
    all_goals rw [← n.second,← m.second]
    · apply diagonal_read; simp [encoder,inner_sub_right,P]
    · apply diagonal_read; simp [frame_encoder_square _ ht,frame_encoder_square _ hs,inner_add_right,P]
    · rw [frame_encoder_cubicNorm _ ht,frame_encoder_cubicNorm _ hs]
  exact ⟨m.first.trans n.first.symm,frames_eq hs ht (by rw [m.second,n.second,h])⟩

private theorem slots {z E : Albert} (hE : diag E = diag 0) (h : ∀ i, inner (jordan (flatFrameP i) z) E = 0) :
    octDot z.o01 E.o01 = 0 ∧ octDot z.o02 E.o02 = 0 ∧ octDot z.o12 E.o12 = 0 := by
  simp [diag] at hE
  have read (d e f : ℝ) : inner (jordan (diagonalAlbert d e f) z) E =
      (d+e)*octDot z.o01 E.o01 + (d+f)*octDot z.o02 E.o02 + (e+f)*octDot z.o12 E.o12 := by
    simp [inner_coordinates,hE.1,hE.2.1,hE.2.2,jordan_o01,jordan_o02,jordan_o12,diagonalAlbert,octMul,octConj,show ((0:Quaternion ℝ), (0:Quaternion ℝ)) = (0:Octonion) from rfl,octDot_smul_left]; ring
  have a := h 0; have b := h 1; have c := h 2
  simp [flat_atoms,flatAtom,read] at a b c
  grind
private theorem slot_injective (u v : ℂ) (x : Octonion) (h : octDot (complexOct u) x = 0)
    (k : octDot (complexOct v) x = 0) (d : u.re*v.im-u.im*v.re ≠ 0) : complexPart x = 0 := by
  simp [complexOct,octDot_coordinates] at h k
  apply Complex.ext <;> simp [complexPart] <;> grind
private theorem recover_slots (m : Normal) {E : Albert} (hd : diag E = diag 0)
    (w : m.weight ≠ 0) (p : ∀ i, inner (jordan (flatFrameP i) m.y) E = 0)
    (q : ∀ i, inner (jordan (flatFrameP i) (jordan m.y m.y)) E = 0) : complexCoordinatesLinear E = 0 := by
  obtain ⟨a,b,c⟩ := slots hd p; obtain ⟨a',b',c'⟩ := slots hd q
  rw [m.square] at a' b' c'
  have A := slot_injective _ _ _ a a' (by change m.a*(m.s*m.b)-0*_ ≠ 0; unfold Normal.weight at w; grind)
  have B := slot_injective _ _ _ b b' (by change m.r*(m.s*_) - m.s*(m.r*_+m.a*m.b) ≠ 0; unfold Normal.weight at w; grind)
  have C := slot_injective _ _ _ c c' (by change m.b*(m.a*m.s)-0*_ ≠ 0; unfold Normal.weight at w; grind)
  exact Prod.ext hd (Prod.ext A (Prod.ext B C))

private theorem recover_atom {T S : Triple} (n : PairForm T) (ht : Frame (T 1))
    (hp : S 0 = T 0) (hq : S 1 = T 1) (hL : fullLedger S = fullLedger T)
    (hne : phiOf T ≠ 0) (k : Fin 3) : complexCoordinatesLinear (S 2 k) = complexCoordinatesLinear (T 2 k) := by
  let E := S 2 k - T 2 k
  have diag (i : Fin 3) : inner (flatFrameP i) E = 0 := by
    have e := congrArg (fun L : Ledger54 => L.2.2.2 k i) hL
    rw [ledger54_R, hp, ledger54_R, n.first] at e
    rw [show E = _ from rfl, inner_sub_right, inner_comm, inner_comm (flatFrameP i), e, sub_self]
  have mixed (i j : Fin 3) : inner (jordan (flatFrameP i) (T 1 j)) E = 0 := by
    have e := congrArg (fun L : Ledger54 => L.1 i j k) hL
    change inner (jordan (S 0 i) (S 1 j)) (S 2 k) = inner (jordan (T 0 i) (T 1 j)) (T 2 k) at e
    rw [hp,hq,n.first] at e
    simp [E,inner_sub_right,e]
  apply sub_eq_zero.mp; rw [← map_sub]
  apply recover_slots n.m (E := E)
  · apply diagonal_read; simpa [inner_zero_right] using diag
  · exact left_ne_zero_of_mul (n.phi_eq ▸ hne)
  · rw [←n.second]; simp [encoder, jordan_sub_right, inner_sub_left, mixed]
  · rw [←n.second,frame_encoder_square _ ht]; simp [jordan_add_right, inner_add_left, mixed]

/-- For the complex component K and hidden matrix M the square reads
K² − G + Re(tr G) I, where G=M†M. Its trace determines Re(tr G). -/
private abbrev K := sectorComplexMatrix
private abbrev G (x : Albert) := sectorColumnGram (hiddenMatrix x)
private theorem gram_eq {z w : Albert} (k : K z = K w) (l : K (jordan z z) = K (jordan w w)) : G z = G w := by
  have sq (x) : K (jordan x x) = K x * K x + (-G x + ((G x).trace.re : ℂ) • 1) := by
    change sectorComplexMatrix (jordan x x) = _
    rw [sectorComplexMatrix_jordan]; unfold sectorProductComplex; dsimp [K,G,sectorColumnGram]; module
  rw [sq,sq,k] at l
  have e := add_left_cancel l
  have t := congrArg (fun M : SectorMatrix => M.trace.re) e
  simp [Matrix.trace_add,Matrix.trace_neg,Matrix.trace_smul] at t
  have tr : (G z).trace.re = (G w).trace.re := by linarith
  rw [tr] at e
  exact neg_injective (add_right_cancel e)

/-- In the column gauge the compact cubic norm records the remaining real
part of the determinant after the visible matrix and column Gram are known. -/
private theorem sector_cubic (z : Albert) : newtonCubicNorm z = (K z).det.re -
    ((K z * G z).trace).re + 2 * (hiddenMatrix z).det.re := by
  simp [newtonCubicNorm_coordinates,K,G,sectorColumnGram,sectorComplexMatrix,
    complexHermitianMatrix,complexCoordinatesLinear,complexPart,hiddenMatrix,hiddenColumn,
    octNormSq,Quaternion.normSq_def',octRe,octMul,octConj,Quaternion.re_mul,
    Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,Matrix.trace,Matrix.diag,
    Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.det_fin_three,Fin.sum_univ_three,
    Complex.mul_re,Complex.mul_im]; ring

private theorem transport (M N : SectorMatrix) (hg : sectorColumnGram M = sectorColumnGram N)
    (hu : IsUnit M.det) (hd : N.det = M.det) :
    ∃ s : SectorUnitary, (s : SectorMatrix).det = 1 ∧ (s : SectorMatrix) * M = N := by
  have e := Matrix.mul_nonsing_inv M hu
  have u : (N*M⁻¹).conjTranspose * (N*M⁻¹) = 1 := calc
    _ = M⁻¹.conjTranspose * (N.conjTranspose*N) * M⁻¹ := by simp [Matrix.mul_assoc]
    _ = (M*M⁻¹).conjTranspose * (M*M⁻¹) := by rw [← show M.conjTranspose*M = N.conjTranspose*N from hg]; simp [Matrix.mul_assoc]
    _ = 1 := by rw [e]; simp
  refine ⟨⟨N*M⁻¹,Matrix.mem_unitaryGroup_iff'.mpr u⟩,?_,?_⟩
  · change (N*M⁻¹).det=1; simp [hd,hu.ne_zero]
  · change N*M⁻¹*M=N; rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul _ hu,Matrix.mul_one]

private theorem aligned_core {T S : Triple} (n : PairForm T) (fT : ∀ a, Frame (T a)) (fS : ∀ a, Frame (S a))
    (hp : S 0 = T 0) (hq : S 1 = T 1) (hL : fullLedger S = fullLedger T) (hne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧ (phiOf T = phiOf S → S ∈ autOrbit T) := by
  let z := encoder (T 2); let w := encoder (S 2); let M := hiddenMatrix z; let N := hiddenMatrix w
  have v : phiOf T = n.m.weight*M.det.im := n.phi_eq
  have v' : phiOf S = n.m.weight*N.det.im := by rw [phiOf_apply,hp,hq,n.first,n.second,flatFrameP_encoder,n.m.phi_eq]
  have ha := recover_atom n (fT 1) hp hq hL hne
  have cz : K w = K z := congrArg complexHermitianMatrix (by simp [w,z,encoder,map_sub,ha])
  have zz : K (jordan w w) = K (jordan z z) := congrArg complexHermitianMatrix (by
    simp [z,w,frame_encoder_square _ (fS 2),frame_encoder_square _ (fT 2),ha])
  have gram := gram_eq cz zz
  have re : N.det.re = M.det.re := by
    have h : newtonCubicNorm w = newtonCubicNorm z := (frame_encoder_cubicNorm _ (fS 2)).trans (frame_encoder_cubicNorm _ (fT 2)).symm
    rw [sector_cubic,sector_cubic,cz,gram] at h; dsimp [M,N]; linarith
  have norm (m : SectorMatrix) : Complex.normSq m.det = (sectorColumnGram m).det.re := by unfold sectorColumnGram; aesop
  have ns : Complex.normSq N.det = Complex.normSq M.det := (norm N).trans ((congrArg (fun G : SectorMatrix => G.det.re) gram).trans (norm M).symm)
  have im : N.det.im^2 = M.det.im^2 := by grind [Complex.normSq_apply]
  refine ⟨by rw [v,v',mul_pow,mul_pow,im],fun h => ?_⟩
  have nz : n.m.weight*M.det.im ≠ 0 := v ▸ hne
  have ie := mul_left_cancel₀ (left_ne_zero_of_mul nz) (v.symm.trans (h.trans v'))
  have unit : IsUnit M.det := isUnit_iff_ne_zero.mpr (by intro he; simp [he] at nz)
  obtain ⟨s,hs,hm⟩ := transport M N gram.symm unit (Complex.ext re ie.symm)
  let g := sectorLeftSU3Automorphism s hs
  have hv : g.equiv z = w := by
    change sectorDecode (K z) ((s:SectorMatrix)*M) = w
    rw [hm,←cz]; exact sectorDecode_encode _
  refine ⟨g,?_⟩; funext a
  apply frames_eq (g.map_frame _ (fT a)) (fS a)
  change encoder (fun i => g.equiv (T a i)) = _
  rw [g.encoder_map]; fin_cases a
  · change g.equiv (encoder (T 0)) = encoder (S 0); rw [hp,n.first,flatFrameP_encoder]; exact sectorLeftSU3_fixes_complex _ _ _ (diagonal_inComplex _ ⟨rfl,rfl,rfl⟩)
  · change g.equiv (encoder (T 1)) = encoder (S 1); rw [hq,n.second]; exact sectorLeftSU3_fixes_complex _ _ _ n.m.sec
  · exact hv

 theorem core (T S : Triple) (ht : ∀ a, Frame (T a)) (hs : ∀ a, Frame (S a))
    (hL : fullLedger T = fullLedger S) (hne : phiOf T ≠ 0) :
    phiOf T ^ 2 = phiOf S ^ 2 ∧ (phiOf T = phiOf S → T ∈ autOrbit S) := by
  obtain ⟨g,⟨n⟩⟩ := normalize T (ht 0); obtain ⟨k,⟨m⟩⟩ := normalize S (hs 0)
  have ne := (phiOf_mapAtoms g T).trans_ne hne
  have eqL := (ledger54_map g T).trans (hL.trans (ledger54_map k S).symm)
  obtain ⟨hp,hq⟩ := align n m (g.map_frame _ (ht 1)) (k.map_frame _ (hs 1)) eqL ne
  obtain ⟨sq,rel⟩ := aligned_core n (frame_mapAtoms _ _ ht) (frame_mapAtoms _ _ hs) hp hq eqL.symm ne
  simp only [phiOf_mapAtoms] at sq rel
  refine ⟨sq,fun e => ?_⟩
  obtain ⟨u,hu⟩ := rel e
  exact ⟨(u.comp g).symm.comp k,by rw [← mapAtoms_comp,← hu,mapAtoms_comp u g,mapAtoms_symm_mapAtoms]⟩
theorem rigid {T S : Triple} (ht : ∀ a, Frame (T a)) (hs : ∀ a, Frame (S a)) (hL : fullLedger T = fullLedger S)
    (h : (phiOf T < 0 ∧ phiOf S < 0) ∨ (0 < phiOf T ∧ 0 < phiOf S)) : T ∈ autOrbit S := by
  obtain ⟨sq,rel⟩ := core T S ht hs hL (h.elim (fun e => e.1.ne) (fun e => e.1.ne'))
  apply rel; rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with eq | eq
  · exact eq
  · rcases h with ⟨_,_⟩ | ⟨_,_⟩ <;> linarith
end
end Glennie.Compact.PairNormNearby
