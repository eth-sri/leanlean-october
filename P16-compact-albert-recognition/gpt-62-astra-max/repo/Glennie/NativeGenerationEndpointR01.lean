module
public import Glennie.UnitShifts
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! After pair reduction, two entries of the second generator are real. Their
nonvanishing identifies the three Peirce slots of a closed subspace with one
real subspace of octonions. It is closed under octonion multiplication, and
the third entry gives it a complex structure. The hidden determinant now has
its literal meaning: three columns span the complementary complex three-space. -/
@[expose] public section
namespace Glennie.NativeGenerationEndpointR01
noncomputable section
set_option maxHeartbeats 1500000

private def e : Fin 3 → Albert := ![diagonalAlbert 1 0 0,diagonalAlbert 0 1 0,diagonalAlbert 0 0 1]
private def slot (i : Fin 3) : Octonion →ₗ[ℝ] Albert where
  toFun q := ![⟨0,0,0,q,0,0⟩,⟨0,0,0,0,q,0⟩,⟨0,0,0,0,0,q⟩] i
  map_add' p q := by fin_cases i <;> ext <;> simp
  map_smul' t q := by fin_cases i <;> ext <;> simp
private def entry (x : Albert) : Fin 3 → Octonion := ![x.o01,x.o02,x.o12]

local macro "peirce" : tactic => `(tactic| ext <;> simp [slot,e,entry,diagonalAlbert,unit,
  jordan_d0,jordan_d1,jordan_d2,jordan_o01,jordan_o02,jordan_o12,
  octDot_coordinates,octMul,octConj,Quaternion.re_mul,Quaternion.imI_mul,
  Quaternion.imJ_mul,Quaternion.imK_mul,octNormSq,Quaternion.normSq_def',smul_eq_mul] <;> ring)

variable (K : Submodule ℝ Albert) (h1 : (1:Albert) ∈ K) (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
include h1 hJ in
private theorem spectral (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (i : Fin 3) : e i ∈ K := by
  let d := ![a,b,c]; let x := diagonalAlbert a b c
  have eq : ((d i-d (i+1)) * (d i-d (i+2))) • e i =
      jordan x x - (d (i+1) + d (i+2)) • x + (d (i+1)*d (i+2)) • (1:Albert) := by
    fin_cases i <;> dsimp [d,x] <;> peirce
  have h : (d i-d (i+1)) * (d i-d (i+2)) ≠ 0 := by fin_cases i <;> simp [d, sub_ne_zero.mpr hab, sub_ne_zero.mpr hac, sub_ne_zero.mpr hbc, sub_ne_zero.mpr hab.symm, sub_ne_zero.mpr hac.symm, sub_ne_zero.mpr hbc.symm]
  exact (K.smul_mem_iff h).mp (eq ▸ K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx)) (K.smul_mem _ h1))

include hJ in
private theorem extract (he : ∀ i, e i ∈ K) (x : Albert) (hx : x ∈ K) (i : Fin 3) : slot i (entry x i) ∈ K := by
  let a : Fin 3 := ![0,0,1] i; let b : Fin 3 := ![1,2,2] i
  have eq : slot i (entry x i) = (4:ℝ) • jordan (e a) (jordan (e b) x) := by
    fin_cases i <;> dsimp [a,b] <;> peirce
  exact eq ▸ K.smul_mem _ (hJ _ (he _) _ (hJ _ (he _) _ hx))

private theorem cross (q r : Octonion) :
    (2:ℝ) • jordan (slot 0 q) (slot 2 r) = slot 1 (octMul q r) ∧
    (2:ℝ) • jordan (slot 1 q) (slot 2 r) = slot 0 (octMul q (octConj r)) ∧
    (2:ℝ) • jordan (slot 0 q) (slot 1 r) = slot 2 (octMul (octConj q) r) := by
  refine ⟨?_,?_,?_⟩ <;> peirce

theorem hiddenOct_mulVec_real (M : Matrix (Fin 3) (Fin 3) ℂ)
    (c : Fin 3 → ℂ) :
    hiddenOct (M.mulVec c) =
      ∑ j : Fin 3,
        ((c j).re • hiddenOct (fun i => M i j) +
          (c j).im • octMul (complexOct Complex.I) (hiddenOct (fun i => M i j))) := by
  apply Prod.ext <;> apply Quaternion.ext <;>
    simp [hiddenOct, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      complexOct, octMul, Quaternion.re_mul, Quaternion.imI_mul,
      Quaternion.imJ_mul, Quaternion.imK_mul,
      Complex.mul_re, Complex.mul_im, smul_eq_mul]
  all_goals ring


private theorem oct_split (c : ℂ) : complexOct c = c.re • octScalar 1 + c.im • complexOct Complex.I := by
  ext <;> simp [complexOct,octScalar,smul_eq_mul]

include h1 hJ in
private theorem reduced {x y z : Albert} (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (xd : IsDiagonal x) (yc : InComplexSector y) {a b : ℝ} (ay : y.o01 = octScalar a) (by' : y.o12 = octScalar b)
    (hn : phi x y z ≠ 0) : K = ⊤ := by
  let M := hiddenMatrix z; let v := complexPart y.o02
  have area : (complexPart y.o01 * complexPart y.o12 * star v).im = - (a*b*v.im) := by
    simp [ay,by',complexPart,octScalar,Complex.mul_im,Complex.mul_re]
  rw [phi_of_diagonal_complex x y z xd yc,area] at hn
  simp only [ne_eq,mul_eq_zero,not_or,neg_eq_zero,sub_eq_zero] at hn
  have he := spectral K h1 hJ x.d0 x.d1 x.d2 ((diagonalAlbert_eq x xd).symm ▸ hx)
    (by tauto) (by tauto) (Ne.symm (by tauto))
  have get := extract K hJ he
  have one0 : slot 0 (octScalar 1) ∈ K := by
    apply (K.smul_mem_iff (show a ≠ 0 by tauto)).mp
    simpa only [←map_smul,octScalar_smul,mul_one,←ay] using (show slot 0 y.o01 ∈ K from get _ hy 0)
  have one2 : slot 2 (octScalar 1) ∈ K := by
    apply (K.smul_mem_iff (show b ≠ 0 by tauto)).mp
    simpa only [←map_smul,octScalar_smul,mul_one,←by'] using (show slot 2 y.o12 ∈ K from get _ hy 2)
  let O := K.comap (slot 1)
  have mul {q r : Octonion} (hq : slot 0 q ∈ K) (hr : slot 2 r ∈ K) : octMul q r ∈ O := by
    change slot 1 _ ∈ K; rw [← (cross q r).1]; exact K.smul_mem _ (hJ _ hq _ hr)
  have r0 (q : Octonion) : slot 0 q ∈ K ↔ q ∈ O := by
    constructor
    · intro h; simpa [octMul_scalar_right] using mul h one2
    · intro h; have H := (cross q (octScalar 1)).2.1 ▸ K.smul_mem (2:ℝ) (hJ _ (show slot 1 q ∈ K from h) _ one2)
      simpa [octConj_scalar,octMul_scalar_right] using H
  have r2 (q : Octonion) : slot 2 q ∈ K ↔ q ∈ O := by
    constructor
    · intro h; simpa [octMul_scalar_left] using mul one0 h
    · intro h; have H := (cross (octScalar 1) q).2.2 ▸ K.smul_mem (2:ℝ) (hJ _ one0 _ (show slot 1 q ∈ K from h))
      simpa [octConj_scalar,octMul_scalar_left] using H
  have slots (i : Fin 3) (q : Octonion) : slot i q ∈ K ↔ q ∈ O := by
    fin_cases i <;> first | exact r0 q | rfl | exact r2 q
  have o1 := (r0 _).mp one0
  have cv : complexOct v ∈ O := by
    rw [show complexOct v = y.o02 from congrArg Albert.o02 (complexAlbert_eq y yc)]; exact get _ hy 1
  have oi : complexOct Complex.I ∈ O := by
    apply (O.smul_mem_iff (show v.im ≠ 0 by tauto)).mp
    simpa only [oct_split v,add_sub_cancel_left] using O.sub_mem cv (O.smul_mem v.re o1)
  have C (c : ℂ) : complexOct c ∈ O := oct_split c ▸ O.add_mem (O.smul_mem _ o1) (O.smul_mem _ oi)
  have hid (i : Fin 3) : hiddenOct (hiddenColumn (entry z i)) ∈ O := by
    have eq := oct_complex_hidden_decomposition (entry z i)
    rw [eq_sub_of_add_eq' eq]; exact O.sub_mem ((slots i _).mp (get _ hz i)) (C _)
  have col (j : Fin 3) : hiddenOct (fun i => M i j) ∈ O := by
    fin_cases j
    · convert O.neg_mem (hid 2) using 1 <;> ext <;> simp [M,entry,hiddenMatrix,hiddenColumn,hiddenOct]
    · exact hid 1
    · convert O.neg_mem (hid 0) using 1 <;> ext <;> simp [M,entry,hiddenMatrix,hiddenColumn,hiddenOct]
  have det : M.det ≠ 0 := fun H => (show M.det.im ≠ 0 by tauto) (by simp [H])
  have allO (q : Octonion) : q ∈ O := by
    rw [← oct_complex_hidden_decomposition q]; apply O.add_mem (C _)
    have heq : M.mulVec (M⁻¹.mulVec (hiddenColumn q)) = hiddenColumn q := by simp [det]
    rw [← heq,hiddenOct_mulVec_real]; apply O.sum_mem; intro j _
    exact O.add_mem (O.smul_mem _ (col j)) (O.smul_mem _ (mul ((r0 _).mpr oi) ((r2 _).mpr (col j))))
  apply top_unique; intro w _
  have decomp : w = w.d0 • e 0 + w.d1 • e 1 + w.d2 • e 2 + slot 0 w.o01 + slot 1 w.o02 + slot 2 w.o12 := by
    ext <;> simp [e,slot,diagonalAlbert]
  rw [decomp]; repeat first | apply K.add_mem | exact K.smul_mem _ (he _) | exact (slots _ _).mpr (allO _)

/-- Definition-free full unital generation: every native product-closed real
submodule containing the unit and a nonzero-Phi triple is the entire Albert space. -/
theorem eq_top_of_phi_ne_zero
    (K : Submodule ℝ Albert) (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (x y z : Albert) (hx : x ∈ K) (hy : y ∈ K) (hz : z ∈ K)
    (hphi : phi x y z ≠ 0) : K = ⊤ := by
  obtain ⟨d,hd⟩ := native_diagonalization x
  obtain ⟨t,a,b,_,_,hA,hB,ht,_⟩ := positive_slots (d.equiv y)
  let g := t.compactAutomorphism.comp d
  let L : Submodule ℝ Albert := K.map g.equiv.toLinearMap
  have hL1 : (1 : Albert) ∈ L := ⟨1, h1, g.map_unit⟩
  have hLJ : ∀ p ∈ L, ∀ q ∈ L, jordan p q ∈ L := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    exact ⟨jordan p q, hJ p hp q hq, g.map_jordan p q⟩
  have hL := reduced L hL1 hLJ (x := g.equiv x) (y := g.equiv y) (z := g.equiv z)
    ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ (relatedTriple_isDiagonal t _ hd) ht hA hB
    (by rw [g.phi_map]; exact hphi)
  apply top_unique
  intro t ht
  have hgt : g.equiv t ∈ L := by rw [hL]; trivial
  rcases hgt with ⟨s, hs, he⟩
  have hst := g.equiv.injective he
  exact hst ▸ hs

end
end Glennie.NativeGenerationEndpointR01
