module
public import GS.Spectral.Blocks
public import GS.Topology.Regular
@[expose] public section

/-! A tuple of commuting two-by-two Hermitians consists of scalar centres
and collinear traceless parts. The spectral theorem supplies the common basis
also in the converse direction (diagonalize just *one* traceless matrix). -/
noncomputable section
open Matrix GS.Isometric
open scoped ComplexOrder
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace GS.Spectral
variable {𝕜 : Type*} [RCLike 𝕜] {r d : ℕ}
abbrev V (d : ℕ) := Fin d → ℝ
abbrev Cone (r d : ℕ) := RankLocus.Locus r (Fin d)
abbrev Target (r d : ℕ) := V d × Cone r d
def vertex : Target r d := (0,RankLocus.tip)

def axis (p : ℝ × 𝕜) : Square 𝕜 2 := !![(p.1:𝕜), star p.2; p.2, -(p.1:𝕜)]
def readAxis (H : Square 𝕜 2) : ℝ × 𝕜 := (RCLike.re (H 0 0), H 1 0)
lemma read_axis (u : ℝ × 𝕜) : readAxis (axis u) = u := by simp [readAxis,axis]
lemma axis_hermitian (u : ℝ × 𝕜) : (axis u).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [axis,conjTranspose_apply,RCLike.star_def]
lemma axis_trace (u : ℝ × 𝕜) : (axis u).trace = 0 := by simp [axis,trace,Fin.sum_univ_two]
lemma axis_read {H : Square 𝕜 2} (h : H.IsHermitian) (t : H.trace = 0) : axis (readAxis H) = H := by
  have h₀ := RCLike.conj_eq_iff_re.mp (h.apply 0 0)
  have h₁ := h.apply 0 1
  simp [trace,Fin.sum_univ_two,add_eq_zero_iff_neg_eq] at t
  ext i j; fin_cases i <;> fin_cases j <;> simp_all [axis,readAxis,RCLike.star_def]
lemma axis_smul (a : ℝ) (p : ℝ × 𝕜) : axis (a • p) = a • axis p := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [axis,RCLike.real_smul_eq_coe_mul,RCLike.star_def]
@[fun_prop] lemma continuous_axis : Continuous (@axis 𝕜 _) := by
  apply continuous_pi; intro i; apply continuous_pi; intro j; fin_cases i <;> fin_cases j <;> simp only [axis,of_apply,cons_val_zero,cons_val_one,head_cons] <;> first | fun_prop | exact RCLike.continuous_conj.comp continuous_snd

variable (e : (ℝ × 𝕜) ≃L[ℝ] V r)
def realize (p : Target r d) (j : Fin d) : Square 𝕜 2 := p.1 j • 1 + axis (e.symm (p.2.val.col j))
lemma realize_inj : Function.Injective (@realize 𝕜 _ r d e) := by
  intro p p' h
  have he (j : Fin d) := congrFun h j
  have hc : p.1 = p'.1 := by
    funext j; have ht := congrArg (RCLike.re ∘ trace) (he j)
    simp [realize,trace_smul,axis_trace,Function.comp_def,RCLike.real_smul_eq_coe_mul,RCLike.mul_re] at ht; linarith
  refine Prod.ext hc (Subtype.ext ?_)
  ext i j; have H := he j
  simp only [realize,hc,add_right_inj] at H
  exact congrFun (e.symm.injective (by simpa [read_axis] using congrArg readAxis H)) i

def signPair := ![(1:ℝ),-1]
def J (s : U 𝕜 2) := mix s (fun k => (signPair k : 𝕜))
lemma J_read (s : U 𝕜 2) : axis (readAxis (J s)) = J s := by
  apply axis_read
  · apply Matrix.isHermitian_conjTranspose_mul_mul
    rw [IsHermitian,diagonal_conjTranspose]; congr 1; ext k; simp [RCLike.star_def]
  · simp [J,signPair,mix,trace_mul_cycle,trace_diagonal,Fin.sum_univ_two]

def center (a : Fin 2 → V d) (j) := (a 0 j + a 1 j)/2
def delta (a : Fin 2 → V d) (j) := (a 0 j - a 1 j)/2
def spectrum (s : U 𝕜 2) (a : Fin 2 → V d) : Target r d :=
  (center a,RankLocus.outer (e (readAxis (J s))) (delta a))
lemma mix_add_scalar (s : U 𝕜 2) (a b : ℝ) (v : Fin 2 → ℝ) :
    mix s (fun k => ((a + b * v k : ℝ):𝕜)) = a • 1 + b • mix s (fun k => (v k : 𝕜)) := by
  have h : diagonal (fun k => ((a + b*v k : ℝ):𝕜)) = a • (1 : Square 𝕜 2) + b • diagonal (fun k => (v k:𝕜)) := by
    ext i j; by_cases eq : i=j <;> simp [diagonal_apply,one_apply,eq,RCLike.real_smul_eq_coe_mul]
  unfold mix; rw [h]; simp [mul_add,add_mul,mul_assoc]

lemma realize_spectrum (s : U 𝕜 2) (a : Fin 2 → V d) (j) :
    realize e (spectrum e s a) j = mix s (fun k => (a k j : 𝕜)) := by
  have h (j) : (spectrum e s a).2.val.col j = delta a j • e (readAxis (J s)) := by ext; apply mul_comm
  simp only [realize,h,map_smul,ContinuousLinearEquiv.symm_apply_apply,axis_smul,J_read]
  rw [J,← mix_add_scalar]; apply congrArg (mix s); funext k; apply congrArg RCLike.ofReal; fin_cases k <;> simp [spectrum,center,delta,signPair] <;> ring

lemma spectrum_onto (p : Target r d) : ∃ s a, spectrum e s a = p := by
  obtain ⟨a,b,h⟩ := RankLocus.factors p.2
  let u := e.symm a; have hu := axis_hermitian u
  let s := hu.eigenvectorUnitary⁻¹
  have hs : axis u = mix s (fun k => (hu.eigenvalues k : 𝕜)) := by
    change _ = (hu.eigenvectorUnitary.valᴴ)ᴴ * _ * _
    rw [conjTranspose_conjTranspose]; exact hu.spectral_theorem
  refine ⟨s,(fun k j => p.1 j + b j * hu.eigenvalues k),realize_inj e ?_⟩
  funext j
  have hv : p.2.val.col j = b j • a := by rw [← h]; ext; apply mul_comm
  rw [realize_spectrum,mix_add_scalar,realize,hv,map_smul,axis_smul,← hs]

/-- Continuous candidate for the eigenvalues in *any* frame, exact on the
represented tuple. This avoids a choice of continuous eigenvectors. -/
def recover (s : U 𝕜 2) (p : Target r d) (k : Fin 2) (j : Fin d) := RCLike.re ((s.val * realize e p j * s.valᴴ) k k)
lemma recover_spec (s : U 𝕜 2) (a : Fin 2 → V d) : recover e s (spectrum e s a) = a := by
  funext k j; simp [recover,realize_spectrum,mix,mul_assoc]
lemma recover_vertex (s : U 𝕜 2) : recover e s (vertex : Target r d) = 0 := by
  funext k j; change RCLike.re ((s.val * ((0:ℝ) • 1 + axis (e.symm 0)) * s.valᴴ) k k) = 0
  have h : axis (0 : ℝ × 𝕜) = 0 := by ext i j; fin_cases i <;> fin_cases j <;> simp [axis]
  simp [h]
@[fun_prop] lemma continuous_spectrum : Continuous (fun p : U 𝕜 2 × (Fin 2 → V d) => spectrum e p.1 p.2) := by
  apply Continuous.prodMk _ (Continuous.subtype_mk _ _)
  · unfold center; fun_prop
  · apply continuous_pi; intro i; apply continuous_pi; intro j
    have h : Continuous (J (𝕜 := 𝕜)) := by unfold J mix; fun_prop
    unfold readAxis delta; fun_prop
@[fun_prop] lemma continuous_recover : Continuous (fun p : U 𝕜 2 × Target r d => recover e p.1 p.2) := by
  unfold recover realize Matrix.col; fun_prop
end GS.Spectral
