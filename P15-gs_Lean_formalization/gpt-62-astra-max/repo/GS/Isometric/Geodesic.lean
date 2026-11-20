module
public import GS.Isometric.Geometry
public import GS.Isometric.Products
public import Mathlib.Analysis.SpecialFunctions.Exponential
@[expose] public section

/-! Differentiate a sandwich with *any* middle matrix. Velocity and
acceleration are just its successive applications with middle map
`Q ↦ C Q + Q K`, in the permuted coordinates of the right generator. -/
noncomputable section
open Matrix NormedSpace Function
open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
namespace GS.Isometric
namespace Geodesic
variable {n : ℕ}
local notation "M" => Square ℝ n
private lemma exp_factor {s : Layer ℝ n} {A : M} (h : A ∈ skewSpace s) (t : ℝ) : SharedFactor s (exp (t • A)) :=
  ⟨exp_mem (s := s.toSubalgebra) (R := ℝ) s.toSubalgebra.toSubmodule.closed_of_finiteDimensional (s.toSubalgebra.smul_mem h.1 t),
    exp_mem_unitary_of_mem_skewAdjoint ((skewSpace s).smul_mem t h).2⟩

def path (L R C Ω Q : M) (t : ℝ) := L * exp (t • C) * Q * (exp (t • Ω) * R)
lemma path_deriv (L R C Ω Q : M) (t : ℝ) : HasDerivAt (path L R C Ω Q) (path L R C Ω (C*Q+Q*Ω) t) t := by
  have h := (((hasDerivAt_exp_smul_const C t).const_mul L).mul_const Q).mul ((hasDerivAt_exp_smul_const' Ω t).mul_const R)
  change HasDerivAt (fun y => L * exp (y • C) * Q * (exp (y • Ω) * R)) _ t
  simpa [path,Pi.mul_def,add_mul,mul_add,mul_assoc] using! h

private lemma pair_comm (A B : M) : pairing A B = pairing B A := real_inner_comm ..
private lemma pa (A B C : M) : pairing (A+B) C = pairing A C + pairing B C := by simp [pairing,inner_add_left]
private lemma pb (A B C : M) : pairing A (B+C) = pairing A B + pairing A C := by simp [pairing,inner_add_right]
private lemma left_adj (A B C : M) : pairing (A*B) C = pairing B (Aᵀ*C) := by simp only [pairing_trace,transpose_mul,mul_assoc,conjTranspose_eq_transpose_of_trivial]
private lemma right_adj (A B C : M) : pairing (A*B) C = pairing A (C*Bᵀ) := by
  simp only [pairing_trace,transpose_mul,conjTranspose_eq_transpose_of_trivial,mul_assoc]; rw [trace_mul_comm,mul_assoc]
private lemma sym_skew {A B : M} (ha : Aᵀ=A) (hb : Bᵀ=-B) : pairing A B = 0 := by
  rw [pairing_trace]; change (Aᵀ*B).trace = 0; rw [ha]
  have h := trace_transpose (A*B); rw [transpose_mul,ha,hb,neg_mul,trace_neg,trace_mul_comm] at h; linarith

private lemma disjoint {a b : Fin n → ℕ} (h : Injective fun i => (a i,b i)) {A B : M}
    (ha : Support a A) (hb : Support b B) (hk : Bᵀ = -B) : pairing A B = 0 := by
  simp only [pairing_entries,RCLike.re_to_real,RCLike.im_to_real,mul_zero,add_zero]
  apply Finset.sum_eq_zero; intro i _; apply Finset.sum_eq_zero; intro j _
  by_cases ea : a i = a j <;> by_cases eb : b i = b j
  · obtain rfl := h (Prod.ext ea eb); have eq : B i i = -B i i := congrFun (congrFun hk i) i; rw [show B i i = 0 by linarith,mul_zero]
  all_goals first | rw [ha i j ea,zero_mul] | rw [hb i j eb,mul_zero]

private lemma core {a b : Fin n → ℕ} (h : Injective fun i => (a i,b i)) {C K D E : M}
    (c : Support a C) (k : Support b K) (d : Support a D) (e : Support b E)
    (hc : Cᵀ = -C) (hk : Kᵀ = -K) (hd : Dᵀ = -D) (he : Eᵀ = -E) :
    pairing (C*(C+K)+(C+K)*K) (D+E) = 0 := by
  have hde : (D+E)ᵀ = -(D+E) := by simp [hd,he,add_comm]
  have p₁ : pairing (C*K) D = 0 := by rw [left_adj,pair_comm]; exact disjoint h (c.conjTranspose.mul d) k hk
  have p₂ : pairing (C*K) E = 0 := by rw [right_adj,pair_comm]; exact disjoint ((Equiv.prodComm _ _).injective.comp h) (e.mul k.conjTranspose) c hc
  have p₃ := sym_skew (show (C*C)ᵀ = C*C by simp [hc]) hde
  have p₄ := sym_skew (show (K*K)ᵀ = K*K by simp [hk]) hde
  simp only [mul_add,add_mul,pa,p₃,p₄]; simp [pb,p₁,p₂]

variable (σ : Equiv.Perm (Fin n))
def rot (X : M) := X.submatrix σ.symm σ.symm
lemma commute_perm (X : M) : rot σ X * perm ℝ σ = perm ℝ σ * X := by ext; simp [rot]
private lemma rot_skew {X : M} (h : Skew X) : (rot σ X)ᵀ = -(rot σ X) := congrArg (rot σ) h

theorem certificate {r l : Layer ℝ n} {a b : Fin n → ℕ} {L R C Ω : M}
    (sep : Injective fun i => (b i,a (σ i))) (ca : ∀ A ∈ l, Support a A) (cb : ∀ B ∈ r, Support b B)
    (hl : SharedFactor l L) (hr : SharedFactor r R) (hc : C ∈ skewSpace l) (hw : Ω ∈ skewSpace r) :
    let P := perm ℝ σ; let γ := path L R C Ω P
    ∀ t, InOrbit r l P (γ t) ∧ HasDerivAt γ (deriv γ t) t ∧ HasDerivAt (deriv γ) (deriv (deriv γ) t) t ∧
      (∀ Z ∈ pointDirections r l (γ t), pairing (deriv (deriv γ) t) Z = 0) ∧
      pairing (deriv γ t) (deriv γ t) = pairing C C + pairing Ω Ω := by
  intro P γ
  let K := rot σ Ω; let go (Q : M) := path L R C Ω (Q*P)
  have punit := perm_isU (𝕜 := ℝ) σ
  have cm (X : M) : rot σ X * P = P * X := commute_perm σ X
  have h (Q t) : HasDerivAt (go Q) (go (C*Q+Q*K) t) t := by simpa [go,add_mul,mul_assoc,K,cm] using path_deriv L R C Ω (Q*P) t
  have h₁ t : HasDerivAt γ (go (C+K) t) t := by simpa [go,γ] using h 1 t
  rw [show deriv γ = _ from funext fun t => (h₁ t).deriv,show deriv (go (C+K)) = _ from funext fun t => (h _ t).deriv]
  intro t
  let A := L * exp (t • C); let B := exp (t • Ω) * R
  have hA : SharedFactor l A := shared_factor_mul hl (exp_factor hc t)
  have hB : SharedFactor r B := shared_factor_mul (exp_factor hw t) hr
  have lift (X Y : M) : pairing (go X t) (go Y t) = pairing X Y := by
    change pairing (A*(X*P)*B) (A*(Y*P)*B) = _
    rw [pairing_right_unitary _ hB.2,pairing_left_unitary _ hA.2,pairing_right_unitary _ punit]
  have hi : Injective fun i => (a i,b (σ.symm i)) := by
    intro i j eq; apply σ.symm.injective; apply sep; simpa using congrArg Prod.swap eq
  have hs {X : M} (hx : X ∈ r) : Support (b ∘ σ.symm) (rot σ X) := fun i j => cb X hx _ _
  refine ⟨⟨A,B,hA,hB,rfl⟩,h₁ t,h _ t,?_,?_⟩
  · intro Z hZ
    let g : Factors r l := (Factor.ofMatrix A hA,(Factor.ofMatrix B hB)⁻¹)
    have act (T : M) : g • T = A*T*B := by change A * T * (Bᴴ)ᴴ = _; simp
    rw [show γ t = g • P from (act P).symm,← action_directions] at hZ
    obtain ⟨Y,y,hY⟩ := hZ
    obtain ⟨D,E,d,e,rfl⟩ := (mem_pointDirections_iff ..).1 y
    have hZ' : Z = go (D+rot σ E) t := hY.symm.trans ((act _).trans (by change A*(D*P+P*E)*B = A*((D+rot σ E)*P)*B; simp [mul_add,add_mul,mul_assoc,cm]))
    rw [hZ',lift]; exact core hi (ca C hc.1) (hs hw.1) (ca D d.1) (hs e.1) hc.2 (rot_skew σ hw.2) d.2 (rot_skew σ e.2)
  · have hz := disjoint hi (ca C hc.1) (hs hw.1) (rot_skew σ hw.2)
    have hK : pairing K K = pairing Ω Ω := by
      rw [← pairing_right_unitary _ punit K K,show K*P = _ from cm Ω,pairing_left_unitary _ punit]
    rw [lift,pa,pb,pb,pair_comm K C,hz,hK]; ring
end Geodesic
end GS.Isometric
