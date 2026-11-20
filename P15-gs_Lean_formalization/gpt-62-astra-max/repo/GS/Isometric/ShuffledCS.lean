module

public import GS.Isometric.CosineSine
public import GS.Isometric.Factorization
public import GS.OriginalLocalModel

@[expose] public section

/-! Express the sum-indexed decomposition in the scalar shuffle convention. -/
noncomputable section
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {p : ℕ}

lemma shuffle_label {k b} (i : Fin (k*b)) : (scalarShuffle k b i).val / k = (finProdFinEquiv.symm i).2.val := by
  let x := finProdFinEquiv.symm i
  have hcast {m n} (e : m = n) (a : Fin m) : (cast (congrArg Fin e) a).val = a.val := by cases e; rfl
  change (cast (congrArg Fin (Nat.mul_comm b k)) (finProdFinEquiv (x.2,x.1)) : Fin (k*b)).val / k = _
  rw [hcast (Nat.mul_comm b k)]
  change (x.1.val + k * x.2.val) / k = x.2.val
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt x.1.isLt),Nat.div_eq_of_lt x.1.isLt,zero_add]

/-- After the thin CS decomposition the first block columns agree. The
residual unitary is block triangular, hence block diagonal; no completion
of a second set of singular vectors is necessary. -/
theorem exhaustion {X : Square 𝕜 (2*p)} : let P := perm 𝕜 (scalarShuffle 2 p)
    In₃U p 2 p P Pᴴ X ↔ IsU X := by
  intro P
  have hp : IsU P := perm_isU _
  refine ⟨fun h => (h.forget hp hp.conjTranspose).2, fun hx => ?_⟩
  let f := finProdFinEquiv (m := 2) (n := p)
  let e := (Equiv.prodComm ..).trans f
  have gram {Z : Square 𝕜 (2*p)} (h : IsU Z) := congrArg (fun A => readBlock e A 0 0) h.1
  obtain ⟨U,W,V,c,s,u,w,v,ac,cs⟩ := thin (readBlock e X 0 0) (readBlock e X 1 0) (by simpa [read_mul,read_star,Fin.sum_univ_two] using gram hx)
  let L := pack e ![U,W]; let T := pack e ![V,1]; let F := Lᴴ*X*T
  have side (B : Fin 2 → Square 𝕜 p) := pack_supported e (fun _ => rfl) B
  have l : IsU L := (pack_unitary e _).2 (by intro i; fin_cases i <;> assumption)
  have t : IsU T := (pack_unitary e _).2 (by intro i; fin_cases i <;> first | exact v | exact IsU.one)
  have hF : IsU F := (l.conjTranspose.mul hx).mul t
  have first (i) : readBlock e F i 0 = ![realDiag 𝕜 c,realDiag 𝕜 s] i := by
    fin_cases i <;> simp [F,L,T,read_mul,Fin.sum_univ_two,mul_assoc,ac,cs,u.star_cancel,w.star_cancel]
  have sum := gram hF
  simp [read_mul,Fin.sum_univ_two,first] at sum
  let B (k : Fin p) : Square 𝕜 2 := !![(c k:𝕜),-(s k:𝕜);s k,c k]
  let K := pack f B
  have b (k) : IsU (B k) := by
    have norm := congrFun (congrFun sum k) k; simp [realDiag,diagonal_mul_diagonal] at norm
    apply IsU.of_left; ext i j; fin_cases i <;> fin_cases j <;> simp [B,conjTranspose_apply,mul_apply,Fin.sum_univ_two,RCLike.star_def] <;> grind
  have k : IsU K := (pack_unitary f _).2 b
  have col (i) : readBlock e F i 0 = readBlock e K i 0 := by rw [first,read_cross]; fin_cases i <;> rfl
  let J := Kᴴ*F
  have low : readBlock e J 1 0 = 0 := by
    change readBlock _ (Kᴴ*F) 1 0 = _; rw [read_mul]; simp_rw [col]; rw [← read_mul,k.1,read_one]; simp
  have jU : IsU J := k.conjTranspose.mul hF
  have hJ : DiagonalBlocks p J := support_of_triangular jU (by
    intro i j hij; obtain ⟨⟨a,i⟩,rfl⟩ := e.surjective i; obtain ⟨⟨b,j⟩,rfl⟩ := e.surjective j
    have quo (x) : (e x).val / p = x.2.val := by change (e.symm (e x)).2.val = _; rw [e.symm_apply_apply]
    simp only [quo] at hij; fin_cases i <;> fin_cases j <;> first | exact congrFun (congrFun low a) b | norm_num at hij)
  let σ := scalarShuffle 2 p
  have mid := pack_supported (f.trans σ) (fun i => by simpa [f,σ] using (shuffle_label (σ.symm i)).symm) B
  refine ⟨J*Tᴴ,_,L,hJ.mul (side _).conjTranspose,mid,side _,jU.mul t.conjTranspose,(pack_unitary _ _).2 b,l,?_⟩
  calc X = L * (Pᴴ * pack (f.trans σ) B * P) * (J*Tᴴ) := by rw [unwire]; change X = L*K*(Kᴴ*(Lᴴ*X*T)*Tᴴ); simp [mul_assoc,k.cancel_star,l.cancel_star,t.2]
       _ = _ := by simp [Matrix.mul_assoc]
end GS.Isometric
