module

public import GS.Isometric.BlockQR
public import GS.Isometric.Products

@[expose] public section

/-! Two and three layers suffice over both fields. QR in the two outer
layers uses opposite orders pulled back from the middle block labels. The
remaining middle factor is both unitary and block triangular. -/
noncomputable section
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

lemma In₃U.forget {r m l} {P Q X : Square 𝕜 n} (h : In₃U r m l P Q X) (hp : IsU P) (hq : IsU Q) :
    In₃ r m l P Q X ∧ IsU X := by
  obtain ⟨R,M,L,hr,hm,hl,u,v,w,rfl⟩ := h
  exact ⟨⟨R,M,L,hr,hm,hl,rfl⟩, (((w.mul hq).mul v).mul hp).mul u⟩

theorem three (r m l : ℕ) (p q : Equiv.Perm (Fin n)) (X : Square 𝕜 n) :
    In₃ r m l (perm 𝕜 p) (perm 𝕜 q) X ∧ IsU X ↔ In₃U r m l (perm 𝕜 p) (perm 𝕜 q) X := by
  let P := perm 𝕜 p
  let Q := perm 𝕜 q
  have hp : IsU P := perm_isU _
  have hq : IsU Q := perm_isU _
  refine ⟨?_,fun h => h.forget hp hq⟩
  rintro ⟨⟨R,M,L,hr,hm,hl,rfl⟩,hx⟩
  have inv : IsUnit (L*Q*M*P*R) := IsUnit.of_mul_eq_one _ hx.2
  simp only [IsUnit.mul_iff] at inv
  obtain ⟨U,T,hu,u,ht,e⟩ := sortedQR (fun i => (q.symm i).val / m) hl inv.1.1.1.1
  obtain ⟨V,S,hv,v,hs,f⟩ := sortedQR (fun i => OrderDual.toDual ((p i).val / m)) hr.conjTranspose inv.2.star
  have f' : R = Sᴴ * Vᴴ := by simpa using congrArg conjTranspose f
  let K := Qᴴ*T*Q*M*(P*Sᴴ*Pᴴ)
  have h : L*Q*M*P*R = U*Q*K*P*Vᴴ := by
    simp [K,e,f',Matrix.mul_assoc,hq.cancel_star,hp.star_cancel]
  have hk : IsU K := by
    have eq : (U*Q)ᴴ * (L*Q*M*P*R) * (P*Vᴴ)ᴴ = K := by
      rw [h]; simp [conjTranspose_mul,Matrix.mul_assoc,u.star_cancel,hq.star_cancel,v.star_cancel,hp.2]
    rw [← eq]
    exact (((u.mul hq).conjTranspose).mul hx).mul (hp.mul v.conjTranspose).conjTranspose
  have h₁ : (Qᴴ*T*Q).BlockTriangular (fun i => i.val / m) := by
    intro i j hij
    simp only [Q,perm_star,mul_perm_apply,perm_mul_apply,Equiv.symm_symm]
    apply ht; simpa using hij
  have h₂ : (P*Sᴴ*Pᴴ).BlockTriangular (fun i => i.val / m) := by
    intro i j hij
    simp only [P,perm_star,mul_perm_apply,perm_mul_apply,conjTranspose_apply,star_eq_zero]
    apply hs; simpa only [Equiv.apply_symm_apply, OrderDual.toDual_lt_toDual] using hij
  exact ⟨Vᴴ,K,U,hv.conjTranspose,support_of_triangular hk ((h₁.mul (fun {_ _} h => hm _ _ h.ne')).mul h₂),
    hu,v.conjTranspose,hk,u,h⟩

theorem two (r l : ℕ) (p : Equiv.Perm (Fin n)) (X : Square 𝕜 n) :
    In₂ r l (perm 𝕜 p) X ∧ IsU X ↔ In₂U r l (perm 𝕜 p) X := by
  constructor
  · rintro ⟨⟨R,L,hr,hl,e⟩,hx⟩
    obtain ⟨V,W,U,hv,hw,hu,v,w,u,e'⟩ := (three r l 1 p (.refl _) X).1
      ⟨⟨R,L,1,hr,hl,Support.one,by simpa using e⟩,hx⟩
    have hu' : DiagonalBlocks l U := fun i j h => hu i j (by grind)
    exact ⟨V,U*W,hv,hu'.mul hw,v,u.mul w,by simp_all⟩
  · rintro ⟨R,L,hr,hl,u,v,rfl⟩
    exact ⟨⟨R,L,hr,hl,rfl⟩,(v.mul (perm_isU p)).mul u⟩
end GS.Isometric
