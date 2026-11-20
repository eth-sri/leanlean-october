module

public import RequestProject.MonoidAlgebraMapDomain
public import RequestProject.FoxLinear

@[expose] public section

/-!
# The chain complex of the cover `K_N` and the Crowell exact sequence

Let `K` be the two-complex of a finite presentation `⟨x_1, …, x_n | r_1, …, r_m⟩`, let `F`
be the free group on the generators and let `Ñ ◁ F` be the normal subgroup corresponding
(Remark 1 of the paper) to a normal subgroup `N` of `G = π₁(K)`; write `Q = F/Ñ` for the
deck group of the cover `K_N`.  The cellular chain complex of `K_N` is the complex of free
left `ℤ[Q]`-modules

`ℤ[Q]^m --∂₂--> ℤ[Q]^n --∂₁--> ℤ[Q]`,
`∂₂(e_j) = (π(∂r_j/∂x_i))_i`,  `∂₁(e_i) = x_i - 1`,

where `π : ℤ[F] → ℤ[Q]` is the projection and `∂r/∂x` are the Fox derivatives.

This file builds that complex and proves everything about it that the paper uses:

* `FiniteChains.bdry1_bdry2` : it is a complex, `∂₁ ∘ ∂₂ = 0`;
* `FiniteChains.exists_bdry1_preimage` : the image of `∂₁` is the augmentation ideal, i.e.
  `H̃₀(K_N) = 0` — the cover is connected;
* `FiniteChains.exists_mem_of_bdry1_eq_zero` : **the Crowell exact sequence**, `ker ∂₁`
  consists exactly of the Fox vectors `(π(∂w/∂x_i))_i` of the elements `w ∈ Ñ`;
* `FiniteChains.exists_bdry2_preimage` : if `N` is perfect, i.e.
  `Ñ ≤ ⟪r_1, …, r_m⟫ ⊔ [Ñ, Ñ]`, then `ker ∂₁ = im ∂₂`, i.e. `H₁(K_N) = 0`;
* `FiniteChains.cover_acyclic` : consequently, if moreover `∂₂` is injective (that is
  `H₂(K_N) = ker ∂₂ = 0`, the requirements (2.2) of Section 2), the chain complex of the
  cover is acyclic.

This is the algebraic content of the passage "`N` perfect and `ker ∂_{2,N} = 0` implies
`K_N` acyclic" used in the proof of `(1) ⇒ (2)` of Theorem A.
-/
noncomputable section

open scoped commutatorElement

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The group ring `ℤ[Q]` of the deck group `Q = F/Ñ` of the cover. -/
abbrev CoverRing := MonoidAlgebra ℤ (FreeGroup α ⧸ Nsub)

/-- The projection `π : ℤ[F] → ℤ[Q]`. -/
def proj :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' Nsub)

/-- The image of a word in `ℤ[Q]`. -/
def qgrp (g : FreeGroup α) : CoverRing Nsub :=
  MonoidAlgebra.single (QuotientGroup.mk g) 1

/-- The augmentation `ℤ[Q] → ℤ`. -/
def augQ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α ⧸ Nsub) 1).toRingHom

/-- A set-theoretic lift `ℤ[Q] → ℤ[F]` of the projection. -/
def liftQ (z : CoverRing Nsub) :=
  MonoidAlgebra.mapDomain (fun q => Quotient.out q) z

omit [Fintype α] [DecidableEq α] in
theorem proj_apply (b : FreeGroupRing α) :
    proj Nsub b = MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g)) b := rfl

variable (g : FreeGroup α)

omit [Fintype α] [DecidableEq α] in
@[simp] theorem proj_single (n : ℤ) :
    proj Nsub (single g n) = single (QuotientGroup.mk g) n := MonoidAlgebra.mapDomain_single

omit [Fintype α] [DecidableEq α] in
theorem proj_grp : proj Nsub (grp g) = qgrp Nsub g := by
  solve_by_elim [grp_eq_single, proj_single]

section

variable {g : FreeGroup α} (hg : g ∈ Nsub)
include hg

omit [Fintype α] [DecidableEq α] in
theorem qgrp_eq_one_of_mem : qgrp Nsub g = 1 := by
  rw [qgrp, ((QuotientGroup.eq_one_iff g).2 hg)]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem proj_grp_of_mem : proj Nsub (grp g) = 1 := by
  simp_all [proj_grp, qgrp_eq_one_of_mem]

end

omit [Fintype α] [DecidableEq α] in
@[simp] theorem augQ_single (q : FreeGroup α ⧸ Nsub) (n : ℤ) : augQ Nsub (single q n) = n := by
  simp [augQ]

omit [Fintype α] [DecidableEq α] in
theorem augQ_proj (b : FreeGroupRing α) : augQ Nsub (proj Nsub b) = aug b := by
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b₁ b₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add]
  | single g n => simp

omit [Fintype α] [DecidableEq α] in
theorem proj_liftQ (z : CoverRing Nsub) : proj Nsub (liftQ Nsub z) = z := by
  rw [proj_apply, liftQ, ← MonoidAlgebra.mapDomain_comp] <;> aesop

/-! ### The Fox vector of a word -/

/-- The Fox vector `(π(∂w/∂x_i))_i ∈ ℤ[Q]^n` of a word. -/
def foxVec (w : FreeGroup α) : α → CoverRing Nsub :=
  fun i => proj Nsub (fox i w)

omit [Fintype α] in
@[simp] theorem foxVec_one : foxVec Nsub 1 = 0 := rfl

variable {Nsub}

section

variable {v : FreeGroup α} (hv : v ∈ Nsub)
include hv

omit [Fintype α] in
theorem foxVec_mul (w : FreeGroup α) :
    foxVec Nsub (v * w) = foxVec Nsub v + foxVec Nsub w := by
  funext i
  simp only [foxVec, fox_mul, map_add, map_mul, proj_grp_of_mem Nsub hv, one_mul, Pi.add_apply]

omit [Fintype α] in
theorem foxVec_inv :
    foxVec Nsub v⁻¹ = - foxVec Nsub v := by
  have h := foxVec_mul (Subgroup.inv_mem _ hv) v
  rw [inv_mul_cancel, foxVec_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

end

section

variable {r : FreeGroup α} (hr : r ∈ Nsub)
include hr

omit [Fintype α] in
theorem foxVec_conj (f : FreeGroup α) :
    foxVec Nsub (f * r * f⁻¹) = proj Nsub (grp f) • foxVec Nsub r := by
  funext i
  have hfox : fox i (f * r * f⁻¹)
      = fox i f + grp f * fox i r + grp (f * r) * fox i f⁻¹ := by
    simp [fox_mul]
  have hff : proj Nsub (grp f) * proj Nsub (grp f⁻¹) = 1 := by
    rw [← map_mul, ← grp_mul, mul_inv_cancel, grp_one, map_one]
  simp only [foxVec, Pi.smul_apply, smul_eq_mul, hfox, fox_inv i f, grp_mul, map_add, map_mul,
    map_neg, proj_grp_of_mem Nsub hr, mul_one]
  rw [mul_neg, ← mul_assoc, hff, one_mul]
  abel

omit [Fintype α] in
theorem foxVec_zpow (n : ℤ) :
    foxVec Nsub (r ^ n) = n • foxVec Nsub r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      rw [zpow_add_one, foxVec_mul (Subgroup.zpow_mem _ hr _), ih, add_smul, one_smul]
  | pred k ih =>
      rw [zpow_sub_one, foxVec_mul (Subgroup.zpow_mem _ hr _), foxVec_inv hr, ih, sub_smul, one_smul, sub_eq_add_neg]

end

/-! ### The module of Fox vectors -/

/-- The set of Fox vectors of the elements of `Ñ`; by the Crowell exact sequence this is
exactly the module of `1`-cycles of the cover. -/
def foxMod : Submodule (CoverRing Nsub) (α → CoverRing Nsub) where
  carrier := {c | ∃ r ∈ Nsub, c = foxVec Nsub r}
  zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r * s, Subgroup.mul_mem _ hr hs, by simp_all [foxVec_mul]⟩
  smul_mem' := by
    rintro u a ⟨r, hr, rfl⟩
    induction u using MonoidAlgebra.induction_linear with
    | zero => exact ⟨1, Subgroup.one_mem _, by simp⟩
    | add u₁ u₂ h₁ h₂ =>
        obtain ⟨r₁, hr₁, e₁⟩ := h₁
        obtain ⟨r₂, hr₂, e₂⟩ := h₂
        refine ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, ?_⟩
        simp_all [foxVec_mul, e₁, e₂, add_smul]
    | single q n =>
        obtain ⟨f, rfl⟩ := Quotient.exists_rep q
        have hconj := Subgroup.Normal.conj_mem ‹Nsub.Normal› r hr f
        refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
        have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n)
            = n • proj Nsub (grp f) := by
          rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        rw [foxVec_zpow hconj, foxVec_conj hr, hsingle, smul_assoc]

/-! ### The kernel of the projection `ℤ[F] → ℤ[Q]` -/

variable (φ : FreeGroup α → FreeGroup α)

/-- Reindexing of a group-ring element along a map of the free group, viewed on `ℤ[F]`. -/
def mapDom (c : FreeGroupRing α) := MonoidAlgebra.mapDomain φ c

omit [Fintype α] [DecidableEq α] in
theorem mapDom_add (c d : FreeGroupRing α) :
    mapDom φ (c + d) = mapDom φ c + mapDom φ d := by apply MonoidAlgebra.mapDomain_add

omit [Fintype α] [DecidableEq α] in
theorem mapDom_single (g : FreeGroup α) (n : ℤ) :
    mapDom φ (single g n) = single (φ g) n := MonoidAlgebra.mapDomain_single

variable (Nsub)

/-- The left ideal of `ℤ[F]` generated by the elements `r - 1` with `r ∈ Ñ`. -/
def relIdeal :=
  Submodule.span (FreeGroupRing α) {y | ∃ r ∈ Nsub, y = grp r - 1}

omit [Fintype α] [DecidableEq α] in
theorem mem_relIdeal_of_proj_eq_zero (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    b ∈ relIdeal Nsub := by
  classical
  set φ : FreeGroup α → FreeGroup α :=
    fun g => Quotient.out _ with hφ
  have hmap : mapDom φ b = 0 := by
    show MonoidAlgebra.mapDomain φ b = 0
    have hcomp : MonoidAlgebra.mapDomain φ b
        = MonoidAlgebra.mapDomain (fun q : FreeGroup α ⧸ Nsub => Quotient.out q)
            (MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g)) b) :=
      MonoidAlgebra.mapDomain_comp _ _ b
    simp_all [hcomp, proj_apply, hb, MonoidAlgebra.mapDomain_zero]
  have key : ∀ c : FreeGroupRing α, c - mapDom φ c ∈ relIdeal Nsub := by
    intro c
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
        have hz : 0 - mapDom φ 0 = 0 := by
          aesop
        simp_all
    | add c₁ c₂ h₁ h₂ =>
        have hsplit : (c₁ + c₂) - mapDom φ (c₁ + c₂)
            = (c₁ - mapDom φ c₁) + (c₂ - mapDom φ c₂) := by
          rw [mapDom_add]; abel
        rw [hsplit]
        apply Submodule.add_mem <;> assumption
    | single g n =>
        have hmk : (QuotientGroup.mk (φ g)) = QuotientGroup.mk g :=
          QuotientGroup.out_eq' _
        have hmem := QuotientGroup.eq.1 hmk
        have hgrp : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) = grp g - grp (φ g) := by
          rw [mul_sub, ← grp_mul, mul_inv_cancel_left, mul_one]
        have hrewrite : (single g n) - mapDom φ (single g n)
            = ((n : ℤ)) * (grp (φ g) * (grp ((φ g)⁻¹ * g) - 1)) := by
          rw [(mapDom_single φ g n), hgrp, single_eq_smul_grp, single_eq_smul_grp, ← smul_sub, zsmul_eq_mul]
        rw [hrewrite]
        have h1 : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) ∈ relIdeal Nsub := by
          simpa [smul_eq_mul] using Submodule.smul_mem (relIdeal Nsub) _ (Submodule.subset_span ⟨_, hmem, rfl⟩)
        simpa [smul_eq_mul] using
          Submodule.smul_mem _ _ h1
  have hb' := key b
  simp_all

/-! ### The Fox vector of a ring element -/

/-- The Fox vector of an element of `ℤ[F]`, i.e. the vector of the linearly extended Fox
derivatives, projected to `ℤ[Q]`. -/
def foxProj (b : FreeGroupRing α) : α → CoverRing Nsub :=
  fun i => proj Nsub (foxLin i b)

omit [Fintype α] in
@[simp] theorem foxProj_zero : foxProj Nsub 0 = 0 := rfl

omit [Fintype α] in
theorem foxProj_add (b₁ b₂ : FreeGroupRing α) :
    foxProj Nsub (b₁ + b₂) = foxProj Nsub b₁ + foxProj Nsub b₂ := by
  funext i; simp [foxProj]

omit [Fintype α] in
theorem foxProj_mul_of_aug_zero (u b : FreeGroupRing α) (hb : aug b = 0) :
    foxProj Nsub (u * b) = proj Nsub u • foxProj Nsub b := by
  funext i
  simp [foxProj, foxLin_mul, hb, zero_smul, zero_add, map_mul, Pi.smul_apply, smul_eq_mul]

omit [Fintype α] in
theorem foxProj_mem_foxMod (b : FreeGroupRing α) (hb : proj Nsub b = 0) :
    foxProj Nsub b ∈ foxMod := by
  refine (Submodule.span_induction
    (p := fun y _ => aug y = 0 ∧ foxProj Nsub y ∈ foxMod) ?_ ?_ ?_ ?_ (mem_relIdeal_of_proj_eq_zero Nsub b hb)).2
  · rintro y ⟨r, hr, rfl⟩
    refine ⟨by simp [map_sub], ?_⟩
    have hval : foxProj Nsub (grp r - 1) = foxVec Nsub r := by
      funext i
      have h1 : foxLin i 1 = 0 := by
        solve_by_elim [grp_one, foxLin_grp, fox_one]
      simp [foxProj, foxVec, map_sub, foxLin_grp, h1, sub_zero]
    solve_by_elim
  · simp
  · rintro x y hx hy ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by rw [map_add, hx1, hy1, add_zero], by
      rw [foxProj_add]; apply Submodule.add_mem <;> assumption⟩
  · rintro a x hx ⟨hx1, hx2⟩
    refine ⟨by simp_all, ?_⟩
    rw [smul_eq_mul, foxProj_mul_of_aug_zero Nsub a x hx1]
    apply Submodule.smul_mem <;> assumption

/-! ### The boundary maps of the cover -/

/-! ### The second boundary and the homology of the cover -/

variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The boundary `∂₂ : ℤ[Q]^m → ℤ[Q]^n`, `∂₂(e_j) = (π(∂r_j/∂x_i))_i`. -/
def bdry2 (u : J → CoverRing Nsub) : α → CoverRing Nsub :=
  fun i => ∑ j : J, u j * proj Nsub (fox i (ρ j))

end FiniteChains
