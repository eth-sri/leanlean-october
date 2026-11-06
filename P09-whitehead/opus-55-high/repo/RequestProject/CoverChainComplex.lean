import RequestProject.MonoidAlgebraMapDomain
import RequestProject.FoxLinear
import RequestProject.Tac
noncomputable section


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

bwd
open scoped commutatorElement

namespace FiniteChains

open MonoidAlgebra

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (Nsub : Subgroup (FreeGroup α)) [Nsub.Normal]

/-- The group ring `ℤ[Q]` of the deck group `Q = F/Ñ` of the cover. -/
abbrev CoverRing := MonoidAlgebra ℤ (FreeGroup α ⧸ Nsub)

/-- The projection `π : ℤ[F] → ℤ[Q]`. -/
def proj : FreeGroupRing α →+* CoverRing Nsub :=
  MonoidAlgebra.mapDomainRingHom ℤ (QuotientGroup.mk' Nsub)

/-- The image of a word in `ℤ[Q]`. -/
def qgrp (g : FreeGroup α) : CoverRing Nsub :=
  MonoidAlgebra.single (QuotientGroup.mk g) 1

/-- The augmentation `ℤ[Q] → ℤ`. -/
def augQ : CoverRing Nsub →+* ℤ :=
  (MonoidAlgebra.lift ℤ ℤ (FreeGroup α ⧸ Nsub) 1).toRingHom

/-- A set-theoretic lift `ℤ[Q] → ℤ[F]` of the projection. -/
def liftQ (z : CoverRing Nsub) : FreeGroupRing α :=
  MonoidAlgebra.mapDomain Quotient.out z

omit [Fintype α] [DecidableEq α] in
theorem proj_apply (b : FreeGroupRing α) :
    proj Nsub b = MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)) b := rfl

omit [Fintype α] [DecidableEq α] in
@[simp] theorem proj_single (g : FreeGroup α) (n : ℤ) :
    proj Nsub (single g n) = single (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) n := MonoidAlgebra.mapDomain_single

omit [Fintype α] [DecidableEq α] in
theorem proj_grp (g : FreeGroup α) : proj Nsub (grp g) = qgrp Nsub g := by
  rw [grp_eq_single, proj_single, qgrp]

omit [Fintype α] [DecidableEq α] in
theorem qgrp_eq_one_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : qgrp Nsub g = 1 := by
  have h : (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) = 1 := by simp_all
  rw [qgrp, h]
  rfl

omit [Fintype α] [DecidableEq α] in
theorem proj_grp_of_mem {g : FreeGroup α} (hg : g ∈ Nsub) : proj Nsub (grp g) = 1 := by
  rw [proj_grp, qgrp_eq_one_of_mem Nsub hg]

omit [Fintype α] [DecidableEq α] in
@[simp] theorem augQ_single (q : FreeGroup α ⧸ Nsub) (n : ℤ) : augQ Nsub (single q n) = n := by
  simp [augQ]

omit [Fintype α] [DecidableEq α] in
theorem augQ_proj (b : FreeGroupRing α) : augQ Nsub (proj Nsub b) = aug b := by
  induction b using MonoidAlgebra.induction_linear <;> simp_all

omit [Fintype α] [DecidableEq α] in
theorem proj_liftQ (z : CoverRing Nsub) : proj Nsub (liftQ Nsub z) = z := by
  rw [proj_apply, liftQ, ← MonoidAlgebra.mapDomain_comp]
  aesop

/-! ### The Fox vector of a word -/

/-- The Fox vector `(π(∂w/∂x_i))_i ∈ ℤ[Q]^n` of a word. -/
def foxVec (w : FreeGroup α) : α → CoverRing Nsub :=
  fun i => proj Nsub (fox i w)

omit [Fintype α] in
@[simp] theorem foxVec_one : foxVec Nsub 1 = 0 := by
  rfl

variable {Nsub}

omit [Fintype α] in
theorem foxVec_mul {v : FreeGroup α} (hv : v ∈ Nsub) (w : FreeGroup α) :
    foxVec Nsub (v * w) = foxVec Nsub v + foxVec Nsub w := by
  funext i
  simp [foxVec, fox_mul, map_add, map_mul, proj_grp_of_mem Nsub hv, one_mul, Pi.add_apply]

omit [Fintype α] in
theorem foxVec_inv {v : FreeGroup α} (hv : v ∈ Nsub) :
    foxVec Nsub v⁻¹ = - foxVec Nsub v := by
  have h := foxVec_mul (Subgroup.inv_mem _ hv) v
  grind [inv_mul_cancel, foxVec_one]

omit [Fintype α] in
theorem foxVec_conj {r : FreeGroup α} (hr : r ∈ Nsub) (f : FreeGroup α) :
    foxVec Nsub (f * r * f⁻¹) = proj Nsub (grp f) • foxVec Nsub r := by
  funext i
  have hfox : fox i (f * r * f⁻¹)
      = fox i f + grp f * fox i r + grp (f * r) * fox i f⁻¹ := by
    grind [fox_mul]
  have hff : proj Nsub (grp f) * proj Nsub (grp f⁻¹) = 1 := by
    rw [← map_mul, ← grp_mul, mul_inv_cancel, grp_one, map_one]
  simp [foxVec, Pi.smul_apply, smul_eq_mul, hfox, fox_inv i f, grp_mul, map_add, map_mul, map_neg, proj_grp_of_mem Nsub hr, mul_one, mul_neg, ← mul_assoc, hff, one_mul]

omit [Fintype α] in
theorem foxVec_zpow {r : FreeGroup α} (hr : r ∈ Nsub) (n : ℤ) :
    foxVec Nsub (r ^ n) = n • foxVec Nsub r := by
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hmem : r ^ (k : ℤ) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_add_one, foxVec_mul hmem, ih, add_smul, one_smul]
  | pred k ih =>
      have hmem : r ^ (-(k : ℤ)) ∈ Nsub := Subgroup.zpow_mem _ hr _
      rw [zpow_sub_one, foxVec_mul hmem, foxVec_inv hr, ih, sub_smul, one_smul, sub_eq_add_neg]

/-! ### The module of Fox vectors -/

/-- The set of Fox vectors of the elements of `Ñ`; by the Crowell exact sequence this is
exactly the module of `1`-cycles of the cover. -/
def foxMod : Submodule (CoverRing Nsub) (α → CoverRing Nsub) where
  carrier := {c | ∃ r ∈ Nsub, c = foxVec Nsub r}
  zero_mem' := ⟨1, Subgroup.one_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨r, hr, rfl⟩ ⟨s, hs, rfl⟩
    exact ⟨r * s, Subgroup.mul_mem _ hr hs, by rw [foxVec_mul hr]⟩
  smul_mem' := by
    rintro u a ⟨r, hr, rfl⟩
    induction u using MonoidAlgebra.induction_linear with
    | zero => aesop
    | add u₁ u₂ h₁ h₂ =>
        obtain ⟨r₁, hr₁, e₁⟩ := h₁
        obtain ⟨r₂, hr₂, e₂⟩ := h₂
        refine ⟨r₁ * r₂, Subgroup.mul_mem _ hr₁ hr₂, ?_⟩
        rw [foxVec_mul hr₁, ← e₁, ← e₂, add_smul]
    | single q n =>
        obtain ⟨f, rfl⟩ := Quotient.exists_rep q
        have hconj := Subgroup.Normal.conj_mem ‹Nsub.Normal› r hr f
        refine ⟨(f * r * f⁻¹) ^ n, Subgroup.zpow_mem _ hconj n, ?_⟩
        have hsingle : (single (QuotientGroup.mk f : FreeGroup α ⧸ Nsub) n : CoverRing Nsub)
            = n • proj Nsub (grp f) := by
          rw [proj_grp, qgrp, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        rw [foxVec_zpow hconj, foxVec_conj hr, hsingle, smul_assoc]

/-! ### The kernel of the projection `ℤ[F] → ℤ[Q]` -/

/-- Reindexing of a group-ring element along a map of the free group, viewed on `ℤ[F]`. -/
def mapDom (φ : FreeGroup α → FreeGroup α) (c : FreeGroupRing α) :
    FreeGroupRing α := MonoidAlgebra.mapDomain φ c

omit [Fintype α] [DecidableEq α] in
theorem mapDom_add (φ : FreeGroup α → FreeGroup α) (c d : FreeGroupRing α) :
    mapDom φ (c + d) = mapDom φ c + mapDom φ d := MonoidAlgebra.mapDomain_add φ c d

omit [Fintype α] [DecidableEq α] in
theorem mapDom_single (φ : FreeGroup α → FreeGroup α) (g : FreeGroup α) (n : ℤ) :
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
    fun g => Quotient.out (QuotientGroup.mk g : FreeGroup α ⧸ Nsub) with hφ
  have hmap : mapDom φ b = 0 := by
    show MonoidAlgebra.mapDomain φ b = 0
    have hcomp : MonoidAlgebra.mapDomain φ b
        = MonoidAlgebra.mapDomain (·.out)
            (MonoidAlgebra.mapDomain (fun g => (QuotientGroup.mk g : FreeGroup α ⧸ Nsub)) b) :=
      MonoidAlgebra.mapDomain_comp _ _ b
    rw [hcomp, ← proj_apply, hb, MonoidAlgebra.mapDomain_zero]
  have key : ∀ c, c - mapDom φ c ∈ relIdeal Nsub := by
    intro c
    induction c using MonoidAlgebra.induction_linear with
    | zero =>
        have hz : (0 : FreeGroupRing α) - mapDom φ 0 = 0 := by
          aesop
        simp_all
    | add c₁ c₂ h₁ h₂ =>
        have hsplit : (c₁ + c₂) - mapDom φ (c₁ + c₂)
            = (c₁ - mapDom φ c₁) + (c₂ - mapDom φ c₂) := by
          grind [mapDom_add]
        aesop
    | single g n =>
        have hmk : (QuotientGroup.mk (φ g) : FreeGroup α ⧸ Nsub) = QuotientGroup.mk g :=
          QuotientGroup.out_eq' _
        have hmem := QuotientGroup.eq.1 hmk
        have hmapd :=
          mapDom_single φ g n
        have hgrp : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) = grp g - grp (φ g) := by
          rw [mul_sub, ← grp_mul, mul_inv_cancel_left, mul_one]
        have hrewrite : (single g n : FreeGroupRing α) - mapDom φ (single g n : FreeGroupRing α)
            = ((n : ℤ) : FreeGroupRing α) * (grp (φ g) * (grp ((φ g)⁻¹ * g) - 1)) := by
          rw [hmapd, hgrp, single_eq_smul_grp, single_eq_smul_grp, ← smul_sub, zsmul_eq_mul]
        rw [hrewrite]
        have hgen : grp ((φ g)⁻¹ * g) - 1 ∈ relIdeal Nsub :=
          Submodule.subset_span ⟨_, hmem, rfl⟩
        have h1 : grp (φ g) * (grp ((φ g)⁻¹ * g) - 1) ∈ relIdeal Nsub := by
          simpa using Submodule.smul_mem _ _ hgen
        simpa using
          Submodule.smul_mem _ _ h1
  have hb' := key b
  simp_all

/-! ### The Fox vector of a ring element -/

/-- The Fox vector of an element of `ℤ[F]`, i.e. the vector of the linearly extended Fox
derivatives, projected to `ℤ[Q]`. -/
def foxProj (b : FreeGroupRing α) : α → CoverRing Nsub :=
  fun i => proj Nsub (foxLin i b)


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
    foxProj Nsub b ∈ foxMod (Nsub := Nsub) := by
  have hmem := mem_relIdeal_of_proj_eq_zero Nsub b hb
  refine (Submodule.span_induction
    (p := fun y _ => aug y = 0 ∧ foxProj Nsub y ∈ foxMod (Nsub := Nsub)) ?_ ?_ ?_ ?_ hmem).2
  · rintro y ⟨r, hr, rfl⟩
    refine ⟨by simp, ?_⟩
    have hval : foxProj Nsub (grp r - 1) = foxVec Nsub r := by
      funext i
      have h1 : foxLin i (1 : FreeGroupRing α) = 0 := by
        rw [← grp_one, foxLin_grp, fox_one]
      simp [foxProj, foxVec, map_sub, foxLin_grp, h1, sub_zero]
    tauto
  · exact ⟨by simp, Submodule.zero_mem _⟩
  · rintro x y hx hy ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨by simp_all, by
      rw [foxProj_add]; aesop⟩
  · rintro a x hx ⟨hx1, hx2⟩
    rw [smul_eq_mul, foxProj_mul_of_aug_zero Nsub a x hx1]
    aesop

/-! ### The boundary maps of the cover -/

/-! ### The second boundary and the homology of the cover -/

variable {J : Type*} [Fintype J] (ρ : J → FreeGroup α)

/-- The boundary `∂₂ : ℤ[Q]^m → ℤ[Q]^n`, `∂₂(e_j) = (π(∂r_j/∂x_i))_i`. -/
def bdry2 (u : J → CoverRing Nsub) : α → CoverRing Nsub :=
  fun i => ∑ j : J, u j * proj Nsub (fox i (ρ j))

omit [Fintype α] in
theorem bdry2_add (u v : J → CoverRing Nsub) :
    bdry2 Nsub ρ (u + v) = bdry2 Nsub ρ u + bdry2 Nsub ρ v := by
  funext i
  simp [bdry2, add_mul, Finset.sum_add_distrib]

omit [Fintype α] in
theorem bdry2_zero : bdry2 Nsub ρ 0 = 0 := by
  funext i; simp [bdry2]
