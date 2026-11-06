module
public import OAI.NumberTheory.DirichletL.Moments.ExceptionalSourceShell
public import OAI.NumberTheory.DirichletL.Moments.WholeDivisorShell

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter

namespace SevenEighths.CenteredMomentExceptionalWholeSource
open HeckeFamily UniqueFactorizationMonoid CenteredMomentWholeDivisorShell CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair CenteredMomentExceptionalAllocationShell CenteredMomentSectorLocalization
universe u
variable {ι:Type u} [Fintype ι] [DecidableEq ι]

lemma weight_nonneg {α κ:Type u} [Fintype α] [Fintype κ] [DecidableEq α] [DecidableEq κ]
    (s:Source α)(v:Source κ)(D:Ideal O)
    (a:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (b:CenteredMomentDivisorAllocation.Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (Z r:ℝ)(hZ:0≤Z):0≤exceptionalWeight s v D a b Z r:=Real.rpow_nonneg hZ _

 theorem whole_weight_bound (lo hi:ι→ℝ)(B δ:ℝ)(hB:0≤B)(hδ:0<δ):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Source I)(v:Source L),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^B) →
      ∀r:ℝ,(∑D∈Ds,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤C*Z^(δ-r):=by
  obtain ⟨Cs,hCs,hshell⟩:=exceptional_shell_subpower lo hi B (δ/2) hB (by linarith)
  obtain ⟨Cn,hCn,hcard⟩:=selected_card_subpower B (δ/2) hB (by linarith)
  refine ⟨Cn*Cs,mul_pos hCn hCs,?_⟩
  filter_upwards [hcard] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v hlo hhi Ds hDs r
  rw [sum_norm_moebius_shells]
  have hz:=zero_lt_one.trans hZ.1
  have hs (n:ℤ)(hn:n∈selectedShells Ds):
      (∑D∈shell Ds n,‖(moebius D:ℂ)‖*
        ∑a∈s.active D,∑b∈v.active D,exceptionalWeight s v D a b Z r)≤Cs*Z^(δ/2-r):=by
    have ht:=selected_scale_bounds Ds (Z^B) hDs n hn
    apply (Finset.sum_le_sum (fun D hD=>mul_le_of_le_one_left
      (Finset.sum_nonneg (fun a _=>Finset.sum_nonneg (fun b _=>weight_nonneg s v D a b Z r hz.le)))
      (moebius_norm_le_one D))).trans
    exact hshell I L s v hlo hhi (shell Ds n)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.1) (dyadicScale n) Z r ht.1 hZ.1 ht.2
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.1)
      (fun D hD=>(shell_member_data Ds n D hD).2.2.2.2.2)
  calc
    _≤∑n∈selectedShells Ds,Cs*Z^(δ/2-r):=Finset.sum_le_sum hs
    _=((selectedShells Ds).card:ℝ)*(Cs*Z^(δ/2-r)):=by simp
    _≤(Cn*Z^(δ/2))*(Cs*Z^(δ/2-r)):=
      mul_le_mul_of_nonneg_right (hZ.2 Ds hDs) (mul_nonneg hCs.le (Real.rpow_nonneg hz.le _))
    _=(Cn*Cs)*Z^(δ-r):=by
      rw [show δ-r=δ/2+(δ/2-r) by ring,Real.rpow_add hz]
      ring
