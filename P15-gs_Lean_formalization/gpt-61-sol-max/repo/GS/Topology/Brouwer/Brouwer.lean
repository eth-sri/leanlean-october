import Mathlib.Tactic

/-
Copyright (c) 2025 Math_XMUM. All rights reserved.
Released under the MIT license; see THIRD_PARTY_LICENSE.txt.

Ported from math-xmum/Brouwer, commit c938f0f2b355adc9f07666c1c2c4002100406923 (2025-11-23),
Gametheory/Brouwer.lean, to the project's pinned mathlib v4.19.0.
Upstream: https://github.com/math-xmum/Brouwer
Adapted to the pinned Lean/mathlib version, with proof simplifications.
-/
import GS.Topology.Brouwer.Scarf
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.PiLex
import Mathlib.Data.PNat.Basic
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity


set_option backward.isDefEq.respectTransparency false
open Classical


noncomputable section

open IndexedLOrder

variable (n l : ℕ+)

abbrev TT := {x : Πₗ (_ : Fin n), Fin (l+1) | ∑ i, (x i : ℕ)  = l}



instance TT.inhabited : Inhabited (TT n l) where
  default :=
    ⟨ fun i => if i = 0 then Fin.last l else 0,  by
      simp only [TT, Set.mem_setOf_eq]
      rw [Finset.sum_eq_single (0 : Fin n)]
      · simp
      · aesop
      · simp [Fin.val_last] ⟩

instance TT.coeFun : CoeFun (TT n l) (fun _ => Fin n → Fin (l+1)) := ⟨Subtype.val⟩

variable {n l} in
def TTtostdSimplex (x : TT n l) : stdSimplex ℝ (Fin n) := ⟨fun i => x i / l, by
  rw [stdSimplex]
  constructor
  · simp_all [div_nonneg]
  · simp only [];
    rw [<-Finset.sum_div, div_eq_one_iff_eq]
    · exact_mod_cast x.2
    · aesop
  ⟩


variable {n l} in
instance TT.ILO : IndexedLOrder (Fin n) (TT n l) where
  IST i := LinearOrder.lift' (fun x : TT n l => toLex (x i,x))
    (fun _ _ h => congrArg Prod.snd (congrArg ofLex h))




lemma size_bound_key (σ : Finset (TT n l)) (C : Finset (Fin n)) (h : TT.ILO.isDominant σ C)
(h2 : σ.Nonempty):
  l < ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (by aesop) + C.card := by
  by_contra h_not
  push_neg at h_not
  let m := fun k => (σ.image (fun x => (x k : ℕ))).min' (by aesop)
  have h_sum_bound := h_not
  have h_sum_plus_one : ∑ k ∈ C, (m k + 1) ≤ l := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_one]
    exact h_sum_bound
  have h_exists_point : ∃ M : TT n l, ∀ k ∈ C, m k + 1 ≤ M k := by
    let M' : Fin n → ℕ := fun k => if k ∈ C then m k + 1 else 0
    let S := ∑ k, M' k
    have h_S_le_l : S ≤ l := by aesop
    let R := l - S
    let M_coords : Fin n → ℕ := fun k => M' k + if k = (0 : Fin n) then R else 0
    have hs : ∑ k, M_coords k = l := by
      simp only [M_coords, Finset.sum_add_distrib]
      simpa [R, S] using Nat.add_sub_of_le h_S_le_l
    have hb (k) : M_coords k ≤ l := by
      rw [← hs]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    refine ⟨⟨(fun k => ⟨M_coords k, Nat.lt_succ_of_le (hb k)⟩), hs⟩, ?_⟩
    intro k hk
    change m k + 1 ≤ M_coords k
    simp [M_coords, M', hk]
  obtain ⟨M, hM⟩ := h_exists_point
  obtain ⟨k, hk, hdom⟩ := h M
  obtain ⟨x, hx, hxmin⟩ := Finset.mem_image.mp
    (Finset.min'_mem (σ.image (fun x => (x k : ℕ))) (by simpa using h2))
  have hlt : x <[k] M := Prod.Lex.left _ _ (by grind)
  exact @not_lt_of_ge _ (TT.ILO.IST k).toPartialOrder.toPreorder M x (hdom x hx) hlt

lemma size_bound_gap (σ : Finset (TT n l)) (C : Finset (Fin n))
    (h : TT.ILO.isDominant σ C) (hσ : σ.Nonempty) :
    let m := fun i => if i ∈ C then (σ.image (fun x => (x i : ℕ))).min'
      (by simpa using hσ) else 0
    ∀ x ∈ σ, ∀ i, m i ≤ (x i : ℕ) ∧ (x i : ℕ) - m i < C.card := by
  let m := fun i => if i ∈ C then (σ.image (fun x => (x i : ℕ))).min'
    (by simpa using hσ) else 0
  have hm : ∀ x ∈ σ, ∀ i, m i ≤ (x i : ℕ) := by
    intro x hx i
    dsimp [m]
    split_ifs
    · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hx)
    · exact Nat.zero_le _
  change ∀ x ∈ σ, ∀ i, m i ≤ (x i : ℕ) ∧ (x i : ℕ) - m i < C.card
  intro x hx i
  refine ⟨hm x hx i, ?_⟩
  have hsx : ∑ k, (x k : ℕ) = (l : ℕ) := x.2
  have hsum : (∑ k, m k) ≤ l := by
    rw [← hsx]
    exact Finset.sum_le_sum (fun k _ => hm x hx k)
  have hg : (x i : ℕ) - m i ≤ l - ∑ k, m k := by
    calc
      _ ≤ ∑ k, ((x k : ℕ) - m k) := Finset.single_le_sum (by intros; omega) (Finset.mem_univ i)
      _ = _ := by rw [Finset.sum_tsub_distrib _ (fun k _ => hm x hx k), hsx]
  have hsumM : (∑ k, m k) = ∑ k ∈ C, (σ.image (fun x => (x k : ℕ))).min' (by simpa using hσ) := by aesop
  have hk := size_bound_key n l σ C h hσ
  rw [hsumM] at hg hsum
  omega

section Brouwer

variable (f : stdSimplex ℝ (Fin n) → stdSimplex ℝ (Fin n))

variable {n l}

instance stdSimplex.upidx (x y : stdSimplex ℝ (Fin n)) : Nonempty { i | x.1 i ≤ y.1 i} := by
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
    (show (∑ i, x.val i) ≤ ∑ i, y.val i by rw [x.property.2,y.property.2])
  exact ⟨⟨i,hi⟩⟩

def stdSimplex.pick (x  y : stdSimplex ℝ (Fin n)) := Classical.choice $ stdSimplex.upidx x y

def Fcolor (x : TT n l) : Fin n := stdSimplex.pick (TTtostdSimplex x) (f (TTtostdSimplex x))

def room_seq (l' : ℕ) :=
  Classical.choice (TT.ILO.Scarf (@Fcolor n ⟨l'+1,Nat.zero_lt_succ _⟩ f)).to_subtype

def room_point_seq (l' : ℕ) := pick_colorful_point
  (Finset.mem_filter.1 (room_seq f l').2).2 |>.1

open Topology Filter

theorem Brouwer (hf : Continuous f) : ∃ x, f x = x := by
  let e := fun k => (room_seq f k).val.2
  obtain ⟨C,hC⟩ := Finite.exists_infinite_fiber e
  letI := hC
  let g := Nat.orderEmbeddingOfSet (e ⁻¹' {C})
  have hg k : (room_seq f (g k)).1.2 = C :=
    (Nat.Subtype.ofNat (e ⁻¹' {C}) k).property
  let u := fun k => (TTtostdSimplex (room_point_seq f (g k)))
  obtain ⟨z,_,φ,hφ,hz⟩ := isCompact_univ.tendsto_subseq (fun k => Set.mem_univ (u k))
  let l := fun k => g (φ k)
  have hl := g.strictMono.comp hφ
  
  have ht : Tendsto (fun k => (l k : ℝ)+1) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hl.tendsto_atTop).atTop_add tendsto_const_nhds
  have hpoint k : (room_point_seq f (l k) : TT n (⟨l k+1,Nat.succ_pos _⟩ : ℕ+)) ∈
      (room_seq f (l k)).1.1 :=
    (pick_colorful_point (Finset.mem_filter.mp (room_seq f (l k)).2).2).property
  have hgap k := size_bound_gap n (⟨l k+1,Nat.succ_pos _⟩ : ℕ+)
    (room_seq f (l k)).1.1 (room_seq f (l k)).1.2
    (Finset.mem_filter.mp (room_seq f (l k)).2).2.1 ⟨_,hpoint k⟩
  have hcard k : (room_seq f (l k)).1.2.card ≤ n := by
    simpa using Finset.card_le_univ (room_seq f (l k)).1.2
  have hge (i : Fin n) (hi : i ∈ C) : z.val i ≤ (f z).val i := by
    have hex : ∀ k, ∃ y : TT n (⟨l k+1,Nat.succ_pos _⟩ : PNat),
        y ∈ (room_seq f (l k)).1.1 ∧ Fcolor f y = i := by
      intro k
      have hm : i ∈ (room_seq f (l k)).1.2 := by aesop
      have he := (Finset.mem_filter.mp (room_seq f (l k)).2).2.2
      simpa only [Finset.mem_image] using (Finset.ext_iff.mp he i).mpr hm
    choose y hy hc using hex
    let v k := TTtostdSimplex (y k)
    have hd : Tendsto (fun k => dist (v k)
        (TTtostdSimplex (room_point_seq f (l k)))) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => dist_nonneg) _
        (tendsto_const_nhds.div_atTop ht :
          Tendsto (fun k => (2*((n : ℝ)+1))/((l k : ℝ)+1)) atTop (𝓝 0))
      intro k
      change ‖(TTtostdSimplex (y k)).val-
        (TTtostdSimplex (room_point_seq f (l k))).val‖ ≤ _
      rw [pi_norm_le_iff_of_nonneg (by positivity)]
      intro j
      have ha := hgap k (y k) (hy k) j
      have hb := hgap k _ (hpoint k) j
      have hc := hcard k
      have he : |((y k) j : ℤ)-((room_point_seq f (l k)) j : ℤ)| < 2*(n+1) := by
        rw [abs_lt]; omega
      simp only [TTtostdSimplex,Pi.sub_apply,Real.norm_eq_abs,PNat.mk_coe,Nat.cast_add,Nat.cast_one]
      rw [← sub_div,abs_div,abs_of_pos (by positivity : (0 : ℝ)<(l k : ℝ)+1)]
      apply le_of_lt
      apply (div_lt_div_iff_of_pos_right (by positivity)).mpr
      exact_mod_cast he
    have hv := hz.congr_dist (hd.congr' (Eventually.of_forall fun _ => dist_comm _ _))
    have hcoord : Continuous (fun x : stdSimplex ℝ (Fin n) => x.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    apply le_of_tendsto_of_tendsto (hcoord.continuousAt.tendsto.comp hv)
      ((hcoord.comp hf).continuousAt.tendsto.comp hv)
    apply Eventually.of_forall
    intro k
    have hcolor : (stdSimplex.pick (v k) (f (v k))).val = i := hc k
    simpa only [hcolor,Set.mem_setOf_eq,Function.comp_apply] using (stdSimplex.pick (v k) (f (v k))).property
  have hz0 (i : Fin n) (hi : i ∉ C) : z.val i = 0 := by
    have hzero : Tendsto (fun k => (TTtostdSimplex (room_point_seq f (l k))).val i)
        atTop (𝓝 0) := by
      apply squeeze_zero
        (fun k => (TTtostdSimplex (room_point_seq f (l k))).property.1 i) _
        (tendsto_const_nhds.div_atTop ht :
          Tendsto (fun k => ((n : ℝ)+1)/((l k : ℝ)+1)) atTop (𝓝 0))
      intro k
      have hi' : i ∉ (room_seq f (l k)).1.2 := by aesop
      have hb := (hgap k _ (hpoint k) i).2
      simp only [if_neg hi',Nat.sub_zero] at hb
      
      have hc := hcard k
      simp only [TTtostdSimplex,Subtype.coe_mk,PNat.mk_coe,Nat.cast_add,Nat.cast_one]
      apply (div_le_div_iff_of_pos_right (by positivity)).mpr
      exact_mod_cast (show ((room_point_seq f (l k) : TT _ _) i : ℕ) ≤ n+1 by omega)
    exact tendsto_nhds_unique
      (((continuous_apply i).comp continuous_subtype_val).continuousAt.tendsto.comp hz) hzero
  have hle (i : Fin n) : z.val i ≤ (f z).val i := by
    by_cases hi : i ∈ C
    · exact hge i hi
    · rw [hz0 i hi]
      exact (f z).property.1 i
  refine ⟨z,Subtype.ext (funext fun i => ?_)⟩
  exact (((Finset.sum_eq_sum_iff_of_le fun i _ => hle i).mp
    (by rw [z.property.2,(f z).property.2])) i (Finset.mem_univ i)).symm

end Brouwer
