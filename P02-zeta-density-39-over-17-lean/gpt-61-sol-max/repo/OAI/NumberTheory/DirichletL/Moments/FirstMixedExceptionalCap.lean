module
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
import Mathlib
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondPaidLedger
public import OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
public import OAI.NumberTheory.DirichletL.Moments.FirstChildLower
public import OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalizationActual

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedExceptionalCap
open HeckeFamily CompletedGauss


open CenteredMomentFirstMixedAllowance

open CenteredMomentFirstPhysicalSource CenteredMomentFirstExceptionalPrefactor




open CenteredMomentSecondHeightFamily
open scoped HeckeO
variable {ι:Type*}[Fintype ι]

local instance {κ:Type*}:DecidableEq κ:=Classical.decEq _

lemma fixed_presentation_log_nonneg (Z:ℝ)(hZ:1<Z):0≤Real.logb Z fixedPresentationCost:=by
  have h₁:(1:ℝ)≤((Ideal.span {fixedBadMask}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
  have h₂:(1:ℝ)≤((Ideal.span {(72:O)}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr (by norm_num)))
  apply Real.logb_nonneg hZ
  unfold fixedPresentationCost
  nlinarith

lemma extracted_allowance_eq (C D:Ideal O)(hC:C≠0)(hD:D≠0)
    (hCD:primeSupport C=primeSupport D)(Z:ℝ):extractedAllowance C D Z=allowance C D Z:=by
  simp only [extractedAllowance,allowance,commonPart_of_equal_support C D hC hCD,
    commonPart_of_equal_support D C hD hCD.symm]






