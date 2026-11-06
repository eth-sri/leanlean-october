module

public import OAI.NumberTheory.DirichletL.Moments.CommonLinearNormalization

@[expose] public section

namespace OAI

noncomputable section
open scoped Classical

namespace SevenEighths.CenteredMomentCommonPairedSource
open UniqueFactorizationMonoid CanonicalQuadraticSieve
open CenteredMomentCommonLinearSource CenteredMomentCommonLinearNormalization
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum
open CenteredMomentExceptionalMaskedSource CenteredMomentExceptionalAmplitudePair
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def normalizedColumn (s:Input ι)(C:Ideal HeckeFamily.O)(hC:Supported C)(R seed L:Ideal HeckeFamily.O)(z:HeckeFamily.O):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*sourceColumn s C hC R seed L z

theorem norm_column (s:Input ι)(C:Ideal HeckeFamily.O)(hC:Supported C)(R seed L:Ideal HeckeFamily.O)
    (hseed:seed∣C)(z:HeckeFamily.O):
    ‖normalizedColumn s C hC R seed L z‖≤
      ∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖:=by
  unfold normalizedColumn
  rw [source_normalized s C hC R seed L hseed]
  simpa using norm_sum_le
    (Finset.univ:Finset (actualAllocations s.pools C))
    (fun B=>commonScalar s C R B*maskedAmplitude (commonData s C R B) L z)

theorem paired_columns (s:Input ι)(v:Input κ)(C D:Ideal HeckeFamily.O)(hC:Supported C)(hD:Supported D)
    (R seed L:Ideal HeckeFamily.O)(hsC:seed∣C)(hsD:seed∣D)(rows:Finset HeckeFamily.O):
    (∑z∈rows,‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑z∈rows,(∑B:actualAllocations s.pools C,‖commonScalar s C R B‖*
        ‖maskedAmplitude (commonData s C R B) L z‖)*
      (∑E:actualAllocations v.pools D,‖commonScalar v D R E‖*
        ‖maskedAmplitude (commonData v D R E) L z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul (norm_column s C hC R seed L hsC z)
        (norm_column v D hD R seed L hsD z) (norm_nonneg _)
        (by positivity)
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=Finset.univ)]
      rw [Finset.sum_comm]
      grind

theorem whole_paired_columns (s:Input ι)(v:Input κ)(C D:Ideal HeckeFamily.O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal HeckeFamily.O)(hsC:seed∣C)(hsD:seed∣D)(Ds:Finset (Ideal HeckeFamily.O))(rows:Finset HeckeFamily.O):
    (∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
      ‖normalizedColumn s C hC R seed L z‖*‖normalizedColumn v D hD R seed L z‖)≤
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑L∈Ds,‖(moebius L:ℂ)‖*∑z∈rows,
            ‖maskedAmplitude (commonData s C R B) L z‖*
              ‖maskedAmplitude (commonData v D R E) L z‖:=by
  calc
    _≤∑L∈Ds,‖(moebius L:ℂ)‖*
      ∑B:actualAllocations s.pools C,∑E:actualAllocations v.pools D,
        (‖commonScalar s C R B‖*‖commonScalar v D R E‖)*
          ∑z∈rows,‖maskedAmplitude (commonData s C R B) L z‖*
            ‖maskedAmplitude (commonData v D R E) L z‖:=
      Finset.sum_le_sum (fun L hL=>mul_le_mul_of_nonneg_left
        (paired_columns s v C D hC hD R seed L hsC hsD rows) (norm_nonneg _))
    _=_:=by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.sum_comm]
      grind

end SevenEighths.CenteredMomentCommonPairedSource

end

end OAI
