module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightChartJetsAndFlowWords
public import DedekindZetaZeroFree.Eisenstein.Continuation.LocalJointPoleClearingAndContinuity
public import DedekindZetaZeroFree.Eisenstein.Continuation.LocallyDiscretePoleLoci
public import DedekindZetaZeroFree.Eisenstein.Continuation.RegularSymmetriesAndUniformRightLevels
public import DedekindZetaZeroFree.Metaplectic.Intertwining.ComplexStandardIntertwinerGerm
public import DedekindZetaZeroFree.LFunctions.Hecke.EntireRegularizations
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveTrivialCharacter
public import DedekindZetaZeroFree.Eisenstein.Induction.ScalarCompactPicturesAndLocalQuotientTensors

@[expose] public section

noncomputable section

set_option maxHeartbeats 4000000

set_option synthInstance.maxHeartbeats 1000000

set_option backward.isDefEq.respectTransparency false

open scoped Classical NumberField

open NumberField IsDedekindDomain

noncomputable section

open scoped Classical NumberField

open DedekindZetaZeroFree

open _root_.DedekindZetaZeroFree.ScalarRationalProductTransport renaming scalar_injective → scalar_injective

namespace DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local notation "Q" => KPGlobalTorusBorelTwistCompatibility.rationalModel F ζ hζ

local notation "V" => KPGlobalTorusBorelTwistCompatibility.Induced F ζ hζ Q



































variable (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)



set_option maxHeartbeats 4000000

set_option backward.isDefEq.respectTransparency false






















end DedekindZetaZeroFree.KPGlobalResidualKernel.IntertwinerRegularization.FactorizationSources.NormalizedCoordinateAnalyticity

end

end
