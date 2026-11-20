module

public import QPBT.Palomar.PauliCompleteness
public import QPBT.Palomar.LowDegreeSoundness
public import QPBT.Palomar.PauliSoundness
public import QPBT.Test.AxiomAudit
import QPBT.Algebra.FieldBasis
import QPBT.Algebra.Pauli
import QPBT.Combining.Defs
import QPBT.Combining.DirectLowDegree.AnyStrategySoundness
import QPBT.Combining.DirectLowDegree.Game
import QPBT.Combining.DirectLowDegree.Geometry
import QPBT.Combining.DirectLowDegree.Transport.BranchComparison
import QPBT.Combining.DirectLowDegree.Transport.Combining.Coefficients
import QPBT.Combining.DirectLowDegree.Transport.Combining.Linearity
import QPBT.Combining.DirectLowDegree.Transport.Combining.Parameters
import QPBT.Combining.DirectLowDegree.Transport.Combining.Polynomial
import QPBT.Combining.DirectLowDegree.Transport.Combining.QuestionLaw
import QPBT.Combining.DirectLowDegree.Transport.Combining.RecoveryTransport
import QPBT.Combining.DirectLowDegree.Transport.Combining.Restriction
import QPBT.Combining.DirectLowDegree.Transport.Combining.Strategy
import QPBT.Combining.DirectLowDegree.Transport.Combining.WinPredicate
import QPBT.Combining.DirectLowDegree.Transport.Consistency.Compression
import QPBT.Combining.DirectLowDegree.Transport.Consistency.Measurements
import QPBT.Combining.DirectLowDegree.Transport.Consistency.State
import QPBT.Combining.DirectLowDegree.Transport.Correspondence
import QPBT.Combining.DirectLowDegree.Transport.LineResampling
import QPBT.Combining.DirectLowDegree.Transport.SeedFiber
import QPBT.Combining.DirectLowDegree.Transport.Strategy
import QPBT.Combining.ExtendedLineGame.PairMeasurement
import QPBT.Combining.ExtendedLineGame.PointPointRejection
import QPBT.Combining.Lines.CombinedMeasurement
import QPBT.Combining.Lines.Construction
import QPBT.Combining.Lines.SubLineBlocks
import QPBT.Combining.Lines.SubLineSeed
import QPBT.Combining.Lines.SubLineSupport
import QPBT.Combining.PairCompletion
import QPBT.Combining.Points.PlacementSupport
import QPBT.Combining.Points.Sandwich
import QPBT.Combining.UniformLinePoint
import QPBT.Extraction.BlockMeasurement
import QPBT.Extraction.EncodingSupport
import QPBT.Extraction.NonencodingSupport
import QPBT.Games.CondLinear
import QPBT.Games.CondLinearTheorems
import QPBT.Games.CondLinearTheorems.Reindex
import QPBT.Games.Defs
import QPBT.Games.DistanceTheorems.ProjectiveRounding
import QPBT.Games.DistanceTheorems.Support
import QPBT.Games.DistanceTheorems.TensorSupport
import QPBT.Games.MeasurementCompression
import QPBT.Games.Sandwich.Defs
import QPBT.Games.StrategyClasses
import QPBT.Observables.Anticommuting
import QPBT.Observables.Defs
import QPBT.Observables.ExpandedDefs
import QPBT.Observables.LineDefs
import QPBT.Observables.LineMeasurement
import QPBT.Observables.LineMeasurement.Expanded
import QPBT.Observables.LineMeasurement.Projector
import QPBT.Observables.PointConsistency
import QPBT.Observables.WinImplications.Approx
import QPBT.Observables.WinImplications.ApproxLines
import QPBT.Observables.WinImplications.Averages
import QPBT.Observables.WinImplications.CommutingObs
import QPBT.Observables.WinImplications.InterchangedCommutation
import QPBT.Observables.WinImplications.LowDegree
import QPBT.Observables.WinImplications.PointObs
import QPBT.Observables.WinImplications.Setup
import QPBT.Observables.WinImplications.TwistedCommutation
import QPBT.Palomar.Bridge
import QPBT.Palomar.Definitions
import QPBT.Palomar.ExtractionBridge
import QPBT.Palomar.LowDegreeConsistencyBridge
import QPBT.Palomar.LowDegreeGameBridge
import QPBT.Palomar.LowDegreeGameStrategyBridge
import QPBT.Palomar.PauliExtractionBridge
import QPBT.Palomar.PauliGameBridge
import QPBT.Palomar.PauliGameStrategyBridge
import QPBT.Test.Completeness.HonestStrategy
import QPBT.Test.LowDegreeGame
import QPBT.Test.LowDegreeGameMeasurements
import QPBT.Test.MagicSquare
import QPBT.Test.MagicSquareTheorems
import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Measurements
import QPBT.Test.MagicSquareTheorems.PerfectStrategy.Observables
import QPBT.Test.MagicSquareTheorems.Rigidity.Constants
import QPBT.Test.MagicSquareTheorems.Rigidity.Dilation
import QPBT.Test.MagicSquareTheorems.Rigidity.IdealTarget
import QPBT.Test.MagicSquareTheorems.Rigidity.Relations
import QPBT.Test.MagicSquareTheorems.Rigidity.Swap
import QPBT.Test.MagicSquareTheorems.Rigidity.TwoQubitSwap
import QPBT.Test.PauliBasisTest
import QPBT.Test.QubitForm
import QPBT.Test.Soundness.NaimarkReduction
import QPBT.Test.SoundnessDefs

/-! # Verified quantum Pauli basis test results

The Solution supplies the four registered theorems and the fixed-field construction.
The imported axiom audit fails the build if any registered result uses an unexpected axiom.
-/
