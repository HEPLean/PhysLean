import PhysLean.ClassicalMechanics.Basic
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
import PhysLean.ClassicalMechanics.HarmonicOscillator.Solution
import PhysLean.ClassicalMechanics.Momentum.Basic
import PhysLean.ClassicalMechanics.Space.Basic
import PhysLean.ClassicalMechanics.Space.VectorIdentities
import PhysLean.ClassicalMechanics.Time.Basic
import PhysLean.ClassicalMechanics.Time.Second
import PhysLean.CondensedMatter.Basic
import PhysLean.Cosmology.Basic
import PhysLean.Cosmology.FLRW.Basic
import PhysLean.Electromagnetism.Basic
import PhysLean.Electromagnetism.FieldStrength.Basic
import PhysLean.Electromagnetism.FieldStrength.Derivative
import PhysLean.Electromagnetism.LorentzAction
import PhysLean.Electromagnetism.MaxwellEquations
import PhysLean.Mathematics.Fin
import PhysLean.Mathematics.Fin.Involutions
import PhysLean.Mathematics.LinearMaps
import PhysLean.Mathematics.List
import PhysLean.Mathematics.List.InsertIdx
import PhysLean.Mathematics.List.InsertionSort
import PhysLean.Mathematics.PiTensorProduct
import PhysLean.Mathematics.RatComplexNum
import PhysLean.Mathematics.SO3.Basic
import PhysLean.Mathematics.SchurTriangulation
import PhysLean.Mathematics.SpecialFunctions.PhysHermite
import PhysLean.Meta.AllFilePaths
import PhysLean.Meta.Basic
import PhysLean.Meta.Informal.Basic
import PhysLean.Meta.Informal.Post
import PhysLean.Meta.Informal.SemiFormal
import PhysLean.Meta.Notes.Basic
import PhysLean.Meta.Notes.HTMLNote
import PhysLean.Meta.Notes.NoteFile
import PhysLean.Meta.Notes.ToHTML
import PhysLean.Meta.Remark.Basic
import PhysLean.Meta.Remark.Properties
import PhysLean.Meta.TODO.Basic
import PhysLean.Meta.TransverseTactics
import PhysLean.Optics.Basic
import PhysLean.Particles.BeyondTheStandardModel.GeorgiGlashow.Basic
import PhysLean.Particles.BeyondTheStandardModel.PatiSalam.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.NoGrav.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.DimSevenPlane
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Ordinary.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Permutations
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BMinusL
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.Basic
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.BoundPlaneDim
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.FamilyMaps
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.HyperCharge
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.PlaneNonSols
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.QuadSol
import PhysLean.Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.PlusU1.QuadSolToSol
import PhysLean.Particles.BeyondTheStandardModel.Spin10.Basic
import PhysLean.Particles.BeyondTheStandardModel.TwoHDM.Basic
import PhysLean.Particles.BeyondTheStandardModel.TwoHDM.GaugeOrbits
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Basic
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Invariants
import PhysLean.Particles.FlavorPhysics.CKMMatrix.PhaseFreedom
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Relations
import PhysLean.Particles.FlavorPhysics.CKMMatrix.Rows
import PhysLean.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.Basic
import PhysLean.Particles.FlavorPhysics.CKMMatrix.StandardParameterization.StandardParameters
import PhysLean.Particles.StandardModel.AnomalyCancellation.Basic
import PhysLean.Particles.StandardModel.AnomalyCancellation.FamilyMaps
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.Basic
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.One.Lemmas
import PhysLean.Particles.StandardModel.AnomalyCancellation.NoGrav.One.LinearParameterization
import PhysLean.Particles.StandardModel.AnomalyCancellation.Permutations
import PhysLean.Particles.StandardModel.Basic
import PhysLean.Particles.StandardModel.HiggsBoson.Basic
import PhysLean.Particles.StandardModel.HiggsBoson.GaugeAction
import PhysLean.Particles.StandardModel.HiggsBoson.PointwiseInnerProd
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import PhysLean.Particles.StandardModel.Representations
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Basic
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.HyperCharge
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.LineY3B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.Basic
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.PlaneWithY3B3
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.OrthogY3B3.ToSols
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Permutations
import PhysLean.Particles.SuperSymmetry.MSSMNu.AnomalyCancellation.Y3
import PhysLean.QFT.AnomalyCancellation.Basic
import PhysLean.QFT.AnomalyCancellation.GroupActions
import PhysLean.QFT.PerturbationTheory.CreateAnnihilate
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Basic
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Instances.ComplexScalar
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Instances.Phi4
import PhysLean.QFT.PerturbationTheory.FeynmanDiagrams.Momentum
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.Basic
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.Grading
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.NormalOrder.Basic
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.NormalOrder.Lemmas
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.NormalOrder.WickContractions
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.StaticWickTerm
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.StaticWickTheorem
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.SuperCommute
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.TimeContraction
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.TimeOrder
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.Universality
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.WickTerm
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.WicksTheorem
import PhysLean.QFT.PerturbationTheory.FieldOpAlgebra.WicksTheoremNormal
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.Basic
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.Grading
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.NormTimeOrder
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.NormalOrder
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.SuperCommute
import PhysLean.QFT.PerturbationTheory.FieldOpFreeAlgebra.TimeOrder
import PhysLean.QFT.PerturbationTheory.FieldSpecification.Basic
import PhysLean.QFT.PerturbationTheory.FieldSpecification.CrAnFieldOp
import PhysLean.QFT.PerturbationTheory.FieldSpecification.CrAnSection
import PhysLean.QFT.PerturbationTheory.FieldSpecification.Filters
import PhysLean.QFT.PerturbationTheory.FieldSpecification.NormalOrder
import PhysLean.QFT.PerturbationTheory.FieldSpecification.TimeOrder
import PhysLean.QFT.PerturbationTheory.FieldStatistics.Basic
import PhysLean.QFT.PerturbationTheory.FieldStatistics.ExchangeSign
import PhysLean.QFT.PerturbationTheory.FieldStatistics.OfFinset
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSign
import PhysLean.QFT.PerturbationTheory.Koszul.KoszulSignInsert
import PhysLean.QFT.PerturbationTheory.WickContraction.Basic
import PhysLean.QFT.PerturbationTheory.WickContraction.Card
import PhysLean.QFT.PerturbationTheory.WickContraction.Erase
import PhysLean.QFT.PerturbationTheory.WickContraction.ExtractEquiv
import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContract
import PhysLean.QFT.PerturbationTheory.WickContraction.InsertAndContractNat
import PhysLean.QFT.PerturbationTheory.WickContraction.Involutions
import PhysLean.QFT.PerturbationTheory.WickContraction.IsFull
import PhysLean.QFT.PerturbationTheory.WickContraction.Join
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.Basic
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertNone
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.InsertSome
import PhysLean.QFT.PerturbationTheory.WickContraction.Sign.Join
import PhysLean.QFT.PerturbationTheory.WickContraction.Singleton
import PhysLean.QFT.PerturbationTheory.WickContraction.StaticContract
import PhysLean.QFT.PerturbationTheory.WickContraction.SubContraction
import PhysLean.QFT.PerturbationTheory.WickContraction.TimeCond
import PhysLean.QFT.PerturbationTheory.WickContraction.TimeContract
import PhysLean.QFT.PerturbationTheory.WickContraction.Uncontracted
import PhysLean.QFT.PerturbationTheory.WickContraction.UncontractedList
import PhysLean.QFT.QED.AnomalyCancellation.Basic
import PhysLean.QFT.QED.AnomalyCancellation.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.ConstAbs
import PhysLean.QFT.QED.AnomalyCancellation.Even.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.Even.LineInCubic
import PhysLean.QFT.QED.AnomalyCancellation.Even.Parameterization
import PhysLean.QFT.QED.AnomalyCancellation.LineInPlaneCond
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.One
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.Three
import PhysLean.QFT.QED.AnomalyCancellation.LowDim.Two
import PhysLean.QFT.QED.AnomalyCancellation.Odd.BasisLinear
import PhysLean.QFT.QED.AnomalyCancellation.Odd.LineInCubic
import PhysLean.QFT.QED.AnomalyCancellation.Odd.Parameterization
import PhysLean.QFT.QED.AnomalyCancellation.Permutations
import PhysLean.QFT.QED.AnomalyCancellation.Sorts
import PhysLean.QFT.QED.AnomalyCancellation.VectorLike
import PhysLean.QuantumMechanics.FiniteTarget.Basic
import PhysLean.QuantumMechanics.OneDimension.GeneralPotential.Basic
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Basic
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Parity
import PhysLean.Relativity.Bispinors.Basic
import PhysLean.Relativity.Lorentz.Algebra.Basic
import PhysLean.Relativity.Lorentz.Algebra.Basis
import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Relativity.Lorentz.Group.Boosts.Basic
import PhysLean.Relativity.Lorentz.Group.Boosts.Generalized
import PhysLean.Relativity.Lorentz.Group.Orthochronous
import PhysLean.Relativity.Lorentz.Group.Proper
import PhysLean.Relativity.Lorentz.Group.Restricted
import PhysLean.Relativity.Lorentz.Group.Rotations
import PhysLean.Relativity.Lorentz.MinkowskiMatrix
import PhysLean.Relativity.PauliMatrices.AsTensor
import PhysLean.Relativity.PauliMatrices.Basic
import PhysLean.Relativity.PauliMatrices.Matrix
import PhysLean.Relativity.PauliMatrices.Relations
import PhysLean.Relativity.PauliMatrices.SelfAdjoint
import PhysLean.Relativity.SL2C.Basic
import PhysLean.Relativity.SL2C.SelfAdjoint
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.SpaceTime.CliffordAlgebra
import PhysLean.Relativity.SpaceTime.ProperTime
import PhysLean.Relativity.SpaceTime.TimeSlice
import PhysLean.Relativity.Special.TwinParadox.Basic
import PhysLean.Relativity.Tensors.Basic
import PhysLean.Relativity.Tensors.Color.Basic
import PhysLean.Relativity.Tensors.Color.Discrete
import PhysLean.Relativity.Tensors.Color.Lift
import PhysLean.Relativity.Tensors.ComplexTensor.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Lemmas
import PhysLean.Relativity.Tensors.ComplexTensor.Matrix.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Lemmas
import PhysLean.Relativity.Tensors.ComplexTensor.Metrics.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.OfRat
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Pre
import PhysLean.Relativity.Tensors.ComplexTensor.Units.Symm
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Contraction
import PhysLean.Relativity.Tensors.ComplexTensor.Vector.Pre.Modules
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Basic
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Contraction
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Metric
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Modules
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Two
import PhysLean.Relativity.Tensors.ComplexTensor.Weyl.Unit
import PhysLean.Relativity.Tensors.Constructors
import PhysLean.Relativity.Tensors.Contraction.Basic
import PhysLean.Relativity.Tensors.Contraction.Basis
import PhysLean.Relativity.Tensors.Contraction.Products
import PhysLean.Relativity.Tensors.Contraction.Pure
import PhysLean.Relativity.Tensors.Dual
import PhysLean.Relativity.Tensors.Elab
import PhysLean.Relativity.Tensors.Evaluation
import PhysLean.Relativity.Tensors.MetricTensor
import PhysLean.Relativity.Tensors.OfInt
import PhysLean.Relativity.Tensors.Product
import PhysLean.Relativity.Tensors.RealTensor.Basic
import PhysLean.Relativity.Tensors.RealTensor.Derivative
import PhysLean.Relativity.Tensors.RealTensor.Matrix.Pre
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Basic
import PhysLean.Relativity.Tensors.RealTensor.Metrics.Pre
import PhysLean.Relativity.Tensors.RealTensor.ToComplex
import PhysLean.Relativity.Tensors.RealTensor.Units.Pre
import PhysLean.Relativity.Tensors.RealTensor.Vector.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Boosts
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.LightLike
import PhysLean.Relativity.Tensors.RealTensor.Vector.Causality.TimeLike
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Basic
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Contraction
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.Modules
import PhysLean.Relativity.Tensors.RealTensor.Vector.Pre.NormOne
import PhysLean.Relativity.Tensors.TensorSpecies.Basic
import PhysLean.Relativity.Tensors.UnitTensor
import PhysLean.StatisticalMechanics.Basic
import PhysLean.Thermodynamics.Basic
