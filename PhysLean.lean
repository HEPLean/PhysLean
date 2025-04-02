import PhysLean.ClassicalMechanics.Basic
import PhysLean.ClassicalMechanics.HarmonicOscillator.Basic
import PhysLean.ClassicalMechanics.HarmonicOscillator.Solution
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
import PhysLean.Particles.StandardModel.Basic
import PhysLean.Particles.StandardModel.HiggsBoson.Basic
import PhysLean.Particles.StandardModel.HiggsBoson.GaugeAction
import PhysLean.Particles.StandardModel.HiggsBoson.PointwiseInnerProd
import PhysLean.Particles.StandardModel.HiggsBoson.Potential
import PhysLean.Particles.StandardModel.Representations
import PhysLean.QFT.AnomalyCancellation.Basic
import PhysLean.QFT.AnomalyCancellation.GroupActions
import PhysLean.QFT.AnomalyCancellation.MSSMNu.B3
import PhysLean.QFT.AnomalyCancellation.MSSMNu.Basic
import PhysLean.QFT.AnomalyCancellation.MSSMNu.HyperCharge
import PhysLean.QFT.AnomalyCancellation.MSSMNu.LineY3B3
import PhysLean.QFT.AnomalyCancellation.MSSMNu.OrthogY3B3.Basic
import PhysLean.QFT.AnomalyCancellation.MSSMNu.OrthogY3B3.PlaneWithY3B3
import PhysLean.QFT.AnomalyCancellation.MSSMNu.OrthogY3B3.ToSols
import PhysLean.QFT.AnomalyCancellation.MSSMNu.Permutations
import PhysLean.QFT.AnomalyCancellation.MSSMNu.Y3
import PhysLean.QFT.AnomalyCancellation.PureU1.Basic
import PhysLean.QFT.AnomalyCancellation.PureU1.BasisLinear
import PhysLean.QFT.AnomalyCancellation.PureU1.ConstAbs
import PhysLean.QFT.AnomalyCancellation.PureU1.Even.BasisLinear
import PhysLean.QFT.AnomalyCancellation.PureU1.Even.LineInCubic
import PhysLean.QFT.AnomalyCancellation.PureU1.Even.Parameterization
import PhysLean.QFT.AnomalyCancellation.PureU1.LineInPlaneCond
import PhysLean.QFT.AnomalyCancellation.PureU1.LowDim.One
import PhysLean.QFT.AnomalyCancellation.PureU1.LowDim.Three
import PhysLean.QFT.AnomalyCancellation.PureU1.LowDim.Two
import PhysLean.QFT.AnomalyCancellation.PureU1.Odd.BasisLinear
import PhysLean.QFT.AnomalyCancellation.PureU1.Odd.LineInCubic
import PhysLean.QFT.AnomalyCancellation.PureU1.Odd.Parameterization
import PhysLean.QFT.AnomalyCancellation.PureU1.Permutations
import PhysLean.QFT.AnomalyCancellation.PureU1.Sorts
import PhysLean.QFT.AnomalyCancellation.PureU1.VectorLike
import PhysLean.QFT.AnomalyCancellation.SM.Basic
import PhysLean.QFT.AnomalyCancellation.SM.FamilyMaps
import PhysLean.QFT.AnomalyCancellation.SM.NoGrav.Basic
import PhysLean.QFT.AnomalyCancellation.SM.NoGrav.One.Lemmas
import PhysLean.QFT.AnomalyCancellation.SM.NoGrav.One.LinearParameterization
import PhysLean.QFT.AnomalyCancellation.SM.Permutations
import PhysLean.QFT.AnomalyCancellation.SMNu.Basic
import PhysLean.QFT.AnomalyCancellation.SMNu.FamilyMaps
import PhysLean.QFT.AnomalyCancellation.SMNu.NoGrav.Basic
import PhysLean.QFT.AnomalyCancellation.SMNu.Ordinary.Basic
import PhysLean.QFT.AnomalyCancellation.SMNu.Ordinary.DimSevenPlane
import PhysLean.QFT.AnomalyCancellation.SMNu.Ordinary.FamilyMaps
import PhysLean.QFT.AnomalyCancellation.SMNu.Permutations
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.BMinusL
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.Basic
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.BoundPlaneDim
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.FamilyMaps
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.HyperCharge
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.PlaneNonSols
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.QuadSol
import PhysLean.QFT.AnomalyCancellation.SMNu.PlusU1.QuadSolToSol
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
import PhysLean.QuantumMechanics.FiniteTarget.Basic
import PhysLean.QuantumMechanics.OneDimension.GeneralPotential.Basic
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Basic
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Completeness
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.Eigenfunction
import PhysLean.QuantumMechanics.OneDimension.HarmonicOscillator.TISE
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Basic
import PhysLean.QuantumMechanics.OneDimension.HilbertSpace.Parity
import PhysLean.Relativity.Lorentz.Algebra.Basic
import PhysLean.Relativity.Lorentz.Algebra.Basis
import PhysLean.Relativity.Lorentz.Bispinors.Basic
import PhysLean.Relativity.Lorentz.ComplexTensor.Basic
import PhysLean.Relativity.Lorentz.ComplexTensor.Basis
import PhysLean.Relativity.Lorentz.ComplexTensor.Lemmas
import PhysLean.Relativity.Lorentz.ComplexTensor.Metrics.Basic
import PhysLean.Relativity.Lorentz.ComplexTensor.Metrics.Basis
import PhysLean.Relativity.Lorentz.ComplexTensor.Metrics.Lemmas
import PhysLean.Relativity.Lorentz.ComplexTensor.OfRat
import PhysLean.Relativity.Lorentz.ComplexTensor.Units.Basic
import PhysLean.Relativity.Lorentz.ComplexTensor.Units.Basis
import PhysLean.Relativity.Lorentz.ComplexTensor.Units.Symm
import PhysLean.Relativity.Lorentz.ComplexVector.Basic
import PhysLean.Relativity.Lorentz.ComplexVector.Contraction
import PhysLean.Relativity.Lorentz.ComplexVector.Metric
import PhysLean.Relativity.Lorentz.ComplexVector.Modules
import PhysLean.Relativity.Lorentz.ComplexVector.Two
import PhysLean.Relativity.Lorentz.ComplexVector.Unit
import PhysLean.Relativity.Lorentz.Group.Basic
import PhysLean.Relativity.Lorentz.Group.Boosts.Basic
import PhysLean.Relativity.Lorentz.Group.Boosts.Generalized
import PhysLean.Relativity.Lorentz.Group.Orthochronous
import PhysLean.Relativity.Lorentz.Group.Proper
import PhysLean.Relativity.Lorentz.Group.Restricted
import PhysLean.Relativity.Lorentz.Group.Rotations
import PhysLean.Relativity.Lorentz.MinkowskiMatrix
import PhysLean.Relativity.Lorentz.PauliMatrices.AsTensor
import PhysLean.Relativity.Lorentz.PauliMatrices.Basic
import PhysLean.Relativity.Lorentz.PauliMatrices.Basis
import PhysLean.Relativity.Lorentz.PauliMatrices.Matrix
import PhysLean.Relativity.Lorentz.PauliMatrices.Relations
import PhysLean.Relativity.Lorentz.PauliMatrices.SelfAdjoint
import PhysLean.Relativity.Lorentz.RealTensor.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Derivative
import PhysLean.Relativity.Lorentz.RealTensor.Matrix.Pre
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Pre
import PhysLean.Relativity.Lorentz.RealTensor.Units.Pre
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Boosts
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Causality
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.Basic
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.Contraction
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.Modules
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Pre.NormOne
import PhysLean.Relativity.Lorentz.SL2C.Basic
import PhysLean.Relativity.Lorentz.SL2C.SelfAdjoint
import PhysLean.Relativity.Lorentz.Weyl.Basic
import PhysLean.Relativity.Lorentz.Weyl.Contraction
import PhysLean.Relativity.Lorentz.Weyl.Metric
import PhysLean.Relativity.Lorentz.Weyl.Modules
import PhysLean.Relativity.Lorentz.Weyl.Two
import PhysLean.Relativity.Lorentz.Weyl.Unit
import PhysLean.Relativity.SpaceTime.Basic
import PhysLean.Relativity.SpaceTime.CliffordAlgebra
import PhysLean.Relativity.SpaceTime.ProperTime
import PhysLean.Relativity.Special.TwinParadox.Basic
import PhysLean.Relativity.Tensors.OverColor.Basic
import PhysLean.Relativity.Tensors.OverColor.Discrete
import PhysLean.Relativity.Tensors.OverColor.Functors
import PhysLean.Relativity.Tensors.OverColor.Iso
import PhysLean.Relativity.Tensors.OverColor.Lift
import PhysLean.Relativity.Tensors.TensorSpecies.Basic
import PhysLean.Relativity.Tensors.TensorSpecies.Basis
import PhysLean.Relativity.Tensors.TensorSpecies.Contractions.Basic
import PhysLean.Relativity.Tensors.TensorSpecies.Contractions.Categorical
import PhysLean.Relativity.Tensors.TensorSpecies.Contractions.ContrMap
import PhysLean.Relativity.Tensors.TensorSpecies.DualRepIso
import PhysLean.Relativity.Tensors.TensorSpecies.MetricTensor
import PhysLean.Relativity.Tensors.TensorSpecies.OfInt
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Basic
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Contraction
import PhysLean.Relativity.Tensors.TensorSpecies.Tensor.Evaluation
import PhysLean.Relativity.Tensors.TensorSpecies.UnitTensor
import PhysLean.Relativity.Tensors.Tree.Basic
import PhysLean.Relativity.Tensors.Tree.Dot
import PhysLean.Relativity.Tensors.Tree.Elab
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.Assoc
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.Basic
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.Congr
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ContrContr
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ContrSwap
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.PermContr
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.PermProd
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdAssoc
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdComm
import PhysLean.Relativity.Tensors.Tree.NodeIdentities.ProdContr
import PhysLean.StatisticalMechanics.Basic
import PhysLean.Thermodynamics.Basic
