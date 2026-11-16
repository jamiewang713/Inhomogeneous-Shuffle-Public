import RiffleLowerV2.Shared.Geometry

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open Set
namespace RiffleLowerV2.Targets
open TimeProfile

def ColdWitnessTarget : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ T eta rho chiGood density : ℝ,
    0 < T → 0 < eta → 0 < rho → 0 < chiGood → 0 < density →
    2*rho*Real.log k ≤ kappa eta/100 →
    ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
    ∀ (cuts : Cuts k N (horizonDepth N T)) (hN : 0 < N),
      eta ≤ lambda1 cuts hN → beta cuts hN (horizon N (horizonDepth N T)) < kappa0 eta →
      LocalGood cuts hN chiGood density rho 0 T →
      ∃ W : ColdWitnessData, WitnessSpec cuts hN eta rho chiGood W

def RoundedTypeTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ C : ℝ, 0 ≤ C →
  ∃ Ctype : ℝ, 0 < Ctype ∧ ∀ T xi : ℝ, 0 < T → 0 < xi → xi < 1/(4*(k : ℝ)) →
  ∀ m : ℕ, ∃ Cround : ℝ, 0 < Cround ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
  ∀ N K : ℕ, N0 ≤ N → ∀ (P : BorelPartition k), P.cellCount = m →
  P.IsRegular xi C → ∀ (cuts : Cuts k N K) (hN : 0 < N) (I : Finset (Fin K)),
  (I.card : ℝ) ≤ T*logScale N → ∀ alpha ∈ Icc (2 : ℝ) 4,
  ∃ D : RoundedTypeData P, TypeDataSpec cuts hN P I xi alpha D ∧
    TypeApproximation cuts hN P I alpha
      (Ctype*T*xi*Real.log (1/xi) + Cround*(Real.log (logScale N)+1)/logScale N) D

def LocalizationTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T eta rho chiGood xi : ℝ,
  0 < T → 0 < eta → 0 < rho → 0 < chiGood → 0 < xi →
  ∀ (P : BorelPartition k) (epsilon : ℝ), 0 < epsilon →
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
  ∀ (cuts : Cuts k N (horizonDepth N T)) (hN : 0 < N) (W : ColdWitnessData)
    (G : ColdGeometryData (horizonDepth N T) P W),
  WitnessSpec cuts hN eta rho chiGood W → GeometrySpec cuts hN eta rho chiGood xi P W G →
  1-epsilon ≤ probability (fixedCountPMF cuts) (ColdLocalization hN P W G)

def ColdGeometryFromEmpiricalTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T eta rho chiGood density : ℝ,
  0 < T → 0 < eta → 0 < rho → 0 < chiGood → 0 < density →
  2*rho*Real.log k ≤ kappa0 eta/100 →
  ∃ xi : ℝ, 0 < xi ∧ xi < 1/(4*(k : ℝ)) ∧
  ∃ P : BorelPartition k, P.IsRegular xi 1 ∧
  ∀ epsilon : ℝ, 0 < epsilon → ∃ N0 : ℕ, 2 ≤ N0 ∧
  ∀ N : ℕ, N0 ≤ N → ∀ (cuts : Cuts k N (horizonDepth N T)) (hN : 0 < N),
  eta ≤ lambda1 cuts hN → beta cuts hN (horizon N (horizonDepth N T)) < kappa0 eta →
  LocalGood cuts hN chiGood density rho 0 T →
  ∃ (W : ColdWitnessData) (G : ColdGeometryData (horizonDepth N T) P W),
    WitnessSpec cuts hN eta rho chiGood W ∧ GeometrySpec cuts hN eta rho chiGood xi P W G ∧
    1-epsilon ≤ probability (fixedCountPMF cuts) (ColdLocalization hN P W G)

def OneColumnTiltTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ p : Simplex k,
  ContinuousOn (tiltedCost p) (Icc (2 : ℝ) 4) ∧
  AntitoneOn (tiltedCost p) (Icc (2 : ℝ) 4) ∧
  ContinuousOn (tiltedEntropy p) (Icc (2 : ℝ) 4) ∧
  ContinuousOn (psi p) (Icc (2 : ℝ) 4) ∧
  (∀ alpha ∈ Icc (2 : ℝ) 4,
    0 ≤ tiltedEntropy p alpha ∧ tiltedEntropy p alpha ≤ tiltedCost p alpha ∧
    tiltedCost p alpha ≤ Real.log k ∧ maxCost p ≤ tiltedCost p alpha ∧
    0 ≤ psi p alpha ∧ psi p alpha ≤ (alpha-1)*Real.log k ∧
    tiltedEntropy p alpha = alpha*tiltedCost p alpha - psi p alpha) ∧
  psi p 2 ≤ 2*maxCost p ∧ 2*psi p 2 ≤ psi p 4

def EmpiricalTiltTarget : Prop :=
  ∀ k N K : ℕ, 2 ≤ k → 2 ≤ N → ∀ (cuts : Cuts k N K) (hN : 0 < N),
  ∀ alpha ∈ Icc (2 : ℝ) 4, ∀ r s : ℝ,
  0 ≤ r → r ≤ s → s ≤ horizon N K →
  0 ≤ J cuts hN alpha r s ∧ J cuts hN alpha r s ≤ (s-r)*Real.log k ∧
  0 ≤ H cuts hN alpha r s ∧ H cuts hN alpha r s ≤ J cuts hN alpha r s ∧
  H cuts hN alpha r s = alpha*J cuts hN alpha r s - B cuts hN alpha r s

def LB05Target : Prop := OneColumnTiltTarget ∧ EmpiricalTiltTarget ∧ ColdWitnessTarget

def RelativeEndpointTarget : Prop :=
  ∀ k N K : ℕ, ∀ (cuts : Cuts k N K) (a : Word k K) (l m : ℕ),
  l ≤ m → m ≤ K → ∀ (x : WordOn k (columnSet K l m)) (omega : Sample cuts),
  let muA := prefixMean cuts (prefixAt l a)
  let tx := relativeMassBefore cuts x
  let dx := massOn cuts x
  ((relativeLowerCount a l m x omega : ℝ)-muA*tx =
    ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => d < x j),
      ((prefixCount (sidePrefix a l m x j d) omega : ℝ) -
        prefixMean cuts (sidePrefix a l m x j d))) ∧
  ((relativeUpperCount a l m x omega : ℝ)-muA*(tx+dx) =
    ((prefixCount (prefixAt l a) omega : ℝ)-muA) -
    ∑ j : columnSet K l m, ∑ d ∈ Finset.univ.filter (fun d : Fin k => x j < d),
      ((prefixCount (sidePrefix a l m x j d) omega : ℝ) -
        prefixMean cuts (sidePrefix a l m x j d))) ∧
  (∀ A : ℝ, 0 < A →
    (∀ v : Prefix k K, |(prefixCount v omega : ℝ)-prefixMean cuts v| ≤
      A*(Real.sqrt (prefixMean cuts v)+1)) →
    |(relativeLowerCount a l m x omega : ℝ)-muA*tx| +
    |(relativeUpperCount a l m x omega : ℝ)-muA*(tx+dx)| ≤
      A*((2*Real.sqrt ((k : ℝ)*K)+1)*Real.sqrt muA + 2*(k : ℝ)*K+1))

def DeterministicColdGeometryTarget : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∀ T eta rho chiGood : ℝ,
  0 < T → 0 < eta → 0 < rho → 0 < chiGood →
  2*rho*Real.log k ≤ kappa0 eta/100 →
  ∃ xi : ℝ, 0 < xi ∧ xi < 1/(4*(k : ℝ)) ∧
  ∃ P : BorelPartition k, P.IsRegular xi 1 ∧
  ∃ N0 : ℕ, 2 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
  ∀ (cuts : Cuts k N (horizonDepth N T)) (hN : 0 < N) (W : ColdWitnessData),
  WitnessSpec cuts hN eta rho chiGood W →
  ∃ G : ColdGeometryData (horizonDepth N T) P W,
    GeometrySpec cuts hN eta rho chiGood xi P W G

def LB09Target : Prop :=
  RelativeEndpointTarget ∧ DeterministicColdGeometryTarget ∧
  LocalizationTarget ∧ ColdGeometryFromEmpiricalTarget

end RiffleLowerV2.Targets
