import RiffleLowerV2.Shared.Statistics

noncomputable section
open scoped BigOperators
open Set
namespace RiffleLowerV2
open TimeProfile
attribute [local instance] Classical.propDecidable

/-! Variable-column words: unused coordinates do not contribute cardinality. -/
def columnSet (K a b : ℕ) : Finset (Fin K) :=
  Finset.univ.filter fun j => a ≤ j.val ∧ j.val < b
abbrev WordOn (k : ℕ) {K : ℕ} (I : Finset (Fin K)) := (j : I) → Fin k

def wordOnList {k K : ℕ} {I : Finset (Fin K)} (x : WordOn k I) : List (Fin k) :=
  (I.attach.sort (fun j l => j.val ≤ l.val)).map x

def massOn {k N K : ℕ} (cuts : Cuts k N K) {I : Finset (Fin K)}
    (x : WordOn k I) : ℝ :=
  ∏ j : I, (cuts.count j.val (x j) : ℝ) / N

def restrictWord {k K : ℕ} (I : Finset (Fin K)) (w : Word k K) : WordOn k I :=
  fun j => w.get j.val

/- The min makes this definition total; users prove m≤K in substantive specs. -/
def prefixAt {k K : ℕ} (m : ℕ) (w : Word k K) : Prefix k K :=
  ⟨⟨min m K, by omega⟩, List.Vector.ofFn fun j =>
    w.get ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_right m K)⟩⟩

/-! LB-05 witness data and exact finite inequalities. -/
structure ColdWitnessData where
  ms : ℕ
  mu : ℕ
  bridgeLength : ℕ
  theta : ℝ

def ColdWitnessData.s (W : ColdWitnessData) (N : ℕ) : ℝ := gridTime N W.ms
def ColdWitnessData.u (W : ColdWitnessData) (N : ℕ) : ℝ := gridTime N W.mu

def WitnessSpec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (eta rho chiGood : ℝ) (W : ColdWitnessData) : Prop :=
  let s := W.s N
  let u := W.u N
  let b := beta cuts hN s
  let jp := J cuts hN W.theta s u
  let hp := H cuts hN W.theta s u
  let jt := J cuts hN 2 u (horizon N K)
  let ht := H cuts hN 2 u (horizon N K)
  let h := b - jp + hp
  let gamma := 2*b - 2*jp - 2*jt + hp + ht
  W.bridgeLength = ⌈2*rho*logScale N⌉₊ ∧
  W.ms ≤ W.mu ∧ W.mu + W.bridgeLength ≤ K ∧
  W.theta ∈ Icc (3 : ℝ) 4 ∧
  (∃ gL gR : Fin K, W.mu ≤ gL.val ∧ gL.val < gR.val ∧
    gR.val < W.mu + W.bridgeLength ∧
    GoodColumn (cuts.profile hN gL) chiGood ∧
    GoodColumn (cuts.profile hN gR) chiGood) ∧
  eta/2 ≤ F cuts hN W.theta s u ∧
  jp ≤ b/2 - 3*kappa eta ∧
  (W.theta = 3 ∨ b/2 - 5*kappa eta ≤ jp) ∧
  kappa eta ≤ h ∧ hp ≤ b - jp - kappa eta ∧
  kappa eta ≤ gamma - h/2 ∧
  b - jp - jt ≤ beta cuts hN (horizon N K) ∧
  beta cuts hN (horizon N K) < kappa0 eta

/- LB-05 output, uniformly over every cut array after N0. -/


/-! LB-06 type counts and mass bins. Counts/bin index are data; a class is derived. -/
structure RoundedTypeData {k : ℕ} (P : BorelPartition k) where
  count : Fin P.cellCount → Fin k → ℕ
  binIndex : ℕ

def retainedTilt {k : ℕ} (P : BorelPartition k) (xi alpha : ℝ)
    (i : Fin P.cellCount) (l : Fin k) : ℝ :=
  (if 2*xi < prob (P.rep i) l then (prob (P.rep i) l)^alpha else 0) /
    (∑ a : Fin k, if 2*xi < prob (P.rep i) a then (prob (P.rep i) a)^alpha else 0)

def cellPositionCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (i : Fin P.cellCount) : ℕ :=
  (I.filter fun j => P.classify (cuts.profile hN j) = i).card

def wordCellCount {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) {I : Finset (Fin K)} (x : WordOn k I)
    (i : Fin P.cellCount) (l : Fin k) : ℕ :=
  (Finset.univ.filter fun j : I =>
    P.classify (cuts.profile hN j.val) = i ∧ x j = l).card

def roundedClass {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P) :
    Finset (WordOn k I) :=
  Finset.univ.filter fun x => ∀ i l, wordCellCount cuts hN P x i l = D.count i l

def massBin {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P)
    (b : ℕ) : Finset (WordOn k I) :=
  (roundedClass cuts hN P I D).filter fun x =>
    (b : ℝ) ≤ -Real.log (massOn cuts x) ∧ -Real.log (massOn cuts x) < (b : ℝ)+1

def selectedClass {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P) :
    Finset (WordOn k I) := massBin cuts hN P I D D.binIndex

def typeJ {k : ℕ} {P : BorelPartition k} (N : ℕ) (D : RoundedTypeData P) : ℝ :=
  (D.binIndex : ℝ) / logScale N

def typeH {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (D : RoundedTypeData P) : ℝ :=
  Real.log (selectedClass cuts hN P I D).card / logScale N

def TypeDataSpec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (xi alpha : ℝ)
    (D : RoundedTypeData P) : Prop :=
  let C0 := roundedClass cuts hN P I D
  let C1 := selectedClass cuts hN P I D
  (∀ i, ∑ l, D.count i l = cellPositionCount cuts hN P I i) ∧
  (∀ i l, prob (P.rep i) l ≤ 2*xi → D.count i l = 0) ∧
  (∀ i l, |(D.count i l : ℝ) - (cellPositionCount cuts hN P I i : ℝ) *
    retainedTilt P xi alpha i l| ≤ 1) ∧
  (∀ i, 0 < ∑ l : Fin k,
    if 2*xi < prob (P.rep i) l then (prob (P.rep i) l)^alpha else 0) ∧
  C0.Nonempty ∧ C1.Nonempty ∧
  ((C0.image (fun x => ⌊-Real.log (massOn cuts x)⌋₊)).card : ℝ) ≤
    2 + (I.card : ℝ)*Real.log (1/xi) ∧
  C0.card = ∏ i : Fin P.cellCount,
    (cellPositionCount cuts hN P I i).factorial / ∏ l : Fin k, (D.count i l).factorial ∧
  (∀ b : ℕ, (massBin cuts hN P I D b).card ≤ C1.card) ∧
  (∀ b : ℕ, (massBin cuts hN P I D b).card = C1.card → D.binIndex ≤ b) ∧
  0 ≤ typeJ N D ∧ 0 ≤ typeH cuts hN P I D ∧
  (C1.card : ℝ) = (N : ℝ) ^ typeH cuts hN P I D ∧
  (∀ x ∈ C1, Real.exp (-1) * (N : ℝ)^(-typeJ N D) < massOn cuts x ∧
    massOn cuts x ≤ (N : ℝ)^(-typeJ N D)) ∧
  (∀ x ∈ C0, ∀ j : I, xi ≤ (cuts.count j.val (x j) : ℝ)/N)

def TypeApproximation {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (I : Finset (Fin K)) (alpha error : ℝ)
    (D : RoundedTypeData P) : Prop :=
  |typeJ N D - (∑ j ∈ I, tiltedCost (cuts.profile hN j) alpha) / logScale N| +
  |typeH cuts hN P I D - (∑ j ∈ I, tiltedEntropy (cuts.profile hN j) alpha) / logScale N|
    ≤ error

/- Constants precede P,cuts,I,alpha; rounding dependence uses cell count m only. -/


/-! LB-09 geometry data and all associated objects. -/
def prefixColumns (K : ℕ) (W : ColdWitnessData) := columnSet K W.ms W.mu
def bridgeColumns (K : ℕ) (W : ColdWitnessData) := columnSet K W.mu (W.mu+W.bridgeLength)
def tailColumns (K : ℕ) (W : ColdWitnessData) := columnSet K (W.mu+W.bridgeLength) K

structure ColdGeometryData {k : ℕ} (K : ℕ) (P : BorelPartition k) (W : ColdWitnessData) where
  ambient : Word k K
  prefixType : RoundedTypeData P
  tailType : RoundedTypeData P
  central : WordOn k (bridgeColumns K W)
  reserveMinus : WordOn k (bridgeColumns K W)
  reservePlus : WordOn k (bridgeColumns K W)
  leftGood : Fin K
  rightGood : Fin K

def coldPrefixFamily {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) :=
  selectedClass cuts hN P (prefixColumns K W) G.prefixType

def coldTailFamily {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) :=
  selectedClass cuts hN P (tailColumns K W) G.tailType

def joinColdWord {k K : ℕ} {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) (x : WordOn k (prefixColumns K W))
    (v : WordOn k (bridgeColumns K W)) (z : WordOn k (tailColumns K W)) : Word k K :=
  List.Vector.ofFn fun j =>
    if hj : j ∈ prefixColumns K W then x ⟨j, hj⟩ else
    if hj : j ∈ bridgeColumns K W then v ⟨j, hj⟩ else
    if hj : j ∈ tailColumns K W then z ⟨j, hj⟩ else G.ambient.get j

def reservePrefix {k K : ℕ} {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) (x : WordOn k (prefixColumns K W))
    (v : WordOn k (bridgeColumns K W)) : Prefix k K :=
  prefixAt (W.mu+W.bridgeLength)
    (joinColdWord G x v (restrictWord (tailColumns K W) G.ambient))

def coldFullFamily {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) :
    Finset (Word k K) :=
  ((coldPrefixFamily cuts hN P W G).product (coldTailFamily cuts hN P W G)).image
    (fun xz => joinColdWord G xz.1 G.central xz.2)

def relativeMassBefore {k N K : ℕ} (cuts : Cuts k N K) {I : Finset (Fin K)}
    (x : WordOn k I) : ℝ :=
  ∑ v ∈ (Finset.univ.filter fun v : WordOn k I => wordOnList v < wordOnList x), massOn cuts v

def integerHalfOpen (l r : ℝ) : Finset ℤ :=
  (Finset.Icc ⌊l⌋ ⌈r⌉).filter fun z => l ≤ (z : ℝ) ∧ (z : ℝ) < r

def coldRelativeSet {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) : Finset ℤ :=
  let muA := prefixMean cuts (prefixAt W.ms G.ambient)
  (coldPrefixFamily cuts hN P W G).biUnion fun x =>
    integerHalfOpen (muA*relativeMassBefore cuts x)
      (muA*(relativeMassBefore cuts x + massOn cuts x))

def geometryEllP {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) : ℝ :=
  beta cuts hN (W.s N) - typeJ N G.prefixType

def geometryH {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) : ℝ :=
  geometryEllP cuts hN P W G + typeH cuts hN P (prefixColumns K W) G.prefixType

def geometryEllB {k N K : ℕ} (cuts : Cuts k N K)
    {P : BorelPartition k} {W : ColdWitnessData} (G : ColdGeometryData K P W) : ℝ :=
  -Real.log (massOn cuts G.central) / logScale N

def geometryZ {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) : ℝ :=
  beta cuts hN (W.s N) - typeJ N G.prefixType - typeJ N G.tailType - geometryEllB cuts G

def geometryG {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W) : ℝ :=
  2*geometryZ cuts hN P W G + typeH cuts hN P (prefixColumns K W) G.prefixType +
    typeH cuts hN P (tailColumns K W) G.tailType

/- Maximal digit, with the smallest-digit tie rule. -/
def IsCanonicalMaxWord {k N K : ℕ} (cuts : Cuts k N K) (w : Word k K) : Prop :=
  ∀ j : Fin K, (∀ l : Fin k, cuts.count j l ≤ cuts.count j (w.get j)) ∧
    (∀ l : Fin k, cuts.count j l = cuts.count j (w.get j) → w.get j ≤ l)

def BridgeSpec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (rho chiGood : ℝ) {P : BorelPartition k} {W : ColdWitnessData}
    (G : ColdGeometryData K P W) : Prop :=
  G.leftGood ∈ bridgeColumns K W ∧ G.rightGood ∈ bridgeColumns K W ∧
  G.leftGood.val < G.rightGood.val ∧
  GoodColumn (cuts.profile hN G.leftGood) chiGood ∧
  GoodColumn (cuts.profile hN G.rightGood) chiGood ∧
  wordOnList G.reserveMinus < wordOnList G.central ∧
  wordOnList G.central < wordOnList G.reservePlus ∧
  (∀ j : bridgeColumns K W, j.val ≠ G.leftGood → G.reserveMinus j = G.central j) ∧
  (∀ j : bridgeColumns K W, j.val ≠ G.rightGood → G.reservePlus j = G.central j) ∧
  (∀ v ∈ ({G.central, G.reserveMinus, G.reservePlus} : Finset (WordOn k (bridgeColumns K W))),
    chiGood^2 * (k : ℝ)^(-(W.bridgeLength : ℝ)) ≤ massOn cuts v) ∧
  0 ≤ geometryEllB cuts G ∧
  geometryEllB cuts G ≤ 2*rho*Real.log k +
    (Real.log k + 2*Real.log (1/chiGood))/logScale N

def GeometrySpec {k N K : ℕ} (cuts : Cuts k N K) (hN : 0 < N)
    (eta rho chiGood xi : ℝ) (P : BorelPartition k) (W : ColdWitnessData)
    (G : ColdGeometryData K P W) : Prop :=
  let b := beta cuts hN (W.s N)
  let ellp := geometryEllP cuts hN P W G
  let hp := typeH cuts hN P (prefixColumns K W) G.prefixType
  let ht := typeH cuts hN P (tailColumns K W) G.tailType
  let h := geometryH cuts hN P W G
  let z := geometryZ cuts hN P W G
  let g := geometryG cuts hN P W G
  let Hrel := coldRelativeSet cuts hN P W G
  let M := (Hrel.card : ℝ)
  let Y := coldFullFamily cuts hN P W G
  let c := min xi (min chiGood (1/(k : ℝ)))
  IsCanonicalMaxWord cuts G.ambient ∧
  prefixMean cuts (prefixAt W.ms G.ambient) = (N : ℝ)^b ∧
  TypeDataSpec cuts hN P (prefixColumns K W) xi W.theta G.prefixType ∧
  TypeDataSpec cuts hN P (tailColumns K W) xi 2 G.tailType ∧
  TypeApproximation cuts hN P (prefixColumns K W) W.theta
    (min (kappa eta) (kappa0 eta)/1000) G.prefixType ∧
  TypeApproximation cuts hN P (tailColumns K W) 2
    (min (kappa eta) (kappa0 eta)/1000) G.tailType ∧
  BridgeSpec cuts hN rho chiGood G ∧
  b/2 + 2*kappa eta ≤ ellp ∧ hp ≤ ellp - kappa eta ∧ kappa eta/2 ≤ h ∧
  Real.exp (-2)*(N : ℝ)^h ≤ M ∧ M ≤ 2*(N : ℝ)^h ∧
  (N : ℝ)^(kappa eta/3) ≤ M ∧ M ≤ N ∧
  (∀ q : Fin (N+1), ((boundary (clipTranslate N Hrel q.val)).card : ℝ) ≤ 4*Real.sqrt M) ∧
  kappa eta/2 ≤ g-h/2 ∧ z ≤ 2*kappa0 eta ∧
  (Y.card : ℝ) = (N : ℝ)^(hp+ht) ∧
  (∀ y ∈ Y, Real.exp (-2)*(N : ℝ)^z < (N : ℝ)*wordMass cuts y ∧
    (N : ℝ)*wordMass cuts y ≤ (N : ℝ)^z) ∧
  (∀ x ∈ coldPrefixFamily cuts hN P W G,
    (N : ℝ)^(b/2+kappa eta) ≤ prefixMean cuts (reservePrefix G x G.reserveMinus) ∧
    (N : ℝ)^(b/2+kappa eta) ≤ prefixMean cuts (reservePrefix G x G.reservePlus)) ∧
  0 < c ∧
  (∀ y ∈ Y, ∀ j : Fin K, c ≤ (cuts.count j (y.get j) : ℝ)/N) ∧
  (∀ x ∈ coldPrefixFamily cuts hN P W G,
    ∀ v ∈ ({G.reserveMinus,G.reservePlus} : Finset (WordOn k (bridgeColumns K W))),
    ∀ j : Fin (reservePrefix G x v).1.val,
      c ≤ (cuts.count ⟨j.val, lt_of_lt_of_le j.isLt
        (Nat.le_of_lt_succ (reservePrefix G x v).1.isLt)⟩
        ((reservePrefix G x v).2.get j) : ℝ)/N)

def ColdLocalization {k N K : ℕ} {cuts : Cuts k N K} (hN : 0 < N)
    (P : BorelPartition k) (W : ColdWitnessData) (G : ColdGeometryData K P W)
    (omega : Sample cuts) : Prop :=
  let q := (lowerRank (prefixAt W.ms G.ambient) omega : ℤ)
  let Hq := clipTranslate N (coldRelativeSet cuts hN P W G) q
  (∀ y ∈ coldFullFamily cuts hN P W G, ∀ i : Fin N,
    sortedWord omega i = y → i ∈ Hq) ∧
  ((coldFullFamily cuts hN P W G).filter (fun y => 2 ≤ wordCount y omega)).card ≤
    ((shuffleEdges omega) ∩ internalEdges Hq).card

/- Uniform conditional intermediate: supplied geometry is DATA with a proved spec. -/


/- LB-09's concrete output existentially constructs W and geometry from empirical premises. -/


/-! Additional owner-facing LB-05/LB-09 targets. -/






def relativeLowerCount {k N K : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (l m : ℕ) (x : WordOn k (columnSet K l m)) (omega : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i : Fin N =>
    (rowWord omega i).toList.take l = a.toList.take l ∧
    wordOnList (restrictWord (columnSet K l m) (rowWord omega i)) < wordOnList x).card

def relativeUpperCount {k N K : ℕ} {cuts : Cuts k N K}
    (a : Word k K) (l m : ℕ) (x : WordOn k (columnSet K l m)) (omega : Sample cuts) : ℕ :=
  (Finset.univ.filter fun i : Fin N =>
    (rowWord omega i).toList.take l = a.toList.take l ∧
    wordOnList (restrictWord (columnSet K l m) (rowWord omega i)) ≤ wordOnList x).card

def sidePrefix {k K : ℕ} (a : Word k K) (l m : ℕ)
    (x : WordOn k (columnSet K l m)) (j : columnSet K l m) (d : Fin k) : Prefix k K :=
  prefixAt (j.val.val+1) (List.Vector.ofFn fun h : Fin K =>
    if h = j.val then d else if hh : h ∈ columnSet K l m then x ⟨h, hh⟩ else a.get h)

/- Exact first-differing-digit identities plus the finite concentration implication. -/


/- No empirical-margin assumptions here: any already-proved witness may be used. -/




end RiffleLowerV2
