import RiffleUpperV2.FirstMoment.RetainedClasses
import RiffleUpperV2.FirstMoment.AnchoredCosts

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
namespace RiffleUpperV2.FirstMoment
open TimeProfile Anchor RiffleUpperV2.Localization InhomogeneousShuffle.FirstMoment

/-- Reading a sparse digit record avoids any dependent transport of its domain. -/
def sparseDigit {d k q : ℕ} (c : SparseAssignment d k q) (j : Fin d) : Option (Fin k) :=
  if hj : j ∈ c.1.1 then some (c.2 ⟨j,hj⟩) else none

theorem encodeExceptions_eq_data {k n d q : ℕ} (cuts : Cuts k n d) (hn : 0 < n)
    (I J : Finset (Fin d)) (chi : ℝ) (w w' : Fin d → Fin k)
    (hq : (exceptionalPositions (cuts.profile hn) I chi w).card ≤ q)
    (hq' : (exceptionalPositions (cuts.profile hn) J chi w').card ≤ q)
    (he : encodeExceptions cuts hn I chi w hq = encodeExceptions cuts hn J chi w' hq') :
    exceptionalPositions (cuts.profile hn) I chi w = exceptionalPositions (cuts.profile hn) J chi w' ∧
      ∀ j ∈ exceptionalPositions (cuts.profile hn) J chi w', w j = w' j := by
  classical
  have hQ : exceptionalPositions (cuts.profile hn) I chi w =
      exceptionalPositions (cuts.profile hn) J chi w' :=
    congrArg (fun c : SparseAssignment d k q => c.1.1) he
  refine ⟨hQ,?_⟩
  intro j hj
  have hj' : j ∈ exceptionalPositions (cuts.profile hn) I chi w := hQ.symm ▸ hj
  have hv := congrArg (fun c : SparseAssignment d k q => sparseDigit c j) he
  simpa [sparseDigit,encodeExceptions,hj,hj'] using hv

set_option quotPrecheck false
section Fibers
variable {k n d N : ℕ} (hk : 0 < k) (hN : 2 ≤ N)
    (cuts : Cuts k n d) (hn : 0 < n) (R : Fin k → Finset (Fin n))
    (T C chi delta width : ℝ) (hchi : 0 < chi) (hchi1 : chi ≤ 1)
    (hchiK : chi ≤ 1/(k : ℝ)) (hwidth : 0 < width) (hd : (d : ℝ) ≤ T*logScale N)
local notation "Candidate" => RetainedAtPile hk N cuts hn R C chi delta hchiK
local notation "desc" => retainedDescriptor hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd
local notation "default" => leftDefault hk cuts hn chi hchiK
local notation "join" => (fun t : Candidate => boundaryJoin t.2.1.1 t.2.1.2.1)
local notation "word" => (fun t : Candidate => completePrefix default t.2.1.2.2)
local notation "interval" => (fun t : Candidate => empiricalPositions d 0 (boundaryJoin t.2.1.1 t.2.1.2.1).1.val t.2.1.2.2.1.val)

/-- Equality of actual keys fixes the full boundary words and the word length. -/
theorem retainedDescriptor_eq_geometry (t s : Candidate) (he : desc t = desc s) :
    t.1 = s.1 ∧ t.2.1.1 = s.2.1.1 ∧ t.2.1.2.1 = s.2.1.2.1 ∧
      t.2.1.2.2.1 = s.2.1.2.2.1 := by
  refine ⟨congrArg (fun c => c.1) he, ?_, ?_, congrArg (fun c => c.2.2.2.1) he⟩
  · have hb := congrArg (fun c => c.2.1) he
    exact congrArg Subtype.val (encodeBoundary_injective hk default hb)
  · have hb := congrArg (fun c => c.2.2.1) he
    exact congrArg Subtype.val (encodeBoundary_injective hk (rightDefault hk cuts hn chi hchiK) hb)

/-- Equality of actual keys fixes all rare positions, their selected values, and the cost bin. -/
theorem retainedDescriptor_eq_costs (t s : Candidate) (he : desc t = desc s) :
    exceptionalPositions (cuts.profile hn) (interval t) chi (word t) =
      exceptionalPositions (cuts.profile hn) (interval s) chi (word s) ∧
    (∀ j ∈ exceptionalPositions (cuts.profile hn) (interval s) chi (word s),
      (word t) j = (word s) j) ∧
    ⌊goodCost N (cuts.profile hn) (interval t) chi (word t)/width⌋₊ =
      ⌊goodCost N (cuts.profile hn) (interval s) chi (word s)/width⌋₊ := by
  have hexc := congrArg (fun c => c.2.2.2.2.1) he
  have h := encodeExceptions_eq_data cuts hn (interval t) (interval s) chi (word t) (word s)
    t.2.2.2.2.2 s.2.2.2.2.2 hexc
  exact ⟨h.1,h.2,congrArg (fun c => c.2.2.2.2.2.1.val) he⟩

/-- The actual descriptor fiber, represented by its selected prefix words. -/
def classPrefixes (s : Candidate) : Finset (Prefix k d) := by
  classical
  exact (Finset.univ.filter (fun t : Candidate => desc t = desc s)).image (fun t => t.2.1.2.2)

theorem mem_classPrefixes (s : Candidate) : s.2.1.2.2 ∈
    classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s := by
  classical
  exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩

/-- A fiber contains one candidate per prefix: the key already fixes its pile
and both boundary words. -/
theorem retainedDescriptor_prefix_injective (t s : Candidate)
    (he : desc t = desc s) (hx : t.2.1.2.2 = s.2.1.2.2) : t = s := by
  have hg := retainedDescriptor_eq_geometry hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd t s he
  rcases t with ⟨p,t⟩
  rcases s with ⟨q,s⟩
  obtain ⟨hp,hy,hz,_⟩ := hg
  dsimp at hp hy hz hx
  subst q
  exact congrArg (fun b => Sigma.mk p b) (Subtype.ext (Prod.ext hy (Prod.ext hz hx)))

/-- Prefix cardinality is exactly the actual descriptor-fiber cardinality. -/
theorem classPrefixes_card (s : Candidate) :
    (classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s).card =
      (Finset.univ.filter (fun t : Candidate => desc t = desc s)).card := by
  classical
  apply Finset.card_image_of_injOn
  intro t ht u hu he
  apply retainedDescriptor_prefix_injective hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd t u
    ((Finset.mem_filter.mp ht).2.trans (Finset.mem_filter.mp hu).2.symm) he

/-- Immediate-stop fibers are literal singletons, since their fixed join
and recorded length determine the whole prefix. -/
theorem classPrefixes_singleton_of_immediate (s : Candidate)
    (hroot : s.2.1.2.2 = join s) :
    classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s =
      {s.2.1.2.2} := by
  classical
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨mem_classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s,?_⟩
  intro x hx
  obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
  have hg := retainedDescriptor_eq_geometry hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd t s (Finset.mem_filter.mp ht).2
  have hp : IsPrefix (join s) t.2.1.2.2 := by
    simpa only [hg.2.1,hg.2.2.1] using t.2.2.1.2.2.2.2.2.1
  rw [← hroot] at hp
  exact (prefix_eq_of_length hp (congrArg Fin.val hg.2.2.2).symm).symm

/-- A terminal first boundary forces the same immediate singleton conclusion. -/
theorem classPrefixes_singleton_of_terminal (s : Candidate)
    (ht : TerminalBoundaryPair s.2.1.1 s.2.1.2.1) :
    classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s =
      {s.2.1.2.2} := by
  have hx := s.2.2.1.2.2.2.2
  have hp := boundaryJoin_properties s.2.2.1.2.2.1 s.2.2.1.2.2.2.1
  have hfull : (join s).1.val = d := by
    have hbound := (join s).1.isLt
    rcases ht with hy | hz
    · have h := prefix_length_le hp.1
      change s.2.1.1.1.val ≤ (join s).1.val at h
      omega
    · have h := prefix_length_le hp.2.1
      change s.2.1.2.1.1.val ≤ (join s).1.val at h
      omega
  have hlen : (join s).1.val = s.2.1.2.2.1.val := by
    have h := prefix_length_le hx.2.1
    have hb := s.2.1.2.2.1.isLt
    change (join s).1.val ≤ s.2.1.2.2.1.val at h
    omega
  exact classPrefixes_singleton_of_immediate hk hN cuts hn R T C chi delta width
    hchi hchi1 hchiK hwidth hd s (prefix_eq_of_length hx.2.1 hlen).symm

/-- Entropy of every nonempty actual retained descriptor fiber. All prefix,
legality, sparse-record and bin premises are derived from the actual key. -/
theorem retainedClassEntropy (hk2 : 2 ≤ k) (s : Candidate) (theta : ℝ)
    (htheta : theta ∈ Set.Icc (3 : ℝ) 4) :
    Real.log ((classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s).card : ℝ) /
      logScale N ≤ theta*goodCost N (cuts.profile hn) (interval s) chi (word s) -
        (∑ j ∈ interval s, psi (cuts.profile hn j) theta)/logScale N +
        (4*width+4*Real.log (k : ℝ)*exceptionalAllowance chi) := by
  classical
  let W := classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s
  have hwitness (x : Prefix k d) (hx : x ∈ W) :
      ∃ t : Candidate, desc t = desc s ∧ t.2.1.2.2 = x := by
    obtain ⟨t,ht,htx⟩ := Finset.mem_image.mp hx
    exact ⟨t,(Finset.mem_filter.mp ht).2,htx⟩
  have hgeom (t : Candidate) (he : desc t = desc s) :=
    retainedDescriptor_eq_geometry hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd t s he
  have hint (t : Candidate) (he : desc t = desc s) : interval t = interval s := by
    have hg := hgeom t he
    dsimp
    rw [hg.2.1,hg.2.2.1,hg.2.2.2]
  have hrecords (t : Candidate) (he : desc t = desc s) :=
    retainedDescriptor_eq_costs hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd t s he
  apply prefixFamilyEntropy hk2 hN cuts hn default (join s) s.2.1.2.2 W
    (mem_classPrefixes hk hN cuts hn R T C chi delta width hchi hchi1 hchiK hwidth hd s)
    (interval s) rfl chi width theta (exceptionalAllowance chi) hwidth htheta
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    exact congrArg Fin.val (hgeom t ht).2.2.2
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    have hpre := t.2.2.1.2.2.2.2.2.1
    simpa only [(hgeom t ht).2.1,(hgeom t ht).2.2.1] using hpre
  · intro x hx j hj
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    apply legal_prefix_digits cuts hn (R t.1) default _ t.2.2.1.2.2.2.2.1
    have hlt := (Finset.mem_filter.mp hj).2.2
    simpa only [(hgeom t ht).2.2.2, Nat.sub_zero] using hlt
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    simpa only [hint t ht] using (hrecords t ht).1
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    exact (hrecords t ht).2.1
  · intro x hx
    obtain ⟨t,ht,rfl⟩ := hwitness x hx
    simpa only [hint t ht] using (hrecords t ht).2.2
  · exact (Nat.cast_le.mpr s.2.2.2.2.2).trans
      (Nat.floor_le (mul_nonneg (exceptionalAllowance_nonneg chi) (logScale_pos hN).le))

end Fibers
end RiffleUpperV2.FirstMoment
