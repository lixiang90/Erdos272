module

public import Erdos272.Global.N20258.PopulationCut20258
public import Erdos272.Capacity.N20258.NaturalPopulation20258
public import Erdos272.Arithmetic.N20258.EndpointCover20258

@[expose] public section
namespace JSP233.PopulationBands20258
open StarCompletion PrivatePairExistence FirstSparseCut20258 PopulationPrice20258 PopulationTariff20258
open NaturalPopulation20258 EndpointCover20258 Density41
set_option autoImplicit false

structure Source where
  plan : Plan
  extras : Extras := []

def Source.Valid (q : Source) : Prop := if q.extras=[] then q.plan.Valid else Good q.plan q.extras

instance (q : Source) : Decidable q.Valid := by unfold Source.Valid; infer_instance

def block (a b lower upper L percent head : ℕ) : ConcentratedCut20258.Block :=
  let length := max 1 (max ((443*a/5000-17)/(upper-1)) ((L-1)/(upper-1)))
  ⟨a,b,lower,upper,length,max head ((percent*b+99)/100)⟩

/-- One set of weights can serve different physical grounds and later
first cutoffs. Recheck the overlap exclusions at the indicated upper cutoff. -/
theorem interval {N a b l u m L U pc v : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    {q : Source} (lo : a≤N) (hi : N≤b) (low : l≤m) (high : m≤u) (room : u+1≤a)
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (source : q.Valid)
    (tests : ∀ t∈q.plan.table,t.1.Valid u L)
    (fee : cost q.plan.table b+4*b*weights q.extras≤q.plan.scale*v)
    (price : PopulationCut20258.Valid (block a b l u L pc q.plan.head) L U q.plan.minimum q.plan.head v)
    (many : L*(N-2)<(CrookedMembers F).card) (few : (CrookedMembers F).card≤U*(N-2)) : F.card≤B N := by
  apply PopulationCut20258.upper (b:=block a b l u L pc q.plan.head) lo hi low high legal cut price many few
  intro A sub large
  have small := price.2.2.1
  have base := price.1
  change b<2^16 at small
  change 161≤a at base
  have omits (x : ℤ) (hx : x∈Ground N) : ∃ S∈CrookedMembers F,x∉S ∧ S.card≤u := by
    obtain ⟨S,hs,out,sz⟩ := cut.crooked x hx
    exact ⟨S,hs,out,sz.trans high⟩
  by_cases none : q.extras=[]
  · rw [Source.Valid,ite_eq_left none] at source
    rw [none] at fee
    simp only [weights,List.map_nil,List.sum_nil,Nat.mul_zero,Nat.add_zero] at fee
    exact PopulationPrice20258.family source hi (by omega) (by omega) (by omega) legal sub large omits many tests fee
  · rw [Source.Valid,ite_eq_right none] at source
    exact NaturalPopulation20258.family source hi (by omega) (by omega) (by omega) legal sub large omits many tests fee

/-- Locate the actual number of crooked members in one of the certified
bands, including exact multiples of the population unit N-2. -/
theorem by_population {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (ground : 3≤N) (two : 2≤m) (legal : Legal (Ground N) F) (cut : Cut N F m c T)
    (ends : List ℕ) (cover : increasing 1 ((m-1)*m+1) ends=true)
    (pay : ∀ p∈rows 1 ends,(p.1-1)*(N-2)<(CrookedMembers F).card →
      (CrookedMembers F).card≤p.2*(N-2) → F.card≤B N) : F.card≤B N := by
  classical
  let H := CrookedMembers F
  let D := N-2
  have pos : 0<D := by dsimp only [D]; omega
  have sparse := cut.sparse
  obtain ⟨mem,bad,_⟩ := actual_sparse_membership.mp cut.omitter
  have hp : 0<H.card := Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨mem,bad⟩⟩
  have cap := TwoTransversals20258.actual_member (by omega : 2≤N) (by omega : m+1≤N) legal mem
    (Finset.card_pos.mp (by rw [cut.size]; omega)) cut.crooked
  rw [cut.size] at cap
  let z := (H.card-1)/D+1
  have lower : (z-1)*D<H.card := by
    have quotient := Nat.div_mul_le_self (H.card-1) D
    simp only [z,Nat.add_sub_cancel]
    exact lt_of_le_of_lt quotient (Nat.sub_lt hp (by decide))
  have upper : H.card≤z*D := by
    have quotient := Nat.lt_mul_div_succ (H.card-1) pos
    dsimp only [z]; rw [Nat.mul_comm D] at quotient; omega
  have fits : z≤(m-1)*m+1 := by
    by_contra! outside
    have over := Nat.mul_le_mul_right D (show (m-1)*m+1≤z-1 by omega)
    change H.card≤((m-1)*m+1)*D at cap
    omega
  obtain ⟨p,hp,lo,hi,_⟩ := locate ends cover (show 1≤z from Nat.succ_le_succ (Nat.zero_le _)) fits
  exact pay p hp (lt_of_le_of_lt (Nat.mul_le_mul_right D (Nat.sub_le_sub_right lo 1)) lower)
    (upper.trans (Nat.mul_le_mul_right D hi))

#print axioms interval
#print axioms by_population
end JSP233.PopulationBands20258
