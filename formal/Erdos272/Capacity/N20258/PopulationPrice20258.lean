module

public import Erdos272.Capacity.N20258.IndividualPrice20258
public import Erdos272.Counting.N20258.PopulationTariff20258

@[expose] public section
namespace JSP233.PopulationPrice20258
open StarCompletion PrivatePairExistence SourceBridge208 IntrinsicTriples208 PopulationTariff20258
open scoped Classical BigOperators
set_option autoImplicit false

structure Plan where
  minimum : ℕ
  top : ℕ
  stop : ℕ
  head : ℕ
  scale : ℕ
  table : Table

def Plan.Valid (p : Plan) : Prop :=
  4≤p.minimum ∧ p.minimum≤p.top ∧ p.top≤256 ∧ 1≤p.stop ∧ 0<p.scale ∧
  p.head≤UniformNumeric84364.value (p.top+1) ∧
  (∀ i : Fin (p.top+1-p.minimum),p.head≤IndividualPrice20258.physical (p.minimum+i.val) p.stop) ∧
  (∀ i : Fin (p.top+1-p.minimum),∀ j : Fin (p.stop-1),
    p.scale*p.head≤p.scale*IndividualPrice20258.value (p.minimum+i.val) (j.val+1)+
      grant p.table (p.minimum+i.val) (j.val+1))

instance (p : Plan) : Decidable p.Valid := by unfold Plan.Valid; infer_instance

theorem family {N n m L v : ℕ} {A F : Finset (Finset ℤ)} {p : Plan} (valid : p.Valid)
    (hi : N≤n) (cap : N≤2^18) (two : 2≤N) (room : m+1≤N) (legal : Legal (Ground N) F)
    (sub : A⊆CrookedMembers F) (large : ∀ S∈A,p.minimum≤S.card)
    (omits : ∀ x∈Ground N,∃ S∈CrookedMembers F,x∉S ∧ S.card≤m)
    (many : L*(N-2)<(CrookedMembers F).card) (tests : ∀ r∈p.table,r.1.Valid m L)
    (fee : cost p.table n≤p.scale*v) : p.head*A.card≤(∑ S∈A,(Pool S).card)+v := by
  classical
  obtain ⟨four,ok,top,positive,scale,tall,tail,cell⟩ := valid
  have inside : A⊆F := sub.trans (Finset.filter_subset _ _)
  have pay (S : Finset ℤ) (hs : S∈A) : p.scale*p.head≤p.scale*(Pool S).card+grant p.table S.card (Defect S) := by
    have sz := large S hs
    have bad := (Finset.mem_filter.mp (sub hs)).2
    have ground := legal.1 S (inside hs)
    by_cases low : S.card≤p.top
    · let i : Fin (p.top+1-p.minimum) := ⟨S.card-p.minimum,by omega⟩
      have si : p.minimum+i.val=S.card := by dsimp only [i]; omega
      by_cases high : p.stop≤Defect S
      · have unit := tail i
        rw [si] at unit
        exact (Nat.mul_le_mul_left _ (unit.trans (IndividualPrice20258.physical_le (by omega) (by omega) high))).trans
          (Nat.le_add_right ..)
      have pos := MixedCore200000.crooked_defect_positive (by omega : 2≤S.card) bad
      let j : Fin (p.stop-1) := ⟨Defect S-1,by omega⟩
      have mark := cell i j
      rw [si,show j.val+1=Defect S by dsimp only [j]; omega] at mark
      exact mark.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
        (IndividualPrice20258.actual cap ground bad (by omega) (by omega))) _)
    · have unit := UniformCardPool20258.pool_floor cap ground bad (by omega : 4≤p.top+1)
        (by omega) (by omega) tall
      exact (Nat.mul_le_mul_left _ unit).trans (Nat.le_add_right ..)
  have paid := Finset.sum_le_sum pay
  have spent := (bill p.table hi two room legal inside omits many tests).trans fee
  refine Nat.le_of_mul_le_mul_left ?_ scale
  calc
    _ = A.card*(p.scale*p.head) := by ring
    _ = ∑ _S∈A,p.scale*p.head := by simp
    _ ≤ _ := paid
    _ = p.scale*(∑ S∈A,(Pool S).card)+∑ S∈A,grant p.table S.card (Defect S) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
    _ ≤ _ := (Nat.add_le_add_left spent _).trans_eq (Nat.mul_add ..).symm

#print axioms family
end JSP233.PopulationPrice20258
