module

public import Erdos272.Global.N20258.PopulationBands20258
public import Erdos272.Arithmetic.N20258.PopulationFees20258
public import Erdos272.Global.N20258.ConcentratedBlocks20258

@[expose] public section
namespace JSP233.PopulationRanges20258
open StarCompletion PrivatePairExistence FirstSparseCut20258 Density41
open PopulationBands20258 PopulationTariff20258 NaturalPopulation20258
set_option autoImplicit false

def Win (m a b : ℕ) : Prop :=
  ∀ {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ},
    a≤N → N≤b → Legal (Ground N) F → Cut N F m c T → F.card≤B N

def Segment (m a b L U : ℕ) : Prop :=
  ∀ {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ},
    a≤N → N≤b → Legal (Ground N) F → Cut N F m c T →
    L*(N-2)<(CrookedMembers F).card → (CrookedMembers F).card≤U*(N-2) → F.card≤B N

theorem paid {m a b L U pc v : ℕ} {q : Source} {p : PopulationFees20258.Prefix (b-1)}
    (room : m+1≤a) (source : q.Valid) (tests : ∀ t∈q.plan.table,t.1.Valid m L)
    (fee : PopulationFees20258.bill p q.plan.table+4*b*weights q.extras≤q.plan.scale*v)
    (price : PopulationCut20258.Valid (block a b m m L pc q.plan.head) L U q.plan.minimum q.plan.head v) :
    Segment m a b L U := by
  intro N F c T lo hi legal cut many few
  rw [PopulationFees20258.bill_eq] at fee
  exact interval (q:=q) lo hi le_rfl le_rfl room legal cut source tests fee price many few

theorem join_population {m a b l k u : ℕ} (left : Segment m a b l k)
    (right : Segment m a b k u) : Segment m a b l u := by
  intro N F c T lo hi legal cut many few
  by_cases middle : (CrookedMembers F).card≤k*(N-2)
  · exact left lo hi legal cut many middle
  · exact right lo hi legal cut (Nat.lt_of_not_ge middle) few

theorem complete {m a b : ℕ} (pos : 2≤m) (base : 3≤a)
    (cover : Segment m a b 0 ((m-1)*m+1)) : Win m a b := by
  classical
  intro N F c T lo hi legal cut
  obtain ⟨member,bad,_⟩ := actual_sparse_membership.mp cut.omitter
  have sparse := cut.sparse
  have few := TwoTransversals20258.actual_member (by omega : 2≤N) (by omega : m+1≤N) legal member
    (Finset.card_pos.mp (by rw [cut.size]; omega)) cut.crooked
  rw [cut.size] at few
  have many : 0<(CrookedMembers F).card := Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨member,bad⟩⟩
  exact cover lo hi legal cut (by simpa only [Nat.zero_mul] using many) few

theorem join_ground {m a h b : ℕ} (left : Win m a h) (right : Win m (h+1) b) : Win m a b := by
  intro N F c T lo hi legal cut
  by_cases within : N≤h
  · exact left lo within legal cut
  · exact right (by omega) hi legal cut

theorem short {m a b : ℕ} (base : 2≤a) (valid : 5000*((m-1)*m+17)≤443*a) : Win m a b := by
  intro N F c T lo hi legal cut
  have sparse := cut.sparse
  apply FortyFourFamily20258.of_member (base.trans lo) (by omega) legal (actual_sparse_membership.mp cut.omitter).1 cut.crooked
  rw [cut.size]
  exact valid.trans (Nat.mul_le_mul_left 443 lo)

theorem classical_route {m a b : ℕ} {q : ConcentratedBlocks20258.Source} {pc : ℕ}
    (valid : q.Valid) (price : (ConcentratedBlocks20258.Route.mk m m pc q).Good a b) : Win m a b := by
  intro N F c T lo hi legal cut
  exact ConcentratedBlocks20258.upper (r:=⟨m,m,pc,q⟩) lo hi le_rfl le_rfl legal cut valid price

#print axioms complete
#print axioms paid
end JSP233.PopulationRanges20258
