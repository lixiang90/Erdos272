module

public import Erdos272.Global.N20258.PopulationRanges20258

@[expose] public section
namespace JSP233.FiniteCuts19227
open StarCompletion PrivatePairExistence Density41 DenseDeletion40 SparseSmall39 FirstSparseCut20258
open PopulationRanges20258 ConcentratedBlocks20258
open scoped Classical
set_option autoImplicit false

def Band (l r a b : ℕ) : Prop := ∀ m : ℕ,l≤m → m≤r → Win m a b

/-- A population band with no extra lower-density hypothesis also accepts the
two concentrated marking certificates and the uniform size certificate. -/
theorem large {l r a b pc : ℕ} {q : Source} (minimum : 2≤l) (range : a≤b) (room : r+1≤a)
    (source : q.Valid)
    (paid : let x := max (q.head 0) ((pc*b+99)/100)
      let h := q.head x
      PopulationCut20258.Valid (PopulationBands20258.block a b l r 0 pc h) 0 ((r-1)*r+1)
        q.minimum h (q.debt b)) : Band l r a b := by
  classical
  intro m lo hi N F c T left right legal cut
  let x := max (q.head 0) ((pc*b+99)/100)
  let h := q.head x
  let z := PopulationBands20258.block a b l r 0 pc h
  change PopulationCut20258.Valid z 0 ((r-1)*r+1) q.minimum h (q.debt b) at paid
  obtain ⟨member,bad,_⟩ := actual_sparse_membership.mp cut.omitter
  have sparse := cut.sparse
  have few := TwoTransversals20258.actual_member (by omega : 2≤N) (by omega : m+1≤N)
    legal member (Finset.card_pos.mp (by rw [cut.size]; omega)) cut.crooked
  rw [cut.size] at few
  have many : 0<(CrookedMembers F).card := Finset.card_pos.mpr ⟨T,Finset.mem_filter.mpr ⟨member,bad⟩⟩
  apply PopulationCut20258.upper (b:=z) left right lo hi legal cut paid (by simpa using many)
    (few.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right (Nat.mul_le_mul (Nat.sub_le_sub_right hi 1) hi) 1)))
  intro A sub sz
  have inside : A⊆F := sub.trans (Finset.filter_subset _ _)
  have lifted : Legal (Ground b) A := by
    refine ⟨?_,fun S hs U hu => legal.2 S (inside hs) U (inside hu)⟩
    intro S hs t ht
    obtain ⟨low,high⟩ := (mem_ground N t).mp (legal.1 S (inside hs) ht)
    exact (mem_ground b t).mpr ⟨low,high.trans (by exact_mod_cast right)⟩
  have crooked (S : Finset ℤ) (hs : S∈A) : ¬IsAP S := (Finset.mem_filter.mp (sub hs)).2
  have small := paid.2.2.1
  change b<2^16 at small
  change q.head x*A.card≤_+q.debt b
  cases eq : q with
  | marked p =>
    rw [eq] at source sz
    exact ConcentratedCharge20258.family source lifted (by omega) (by omega) sz crooked
  | uniform s =>
    rw [eq] at source sz
    have each (S : Finset ℤ) (hs : S∈A) : (Source.uniform s).head x≤(IntrinsicTriples208.Pool S).card :=
      (min_le_right ..).trans (UniformCardPool20258.pool_floor (by omega : b≤2^18)
        (lifted.1 S hs) (crooked S hs) source.1 source.2 (sz S hs) le_rfl)
    simpa only [Source.debt,Nat.add_zero,Finset.sum_const,smul_eq_mul,Nat.mul_comm _ A.card]
      using Finset.sum_le_sum each

/-- With no common root in the retained crooked family, the first cutoff
exists independently of a numerical threshold for the common-root case. -/
theorem first {N : ℕ} {F : Finset (Finset ℤ)} (pos : 1≤N) (legal : Legal (Ground N) F)
    (counter : B N<F.card) (unrooted : ¬∃ c∈Ground N,∀ S∈Retained N 12 F,¬IsAP S → c∈S) :
    ∃ m c T,Cut N F m c T := by
  classical
  let covers := fun k : ℕ => ∀ z∈Ground N,∃ S∈SparseCrooked N 12 F,z∉S ∧ S.card≤k
  have top : covers N := by
    intro z hz
    by_contra! h
    apply unrooted
    refine ⟨z,hz,?_⟩
    intro S hs bad
    have mem := (Finset.mem_sdiff.mp hs).1
    have sp := actual_sparse_membership.mpr ⟨mem,bad,actual_retained_crooked_sparse hs bad⟩
    have sz : S.card≤N := by simpa only [ground_card] using Finset.card_le_card (legal.1 S mem)
    by_contra miss
    exact (not_lt_of_ge sz) (h S sp miss)
  have ex : ∃ k,covers k := ⟨N,top⟩
  let m := Nat.find ex
  have hits : covers m := Nat.find_spec ex
  have strict : 0<m := by
    obtain ⟨Q,mem,_,sz⟩ := hits 1 ((mem_ground N 1).mpr ⟨le_rfl,by exact_mod_cast pos⟩)
    by_contra! zero
    have empty := Finset.card_eq_zero.mp (show Q.card=0 by omega)
    have only : F⊆{Q} := by
      intro S hs
      apply Finset.mem_singleton.mpr
      by_contra ne
      have nonempty := isAP_nonempty (legal.2 S hs Q (actual_sparse_subset N 12 F mem) ne)
      rw [empty,Finset.inter_empty] at nonempty
      exact Finset.not_nonempty_empty nonempty
    have bound : F.card≤1 := by simpa only [Finset.card_singleton] using Finset.card_le_card only
    unfold B at counter
    omega
  have prev : ∃ c∈Ground N,∀ S∈SparseCrooked N 12 F,c∉S → m≤S.card := by
    by_contra! no
    apply Nat.find_min ex (show m-1<m by omega)
    intro z hz
    obtain ⟨S,hs,away,short⟩ := no z hz
    exact ⟨S,hs,away,by omega⟩
  obtain ⟨c,hc,least⟩ := prev
  obtain ⟨T,ht,out,sz⟩ := hits c hc
  exact ⟨m,c,T,hc,ht,out,le_antisymm sz (least T ht out),hits,least⟩

#print axioms first
#print axioms large
end JSP233.FiniteCuts19227
