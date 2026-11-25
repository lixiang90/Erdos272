module

public import Erdos272.Global.N20258.RootedFamily20258
public import Erdos272.Counting.N20258.MixedOmitter20258

@[expose] public section
namespace JSP233.FirstSparseCut20258
open StarCompletion PrivatePairExistence Density41 DenseDeletion40 AnchorCompletion38 SparseSmall39
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- At the first empty common intersection on the true ground, the same
size controls the rooted members and lower-bounds all the sparse avoiders. -/
structure Cut (N : ℕ) (F : Finset (Finset ℤ)) (m : ℕ) (c : ℤ) (T : Finset ℤ) : Prop where
  ground : c∈Ground N
  omitter : T∈SparseCrooked N 12 F
  misses : c∉T
  size : T.card=m
  covers : ∀ z∈Ground N, ∃ Q∈SparseCrooked N 12 F, z∉Q ∧ Q.card≤m
  minimum : ∀ S∈SparseCrooked N 12 F, c∉S → m≤S.card

theorem extract {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20000≤N) (hi : N<2^16)
    (legal : Legal (Ground N) F) (counter : B N<F.card) :
    ∃ m c T, Cut N F m c T := by
  let covers := fun k : ℕ => ∀ z∈Ground N, ∃ S∈SparseCrooked N 12 F, z∉S ∧ S.card≤k
  have top : covers N := by
    intro z hz
    by_contra! h
    apply (not_lt_of_ge (RootedFamily20258.actual_upper lo hi legal ⟨z,hz,?_⟩)) counter
    intro S hs bad
    have mem := (Finset.mem_sdiff.mp hs).1
    have sparse := actual_sparse_membership.mpr ⟨mem,bad,actual_retained_crooked_sparse hs bad⟩
    by_contra miss
    have sz : S.card≤N := by simpa only [ground_card] using Finset.card_le_card (legal.1 S mem)
    exact (not_lt_of_ge sz) (h S sparse miss)
  have existsCut : ∃ k, covers k := ⟨N,top⟩
  let m := Nat.find existsCut
  have every : covers m := Nat.find_spec existsCut
  have hm : 0<m := by
    have one : (1:ℤ)∈Ground N := (mem_ground N 1).mpr ⟨le_rfl,by omega⟩
    obtain ⟨Q,hQ,_,size⟩ := every 1 one
    by_contra! hz
    have empty := Finset.card_eq_zero.mp (show Q.card=0 by omega)
    have sub := actual_sparse_subset N 12 F hQ
    have all : F⊆{Q} := by
      intro S hs
      apply Finset.mem_singleton.mpr
      by_contra ne
      have both := isAP_nonempty (legal.2 S hs Q sub ne)
      rw [empty,Finset.inter_empty] at both
      exact Finset.not_nonempty_empty both
    have fc : F.card≤1 := by simpa only [Finset.card_singleton] using Finset.card_le_card all
    unfold B at counter
    omega
  have prev : ∃ c∈Ground N, ∀ S∈SparseCrooked N 12 F, c∉S → m≤S.card := by
    by_contra! none
    apply Nat.find_min existsCut (show m-1<m by omega)
    intro z hz
    obtain ⟨S,hS,miss,short⟩ := none z hz
    exact ⟨S,hS,miss,by omega⟩
  obtain ⟨c,hc,minimum⟩ := prev
  obtain ⟨T,hT,miss,sz⟩ := every c hc
  exact ⟨m,c,T,hc,hT,miss,le_antisymm sz (minimum T hT miss),every,minimum⟩

theorem Cut.crooked {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (cut : Cut N F m c T) :
    ∀ z∈Ground N, ∃ S∈CrookedMembers F, z∉S ∧ S.card≤m := by
  intro z hz
  obtain ⟨S,hs,miss,sz⟩ := cut.covers z hz
  obtain ⟨mem,bad,_⟩ := actual_sparse_membership.mp hs
  exact ⟨S,Finset.mem_filter.mpr ⟨mem,bad⟩,miss,sz⟩

theorem Cut.sparse {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (cut : Cut N F m c T) : 12*m≤N := cut.size ▸ (actual_sparse_membership.mp cut.omitter).2.2

theorem Cut.root_bound {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (legal : Legal (Ground N) F) (cut : Cut N F m c T) (two : 2≤m) :
    (RootPart (SparseCrooked N 12 F) c).card≤m*N := by
  have sparse := cut.sparse
  have hT := (actual_sparse_membership.mp cut.omitter).1
  have degree := MixedOmitter20258.actual_degree legal hT cut.misses
  rw [cut.size] at degree
  have standard := degreeBudget_closed N m (by omega) (by omega)
  have sub : RootPart (SparseCrooked N 12 F) c ⊆ RootPart (CrookedMembers F) c := by
    intro S hs
    obtain ⟨mem,hc⟩ := Finset.mem_filter.mp hs
    obtain ⟨hf,bad,_⟩ := actual_sparse_membership.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hf,bad⟩,hc⟩
  exact (Finset.card_le_card sub).trans <| degree.trans <|
    (by omega : DegreeBudget N m≤m*(N-2)).trans (Nat.mul_le_mul_left m (Nat.sub_le _ _))

#print axioms extract
#print axioms Cut.root_bound
end
end JSP233.FirstSparseCut20258
