module

public import Erdos272.Global.N20258.RootedFamily20258
public import Erdos272.Global.N20258.SmallFortyOne20258

@[expose] public section
namespace JSP233.FirstEmptyKernel20258
open StarCompletion PrivatePairExistence Density41 DenseDeletion40
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- The first size at which the crooked members have empty common kernel.
Each point has a true omitter of at most this size. One point has a true
omitter of exactly that size and belongs to every smaller crooked member. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258 ≤ N) (hi : N ≤ 21000)
    (legal : Legal (Ground N) F) (counter : B N < F.card) :
    ∃ m : ℕ, 42 ≤ m ∧ m ≤ 265 ∧
      (∀ x ∈ Ground N, ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ m) ∧
      (∃ c ∈ Ground N, ∃ T ∈ CrookedMembers F, c ∉ T ∧ T.card=m ∧
        ∀ S ∈ CrookedMembers F, S.card < m → c ∈ S) ∧
      (m ≤ 45 → ∀ P ∈ F, 42 ≤ P.card) := by
  classical
  let cover := fun k : ℕ => ∀ x ∈ Ground N, ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ k
  have top : cover 265 := by
    intro c hc
    have misses : ∃ T ∈ SparseCrooked N 12 F, c ∉ T := by
      by_contra! common
      apply (not_lt_of_ge (RootedFamily20258.actual_upper (by omega) (by omega) legal ⟨c,hc,?_⟩)) counter
      intro T hT bad
      exact common T (actual_sparse_membership.mpr
        ⟨(Finset.mem_sdiff.mp hT).1,bad,actual_retained_crooked_sparse hT bad⟩)
    obtain ⟨T,hT,miss⟩ := misses
    by_contra! large
    have upper := LargeOmitter20258.actual_upper_at_266 (by omega) hi legal hT miss (by
      intro S hS hmiss
      obtain ⟨mem,bad,_⟩ := actual_sparse_membership.mp hS
      have h := large S (Finset.mem_filter.mpr ⟨mem,bad⟩) hmiss
      omega)
    unfold B at counter
    omega
  have possible : ∃ k : ℕ, cover k := ⟨265,top⟩
  let m := Nat.find possible
  have covers : cover m := Nat.find_spec possible
  have ceiling : m ≤ 265 := Nat.find_min' possible top
  have small (le : m ≤ 45) : ∀ P ∈ F, 42 ≤ P.card := by
    intro P member
    by_contra! tiny
    exact (not_lt_of_ge (SmallFortyOne20258.actual_upper lo (by omega) legal member (by omega) (by
      intro x hx
      obtain ⟨S,hS,miss,sz⟩ := covers x hx
      exact ⟨S,hS,miss,sz.trans le⟩))) counter
  have floor : 42 ≤ m := by
    by_contra! h
    have one : (1 : ℤ) ∈ Ground N := (mem_ground N 1).mpr ⟨by decide,by omega⟩
    obtain ⟨S,hS,_,sz⟩ := covers 1 one
    have := small (by omega) S (Finset.mem_filter.mp hS).1
    omega
  have prior : ∃ c ∈ Ground N, ∀ S ∈ CrookedMembers F, S.card < m → c ∈ S := by
    by_contra! no
    apply Nat.find_min possible (show m-1 < m by omega)
    intro x hx
    obtain ⟨S,hS,sz,miss⟩ := no x hx
    exact ⟨S,hS,miss,by omega⟩
  obtain ⟨c,hc,root⟩ := prior
  obtain ⟨T,hT,miss,sz⟩ := covers c hc
  have eq : T.card=m := le_antisymm sz (le_of_not_gt (fun h => miss (root T hT h)))
  exact ⟨m,floor,ceiling,covers,⟨c,hc,T,hT,miss,eq,root⟩,small⟩

#print axioms actual
end
end JSP233.FirstEmptyKernel20258
