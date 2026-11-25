module

public import Erdos272.Global.N20258.ConcentratedBlocks20258

@[expose] public section
namespace JSP233.ConcentratedFortyFive20258
open StarCompletion PrivatePairExistence FirstSparseCut20258 Density41 SparseSmall39
open ConcentratedBlocks20258 EndpointCover20258
set_option autoImplicit false

private def route : Route := ⟨45,45,80,.marked ⟨45,100,17,3000⟩⟩
private def ends := [20424,20656,20983,21438,22077,22599]

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem paid : route.source.Valid := by decide +kernel

set_option maxRecDepth 32000 in
set_option maxHeartbeats 3000000 in
private theorem checked (i : Fin 6) : let p := (rows 20258 ends)[i.val]!
    route.Good p.1 p.2 := by
  fin_cases i <;> decide +kernel

/-- A first cutoff of 45 is impossible in a counterexample, including
the entire case of a large population of sparse crooked members. -/
theorem of_cut {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 20258≤N) (legal : Legal (Ground N) F) (cut : Cut N F 45 c T) : F.card≤B N := by
  by_cases high : 22600≤N
  · exact FortyFourFamily20258.of_member (by omega) (by omega) legal
      (actual_sparse_membership.mp cut.omitter).1 cut.crooked (by rw [cut.size]; omega)
  obtain ⟨q,hq,l,u,_⟩ := locate ends (by decide +kernel : increasing 20258 22599 ends=true) lo (by omega)
  have indices : ∀ p∈rows 20258 ends, ∃ i : Fin 6, p=(rows 20258 ends)[i.val]! := by decide +kernel
  obtain ⟨i,h⟩ := indices q hq
  exact ConcentratedBlocks20258.upper (r:=route) l u le_rfl le_rfl legal cut paid (h ▸ checked i)

/-- If every ground point has a crooked omitter of at most 45 points,
the original family already satisfies the conjectured bound. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258≤N) (legal : Legal (Ground N) F)
    (omits : ∀ z∈Ground N, ∃ S∈CrookedMembers F,z∉S ∧ S.card≤45) : F.card≤B N := by
  classical
  by_contra! counter
  obtain ⟨c,hc,large⟩ := FortyFourFamily20258.counterexample_site lo legal counter
  obtain ⟨T,ht,miss,sz⟩ := omits c hc
  have sparse (S : Finset ℤ) (hs : S∈CrookedMembers F) (small : S.card≤45) : S∈SparseCrooked N 12 F := by
    obtain ⟨mem,bad⟩ := Finset.mem_filter.mp hs
    exact actual_sparse_membership.mpr ⟨mem,bad,by omega⟩
  apply (not_lt_of_ge (of_cut lo legal (c:=c) (T:=T) ?_)) counter
  refine ⟨hc,sparse T ht sz,miss,le_antisymm sz (large T ht miss),?_,?_⟩
  · intro z hz
    obtain ⟨S,hs,away,size⟩ := omits z hz
    exact ⟨S,sparse S hs size,away,size⟩
  · intro S hs away
    obtain ⟨mem,bad,_⟩ := actual_sparse_membership.mp hs
    exact large S (Finset.mem_filter.mpr ⟨mem,bad⟩) away

#print axioms of_cut
#print axioms actual
end JSP233.ConcentratedFortyFive20258
