module

public import Erdos272.Counting.N20258.PaddedSource20258

@[expose] public section
namespace JSP233.CutoffTranslation20258
open StarCompletion AffineLine30 PrivatePairExistence
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- The cutoff and its two witnesses are chosen on the true ground. -/
structure Witnesses (N : ℕ) (F : Finset (Finset ℤ)) (m : ℕ) (P : Finset ℤ) (c : ℤ) (T : Finset ℤ) : Prop where
  ground : c ∈ Ground N
  parent : P ∈ CrookedMembers F
  omitter : T ∈ CrookedMembers F
  misses : c ∉ T
  size : T.card=m
  minimum : ∀ S ∈ CrookedMembers F, P.card ≤ S.card
  rooted : ∀ S ∈ CrookedMembers F, c ∉ S → m ≤ S.card
  covers : ∀ x ∈ Ground N, ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ m

theorem crooked_map (F : Finset (Finset ℤ)) (j : ℤ) :
    CrookedMembers (mapFamily j 1 F)=mapFamily j 1 (CrookedMembers F) := by
  ext U
  constructor
  · intro hU
    obtain ⟨mem,bad⟩ := Finset.mem_filter.mp hU
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp mem
    exact Finset.mem_image.mpr ⟨S,Finset.mem_filter.mpr ⟨hS,fun ap => bad (affine_isAP j 1 (by decide) ap)⟩,rfl⟩
  · intro hU
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨mem,bad⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨S,mem,rfl⟩,fun ap => bad ((affine_isAP_iff j 1 (by decide) S).mp ap)⟩

theorem translate {N U j m : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ} {c : ℤ}
    (fits : j+N ≤ U) (legal : Legal (Ground N) F) (w : Witnesses N F m P c T) :
    Witnesses U (mapFamily j 1 F) m (mapSet j 1 P) (affine j 1 c) (mapSet j 1 T) := by
  have pos : (0 : ℤ) < 1 := by decide
  have member (S : Finset ℤ) (hs : S ∈ CrookedMembers F) :
      mapSet j 1 S ∈ CrookedMembers (mapFamily j 1 F) := by
    rw [crooked_map]
    exact Finset.mem_image.mpr ⟨S,hs,rfl⟩
  have cg := (mem_ground N c).mp w.ground
  refine ⟨(mem_ground U _).mpr (by simp only [affine,one_mul]; omega),member P w.parent,
    member T w.omitter,fun h => w.misses ((mem_mapSet j 1 pos T c).mp h),
    (mapSet_card j 1 pos T).trans w.size,?_,?_,?_⟩
  · intro S hs
    rw [crooked_map] at hs
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hs
    simpa only [mapSet_card j 1 pos] using w.minimum A hA
  · intro S hs miss
    rw [crooked_map] at hs
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hs
    rw [mapSet_card j 1 pos]
    exact w.rooted A hA (fun h => miss ((mem_mapSet j 1 pos A c).mpr h))
  · intro y _
    let x := y-j
    have eq : affine j 1 x=y := by dsimp only [affine,x]; ring
    have pull : ∃ S ∈ CrookedMembers F, x ∉ S ∧ S.card ≤ m := by
      by_cases inside : x ∈ Ground N
      · exact w.covers x inside
      · exact ⟨T,w.omitter,fun hx => inside (legal.1 T (Finset.mem_filter.mp w.omitter).1 hx),w.size.le⟩
    obtain ⟨S,hs,miss,sm⟩ := pull
    exact ⟨mapSet j 1 S,member S hs,fun hy => miss ((mem_mapSet j 1 pos S x).mp (eq.symm ▸ hy)),
      (mapSet_card j 1 pos S).le.trans sm⟩

#print axioms translate
end
end JSP233.CutoffTranslation20258
