module

public import Erdos272.Counting.N20258.MarkedPairCount20258
public import Erdos272.Foundation.PrivateUnion

@[expose] public section
namespace JSP233.ConcentratedCores20258
open StarCompletion APGeometry APCount41 MarkedPairCount20258
open scoped Classical
set_option autoImplicit false

private theorem union_at {P : Finset ℤ → Finset ℤ} {C : Finset (Finset ℤ)} {d t : ℤ}
    (ne : C.Nonempty) (atPoint : ∀ S∈C,APAt d t (P S) ∧ t∈P S) :
    APAt d t (C.biUnion P) ∧ t∈C.biUnion P := by
  classical
  induction C using Finset.induction_on with
  | empty => simp at ne
  | @insert S C hs ih =>
    obtain ⟨ap,mem⟩ := atPoint S (Finset.mem_insert_self ..)
    rcases C.eq_empty_or_nonempty with empty|nonempty
    · subst C; simpa using And.intro ap mem
    obtain ⟨rest,hit⟩ := ih nonempty (fun T ht => atPoint T (Finset.mem_insert_of_mem ht))
    rw [Finset.biUnion_insert]
    refine ⟨?_,Finset.mem_union_left _ mem⟩
    simpa only [APAt,Finset.mem_union] using
      PrivateUnion.union_APAt d t (fun x => x∈P S) (fun x => x∈C.biUnion P) ap rest mem hit

/-- Two sufficiently numerous families, each having a common core point,
have intersecting core unions. Otherwise each ordered pair must be paid by
an exterior incidence in the row or column, with at most s*o in either. -/
private theorem cross {A C D : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {s o : ℕ}
    (subC : C⊆A) (subD : D⊆A) (largeC : 2*s*o<C.card) (largeD : 2*s*o<D.card)
    (pivotC : ∃ z,∀ S∈C,z∈P S) (pivotD : ∃ z,∀ S∈D,z∈P S)
    (meet : ∀ S∈A,∀ T∈A,(S∩T).Nonempty) (size : ∀ S∈A,S.card≤s)
    (pair : ∀ t x,((A.filter (fun S => t∈P S)).filter (fun S => x∈S\P S)).card≤o) :
    ((C.biUnion P)∩(D.biUnion P)).Nonempty := by
  classical
  by_contra miss
  let rel (S T : Finset ℤ) := (S∩(T\P T)).Nonempty
  have each {G : Finset (Finset ℤ)} (sub : G⊆A) (common : ∃ z,∀ S∈G,z∈P S)
      {S : Finset ℤ} (mem : S∈A) : (G.filter (rel S)).card≤s*o := by
    obtain ⟨t,ht⟩ := common
    apply (hits G S (fun T => T\P T) ?_).trans (Nat.mul_le_mul_right o (size S mem))
    intro x _
    apply (Finset.card_le_card ?_).trans (pair t x)
    intro T hT
    obtain ⟨inG,ext⟩ := Finset.mem_filter.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨sub inG,ht T inG⟩,ext⟩
  have total := rectangle C D rel rel (l:=s*o) (r:=s*o) (by
    intro S hs T ht
    obtain ⟨x,hx⟩ := meet S (subC hs) T (subD ht)
    obtain ⟨xs,xt⟩ := Finset.mem_inter.mp hx
    by_cases inT : x∈P T
    · have outside : x∉P S := fun h => miss ⟨x,Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨S,hs,h⟩,Finset.mem_biUnion.mpr ⟨T,ht,inT⟩⟩⟩
      exact Or.inr ⟨x,Finset.mem_inter.mpr ⟨xt,Finset.mem_sdiff.mpr ⟨xs,outside⟩⟩⟩
    · exact Or.inl ⟨x,Finset.mem_inter.mpr ⟨xs,Finset.mem_sdiff.mpr ⟨xt,inT⟩⟩⟩)
    (fun S hs => each subD pivotD (subC hs)) (fun T ht => each subC pivotC (subD ht))
  have lc := Nat.mul_lt_mul_of_pos_right largeC (by omega : 0<D.card)
  have ld := Nat.mul_lt_mul_of_pos_left largeD (by omega : 0<C.card)
  nlinarith only [lc,ld,total]

/-- For each stride there is one pivot whose removal leaves bounded core
depth everywhere. The pivot is the smallest right endpoint among the
unions of all large subfamilies having a common core point. -/
theorem pivot {A : Finset (Finset ℤ)} {P : Finset ℤ → Finset ℤ} {d : ℤ} {s o : ℕ}
    (step : ∀ S∈A,∃ p,APAt d p (P S)) (meet : ∀ S∈A,∀ T∈A,(S∩T).Nonempty)
    (size : ∀ S∈A,S.card≤s)
    (pair : ∀ t x,((A.filter (fun S => t∈P S)).filter (fun S => x∈S\P S)).card≤o) :
    ∃ t,∀ z,((A.filter (fun S => t∉P S)).filter (fun S => z∈P S)).card≤2*s*o := by
  classical
  let families := A.powerset.filter (fun C => 2*s*o<C.card ∧ ∃ z,∀ S∈C,z∈P S)
  have info {C} (mem : C∈families) : C⊆A ∧ 2*s*o<C.card ∧ ∃ z,∀ S∈C,z∈P S := by
    obtain ⟨sub,rest⟩ := Finset.mem_filter.mp mem
    exact ⟨Finset.mem_powerset.mp sub,rest⟩
  have ap {C} (mem : C∈families) : ∃ z,APAt d z (C.biUnion P) ∧ z∈C.biUnion P := by
    obtain ⟨sub,num,z,hz⟩ := info mem
    apply Exists.intro z
    apply union_at (Finset.card_pos.mp (by omega))
    intro S hs
    obtain ⟨p,hp⟩ := step S (sub hs)
    exact ⟨apAt_rebase hp (hz S hs),hz S hs⟩
  obtain ⟨t,all⟩ : ∃ t,∀ C∈families,t∈C.biUnion P := by
    rcases families.eq_empty_or_nonempty with empty|nonempty
    · exact ⟨0,by simp [empty]⟩
    obtain ⟨C,hC,least⟩ := Finset.exists_min_image families (fun D => High (D.biUnion P)) nonempty
    refine ⟨High (C.biUnion P),?_⟩
    intro D hD
    obtain ⟨p,cp,hp⟩ := ap hC
    obtain ⟨q,dq,hq⟩ := ap hD
    obtain ⟨sc,lc,pc⟩ := info hC
    obtain ⟨sd,ld,pd⟩ := info hD
    exact CoreCleanup208.same_step_intersection_high cp dq ⟨p,hp⟩ ⟨q,hq⟩ (least D hD)
      (cross sc sd lc ld pc pd meet size pair)
  refine ⟨t,?_⟩
  intro z
  let C := (A.filter (fun S => t∉P S)).filter (fun S => z∈P S)
  change C.card≤_
  by_contra! large
  have sub : C⊆A := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have mem : C∈families := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr sub,large,
    z,fun _ hs => (Finset.mem_filter.mp hs).2⟩
  obtain ⟨S,hs,h⟩ := Finset.mem_biUnion.mp (all C mem)
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2 h

#print axioms pivot
end JSP233.ConcentratedCores20258
