module

public import Erdos272.Core.N65172.APCoatom65172

@[expose] public section
namespace JSP233.SharedOutside20258
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- If another member contains the unique point outside an AP core and
three core points, its actual intersection has stride at least twice
the core stride. An off-grid outside point allows at most two core hits. -/
theorem stride {Ω P T : Finset ℤ} {F : Finset (Finset ℤ)} {d p x : ℤ}
    (legal : Legal Ω F) (hS : insert x P∈F) (hT : T∈F) (ne : insert x P≠T)
    (core : APAt d p P) (bad : ¬IsAP (insert x P)) (out : x∉P) (hit : x∈T)
    (three : 3≤(P∩T).card) :
    ∃ e q, APAt e q (insert x P∩T) ∧ d∣e ∧ 2*d≤e ∧ d∣x-p := by
  let I := insert x P∩T
  have eqI : I=insert x (P∩T) := by
    ext z
    by_cases eqn : z=x
    · subst z; simp [I,hit]
    · simp [I,eqn]
  have four : 4≤I.card := by
    have outside : x∉P∩T := fun h => out (Finset.mem_inter.mp h).1
    rw [eqI,Finset.card_insert_of_notMem outside]
    omega
  have missed : (I\P).card≤1 := by
    have sub : I\P⊆{x} := by
      intro z hz
      obtain ⟨mem,no⟩ := Finset.mem_sdiff.mp hz
      exact Finset.mem_singleton.mpr ((Finset.mem_insert.mp (Finset.mem_inter.mp mem).1).resolve_right no)
    simpa using Finset.card_le_card sub
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0<(P∩T).card by omega)
  have uP := (Finset.mem_inter.mp hu).1
  have uI : u∈I := eqI ▸ Finset.mem_insert_of_mem hu
  have xI : x∈I := eqI ▸ Finset.mem_insert_self _ _
  obtain ⟨e,q,step,_⟩ := (isAP_iff_exists_APAt I).mp (legal.2 _ hS T hT ne)
  have multiple := APCoatom65172.step_divides step core four missed
  have different : d≠e := by
    rintro rfl
    have unite : IsAP (P∪I) := by
      apply (isAP_iff_exists_APAt _).mpr
      refine ⟨d,u,?_,Finset.mem_union_left _ uP⟩
      change PrivateUnion.APAt d u (fun z => z∈P∪I)
      simpa only [Finset.mem_union] using PrivateUnion.union_APAt d u
        (fun z => z∈P) (fun z => z∈I) (apAt_rebase core uP) (apAt_rebase step uI) uP uI
    have all : P∪I=insert x P := by ext z; rw [eqI]; simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_insert]; tauto
    exact bad (all ▸ unite)
  have gap : 2*d≤e := by
    obtain ⟨t,ht⟩ := multiple
    have dp := core.1
    have ep := step.1
    have tp : 0<t := by
      by_contra! no
      have := mul_nonpos_of_nonneg_of_nonpos dp.le no
      omega
    have two : 2≤t := by
      by_contra! small
      have eq : t=1 := by omega
      exact different (by simpa [eq] using ht.symm)
    nlinarith only [mul_le_mul_of_nonneg_left two dp.le,ht]
  have phase := multiple.trans (apAt_dvd_sub step uI xI)
  obtain ⟨_,l,h,members⟩ := core
  have up := ((members u).mp uP).2.2
  have add := Int.dvd_add phase up
  have same : x-u+(u-p)=x-p := by ring
  rw [same] at add
  exact ⟨e,q,step,multiple,gap,add⟩

/-- The second member need not itself have an AP core.
More than half of the marked core forces distinct outside points. -/
theorem half {Ω P T : Finset ℤ} {F : Finset (Finset ℤ)} {d p x : ℤ}
    (legal : Legal Ω F) (hS : insert x P∈F) (hT : T∈F) (ne : insert x P≠T)
    (core : APAt d p P) (bad : ¬IsAP (insert x P)) (out : x∉P) (hit : x∈T) :
    (P∩T).card≤2 ∨ 2*(P∩T).card≤P.card+1 := by
  by_cases few : (P∩T).card≤2
  · exact Or.inl few
  right
  have three : 3≤(P∩T).card := by omega
  obtain ⟨e,q,step,_,gap,_⟩ := stride legal hS hT ne core bad out hit three
  let R := P∩T
  have rne : R.Nonempty := Finset.card_pos.mp (by change 0<(P∩T).card; omega)
  let u := R.min' rne
  have hu : u∈R := Finset.min'_mem _ _
  have sub : R⊆P := Finset.inter_subset_left
  have pn := rne.mono sub
  have ui : u∈insert x P∩T := Finset.mem_inter.mpr
    ⟨Finset.mem_insert_of_mem (sub hu),(Finset.mem_inter.mp hu).2⟩
  have eq : P∩(insert x P∩T)=R := by ext z; simp only [R,Finset.mem_inter,Finset.mem_insert]; tauto
  have hr := apAt_inter (apAt_rebase core (sub hu)) (apAt_rebase step ui)
  rw [eq] at hr
  let l : ℤ := Int.lcm d e
  have dl : e∣l := (Int.coe_lcm_dvd_iff.mp (dvd_refl l)).2
  have el : e≤l := Int.le_of_dvd hr.1 dl
  have small := apAt_span_eq hr rne
  have big := apAt_span_eq core pn
  have low := Finset.min'_le P _ (sub (Finset.min'_mem R rne))
  have high := Finset.le_max' P _ (sub (Finset.max'_mem R rne))
  have rc : (1:ℤ)≤(R.card:ℤ) := by exact_mod_cast (show 1≤R.card from Finset.card_pos.mpr rne)
  have paid := mul_le_mul_of_nonneg_right (gap.trans el) (sub_nonneg.mpr rc)
  have lengths : 2*(R.card:ℤ)≤(P.card:ℤ)+1 := by
    apply (mul_le_mul_iff_right₀ core.1).mp
    change _=l*((R.card:ℤ)-1) at small
    nlinarith only [small,big,low,high,paid]
  exact_mod_cast lengths

theorem off_grid {Ω P T : Finset ℤ} {F : Finset (Finset ℤ)} {d p x : ℤ}
    (legal : Legal Ω F) (hS : insert x P∈F) (hT : T∈F) (ne : insert x P≠T)
    (core : APAt d p P) (bad : ¬IsAP (insert x P)) (out : x∉P) (hit : x∈T)
    (phase : ¬d∣x-p) : (P∩T).card≤2 := by
  by_contra! big
  obtain ⟨_,_,_,_,_,on⟩ := stride legal hS hT ne core bad out hit (by omega)
  exact phase on

/-- A subfamily whose AP cores all contain W has at most one marked
member per point of the complement of W under either overlap condition. -/
theorem band {Ω W : Finset ℤ} {F A : Finset (Finset ℤ)}
    (legal : Legal Ω F) (sub : A⊆F) (inside : W⊆Ω) (three : 3≤W.card)
    (P : Finset ℤ → Finset ℤ) (x d p : Finset ℤ → ℤ)
    (member : ∀ S∈A, S=insert (x S) (P S)) (outside : ∀ S∈A,x S∉P S)
    (core : ∀ S∈A, APAt (d S) (p S) (P S)) (bad : ∀ S∈A,¬IsAP S)
    (common : ∀ S∈A,W⊆P S)
    (wide : ∀ S∈A, (P S).card+1<2*W.card ∨ ¬d S∣x S-p S) : A.card≤Ω.card-W.card := by
  have point (S : Finset ℤ) (hs : S∈A) : x S∈S :=
    (congrArg (fun U : Finset ℤ => x S∈U) (member S hs)).mpr (Finset.mem_insert_self _ _)
  have inject : Set.InjOn x (A : Set (Finset ℤ)) := by
    intro S hs T ht eqx
    by_contra ne
    have st : insert (x S) (P S)≠T := (member S hs) ▸ ne
    have hit : x S∈T := by rw [eqx]; exact point T ht
    have intersection : W⊆P S∩T := by
      intro y hy
      exact Finset.mem_inter.mpr ⟨common S hs hy,member T ht ▸ Finset.mem_insert_of_mem (common T ht hy)⟩
    have sz := Finset.card_le_card intersection
    rcases wide S hs with many | off
    · rcases half legal (member S hs ▸ sub hs) (sub ht) st (core S hs) (member S hs ▸ bad S hs)
        (outside S hs) hit with a | a <;> omega
    · have a := off_grid legal (member S hs ▸ sub hs) (sub ht) st (core S hs) (member S hs ▸ bad S hs)
        (outside S hs) hit off
      omega
  have image : A.image x⊆Ω\W := by
    intro y hy
    obtain ⟨S,hs,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_sdiff.mpr ⟨legal.1 S (sub hs) (point S hs),fun hw => outside S hs (common S hs hw)⟩
  have bound := Finset.card_le_card image
  rw [Finset.card_image_of_injOn inject,Finset.card_sdiff_of_subset inside] at bound
  exact bound

#print axioms half
#print axioms off_grid
#print axioms band
end
end JSP233.SharedOutside20258
