import Erdos272.Core.ThinCore36

/-! Cross-step matching of all actual large rooted AP windows outside the
reserved exterior corner. The retained-family final count is not asserted. -/
namespace JSP233.CoreAP36
open StarCompletion StaircaseGeometry AffineLine30 CrossLine30 StepHall33 ThinCore36
open scoped Classical BigOperators
noncomputable section

def APWindow (c d : ℕ) (p : ℕ×ℕ) : Finset ℤ :=
  mapSet (c:ℤ) (d:ℤ) (Window p.1 p.2)

theorem apWindow_injective (c d : ℕ) (hd : 0<d) : Function.Injective (APWindow c d) := by
  intro p q he
  have hdZ : (0:ℤ)<d := by exact_mod_cast hd
  exact window_injective ((mapSet_injective (c:ℤ) (d:ℤ) hdZ) he)

theorem actual_fixed_step_matching (N c L R d : ℕ) (C : Finset (ℕ×ℕ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N) (hd : 0<d)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ p∈C, APWindow c d p⊆Ground N)
    (hvalid : ∀ p∈C, 3≤p.1+p.2) :
    ∃ f : C→Option (Finset ℤ), Function.Injective f ∧
      (∀ p, f p=none → 2*d≤c-1) ∧
      ∀ p, f p=none ∨ ∃ Q, f p=some Q ∧ Q⊆APWindow c d p.val ∧
        IsStepPrimitive (c:ℤ) (d:ℤ) Q ∧ ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q := by
  by_cases hdt : d≤L+N-R
  · exact actual_core_cutoff_matching N c L R d C hc hcL hLR hRN hd hdt hcore hground hvalid
  · let F := C.image (APWindow c d)
    have hdZ : (0:ℤ)<d := by exact_mod_cast hd
    have hgroundF : ∀ S∈F, S⊆Ground N := by
      intro S hS
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hS
      exact hground p hp
    have hF : ∀ S∈F, ∃ l r : ℕ, S=mapSet (c:ℤ) (d:ℤ) (Window l r) ∧ 4≤S.card := by
      intro S hS
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hS
      refine ⟨p.1,p.2,he.symm,?_⟩
      rw [←he,APWindow,mapSet_card _ _ hdZ,window_card]
      have hh := hvalid p hp
      omega
    obtain ⟨f,hf,hfn,hm⟩ := actual_step_matching_with_dummy_geometry N (c:ℤ) (d:ℤ)
      hdZ F hgroundF hF
    let e : C→F := fun p => ⟨APWindow c d p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩
    have he : Function.Injective e := by
      intro p q hpq
      apply Subtype.ext
      exact apWindow_injective c d hd (congrArg Subtype.val hpq)
    have hLt : L≤L+N-R := by omega
    have hgap : (L:ℤ)-(c:ℤ)<(d:ℤ) := by
      have hLd : L<d := by omega
      have hLdZ : (L:ℤ)<(d:ℤ) := by exact_mod_cast hLd
      omega
    refine ⟨fun p => f (e p),hf.comp he,?_,?_⟩
    · intro p hn
      have hh := hfn (e p) hn
      have hcsub : ((c-1:ℕ):ℤ)=(c:ℤ)-1 := by omega
      rw [←hcsub] at hh
      exact_mod_cast hh
    · intro p
      rcases hm (e p) with hn | ⟨Q,hQ,hsub,hprim⟩
      · exact Or.inl hn
      · refine Or.inr ⟨Q,hQ,hsub,hprim,?_⟩
        exact large_step_pair_not_exterior (c:ℤ) (d:ℤ) (L:ℤ) (R:ℤ) hdZ hgap
          (APWindow c d p.val) Q ⟨p.val.1,p.val.2,rfl⟩ hsub

def StepCells (C : Finset (ℕ×(ℕ×ℕ))) (d : ℕ) : Finset (ℕ×ℕ) :=
  (C.filter (fun q => q.1=d)).image Prod.snd

theorem mem_stepCells (C : Finset (ℕ×(ℕ×ℕ))) (d : ℕ) (p : ℕ×ℕ) :
    p∈StepCells C d ↔ (d,p)∈C := by
  constructor
  · intro hp
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp
    obtain ⟨hqC,hqd⟩ := Finset.mem_filter.mp hq
    have he : q=(d,p) := Prod.ext hqd hqp
    exact he ▸ hqC
  · intro hp
    exact Finset.mem_image.mpr ⟨(d,p),Finset.mem_filter.mpr ⟨hp,rfl⟩,rfl⟩

def RowCertificate (c L R d : ℕ) (p : ℕ×ℕ) (o : Option (Finset ℤ)) : Prop :=
  (o=none → 2*d≤c-1) ∧ ∀ Q, o=some Q →
    Q⊆APWindow c d p ∧ IsStepPrimitive (c:ℤ) (d:ℤ) Q ∧
      ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q

theorem all_local_functions (N c L R : ℕ) (C : Finset (ℕ×(ℕ×ℕ)))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hstep : ∀ q∈C, 0<q.1)
    (hground : ∀ q∈C, APWindow c q.1 q.2⊆Ground N)
    (hvalid : ∀ q∈C, 3≤q.2.1+q.2.2) :
    ∃ f : ℕ→(ℕ×ℕ)→Option (Finset ℤ),
      (∀ d, Set.InjOn (f d) (StepCells C d)) ∧
      ∀ d p, p∈StepCells C d → RowCertificate c L R d p (f d p) := by
  have hex : ∀ d : ℕ, ∃ f : (ℕ×ℕ)→Option (Finset ℤ),
      Set.InjOn f (StepCells C d) ∧
        ∀ p∈StepCells C d, RowCertificate c L R d p (f p) := by
    intro d
    by_cases hd : 0<d
    · have hg : ∀ p∈StepCells C d, APWindow c d p⊆Ground N := by
        intro p hp
        exact hground (d,p) ((mem_stepCells C d p).mp hp)
      have hv : ∀ p∈StepCells C d, 3≤p.1+p.2 := by
        intro p hp
        exact hvalid (d,p) ((mem_stepCells C d p).mp hp)
      obtain ⟨f,hf,hfn,hm⟩ := actual_fixed_step_matching N c L R d (StepCells C d)
        hc hcL hLR hRN hd hcore hg hv
      have hcert : ∀ p : StepCells C d, RowCertificate c L R d p.val (f p) := by
        intro p
        refine ⟨hfn p,?_⟩
        intro Q hQ
        rcases hm p with hn | ⟨Q0,he,hsub,hprim,havoid⟩
        · rw [hn] at hQ
          cases hQ
        · have heQ : Q0=Q := Option.some.inj (he.symm.trans hQ)
          exact heQ ▸ ⟨hsub,hprim,havoid⟩
      let g : (ℕ×ℕ)→Option (Finset ℤ) := fun p =>
        if hp : p∈StepCells C d then f ⟨p,hp⟩ else none
      refine ⟨g,?_,?_⟩
      · intro p hp q hq he
        change p∈StepCells C d at hp
        change q∈StepCells C d at hq
        have he0 : f ⟨p,hp⟩=f ⟨q,hq⟩ := by simpa [g,hp,hq] using he
        exact congrArg Subtype.val (hf he0)
      · intro p hp
        simpa only [g,dif_pos hp] using hcert ⟨p,hp⟩
    · have hn : ∀ p, p∉StepCells C d := by
        intro p hp
        have hh := hstep (d,p) ((mem_stepCells C d p).mp hp)
        exact hd hh
      refine ⟨fun _ => none,?_,?_⟩
      · intro p hp
        exact (hn p hp).elim
      · intro p hp
        exact (hn p hp).elim
  choose f hf using hex
  exact ⟨f,fun d => (hf d).1,fun d p hp => (hf d).2 p hp⟩

def Tag (d : ℕ) (o : Option (Finset ℤ)) : ℕ⊕Finset ℤ :=
  match o with
  | none => Sum.inl d
  | some Q => Sum.inr Q

theorem tag_injective (d : ℕ) : Function.Injective (Tag d) := by
  intro x y he
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some Q => simp [Tag] at he
  | some Q =>
    cases y with
    | none => simp [Tag] at he
    | some P => exact congrArg some (Sum.inr.inj he)

theorem coordinate_core_ap_matching (N c L R : ℕ) (C : Finset (ℕ×(ℕ×ℕ)))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hstep : ∀ q∈C, 0<q.1)
    (hground : ∀ q∈C, APWindow c q.1 q.2⊆Ground N)
    (hvalid : ∀ q∈C, 3≤q.2.1+q.2.2) :
    ∃ f : C→ℕ⊕Finset ℤ, Function.Injective f ∧ ∀ p,
      (f p=Sum.inl p.val.1 ∧ 2*p.val.1≤c-1) ∨
        ∃ Q, f p=Sum.inr Q ∧ Q⊆APWindow c p.val.1 p.val.2 ∧
          IsStepPrimitive (c:ℤ) (p.val.1:ℤ) Q ∧ ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q := by
  obtain ⟨g,hginj,hcert⟩ := all_local_functions N c L R C hc hcL hLR hRN hcore hstep hground hvalid
  have hmem (p : C) : p.val.2∈StepCells C p.val.1 := (mem_stepCells _ _ _).mpr p.property
  let f : C→ℕ⊕Finset ℤ := fun p => Tag p.val.1 (g p.val.1 p.val.2)
  have hkey : ∀ p q : C, f p=f q → p.val.1=q.val.1 := by
    intro p q he
    cases hp : g p.val.1 p.val.2 with
    | none =>
      cases hq : g q.val.1 q.val.2 with
      | none => simpa only [f,Tag,hp,hq,Sum.inl.injEq] using he
      | some Q => simp [f,Tag,hp,hq] at he
    | some Q =>
      cases hq : g q.val.1 q.val.2 with
      | none => simp [f,Tag,hp,hq] at he
      | some P =>
        have heQ : Q=P := by simpa only [f,Tag,hp,hq,Sum.inr.injEq] using he
        have hp0 := (hcert p.val.1 p.val.2 (hmem p)).2 Q hp
        have hq0 := (hcert q.val.1 q.val.2 (hmem q)).2 P hq
        rw [←heQ] at hq0
        have hd := primitive_step_unique
          (by exact_mod_cast hstep p.val p.property)
          (by exact_mod_cast hstep q.val q.property) hp0.2.1 hq0.2.1
        exact_mod_cast hd
  refine ⟨f,?_,?_⟩
  · intro p q he
    have hd := hkey p q he
    change Tag p.val.1 (g p.val.1 p.val.2)=Tag q.val.1 (g q.val.1 q.val.2) at he
    rw [←hd] at he
    have ho := tag_injective p.val.1 he
    have hqmem : q.val.2∈StepCells C p.val.1 := by rw [hd]; exact hmem q
    have hcells := hginj p.val.1 (hmem p) hqmem ho
    exact Subtype.ext (Prod.ext hd hcells)
  · intro p
    cases hp : g p.val.1 p.val.2 with
    | none =>
      exact Or.inl ⟨by simp [f,Tag,hp],(hcert _ _ (hmem p)).1 hp⟩
    | some Q =>
      have hh := (hcert _ _ (hmem p)).2 Q hp
      exact Or.inr ⟨Q,by simp [f,Tag,hp],hh.1,hh.2.1,hh.2.2⟩

theorem actual_AP_nat_representation (c : ℕ) (S : Finset ℤ)
    (hAP : IsAP S) (hroot : (c:ℤ)∈S) (hlarge : 4≤S.card) :
    ∃ q : ℕ×(ℕ×ℕ), 0<q.1 ∧ S=APWindow c q.1 q.2 ∧ 3≤q.2.1+q.2.2 := by
  obtain ⟨d,hd,l,r,hrep⟩ := actual_AP_representation hAP hroot
  have hcast : (d.toNat:ℤ)=d := Int.toNat_of_nonneg hd.le
  have hdn : 0<d.toNat := by omega
  have hcard : S.card=l+r+1 := by rw [hrep,mapSet_card _ _ hd,window_card]
  refine ⟨(d.toNat,(l,r)),hdn,?_,?_⟩
  · simpa only [APWindow,hcast] using hrep
  · change 3≤l+r
    omega

theorem actual_core_root_AP_matching (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F (c:ℤ)) (hlarge : ∀ S∈F, 4≤S.card) :
    ∃ f : F→ℕ⊕Finset ℤ, Function.Injective f ∧ ∀ S,
      (∃ d, f S=Sum.inl d ∧ 0<d ∧ 2*d≤c-1) ∨
        ∃ Q, f S=Sum.inr Q ∧ Q⊆S.val ∧
          IsStepPrimitive (c:ℤ) (trueStep (c:ℤ) S.val) Q ∧
            ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q := by
  have hex : ∀ S : F, ∃ q : ℕ×(ℕ×ℕ),
      0<q.1 ∧ S.val=APWindow c q.1 q.2 ∧ 3≤q.2.1+q.2.2 := by
    intro S
    exact actual_AP_nat_representation c S.val (hAP S.val S.property)
      (hroot S.val S.property) (hlarge S.val S.property)
  choose q hq using hex
  let C := Finset.univ.image q
  have hstepC : ∀ p∈C, 0<p.1 := by
    intro p hp
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hp
    exact (hq S).1
  have hgroundC : ∀ p∈C, APWindow c p.1 p.2⊆Ground N := by
    intro p hp
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hp
    rw [←(hq S).2.1]
    exact hground S.val S.property
  have hvalidC : ∀ p∈C, 3≤p.2.1+p.2.2 := by
    intro p hp
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hp
    exact (hq S).2.2
  have hqinj : Function.Injective q := by
    intro S T he
    apply Subtype.ext
    calc
      S.val=APWindow c (q S).1 (q S).2 := (hq S).2.1
      _=APWindow c (q T).1 (q T).2 := by rw [he]
      _=T.val := (hq T).2.1.symm
  let e : F→C := fun S => ⟨q S,Finset.mem_image.mpr ⟨S,Finset.mem_univ S,rfl⟩⟩
  have heinj : Function.Injective e := by
    intro S T he
    exact hqinj (congrArg Subtype.val he)
  obtain ⟨g,hg,hm⟩ := coordinate_core_ap_matching N c L R C hc hcL hLR hRN hcore
    hstepC hgroundC hvalidC
  refine ⟨fun S => g (e S),hg.comp heinj,?_⟩
  intro S
  rcases hm (e S) with ⟨he,hbound⟩ | ⟨Q,he,hsub,hprim,havoid⟩
  · exact Or.inl ⟨(q S).1,he,(hq S).1,hbound⟩
  · have hrep : S.val=mapSet (c:ℤ) ((q S).1:ℤ) (Window (q S).2.1 (q S).2.2) := (hq S).2.1
    have hdtrue := trueStep_eq_of_representation (hAP S.val S.property)
      (hroot S.val S.property) (by have hh := hlarge S.val S.property; omega)
      (by exact_mod_cast (hq S).1) hrep
    have hsubS : Q⊆S.val := by rw [(hq S).2.1]; exact hsub
    exact Or.inr ⟨Q,he,hsubS,by simpa only [hdtrue] using hprim,havoid⟩

def CoreAPPairs (N c L R : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (StarResources30.CoveredAPBadPairs (c:ℤ) (Ground N) F).filter
    (fun Q => ¬ExteriorPair (c:ℤ) (L:ℤ) (R:ℤ) Q)

theorem actual_core_root_AP_card (N c L R : ℕ) (F : Finset (Finset ℤ))
    (hc : 1≤c) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hcore : 4*(L+N-R)*(Nat.log 2 N+1)≤N)
    (hground : ∀ S∈F, S⊆Ground N) (hAP : ∀ S∈F, IsAP S)
    (hroot : Rooted F (c:ℤ)) (hlarge : ∀ S∈F, 4≤S.card) :
    F.card≤(c-1)/2+(CoreAPPairs N c L R F).card := by
  obtain ⟨f,hf,hm⟩ := actual_core_root_AP_matching N c L R F hc hcL hLR hRN hcore
    hground hAP hroot hlarge
  let D := Finset.Icc 1 ((c-1)/2)
  let P := CoreAPPairs N c L R F
  let U := (D.image (Sum.inl : ℕ→ℕ⊕Finset ℤ))∪(P.image Sum.inr)
  have hmem : ∀ S : F, f S∈U := by
    intro S
    rcases hm S with ⟨d,he,hd,hbound⟩ | ⟨Q,he,hsub,hprim,havoid⟩
    · have hdD : d∈D := by
        apply Finset.mem_Icc.mpr
        refine ⟨by omega,?_⟩
        apply (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr
        omega
      rw [he]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d,hdD,rfl⟩)
    · have hQP : Q∈P := by
        apply Finset.mem_filter.mpr
        refine ⟨?_,havoid⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr (hsub.trans (hground S.val S.property)),
          hprim.1,hprim.2.1,hprim.2.2.1,?_⟩
        exact ⟨S.val,S.property,hAP S.val S.property,hsub⟩
      rw [he]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨Q,hQP,rfl⟩)
  have hsub : (Finset.univ.image f)⊆U := by
    intro x hx
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hx
    exact hmem S
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hf] at hcount
  have hdis : Disjoint (D.image (Sum.inl : ℕ→ℕ⊕Finset ℤ)) (P.image Sum.inr) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨Q,_,he⟩ := Finset.mem_image.mp hy
    exact Sum.inr_ne_inl he
  have hU : U.card=D.card+P.card := by
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hD : D.card=(c-1)/2 := by simp [D]
  rw [hU,hD] at hcount
  simpa only [Finset.card_univ,Fintype.card_coe] using hcount

#print axioms apWindow_injective
#print axioms actual_fixed_step_matching
#print axioms mem_stepCells
#print axioms all_local_functions
#print axioms tag_injective
#print axioms coordinate_core_ap_matching
#print axioms actual_AP_nat_representation
#print axioms actual_core_root_AP_matching
#print axioms actual_core_root_AP_card
end
end JSP233.CoreAP36
