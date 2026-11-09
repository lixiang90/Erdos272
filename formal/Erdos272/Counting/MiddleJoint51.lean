module

public import Erdos272.Geometry.MiddleCoordinates51

@[expose] public section
namespace JSP233.MiddleJoint51
open StarCompletion APGeometry LongTerminal35 WitnessInterval43 MiddleCoordinates51
open APCount41 APPrepare49 PreparedWitness48 PreparedClasses50 DenseDeletion40 FamilyReflect43 RestrictedWitness44
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

def CoprimeBox (A₀ A₁ B₀ B₁ : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.Ioc A₀ A₁).product (Finset.Ioc B₀ B₁)).filter (fun p=>p.1.Coprime p.2)

def UpperTriangle (A B : ℕ) : Finset (ℕ×ℕ) :=
  (CoprimeBox A B A B).filter (fun p=>p.1<p.2)

theorem coprime_box_card_le (A₀ A₁ B₀ B₁ : ℕ) :
    (CoprimeBox A₀ A₁ B₀ B₁).card≤(A₁-A₀)*(B₁-B₀) := by
  have hh := Finset.card_filter_le ((Finset.Ioc A₀ A₁).product (Finset.Ioc B₀ B₁))
    (fun p:ℕ×ℕ=>p.1.Coprime p.2)
  simpa only [CoprimeBox,Finset.product_eq_sprod,Finset.card_product,Nat.card_Ioc] using hh

theorem twice_upper_triangle_card_le (A B : ℕ) :
    2*(UpperTriangle A B).card ≤ (CoprimeBox A B A B).card := by
  classical
  let T := UpperTriangle A B
  have hinj : Function.Injective (Prod.swap : ℕ × ℕ → ℕ × ℕ) := Prod.swap_injective
  have hdis : Disjoint T (T.image Prod.swap) := by
    apply Finset.disjoint_left.mpr
    intro p hp hp'
    obtain ⟨q,hq,hqp⟩ := Finset.mem_image.mp hp'
    have hltp := (Finset.mem_filter.mp hp).2
    have hltq := (Finset.mem_filter.mp hq).2
    have hfst := congrArg Prod.fst hqp
    have hsnd := congrArg Prod.snd hqp
    change q.2 = p.1 at hfst
    change q.1 = p.2 at hsnd
    omega
  have hsub : T ∪ T.image Prod.swap ⊆ CoprimeBox A B A B := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (Finset.mem_filter.mp hp).1
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hqi,hcop⟩ := Finset.mem_filter.mp (Finset.mem_filter.mp hq).1
      have hqI := Finset.mem_product.mp hqi
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqI.2,hqI.1⟩,hcop.symm⟩
  have hh := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,Finset.card_image_of_injective _ hinj] at hh
  dsimp only [T] at hh
  omega


theorem coordinate_pools_exact {C A e M : ℕ} {E Wm Wp : Finset (ℕ × ℕ)}
    (hE : E ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e))
    (hWm : Wm ⊆ CoprimeBox 0 C A M) (hdis : Disjoint E Wm)
    (hWp : ∀ p ∈ Wp, 1 ≤ p.1 ∧ p.1 < p.2 ∧ e < p.2 ∧ p.2 ≤ M ∧ p.1.Coprime p.2) :
    E.card+Wm.card+Wp.card≤C*(e-A)+(CoprimeBox 0 C e M).card+
      (CoprimeBox 0 e e M).card+(UpperTriangle e M).card := by
  classical
  let W₀ := Wm.filter (fun p => p.2 ≤ e)
  let W₁ := Wm.filter (fun p => ¬p.2 ≤ e)
  let V₀ := Wp.filter (fun p => p.1 ≤ e)
  let V₁ := Wp.filter (fun p => ¬p.1 ≤ e)
  have hW₀ : W₀ ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e) := by
    intro p hp
    obtain ⟨hpW,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI,_hcop⟩ := Finset.mem_filter.mp (hWm hpW)
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpI
    obtain ⟨hp₁0,hp₁C⟩ := Finset.mem_Ioc.mp hp₁
    obtain ⟨hp₂A,_hp₂M⟩ := Finset.mem_Ioc.mp hp₂
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp₁0,hp₁C⟩,
      Finset.mem_Ioc.mpr ⟨hp₂A,hpe⟩⟩
  have hW₁ : W₁ ⊆ CoprimeBox 0 C e M := by
    intro p hp
    obtain ⟨hpW,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpI,hcop⟩ := Finset.mem_filter.mp (hWm hpW)
    obtain ⟨hp₁,hp₂⟩ := Finset.mem_product.mp hpI
    have hp₂M := (Finset.mem_Ioc.mp hp₂).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp₁,
      Finset.mem_Ioc.mpr ⟨by omega,hp₂M⟩⟩,hcop⟩
  have hV₀ : V₀ ⊆ CoprimeBox 0 e e M := by
    intro p hp
    obtain ⟨hpV,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp₁,hlt,hp₂e,hp₂M,hcop⟩ := hWp p hpV
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨hp₁,hpe⟩,Finset.mem_Ioc.mpr ⟨hp₂e,hp₂M⟩⟩,hcop⟩
  have hV₁ : V₁ ⊆ UpperTriangle e M := by
    intro p hp
    obtain ⟨hpV,hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨_hp₁,hlt,hp₂e,hp₂M,hcop⟩ := hWp p hpV
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨by omega,by omega⟩,Finset.mem_Ioc.mpr ⟨hp₂e,hp₂M⟩⟩,hcop⟩,hlt⟩
  have hrect : E.card+W₀.card≤C*(e-A) := by
    have hdis₀ : Disjoint E W₀ := hdis.mono_right (Finset.filter_subset _ _)
    have hsub := Finset.union_subset hE hW₀
    have hh := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdis₀] at hh
    simpa only [Finset.product_eq_sprod,Finset.card_product,Nat.card_Icc,
      Nat.card_Ioc,Nat.add_sub_cancel] using hh
  have hwm := Finset.card_le_card hW₁
  have hv0 := Finset.card_le_card hV₀
  have hv1 := Finset.card_le_card hV₁
  have hwp := Finset.card_filter_add_card_filter_not (s:=Wp) (fun p=>p.1≤e)
  have hmp := Finset.card_filter_add_card_filter_not (s:=Wm) (fun p=>p.2≤e)
  change W₀.card+W₁.card=Wm.card at hmp
  change V₀.card+V₁.card=Wp.card at hwp
  omega

theorem actual_intrinsic_not_AP {S Q : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hw : IntrinsicPair c S Q) : ¬IsAP S := by
  intro hAP
  exact hw.2.2.2 ⟨S,hAP,Finset.insert_subset_iff.mpr ⟨hc,hw.2.2.1⟩,Finset.Subset.refl S⟩

theorem actual_middle_step_joint {N c d C A M : ℕ} {F Cm Cp E : Finset (Finset ℤ)}
    (hd : 0<d) (hAM : A≤M)
    (hF : Legal (Ground N) F) (hMF : Cm ⊆ F) (hPF : Cp ⊆ F) (hEF : E ⊆ F)
    (hcM : ∀ S ∈ Cm, (c:ℤ)∈S) (hcP : ∀ S ∈ Cp, (c:ℤ)∈S)
    (m : {S // S ∈ Cm} → ℕ × ℕ) (p : {S // S ∈ Cp} → ℕ × ℕ)
    (model : {S // S∈E}→ℕ×ℕ)
    (hm : ∀ S, 1 ≤ (m S).1 ∧ (m S).1 ≤ C ∧ A < (m S).2 ∧ (m S).2 ≤ M ∧
      (m S).1.Coprime (m S).2 ∧ IntrinsicPair c S.val {(c:ℤ)-((m S).1:ℤ)*d,(c:ℤ)+((m S).2:ℤ)*d})
    (hp : ∀ S, 1 ≤ (p S).1 ∧ (p S).1 < (p S).2 ∧ A < (p S).2 ∧ (p S).2 ≤ M ∧
      (p S).1.Coprime (p S).2 ∧ IntrinsicPair c S.val {(c:ℤ)+((p S).1:ℤ)*d,(c:ℤ)+((p S).2:ℤ)*d})
    (hEModel : ∀T,T.val=CenteredGrid c d (model T).1 (model T).2 ∧
      1≤(model T).1 ∧ (model T).1≤C ∧ A<(model T).2 ∧ (model T).2≤M) :
    ∃e:ℕ,A≤e ∧ e≤M ∧ (∀T,(model T).2≤e) ∧
      (e=A ∨ ∃T,(model T).2=e) ∧
      Cm.card+Cp.card+E.card≤C*(e-A)+(CoprimeBox 0 C e M).card+
        (CoprimeBox 0 e e M).card+(UpperTriangle e M).card := by
  classical
  have hmodel : ∀T,T.val=CenteredGrid c d (model T).1 (model T).2 ∧
      1≤(model T).1 ∧ (model T).1≤C ∧ A<(model T).2 ∧ (model T).2≤M ∧ IsAP T.val := by
    intro T
    obtain ⟨he,ha,hC,hA,hM⟩ := hEModel T
    refine ⟨he,ha,hC,hA,hM,?_⟩
    rw [he]
    exact centered_grid_isAP hd
  have hcrookedM : ∀S∈Cm,¬IsAP S := fun S hS=>
    actual_intrinsic_not_AP (hcM S hS) (hm ⟨S,hS⟩).2.2.2.2.2
  have hcrookedP : ∀S∈Cp,¬IsAP S := fun S hS=>
    actual_intrinsic_not_AP (hcP S hS) (hp ⟨S,hS⟩).2.2.2.2.2
  let X := {S // S ∈ Cm}
  let Y := {S // S ∈ Cp}
  let Z := {S // S ∈ E}
  let fE (T : Z) := (model T)
  let Wm := (Finset.univ : Finset X).image m
  let Wp := (Finset.univ : Finset Y).image p
  let EE := (Finset.univ : Finset Z).image fE
  have hm_inj : Function.Injective m := by
    intro S T heq
    apply Subtype.ext
    have hwS := (hm S).2.2.2.2.2
    have hwT := (hm T).2.2.2.2.2
    apply actual_intrinsic_member_eq hF (hMF S.property) (hMF T.property)
      (hcM S.val S.property) (hcM T.val T.property) hwS
    rw [heq]
    exact hwT.2.2.1
  have hp_inj : Function.Injective p := by
    intro S T heq
    apply Subtype.ext
    have hwS := (hp S).2.2.2.2.2
    have hwT := (hp T).2.2.2.2.2
    apply actual_intrinsic_member_eq hF (hPF S.property) (hPF T.property)
      (hcP S.val S.property) (hcP T.val T.property) hwS
    rw [heq]
    exact hwT.2.2.1
  have he_inj : Function.Injective fE := by
    intro S T heq
    apply Subtype.ext
    change model S=model T at heq
    have hS := (hmodel S).1
    rw [heq] at hS
    exact hS.trans (hmodel T).1.symm
  have hwm_card : Wm.card = Cm.card := by
    simp only [Wm,Finset.card_image_of_injective _ hm_inj,Finset.card_univ,X,Fintype.card_coe]
  have hwp_card : Wp.card = Cp.card := by
    simp only [Wp,Finset.card_image_of_injective _ hp_inj,Finset.card_univ,Y,Fintype.card_coe]
  have he_card : EE.card = E.card := by
    simp only [EE,Finset.card_image_of_injective _ he_inj,Finset.card_univ,Z,Fintype.card_coe]
  have he_exists : ∃ e : ℕ, A ≤ e ∧ e ≤ M ∧ (∀ T : Z, (model T).2 ≤ e) ∧
      (e = A ∨ ∃ T : Z, (model T).2 = e) := by
    by_cases hne : E.Nonempty
    · have hz : (Finset.univ : Finset Z).Nonempty := by
        obtain ⟨T,hT⟩ := hne
        exact ⟨⟨T,hT⟩,Finset.mem_univ _⟩
      obtain ⟨T,_hT,hmax⟩ := Finset.exists_max_image Finset.univ
        (fun T : Z => (model T).2) hz
      refine ⟨(model T).2,(hmodel T).2.2.2.1.le,(hmodel T).2.2.2.2.1,
        fun S => hmax S (Finset.mem_univ _),Or.inr ⟨T,rfl⟩⟩
    · refine ⟨A,le_rfl,hAM,?_,Or.inl rfl⟩
      intro T
      exact False.elim (hne ⟨T.val,T.property⟩)
  obtain ⟨e,hAe,heM,hmax,hewitness⟩ := he_exists
  have hErect : EE ⊆ (Finset.Icc 1 C).product (Finset.Ioc A e) := by
    intro q hq
    obtain ⟨T,_hT,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr
      ⟨(hmodel T).2.1,(hmodel T).2.2.1⟩,
      Finset.mem_Ioc.mpr ⟨(hmodel T).2.2.2.1,hmax T⟩⟩
  have hWmBox : Wm ⊆ CoprimeBox 0 C A M := by
    intro q hq
    obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ioc.mpr ⟨(hm S).1,(hm S).2.1⟩,
        Finset.mem_Ioc.mpr ⟨(hm S).2.2.1,(hm S).2.2.2.1⟩⟩,(hm S).2.2.2.2.1⟩
  have hdis : Disjoint EE Wm := by
    apply Finset.disjoint_left.mpr
    intro q hqE hqW
    obtain ⟨T,_hT,rfl⟩ := Finset.mem_image.mp hqE
    obtain ⟨S,_hS,hcoords⟩ := Finset.mem_image.mp hqW
    have hmT := (hmodel T).1
    have hrootT : (c:ℤ)∈T.val := by
      rw [hmT]
      exact centered_grid_root_mem c d (model T).1 (model T).2
    apply witness_pair_not_subset_AP_member hF (hMF S.property) (hEF T.property)
      (hcM S.val S.property) hrootT
      (hcrookedM S.val S.property) (hmodel T).2.2.2.2.2 (hm S).2.2.2.2.2
    change m S = (model T) at hcoords
    rw [hcoords]
    exact Finset.insert_subset_iff.mpr ⟨(by rw [hmT];exact centered_grid_negative_mem le_rfl),
      Finset.singleton_subset_iff.mpr ((by rw [hmT];exact centered_grid_positive_mem le_rfl))⟩
  have hWpAbove : ∀ q ∈ Wp,
      1 ≤ q.1 ∧ q.1 < q.2 ∧ e < q.2 ∧ q.2 ≤ M ∧ q.1.Coprime q.2 := by
    intro q hq
    obtain ⟨S,_hS,rfl⟩ := Finset.mem_image.mp hq
    refine ⟨(hp S).1,(hp S).2.1,?_,(hp S).2.2.2.1,(hp S).2.2.2.2.1⟩
    by_contra hn
    have hbe : (p S).2 ≤ e := by omega
    rcases hewitness with he | ⟨T,hTe⟩
    · have hh := (hp S).2.2.1
      omega
    · have hmT := (hmodel T).1
      have hrootT : (c:ℤ)∈T.val := by
        rw [hmT]
        exact centered_grid_root_mem c d (model T).1 (model T).2
      have ha : (p S).1 ≤ (model T).2 := by
        have hab := (hp S).2.1
        omega
      have hb : (p S).2 ≤ (model T).2 := by omega
      apply witness_pair_not_subset_AP_member hF (hPF S.property) (hEF T.property)
        (hcP S.val S.property) hrootT
        (hcrookedP S.val S.property) (hmodel T).2.2.2.2.2 (hp S).2.2.2.2.2
      exact Finset.insert_subset_iff.mpr ⟨(by rw [hmT];exact centered_grid_positive_mem ha),
        Finset.singleton_subset_iff.mpr ((by rw [hmT];exact centered_grid_positive_mem hb))⟩
  have hh := coordinate_pools_exact hErect hWmBox hdis hWpAbove
  rw [hwm_card,hwp_card,he_card] at hh
  exact ⟨e,hAe,heM,hmax,hewitness,by omega⟩

def ResourceCount (C A M e : ℕ) : ℕ :=
  C*(e-A)+(CoprimeBox 0 C e M).card+(CoprimeBox 0 e e M).card+(UpperTriangle e M).card

def StepFiber (G : Finset (Finset ℤ)) (ds : Finset ℤ→ℕ) (d : ℕ) : Finset (Finset ℤ) :=
  G.filter (fun S=>ds S=d)

theorem actual_middle_step_joint_functions {N c d C A M : ℕ} {F Cm Cp E : Finset (Finset ℤ)}
    (hd : 0<d) (hAM : A≤M) (hF : Legal (Ground N) F)
    (hMF : Cm⊆F) (hPF : Cp⊆F) (hEF : E⊆F)
    (hcM : ∀S∈Cm,(c:ℤ)∈S) (hcP : ∀S∈Cp,(c:ℤ)∈S)
    (m p model : Finset ℤ→ℕ×ℕ)
    (hm : ∀S∈Cm,1≤(m S).1 ∧ (m S).1≤C ∧ A<(m S).2 ∧ (m S).2≤M ∧
      (m S).1.Coprime (m S).2 ∧ IntrinsicPair c S
        {(c:ℤ)-((m S).1:ℤ)*d,(c:ℤ)+((m S).2:ℤ)*d})
    (hp : ∀S∈Cp,1≤(p S).1 ∧ (p S).1<(p S).2 ∧ A<(p S).2 ∧ (p S).2≤M ∧
      (p S).1.Coprime (p S).2 ∧ IntrinsicPair c S
        {(c:ℤ)+((p S).1:ℤ)*d,(c:ℤ)+((p S).2:ℤ)*d})
    (hmodel : ∀S∈E,S=CenteredGrid c d (model S).1 (model S).2 ∧
      1≤(model S).1 ∧ (model S).1≤C ∧ A<(model S).2 ∧ (model S).2≤M) :
    ∃e:ℕ,A≤e ∧ e≤M ∧ (∀T∈E,(model T).2≤e) ∧
      (e=A ∨ ∃T∈E,(model T).2=e) ∧ Cm.card+Cp.card+E.card≤ResourceCount C A M e := by
  obtain ⟨e,hAe,heM,hmax,hatt,hcount⟩ := actual_middle_step_joint hd hAM hF hMF hPF hEF hcM hcP
    (fun S=>m S.val) (fun S=>p S.val) (fun S=>model S.val)
    (fun S=>hm S.val S.property) (fun S=>hp S.val S.property) (fun S=>hmodel S.val S.property)
  refine ⟨e,hAe,heM,fun T hT=>hmax ⟨T,hT⟩,?_,hcount⟩
  rcases hatt with hh|⟨T,hT⟩
  · exact Or.inl hh
  · exact Or.inr ⟨T.val,T.property,hT⟩

theorem actual_middle_fiber_sum {N c : ℕ} {F Cm Cp E : Finset (Finset ℤ)}
    (C A M : ℕ→ℕ) (hAM : ∀d∈Finset.Icc 1 N,A d≤M d)
    (hF : Legal (Ground N) F) (hMF : Cm⊆F) (hPF : Cp⊆F) (hEF : E⊆F)
    (hcM : ∀S∈Cm,(c:ℤ)∈S) (hcP : ∀S∈Cp,(c:ℤ)∈S)
    (dm dp dE : Finset ℤ→ℕ) (m p model : Finset ℤ→ℕ×ℕ)
    (hdm : ∀S∈Cm,dm S∈Finset.Icc 1 N) (hdp : ∀S∈Cp,dp S∈Finset.Icc 1 N)
    (hdE : ∀S∈E,dE S∈Finset.Icc 1 N)
    (hm : ∀S∈Cm,1≤(m S).1 ∧ (m S).1≤C (dm S) ∧ A (dm S)<(m S).2 ∧
      (m S).2≤M (dm S) ∧ (m S).1.Coprime (m S).2 ∧ IntrinsicPair c S
        {(c:ℤ)-((m S).1:ℤ)*dm S,(c:ℤ)+((m S).2:ℤ)*dm S})
    (hp : ∀S∈Cp,1≤(p S).1 ∧ (p S).1<(p S).2 ∧ A (dp S)<(p S).2 ∧
      (p S).2≤M (dp S) ∧ (p S).1.Coprime (p S).2 ∧ IntrinsicPair c S
        {(c:ℤ)+((p S).1:ℤ)*dp S,(c:ℤ)+((p S).2:ℤ)*dp S})
    (hmodel : ∀S∈E,S=CenteredGrid c (dE S) (model S).1 (model S).2 ∧
      1≤(model S).1 ∧ (model S).1≤C (dE S) ∧ A (dE S)<(model S).2 ∧ (model S).2≤M (dE S)) :
    ∃e:ℕ→ℕ,(∀d∈Finset.Icc 1 N,A d≤e d ∧ e d≤M d ∧
      (∀T∈StepFiber E dE d,(model T).2≤e d) ∧
      (e d=A d ∨ ∃T∈StepFiber E dE d,(model T).2=e d)) ∧
      Cm.card+Cp.card+E.card≤∑d∈Finset.Icc 1 N,ResourceCount (C d) (A d) (M d) (e d) := by
  let Row (d e:ℕ) : Prop := A d≤e ∧ e≤M d ∧
    (∀T∈StepFiber E dE d,(model T).2≤e) ∧
    (e=A d ∨ ∃T∈StepFiber E dE d,(model T).2=e) ∧
    (StepFiber Cm dm d).card+(StepFiber Cp dp d).card+(StepFiber E dE d).card≤
      ResourceCount (C d) (A d) (M d) e
  have hrow : ∀d∈Finset.Icc 1 N,∃e,Row d e := by
    intro d hd
    apply actual_middle_step_joint_functions (d:=d) (C:=C d) (A:=A d) (M:=M d) (by have hh:=(Finset.mem_Icc.mp hd).1;omega) (hAM d hd) hF
      ((Finset.filter_subset _ _).trans hMF) ((Finset.filter_subset _ _).trans hPF)
      ((Finset.filter_subset _ _).trans hEF)
      (fun S hS=>hcM S (Finset.mem_filter.mp hS).1)
      (fun S hS=>hcP S (Finset.mem_filter.mp hS).1) m p model
    · intro S hS
      obtain ⟨hSC,hSd⟩ := Finset.mem_filter.mp hS
      simpa only [hSd] using hm S hSC
    · intro S hS
      obtain ⟨hSC,hSd⟩ := Finset.mem_filter.mp hS
      simpa only [hSd] using hp S hSC
    · intro S hS
      obtain ⟨hSC,hSd⟩ := Finset.mem_filter.mp hS
      simpa only [hSd] using hmodel S hSC
  have hex : ∀d:ℕ,∃e,d∈Finset.Icc 1 N→Row d e := by
    intro d
    by_cases hd:d∈Finset.Icc 1 N
    · obtain ⟨e,he⟩ := hrow d hd
      exact ⟨e,fun _=>he⟩
    · exact ⟨A d,fun hh=>False.elim (hd hh)⟩
  choose e he using hex
  refine ⟨e,fun d hd=>⟨(he d hd).1,(he d hd).2.1,(he d hd).2.2.1,(he d hd).2.2.2.1⟩,?_⟩
  have hM : Cm.card=∑d∈Finset.Icc 1 N,(StepFiber Cm dm d).card :=
    Finset.card_eq_sum_card_fiberwise hdm
  have hP : Cp.card=∑d∈Finset.Icc 1 N,(StepFiber Cp dp d).card :=
    Finset.card_eq_sum_card_fiberwise hdp
  have hE : E.card=∑d∈Finset.Icc 1 N,(StepFiber E dE d).card :=
    Finset.card_eq_sum_card_fiberwise hdE
  have hs := Finset.sum_le_sum (fun d hd=>(he d hd).2.2.2.2)
  simp only [Finset.sum_add_distrib] at hs
  rw [←hM,←hP,←hE] at hs
  exact hs

theorem actual_prepared_middle_resource_sum {N c L R : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p : Finset ℤ→ℤ)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedCrooked F c L,IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ∃e:ℕ→ℕ,(∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) ∧
      (CM (PreparedCrooked F c L) p R).card+(EM (PreparedAP F c L) c R).card≤
        ∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d) := by
  let Cm := NegativeCM (PreparedCrooked F c L) x p c R
  let Cp := PositiveCM (PreparedCrooked F c L) x p c R
  let E := EM (PreparedAP F c L) c R
  have hCsub : PreparedCrooked F c L⊆F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).1
  have hmC : Cm⊆PreparedCrooked F c L := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hpC : Cp⊆PreparedCrooked F c L := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hcrooked : ∀S∈PreparedCrooked F c L,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
  have hneg : ∀S:Finset ℤ,∃d:ℕ,∃w:ℕ×ℕ,S∈Cm→
      d∈Finset.Icc 1 N ∧ 1≤w.1 ∧ w.1≤c/d ∧ (L-c)/d<w.2 ∧ w.2≤(R-c)/d ∧
        w.1.Coprime w.2 ∧ IntrinsicPair c S {(c:ℤ)-(w.1:ℤ)*d,(c:ℤ)+(w.2:ℤ)*d} := by
    intro S
    by_cases hS:S∈Cm
    · obtain ⟨d,a,b,hd,hdN,ha,haC,hAb,hbM,hcop,_hx,_hp,hw⟩ :=
        actual_negative_CM_coordinates x p hF hcL hRN
          (fun T hT=>⟨(hW T hT).1,(hW T hT).2.2⟩) hS
      exact ⟨d,(a,b),fun _=>⟨Finset.mem_Icc.mpr ⟨hd,hdN⟩,ha,haC,hAb,hbM,hcop,hw⟩⟩
    · exact ⟨0,(0,0),fun hh=>False.elim (hS hh)⟩
  have hpos : ∀S:Finset ℤ,∃d:ℕ,∃w:ℕ×ℕ,S∈Cp→
      d∈Finset.Icc 1 N ∧ 1≤w.1 ∧ w.1<w.2 ∧ (L-c)/d<w.2 ∧ w.2≤(R-c)/d ∧
        w.1.Coprime w.2 ∧ IntrinsicPair c S {(c:ℤ)+(w.1:ℤ)*d,(c:ℤ)+(w.2:ℤ)*d} := by
    intro S
    by_cases hS:S∈Cp
    · obtain ⟨d,a,b,hd,hdN,ha,hab,hAb,hbM,hcop,_hx,_hp,hw⟩ :=
        actual_positive_CM_coordinates x p hcL hRN hW hS
      exact ⟨d,(a,b),fun _=>⟨Finset.mem_Icc.mpr ⟨hd,hdN⟩,ha,hab,hAb,hbM,hcop,hw⟩⟩
    · exact ⟨0,(0,0),fun hh=>False.elim (hS hh)⟩
  have hmodels : ∀S:Finset ℤ,∃w:ℕ×ℕ,S∈E→
      Step S∈Finset.Icc 1 N ∧ S=CenteredGrid c (Step S) w.1 w.2 ∧
        1≤w.1 ∧ w.1≤c/Step S ∧ (L-c)/Step S<w.2 ∧ w.2≤(R-c)/Step S := by
    intro S
    by_cases hS:S∈E
    · obtain ⟨a,b,hd,hdN,heq,ha,haC,hAb,hbM⟩ := actual_EM_centered_model hF hcL hP hLP hS
      exact ⟨(a,b),fun _=>⟨Finset.mem_Icc.mpr ⟨hd,hdN⟩,heq,ha,haC,hAb,hbM⟩⟩
    · exact ⟨(0,0),fun hh=>False.elim (hS hh)⟩
  choose dm m hm using hneg
  choose dp pos hp using hpos
  choose model hmodel using hmodels
  have hEF : E⊆F := by
    intro S hS
    exact (actual_prepared_AP_member (Finset.mem_filter.mp hS).1).1
  obtain ⟨e,he,hcount⟩ := actual_middle_fiber_sum
    (fun d=>c/d) (fun d=>(L-c)/d) (fun d=>(R-c)/d)
    (fun d _=>Nat.div_le_div_right (Nat.sub_le_sub_right hLR c))
    hF (hmC.trans hCsub) (hpC.trans hCsub) hEF
    (fun S hS=>hroot S (hCsub (hmC hS)) (hcrooked S (hmC hS)))
    (fun S hS=>hroot S (hCsub (hpC hS)) (hcrooked S (hpC hS)))
    dm dp Step m pos model (fun S hS=>(hm S hS).1) (fun S hS=>(hp S hS).1)
    (fun S hS=>(hmodel S hS).1) (fun S hS=>(hm S hS).2)
    (fun S hS=>(hp S hS).2) (fun S hS=>(hmodel S hS).2)
  refine ⟨e,fun d hd=>⟨(he d hd).1,(he d hd).2.1⟩,?_⟩
  have hpart := (actual_CM_sign_partition (c:=c) (R:=R) x p (fun S hS=>(hW S hS).1)).2.2
  change (CM (PreparedCrooked F c L) p R).card+E.card≤_
  rw [hpart]
  exact hcount

theorem actual_original_middle_resource_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃c∈Finset.Icc 1 N,∃L R:ℕ,c<L ∧ L≤R ∧ R≤N ∧ ∃e:ℕ→ℕ,
        (∀d∈Finset.Icc 1 N,(L-c)/d≤e d ∧ e d≤(R-c)/d) ∧
        (F.card:ℝ)≤(∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ)+
          ((R:ℝ)+(2/3)*L)*(N-R)+(Deleted N 28 F).card+
          (WitnessException (Ground N) c:ℝ)+4*(N:ℝ)*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,_hT,_henv,x,p,hx,hcount⟩ :=
    actual_original_middle_reduction28 hN hF hcounter
  obtain ⟨P,hP,hLP⟩ := hP
  have hPF := (Finset.mem_filter.mp hP).1
  obtain ⟨e,he,hbound⟩ := actual_prepared_middle_resource_sum x p
    (actual_retained_legal (r:=28) hLH) (by omega) hLR hRN hroot hPF hLP
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.1,(hx S hS).2.2.2.1⟩)
  have hboundR : ((CM (PreparedCrooked (Retained N 28 H) c L) p R).card:ℝ)+
      (EM (PreparedAP (Retained N 28 H) c L) c R).card≤
      (∑d∈Finset.Icc 1 N,ResourceCount (c/d) ((L-c)/d) ((R-c)/d) (e d):ℕ) := by
    exact_mod_cast hbound
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,e,he,?_⟩
  linarith only [hcount,hboundR]

#print axioms coprime_box_card_le
#print axioms twice_upper_triangle_card_le
#print axioms coordinate_pools_exact
#print axioms actual_intrinsic_not_AP
#print axioms actual_middle_step_joint
#print axioms actual_middle_step_joint_functions
#print axioms actual_original_middle_resource_reduction28
#print axioms actual_prepared_middle_resource_sum
#print axioms actual_middle_fiber_sum
end
end JSP233.MiddleJoint51
