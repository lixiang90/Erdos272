import Erdos272.Core.AnchorCompletion38
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Cast

/-! Actual first-hit partitions and sparse small-member counting.
All class capacities are supplied by the proved two-point theorem. -/
namespace JSP233.SparseSmall39
open StarCompletion AnchorCompletion38
open scoped Classical BigOperators
noncomputable section

def Earlier (T : Finset ℤ) (x : ℤ) : Finset ℤ := T.filter (fun y => y<x)

def Hit (T S : Finset ℤ) : ℤ :=
  if h : (S∩T).Nonempty then (S∩T).min' h else 0

def HitClass (F : Finset (Finset ℤ)) (c : ℤ) (T : Finset ℤ) (x : ℤ) : Finset (Finset ℤ) :=
  (RootPart F c).filter (fun S => Hit T S=x)

def DegreeBudget (N s : ℕ) : ℕ := ∑ i∈Finset.range s, (N-i-2)

theorem hit_spec {S T : Finset ℤ} (hne : (S∩T).Nonempty) :
    Hit T S∈S∩T ∧ ∀ y∈S∩T, Hit T S≤y := by
  simp only [Hit,dif_pos hne]
  exact ⟨Finset.min'_mem _ hne,fun y hy => Finset.min'_le _ y hy⟩

theorem rooted_member_hits_omitter {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T S : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hT : T∈F) (hTc : c∉T) (hS : S∈RootPart F c) :
    (S∩T).Nonempty := by
  obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hS
  have hne : S≠T := by intro he; exact hTc (he ▸ hcS)
  exact isAP_nonempty (hlegal.2 S hSF T hT hne)

theorem hitClass_avoids_earlier {N : ℕ} {F : Finset (Finset ℤ)} {c x : ℤ} {T S : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hT : T∈F) (hTc : c∉T) (hS : S∈HitClass F c T x) :
    Disjoint S (Earlier T x) := by
  obtain ⟨hSR,hHit⟩ := Finset.mem_filter.mp hS
  have hs := hit_spec (rooted_member_hits_omitter hlegal hT hTc hSR)
  apply Finset.disjoint_left.mpr
  intro y hyS hyE
  obtain ⟨hyT,hyx⟩ := Finset.mem_filter.mp hyE
  have hh := hs.2 y (Finset.mem_inter.mpr ⟨hyS,hyT⟩)
  rw [hHit] at hh
  omega

theorem actual_hitClass_capacity {N : ℕ} {F : Finset (Finset ℤ)} {c x : ℤ} {T : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hT : T∈F) (hTc : c∉T) (hx : x∈T) :
    (HitClass F c T x).card≤N-(Earlier T x).card-2 := by
  classical
  let C := HitClass F c T x
  by_cases hC : C.Nonempty
  · have hCF : C⊆F := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
    have hLC : Legal (Ground N\Earlier T x) C := ⟨by
      intro S hS y hy
      exact Finset.mem_sdiff.mpr ⟨hlegal.1 S (hCF hS) hy,
        fun he => Finset.disjoint_left.mp (hitClass_avoids_earlier hlegal hT hTc hS) hy he⟩,
      fun S hS U hU hne => hlegal.2 S (hCF hS) U (hCF hU) hne⟩
    have hcS : ∀ S∈C, c∈S := fun S hS =>
      (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2
    have hxS : ∀ S∈C, x∈S := by
      intro S hS
      obtain ⟨hSR,hHit⟩ := Finset.mem_filter.mp hS
      have hh := (Finset.mem_inter.mp (hit_spec (rooted_member_hits_omitter hlegal hT hTc hSR)).1).1
      rwa [hHit] at hh
    have hcap := actual_two_point_crooked_ground_capacity (Ground N\Earlier T x) C c x
      (by intro he; exact hTc (he ▸ hx)) hC hLC (fun S hS => hbad S (hCF hS)) hcS hxS
    have hsub : Earlier T x⊆Ground N := (Finset.filter_subset _ _).trans (hlegal.1 T hT)
    have he := Finset.card_sdiff_add_card_eq_card hsub
    rw [ground_card] at he
    change C.card≤N-(Earlier T x).card-2
    omega
  · have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    change C.card≤_
    simp only [he,Finset.card_empty,Nat.zero_le]

theorem earlier_card_orderIso (T : Finset ℤ) (i : Fin T.card) :
    (Earlier T (T.orderIsoOfFin rfl i).val).card=i.val := by
  classical
  let e := T.orderIsoOfFin rfl
  have heq : Earlier T (e i).val=(Finset.Iio i).image (fun j => (e j).val) := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxT,hxi⟩ := Finset.mem_filter.mp hx
      let j := e.symm ⟨x,hxT⟩
      have hj : j < i := by
        apply e.lt_iff_lt.mp
        change (e j).val<(e i).val
        simpa only [j,OrderIso.apply_symm_apply] using hxi
      exact Finset.mem_image.mpr ⟨j,Finset.mem_Iio.mpr hj,by simp only [j,OrderIso.apply_symm_apply]⟩
    · intro hx
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨(e j).property,e.strictMono (Finset.mem_Iio.mp hj)⟩
  have hinj : Function.Injective (fun j : Fin T.card => (e j).val) := by
    intro j k h
    exact e.injective (Subtype.ext h)
  rw [heq,Finset.card_image_of_injective _ hinj,Fin.card_Iio]

theorem sum_earlier_function (T : Finset ℤ) (f : ℕ→ℕ) :
    (∑ x∈T,f (Earlier T x).card)=∑ i∈Finset.range T.card, f i := by
  classical
  let e := T.orderIsoOfFin rfl
  calc
    _=∑ x : ↥T, f (Earlier T x.val).card := (Finset.sum_coe_sort T _).symm
    _=∑ i : Fin T.card, f i.val := by
      rw [←e.toEquiv.sum_comp (fun x : ↥T => f (Earlier T x.val).card)]
      apply Finset.sum_congr rfl
      intro i _
      simpa only [OrderIso.coe_toEquiv,e] using congrArg f (earlier_card_orderIso T i)
    _=_ := Fin.sum_univ_eq_sum_range _ _

theorem degreeBudget_mono (N : ℕ) {m s : ℕ} (hms : m≤s) : DegreeBudget N m≤DegreeBudget N s := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hms)
  intro i _ _
  exact Nat.zero_le _

theorem actual_degree_from_omitter {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S) (hT : T∈F) (hTc : c∉T) :
    (RootPart F c).card≤DegreeBudget N T.card := by
  have hmaps : ∀ S∈RootPart F c, Hit T S∈T := by
    intro S hS
    exact (Finset.mem_inter.mp (hit_spec (rooted_member_hits_omitter hlegal hT hTc hS)).1).2
  have he := Finset.card_eq_sum_card_fiberwise hmaps
  change (RootPart F c).card=∑ x∈T,(HitClass F c T x).card at he
  rw [he]
  calc
    _≤∑ x∈T,(N-(Earlier T x).card-2) :=
      Finset.sum_le_sum (fun x hx => actual_hitClass_capacity hlegal hbad hT hTc hx)
    _=_ := sum_earlier_function T (fun i => N-i-2)

theorem degreeBudget_closed (N s : ℕ) (hN : 2≤N) (hs : s+1≤N) :
    DegreeBudget N s+s.choose 2=s*(N-2) := by
  have hpoint : ∀ i∈Finset.range s,(N-i-2)+i=N-2 := by
    intro i hi
    have hh := Finset.mem_range.mp hi
    omega
  have hh := Finset.sum_congr (s₁:=Finset.range s) rfl hpoint
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_range,
    Finset.sum_range_id,←Nat.choose_two_right] at hh
  exact hh

theorem actual_degree_sparse {N s : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 2≤N) (hs : s+1≤N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (homitter : ∃ T∈F,c∉T) :
    (RootPart F c).card≤s*(N-2)-s.choose 2 := by
  obtain ⟨T,hT,hTc⟩ := homitter
  have hh := (actual_degree_from_omitter hlegal hbad hT hTc).trans
    (degreeBudget_mono N (hsize T hT))
  have he := degreeBudget_closed N s hN hs
  omega

def SmallMembers (F : Finset (Finset ℤ)) (K : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S => S.card≤16*K)

theorem actual_pair_class_bound {N : ℕ} {F : Finset (Finset ℤ)} {Q : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S) (hQ : Q.card=2) :
    (F.filter (fun S => Q⊆S)).card≤N := by
  classical
  let C := F.filter (fun S => Q⊆S)
  by_cases hC : C.Nonempty
  · obtain ⟨u,v,huv,hrep⟩ := Finset.card_eq_two.mp hQ
    have hCF : C⊆F := Finset.filter_subset _ _
    have hLC : Legal (Ground N) C := ⟨fun S hS => hlegal.1 S (hCF hS),
      fun S hS T hT hne => hlegal.2 S (hCF hS) T (hCF hT) hne⟩
    have hu : ∀ S∈C,u∈S := by
      intro S hS
      apply (Finset.mem_filter.mp hS).2
      rw [hrep]
      simp
    have hv : ∀ S∈C,v∈S := by
      intro S hS
      apply (Finset.mem_filter.mp hS).2
      rw [hrep]
      simp
    have hh := actual_two_point_crooked_ground_capacity (Ground N) C u v huv hC hLC
      (fun S hS => hbad S (hCF hS)) hu hv
    rw [ground_card] at hh
    change C.card≤N
    omega
  · have he : C=∅ := Finset.not_nonempty_iff_eq_empty.mp hC
    change C.card≤N
    simp only [he,Finset.card_empty,Nat.zero_le]

theorem actual_pair_pool_bound {N : ℕ} {F : Finset (Finset ℤ)} (H : Finset ℤ)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hmeet : ∀ S∈F,2≤(S∩H).card) : F.card≤H.card.choose 2*N := by
  classical
  let C := fun Q : Finset ℤ => F.filter (fun S => Q⊆S)
  have hcover : F⊆(H.powersetCard 2).biUnion C := by
    intro S hS
    obtain ⟨Q,hQsub,hQcard⟩ := Finset.exists_subset_card_eq (hmeet S hS)
    have hQS : Q⊆S := fun x hx => (Finset.mem_inter.mp (hQsub hx)).1
    have hQH : Q⊆H := fun x hx => (Finset.mem_inter.mp (hQsub hx)).2
    exact Finset.mem_biUnion.mpr ⟨Q,Finset.mem_powersetCard.mpr ⟨hQH,hQcard⟩,
      Finset.mem_filter.mpr ⟨hS,hQS⟩⟩
  calc
    F.card≤((H.powersetCard 2).biUnion C).card := Finset.card_le_card hcover
    _≤∑ Q∈H.powersetCard 2,(C Q).card := Finset.card_biUnion_le
    _≤∑ _Q∈H.powersetCard 2,N := Finset.sum_le_sum (fun Q hQ =>
      actual_pair_class_bound hlegal hbad (Finset.mem_powersetCard.mp hQ).2)
    _=H.card.choose 2*N := by simp

theorem choose_small_pool (h K : ℕ) (hh : h≤32*K) : h.choose 2≤512*K^2 := by
  have hd := Nat.div_mul_le_self (h*(h-1)) 2
  rw [←Nat.choose_two_right] at hd
  have hs := Nat.mul_self_le_mul_self hh
  have ht := Nat.mul_le_mul_left h (Nat.sub_le h 1)
  nlinarith only [hd,hs,ht]

theorem actual_small_pair_pool_bound {N K : ℕ} {F : Finset (Finset ℤ)} (H : Finset ℤ)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S)
    (hH : H.card≤32*K) (hmeet : ∀ S∈F,2≤(S∩H).card) :
    F.card≤512*K^2*N := by
  exact (actual_pair_pool_bound H hlegal hbad hmeet).trans
    (Nat.mul_le_mul_right N (choose_small_pool H.card K hH))

theorem actual_singleton_avoiders_two_hits {N : ℕ} {F : Finset (Finset ℤ)}
    {A B : Finset ℤ} {c : ℤ} (hlegal : Legal (Ground N) F)
    (hA : A∈F) (hB : B∈F) (hAB : A∩B={c}) :
    ∀ S∈Avoiders F c,2≤(S∩((A∪B).erase c)).card := by
  intro S hS
  obtain ⟨hSF,hSc⟩ := Finset.mem_filter.mp hS
  have hcAB : c∈A∩B := by rw [hAB]; simp
  obtain ⟨hcA,hcB⟩ := Finset.mem_inter.mp hcAB
  have hSA : S≠A := by intro he; exact hSc (he.symm ▸ hcA)
  have hSB : S≠B := by intro he; exact hSc (he.symm ▸ hcB)
  obtain ⟨a,ha⟩ := isAP_nonempty (hlegal.2 S hSF A hA hSA)
  obtain ⟨b,hb⟩ := isAP_nonempty (hlegal.2 S hSF B hB hSB)
  obtain ⟨haS,haA⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbS,hbB⟩ := Finset.mem_inter.mp hb
  have hab : a≠b := by
    intro he
    have haAB : a∈A∩B := Finset.mem_inter.mpr ⟨haA,he.symm ▸ hbB⟩
    rw [hAB] at haAB
    exact hSc ((Finset.mem_singleton.mp haAB) ▸ haS)
  have haH : a∈(A∪B).erase c := Finset.mem_erase.mpr
    ⟨by intro he; exact hSc (he ▸ haS),Finset.mem_union.mpr (Or.inl haA)⟩
  have hbH : b∈(A∪B).erase c := Finset.mem_erase.mpr
    ⟨by intro he; exact hSc (he ▸ hbS),Finset.mem_union.mpr (Or.inr hbB)⟩
  have hsub : ({a,b}:Finset ℤ)⊆S∩((A∪B).erase c) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Finset.mem_inter.mpr ⟨haS,haH⟩
    · have he : x=b := Finset.mem_singleton.mp hx
      exact he.symm ▸ Finset.mem_inter.mpr ⟨hbS,hbH⟩
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_pair hab] using hh

theorem actual_no_singleton_two_hits {N : ℕ} {F : Finset (Finset ℤ)} {A : Finset ℤ}
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F, ¬IsAP S) (hcount : 2≤F.card)
    (hA : A∈F) (hno : ¬∃ U∈F,∃ V∈F,∃ c : ℤ,U∩V={c}) :
    ∀ S∈F,2≤(S∩A).card := by
  have hAN : A.Nonempty := by
    obtain ⟨T,hT,hTA⟩ := Finset.exists_mem_ne (by omega : 1<F.card) A
    obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 A hA T hT (Ne.symm hTA))
    exact ⟨x,(Finset.mem_inter.mp hx).1⟩
  intro S hS
  by_cases he : S=A
  · subst S
    rw [Finset.inter_self]
    by_contra hn
    exact hbad A hA (nonempty_card_le_two_isAP hAN (by omega))
  · have hne := isAP_nonempty (hlegal.2 S hS A hA he)
    have hp := hne.card_pos
    by_contra hn
    have hcard : (S∩A).card=1 := by omega
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp hcard
    exact hno ⟨S,hS,A,hA,c,hc⟩

theorem actual_small_sparse_count {N K s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    (SmallMembers F K).card≤DegreeBudget N s+512*K^2*N := by
  classical
  let G := SmallMembers F K
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G := ⟨fun S hS => hlegal.1 S (hGF hS),
    fun S hS T hT hne => hlegal.2 S (hGF hS) T (hGF hT) hne⟩
  have hBG : ∀ S∈G,¬IsAP S := fun S hS => hbad S (hGF hS)
  by_cases hsmall : G.card≤1
  · have hp : 1≤512*K^2*N := by
      have hk2 : 1≤K^2 := by
        have hk1 : 1≤K := by omega
        nlinarith
      nlinarith
    change G.card≤_
    omega
  have hcount : 2≤G.card := by omega
  by_cases hsing : ∃ A∈G,∃ B∈G,∃ c : ℤ,A∩B={c}
  · obtain ⟨A,hA,B,hB,c,hAB⟩ := hsing
    have hcAB : c∈A∩B := by rw [hAB]; simp
    have hcA := (Finset.mem_inter.mp hcAB).1
    have hcN : c∈Ground N := hlegal.1 A (hGF hA) hcA
    obtain ⟨T,hT,hTc⟩ := hnocommon c hcN
    have hdegree := (actual_degree_from_omitter hlegal hbad hT hTc).trans
      (degreeBudget_mono N (hsize T hT))
    have hrootSub : RootPart G c⊆RootPart F c := by
      intro S hS
      exact Finset.mem_filter.mpr ⟨hGF (Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2⟩
    have hroot := (Finset.card_le_card hrootSub).trans hdegree
    have hHL : ((A∪B).erase c).card≤32*K := by
      have ha := (Finset.mem_filter.mp hA).2
      have hb := (Finset.mem_filter.mp hB).2
      have hu := Finset.card_union_le A B
      have he := Finset.card_le_card (Finset.erase_subset c (A∪B))
      omega
    have hLA : Legal (Ground N) (Avoiders G c) := ⟨
      fun S hS => hLG.1 S (Finset.mem_filter.mp hS).1,
      fun S hS U hU hne => hLG.2 S (Finset.mem_filter.mp hS).1 U (Finset.mem_filter.mp hU).1 hne⟩
    have havoid := actual_small_pair_pool_bound ((A∪B).erase c) hLA
      (fun S hS => hBG S (Finset.mem_filter.mp hS).1) hHL
      (actual_singleton_avoiders_two_hits hLG hA hB hAB)
    have hpart := root_avoider_card_partition G c
    change G.card≤_
    omega
  · obtain ⟨A,hA⟩ := Finset.card_pos.mp (by omega : 0<G.card)
    have hHA : A.card≤32*K := (Finset.mem_filter.mp hA).2.trans (by omega)
    have hh := actual_small_pair_pool_bound A hLG hBG hHA
      (actual_no_singleton_two_hits hLG hBG hcount hA hsing)
    change G.card≤_
    omega

theorem actual_small_sparse_integer {N K s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2≤N) (hs : s+1≤N) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    (SmallMembers F K).card+s.choose 2≤s*(N-2)+512*K^2*N := by
  have hh := actual_small_sparse_count (by omega : 1≤N) hK hlegal hbad hsize hnocommon
  have he := degreeBudget_closed N s hN hs
  omega

theorem degreeBudget_real_upper (N s : ℕ) (x : ℝ) (hN : 2≤N) (hs : s+1≤N)
    (hsx : (s:ℝ)≤x) (hx : x≤(N:ℝ)-2) :
    (DegreeBudget N s:ℝ)≤x*((N:ℝ)-2)-x*(x-1)/2 := by
  have he := congrArg (fun m : ℕ => (m:ℝ)) (degreeBudget_closed N s hN hs)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub hN,Nat.cast_ofNat,Nat.cast_choose_two] at he
  have hm := mul_nonneg (sub_nonneg.mpr hsx)
    (show 0≤(N:ℝ)-3/2-(x+(s:ℝ))/2 by linarith)
  nlinarith only [he,hm]

theorem degreeBudget_ratio (N r : ℕ) (hN : 4≤N) (hr : 2≤r) :
    (DegreeBudget N (N/r):ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)) := by
  let x := (N:ℝ)/(r:ℝ)
  have hrpos : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have hrne : (r:ℝ)≠0 := ne_of_gt hrpos
  have hrR : (2:ℝ)≤r := by exact_mod_cast hr
  have hNR : (4:ℝ)≤N := by exact_mod_cast hN
  have hprod := Nat.div_mul_le_self N r
  have htwo : 2*(N/r)≤N := by
    have hm := Nat.mul_le_mul_left (N/r) hr
    nlinarith only [hm,hprod]
  have hs : N/r+1≤N := by omega
  have hsx : ((N/r:ℕ):ℝ)≤x := by
    apply (le_div_iff₀ hrpos).mpr
    exact_mod_cast hprod
  have hx : x≤(N:ℝ)-2 := by
    apply (div_le_iff₀ hrpos).mpr
    have hm := mul_le_mul_of_nonneg_left hrR (by linarith : (0:ℝ)≤(N:ℝ)-2)
    nlinarith only [hm,hNR]
  have hh := degreeBudget_real_upper N (N/r) x (by omega) hs hsx hx
  have he : x*((N:ℝ)-2)-x*(x-1)/2=
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)) := by
    dsimp [x]
    field_simp
    ring
  rwa [he] at hh

theorem actual_degree_sparse_rational {N r : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 4≤N) (hr : 2≤r) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (homitter : ∃ T∈F,c∉T) :
    ((RootPart F c).card:ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)) := by
  obtain ⟨T,hT,hTc⟩ := homitter
  have hTsize : T.card≤N/r := (Nat.le_div_iff_mul_le (by omega : 0<r)).mpr
    (by simpa only [Nat.mul_comm] using hsize T hT)
  have hh := (actual_degree_from_omitter hlegal hbad hT hTc).trans (degreeBudget_mono N hTsize)
  have hhR : ((RootPart F c).card:ℝ)≤(DegreeBudget N (N/r):ℝ) := by exact_mod_cast hh
  exact hhR.trans (degreeBudget_ratio N r hN hr)

theorem actual_small_sparse_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    ((SmallMembers F K).card:ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))+
        512*(K:ℝ)^2*(N:ℝ) := by
  have hsmall : ∀ S∈F,S.card≤N/r := by
    intro S hS
    apply (Nat.le_div_iff_mul_le (by omega : 0<r)).mpr
    simpa only [Nat.mul_comm] using hsize S hS
  have hh := actual_small_sparse_count (by omega : 1≤N) hK hlegal hbad hsmall hnocommon
  have hhR : ((SmallMembers F K).card:ℝ)≤(DegreeBudget N (N/r):ℝ)+512*(K:ℝ)^2*(N:ℝ) := by
    exact_mod_cast hh
  have hd := degreeBudget_ratio N r hN hr
  linarith

theorem actual_omitter_of_empty_kernel {N : ℕ} {F : Finset (Finset ℤ)}
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ∀ c∈Ground N,∃ T∈F,c∉T := by
  classical
  intro c hc
  by_contra hn
  have hh : c∈PrivateFinset.Kernel (Ground N) F := by
    apply Finset.mem_filter.mpr
    refine ⟨hc,?_⟩
    intro T hT
    by_contra hTc
    exact hn ⟨T,hT,hTc⟩
  rw [hkernel] at hh
  exact Finset.notMem_empty c hh

theorem actual_small_empty_kernel_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F, ¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ((SmallMembers F K).card:ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))+
        512*(K:ℝ)^2*(N:ℝ) := by
  exact actual_small_sparse_rational hN hr hK hlegal hbad hsize
    (actual_omitter_of_empty_kernel hkernel)

#print axioms hit_spec
#print axioms rooted_member_hits_omitter
#print axioms hitClass_avoids_earlier
#print axioms actual_hitClass_capacity
#print axioms earlier_card_orderIso
#print axioms sum_earlier_function
#print axioms degreeBudget_mono
#print axioms actual_degree_from_omitter
#print axioms degreeBudget_closed
#print axioms actual_degree_sparse
#print axioms actual_pair_class_bound
#print axioms actual_pair_pool_bound
#print axioms choose_small_pool
#print axioms actual_small_pair_pool_bound
#print axioms actual_singleton_avoiders_two_hits
#print axioms actual_no_singleton_two_hits
#print axioms actual_small_sparse_count
#print axioms actual_small_sparse_integer
#print axioms degreeBudget_real_upper
#print axioms degreeBudget_ratio
#print axioms actual_degree_sparse_rational
#print axioms actual_small_sparse_rational
#print axioms actual_omitter_of_empty_kernel
#print axioms actual_small_empty_kernel_rational

end
end JSP233.SparseSmall39
