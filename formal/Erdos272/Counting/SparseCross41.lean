import Erdos272.Global.SparseSmall39

/-! A singleton intersection needs cross pairs, not all pairs of the union. -/
namespace JSP233.SparseCross41
open StarCompletion SparseSmall39
open scoped Classical BigOperators
noncomputable section

theorem actual_cross_pool_bound {N : ℕ} {F : Finset (Finset ℤ)} (A B : Finset ℤ)
    (hlegal : Legal (Ground N) F) (hbad : ∀ S∈F,¬IsAP S)
    (hdisjoint : Disjoint A B)
    (hhit : ∀ S∈F,∃ a∈A,∃ b∈B,a∈S ∧ b∈S) :
    F.card≤A.card*B.card*N := by
  let C := fun p : ℤ×ℤ => F.filter (fun S=>p.1∈S ∧ p.2∈S)
  have hcover : F⊆(A.product B).biUnion C := by
    intro S hS
    obtain ⟨a,ha,b,hb,haS,hbS⟩ := hhit S hS
    exact Finset.mem_biUnion.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,
      Finset.mem_filter.mpr ⟨hS,haS,hbS⟩⟩
  have hclass : ∀ p∈A.product B,(C p).card≤N := by
    intro p hp
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    have hab : p.1≠p.2 := by
      intro he
      exact Finset.disjoint_left.mp hdisjoint ha (he.symm ▸ hb)
    have hsub : C p⊆F.filter (fun S=>({p.1,p.2}:Finset ℤ)⊆S) := by
      intro S hS
      obtain ⟨hSF,haS,hbS⟩ := Finset.mem_filter.mp hS
      apply Finset.mem_filter.mpr
      refine ⟨hSF,?_⟩
      simpa only [Finset.insert_subset_iff,Finset.singleton_subset_iff] using And.intro haS hbS
    exact (Finset.card_le_card hsub).trans
      (actual_pair_class_bound hlegal hbad (Finset.card_pair hab))
  calc
    F.card≤((A.product B).biUnion C).card := Finset.card_le_card hcover
    _≤∑ p∈A.product B,(C p).card := Finset.card_biUnion_le
    _≤∑ _p∈A.product B,N := Finset.sum_le_sum hclass
    _=A.card*B.card*N := by simp

theorem singleton_erases_disjoint {A B : Finset ℤ} {c : ℤ} (hAB : A∩B={c}) :
    Disjoint (A.erase c) (B.erase c) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨hxc,hxA⟩ := Finset.mem_erase.mp hxA
  obtain ⟨_,hxB⟩ := Finset.mem_erase.mp hxB
  have hx : x∈A∩B := Finset.mem_inter.mpr ⟨hxA,hxB⟩
  rw [hAB] at hx
  exact hxc (Finset.mem_singleton.mp hx)

theorem actual_singleton_cross_hits {N : ℕ} {F : Finset (Finset ℤ)}
    {A B : Finset ℤ} {c : ℤ} (hlegal : Legal (Ground N) F)
    (hA : A∈F) (hB : B∈F) (hAB : A∩B={c}) :
    ∀ S∈Avoiders F c,∃ a∈A.erase c,∃ b∈B.erase c,a∈S ∧ b∈S := by
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
  refine ⟨a,Finset.mem_erase.mpr ⟨?_,haA⟩,b,Finset.mem_erase.mpr ⟨?_,hbB⟩,haS,hbS⟩
  · intro he; exact hSc (he ▸ haS)
  · intro he; exact hSc (he ▸ hbS)

theorem choose_pool16 (h K : ℕ) (hh : h≤16*K) : h.choose 2≤128*K^2 := by
  have hd := Nat.div_mul_le_self (h*(h-1)) 2
  rw [←Nat.choose_two_right] at hd
  have hs := Nat.mul_self_le_mul_self hh
  have ht := Nat.mul_le_mul_left h (Nat.sub_le h 1)
  nlinarith only [hd,hs,ht]

theorem actual_small_sparse_count {N K s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    (SmallMembers F K).card≤DegreeBudget N s+256*K^2*N := by
  let G := SmallMembers F K
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G := ⟨fun S hS=>hlegal.1 S (hGF hS),
    fun S hS T hT hne=>hlegal.2 S (hGF hS) T (hGF hT) hne⟩
  have hBG : ∀ S∈G,¬IsAP S := fun S hS=>hbad S (hGF hS)
  by_cases hsmall : G.card≤1
  · have hp : 1≤256*K^2*N := by
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
    obtain ⟨T,hT,hTc⟩ := hnocommon c (hlegal.1 A (hGF hA) hcA)
    have hdegree := (actual_degree_from_omitter hlegal hbad hT hTc).trans
      (degreeBudget_mono N (hsize T hT))
    have hrootSub : RootPart G c⊆RootPart F c := by
      intro S hS
      exact Finset.mem_filter.mpr ⟨hGF (Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2⟩
    have hroot := (Finset.card_le_card hrootSub).trans hdegree
    have hLA : Legal (Ground N) (Avoiders G c) := ⟨
      fun S hS=>hLG.1 S (Finset.mem_filter.mp hS).1,
      fun S hS U hU hne=>hLG.2 S (Finset.mem_filter.mp hS).1 U (Finset.mem_filter.mp hU).1 hne⟩
    have havoid := actual_cross_pool_bound (A.erase c) (B.erase c) hLA
      (fun S hS=>hBG S (Finset.mem_filter.mp hS).1)
      (singleton_erases_disjoint hAB) (actual_singleton_cross_hits hLG hA hB hAB)
    have ha : (A.erase c).card≤16*K :=
      (Finset.card_le_card (Finset.erase_subset c A)).trans (Finset.mem_filter.mp hA).2
    have hb : (B.erase c).card≤16*K :=
      (Finset.card_le_card (Finset.erase_subset c B)).trans (Finset.mem_filter.mp hB).2
    have hprod := Nat.mul_le_mul_right N (Nat.mul_le_mul ha hb)
    have hbound : (Avoiders G c).card≤256*K^2*N := by nlinarith only [havoid,hprod]
    have hpart := root_avoider_card_partition G c
    change G.card≤_
    omega
  · obtain ⟨A,hA⟩ := Finset.card_pos.mp (by omega : 0<G.card)
    have hh := actual_pair_pool_bound A hLG hBG
      (actual_no_singleton_two_hits hLG hBG hcount hA hsing)
    have hpool := Nat.mul_le_mul_right N (choose_pool16 A.card K (Finset.mem_filter.mp hA).2)
    change G.card≤_
    nlinarith only [hh,hpool]

theorem actual_small_sparse_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    ((SmallMembers F K).card:ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))+
      256*(K:ℝ)^2*(N:ℝ) := by
  have hsmall : ∀ S∈F,S.card≤N/r := by
    intro S hS
    apply (Nat.le_div_iff_mul_le (by omega : 0<r)).mpr
    simpa only [Nat.mul_comm] using hsize S hS
  have hh := actual_small_sparse_count (by omega : 1≤N) hK hlegal hbad hsmall hnocommon
  have hhR : ((SmallMembers F K).card:ℝ)≤(DegreeBudget N (N/r):ℝ)+256*(K:ℝ)^2*(N:ℝ) := by
    exact_mod_cast hh
  have hd := degreeBudget_ratio N r hN hr
  linarith

theorem actual_small_empty_kernel_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ((SmallMembers F K).card:ℝ)≤
      ((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ))+
      256*(K:ℝ)^2*(N:ℝ) := by
  exact actual_small_sparse_rational hN hr hK hlegal hbad hsize
    (actual_omitter_of_empty_kernel hkernel)

#print axioms actual_cross_pool_bound
#print axioms singleton_erases_disjoint
#print axioms actual_singleton_cross_hits
#print axioms choose_pool16
#print axioms actual_small_sparse_count
#print axioms actual_small_sparse_rational
#print axioms actual_small_empty_kernel_rational
end
end JSP233.SparseCross41
