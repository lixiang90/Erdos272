import Erdos272.Counting.SparseCross41

/-! A small omitter pays the small root part. The global degree bound and
the cross-pair error are alternatives, rather than additive worst cases. -/
namespace JSP233.SmallJoint46
open StarCompletion SparseSmall39
open scoped Classical BigOperators
noncomputable section

theorem degreeBudget_le_linear (N s : ℕ) : DegreeBudget N s≤s*N := by
  unfold DegreeBudget
  calc
    _≤∑ _i∈Finset.range s,N := Finset.sum_le_sum (fun i _=>by omega)
    _=s*N := by simp

theorem erase_small_card {A : Finset ℤ} {c : ℤ} {K : ℕ}
    (hc : c∈A) (hA : A.card≤16*K) : (A.erase c).card≤16*K-1 := by
  rw [Finset.card_erase_of_mem hc]
  exact Nat.sub_le_sub_right hA 1

theorem actual_small_joint_count {N K s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    (SmallMembers F K).card≤max (DegreeBudget N s) (256*K^2*N) := by
  let G := SmallMembers F K
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G := ⟨fun S hS=>hlegal.1 S (hGF hS),
    fun S hS T hT hne=>hlegal.2 S (hGF hS) T (hGF hT) hne⟩
  have hBG : ∀ S∈G,¬IsAP S := fun S hS=>hbad S (hGF hS)
  by_cases hsmall : G.card≤1
  · have hk2 : 1≤K^2 := by
      have hk1 : 1≤K := by omega
      nlinarith
    have hp : 1≤256*K^2*N := by nlinarith
    exact (hsmall.trans hp).trans (le_max_right _ _)
  have hcount : 2≤G.card := by omega
  by_cases hsing : ∃ A∈G,∃ B∈G,∃ c : ℤ,A∩B={c}
  · obtain ⟨A,hA,B,hB,c,hAB⟩ := hsing
    have hcAB : c∈A∩B := by rw [hAB]; simp
    obtain ⟨hcA,hcB⟩ := Finset.mem_inter.mp hcAB
    have hpart := root_avoider_card_partition G c
    by_cases havoid : (Avoiders G c).Nonempty
    · obtain ⟨T,hT⟩ := havoid
      obtain ⟨hTG,hTc⟩ := Finset.mem_filter.mp hT
      have hdegree := (actual_degree_from_omitter hLG hBG hTG hTc).trans
        ((degreeBudget_mono N (Finset.mem_filter.mp hTG).2).trans
          (degreeBudget_le_linear N (16*K)))
      have hLA : Legal (Ground N) (Avoiders G c) := ⟨
        fun S hS=>hLG.1 S (Finset.mem_filter.mp hS).1,
        fun S hS U hU hne=>hLG.2 S (Finset.mem_filter.mp hS).1 U (Finset.mem_filter.mp hU).1 hne⟩
      have hcross := SparseCross41.actual_cross_pool_bound (A.erase c) (B.erase c) hLA
        (fun S hS=>hBG S (Finset.mem_filter.mp hS).1)
        (SparseCross41.singleton_erases_disjoint hAB)
        (SparseCross41.actual_singleton_cross_hits hLG hA hB hAB)
      have ha := erase_small_card hcA (Finset.mem_filter.mp hA).2
      have hb := erase_small_card hcB (Finset.mem_filter.mp hB).2
      have hproduct := Nat.mul_le_mul_right N (Nat.mul_le_mul ha hb)
      have hcross' : (Avoiders G c).card≤(16*K-1)^2*N := by
        nlinarith only [hcross,hproduct]
      have hsub : 16*K-1+1=16*K := Nat.sub_add_cancel (by omega)
      have hpoly : (16*K-1)^2+16*K≤256*K^2 := by nlinarith only [hsub]
      have hpay := Nat.mul_le_mul_right N hpoly
      have hh : G.card≤256*K^2*N := by nlinarith only [hdegree,hcross',hpart,hpay]
      exact hh.trans (le_max_right _ _)
    · have he : Avoiders G c=∅ := Finset.not_nonempty_iff_eq_empty.mp havoid
      obtain ⟨T,hT,hTc⟩ := hnocommon c (hlegal.1 A (hGF hA) hcA)
      have hdegree := (actual_degree_from_omitter hlegal hbad hT hTc).trans
        (degreeBudget_mono N (hsize T hT))
      have hrootSub : RootPart G c⊆RootPart F c := by
        intro S hS
        exact Finset.mem_filter.mpr ⟨hGF (Finset.mem_filter.mp hS).1,(Finset.mem_filter.mp hS).2⟩
      have hroot := (Finset.card_le_card hrootSub).trans hdegree
      rw [he,Finset.card_empty] at hpart
      have hh : G.card≤DegreeBudget N s := by omega
      exact hh.trans (le_max_left _ _)
  · obtain ⟨A,hA⟩ := Finset.card_pos.mp (by omega : 0<G.card)
    have hh := actual_pair_pool_bound A hLG hBG
      (actual_no_singleton_two_hits hLG hBG hcount hA hsing)
    have hpool := Nat.mul_le_mul_right N
      (SparseCross41.choose_pool16 A.card K (Finset.mem_filter.mp hA).2)
    have hlo : G.card≤256*K^2*N := by nlinarith only [hh,hpool]
    exact hlo.trans (le_max_right _ _)

theorem actual_small_joint_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    ((SmallMembers F K).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      (256*(K:ℝ)^2*(N:ℝ)) := by
  have hsmall : ∀ S∈F,S.card≤N/r := by
    intro S hS
    apply (Nat.le_div_iff_mul_le (by omega : 0<r)).mpr
    simpa only [Nat.mul_comm] using hsize S hS
  have hh := actual_small_joint_count (by omega : 1≤N) hK hlegal hbad hsmall hnocommon
  have hhR : ((SmallMembers F K).card:ℝ)≤max (DegreeBudget N (N/r):ℝ)
      (256*(K:ℝ)^2*(N:ℝ)) := by exact_mod_cast hh
  exact hhR.trans (max_le_max (degreeBudget_ratio N r hN hr) le_rfl)

theorem actual_small_joint_empty_kernel {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,r*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ((SmallMembers F K).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      (256*(K:ℝ)^2*(N:ℝ)) := by
  exact actual_small_joint_rational hN hr hK hlegal hbad hsize
    (actual_omitter_of_empty_kernel hkernel)

#print axioms degreeBudget_le_linear
#print axioms erase_small_card
#print axioms actual_small_joint_count
#print axioms actual_small_joint_rational
#print axioms actual_small_joint_empty_kernel
end
end JSP233.SmallJoint46
