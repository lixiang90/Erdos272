module

public import Erdos272.Core.SmallJoint46

@[expose] public section
namespace JSP233.SmallSpan48
open StarCompletion SparseSmall39 SmallJoint46
open scoped Classical BigOperators
noncomputable section

def SpanMembers (F : Finset (Finset ℤ)) (L : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>S.card≤L)

theorem erase_span_card {A : Finset ℤ} {c : ℤ} {L : ℕ}
    (hc : c∈A) (hA : A.card≤L) : (A.erase c).card≤L-1 := by
  rw [Finset.card_erase_of_mem hc]
  exact Nat.sub_le_sub_right hA 1

theorem choose_span_pool (h L : ℕ) (hh : h≤L) (hL : 0<L) :
    h.choose 2≤(L-1)^2+L := by
  have hd := Nat.div_mul_le_self (h*(h-1)) 2
  rw [←Nat.choose_two_right] at hd
  have hs := Nat.mul_self_le_mul_self hh
  have ht := Nat.mul_le_mul_left h (Nat.sub_le h 1)
  have hsub : L-1+1=L := Nat.sub_add_cancel (by omega)
  nlinarith only [hd,hs,ht,hsub]

theorem span_fee_le_square (L : ℕ) (hL : 0<L) : (L-1)^2+L≤L^2 := by
  have hsub : L-1+1=L := Nat.sub_add_cancel (by omega)
  nlinarith only [hsub]

theorem actual_span_joint_exact {N L s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hL : 0<L) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S∈F,¬IsAP S) (hsize : ∀ S∈F,S.card≤s)
    (hnocommon : ∀ c∈Ground N,∃ T∈F,c∉T) :
    (SpanMembers F L).card≤max (DegreeBudget N s) (((L-1)^2+L)*N) := by
  let G := SpanMembers F L
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G := ⟨fun S hS=>hlegal.1 S (hGF hS),
    fun S hS T hT hne=>hlegal.2 S (hGF hS) T (hGF hT) hne⟩
  have hBG : ∀ S∈G,¬IsAP S := fun S hS=>hbad S (hGF hS)
  by_cases hsmall : G.card≤1
  · have hp : 1≤((L-1)^2+L)*N := by nlinarith [Nat.zero_le ((L-1)^2)]
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
          (degreeBudget_le_linear N (L)))
      have hLA : Legal (Ground N) (Avoiders G c) := ⟨
        fun S hS=>hLG.1 S (Finset.mem_filter.mp hS).1,
        fun S hS U hU hne=>hLG.2 S (Finset.mem_filter.mp hS).1 U (Finset.mem_filter.mp hU).1 hne⟩
      have hcross := SparseCross41.actual_cross_pool_bound (A.erase c) (B.erase c) hLA
        (fun S hS=>hBG S (Finset.mem_filter.mp hS).1)
        (SparseCross41.singleton_erases_disjoint hAB)
        (SparseCross41.actual_singleton_cross_hits hLG hA hB hAB)
      have ha := erase_span_card hcA (Finset.mem_filter.mp hA).2
      have hb := erase_span_card hcB (Finset.mem_filter.mp hB).2
      have hproduct := Nat.mul_le_mul_right N (Nat.mul_le_mul ha hb)
      have hcross' : (Avoiders G c).card≤(L-1)^2*N := by
        nlinarith only [hcross,hproduct]
      have hh : G.card≤((L-1)^2+L)*N := by nlinarith only [hdegree,hcross',hpart]
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
      (choose_span_pool A.card L (Finset.mem_filter.mp hA).2 hL)
    exact (hh.trans hpool).trans (le_max_right _ _)

theorem actual_span_joint_square {N L s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hL : 0<L) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,S.card≤s)
    (hnocommon : ∀c∈Ground N,∃T∈F,c∉T) :
    (SpanMembers F L).card≤max (DegreeBudget N s) (L^2*N) := by
  exact (actual_span_joint_exact hN hL hlegal hbad hsize hnocommon).trans
    (max_le_max le_rfl (Nat.mul_le_mul_right N (span_fee_le_square L hL)))

theorem actual_span_joint_rational {N r L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hL : 0<L) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,r*S.card≤N)
    (hnocommon : ∀c∈Ground N,∃T∈F,c∉T) :
    ((SpanMembers F L).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      ((L:ℝ)^2*(N:ℝ)) := by
  have hsmall : ∀S∈F,S.card≤N/r := by
    intro S hS
    apply (Nat.le_div_iff_mul_le (by omega : 0<r)).mpr
    simpa only [Nat.mul_comm] using hsize S hS
  have hh := actual_span_joint_square (by omega : 1≤N) hL hlegal hbad hsmall hnocommon
  have hhR : ((SpanMembers F L).card:ℝ)≤max (DegreeBudget N (N/r):ℝ)
      ((L:ℝ)^2*(N:ℝ)) := by exact_mod_cast hh
  exact hhR.trans (max_le_max (degreeBudget_ratio N r hN hr) le_rfl)

theorem actual_span_empty_kernel {N r L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hL : 0<L) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,r*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ((SpanMembers F L).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      ((L:ℝ)^2*(N:ℝ)) := by
  exact actual_span_joint_rational hN hr hL hlegal hbad hsize
    (actual_omitter_of_empty_kernel hkernel)

theorem actual_span12_joint {N K s : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,S.card≤s)
    (hnocommon : ∀c∈Ground N,∃T∈F,c∉T) :
    (SpanMembers F (12*K)).card≤max (DegreeBudget N s) (144*K^2*N) := by
  have hh := actual_span_joint_square hN (by omega : 0<12*K) hlegal hbad hsize hnocommon
  have he : (12*K)^2*N=144*K^2*N := by ring
  rwa [he] at hh

theorem actual_span12_rational {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,r*S.card≤N)
    (hnocommon : ∀c∈Ground N,∃T∈F,c∉T) :
    ((SpanMembers F (12*K)).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      (144*(K:ℝ)^2*(N:ℝ)) := by
  have hh := actual_span_joint_rational hN hr (by omega : 0<12*K) hlegal hbad hsize hnocommon
  have he : ((12*K:ℕ):ℝ)^2*(N:ℝ)=144*(K:ℝ)^2*(N:ℝ) := by push_cast;ring
  rwa [he] at hh

theorem actual_span12_empty_kernel {N r K : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4≤N) (hr : 2≤r) (hK : 0<K) (hlegal : Legal (Ground N) F)
    (hbad : ∀S∈F,¬IsAP S) (hsize : ∀S∈F,r*S.card≤N)
    (hkernel : PrivateFinset.Kernel (Ground N) F=∅) :
    ((SpanMembers F (12*K)).card:ℝ)≤max
      (((2*(r:ℝ)-1)/(2*(r:ℝ)^2))*(N:ℝ)^2-3*(N:ℝ)/(2*(r:ℝ)))
      (144*(K:ℝ)^2*(N:ℝ)) := by
  exact actual_span12_rational hN hr hK hlegal hbad hsize
    (actual_omitter_of_empty_kernel hkernel)

#print axioms erase_span_card
#print axioms choose_span_pool
#print axioms span_fee_le_square
#print axioms actual_span_joint_exact
#print axioms actual_span_joint_square
#print axioms actual_span_joint_rational
#print axioms actual_span_empty_kernel
#print axioms actual_span12_joint
#print axioms actual_span12_rational
#print axioms actual_span12_empty_kernel
end
end JSP233.SmallSpan48

