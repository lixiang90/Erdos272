module

public import Erdos272.Resources.N84364.CrossRankBudget84364
public import Erdos272.Core.N65172.Small77Kernel65172

@[expose] public section

namespace JSP233.Small77Rank65172
open StarCompletion SparseSmall39 SmallKernel112 CrossRankBudget84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Avoid (F : Finset (Finset ℤ)) (D : Finset ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S=>Disjoint S D)

theorem legal_sub {Ω : Finset ℤ} {F H : Finset (Finset ℤ)}
    (hlegal : Legal Ω F) (hHF : H⊆F) : Legal Ω H :=
  ⟨fun S hS=>hlegal.1 S (hHF hS),fun S hS T hT hne=>hlegal.2 S (hHF hS) T (hHF hT) hne⟩

theorem root_budget {N : ℕ} {F : Finset (Finset ℤ)} {x : ℤ}
    (hN : 78≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅) (hx : x∈Ground N) :
    ((RootPart F x).card : ℝ)≤77*(N : ℝ)-3080 := by
  obtain ⟨T,hTS,hxT⟩ := actual_omitter_of_empty_kernel hkernel x hx
  obtain ⟨hTF,hTc⟩ := Finset.mem_filter.mp hTS
  have hb := (actual_degree_from_omitter hlegal hbad hTF hxT).trans (degreeBudget_mono N hTc)
  have hc := degreeBudget_closed N 77 (by omega) (by omega)
  have hchoose : Nat.choose 77 2=2926 := by decide
  rw [hchoose] at hc
  have hs : N-2+2=N := Nat.sub_add_cancel (by omega)
  have he : 77*(N-2)+154=77*N := by nlinarith only [hs]
  have hh : (RootPart F x).card+3080≤77*N := by omega
  have hr : ((RootPart F x).card : ℝ)+3080≤77*(N : ℝ) := by exact_mod_cast hh
  linarith only [hr]

theorem avoid_cover (F : Finset (Finset ℤ)) (D : Finset ℤ) :
    F.card≤(Avoid F D).card+∑x∈D,(RootPart F x).card := by
  have hcover : F⊆Avoid F D ∪ D.biUnion (fun x=>RootPart F x) := by
    intro S hS
    by_cases hd : Disjoint S D
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hS,hd⟩))
    · apply Finset.mem_union.mpr;right
      by_contra hn
      apply hd
      apply Finset.disjoint_left.mpr
      intro x hxS hxD
      exact hn (Finset.mem_biUnion.mpr ⟨x,hxD,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩)
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _))

theorem avoid_cover_budget {N : ℕ} {F : Finset (Finset ℤ)} {D : Finset ℤ}
    (hN : 78≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅) (hD : D⊆Ground N) :
    (F.card : ℝ)≤(Avoid F D).card+(D.card : ℝ)*(77*(N : ℝ)-3080) := by
  have hc : (F.card : ℝ)≤(Avoid F D).card+∑x∈D,((RootPart F x).card : ℝ) := by
    exact_mod_cast avoid_cover F D
  have hs := Finset.sum_le_sum (fun x hx=>root_budget hN hlegal hbad hkernel (hD hx))
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  linarith only [hc,hs]

theorem hits_diff {Ω A D S : Finset ℤ} {F : Finset (Finset ℤ)}
    (hlegal : Legal Ω F) (hA : A∈F) (hS : S∈F)
    (hDA : D⊆A) (hDN : D.Nonempty) (havoid : Disjoint S D) :
    (S∩(A\D)).Nonempty := by
  have hne : S≠A := by
    intro he
    obtain ⟨x,hx⟩ := hDN
    exact Finset.disjoint_left.mp havoid (he.symm ▸ hDA hx) hx
  obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 S hS A hA hne)
  obtain ⟨hxS,hxA⟩ := Finset.mem_inter.mp hx
  exact ⟨x,Finset.mem_inter.mpr ⟨hxS,Finset.mem_sdiff.mpr
    ⟨hxA,fun hxD=>Finset.disjoint_left.mp havoid hxS hxD⟩⟩⟩

theorem moderate_credit {N : ℕ} {F : Finset (Finset ℤ)} {A B : Finset ℤ}
    (hN : 78≤N) (hlegal : Legal (Ground N) F) (hbad : ∀S∈F,¬IsAP S)
    (hkernel : PrivateFinset.Kernel (Ground N) (Small F 77)=∅)
    (hA : A∈F) (hB : B∈F) (hAc : A.card=77) (hBc : B.card=77)
    (hlo : 2≤(A∩B).card) (hhi : (A∩B).card≤75) :
    (F.card : ℝ)≤5779*(N : ℝ)-231312 := by
  let D:=A∩B
  let X:=A\D
  let Y:=B\D
  let H:=Avoid F D
  have hDF : D⊆Ground N := Finset.inter_subset_left.trans (hlegal.1 A hA)
  have hDN : D.Nonempty := Finset.card_pos.mp (by dsimp only [D];omega)
  have hHF : H⊆F := Finset.filter_subset _ _
  have hXY : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hxX hxY
    obtain ⟨hxA,hxn⟩ := Finset.mem_sdiff.mp hxX
    exact hxn (Finset.mem_inter.mpr ⟨hxA,(Finset.mem_sdiff.mp hxY).1⟩)
  have hDX : Disjoint D X := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxX
    exact (Finset.mem_sdiff.mp hxX).2 hxD
  have hDY : Disjoint D Y := by
    apply Finset.disjoint_left.mpr
    intro x hxD hxY
    exact (Finset.mem_sdiff.mp hxY).2 hxD
  have havoid : ∀S∈H,Disjoint S D := fun S hS=>(Finset.mem_filter.mp hS).2
  have hb := actual_cross_hit_budget (legal_sub hlegal hHF) (fun S hS=>hbad S (hHF hS))
    hDF (Finset.sdiff_subset.trans (hlegal.1 A hA)) (Finset.sdiff_subset.trans (hlegal.1 B hB))
    hXY hDX hDY havoid
    (fun S hS=>hits_diff hlegal hA (hHF hS) Finset.inter_subset_left hDN (havoid S hS))
    (fun S hS=>hits_diff hlegal hB (hHF hS) Finset.inter_subset_right hDN (havoid S hS))
  rw [ground_card] at hb
  have hr : (H.card : ℝ)+(X.card : ℝ)*Y.card*(D.card+2)+
      (Y.card : ℝ)*(X.card.choose 2 : ℝ)+(X.card : ℝ)*(Y.card.choose 2 : ℝ)
      ≤(X.card : ℝ)*Y.card*N := by exact_mod_cast hb
  rw [Nat.cast_choose_two,Nat.cast_choose_two] at hr
  have hxN := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_left (s₁:=A) (s₂:=B))
  have hyN := Finset.card_sdiff_add_card_eq_card (Finset.inter_subset_right (s₁:=A) (s₂:=B))
  change X.card+D.card=A.card at hxN
  change Y.card+D.card=B.card at hyN
  rw [hAc] at hxN
  rw [hBc] at hyN
  have hx : (X.card : ℝ)=77-(D.card : ℝ) := by
    have hh : (X.card : ℝ)+(D.card : ℝ)=77 := by exact_mod_cast hxN
    linarith only [hh]
  have hy : (Y.card : ℝ)=77-(D.card : ℝ) := by
    have hh : (Y.card : ℝ)+(D.card : ℝ)=77 := by exact_mod_cast hyN
    linarith only [hh]
  rw [hx,hy] at hr
  have hc := avoid_cover_budget hN hlegal hbad hkernel hDF
  change (F.card : ℝ)≤(H.card : ℝ)+(D.card : ℝ)*(77*(N : ℝ)-3080) at hc
  have hp : (F.card : ℝ)≤((77-(D.card : ℝ))^2+77*D.card)*N-
      78*(77-(D.card : ℝ))^2-3080*D.card := by nlinarith only [hr,hc]
  have hl : (2 : ℝ)≤D.card := by exact_mod_cast hlo
  have hh : (D.card : ℝ)≤75 := by exact_mod_cast hhi
  have hn : (78 : ℝ)≤N := by exact_mod_cast hN
  have hm := mul_nonneg (show (0 : ℝ)≤75-(D.card : ℝ) by linarith only [hh])
    (show (0 : ℝ)≤((D.card : ℝ)-2)*((N : ℝ)-78)+2926 by
      have ht:=mul_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hn)
      linarith only [ht])
  nlinarith only [hp,hm]

#print axioms legal_sub
#print axioms root_budget
#print axioms avoid_cover
#print axioms avoid_cover_budget
#print axioms hits_diff
#print axioms moderate_credit
end
end JSP233.Small77Rank65172
