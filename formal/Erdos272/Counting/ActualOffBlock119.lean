import Erdos272.Counting.BlockPacking119
import Erdos272.Counting.FullResidueBudget119

/-! Complete classes are now obtained from actual truncated off-source AP
traces. The physical720-endpoint loss and the final ceil block are paid
before the twelve-trace contradiction. -/
namespace JSP233.ActualOffBlock119
open StarCompletion APGeometry BlockAP119 BlockPacking119
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_complete_block_sum {F : Finset (Finset ℤ)}
    (T : Finset ℤ→Finset ℤ) (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ) (y A : ℤ)
    (hAP : ∀S∈F,APAt (d S:ℤ) (a S) (T S))
    (hd : ∀S∈F,0<d S ∧ d S≤12)
    (hc : ∀S∈F,Complete (T S) (d S) (a S) A)
    (hoff : ∀S∈F,¬(d S:ℤ)∣y-a S)
    (hpair : ∀S∈F,∀U∈F,S≠U→((T S)∩(T U)).card≤1) :
    (∑S∈F,((T S)∩Block A).card)≤330 := by
  let code := fun S=>Code (d S) (a S) y
  let C := F.image code
  have hC : C⊆FullResidueBudget119.AllCodes := by
    intro c hcC
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hcC
    apply FullResidueBudget119.mem_allCodes.mpr
    exact actual_off_code_bounds (hd S hS).1 (hd S hS).2 (hoff S hS)
  have hdisj : ∀z:ℕ,(C.filter (fun c=>z%c.1=c.2)).card≤1 := by
    intro z
    apply Finset.card_le_one.mpr
    intro c hcC u huC
    obtain ⟨hcC,hzc⟩ := Finset.mem_filter.mp hcC
    obtain ⟨huC,hzu⟩ := Finset.mem_filter.mp huC
    obtain ⟨S,hS,hCS⟩ := Finset.mem_image.mp hcC
    obtain ⟨U,hU,hCU⟩ := Finset.mem_image.mp huC
    by_cases hSU : S=U
    · rw [←hCS,←hCU,hSU]
    · have hs := actual_complete_classes_separated (hd S hS).1 (hd U hU).1
        (hd S hS).2 (hd U hU).2 (hc S hS) (hc U hU) (hpair S hS U hU hSU)
      have hzS : (d S:ℤ)∣(y+(z:ℤ))-a S := (code_residue_iff (hd S hS).1 _ _ z).mpr (by
        rw [←hCS] at hzc
        exact hzc)
      have hzU : (d U:ℤ)∣(y+(z:ℤ))-a U := (code_residue_iff (hd U hU).1 _ _ z).mpr (by
        rw [←hCU] at hzu
        exact hzu)
      exact False.elim (hs (y+(z:ℤ)) ⟨hzS,hzU⟩)
  have hb := FullResidueBudget119.full_residue_span_budget C hC hdisj
  have hinj := actual_complete_code_injective T d a y A hd hc hoff hpair
  rw [Finset.sum_image (by
    intro S hS U hU hEq
    exact hinj hS hU hEq)] at hb
  have hsum := Finset.sum_le_sum (fun S hS=>actual_block_trace_card (hd S hS).1 (hAP S hS) (A:=A))
  exact hsum.trans hb

theorem actual_truncated_trace_sum {F : Finset (Finset ℤ)}
    (T : Finset ℤ→Finset ℤ) (d : Finset ℤ→ℕ) (a : Finset ℤ→ℤ) (y L : ℤ) (M : ℕ)
    (hAP : ∀S∈F,APAt (d S:ℤ) (a S) (T S))
    (hd : ∀S∈F,0<d S ∧ d S≤12)
    (hsub : ∀S∈F,T S⊆Finset.Icc L (L+(M:ℤ)-1))
    (hne : ∀S∈F,(T S).Nonempty)
    (hoff : ∀S∈F,¬(d S:ℤ)∣y-a S)
    (hpair : ∀S∈F,∀U∈F,S≠U→((T S)∩(T U)).card≤1) :
    (∑S∈F,(T S).card)≤330*((M+359)/360)+720*F.card := by
  let lo := fun S=>if h:S∈F then (T S).min' (hne S h) else 0
  let hi := fun S=>if h:S∈F then (T S).max' (hne S h) else 0
  have hlo : ∀S∈F,lo S∈T S := by
    intro S hS
    simp only [lo,dif_pos hS]
    exact Finset.min'_mem _ (hne S hS)
  have hhi : ∀S∈F,hi S∈T S := by
    intro S hS
    simp only [hi,dif_pos hS]
    exact Finset.max'_mem _ (hne S hS)
  have hspan : ∀S∈F,∀x∈T S,lo S≤x ∧ x≤hi S := by
    intro S hS x hx
    simp only [lo,hi,dif_pos hS]
    exact ⟨Finset.min'_le _ x hx,Finset.le_max' _ x hx⟩
  apply actual_trace_sum_bound T lo hi L M 330 hsub hspan
  intro A
  let G := F.filter (fun S=>Active (lo S) (hi S) A)
  have hGF : G⊆F := Finset.filter_subset _ _
  apply actual_complete_block_sum T d a y A
    (fun S hS=>hAP S (hGF hS)) (fun S hS=>hd S (hGF hS))
  · intro S hS
    exact actual_complete_of_endpoints (hAP S (hGF hS)) (hlo S (hGF hS)) (hhi S (hGF hS))
      (Finset.mem_filter.mp hS).2.1 (Finset.mem_filter.mp hS).2.2
  · exact fun S hS=>hoff S (hGF hS)
  · exact fun S hS U hU hn=>hpair S (hGF hS) U (hGF hU) hn

theorem actual_off_point_capacity11 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ) (y : ℤ)
    (hLR : L≤R) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S≤12)
    (hlong : ∀S∈F,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffPoint F d a y).card≤11 := by
  by_contra hn
  obtain ⟨C,hCE,hCc⟩ := Finset.exists_subset_card_eq
    (show 12≤(OffResidue44.OffPoint F d a y).card by omega)
  let T := fun S:Finset ℤ=>S∩Finset.Icc (L:ℤ) (R:ℤ)
  let dn := fun S:Finset ℤ=>(d S).toNat
  have hCF : C⊆F := hCE.trans (Finset.filter_subset _ _)
  have hdcast : ∀S∈C,(dn S:ℤ)=d S := by
    intro S hS
    exact Int.toNat_of_nonneg (htrace S (hCF hS)).1.le
  have hd : ∀S∈C,0<dn S ∧ dn S≤12 := by
    intro S hS
    have hpos := (htrace S (hCF hS)).1
    have hu := hsteps S (hCF hS)
    have he := hdcast S hS
    constructor <;> omega
  have hpair : ∀S∈C,∀U∈C,S≠U→((T S)∩(T U)).card≤1 := by
    intro S hS U hU hne
    obtain ⟨hSF,hyS,hoff⟩ := Finset.mem_filter.mp (hCE hS)
    obtain ⟨hUF,hyU,_hoffU⟩ := Finset.mem_filter.mp (hCE hU)
    exact OffResidue44.off_point_trace_inter_card (htrace S hSF)
      (hlegal.2 S hSF U hUF hne) hyS hyU hoff
  have hAP : ∀S∈C,APAt (dn S:ℤ) (a S) (T S) := by
    intro S hS
    rw [hdcast S hS]
    exact htrace S (hCF hS)
  have hsub : ∀S∈C,T S⊆Finset.Icc (L:ℤ) ((L:ℤ)+(R-L+1:ℕ)-1) := by
    intro S _hS x hx
    have hh := Finset.mem_Icc.mp (Finset.mem_inter.mp hx).2
    exact Finset.mem_Icc.mpr ⟨hh.1,by omega⟩
  have hne : ∀S∈C,(T S).Nonempty := by
    intro S hS
    apply Finset.card_pos.mp
    have hh := hlong S (hCF hS)
    dsimp only [T]
    omega
  have hoff : ∀S∈C,¬(dn S:ℤ)∣y-a S := by
    intro S hS
    rw [hdcast S hS]
    exact (Finset.mem_filter.mp (hCE hS)).2.2
  have hb := actual_truncated_trace_sum T dn a y (L:ℤ) (R-L+1) hAP hd hsub hne hoff hpair
  have hl : (∑S∈C,((R-L+1)/13+2))≤∑S∈C,(T S).card :=
    Finset.sum_le_sum (by
      intro S hS
      have hh := hlong S (hCF hS)
      dsimp only [T]
      omega)
  simp only [Finset.sum_const,nsmul_eq_mul,hCc] at hl
  rw [hCc] at hb
  omega

theorem actual_off_residue_count11 {N L R : ℕ} {F : Finset (Finset ℤ)}
    (d a : Finset ℤ→ℤ)
    (hLR : L≤R) (hM : 1801800≤R-L+1)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀S∈F,APAt (d S) (a S) (S∩Finset.Icc (L:ℤ) (R:ℤ)))
    (hsteps : ∀S∈F,d S≤12)
    (hlong : ∀S∈F,(R-L+1)/13+1<(S∩Finset.Icc (L:ℤ) (R:ℤ)).card) :
    (OffResidue44.OffMembers F d a).card≤11*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by
  have hcover : OffResidue44.OffMembers F d a⊆
      (Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a) := by
    intro S hS
    obtain ⟨hSF,y,hyS,hoff⟩ := Finset.mem_filter.mp hS
    have hyI : y∉Finset.Icc (L:ℤ) (R:ℤ) := by
      intro hyI
      exact hoff (OffResidue44.origin_dvd (htrace S hSF) (Finset.mem_inter.mpr ⟨hyS,hyI⟩))
    exact Finset.mem_biUnion.mpr ⟨y,Finset.mem_sdiff.mpr ⟨hlegal.1 S hSF hyS,hyI⟩,
      Finset.mem_filter.mpr ⟨hSF,hyS,hoff⟩⟩
  calc
    _≤((Ground N\Finset.Icc (L:ℤ) (R:ℤ)).biUnion (OffResidue44.OffPoint F d a)).card := Finset.card_le_card hcover
    _≤∑y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),(OffResidue44.OffPoint F d a y).card := Finset.card_biUnion_le
    _≤∑_y∈Ground N\Finset.Icc (L:ℤ) (R:ℤ),11 := Finset.sum_le_sum (by
      intro y _hy
      exact actual_off_point_capacity11 d a y hLR hM hlegal htrace hsteps hlong)
    _=11*(Ground N\Finset.Icc (L:ℤ) (R:ℤ)).card := by simp [Nat.mul_comm]

#print axioms actual_complete_block_sum
#print axioms actual_truncated_trace_sum
#print axioms actual_off_point_capacity11
#print axioms actual_off_residue_count11
end
end JSP233.ActualOffBlock119
