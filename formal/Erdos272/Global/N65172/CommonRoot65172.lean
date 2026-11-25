module

public import Erdos272.Counting.N65172.SmallThinning65172
public import Erdos272.Global.N65172.CommonBounds65172
public import Erdos272.Global.N65172.HighRoot65172
public import Erdos272.Resources.N65172.SmallCredit65172

@[expose] public section

namespace JSP233.CommonRoot65172
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 WindowData65172 CommonBounds65172 SmallData65172
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option Elab.async false

theorem root_cap_le {w : ℕ} (hw : w<8) : RootK w≤554 := by
  interval_cases w <;> norm_num [RootK]

theorem root_credit_formula {w : ℕ} (hw : w<8) :
    (RootCredit w : ℝ)=(RootK w : ℝ)*((RootK w : ℝ)+3)/2 := by
  interval_cases w <;> norm_num [RootCredit,RootK]

theorem actual_root_from_kernel {N p : ℕ} {F : Finset (Finset ℤ)}
    (hp : p<2) (hN : (policy p).low≤N) (hhi : N≤(policy p).high)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<8, (info w).low≤N → N≤(info w).high → SourceBound N w F)
    (hsmall : (Small (SparseCrooked N 12 F) (policy p).T).Nonempty)
    (hkernel : (Kernel (Ground N) (Small (SparseCrooked N 12 F) (policy p).L)).Nonempty) :
    ∃ c∈Ground N, ∀ S∈Retained N 12 F, ¬IsAP S → c∈S := by
  have hg := SmallGates65172.gates hp
  have hlo := hg.low_bound.trans hN
  have hupper := hhi.trans hg.high_bound
  let G := SparseCrooked N 12 F
  have hGF : G⊆F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S∈G, 12*S.card≤N := fun S hS => (actual_sparse_membership.mp hS).2.2
  obtain ⟨c,hc⟩ := hkernel
  obtain ⟨hcN,hcsmall⟩ := Finset.mem_filter.mp hc
  by_cases hroot : ∀ S∈G, c∈S
  · exact ⟨c,hcN,fun S hS hbadS => hroot S (Finset.mem_filter.mpr ⟨hS,hbadS⟩)⟩
  have homit : ∃ S∈G, c∉S := by simpa only [not_forall,exists_prop] using hroot
  obtain ⟨T,hT,hmin⟩ := actual_minimum_omitter homit
  let A := Avoiders G c
  have hAG : A⊆G := Finset.filter_subset _ _
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hlegal.1 S (hAG hS),
      fun S hS U hU hSU => hlegal.2 S (hAG hS) U (hAG hU) hSU⟩
  have hAsize : ∀ S∈A, (policy p).L+1≤S.card := by
    intro S hS
    by_contra hn
    have hh : S∈Small G (policy p).L := Finset.mem_filter.mpr ⟨hAG hS,by omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  have hpartition := root_avoider_card_partition G c
  have hpR : (G.card : ℝ)=(RootPart G c).card+A.card := by exact_mod_cast hpartition.symm
  have hpaid : ∀ w, w<8 → (info w).low≤N → N≤(info w).high →
      T.card≤RootK w → (∀ S∈A, (info w).memberFloor≤S.card) →
      WitnessCondition w F → False := by
    intro w hw hl wh hcut hsize hwitness
    have hK := root_cap_le hw
    have hr := CommonBounds80470.degree_payment (by omega : 2≤N)
      (by omega : RootK w+2≤N) hlegal hbad hT hcut
    have hcredit := root_credit_formula hw
    have hpay : (G.card : ℝ)≤A.card+(RootK w : ℝ)*N-(RootCredit w : ℝ) := by
      rw [hcredit]
      linarith only [hpR,hr]
    exact source_contradiction hw hl wh hF hcard
      (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF)
      (hsource w hw hl wh A hA (fun S hS => hbad S (hAG hS)) hsize
        (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF) hwitness) hpay
  obtain ⟨A₀,hA₀⟩ := hsmall
  obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
  by_cases h78 : T.card≤78
  · have hL77 : (policy p).L≤77 := by
      have ht := hAsize T hT
      omega
    apply False.elim (hpaid 0 (by decide)
      ((hg.root78_low hL77).trans hN) (hhi.trans (hg.root78_high hL77)) h78 ?_ ?_)
    · intro S hS
      change 78≤S.card
      have ht := hAsize S hS
      have hTL := hg.T_le_L
      have hTlow := hg.T_lower
      omega
    · intro _
      refine ⟨A₀,hGF hA₀G,?_⟩
      change A₀.card≤77
      have hTL := hg.T_le_L
      omega
  by_cases h79 : T.card≤79
  · have hL78 : (policy p).L≤78 := by
      have ht := hAsize T hT
      omega
    apply False.elim (hpaid 2 (by decide)
      ((hg.root79_low hL78).trans hN) (hhi.trans (hg.root79_high hL78)) h79 ?_ ?_)
    · intro S hS
      change 79≤S.card
      have ht := hmin S hS
      omega
    · intro _
      refine ⟨A₀,hGF hA₀G,?_⟩
      change A₀.card≤78
      have hTL := hg.T_le_L
      omega
  by_cases h100 : T.card≤100
  · apply False.elim (hpaid (policy p).base (hg.base_lt.trans (by decide : 7<8))
      (hg.base_low.trans hN) (hhi.trans hg.base_high) ?_ ?_ ?_)
    · simpa only [hg.base_root_cap] using h100
    · intro S hS
      rw [hg.base_minimum]
      apply max_le
      · have hm := hmin S hS
        omega
      · exact hAsize S hS
    · intro _
      exact ⟨A₀,hGF hA₀G,hW.trans hg.base_root_witness⟩
  by_cases h554 : T.card≤554
  · apply False.elim (hpaid 7 (by decide) hlo hupper h554 ?_ ?_)
    · intro S hS
      change 101≤S.card
      have hm := hmin S hS
      omega
    · intro hn
      omega
  have hb := HighRoot65172.actual_high_root (by omega) hupper hlegal hbad hsparse hT (by omega) hmin
  exact False.elim (high_contradiction hlo hupper hF hcard hb)

theorem whole_source_contradiction {N p : ℕ} {F : Finset (Finset ℤ)}
    (hp : p<2) (hN : (policy p).low≤N) (hhi : N≤(policy p).high)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<8, (info w).low≤N → N≤(info w).high → SourceBound N w F)
    (hsmall : Small (SparseCrooked N 12 F) (policy p).T=∅) : False := by
  have hg := SmallGates65172.gates hp
  have hlo := hg.low_bound.trans hN
  have hupper := hhi.trans hg.high_bound
  let G := SparseCrooked N 12 F
  have hGF : G⊆F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S∈G, 12*S.card≤N := fun S hS => (actual_sparse_membership.mp hS).2.2
  have hminimum : ∀ S∈G, (policy p).T+1≤S.card := by
    intro S hS
    by_contra hn
    have hh : S∈Small G (policy p).T := Finset.mem_filter.mpr ⟨hS,by omega⟩
    rw [hsmall] at hh
    exact Finset.notMem_empty _ hh
  have hpaid : ∀ w, w<8 → (info w).low≤N → N≤(info w).high →
      (∀ S∈G, (info w).memberFloor≤S.card) → WitnessCondition w F → False := by
    intro w hw hl wh hsize hwitness
    apply source_contradiction hw hl wh hF hcard hsparse hGF
      (hsource w hw hl wh G hlegal hbad hsize hsparse hGF hwitness)
    have hK := root_cap_le hw
    have hK0 := Nat.cast_nonneg (α := ℝ) (RootK w)
    have hn : (65172 : ℝ)≤N := by exact_mod_cast hlo
    have hKR : (RootK w : ℝ)≤554 := by exact_mod_cast hK
    rw [root_credit_formula hw]
    have hb := mul_nonneg hK0 (show 0≤(N : ℝ)-((RootK w : ℝ)+3)/2 by linarith)
    nlinarith only [hb]
  by_cases h78 : (Small G 78).Nonempty
  · obtain ⟨A₀,hA₀⟩ := h78
    obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
    apply hpaid 1 (by decide) (hg.whole78_low.trans hN)
      (hhi.trans hg.whole78_high) ?_ ?_
    · intro S hS
      change 78≤S.card
      have hm := hminimum S hS
      have ht := hg.T_lower
      omega
    · intro _
      exact ⟨A₀,hGF hA₀G,hW⟩
  by_cases h79 : (Small G 79).Nonempty
  · obtain ⟨A₀,hA₀⟩ := h79
    obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
    have hT78 : (policy p).T≤78 := by
      have hm := hminimum A₀ hA₀G
      omega
    apply hpaid 3 (by decide) ((hg.whole79_low hT78).trans hN)
      (hhi.trans (hg.whole79_high hT78)) ?_ ?_
    · intro S hS
      change 79≤S.card
      by_contra hn
      exact h78 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
    · intro _
      exact ⟨A₀,hGF hA₀G,hW⟩
  by_cases h82 : (Small G 82).Nonempty
  · obtain ⟨A₀,hA₀⟩ := h82
    obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
    have hT81 : (policy p).T≤81 := by
      have hm := hminimum A₀ hA₀G
      omega
    apply hpaid (policy p).base (hg.base_lt.trans (by decide : 7<8))
      (hg.base_low.trans hN) (hhi.trans hg.base_high) ?_ ?_
    · intro S hS
      apply (hg.base_whole_minimum hT81).trans
      apply max_le
      · by_contra hn
        exact h79 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
      · exact hminimum S hS
    · intro _
      exact ⟨A₀,hGF hA₀G,hW.trans hg.base_whole_witness⟩
  by_cases h86 : (Small G 86).Nonempty
  · obtain ⟨A₀,hA₀⟩ := h86
    obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
    apply hpaid (policy p).mid (hg.mid_lt.trans (by decide : 7<8))
      (hg.mid_low.trans hN) (hhi.trans hg.mid_high) ?_ ?_
    · intro S hS
      rw [hg.mid_minimum]
      apply max_le
      · by_contra hn
        exact h82 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
      · exact hminimum S hS
    · intro _
      exact ⟨A₀,hGF hA₀G,hW.trans hg.mid_witness⟩
  by_cases h100 : (Small G 100).Nonempty
  · apply hpaid 6 (by decide) hlo hupper ?_ ?_
    · intro S hS
      change 87≤S.card
      by_contra hn
      exact h86 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
    · intro _
      obtain ⟨A₀,hA₀⟩ := h100
      obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
      exact ⟨A₀,hGF hA₀G,hW⟩
  apply hpaid 7 (by decide) hlo hupper ?_ ?_
  · intro S hS
    change 101≤S.card
    by_contra hn
    exact h100 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
  · intro hn
    omega

theorem thin_source_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172≤N) (hhi : N≤65967) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : SourceBound N 0 F)
    (hsmall : (Small (SparseCrooked N 12 F) 77).Nonempty)
    (hthin : (Small (SparseCrooked N 12 F) 77).card≤N*(N-1)/5852) : False := by
  let G:=SparseCrooked N 12 F
  let S:=Small G 77
  let A:=G\S
  have hGF : G⊆F := actual_sparse_subset N 12 F
  have hlegalG : Legal (Ground N) G := actual_sparse_legal hF
  have hAG : A⊆G := Finset.sdiff_subset
  have hAF : A⊆F := hAG.trans hGF
  have hlegalA:=Small77Rank65172.legal_sub hlegalG hAG
  have hbad : ∀T∈A,¬IsAP T := fun T hT=>(actual_sparse_membership.mp (hAG hT)).2.1
  have hsparse : ∀T∈A,12*T.card≤N := fun T hT=>(actual_sparse_membership.mp (hAG hT)).2.2
  have hsize : ∀T∈A,(info 0).memberFloor≤T.card := by
    intro T hT
    change 78≤T.card
    obtain ⟨hTG,hTS⟩ := Finset.mem_sdiff.mp hT
    by_contra hn
    exact hTS (Finset.mem_filter.mpr ⟨hTG,by omega⟩)
  obtain ⟨A₀,hA₀⟩ := hsmall
  obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
  have hwitness : WitnessCondition 0 F := by
    intro _
    exact ⟨A₀,hGF hA₀G,hW⟩
  have hinner:=hsource A hlegalA hbad hsize hsparse hAF hwitness
  have hSsub : S⊆G := Finset.filter_subset _ _
  have hcN:=Finset.card_sdiff_add_card_eq_card hSsub
  change A.card+S.card=G.card at hcN
  have hcR : (A.card : ℝ)+(S.card : ℝ)=G.card := by exact_mod_cast hcN
  have hpay:=SmallThinning65172.thin_payment (by omega : 48≤N) hhi hthin
  have hG : (G.card : ℝ)≤A.card+(RootK 0 : ℝ)*(N : ℝ)-(RootCredit 0 : ℝ) := by
    change (G.card : ℝ)≤A.card+78*(N : ℝ)-3159
    linarith only [hcR,hpay]
  exact source_contradiction (w:=0) (by decide) hN hhi hF hcard hsparse hAF hinner hG

#print axioms thin_source_contradiction

theorem policy_cover {N : ℕ} (hN : 65172≤N) (hhi : N≤65967) :
    ∃p<2,(policy p).low≤N ∧ N≤(policy p).high := by
  exact ⟨0,by decide,hN,hhi⟩

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172≤N) (hhi : N≤65967)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<8, (info w).low≤N → N≤(info w).high → SourceBound N w F) :
    ∃ c∈Ground N, ∀ S∈Retained N 12 F, ¬IsAP S → c∈S := by
  obtain ⟨p,hp,hlo,hupper⟩ := policy_cover hN hhi
  let G := SparseCrooked N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  by_cases hsmall : Small G (policy p).T=∅
  · exact False.elim (whole_source_contradiction hp hlo hupper hF hcard hsource hsmall)
  have hsmallN := Finset.nonempty_iff_ne_empty.mpr hsmall
  by_cases hkernel : Kernel (Ground N) (Small G (policy p).L)=∅
  · have hk : Kernel (Ground N) (Small G 77)=∅ := by simpa only [policy] using hkernel
    rcases SmallCredit65172.credit_or_thin hN hlegal hbad hk with hb | hthin
    · have hbound : (G.card : ℝ)≤((policy p).coefficient : ℝ)*N-(policy p).credit := by
        simpa only [policy,Nat.cast_ofNat] using hb
      exact False.elim (small_policy_contradiction hp hlo hupper hF hcard hbound)
    · exact False.elim (thin_source_contradiction hN hhi hF hcard
        (hsource 0 (by decide) (by change 65172≤N;exact hN) (by change N≤65967;exact hhi))
        (by simpa only [policy] using hsmallN) hthin.2)
  exact actual_root_from_kernel hp hlo hupper hF hcard hsource hsmallN
    (Finset.nonempty_iff_ne_empty.mpr hkernel)

#print axioms root_cap_le
#print axioms root_credit_formula
#print axioms actual_root_from_kernel
#print axioms whole_source_contradiction
#print axioms policy_cover
#print axioms actual_common_root
end
end JSP233.CommonRoot65172
