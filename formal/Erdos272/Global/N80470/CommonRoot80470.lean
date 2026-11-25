module

public import Erdos272.Global.N80470.CommonBounds80470
public import Erdos272.Global.N80470.HighRoot80470
public import Erdos272.Resources.N80470.SmallCredit80470

@[expose] public section

namespace JSP233.CommonRoot80470
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 WindowData80470 CommonBounds80470
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_root_from_kernel {N L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 80470≤N) (hhi : N≤82425) (hL : L=85 ∨ L=86)
    (hLlow : L=85 → N≤81426)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<4, (info w).low≤N → N≤(info w).high → SourceBound N w F)
    (hsmall : (Small (SparseCrooked N 12 F) 85).Nonempty)
    (hkernel : (Kernel (Ground N) (Small (SparseCrooked N 12 F) L)).Nonempty) :
    ∃ c∈Ground N, ∀ S∈Retained N 12 F, ¬IsAP S → c∈S := by
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
  have hAsize : ∀ S∈A, L+1≤S.card := by
    intro S hS
    by_contra hn
    have hh : S∈Small G L := Finset.mem_filter.mpr ⟨hAG hS,by omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  have hp := root_avoider_card_partition G c
  have hpR : (G.card : ℝ)=(RootPart G c).card+A.card := by exact_mod_cast hp.symm
  have hpaid : ∀ w, w<4 → (info w).low≤N → N≤(info w).high →
      T.card≤RootK w → (∀ S∈A, (info w).memberFloor≤S.card) →
      WitnessCondition w F → False := by
    intro w hw hlo hupper hcut hsize hwitness
    have hK : RootK w≤554 := by interval_cases w <;> norm_num [RootK]
    have hr := degree_payment (by omega : 2≤N) (by omega : RootK w+2≤N)
      hlegal hbad hT hcut
    have hcredit : (RootCredit w : ℝ)=(RootK w : ℝ)*((RootK w : ℝ)+3)/2 := by
      interval_cases w <;> norm_num [RootCredit,RootK]
    have hpay : (G.card : ℝ)≤A.card+(RootK w : ℝ)*N-(RootCredit w : ℝ) := by
      rw [hcredit]
      linarith only [hpR,hr]
    exact source_contradiction hw hlo hupper hF hcard
      (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF)
      (hsource w hw hlo hupper A hA (fun S hS => hbad S (hAG hS)) hsize
        (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF) hwitness) hpay
  by_cases h86 : T.card≤86
  · have hL85 : L=85 := by
      have ht := hAsize T hT
      omega
    apply False.elim (hpaid 0 (by decide) hN (hLlow hL85) h86 ?_ ?_)
    · intro S hS
      change 86≤S.card
      have hs := hAsize S hS
      omega
    · intro _
      obtain ⟨A₀,hA₀⟩ := hsmall
      obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
      exact ⟨A₀,hGF hA₀G,hW⟩
  by_cases h129 : T.card≤129
  · apply False.elim (hpaid 2 (by decide) hN hhi h129 ?_ ?_)
    · intro S hS
      change 87≤S.card
      have hm := hmin S hS
      omega
    · intro _
      exact ⟨T,hGF (hAG hT),h129⟩
  by_cases h554 : T.card≤554
  · apply False.elim (hpaid 3 (by decide) hN hhi h554 ?_ ?_)
    · intro S hS
      change 130≤S.card
      have hm := hmin S hS
      omega
    · intro hn
      omega
  have hb := HighRoot80470.actual_high_root hN hhi hlegal hbad hsparse hT (by omega) hmin
  exact False.elim (high_contradiction hN hhi hF hcard hb)

theorem whole_source_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 80470≤N) (hhi : N≤82425)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<4, (info w).low≤N → N≤(info w).high → SourceBound N w F)
    (hsmall : Small (SparseCrooked N 12 F) 85=∅) : False := by
  let G := SparseCrooked N 12 F
  have hGF : G⊆F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S∈G, 12*S.card≤N := fun S hS => (actual_sparse_membership.mp hS).2.2
  have hpaid : ∀ w, w<4 → (info w).low≤N → N≤(info w).high →
      (∀ S∈G, (info w).memberFloor≤S.card) → WitnessCondition w F → False := by
    intro w hw hlo hupper hsize hwitness
    apply source_contradiction hw hlo hupper hF hcard hsparse hGF
      (hsource w hw hlo hupper G hlegal hbad hsize hsparse hGF hwitness)
    have hn : (80470 : ℝ)≤N := by exact_mod_cast hN
    interval_cases w <;> norm_num [RootK,RootCredit] <;> linarith only [hn]
  by_cases h86 : (Small G 86).Nonempty
  · apply hpaid 1 (by decide) hN hhi ?_ ?_
    · intro S hS
      change 86≤S.card
      by_contra hn
      have hh : S∈Small G 85 := Finset.mem_filter.mpr ⟨hS,by omega⟩
      rw [hsmall] at hh
      exact Finset.notMem_empty _ hh
    · intro _
      obtain ⟨A₀,hA₀⟩ := h86
      obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
      exact ⟨A₀,hGF hA₀G,hW⟩
  by_cases h129 : (Small G 129).Nonempty
  · apply hpaid 2 (by decide) hN hhi ?_ ?_
    · intro S hS
      change 87≤S.card
      by_contra hn
      exact h86 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
    · intro _
      obtain ⟨A₀,hA₀⟩ := h129
      obtain ⟨hA₀G,hW⟩ := Finset.mem_filter.mp hA₀
      exact ⟨A₀,hGF hA₀G,hW⟩
  apply hpaid 3 (by decide) hN hhi ?_ ?_
  · intro S hS
    change 130≤S.card
    by_contra hn
    exact h129 ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩
  · intro hn
    omega

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 80470≤N) (hhi : N≤82425)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsource : ∀ w<4, (info w).low≤N → N≤(info w).high → SourceBound N w F) :
    ∃ c∈Ground N, ∀ S∈Retained N 12 F, ¬IsAP S → c∈S := by
  let G := SparseCrooked N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S∈G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  by_cases hsmall : Small G 85=∅
  · exact False.elim (whole_source_contradiction hN hhi hF hcard hsource hsmall)
  have hsmallN := Finset.nonempty_iff_ne_empty.mpr hsmall
  by_cases hlow : N≤81426
  · by_cases hkernel : Kernel (Ground N) (Small G 85)=∅
    · have hb := SmallCredit80470.actual_small_empty_kernel85 (by omega : 1850≤N)
        hlegal hbad hsmallN hkernel
      exact False.elim (small_low_contradiction hN hhi hF hcard hb)
    exact actual_root_from_kernel hN hhi (Or.inl rfl) (fun _ => hlow) hF hcard hsource
      hsmallN (Finset.nonempty_iff_ne_empty.mpr hkernel)
  have hupper : 81427≤N := by omega
  by_cases hkernel : Kernel (Ground N) (Small G 86)=∅
  · have hb := SmallCredit80470.actual_small86_with_small85 (by omega : 1893≤N)
      hlegal hbad hsmallN hkernel
    exact False.elim (small_upper_contradiction hupper hhi hF hcard hb)
  exact actual_root_from_kernel hN hhi (Or.inr rfl) (by omega) hF hcard hsource
    hsmallN (Finset.nonempty_iff_ne_empty.mpr hkernel)

#print axioms actual_root_from_kernel
#print axioms whole_source_contradiction
#print axioms actual_common_root
end
end JSP233.CommonRoot80470
