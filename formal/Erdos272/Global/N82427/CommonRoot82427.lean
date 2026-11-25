module

public import Erdos272.Global.N82427.CommonBounds82427
public import Erdos272.Global.N82427.HighRoot82427
public import Erdos272.Resources.N82427.SmallCredit82427

@[expose] public section

namespace JSP233.CommonRoot82427
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 WindowData82427 CommonBounds82427
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_root_from_kernel {N L : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427 ≤ N) (hhi : N ≤ 84363) (hL : L=86 ∨ L=87)
    (hLlow : L=86 → N ≤ 83394)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsource : ∀ w < 4, (info w).low ≤ N → N ≤ (info w).high → SourceBound N w)
    (hkernel : (Kernel (Ground N) (Small (SparseCrooked N 12 F) L)).Nonempty) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  let G := SparseCrooked N 12 F
  have hGF : G ⊆ F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S ∈ G, 12*S.card ≤ N := fun S hS => (actual_sparse_membership.mp hS).2.2
  obtain ⟨c, hc⟩ := hkernel
  obtain ⟨hcN, hcsmall⟩ := Finset.mem_filter.mp hc
  by_cases hroot : ∀ S ∈ G, c ∈ S
  · exact ⟨c, hcN, fun S hS hbadS => hroot S (Finset.mem_filter.mpr ⟨hS, hbadS⟩)⟩
  have homit : ∃ S ∈ G, c ∉ S := by simpa only [not_forall, exists_prop] using hroot
  obtain ⟨T, hT, hmin⟩ := actual_minimum_omitter homit
  let A := Avoiders G c
  have hAG : A ⊆ G := Finset.filter_subset _ _
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hlegal.1 S (hAG hS), fun S hS U hU hSU => hlegal.2 S (hAG hS) U (hAG hU) hSU⟩
  have hAsize : ∀ S ∈ A, L+1 ≤ S.card := by
    intro S hS
    by_contra hn
    have hh : S ∈ Small G L := Finset.mem_filter.mpr ⟨hAG hS, by omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  have hp := root_avoider_card_partition G c
  have hpR : (G.card : ℝ) = (RootPart G c).card+A.card := by exact_mod_cast hp.symm
  have hpaid : ∀ w, w < 4 → (info w).low ≤ N → N ≤ (info w).high →
      T.card ≤ RootK w → (∀ S ∈ A, (info w).memberFloor ≤ S.card) → False := by
    intro w hw hlo hupper hcut hsize
    have hK : RootK w ≤ 554 := by interval_cases w <;> norm_num [RootK]
    have hr := degree_payment (by omega : 2 ≤ N) (by omega : RootK w+2 ≤ N)
      hlegal hbad hT hcut
    have hcredit : (RootCredit w : ℝ) = (RootK w : ℝ)*((RootK w : ℝ)+3)/2 := by
      interval_cases w <;> norm_num [RootCredit, RootK]
    have hpay : (G.card : ℝ) ≤ A.card+(RootK w : ℝ)*N-(RootCredit w : ℝ) := by
      rw [hcredit]
      linarith only [hpR, hr]
    exact source_contradiction hw hlo hupper hF hcard
      (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF)
      (hsource w hw hlo hupper A hA (fun S hS => hbad S (hAG hS)) hsize
        (fun S hS => hsparse S (hAG hS))) hpay
  by_cases h87 : T.card ≤ 87
  · have hL86 : L=86 := by
      have ht := hAsize T hT
      omega
    apply False.elim (hpaid 0 (by decide) hN (hLlow hL86) h87 ?_)
    intro S hS
    change 87 ≤ S.card
    have hs := hAsize S hS
    omega
  by_cases h129 : T.card ≤ 129
  · apply False.elim (hpaid 2 (by decide) hN hhi h129 ?_)
    intro S hS
    change 88 ≤ S.card
    have hm := hmin S hS
    omega
  by_cases h554 : T.card ≤ 554
  · apply False.elim (hpaid 3 (by decide) hN hhi h554 ?_)
    intro S hS
    change 130 ≤ S.card
    have hm := hmin S hS
    omega
  have hb := HighRoot82427.actual_high_root hN hhi hlegal hbad hsparse hT (by omega) hmin
  exact False.elim (high_contradiction hN hhi hF hcard hb)

theorem whole_source_contradiction {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 2) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsource : SourceBound N w)
    (hsmall : Small (SparseCrooked N 12 F) 86=∅) : False := by
  let G := SparseCrooked N 12 F
  have hGF : G ⊆ F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S ∈ G, 12*S.card ≤ N := fun S hS => (actual_sparse_membership.mp hS).2.2
  have hsize : ∀ S ∈ G, (info w).memberFloor ≤ S.card := by
    intro S hS
    have hfloor : (info w).memberFloor=87 := by interval_cases w <;> rfl
    rw [hfloor]
    by_contra hn
    have hh : S ∈ Small G 86 := Finset.mem_filter.mpr ⟨hS, by omega⟩
    rw [hsmall] at hh
    exact Finset.notMem_empty _ hh
  apply source_contradiction (by omega : w < 4) hlo hhi hF hcard hsparse hGF
    (hsource G hlegal hbad hsize hsparse)
  have hN : (82427 : ℝ) ≤ N := by
    exact_mod_cast (WindowGates82427.gates (by omega : w < 4)).low_bound.trans hlo
  interval_cases w
  · norm_num only [RootK, RootCredit, Nat.cast_ofNat]
    change (G.card : ℝ) ≤ G.card+87*N-3915
    linarith only [hN]
  · norm_num [RootK, RootCredit, G]

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427 ≤ N) (hhi : N ≤ 84363)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsource : ∀ w < 4, (info w).low ≤ N → N ≤ (info w).high → SourceBound N w) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  let G := SparseCrooked N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  by_cases hlow : N ≤ 83394
  · by_cases hsmall : Small G 86=∅
    · exact False.elim (whole_source_contradiction (by decide : 0 < 2) hN hlow hF hcard
        (hsource 0 (by decide) hN hlow) hsmall)
    by_cases hkernel : Kernel (Ground N) (Small G 86)=∅
    · have hb := SmallCredit82427.actual_small_empty_kernel86 (by omega : 1893 ≤ N)
        hlegal hbad (Finset.nonempty_iff_ne_empty.mpr hsmall) hkernel
      exact False.elim (small_low_contradiction hN hhi hF hcard hb)
    exact actual_root_from_kernel hN hhi (Or.inl rfl) (fun _ => hlow) hF hcard hsource
      (Finset.nonempty_iff_ne_empty.mpr hkernel)
  have hupper : 83395 ≤ N := by omega
  by_cases hsmall86 : Small G 86=∅
  · exact False.elim (whole_source_contradiction (by decide : 1 < 2) hupper hhi hF hcard
      (hsource 1 (by decide) hupper hhi) hsmall86)
  by_cases hkernel : Kernel (Ground N) (Small G 87)=∅
  · have hb := SmallCredit82427.actual_small87_with_small86 (by omega : 1937 ≤ N)
      hlegal hbad (Finset.nonempty_iff_ne_empty.mpr hsmall86) hkernel
    exact False.elim (small_upper_contradiction hupper hhi hF hcard hb)
  exact actual_root_from_kernel hN hhi (Or.inr rfl) (by omega) hF hcard hsource
    (Finset.nonempty_iff_ne_empty.mpr hkernel)

#print axioms actual_root_from_kernel
#print axioms whole_source_contradiction
#print axioms actual_common_root
end
end JSP233.CommonRoot82427
