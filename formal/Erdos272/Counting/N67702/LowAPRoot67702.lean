module

public import Erdos272.Counting.N80470.APQuotient80470

@[expose] public section

namespace JSP233.LowAPRoot67702
open StarCompletion APGeometry APCount41 APTail208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_same_step_common_root_low {N L d : ℕ} {F : Finset (Finset ℤ)}
    (hF : F.Nonempty) (hlegal : Legal (Ground N) F)
    (hne : ∀ S∈F,S.Nonempty) (hstep : ∀ S∈F,∃ p : ℤ,APAt (d : ℤ) p S)
    (hlow : ∀ S∈F,Low S≤(L : ℤ)) :
    ∃ c∈Ground N,c≤(L : ℤ) ∧ ∀ S∈F,c∈S := by
  let M := F.image Low
  have hM : M.Nonempty := hF.image Low
  let c := M.max' hM
  have hcM : c∈M := Finset.max'_mem _ hM
  obtain ⟨A,hA,hAc⟩ := Finset.mem_image.mp hcM
  have hcA : c∈A := hAc ▸ (low_spec (hne A hA)).1
  have hcL : c≤(L : ℤ) := hAc ▸ hlow A hA
  refine ⟨c,hlegal.1 A hA hcA,hcL,?_⟩
  intro S hS
  by_cases he : S=A
  · exact he.symm ▸ hcA
  obtain ⟨y,hy⟩ := isAP_nonempty (hlegal.2 A hA S hS (Ne.symm he))
  obtain ⟨hyA,hyS⟩ := Finset.mem_inter.mp hy
  obtain ⟨p,hp⟩ := hstep S hS
  obtain ⟨q,hq⟩ := hstep A hA
  have hlowS : Low S≤c := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  have hcy : c≤y := hAc ▸ (low_spec (hne A hA)).2 y hyA
  have hcdiv : (d : ℤ)∣c-Low S := by
    have h1 := apAt_dvd_sub hp (low_spec (hne S hS)).1 hyS
    have h2 := apAt_dvd_sub hq hcA hyA
    have hh := Int.dvd_sub h1 h2
    convert hh using 1
    ring
  exact apAt_fill hp (low_spec (hne S hS)).1 hyS hlowS hcy hcdiv

theorem actual_same_step_two_rectangle {N d : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hd : 0<d) (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hroot : ∀ S∈F,c∈S) (htwo : ∀ S∈F,2≤S.card)
    (hstep : ∀ S∈F,∃ p : ℤ,APAt (d : ℤ) p S) :
    F.card≤((c-1).toNat/d)*(((N : ℤ)-c).toNat/d)+
      (c-1).toNat/d+((N : ℤ)-c).toNat/d := by
  have hnot : ({c} : Finset ℤ)∉F := by
    intro hmem
    have ht := htwo {c} hmem
    simp only [Finset.card_singleton] at ht
    omega
  let H := insert ({c} : Finset ℤ) F
  have hH : Legal (Ground N) H := legal_insert_common_singleton hc hlegal hroot
  have hHroot : ∀ S∈H,c∈S := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · simp
    · exact hroot S hS
  have hHstep : ∀ S∈H,∃ p : ℤ,APAt (d : ℤ) p S := by
    intro S hS
    rcases Finset.mem_insert.mp hS with rfl | hS
    · exact ⟨c,singleton_apAt hd c⟩
    · exact hstep S hS
  have hb := actual_same_step_rectangle hd hc hH hHroot hHstep
  have hcard : H.card=F.card+1 := by
    dsimp only [H]
    exact Finset.card_insert_of_notMem hnot
  rw [hcard] at hb
  nlinarith only [hb]

#print axioms actual_same_step_common_root_low
#print axioms actual_same_step_two_rectangle
end
end JSP233.LowAPRoot67702
