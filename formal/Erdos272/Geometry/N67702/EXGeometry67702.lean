module

public import Erdos272.Resources.ActualExterior208

@[expose] public section

namespace JSP233.EXGeometry67702
open StarCompletion APGeometry APCount41
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_four_step_bound {N : ℕ} {S : Finset ℤ}
    (hground : S⊆Ground N) (hAP : IsAP S) (hfour : 4≤S.card) :
    3*Step S≤N-1 := by
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  have hne := isAP_nonempty hAP
  have hI : S⊆Finset.Icc (1 : ℤ) (N : ℤ) := by
    intro x hx
    exact Finset.mem_Icc.mpr ((mem_ground N x).mp (hground hx))
  have hspan := apAt_card_span hp hne hI
  have hfourZ : (4 : ℤ)≤S.card := by exact_mod_cast hfour
  have hdZ : (0 : ℤ)≤Step S := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (show (3 : ℤ)≤(S.card : ℤ)-1 by omega) hdZ
  obtain ⟨x,hx⟩ := hne
  have hxN := (mem_ground N x).mp (hground hx)
  omega

theorem actual_four_step_maps {N : ℕ} {F : Finset (Finset ℤ)}
    (hground : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hfour : ∀ S∈F,4≤S.card) (hlarge : ∀ S∈F,2≤Step S) :
    Set.MapsTo Step (F : Set (Finset ℤ)) (Finset.Icc 2 ((N-1)/3)) := by
  intro S hS
  refine Finset.mem_Icc.mpr ⟨hlarge S hS,?_⟩
  have hh := actual_four_step_bound (hground S hS) (hAP S hS) (hfour S hS)
  apply (Nat.le_div_iff_mul_le (by decide : 0<3)).mpr
  nlinarith only [hh]

theorem actual_empty_three_gap {N L R d : ℕ} {S : Finset ℤ}
    (hground : S⊆Ground N) (hAP : IsAP S) (hstep : Step S=d)
    (hends : Low S≤(L : ℤ) ∧ (R : ℤ)≤High S)
    (hlo : N-1<4*d) (hgap : (3 : ℤ)*d<(R : ℤ)-L) : False := by
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  rw [hstep] at hd hp
  have hne := isAP_nonempty hAP
  have hI : S⊆Finset.Icc (1 : ℤ) (N : ℤ) := by
    intro x hx
    exact Finset.mem_Icc.mpr ((mem_ground N x).mp (hground hx))
  have hspan := apAt_card_span hp hne hI
  have hdZ : (0 : ℤ)<d := by exact_mod_cast hd
  have hne' := hne
  obtain ⟨x,hx⟩ := hne'
  have hxN := (mem_ground N x).mp (hground hx)
  have hlowZ : (N : ℤ)-1<4*(d : ℤ) := by omega
  have hcard : S.card≤4 := by
    by_contra hn
    have hc : (4 : ℤ)≤(S.card : ℤ)-1 := by omega
    have hm := mul_le_mul_of_nonneg_left hc hdZ.le
    nlinarith only [hspan,hlowZ,hm]
  have hcardZ : (S.card : ℤ)-1≤3 := by
    have hh : (S.card : ℤ)≤4 := by exact_mod_cast hcard
    omega
  have hm := mul_le_mul_of_nonneg_left hcardZ hdZ.le
  have he : High S-Low S=(d : ℤ)*((S.card : ℤ)-1) := by
    simpa only [High,Low,dif_pos hne] using apAt_span_eq hp hne
  omega

#print axioms actual_four_step_bound
#print axioms actual_four_step_maps
#print axioms actual_empty_three_gap
end
end JSP233.EXGeometry67702
