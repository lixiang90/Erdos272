module

public import Erdos272.Arithmetic.N291012.NearSparse291012
public import Erdos272.Global.RootQuadratic208
public import Erdos272.Arithmetic.RecoveryCaps213

@[expose] public section

namespace JSP233.HighRoot9003045
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RecoveryCaps213 RootQuadratic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 225000 ≤ N) (hhi : N ≤ 291011) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 900 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn : (225000 : ℝ) ≤ N := by exact_mod_cast hN
  have hnr : (N : ℝ) ≤ 291011 := by exact_mod_cast hhi
  have hTF := (Finset.mem_filter.mp hT).1
  have hcT := (Finset.mem_filter.mp hT).2
  have ht := hsparse T hTF
  have hts : T.card+1 ≤ N := by omega
  have caps := actual_caps (by omega : 100000 ≤ N) (by omega : N ≤ 656184)
  have hH : Harmonic N ≤ 14 := caps.harmonic_le.trans (by norm_num [HCap, LogCap])
  have hhr : Harmonic N/(N : ℝ) ≤ (14/225000 : ℝ) := calc
    _ ≤ 14/(N : ℝ) := div_le_div_of_nonneg_right hH hNp.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 14) (by norm_num) hn
  have hsub : Avoiders G c ⊆ G := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (Avoiders G c) :=
    ⟨fun S hS => hF.1 S (hsub hS), fun S hS U hU he => hF.2 S (hsub hS) U (hsub hU) he⟩
  have hmax : ∀ S ∈ Avoiders G c, S.card < 25000 := by
    intro S hS
    have hh := hsparse S (hsub hS)
    omega
  have hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) := by
    by_cases hs : 32*T.card ≤ N
    · have hr := actual_normalized_root (by omega : 2 ≤ N) hF hbad hTF hcT hts
        (z := (1/32 : ℝ)) (by
          apply (div_le_iff₀ hNp).mpr
          have hh : 32*(T.card : ℝ) ≤ N := by exact_mod_cast hs
          linarith only [hh]) (by norm_num)
      have ha := NearSparse291012.actual_family_normalized (K := 300) (J := 5) hlegal
        (by decide) (by omega : 0 < N) (by intro S hS; have hh := hmax S hS; norm_num; omega)
        (fun S hS => hbad S (hsub hS)) (by intro S hS; have hh := hmin S hS; omega)
      norm_num at hr ha
      have hp := actual_partition_payment hr ha
      norm_num [Q] at hp
      simp only [mul_div_assoc] at hp
      nlinarith only [hp, hnr, hhr]
    · have hr := actual_normalized_root (by omega : 2 ≤ N) hF hbad hTF hcT hts
        (z := (1/12 : ℝ)) (by
          apply (div_le_iff₀ hNp).mpr
          have hh : 12*(T.card : ℝ) ≤ N := by exact_mod_cast ht
          linarith only [hh]) (by norm_num)
      have ha := NearSparse291012.actual_family_normalized (K := 2343) (J := 2) hlegal
        (by decide) (by omega : 0 < N) (by intro S hS; have hh := hmax S hS; norm_num; omega)
        (fun S hS => hbad S (hsub hS)) (by intro S hS; have hh := hmin S hS; omega)
      norm_num at hr ha
      have hp := actual_partition_payment hr ha
      norm_num [Q] at hp
      simp only [mul_div_assoc] at hp
      nlinarith only [hp, hnr, hhr]
  exact (div_le_iff₀ (sq_pos_of_pos hNp)).mp hwhole

#print axioms actual_high_root
end
end JSP233.HighRoot9003045
