module

public import Erdos272.Arithmetic.N291012.NearSparse291012
public import Erdos272.Global.RootQuadratic208
public import Erdos272.Resources.N158375.LocalRecovery158375

@[expose] public section

namespace JSP233.HighRoot158375
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem normalized_stage {N lo hi K J D : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 2 ≤ N) (hlo : 0 < lo) (hloN : lo ≤ N) (hhiN : N ≤ hi)
    (hK : 0 < K) (hD : 0 < D) (hH : Harmonic N ≤ (5107/400 : ℝ))
    (hF : Legal (Ground N) G) (hbad : ∀ S ∈ G, ¬IsAP S)
    (hsparse : ∀ S ∈ G, 12*S.card ≤ N) (hT : T ∈ Avoiders G c)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card)
    (hsize : 3*K ≤ T.card) (hscale : D*T.card ≤ N)
    (hdyadic : hi/12 < 3*K*2^J)
    (hprice : Q (1/(D : ℝ))+(2303/200 : ℝ)/K+
      2*(hi : ℝ)/((K : ℝ)*((5*K/3 : ℕ) : ℝ)^2)+
      (7/2 : ℝ)*J*((5107/400 : ℝ)/(lo : ℝ)) ≤ 7/80) :
    (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hl : (0 : ℝ) < lo := Nat.cast_pos.mpr hlo
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have hTF := (Finset.mem_filter.mp hT).1
  have hcT := (Finset.mem_filter.mp hT).2
  have ht := hsparse T hTF
  have hroot := actual_normalized_root hN hF hbad hTF hcT (by omega : T.card+1 ≤ N)
    (z := 1/(D : ℝ)) (by
      apply (div_le_div_iff₀ hn hd).mpr
      have hh : (D : ℝ)*(T.card : ℝ) ≤ N := by exact_mod_cast hscale
      nlinarith only [hh]) (by
        apply (div_le_one hd).mpr
        exact_mod_cast (show 1 ≤ D by omega))
  have hsub : Avoiders G c ⊆ G := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (Avoiders G c) :=
    ⟨fun S hS => hF.1 S (hsub hS), fun S hS U hU he => hF.2 S (hsub hS) U (hsub hU) he⟩
  have hnear := NearSparse291012.actual_family_normalized (K := K) (J := J) hlegal hK
    (by omega : 0 < N) (by
      intro S hS
      have hs := hsparse S (hsub hS)
      have hh : S.card ≤ hi/12 := (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mpr (by omega)
      exact hh.trans_lt hdyadic)
    (fun S hS => hbad S (hsub hS)) (fun S hS => hsize.trans (hmin S hS))
  have hwhole := actual_partition_payment hroot hnear
  have hhr : Harmonic N/(N : ℝ) ≤ (5107/400 : ℝ)/(lo : ℝ) := calc
    _ ≤ (5107/400 : ℝ)/(N : ℝ) := div_le_div_of_nonneg_right hH hn.le
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 5107/400) hl
      (by exact_mod_cast hloN)
  have hlinear := mul_le_mul_of_nonneg_left hhr (show (0 : ℝ) ≤ (7/2 : ℝ)*J by positivity)
  have hfar : 2*(N : ℝ)/((K : ℝ)*((5*K/3 : ℕ) : ℝ)^2) ≤
      2*(hi : ℝ)/((K : ℝ)*((5*K/3 : ℕ) : ℝ)^2) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hh : (N : ℝ) ≤ hi := by exact_mod_cast hhiN
    linarith only [hh]
  simp only [mul_div_assoc] at hwhole hfar hprice
  linarith only [hwhole, hfar, hlinear, hprice]

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 158375 ≤ N) (hhi : N ≤ 179999) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 555 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have caps := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hH : Harmonic N ≤ (5107/400 : ℝ) := caps.harmonic_le.trans
    (by norm_num [LocalRecovery158375.HLocal])
  have ht := hsparse T (Finset.mem_filter.mp hT).1
  suffices hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) from
    (div_le_iff₀ (sq_pos_of_pos hn)).mp hwhole
  by_cases hlow : N ≤ 170999
  · by_cases h240 : 240*T.card ≤ N
    · exact normalized_stage (lo := 150000) (hi := 170999) (K := 185) (J := 5) (D := 240)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h240
        (by decide) (by norm_num [Q])
    by_cases h60 : 60*T.card ≤ N
    · exact normalized_stage (lo := 150000) (hi := 170999) (K := 208) (J := 5) (D := 60)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h60
        (by decide) (by norm_num [Q])
    by_cases h20 : 20*T.card ≤ N
    · exact normalized_stage (lo := 150000) (hi := 170999) (K := 833) (J := 3) (D := 20)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h20
        (by decide) (by norm_num [Q])
    exact normalized_stage (lo := 150000) (hi := 170999) (K := 2500) (J := 1) (D := 12)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) ht
        (by decide) (by norm_num [Q])
  · by_cases h300 : 300*T.card ≤ N
    · exact normalized_stage (lo := 170000) (hi := 179999) (K := 185) (J := 5) (D := 300)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h300
        (by decide) (by norm_num [Q])
    by_cases h200 : 200*T.card ≤ N
    · exact normalized_stage (lo := 170000) (hi := 179999) (K := 189) (J := 5) (D := 200)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h200
        (by decide) (by norm_num [Q])
    by_cases h60 : 60*T.card ≤ N
    · exact normalized_stage (lo := 170000) (hi := 179999) (K := 283) (J := 5) (D := 60)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h60
        (by decide) (by norm_num [Q])
    by_cases h20 : 20*T.card ≤ N
    · exact normalized_stage (lo := 170000) (hi := 179999) (K := 944) (J := 3) (D := 20)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) h20
        (by decide) (by norm_num [Q])
    exact normalized_stage (lo := 170000) (hi := 179999) (K := 2833) (J := 1) (D := 12)
        (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
        hF hbad hsparse hT hmin (by omega) ht
        (by decide) (by norm_num [Q])

#print axioms normalized_stage
#print axioms actual_high_root
end
end JSP233.HighRoot158375
