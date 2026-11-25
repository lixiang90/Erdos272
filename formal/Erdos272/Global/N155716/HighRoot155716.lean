module

public import Erdos272.Global.N158375.HighRoot158375

@[expose] public section

namespace JSP233.HighRoot155716
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208 HighRoot158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 155716 ≤ N) (hhi : N ≤ 179999) (hF : Legal (Ground N) G)
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

#print axioms actual_high_root
end
end JSP233.HighRoot155716
