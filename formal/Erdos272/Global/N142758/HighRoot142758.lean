module

public import Erdos272.Global.N150465.HighRoot150465

@[expose] public section

namespace JSP233.HighRoot142758
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208 HighRoot158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 130000 ≤ N) (hhi : N ≤ 179999) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 555 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  by_cases hlarge : 150000 ≤ N
  · exact HighRoot150465.actual_high_root hlarge hhi hF hbad hsparse hT hsize hmin
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have caps := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hH : Harmonic N ≤ (5107/400 : ℝ) := caps.harmonic_le.trans
    (by norm_num [LocalRecovery158375.HLocal])
  have ht := hsparse T (Finset.mem_filter.mp hT).1
  suffices hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) from
    (div_le_iff₀ (sq_pos_of_pos hn)).mp hwhole
  by_cases h200 : 200*T.card ≤ N
  · exact normalized_stage (lo := 130000) (hi := 150464) (K := 185) (J := 5) (D := 200)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h200
      (by decide) (by norm_num [Q])
  by_cases h50 : 50*T.card ≤ N
  · exact normalized_stage (lo := 130000) (hi := 150464) (K := 216) (J := 5) (D := 50)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h50
      (by decide) (by norm_num [Q])
  by_cases h20 : 20*T.card ≤ N
  · exact normalized_stage (lo := 130000) (hi := 150464) (K := 833) (J := 3) (D := 20)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h20
      (by decide) (by norm_num [Q])
  exact normalized_stage (lo := 130000) (hi := 150464) (K := 2167) (J := 1) (D := 12)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) ht
      (by decide) (by norm_num [Q])

#print axioms actual_high_root
end
end JSP233.HighRoot142758
