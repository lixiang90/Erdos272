module

public import Erdos272.Global.N158375.HighRoot158375
public import Erdos272.Arithmetic.N94488.HarmonicCaps94488

@[expose] public section

namespace JSP233.HighRoot80470
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208 HighRoot158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 80470 ≤ N) (hhi : N ≤ 82425) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 555 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hH := HarmonicCaps94488.source_cap (by omega : N ≤ 179999)
  have ht := hsparse T (Finset.mem_filter.mp hT).1
  suffices hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) from
    (div_le_iff₀ (sq_pos_of_pos hn)).mp hwhole
  by_cases h110 : 110*T.card ≤ N
  · exact normalized_stage (lo := 80470) (hi := 82425) (K := 185) (J := 5) (D := 110)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h110
      (by decide) (by norm_num [Q])
  by_cases h31 : 31*T.card ≤ N
  · exact normalized_stage (lo := 80470) (hi := 82425) (K := 240) (J := 4) (D := 31)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h31
      (by decide) (by norm_num [Q])
  by_cases h15 : 15*T.card ≤ N
  · exact normalized_stage (lo := 80470) (hi := 82425) (K := 858) (J := 2) (D := 15)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h15
      (by decide) (by norm_num [Q])
  exact normalized_stage (lo := 80470) (hi := 82425) (K := 1717) (J := 1) (D := 12)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) ht
      (by decide) (by norm_num [Q])

#print axioms actual_high_root
end
end JSP233.HighRoot80470
