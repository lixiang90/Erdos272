module

public import Erdos272.Global.N158375.HighRoot158375
public import Erdos272.Arithmetic.N94488.HarmonicCaps94488

@[expose] public section

namespace JSP233.HighRoot82427
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208 HighRoot158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 82427 ≤ N) (hhi : N ≤ 84363) (hF : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hsparse : ∀ S ∈ G, 12*S.card ≤ N)
    (hT : T ∈ Avoiders G c) (hsize : 555 ≤ T.card)
    (hmin : ∀ S ∈ Avoiders G c, T.card ≤ S.card) :
    (G.card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2 := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hH := HarmonicCaps94488.source_cap (by omega : N ≤ 179999)
  have ht := hsparse T (Finset.mem_filter.mp hT).1
  suffices hwhole : (G.card : ℝ)/(N : ℝ)^2 ≤ (7/80 : ℝ) from
    (div_le_iff₀ (sq_pos_of_pos hn)).mp hwhole
  by_cases h118 : 118*T.card ≤ N
  · exact normalized_stage (lo := 82427) (hi := 84363) (K := 185) (J := 4) (D := 118)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h118
      (by decide) (by norm_num [Q])
  by_cases h33 : 33*T.card ≤ N
  · exact normalized_stage (lo := 82427) (hi := 84363) (K := 232) (J := 4) (D := 33)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h33
      (by decide) (by norm_num [Q])
  by_cases h16 : 16*T.card ≤ N
  · exact normalized_stage (lo := 82427) (hi := 84363) (K := 832) (J := 2) (D := 16)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h16
      (by decide) (by norm_num [Q])
  exact normalized_stage (lo := 82427) (hi := 84363) (K := 1717) (J := 1) (D := 12)
      (by omega) (by decide) (by omega) (by omega) (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) ht
      (by decide) (by norm_num [Q])

#print axioms actual_high_root
end
end JSP233.HighRoot82427
