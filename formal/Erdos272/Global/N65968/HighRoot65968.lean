module

public import Erdos272.Global.N158375.HighRoot158375
public import Erdos272.Arithmetic.N80470.Harmonic80470

@[expose] public section

namespace JSP233.HighRoot65968
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootQuadratic208 HighRoot158375
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_high_root {N : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 65968≤N) (hhi : N≤67701) (hF : Legal (Ground N) G)
    (hbad : ∀ S∈G, ¬IsAP S) (hsparse : ∀ S∈G, 12*S.card≤N)
    (hT : T∈Avoiders G c) (hsize : 555≤T.card)
    (hmin : ∀ S∈Avoiders G c, T.card≤S.card) :
    (G.card : ℝ)≤(7/80 : ℝ)*(N : ℝ)^2 := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega)
  have hH := (Harmonic80470.actual_cap (by omega : 10000≤N)
    (by omega : N≤82427)).trans (by norm_num : (4759/400 : ℝ)≤5107/400)
  have ht := hsparse T (Finset.mem_filter.mp hT).1
  suffices hwhole : (G.card : ℝ)/(N : ℝ)^2≤(7/80 : ℝ) from
    (div_le_iff₀ (sq_pos_of_pos hn)).mp hwhole
  by_cases h75 : 75*T.card≤N
  · exact normalized_stage (lo := 65968) (hi := 67701) (K := 185) (J := 4) (D := 75)
      (by omega) (by decide) hN hhi (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h75
      (by decide) (by norm_num [Q])
  by_cases h23 : 23*T.card≤N
  · exact normalized_stage (lo := 65968) (hi := 67701) (K := 293) (J := 3) (D := 23)
      (by omega) (by decide) hN hhi (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h23
      (by decide) (by norm_num [Q])
  by_cases h13 : 13*T.card≤N
  · exact normalized_stage (lo := 65968) (hi := 67701) (K := 956) (J := 2) (D := 13)
      (by omega) (by decide) hN hhi (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) h13
      (by decide) (by norm_num [Q])
  exact normalized_stage (lo := 65968) (hi := 67701) (K := 1691) (J := 1) (D := 12)
      (by omega) (by decide) hN hhi (by decide) (by decide) hH
      hF hbad hsparse hT hmin (by omega) ht
      (by decide) (by norm_num [Q])

#print axioms actual_high_root
end
end JSP233.HighRoot65968
