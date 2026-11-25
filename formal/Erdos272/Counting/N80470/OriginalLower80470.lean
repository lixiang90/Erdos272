module

public import Erdos272.Global.N84364.CommonRoot84364

@[expose] public section

namespace JSP233.OriginalLower80470
open StarCompletion
set_option autoImplicit false

theorem original_quarter_lower {N : ℕ} {F : Finset (Finset ℤ)} (hcard : B N≤F.card) :
    (N : ℝ)^2/2-(N : ℝ)/4≤F.card := by
  have hmod := Nat.mod_lt (N-1) (by decide : 0<4)
  have hdiv := Nat.mod_add_div (N-1) 4
  have hf : N≤4*((N-1)/4)+4 := by omega
  have hfR : (N : ℝ)≤4*(((N-1)/4 : ℕ) : ℝ)+4 := by exact_mod_cast hf
  have hbNat : N.choose 2+1+(N-1)/4≤F.card := by simpa only [B] using hcard
  have hb : (N.choose 2 : ℝ)+1+(((N-1)/4 : ℕ) : ℝ)≤F.card := by
    exact_mod_cast hbNat
  rw [Nat.cast_choose_two] at hb
  nlinarith only [hfR,hb]

#print axioms original_quarter_lower
end JSP233.OriginalLower80470
