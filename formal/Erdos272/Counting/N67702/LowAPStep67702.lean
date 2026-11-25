module

public import Erdos272.Counting.N67702.LowAPRoot67702

@[expose] public section

namespace JSP233.LowAPStep67702
open StarCompletion APGeometry APCount41 LowAPRoot67702
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_same_step_low {N L d : ℕ} {F : Finset (Finset ℤ)}
    (hL : 1≤L) (hhalf : 2*L≤N) (hd : 0<d)
    (hlegal : Legal (Ground N) F) (htwo : ∀ S∈F,2≤S.card)
    (hstep : ∀ S∈F,∃ p : ℤ,APAt (d : ℤ) p S)
    (hlow : ∀ S∈F,Low S≤(L : ℤ)) :
    (F.card : ℝ)≤((L : ℝ)-1)*((N : ℝ)-L)/(d : ℝ)^2+((N : ℝ)-1)/d := by
  have hN : 1≤N := by omega
  have hLN : (L : ℝ)≤N := by exact_mod_cast (show L≤N by omega)
  have hLR : (1 : ℝ)≤L := by exact_mod_cast hL
  have hNR : (1 : ℝ)≤N := by exact_mod_cast hN
  by_cases hF : F.Nonempty
  · have hne : ∀ S∈F,S.Nonempty := fun S hS =>
      Finset.card_pos.mp (by have hh:=htwo S hS;omega)
    obtain ⟨c,hc,hcL,hroot⟩ := actual_same_step_common_root_low hF hlegal hne hstep hlow
    let a := (c-1).toNat
    let b := ((N : ℤ)-c).toNat
    let U := a/d
    let V := b/d
    have hcN := (mem_ground N c).mp hc
    have ha : a≤L-1 := by dsimp only [a];omega
    have hab : a+b=N-1 := by dsimp only [a,b];omega
    have habR : (a : ℝ)+b=(N : ℝ)-1 := by
      have hh : ((a+b : ℕ) : ℝ)=((N-1 : ℕ) : ℝ) := by exact_mod_cast hab
      simpa only [Nat.cast_add,Nat.cast_sub hN,Nat.cast_one] using hh
    have haR : (a : ℝ)≤(L : ℝ)-1 := by
      have hh : (a : ℝ)≤((L-1 : ℕ) : ℝ) := by exact_mod_cast ha
      simpa only [Nat.cast_sub hL,Nat.cast_one] using hh
    have hhalfR : (2 : ℝ)*L≤N := by exact_mod_cast hhalf
    have hquad : (a : ℝ)*b≤((L : ℝ)-1)*((N : ℝ)-L) := by
      have hp := mul_nonneg (sub_nonneg.mpr haR)
        (show (0 : ℝ)≤(N : ℝ)-L-a by linarith only [haR,hhalfR])
      have he : ((L : ℝ)-1)*((N : ℝ)-L)-(a : ℝ)*b=
          ((L : ℝ)-1-a)*((N : ℝ)-L-a) := by
        rw [show (b : ℝ)=(N : ℝ)-1-a by linarith only [habR]]
        ring
      linarith only [hp,he]
    have hu : (U : ℝ)≤(a : ℝ)/d := Nat.cast_div_le
    have hv : (V : ℝ)≤(b : ℝ)/d := Nat.cast_div_le
    have hprod : (U : ℝ)*V≤(a : ℝ)*b/(d : ℝ)^2 := by
      have hh := mul_le_mul hu hv (by positivity) (by positivity)
      have he : ((a : ℝ)/d)*((b : ℝ)/d)=(a : ℝ)*b/(d : ℝ)^2 := by ring
      simpa only [he] using hh
    have hsum : (U : ℝ)+V≤((N : ℝ)-1)/d := by
      calc
        _≤(a : ℝ)/d+(b : ℝ)/d := add_le_add hu hv
        _=((N : ℝ)-1)/d := by rw [←add_div,habR]
    have hrect := actual_same_step_two_rectangle hd hc hlegal hroot htwo hstep
    have hrectR : (F.card : ℝ)≤(U : ℝ)*V+U+V := by exact_mod_cast hrect
    have hdiv := div_le_div_of_nonneg_right hquad (sq_nonneg (d : ℝ))
    linarith only [hrectR,hprod,hsum,hdiv]
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hF
    simp only [hz,Finset.card_empty,Nat.cast_zero]
    have hl0 : (0 : ℝ)≤(L : ℝ)-1 := sub_nonneg.mpr hLR
    have hn0 : (0 : ℝ)≤(N : ℝ)-1 := sub_nonneg.mpr hNR
    have hnl : (0 : ℝ)≤(N : ℝ)-L := sub_nonneg.mpr hLN
    positivity

#print axioms actual_same_step_low
end
end JSP233.LowAPStep67702
