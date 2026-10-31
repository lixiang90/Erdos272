import Erdos272.Resources.RawEndpoint112

/-! Preserve the actual harmonic bound and the quarter in B(N). A preliminary
42w payment pays L-c and the constant error before the final width estimate.
The full original family and both actual extreme omitters stay explicit. -/
namespace JSP233.RawEndpoint113
open StarCompletion APGeometry DenseDeletion40 LongTerminal35
open HarmonicAbel29 HarmonicLog55 RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def CorePolynomial (x : ℝ) : ℝ :=
  x^3/6+11*x^2/2+(1961/125:ℝ)*x+32272599/62500

def RefinedPolynomial (x : ℝ) : ℝ := (114959/3359:ℝ)*CorePolynomial x

theorem original_quarter_card_lower {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1≤N) (hcard : B N≤F.card) : (N:ℝ)^2/2-(N:ℝ)/4≤F.card := by
  have hq : N≤4*((N-1)/4)+4 := by omega
  have hqR : (N:ℝ)≤4*(((N-1)/4:ℕ):ℝ)+4 := by exact_mod_cast hq
  have hb : (N.choose 2:ℝ)+1+(((N-1)/4:ℕ):ℝ)≤F.card := by
    exact_mod_cast hcard
  rw [Nat.cast_choose_two] at hb
  nlinarith only [hqR,hb]

theorem core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x+293/500)/2+4*(x+293/500)^2+
      6*(x+293/500)+5093/10=CorePolynomial x := by
  dsimp only [SimplexPolynomial,CorePolynomial]
  ring

theorem actual_retained11_width {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hNr : 3000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hthin : 42*(L+N-R)≤N) (hdelete : 10185≤N) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*RefinedPolynomial (Real.log N) := by
  have hr := actual_retained11_raw_half hdelete hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hb := original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast hNr
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
    ring
  have ht : (42:ℝ)*((L:ℝ)+(N-R))≤N := by
    have hh : (42:ℝ)*((L+N-R:ℕ):ℝ)≤N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by
      exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : DeficitCoeff*((L:ℝ)+(N-R))^2≤
      (N:ℝ)*(SimplexPolynomial (Real.log N) (Harmonic N)/2+
        4*(Harmonic N)^2+6*Harmonic N+5093/10) := by
    nlinarith only [hr,hb,ht,hd,hn]
  have hh := actual_harmonic_log_586 (N:=N) (by omega : 63≤N)
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+293/500)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+
      4*(Harmonic N)^2+6*Harmonic N+5093/10≤CorePolynomial (Real.log N) := by
    rw [←core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh,hhsq]
  have htotal := hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))
  dsimp only [DeficitCoeff] at htotal
  dsimp only [RefinedPolynomial]
  nlinarith only [htotal]

#print axioms original_quarter_card_lower
#print axioms core_harmonic_identity
#print axioms actual_retained11_width
end
end JSP233.RawEndpoint113
