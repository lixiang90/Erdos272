import Erdos272.Resources.RawEndpoint127

/-! The complete2+3 witness bound is paid before intervals and thin width.
The same original family's full485N deletion remains explicit. The absolute
tangent fee is retained, rather than absorbed into a coefficient of N. -/
namespace JSP233.CoarseEndpoint127
open StarCompletion APGeometry DenseDeletion40 DenseSharper41
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115 RawEndpoint127
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def CoarseCorePolynomial (x : ℝ) : ℝ :=
  BootstrapCorePolynomial x+9677/20

def CoarsePolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*CoarseCorePolynomial x

theorem actual_retained11_profile {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    ProfileDeficit L (N-R)≤(N:ℝ)*CoarseCorePolynomial (Real.log N)+WitnessSingle127.FullFee := by
  have hr := RawEndpoint127.actual_prepared_family_raw_profile (by omega : 16≤N)
    hc (actual_retained_legal hF) hcL hLR hRN hroot hP hcP hLP hT hcT hTR houtside
  have hd := actual_retained_sharp_lower (r:=11) (by decide : 0<11)
    (by norm_num;omega) hF
  have hdR : (F.card:ℝ)≤(Retained N 11 F).card+485*(N:ℝ) := by exact_mod_cast hd
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (100000:ℝ)≤N := by exact_mod_cast hN
  have hL : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hcost : ProfileDeficit L (N-R)≤(N:ℝ)*
      ((DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*(Real.log N)^2+
        (61/25)*Real.log N+(89/10)*Harmonic N+5137/10)+WitnessSingle127.FullFee := by
    nlinarith only [hr,hdR,hb,hn,hL]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hp : (DivisorMoment122.Q3 (Real.log N)+2*Harmonic N-53107/200)+2*(Real.log N)^2+
      (61/25)*Real.log N+(89/10)*Harmonic N+5137/10≤CoarseCorePolynomial (Real.log N) := by
    dsimp only [CoarseCorePolynomial]
    rw [←bootstrap_core_harmonic_identity]
    dsimp only [DivisorMoment122.Q3]
    nlinarith only [hh]
  have hm := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N)
  linarith only [hcost,hm]

theorem actual_retained11_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*CoarsePolynomial (Real.log N)+
      (114959/3359:ℝ)*WitnessSingle127.FullFee := by
  have hp := actual_retained11_profile hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have he := profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [CoarsePolynomial]
  nlinarith only [hp,he,hs]

#print axioms actual_retained11_profile
#print axioms actual_retained11_width
end
end JSP233.CoarseEndpoint127
