module

public import Erdos272.Resources.RawEndpoint116
public import Erdos272.Arithmetic.HarmonicCorrect118

@[expose] public section

/-! The independent actual bootstrap retains its original 68-class fringe
and width32 preparation. The finite corrected harmonic sequence sharpens
only the error polynomial; no final restoration count is used to pay its
own profile, and the original-family inputs remain explicit. -/
namespace JSP233.RawEndpoint118
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 JointFringe44
open HarmonicAbel29 HarmonicLog55 RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def BootstrapCorePolynomial (x : ℝ) : ℝ :=
  x^3/6+11*x^2/2+(781/50:ℝ)*x+1334561/40000

def BootstrapPolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*BootstrapCorePolynomial x

theorem bootstrap_core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x+231/400)/2+4*(x+231/400)^2+
      6*(x+231/400)+2641/100=BootstrapCorePolynomial x := by
  dsimp only [SimplexPolynomial,BootstrapCorePolynomial]
  ring

theorem actual_readded11_bootstrap_profile_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N) :
    RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*BootstrapCorePolynomial (Real.log N) := by
  have hr := RawEndpoint115.actual_readded11_raw_profile hc hF hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside
  have hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty :=
    ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩⟩
  have hcount := RawEndpoint116.actual_deleted_avoider_count68 (by omega : 4913≤N) hc hF hcL hLR hRN hne hi hthin
  have hcount' := hcount.trans (Nat.mul_le_mul_left 68 (Nat.sub_le (L+N-R) 1))
  have hcountR : ((TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card:ℝ)≤
      68*((L+N-R:ℕ):ℝ) := by exact_mod_cast hcount'
  have hb := RawEndpoint113.original_quarter_card_lower (by omega : 1≤N) hcard
  have hn : (3000:ℝ)≤N := by exact_mod_cast (show 3000≤N by omega)
  have he : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N-R) := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add];ring
  rw [he] at hcountR
  have ht : (32:ℝ)*((L:ℝ)+(N-R))≤N := by
    have hh : (32:ℝ)*((L+N-R:ℕ):ℝ)≤N := by exact_mod_cast hthin
    rwa [he] at hh
  have hd : ((L-c:ℕ):ℝ)≤(L:ℝ)+(N-R) := by
    have hh : ((L-c:ℕ):ℝ)≤((L+N-R:ℕ):ℝ) := by exact_mod_cast (by omega : L-c≤L+N-R)
    rwa [he] at hh
  have hcost : RawEndpoint115.ProfileDeficit L (N-R)≤(N:ℝ)*
      (SimplexPolynomial (Real.log N) (Harmonic N)/2+4*(Harmonic N)^2+
        6*Harmonic N+2641/100) := by
    nlinarith only [hr,hb,hcountR,ht,hd,hn]
  have hh := HarmonicCorrect118.actual_harmonic_log_5775 hN
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+231/400)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+4*(Harmonic N)^2+
      6*Harmonic N+2641/100≤BootstrapCorePolynomial (Real.log N) := by
    rw [←bootstrap_core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh,hhsq]
  exact hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))

theorem actual_readded11_bootstrap_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 100000≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcard : B N≤F.card) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈Retained N 11 F,¬IsAP S→(c:ℤ)∈S)
    (hP : P∈Retained N 11 F) (hcP : (c:ℤ)∉P) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hT : T∈Retained N 11 F) (hcT : (c:ℤ)∉T) (hTR : ∀z∈T,z≤(R:ℤ))
    (houtside : ∀S∈Retained N 11 F,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N) :
    ((L:ℝ)+(N-R))^2≤(N:ℝ)*BootstrapPolynomial (Real.log N) := by
  have hp := actual_readded11_bootstrap_profile_width hN hc hF hcard hcL hLR hRN hroot
    hP hcP hLP hT hcT hTR houtside hi hthin
  have he := RawEndpoint115.profile_square_identity (L:ℝ) ((N:ℝ)-R)
  have hs := sq_nonneg (329*((N:ℝ)-R)-(49159/200:ℝ)*L)
  dsimp only [DeficitCoeff] at he
  dsimp only [BootstrapPolynomial]
  nlinarith only [hp,he,hs]

theorem bootstrap_core_improves {x : ℝ} (hx : 0≤x) :
    BootstrapCorePolynomial x≤RawEndpoint116.BootstrapCorePolynomial x := by
  dsimp only [BootstrapCorePolynomial,RawEndpoint116.BootstrapCorePolynomial]
  linarith only [hx]

#print axioms bootstrap_core_harmonic_identity
#print axioms actual_readded11_bootstrap_profile_width
#print axioms actual_readded11_bootstrap_width
#print axioms bootstrap_core_improves
end
end JSP233.RawEndpoint118
