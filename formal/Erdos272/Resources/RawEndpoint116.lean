module

public import Erdos272.Resources.RawEndpoint115
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! A non-circular bootstrap after actual unit interval preparation.
At width32 the original p17 fringe counts all actual deleted avoiders.  Its
68 classes replace the485N deletion loss before any new Bad/Good/ratio gate.
No ordinary original-family startup is asserted in this local interface. -/
namespace JSP233.RawEndpoint116
open StarCompletion APGeometry DenseDeletion40 LongTerminal35 JointFringe44
open HarmonicAbel29 HarmonicLog55 RawEndpoint112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def BootstrapCorePolynomial (x : ℝ) : ℝ :=
  x^3/6+11*x^2/2+(1961/125:ℝ)*x+2091974/62500

def BootstrapPolynomial (x : ℝ) : ℝ :=
  (114959/3359:ℝ)*BootstrapCorePolynomial x

theorem joint_count17 : JointCount 17=68 := by
  norm_num [JointCount,ShortCount,Finset.sum_Icc_succ_top]

theorem actual_deleted_avoider_count68 {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 4913≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
    (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hne : (Avoiders (Retained N 11 F) (c:ℤ)).Nonempty)
    (hi : ∀S∈Avoiders (Retained N 11 F) (c:ℤ),∃a b:ℕ,
      c<a ∧ a≤L ∧ R≤b ∧ b≤N ∧ S=Interval (a,b))
    (hthin : 32*(L+N-R)≤N) :
    (TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)).card≤68*((L+N-R)-1) := by
  let E := TerminalDeficit51.OmittedAvoiders N 11 F (c:ℤ)
  have hGF : Retained N 11 F⊆F := Finset.sdiff_subset
  have hEF : E⊆F := (Finset.filter_subset _ _).trans (actual_deleted_subset N 11 F)
  have hbad : ∀S∈E,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1
  have hdense : ∀S∈E,N<11*S.card := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2
  have hcG := (mem_ground N (c:ℤ)).mp hc
  have hb := TerminalDeficit51.actual_interval_fringe_count 11 17 N c L R F (Retained N 11 F) E
    (by decide) (by decide) (by decide) (by norm_num;exact hN)
    (by omega) hcL hLR hRN (by omega) hGF hEF hF hbad hdense hne hi
  rw [joint_count17] at hb
  exact hb

theorem bootstrap_core_harmonic_identity (x : ℝ) :
    SimplexPolynomial x (x+293/500)/2+4*(x+293/500)^2+
      6*(x+293/500)+2641/100=BootstrapCorePolynomial x := by
  dsimp only [SimplexPolynomial,BootstrapCorePolynomial]
  ring

theorem actual_readded11_bootstrap_profile_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 4913≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
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
  have hcount := actual_deleted_avoider_count68 hN hc hF hcL hLR hRN hne hi hthin
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
  have hh := actual_harmonic_log_586 (N:=N) (by omega : 63≤N)
  have hh0 := harmonic_nonneg N
  have hl0 : 0≤Real.log (N:ℝ) := Real.log_nonneg (by linarith only [hn])
  have hhsq : (Harmonic N)^2≤(Real.log (N:ℝ)+293/500)^2 := by gcongr
  have hp : SimplexPolynomial (Real.log N) (Harmonic N)/2+4*(Harmonic N)^2+
      6*Harmonic N+2641/100≤BootstrapCorePolynomial (Real.log N) := by
    rw [←bootstrap_core_harmonic_identity]
    dsimp only [SimplexPolynomial]
    nlinarith only [hh,hhsq]
  exact hcost.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg N))

theorem actual_readded11_bootstrap_width {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (hN : 4913≤N) (hc : (c:ℤ)∈Ground N) (hF : Legal (Ground N) F)
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

#print axioms joint_count17
#print axioms actual_deleted_avoider_count68
#print axioms bootstrap_core_harmonic_identity
#print axioms actual_readded11_bootstrap_profile_width
#print axioms actual_readded11_bootstrap_width
end
end JSP233.RawEndpoint116
