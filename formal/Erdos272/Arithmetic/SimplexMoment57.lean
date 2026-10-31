import Erdos272.Arithmetic.HarmonicLog55
import Erdos272.Resources.ResourceBudget56
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace JSP233.SimplexMoment57
open scoped Classical BigOperators
open MeasureTheory Set intervalIntegral
open DivisorMoment45 HarmonicAbel29 HarmonicLog55
open StarCompletion APGeometry RestrictedWitness44
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def LogKernel (X : ℝ) (k : ℕ) (t : ℝ) : ℝ := (Real.log X-Real.log t)^k/t

theorem log_kernel_antitone {X : ℝ} (_hX : 1≤X) (k : ℕ) :
    AntitoneOn (LogKernel X k) (Icc 1 X) := by
  intro x hx y hy hxy
  have hx0 : 0<x := by linarith only [hx.1]
  have hy0 : 0<y := by linarith only [hy.1]
  have hlogxy := Real.log_le_log hx0 hxy
  have hlogyX := Real.log_le_log hy0 hy.2
  have hlogxX := Real.log_le_log hx0 hx.2
  have h0 : 0≤Real.log X-Real.log y := sub_nonneg.mpr hlogyX
  have hp : (Real.log X-Real.log y)^k≤(Real.log X-Real.log x)^k := by gcongr
  dsimp only [LogKernel]
  calc
    _≤(Real.log X-Real.log x)^k/y := div_le_div_of_nonneg_right hp hy0.le
    _≤_ := div_le_div_of_nonneg_left (pow_nonneg (sub_nonneg.mpr hlogxX) _) hx0 hxy

theorem log_kernel_continuous {X : ℝ} (_hX : 1≤X) (k : ℕ) :
    ContinuousOn (LogKernel X k) (Icc 1 X) := by
  have hl : ContinuousOn Real.log (Icc 1 X) := Real.continuousOn_log.mono (by
    intro x hx
    change x∉({0}:Set ℝ)
    simp only [mem_singleton_iff]
    linarith only [hx.1])
  exact ((continuousOn_const.sub hl).pow k).div continuousOn_id (by intro x hx;linarith only [hx.1])

theorem log_kernel_integral {X : ℝ} (hX : 1≤X) (k : ℕ) :
    (∫ t in (1:ℝ)..X,LogKernel X k t)=(Real.log X)^(k+1)/(k+1) := by
  have hk : (k+1:ℝ)≠0 := by positivity
  have hder : ∀t∈uIcc (1:ℝ) X,
      HasDerivAt (fun t:ℝ=>-((Real.log X-Real.log t)^(k+1)/(k+1)))
        (LogKernel X k t) t := by
    intro t ht
    rw [uIcc_of_le hX] at ht
    have ht0 : t≠0 := by linarith only [ht.1]
    have hd := ((((Real.hasDerivAt_log ht0).const_sub (Real.log X)).pow (k+1)).div_const (k+1:ℝ)).neg
    convert hd using 1 <;> first | rfl | (simp only [LogKernel,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one];field_simp [ht0,hk])
  have hi : IntervalIntegrable (LogKernel X k) volume (1:ℝ) X :=
    (log_kernel_continuous hX k).intervalIntegrable_of_Icc hX
  have hh := integral_eq_sub_of_hasDerivAt hder hi
  simpa only [sub_self,zero_pow (Nat.succ_ne_zero k),zero_div,neg_zero,Real.log_one,
    sub_zero,zero_sub,neg_neg] using hh


theorem actual_log_kernel_sum {N : ℕ} (hN : 1≤N) (k : ℕ) :
    (∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) k a)≤
      (Real.log N)^k+(Real.log N)^(k+1)/(k+1) := by
  have hNR : (1:ℝ)≤N := by exact_mod_cast hN
  have haf : AntitoneOn (LogKernel (N:ℝ) k) (Icc ((1:ℕ):ℝ) (N:ℝ)) := by
    simpa only [Nat.cast_one] using log_kernel_antitone hNR k
  have hi := AntitoneOn.sum_le_integral_Ico hN haf
  have hshift : (∑a∈Finset.Ico 1 N,LogKernel (N:ℝ) k ((a+1:ℕ):ℝ))=
      ∑a∈Finset.Ico 2 (N+1),LogKernel (N:ℝ) k a := by
    simpa only [Nat.reduceAdd] using
      (Finset.sum_Ico_add' (fun a:ℕ=>LogKernel (N:ℝ) k a) 1 N 1)
  simp only [Nat.cast_one] at hi
  rw [hshift,log_kernel_integral hNR k] at hi
  have hfull : (∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) k a)=
      (Real.log N)^k+∑a∈Finset.Ico 2 (N+1),LogKernel (N:ℝ) k a := by
    rw [←Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1<N+1)]
    simp only [LogKernel,Nat.cast_one,Real.log_one,sub_zero,div_one]
  linarith only [hi,hfull]

def DivCount : ℕ→ℕ→ℕ
  | 0,N=>N
  | k+1,N=>∑a∈Finset.Icc 1 N,DivCount k (N/a)

def P1 (L:ℝ) : ℝ := 1+L
def P2 (L:ℝ) : ℝ := 1+2*L+L^2/2
def P3 (L:ℝ) : ℝ := 1+3*L+3*L^2/2+L^3/6

theorem div_count_zero (k : ℕ) : DivCount k 0=0 := by
  cases k <;> simp [DivCount]

theorem div_count_extend {n B : ℕ} (hnB : n≤B) (k : ℕ) :
    (∑a∈Finset.Icc 1 B,DivCount k (n/a))=DivCount (k+1) n := by
  rw [DivCount]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hnB)
  intro a ha han
  have hna : n<a := by
    have hh := Finset.mem_Icc.mp ha
    have hh' : ¬(1≤a ∧ a≤n) := by simpa only [Finset.mem_Icc] using han
    omega
  rw [Nat.div_eq_of_lt hna,div_count_zero]

theorem div_count_one_harmonic (N : ℕ) :
    (DivCount 1 N:ℝ)≤N*Harmonic N := by
  calc
    _=∑a∈Finset.Icc 1 N,((N/a:ℕ):ℝ) := by simp only [DivCount,Nat.cast_sum]
    _≤∑a∈Finset.Icc 1 N,(N:ℝ)/a := Finset.sum_le_sum (fun a _=>Nat.cast_div_le)
    _=N*Harmonic N := by simp only [Harmonic,div_eq_mul_inv,←Finset.mul_sum,one_mul]

theorem div_count_one_log {N : ℕ} (hN : 1≤N) :
    (DivCount 1 N:ℝ)≤N*P1 (Real.log N) := by
  have hh := actual_log_kernel_sum hN 0
  simp only [LogKernel,pow_zero,Nat.cast_zero,zero_add,pow_one,div_one] at hh
  have hbound : (Harmonic N)≤1+Real.log N := by
    simpa only [Harmonic] using hh
  exact (div_count_one_harmonic N).trans
    (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg N))


theorem actual_quotient_log_bounds {N a : ℕ} (ha : a∈Finset.Icc 1 N) :
    0<N/a ∧ ((N/a:ℕ):ℝ)≤(N:ℝ)/a ∧ 0≤Real.log ((N/a:ℕ):ℝ) ∧
      Real.log ((N/a:ℕ):ℝ)≤Real.log N-Real.log a ∧ 0≤Real.log N-Real.log a := by
  obtain ⟨ha0,haN⟩ := Finset.mem_Icc.mp ha
  have hn : 0<N/a := Nat.div_pos haN ha0
  have hcast : ((N/a:ℕ):ℝ)≤(N:ℝ)/a := Nat.cast_div_le
  have h0 : 0≤Real.log ((N/a:ℕ):ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hN0 : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have ha0R : (a:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hl : Real.log ((N/a:ℕ):ℝ)≤Real.log N-Real.log a := by
    rw [←Real.log_div hN0 ha0R]
    exact Real.log_le_log (Nat.cast_pos.mpr hn) hcast
  exact ⟨hn,hcast,h0,hl,h0.trans hl⟩

theorem div_count_two_log {N : ℕ} (hN : 1≤N) :
    (DivCount 2 N:ℝ)≤N*P2 (Real.log N) := by
  have hs0 := actual_log_kernel_sum hN 0
  have hs1 := actual_log_kernel_sum hN 1
  norm_num at hs0 hs1
  have heq : (DivCount 2 N:ℝ)=∑a∈Finset.Icc 1 N,(DivCount 1 (N/a):ℝ) := by
    simp only [DivCount,Nat.cast_sum]
  rw [heq]
  calc
    _≤∑a∈Finset.Icc 1 N,((N:ℝ)/a)*P1 (Real.log N-Real.log a) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hn,hcast,h0,hl,hL⟩ := actual_quotient_log_bounds ha
      have hp : P1 (Real.log ((N/a:ℕ):ℝ))≤P1 (Real.log N-Real.log a) := by
        dsimp only [P1];linarith only [hl]
      exact (div_count_one_log hn).trans (mul_le_mul hcast hp (by dsimp [P1];positivity) (by positivity))
    _=(N:ℝ)*((∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 0 a)+
        ∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 1 a) := by
      have hsum : (∑a∈Finset.Icc 1 N,((N:ℝ)/a)*P1 (Real.log N-Real.log a))=
          ∑a∈Finset.Icc 1 N,((N:ℝ)*LogKernel (N:ℝ) 0 a+N*LogKernel (N:ℝ) 1 a) := by
        apply Finset.sum_congr rfl;intro a _;dsimp only [P1,LogKernel];ring
      rw [hsum,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]
      ring
    _≤(N:ℝ)*((1+Real.log N)+(Real.log N+(Real.log N)^2/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add hs0 hs1) (Nat.cast_nonneg N)
    _=N*P2 (Real.log N) := by dsimp only [P2];ring

theorem div_count_three_log {N : ℕ} (hN : 1≤N) :
    (DivCount 3 N:ℝ)≤N*P3 (Real.log N) := by
  have hs0 := actual_log_kernel_sum hN 0
  have hs1 := actual_log_kernel_sum hN 1
  have hs2 := actual_log_kernel_sum hN 2
  norm_num at hs0 hs1 hs2
  have heq : (DivCount 3 N:ℝ)=∑a∈Finset.Icc 1 N,(DivCount 2 (N/a):ℝ) := by
    simp only [DivCount,Nat.cast_sum]
  rw [heq]
  calc
    _≤∑a∈Finset.Icc 1 N,((N:ℝ)/a)*P2 (Real.log N-Real.log a) := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hn,hcast,h0,hl,hL⟩ := actual_quotient_log_bounds ha
      have hp : P2 (Real.log ((N/a:ℕ):ℝ))≤P2 (Real.log N-Real.log a) := by
        dsimp only [P2];gcongr
      exact (div_count_two_log hn).trans (mul_le_mul hcast hp (by dsimp [P2];positivity) (by positivity))
    _=(N:ℝ)*((∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 0 a)+
        2*(∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 1 a)+
        (∑a∈Finset.Icc 1 N,LogKernel (N:ℝ) 2 a)/2) := by
      have hsum : (∑a∈Finset.Icc 1 N,((N:ℝ)/a)*P2 (Real.log N-Real.log a))=
          ∑a∈Finset.Icc 1 N,((N:ℝ)*LogKernel (N:ℝ) 0 a+
            (2*N)*LogKernel (N:ℝ) 1 a+(N/2)*LogKernel (N:ℝ) 2 a) := by
        apply Finset.sum_congr rfl;intro a _;dsimp only [P2,LogKernel];ring
      rw [hsum,Finset.sum_add_distrib,Finset.sum_add_distrib,
        ←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum]
      ring
    _≤(N:ℝ)*((1+Real.log N)+2*(Real.log N+(Real.log N)^2/2)+
        ((Real.log N)^2+(Real.log N)^3/3)/2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      exact add_le_add (add_le_add hs0 (mul_le_mul_of_nonneg_left hs1 (by norm_num)))
        (div_le_div_of_nonneg_right hs2 (by norm_num))
    _=N*P3 (Real.log N) := by dsimp only [P3];ring


theorem quad_pool_eq_div_count (N : ℕ) : (QuadPool N).card=DivCount 3 N := by
  calc
    _=∑g∈Finset.Icc 1 N,∑a∈Finset.Icc 1 N,∑b∈Finset.Icc 1 N,N/(g*a*b) := by
      simp only [QuadPool,Finset.card_sigma,Nat.card_Icc,Nat.add_sub_cancel]
    _=∑g∈Finset.Icc 1 N,∑a∈Finset.Icc 1 N,DivCount 1 (N/g/a) := by
      apply Finset.sum_congr rfl;intro g _
      apply Finset.sum_congr rfl;intro a _
      have hbound : N/g/a≤N := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
      simpa only [DivCount,Nat.div_div_eq_div_mul,Nat.mul_assoc] using div_count_extend hbound 0
    _=∑g∈Finset.Icc 1 N,DivCount 2 (N/g) := by
      apply Finset.sum_congr rfl;intro g _
      exact div_count_extend (Nat.div_le_self _ _) 1
    _=DivCount 3 N := rfl

theorem actual_divisor_second_moment_simplex {N : ℕ} (hN : 1≤N) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤(N:ℝ)*P3 (Real.log N) := by
  have hh : ((∑n∈Finset.Icc 1 N,n.divisors.card^2:ℕ):ℝ)≤(QuadPool N).card := by
    exact_mod_cast actual_second_moment_encoding N
  rw [quad_pool_eq_div_count] at hh
  simpa only [Nat.cast_sum,Nat.cast_pow] using hh.trans (div_count_three_log hN)

def DivisorPool (N : ℕ) : Finset (Σ _d:ℕ,ℕ) :=
  (Finset.Icc 1 N).sigma (fun d=>Finset.Icc 1 (N/d))

theorem actual_first_moment_encoding (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card)≤(DivisorPool N).card := by
  let U := (Finset.Icc 1 N).sigma (fun n=>n.divisors)
  let code : U→(Σ _d:ℕ,ℕ) := fun u=>⟨u.val.2,u.val.1/u.val.2⟩
  have hm : ∀u:U,code u∈DivisorPool N := by
    intro u
    obtain ⟨hn,hd⟩ := Finset.mem_sigma.mp u.property
    obtain ⟨hn0,hnN⟩ := Finset.mem_Icc.mp hn
    have hd0 := Nat.pos_of_mem_divisors hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hdle := Nat.le_of_dvd hn0 hdvd
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd0,hdle.trans hnN⟩,?_⟩
    exact Finset.mem_Icc.mpr ⟨Nat.div_pos hdle hd0,Nat.div_le_div_right hnN⟩
  let decode : (Σ _d:ℕ,ℕ)→(Σ _n:ℕ,ℕ) := fun z=>⟨z.1*z.2,z.1⟩
  have hrec : ∀u:U,decode (code u)=u.val := by
    intro u
    have hdvd := Nat.dvd_of_mem_divisors (Finset.mem_sigma.mp u.property).2
    dsimp only [decode,code]
    rw [Nat.mul_div_cancel' hdvd]
  have hi : Function.Injective code := by
    intro u v h
    apply Subtype.ext
    rw [←hrec u,←hrec v,h]
  have hc := Finset.card_le_card_of_injective (f:=fun u:U=>(⟨code u,hm u⟩:DivisorPool N))
    (by intro u v heq;exact hi (congrArg Subtype.val heq))
  simpa only [U,Finset.card_sigma] using hc

theorem divisor_pool_eq_div_count (N : ℕ) : (DivisorPool N).card=DivCount 1 N := by
  simp only [DivisorPool,Finset.card_sigma,Nat.card_Icc,Nat.add_sub_cancel,DivCount]

theorem actual_divisor_first_moment (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ))≤(N:ℝ)*Harmonic N := by
  have hh : ((∑n∈Finset.Icc 1 N,n.divisors.card:ℕ):ℝ)≤(DivisorPool N).card := by
    exact_mod_cast actual_first_moment_encoding N
  rw [divisor_pool_eq_div_count] at hh
  simpa only [Nat.cast_sum] using hh.trans (div_count_one_harmonic N)

theorem actual_exception_two_moments {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    WitnessException (Ground N) c≤2*(∑n∈Finset.Icc 1 N,n.divisors.card^2)+
      4*(∑n∈Finset.Icc 1 N,n.divisors.card) := by
  have hsecond := actual_distance_sum_twice hc (fun n=>n.divisors.card^2) (by simp)
  have hfirst := actual_distance_sum_twice hc (fun n=>n.divisors.card) (by simp)
  unfold WitnessException
  omega

theorem actual_simplex_exception {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤(N:ℝ)*SimplexPolynomial (Real.log N) (Harmonic N) := by
  have hN : 1≤N := by have hh:=(mem_ground N c).mp hc;omega
  have hh : (WitnessException (Ground N) c:ℝ)≤
      2*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+4*(∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)) := by
    exact_mod_cast actual_exception_two_moments hc
  have hm := actual_divisor_second_moment_simplex hN
  have hf := actual_divisor_first_moment N
  calc
    _≤2*((N:ℝ)*P3 (Real.log N))+4*((N:ℝ)*Harmonic N) := by linarith only [hh,hm,hf]
    _=(N:ℝ)*SimplexPolynomial (Real.log N) (Harmonic N) := by
      dsimp only [P3,SimplexPolynomial];ring

theorem actual_simplex_exception_refined {N hi J : ℕ} {c : ℤ}
    (hN : 63≤N) (hhi : N<hi) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*SimplexPolynomial (LogUpper J hi) (HarmonicUpper J hi) := by
  exact actual_conditional_simplex_exception hN hhi (actual_simplex_exception hc)

def SimplexTailPolynomial67 (J hi D : ℕ) : ℝ :=
  67*(SimplexPolynomial (LogUpper J hi) (HarmonicUpper J hi)+
    4*(HarmonicUpper J hi)^2+6*HarmonicUpper J hi+28+D+1)

theorem actual_original_simplex_endpoint67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+(DenseDeletion40.Deleted N 28 F).card+
        N*SimplexPolynomial (LogUpper J hi) (HarmonicUpper J hi)+
          4*N*(HarmonicUpper J hi)^2+6*N*HarmonicUpper J hi+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hraw⟩ :=
    ResourceBudget56.actual_original_prepared_endpoint67 hN hF hcounter
  have h63 : 63≤N := by norm_num at hN;omega
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by
    have hh:=Finset.mem_Icc.mp hc
    omega)
  have hW := actual_simplex_exception_refined (J:=J) h63 hhi hcG
  have hh := actual_refined_harmonic_upper (J:=J) h63 hhi
  have h0 := harmonic_nonneg N
  have herror : 4*(N:ℝ)*(Harmonic N)^2+6*N*Harmonic N≤
      4*N*(HarmonicUpper J hi)^2+6*N*HarmonicUpper J hi := by gcongr
  refine ⟨H,c,L,R,⟨hHF,hLH,hcard,hD,hG,hc,hLc,hLR,hRN,hroot,hP,hT,henv⟩,?_⟩
  linarith only [hraw,hW,herror]

theorem actual_original_simplex_tail67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (((L+N-R:ℕ):ℝ)^2≤SimplexTailPolynomial67 J hi 3137*N) := by
  obtain ⟨H,c,L,R,hcontext,hraw⟩ := actual_original_simplex_endpoint67 (J:=J) hN hhi hF hcounter
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hkeep := hcontext
  obtain ⟨_hHF,_hLH,_hcard,_hD,_hG,_hc,hcL,hLR,hRN,_hroot,_hP,_hT,_henv⟩ := hcontext
  have hD : (DenseDeletion40.Deleted N 28 F).card≤3137*N := by
    apply DenseSharper41.actual_deleted_sharp (by decide : 0<28) (by norm_num;norm_num at hN;omega) hF
  have hDR : ((DenseDeletion40.Deleted N 28 F).card:ℝ)≤3137*(N:ℝ) := by exact_mod_cast hD
  have hdiff : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter;omega
  have hchooseR : ((N.choose 2):ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hchooseR
  have ht : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-R := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
  refine ⟨H,c,L,R,hkeep,?_⟩
  dsimp only [SimplexTailPolynomial67]
  norm_num only [Nat.cast_ofNat]
  rw [ht]
  nlinarith only [hraw,hDR,hdiff,hchooseR,hn]

#print axioms log_kernel_antitone
#print axioms log_kernel_continuous
#print axioms log_kernel_integral
#print axioms actual_log_kernel_sum
#print axioms div_count_zero
#print axioms div_count_extend
#print axioms div_count_one_harmonic
#print axioms div_count_one_log
#print axioms actual_quotient_log_bounds
#print axioms div_count_two_log
#print axioms div_count_three_log
#print axioms quad_pool_eq_div_count
#print axioms actual_divisor_second_moment_simplex
#print axioms actual_first_moment_encoding
#print axioms divisor_pool_eq_div_count
#print axioms actual_divisor_first_moment
#print axioms actual_exception_two_moments
#print axioms actual_simplex_exception
#print axioms actual_simplex_exception_refined
#print axioms actual_original_simplex_endpoint67
#print axioms actual_original_simplex_tail67
end
end JSP233.SimplexMoment57
