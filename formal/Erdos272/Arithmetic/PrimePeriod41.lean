import Erdos272.Global.StartupSeeds40

/-! Unbounded actual prime-factor and totient supplies from the thirty native seeds.
The period is thirty binary exponents. No prime-count or ordering premise is exported. -/
namespace JSP233.PrimePeriod41
open PrimorialRatio39 StartupSeeds40
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def Rho : ℝ := (32/31:ℝ)^6
def DistanceOmega (i : Fin 30) (t : ℕ) : ℕ := (Seeds i).w+6*t
def ProductOmega (i : Fin 30) (t : ℕ) : ℕ := (Seeds i).v+10*t
def PeriodRatio (i : Fin 30) (t : ℕ) : ℝ := (Seeds i).ratio*Rho^t
def PeriodBlock (i : Fin 30) (t N : ℕ) : Prop :=
  2^(49+i.val+30*t)≤N ∧ N<2^(50+i.val+30*t)

theorem prime_at_mono : Monotone PrimeAt := Nat.nth_monotone Nat.infinite_setOf_prime

theorem primorial_growth (a n L : ℕ) (hL : L≤PrimeAt a) :
    L^n*Primorial a≤Primorial (a+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := hL.trans (prime_at_mono (Nat.le_add_right a n))
    calc
      L^(n+1)*Primorial a=L*(L^n*Primorial a) := by ring
      _≤PrimeAt (a+n)*Primorial (a+n) := Nat.mul_le_mul hp ih
      _=Primorial (a+(n+1)) := by
        simp only [Primorial,show a+(n+1)=a+n+1 by omega,Finset.prod_range_succ]
        ring

theorem ratio_growth (a n L : ℕ) (hL : 2≤L) (ha : L≤PrimeAt a) :
    Ratio (a+n)≤Ratio a*((L:ℝ)/((L:ℝ)-1))^n := by
  have hL0 : (0:ℝ)≤(L:ℝ)/((L:ℝ)-1) := by
    have hh : (2:ℝ)≤L := by exact_mod_cast hL
    exact div_nonneg (by positivity) (by linarith)
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := real_ratio_antitone hL (ha.trans (prime_at_mono (Nat.le_add_right a n)))
    have hp0 : 0≤(PrimeAt (a+n):ℝ)/((PrimeAt (a+n):ℝ)-1) := by
      have hh : (2:ℝ)≤PrimeAt (a+n) := by exact_mod_cast (prime_at_prime (a+n)).two_le
      exact div_nonneg (by positivity) (by linarith)
    have hh := mul_le_mul ih hp hp0
      (mul_nonneg (ratio_nonneg a) (pow_nonneg hL0 n))
    calc
      Ratio (a+(n+1))=Ratio (a+n)*((PrimeAt (a+n):ℝ)/((PrimeAt (a+n):ℝ)-1)) := by
        simp only [Ratio,show a+(n+1)=a+n+1 by omega,Finset.prod_range_succ]
      _≤(Ratio a*((L:ℝ)/((L:ℝ)-1))^n)*((L:ℝ)/((L:ℝ)-1)) := hh
      _=Ratio a*((L:ℝ)/((L:ℝ)-1))^(n+1) := by ring

theorem rho_bounds : 0≤Rho ∧ Rho<2 := by norm_num [Rho]

theorem seed_prime_thresholds (i : Fin 30) :
    32≤PrimeAt (Seeds i).w ∧ 64≤PrimeAt ((Seeds i).v+1) := by
  have hh : 13≤(Seeds i).w ∧ 21≤(Seeds i).v := by fin_cases i <;> norm_num [Seeds]
  have h32 : 32≤PrimeAt 13 := by norm_num [prime_at_seed32_nat,Prime32]
  have h64 : 64≤PrimeAt 22 := by norm_num [prime_at_seed32_nat,Prime32]
  exact ⟨h32.trans (prime_at_mono hh.1),h64.trans (prime_at_mono (by omega))⟩

theorem power32_period (t : ℕ) : (32:ℕ)^(6*t)=2^(30*t) := by
  calc
    (32:ℕ)^(6*t)=(2^5)^(6*t) := by norm_num
    _=2^(5*(6*t)) := (pow_mul 2 5 (6*t)).symm
    _=2^(30*t) := by congr 1; omega

theorem power64_period (t : ℕ) : (64:ℕ)^(10*t)=2^(60*t) := by
  calc
    (64:ℕ)^(10*t)=(2^6)^(10*t) := by norm_num
    _=2^(6*(10*t)) := (pow_mul 2 6 (10*t)).symm
    _=2^(60*t) := by congr 1; omega

theorem period_distance_primorial (i : Fin 30) (t : ℕ) :
    2^(50+i.val+30*t)≤Primorial (DistanceOmega i t+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,hP,_,_,_,_⟩ := seed_checks i
  have hp := (seed_prime_thresholds i).1.trans (prime_at_mono (Nat.le_succ _))
  have hg := primorial_growth ((Seeds i).w+1) (6*t) 32 hp
  rw [power32_period] at hg
  calc
    2^(50+i.val+30*t)=2^(30*t)*2^(50+i.val) := by
      rw [←pow_add]; congr 1; omega
    _≤2^(30*t)*Primorial ((Seeds i).w+1) := Nat.mul_le_mul_left _ hP
    _≤Primorial (DistanceOmega i t+1) := by
      have he : (Seeds i).w+1+6*t=DistanceOmega i t+1 := by dsimp [DistanceOmega]; omega
      simpa only [he] using hg

theorem period_product_primorial (i : Fin 30) (t : ℕ) :
    2^(2*(50+i.val+30*t))≤Primorial (ProductOmega i t+1) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hP,_,_,_⟩ := seed_checks i
  have hg := primorial_growth ((Seeds i).v+1) (10*t) 64 (seed_prime_thresholds i).2
  rw [power64_period] at hg
  calc
    2^(2*(50+i.val+30*t))=2^(60*t)*2^(2*(50+i.val)) := by
      rw [←pow_add]; congr 1; omega
    _≤2^(60*t)*Primorial ((Seeds i).v+1) := Nat.mul_le_mul_left _ hP
    _≤Primorial (ProductOmega i t+1) := by
      have he : (Seeds i).v+1+10*t=ProductOmega i t+1 := by dsimp [ProductOmega]; omega
      simpa only [he] using hg

theorem period_ratio_bound (i : Fin 30) (t : ℕ) :
    Ratio (DistanceOmega i t)≤PeriodRatio i t := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,hR,_,_⟩ := seed_checks i
  have hg := ratio_growth (Seeds i).w (6*t) 32 (by decide) (seed_prime_thresholds i).1
  rw [hR] at hg
  norm_num only [Nat.cast_ofNat,show (32:ℝ)-1=31 by norm_num] at hg
  simpa only [DistanceOmega,PeriodRatio,Rho,pow_mul] using hg

theorem period_ratio_nonneg (i : Fin 30) (t : ℕ) : 0≤PeriodRatio i t := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hR0,_⟩ := seed_checks i
  exact mul_nonneg hR0 (pow_nonneg rho_bounds.1 t)

theorem uniform_period_arithmetic (i : Fin 30) (t N : ℕ)
    (hN : N<2^(50+i.val+30*t)) :
    (∀ m≤N,m.primeFactors.card≤DistanceOmega i t) ∧
    (∀ m≤N,(m:ℝ)≤PeriodRatio i t*Nat.totient m) ∧
    (∀ m≤N^2,m.primeFactors.card≤ProductOmega i t) := by
  obtain ⟨hw,hr⟩ := uniform_omega_and_ratio N (DistanceOmega i t)
    (hN.trans_le (period_distance_primorial i t))
  have hsquare : N^2<2^(2*(50+i.val+30*t)) := by
    have hh := Nat.mul_self_lt_mul_self hN
    have he : 2^(50+i.val+30*t)*2^(50+i.val+30*t)=2^(2*(50+i.val+30*t)) := by
      rw [←pow_add]; congr 1; omega
    simpa only [pow_two,he] using hh
  have hp := (uniform_omega_and_ratio (N^2) (ProductOmega i t)
    (hsquare.trans_le (period_product_primorial i t))).1
  refine ⟨hw,?_,hp⟩
  intro m hm
  exact (hr m hm).trans (mul_le_mul_of_nonneg_right (period_ratio_bound i t)
    (show (0:ℝ)≤Nat.totient m by positivity))

theorem exists_period_block (N : ℕ) (hN : 2^49≤N) :
    ∃ i : Fin 30,∃ t : ℕ,PeriodBlock i t N := by
  have hNz : N≠0 := by norm_num at hN; omega
  have hq : 49≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide) hNz).mpr hN
  let d := Nat.log 2 N-49
  let i : Fin 30 := ⟨d%30,Nat.mod_lt d (by decide)⟩
  let t := d/30
  have he : 49+i.val+30*t=Nat.log 2 N := by
    have hh := Nat.mod_add_div d 30
    dsimp [i,t,d] at *
    omega
  refine ⟨i,t,?_,?_⟩
  · rw [he]
    exact Nat.pow_log_le_self 2 hNz
  · have he' : 50+i.val+30*t=Nat.log 2 N+1 := by omega
    rw [he']
    exact Nat.lt_pow_succ_log_self (by decide) N

theorem automatic_uniform_arithmetic (N : ℕ) (hN : 2^49≤N) :
    ∃ i : Fin 30,∃ t : ℕ,PeriodBlock i t N ∧
      (∀ m≤N,m.primeFactors.card≤DistanceOmega i t) ∧
      (∀ m≤N,(m:ℝ)≤PeriodRatio i t*Nat.totient m) ∧
      (∀ m≤N^2,m.primeFactors.card≤ProductOmega i t) := by
  obtain ⟨i,t,hblock⟩ := exists_period_block N hN
  exact ⟨i,t,hblock,uniform_period_arithmetic i t N hblock.2⟩

theorem period_long_gate_scaled (i : Fin 30) (t : ℕ) :
    2*PeriodRatio i t*(2^DistanceOmega i t:ℕ)≤(128:ℝ)^t*(Seeds i).kl := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hgate⟩ := seed_checks i
  have h128 : Rho*64≤(128:ℝ) := by have hh:=rho_bounds.2; linarith
  have hp : (Rho*64)^t≤(128:ℝ)^t :=
    pow_le_pow_left₀ (mul_nonneg rho_bounds.1 (by norm_num)) h128 t
  have htwo : (2:ℝ)^(6*t)=(64:ℝ)^t := by rw [pow_mul]; norm_num
  calc
    2*PeriodRatio i t*(2^DistanceOmega i t:ℕ)=
        (2*(Seeds i).ratio*(2^(Seeds i).w:ℕ))*(Rho*64)^t := by
      dsimp only [PeriodRatio,DistanceOmega]
      push_cast
      rw [pow_add,htwo,mul_pow]
      ring
    _≤((Seeds i).kl:ℝ)*(128:ℝ)^t := mul_le_mul hgate hp
      (pow_nonneg (mul_nonneg rho_bounds.1 (by norm_num)) t) (by positivity)
    _=(128:ℝ)^t*(Seeds i).kl := by ring

theorem period_cutoff_lower (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) :
    (32768:ℕ)^t*(Seeds i).kl≤Startup49.Cutoff N := by
  obtain ⟨_,_,_,_,_,_,_,_,hlo,_,_,_,_,_,_⟩ := seed_checks i
  have hsquare : ((32768:ℕ)^t)^2=2^(30*t) := by
    rw [←pow_mul,show (32768:ℕ)=2^15 by norm_num,←pow_mul]
    congr 1
    omega
  have hs : (((32768:ℕ)^t*(Seeds i).kl)*128)^2≤N := by
    calc
      _=2^(30*t)*((Seeds i).kl*128)^2 := by rw [mul_assoc,mul_pow,hsquare]
      _≤2^(30*t)*2^(49+i.val) := Nat.mul_le_mul_left _ hlo
      _=2^(49+i.val+30*t) := by rw [←pow_add]; congr 1; omega
      _≤N := hblock.1
  have hh := Nat.le_sqrt'.mpr hs
  exact (Nat.le_div_iff_mul_le (by decide : 0<128)).mpr hh

theorem period_cutoff_upper (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) :
    Startup49.Cutoff N≤2^((Seeds i).ell+15*t) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hup,_,_,_,_,_⟩ := seed_checks i
  have hsquare : ((2:ℕ)^(15*t))^2=2^(30*t) := by
    rw [←pow_mul]
    congr 1
    omega
  have he : (128*2^((Seeds i).ell+15*t))^2=2^(30*t)*(128*2^(Seeds i).ell)^2 := by
    rw [pow_add,←mul_assoc,mul_pow,hsquare]
    ring
  have hN : N≤(128*2^((Seeds i).ell+15*t))^2 := by
    calc
      N≤2^(50+i.val+30*t) := hblock.2.le
      _=2^(30*t)*2^(50+i.val) := by rw [←pow_add]; congr 1; omega
      _≤2^(30*t)*(128*2^(Seeds i).ell)^2 := Nat.mul_le_mul_left _ hup
      _=(128*2^((Seeds i).ell+15*t))^2 := he.symm
  have hs := Nat.sqrt_le_sqrt hN
  rw [Nat.sqrt_eq'] at hs
  have hd := Nat.div_le_div_right (c:=128) hs
  simpa only [Startup49.Cutoff,Nat.mul_div_right _ (by decide : 0<128)] using hd

theorem actual_period_long_gate (i : Fin 30) (t N : ℕ) (hblock : PeriodBlock i t N) :
    2*PeriodRatio i t*(2^DistanceOmega i t:ℕ)≤(Startup49.Cutoff N:ℝ) := by
  have hp : (128:ℕ)^t≤(32768:ℕ)^t := Nat.pow_le_pow_left (by decide) t
  have hm := Nat.mul_le_mul_right (Seeds i).kl hp
  have hl := hm.trans (period_cutoff_lower i t N hblock)
  have hlR : (128:ℝ)^t*(Seeds i).kl≤(Startup49.Cutoff N:ℝ) := by exact_mod_cast hl
  exact (period_long_gate_scaled i t).trans hlR

theorem automatic_startup_arithmetic (N : ℕ) (hN : 2^49≤N) :
    ∃ i : Fin 30,∃ t : ℕ,PeriodBlock i t N ∧
      (∀ m≤N,m.primeFactors.card≤DistanceOmega i t) ∧
      (∀ m≤N,(m:ℝ)≤PeriodRatio i t*Nat.totient m) ∧
      (∀ m≤N^2,m.primeFactors.card≤ProductOmega i t) ∧
      (32768:ℕ)^t*(Seeds i).kl≤Startup49.Cutoff N ∧
      Startup49.Cutoff N≤2^((Seeds i).ell+15*t) ∧
      2*PeriodRatio i t*(2^DistanceOmega i t:ℕ)≤(Startup49.Cutoff N:ℝ) := by
  obtain ⟨i,t,hblock⟩ := exists_period_block N hN
  obtain ⟨hw,hr,hp⟩ := uniform_period_arithmetic i t N hblock.2
  exact ⟨i,t,hblock,hw,hr,hp,period_cutoff_lower i t N hblock,
    period_cutoff_upper i t N hblock,actual_period_long_gate i t N hblock⟩

theorem actual_period_half_supply (i : Fin 30) (t N m : ℕ)
    (hblock : PeriodBlock i t N) (hm : 0<m) (hmN : m≤N) :
    (Startup49.Cutoff N:ℝ)≤4*PeriodRatio i t*
      (SquarefreeSupply35.IntervalCoprime m (Startup49.Cutoff N/2) (Startup49.Cutoff N)).card := by
  obtain ⟨hw,hr,_⟩ := uniform_period_arithmetic i t N hblock.2
  exact TotientRatio38.actual_half_interval_real_supply m (Startup49.Cutoff N)
    (DistanceOmega i t) (PeriodRatio i t) hm (hr m hmN) (hw m hmN)
    (actual_period_long_gate i t N hblock)

#print axioms prime_at_mono
#print axioms primorial_growth
#print axioms ratio_growth
#print axioms rho_bounds
#print axioms seed_prime_thresholds
#print axioms power32_period
#print axioms power64_period
#print axioms period_distance_primorial
#print axioms period_product_primorial
#print axioms period_ratio_bound
#print axioms period_ratio_nonneg
#print axioms uniform_period_arithmetic
#print axioms exists_period_block
#print axioms automatic_uniform_arithmetic
#print axioms period_long_gate_scaled
#print axioms period_cutoff_lower
#print axioms period_cutoff_upper
#print axioms actual_period_long_gate
#print axioms automatic_startup_arithmetic
#print axioms actual_period_half_supply
end
end JSP233.PrimePeriod41
