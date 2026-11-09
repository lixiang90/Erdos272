module

public import Erdos272.Arithmetic.PrimePeriod41
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Unbounded short-band schedules and weighted sums from actual finite seeds. -/
namespace JSP233.WeightedPeriod42
open StarCompletion PrimorialRatio39 StartupSeeds40 PrimePeriod41 WeightedFar38 WeightedTail39
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 3000000

def Scale (t : ℕ) : ℕ := 128^t
def Ell (i : Fin 30) (t : ℕ) : ℕ := (Seeds i).ell+15*t
def Slope (E B : ℕ) : ℝ := ((B+1:ℕ):ℝ)/((2*(B-E):ℕ):ℝ)
def Envelope (i : Fin 30) (t j : ℕ) : ℝ :=
  BandEnvelope (Ell i t) (ProductOmega i t) (Scale t*(Seeds i).b0)
    (Scale t*(Seeds i).b1) (Scale t*(Seeds i).b) (PeriodRatio i t) j
def SeedEnvelope (i : Fin 30) (j : ℕ) : ℝ :=
  BandEnvelope (Seeds i).ell (Seeds i).v (Seeds i).b0 (Seeds i).b1 (Seeds i).b (Seeds i).ratio j

theorem linear_growth (a step t : ℕ) (hstep : step≤a) : a+step*t≤2^t*a := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : 1≤(2:ℕ)^t := by
      have hh : 0<(2:ℕ)^t := by positivity
      omega
    have hh : step≤2^t*a := hstep.trans (by have hm:=Nat.mul_le_mul_right a hp; simpa using hm)
    rw [pow_succ]
    nlinarith only [ih,hh]

theorem scale_pos (t : ℕ) : 0<Scale t := by unfold Scale; positivity

theorem error_growth (e v t : ℕ) (he : 15≤e) (hv : 10≤v+1) :
    (e+15*t)*(v+10*t+1)≤Scale t*(e*(v+1)) := by
  have h1 := linear_growth e 15 t he
  have h2 := linear_growth (v+1) 10 t hv
  have hp := Nat.mul_le_mul h1 h2
  have hs : ((2:ℕ)^t)^2≤Scale t := by
    calc
      ((2:ℕ)^t)^2=(4:ℕ)^t := by rw [sq,←mul_pow]; norm_num
      _≤Scale t := Nat.pow_le_pow_left (by decide) t
  have hm := Nat.mul_le_mul_right (e*(v+1)) hs
  nlinarith only [hp,hm]

theorem slope_nonneg (E B : ℕ) : 0≤Slope E B := by unfold Slope; positivity

theorem scaled_slope (E Et B s : ℕ) (hs : 1≤s) (hbase : E<B) (hEt : Et≤s*E) :
    Slope Et (s*B)≤Slope E B := by
  have hs0 : 0<s := by omega
  have hlocal : Et<s*B := hEt.trans_lt (Nat.mul_lt_mul_of_pos_left hbase hs0)
  have hbaseR : (0:ℝ)<(B:ℝ)-E := by
    have hh : (E:ℝ)<B := by exact_mod_cast hbase
    linarith
  have hlocalR : (0:ℝ)<(s:ℝ)*B-Et := by
    have hh : (Et:ℝ)<(s:ℝ)*B := by exact_mod_cast hlocal
    linarith
  have hsR : (1:ℝ)≤s := by exact_mod_cast hs
  have hEtR : (Et:ℝ)≤(s:ℝ)*E := by exact_mod_cast hEt
  have hd : (s:ℝ)*((B:ℝ)-E)≤(s:ℝ)*B-Et := by nlinarith only [hEtR]
  have hn : (s:ℝ)*B+1≤(s:ℝ)*(B+1) := by nlinarith only [hsR]
  have hr : ((s:ℝ)*B+1)/(2*((s:ℝ)*B-Et))≤((B:ℝ)+1)/(2*((B:ℝ)-E)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hh1 := mul_le_mul_of_nonneg_right hn (by positivity : (0:ℝ)≤2*((B:ℝ)-E))
    have hh2 := mul_le_mul_of_nonneg_left hd (show (0:ℝ)≤B+1 by positivity)
    nlinarith only [hh1,hh2]
  simpa only [Slope,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_sub hbase.le,Nat.cast_sub hlocal.le] using hr

theorem short_coefficient_slope (e v B : ℕ) :
    ShortCoefficient e v B=(e:ℝ)*Slope (e*(v+1)) B := by
  simp only [ShortCoefficient,Slope,Nat.cast_mul,mul_div_assoc]

theorem tail_slope_eq (ell v B : ℕ) : TailSlope ell v B=Slope ((ell+3)*(v+1)) B := rfl

theorem period_short_growth (e v B t : ℕ) (he : 15≤e) (hv : 10≤v+1)
    (hbase : e*(v+1)<B) :
    ShortCoefficient (e+15*t) (v+10*t) (Scale t*B)≤(2:ℝ)^t*ShortCoefficient e v B := by
  have hs : 1≤Scale t := by have hh:=scale_pos t; omega
  have herr := error_growth e v t he hv
  have hsl := scaled_slope (e*(v+1)) ((e+15*t)*(v+10*t+1)) B (Scale t) hs hbase herr
  have heR : ((e+15*t:ℕ):ℝ)≤(2:ℝ)^t*e := by exact_mod_cast linear_growth e 15 t he
  rw [short_coefficient_slope,short_coefficient_slope]
  have hm := mul_le_mul heR hsl (slope_nonneg _ _) (by positivity : (0:ℝ)≤(2:ℝ)^t*e)
  nlinarith only [hm]

theorem period_tail_slope_growth (ell v b t : ℕ) (he : 15≤ell) (hv : 10≤v+1)
    (hbase : (ell+3)*(v+1)<b) :
    TailSlope (ell+15*t) (v+10*t) (Scale t*b)≤TailSlope ell v b := by
  have hs : 1≤Scale t := by have hh:=scale_pos t; omega
  have herr := error_growth (ell+3) v t (by omega) hv
  have hh := scaled_slope ((ell+3)*(v+1)) ((ell+3+15*t)*(v+10*t+1)) b (Scale t) hs hbase herr
  simpa only [tail_slope_eq,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh

theorem seed_min_parameters (i : Fin 30) : 15≤(Seeds i).ell ∧ 10≤(Seeds i).v+1 := by
  fin_cases i <;> norm_num [Seeds]

theorem period_ratio_dyadic (i : Fin 30) (t : ℕ) : PeriodRatio i t≤(2:ℝ)^t*(Seeds i).ratio := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hR0,_⟩ := seed_checks i
  have hp := pow_le_pow_left₀ rho_bounds.1 rho_bounds.2.le t
  have hh := mul_le_mul_of_nonneg_left hp hR0
  simpa only [PeriodRatio,mul_comm] using hh

theorem max_scaled (a b c d s : ℝ) (hs : 0≤s) (ha : a≤s*c) (hb : b≤s*d) :
    max a b≤s*max c d := by
  exact max_le (ha.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hs))
    (hb.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hs))

theorem envelope_growth (i : Fin 30) (t j : ℕ) : Envelope i t j≤(2:ℝ)^t*SeedEnvelope i j := by
  obtain ⟨he,hv⟩ := seed_min_parameters i
  obtain ⟨_,_,h0,h1,hb,_,_,_,_,_,_,_,_,_,_⟩ := seed_checks i
  have hR : 4*PeriodRatio i t≤(2:ℝ)^t*(4*(Seeds i).ratio) := by
    have hh := mul_le_mul_of_nonneg_left (period_ratio_dyadic i t) (by norm_num : (0:ℝ)≤4)
    nlinarith only [hh]
  by_cases hj0 : j=0
  · subst j
    have hh := period_short_growth (Seeds i).ell (Seeds i).v (Seeds i).b0 t he hv h0
    simpa [Envelope,SeedEnvelope,BandEnvelope,Ell,ProductOmega]
      using max_scaled _ _ _ _ ((2:ℝ)^t) (by positivity) hh hR
  by_cases hj1 : j=1
  · subst j
    have hh := period_short_growth ((Seeds i).ell+1) (Seeds i).v (Seeds i).b1 t (by omega) hv h1
    have hh' : ShortCoefficient (Ell i t+1) (ProductOmega i t) (Scale t*(Seeds i).b1)≤
        (2:ℝ)^t*ShortCoefficient ((Seeds i).ell+1) (Seeds i).v (Seeds i).b1 := by
      simpa only [Ell,ProductOmega,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hh
    simpa [Envelope,SeedEnvelope,BandEnvelope]
      using max_scaled _ _ _ _ ((2:ℝ)^t) (by positivity) hh' hR
  have hs := period_tail_slope_growth (Seeds i).ell (Seeds i).v (Seeds i).b t he hv hb
  have hel : ((Ell i t+j:ℕ):ℝ)≤(2:ℝ)^t*((Seeds i).ell+j) := by
    have hh := linear_growth ((Seeds i).ell+j) 15 t (by omega)
    have hhR : (((Seeds i).ell+j+15*t:ℕ):ℝ)≤(2:ℝ)^t*((Seeds i).ell+j) := by exact_mod_cast hh
    simpa only [Ell,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hhR
  simp only [Nat.cast_add] at hel
  have hm := mul_le_mul hs hel (by positivity : (0:ℝ)≤(Ell i t:ℝ)+j)
    (tail_slope_nonneg (Seeds i).ell (Seeds i).v (Seeds i).b)
  have htail : TailSlope (Ell i t) (ProductOmega i t) (Scale t*(Seeds i).b)*(Ell i t+j)≤
      (2:ℝ)^t*(TailSlope (Seeds i).ell (Seeds i).v (Seeds i).b*((Seeds i).ell+j)) := by
    simpa only [Ell,ProductOmega,Nat.cast_add,mul_assoc,mul_left_comm,mul_comm] using hm
  simpa only [Envelope,SeedEnvelope,BandEnvelope,if_neg hj0,if_neg hj1]
    using max_scaled _ _ _ _ ((2:ℝ)^t) (by positivity) htail hR

theorem seed_sum_bound (i : Fin 30) (n : ℕ) :
    (∑ j∈Finset.range n,SeedEnvelope i j*(1/2:ℝ)^j)≤160 := by
  have hh := envelope_prefix_tail_bound (Seeds i).ell (Seeds i).v
    (Seeds i).b0 (Seeds i).b1 (Seeds i).b n 32 (Seeds i).ratio (by decide) (seed_tail_gate i)
  exact hh.trans (seed_sigma_bound i)

theorem period_sum_bound (i : Fin 30) (t n : ℕ) :
    (∑ j∈Finset.range n,Envelope i t j*(1/2:ℝ)^j)≤(2:ℝ)^t*160 := by
  calc
    _≤∑ j∈Finset.range n,((2:ℝ)^t*SeedEnvelope i j)*(1/2:ℝ)^j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (envelope_growth i t j) (by positivity)
    _=(2:ℝ)^t*(∑ j∈Finset.range n,SeedEnvelope i j*(1/2:ℝ)^j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤(2:ℝ)^t*160 := mul_le_mul_of_nonneg_left (seed_sum_bound i n) (by positivity)

#print axioms linear_growth
#print axioms scale_pos
#print axioms error_growth
#print axioms slope_nonneg
#print axioms scaled_slope
#print axioms short_coefficient_slope
#print axioms tail_slope_eq
#print axioms period_short_growth
#print axioms period_tail_slope_growth
#print axioms seed_min_parameters
#print axioms period_ratio_dyadic
#print axioms max_scaled
#print axioms envelope_growth
#print axioms seed_sum_bound
#print axioms period_sum_bound
end
end JSP233.WeightedPeriod42
