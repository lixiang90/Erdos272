import Erdos272.Counting.MiddleJoint51
import Erdos272.Arithmetic.MixedFloor29
import Mathlib.Analysis.PSeries

/-! Finite coprime densities for the actual MiddleJoint51 resource pools.
The finite convolution/sieve proof follows the fixed Erdos272 source at
a624e9de77e0bd8868e7103f8b379f9dbd86b607, sections 10586--11113;
it is reproved here and does not import that external file or its target. -/
namespace JSP233.CoprimeDensity52
open scoped Classical BigOperators
open MixedFloor29
noncomputable section
set_option maxHeartbeats 2500000

def reciprocalSum (N : ℕ) : ℝ := ∑ d∈Finset.Icc 1 N,(d:ℝ)⁻¹

theorem coprime_moebius_indicator {m : ℕ} (hm : 0<m) (j : ℕ) :
    (∑ d∈m.divisors,if d∣j then (ArithmeticFunction.moebius d:ℝ) else 0)=
      if m.Coprime j then 1 else 0 := by
  simpa only [Nat.coprime_iff_gcd_eq_one,Nat.gcd_comm] using
    (MixedFloor29.coprime_indicator j m hm).symm

theorem card_multiples_Icc (K d : ℕ) :
    ((Finset.Icc 1 K).filter (fun j=>d∣j)).card=K/d := by
  have he : (Finset.range (K+1)).filter (fun j=>j≠0 ∧ d∣j)=
      (Finset.Icc 1 K).filter (fun j=>d∣j) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
    omega
  rw [←he]
  exact Nat.card_multiples' K d

theorem nat_div_error_le_one {K d : ℕ} (hd : 0<d) :
    |((K/d:ℕ):ℝ)-(K:ℝ)/d|≤1 := by
  obtain ⟨hlo,hhi⟩ := TotientFloor29.nat_div_bounds K d hd
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def reciprocalSquareSum (N : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 N, ((d : ℝ)^2)⁻¹

noncomputable def moebiusSquareSum (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)/((d : ℝ)^2)

theorem reciprocalSquareSum_bounds {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ reciprocalSquareSum N ∧ reciprocalSquareSum N ≤ 5/3 := by
  refine ⟨?_,?_⟩
  swap
  · simpa only [reciprocalSquareSum,APCount41.SquareReciprocal,one_div] using APCount41.square_reciprocal_bound N
  have hh := Finset.single_le_sum (f := fun d : ℕ => ((d : ℝ)^2)⁻¹)
    (s := Finset.Icc 1 N) (fun d _hd => by positivity)
    (show 1 ∈ Finset.Icc 1 N from Finset.mem_Icc.mpr ⟨le_rfl,hN⟩)
  simpa only [reciprocalSquareSum,Nat.cast_one,one_pow,inv_one] using hh

theorem truncated_product_fiber {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    (((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1*p.2 ≤ N)).filter (fun p => p.1*p.2 = n) =
        n.divisorsAntidiagonal := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hnN := (Finset.mem_Icc.mp hn).2
  ext p
  simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
    Nat.mem_divisorsAntidiagonal]
  constructor
  · rintro ⟨⟨⟨hp,hq⟩,_hprod⟩,heq⟩
    exact ⟨heq,by omega⟩
  · rintro ⟨heq,_hn0⟩
    have hp : 0 < p.1 := by nlinarith only [heq,hn1]
    have hq : 0 < p.2 := by nlinarith only [heq,hn1]
    have hpN : p.1 ≤ N := (Nat.le_mul_of_pos_right p.1 hq).trans (heq ▸ hnN)
    have hqN : p.2 ≤ N := (Nat.le_mul_of_pos_left p.2 hp).trans (heq ▸ hnN)
    exact ⟨⟨⟨⟨hp,hpN⟩,⟨hq,hqN⟩⟩,heq ▸ hnN⟩,heq⟩

theorem moebius_antidiagonal_weight (n : ℕ) :
    (∑ p ∈ n.divisorsAntidiagonal,
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) =
      if n = 1 then 1 else 0 := by
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius p.1 : ℝ)/((n : ℝ)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have heq : (p.1 : ℝ)*p.2 = n := by
        exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hp).1
      rw [heq]
    _ = (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ))/((n : ℝ)^2) := by
      rw [Nat.sum_divisorsAntidiagonal (fun d _k =>
        (ArithmeticFunction.moebius d : ℝ)/((n : ℝ)^2)),Finset.sum_div]
    _ = _ := by
      have hh : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) =
          if n = 1 then 1 else 0 := by
        exact_mod_cast moebius_divisor_indicator n
      rw [hh]
      split_ifs with hn
      · subst n; norm_num
      · simp

theorem truncated_moebius_product_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => p.1*p.2 ≤ N),
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) = 1 := by
  let P := ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
    (fun p : ℕ × ℕ => p.1*p.2 ≤ N)
  have hmaps : ∀ p ∈ P, p.1*p.2 ∈ Finset.Icc 1 N := by
    intro p hp
    obtain ⟨hpI,hprod⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpi,hqi⟩ := Finset.mem_product.mp hpI
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp hpi).1
      (Finset.mem_Icc.mp hqi).1,hprod⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmaps
    (fun p : ℕ × ℕ => (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2))
  calc
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ p ∈ P.filter (fun p => p.1*p.2 = n),
        (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2) := hsum.symm
    _ = ∑ n ∈ Finset.Icc 1 N, if n = 1 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [show P.filter (fun p => p.1*p.2 = n) = n.divisorsAntidiagonal from
        truncated_product_fiber hn,moebius_antidiagonal_weight]
    _ = 1 := by simp [hN]

theorem moebius_product_full_sum (N : ℕ) :
    (∑ p ∈ (Finset.Icc 1 N).product (Finset.Icc 1 N),
      (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)) =
      moebiusSquareSum N*reciprocalSquareSum N := by
  rw [Finset.product_eq_sprod,Finset.sum_product,moebiusSquareSum,reciprocalSquareSum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
  ring


def coprimeRectangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 A).product (Finset.Icc 1 B)).filter (fun p => p.1.Coprime p.2)

theorem divisors_eq_filter_Icc {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (Finset.Icc 1 N).filter (fun d => d ∣ m) = m.divisors := by
  ext d
  simp only [Finset.mem_filter,Finset.mem_Icc,Nat.mem_divisors]
  constructor
  · rintro ⟨_hdI,hdm⟩
    exact ⟨hdm,hm.ne'⟩
  · rintro ⟨hdm,_hm0⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdm hm,(Nat.le_of_dvd hm hdm).trans hmN⟩,hdm⟩

theorem coprime_moebius_full_indicator {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) (j : ℕ) :
    (∑ d ∈ Finset.Icc 1 N,
      if d ∣ m ∧ d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0) =
        if m.Coprime j then 1 else 0 := by
  calc
    _ = ∑ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ m),
        if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases hdm : d ∣ m <;> simp [hdm]
    _ = ∑ d ∈ m.divisors, if d ∣ j then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      rw [divisors_eq_filter_Icc hm hmN]
    _ = _ := by exact_mod_cast coprime_moebius_indicator hm j

theorem coprimeRectangle_card_moebius {N A B : ℕ} (hAN : A ≤ N) :
    ((coprimeRectangle A B).card : ℝ) = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*(A/d : ℕ)*(B/d : ℕ) := by
  calc
    _ = ∑ p ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B),
        if p.1.Coprime p.2 then (1 : ℝ) else 0 := by simp [coprimeRectangle]
    _ = ∑ p ∈ (Finset.Icc 1 A).product (Finset.Icc 1 B), ∑ d ∈ Finset.Icc 1 N,
        if d ∣ p.1 ∧ d ∣ p.2 then (ArithmeticFunction.moebius d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have ha := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      exact (coprime_moebius_full_indicator ha.1 (ha.2.trans hAN) p.2).symm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      have hprod : ((Finset.Icc 1 A).product (Finset.Icc 1 B)).filter
          (fun p : ℕ × ℕ => d ∣ p.1 ∧ d ∣ p.2) =
          ((Finset.Icc 1 A).filter (fun a => d ∣ a)).product
            ((Finset.Icc 1 B).filter (fun b => d ∣ b)) := by
        ext p
        simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product]
        tauto
      rw [← Finset.sum_filter,hprod]
      simp only [Finset.product_eq_sprod,Finset.sum_const,nsmul_eq_mul,Finset.card_product,
        card_multiples_Icc,Nat.cast_mul]
      ring

theorem nat_div_product_error {A B d : ℕ} (hd : 0 < d) :
    |((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2)| ≤ ((A : ℝ)+B)/d := by
  have ha := nat_div_error_le_one (K := A) hd
  have hb := nat_div_error_le_one (K := B) hd
  have ha0 : (0 : ℝ) ≤ (A/d : ℕ) := Nat.cast_nonneg _
  have hb0 : (0 : ℝ) ≤ (B/d : ℕ) := Nat.cast_nonneg _
  have hau := Nat.cast_div_le (α := ℝ) (m := A) (n := d)
  have hbu := Nat.cast_div_le (α := ℝ) (m := B) (n := d)
  have hda : (0 : ℝ) ≤ (A : ℝ)/d := by positivity
  have hdb : (0 : ℝ) ≤ (B : ℝ)/d := by positivity
  have hid : (A : ℝ)*B/((d : ℝ)^2) = ((A : ℝ)/d)*((B : ℝ)/d) := by ring
  have hsum : ((A : ℝ)+B)/d = (A : ℝ)/d+(B : ℝ)/d := by ring
  rw [hid,hsum]
  apply abs_le.mpr
  have hap := (abs_le.mp ha).1
  have hbp := (abs_le.mp hb).1
  have hprod := mul_le_mul hau hbu hb0 hda
  constructor
  · nlinarith only [hap,hbp,hau,hbu,ha0,hb0,hda,hdb]
  · nlinarith only [hprod,hda,hdb]


noncomputable def finiteCoprimeDensity (N : ℕ) : ℝ := (reciprocalSquareSum N)⁻¹

theorem reciprocal_product_row_tail {N a : ℕ} (ha : a ∈ Finset.Icc 1 N) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N), ((k : ℝ)^2)⁻¹) ≤
      2*a/N := by
  obtain ⟨ha1,haN⟩ := Finset.mem_Icc.mp ha
  have hN : 0 < N := lt_of_lt_of_le ha1 haN
  have hdiv : 0 < N/a := Nat.div_pos haN ha1
  have hdivN : N/a ≤ N := Nat.div_le_self _ _
  have hset : (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N) = Finset.Ioc (N/a) N := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_Icc,Finset.mem_Ioc]
    have hiff : N/a < k ↔ N < k*a := Nat.div_lt_iff_lt_mul ha1
    constructor
    · rintro ⟨⟨_hk1,hkN⟩,hprod⟩
      exact ⟨hiff.mpr (by nlinarith only [hprod]),hkN⟩
    · rintro ⟨hk,hkN⟩
      exact ⟨⟨by omega,hkN⟩,by have hh := hiff.mp hk; nlinarith only [hh]⟩
  rw [hset]
  have htail := sum_Ioc_inv_sq_le_sub (α := ℝ) (k := N/a) hdiv.ne' hdivN
  have hrem := Nat.mod_lt N ha1
  have hquot := Nat.mod_add_div N a
  have hmul : N ≤ 2*a*(N/a) := by nlinarith only [hrem,hquot,hdiv]
  have hmulR : (N : ℝ) ≤ 2*a*(N/a : ℕ) := by exact_mod_cast hmul
  have hquotR : (0 : ℝ) < (N/a : ℕ) := Nat.cast_pos.mpr hdiv
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hinv : ((N/a : ℕ) : ℝ)⁻¹ ≤ 2*a/N := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ hquotR hNR).mpr
    simpa only [one_mul] using hmulR
  have hnonneg : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  linarith only [htail,hinv,hnonneg]

theorem reciprocal_product_tail_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => ¬p.1*p.2 ≤ N),
      ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹) ≤ 2*reciprocalSum N/N := by
  have hsplit : (∑ p ∈ ((Finset.Icc 1 N).product (Finset.Icc 1 N)).filter
      (fun p : ℕ × ℕ => ¬p.1*p.2 ≤ N),
      ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹) =
      ∑ a ∈ Finset.Icc 1 N, ((a : ℝ)^2)⁻¹*
        (∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬a*k ≤ N), ((k : ℝ)^2)⁻¹) := by
    rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _ha
    simp only [Finset.sum_filter,Finset.mul_sum,mul_ite,mul_zero]
  rw [hsplit]
  calc
    _ ≤ ∑ a ∈ Finset.Icc 1 N, ((a : ℝ)^2)⁻¹*(2*a/N) := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_left (reciprocal_product_row_tail ha) (by positivity)
    _ = 2*reciprocalSum N/N := by
      calc
        _ = ∑ a ∈ Finset.Icc 1 N, (2/N)*(a : ℝ)⁻¹ := by
          apply Finset.sum_congr rfl
          intro a ha
          have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by
            have hh := (Finset.mem_Icc.mp ha).1; omega)
          have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          field_simp
        _ = _ := by rw [← Finset.mul_sum]; unfold reciprocalSum; ring

theorem moebiusSquareSum_normalization_error {N : ℕ} (hN : 1 ≤ N) :
    |moebiusSquareSum N*reciprocalSquareSum N-1| ≤ 2*reciprocalSum N/N := by
  let I := (Finset.Icc 1 N).product (Finset.Icc 1 N)
  let f (p : ℕ × ℕ) : ℝ :=
    (ArithmeticFunction.moebius p.1 : ℝ)/(((p.1 : ℝ)*p.2)^2)
  have hgood : (∑ p ∈ I.filter (fun p => p.1*p.2 ≤ N), f p) = 1 :=
    truncated_moebius_product_sum hN
  have hfull : (∑ p ∈ I, f p) = moebiusSquareSum N*reciprocalSquareSum N :=
    moebius_product_full_sum N
  have hpart := Finset.sum_filter_add_sum_filter_not I (fun p => p.1*p.2 ≤ N) f
  have heq : moebiusSquareSum N*reciprocalSquareSum N-1 =
      ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N), f p := by linarith only [hpart,hgood,hfull]
  rw [heq]
  calc
    _ ≤ ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N), |f p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ I.filter (fun p => ¬p.1*p.2 ≤ N),
        ((p.1 : ℝ)^2)⁻¹*((p.2 : ℝ)^2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p _hp
      have hmu : |(ArithmeticFunction.moebius p.1 : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.1)
      dsimp only [f]
      rw [abs_div,abs_of_nonneg (sq_nonneg ((p.1 : ℝ)*p.2))]
      calc
        _ ≤ 1/(((p.1 : ℝ)*p.2)^2) := div_le_div_of_nonneg_right hmu (sq_nonneg _)
        _ = _ := by simp only [mul_pow,one_div,mul_inv_rev]; ring
    _ ≤ 2*reciprocalSum N/N := reciprocal_product_tail_le hN

theorem finiteCoprimeDensity_bounds {N : ℕ} (hN : 1 ≤ N) :
    0 < finiteCoprimeDensity N ∧ finiteCoprimeDensity N ≤ 1 := by
  have hH := (reciprocalSquareSum_bounds hN).1
  have hHpos : 0 < reciprocalSquareSum N := by linarith only [hH]
  refine ⟨inv_pos.mpr hHpos,?_⟩
  change (reciprocalSquareSum N)⁻¹ ≤ 1
  exact (inv_le_one₀ hHpos).mpr hH

theorem moebiusSquareSum_density_error {N : ℕ} (hN : 1 ≤ N) :
    |moebiusSquareSum N-finiteCoprimeDensity N| ≤ 2*reciprocalSum N/N := by
  have hH := (reciprocalSquareSum_bounds hN).1
  have hHpos : 0 < reciprocalSquareSum N := by linarith only [hH]
  have hh := moebiusSquareSum_normalization_error hN
  have hid : |moebiusSquareSum N-finiteCoprimeDensity N| * reciprocalSquareSum N =
      |moebiusSquareSum N*reciprocalSquareSum N-1| := by
    rw [← abs_of_pos hHpos,← abs_mul]
    congr 1
    rw [sub_mul]
    simp only [finiteCoprimeDensity,inv_mul_cancel₀ hHpos.ne',abs_of_pos hHpos]
  have hnonneg := abs_nonneg (moebiusSquareSum N-finiteCoprimeDensity N)
  nlinarith only [hh,hid,hH,hnonneg]

theorem finiteCoprimeDensity_weights_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ d ∈ Finset.Icc 1 N, finiteCoprimeDensity N/((d : ℝ)^2)) = 1 := by
  rw [show (∑ d ∈ Finset.Icc 1 N, finiteCoprimeDensity N/((d : ℝ)^2)) =
    finiteCoprimeDensity N*reciprocalSquareSum N by
      simp only [div_eq_mul_inv,← Finset.mul_sum,reciprocalSquareSum]]
  have hH := (reciprocalSquareSum_bounds hN).1
  exact inv_mul_cancel₀ (by linarith : reciprocalSquareSum N ≠ 0)


theorem coprimeRectangle_moebius_error {N A B : ℕ} (hAN : A ≤ N) :
    |((coprimeRectangle A B).card : ℝ)-moebiusSquareSum N*A*B| ≤
      ((A : ℝ)+B)*reciprocalSum N := by
  have hmain : moebiusSquareSum N*A*B = ∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*((A : ℝ)*B/((d : ℝ)^2)) := by
    simp only [moebiusSquareSum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  have heq : ((coprimeRectangle A B).card : ℝ)-moebiusSquareSum N*A*B =
      ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2)) := by
    rw [coprimeRectangle_card_moebius hAN,hmain,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 N, |(ArithmeticFunction.moebius d : ℝ)*
        (((A/d : ℕ) : ℝ)*(B/d : ℕ)-(A : ℝ)*B/((d : ℝ)^2))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 N, ((A : ℝ)+B)/d := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have herr := nat_div_product_error (A := A) (B := B) (Finset.mem_Icc.mp hd).1
      exact (mul_le_mul hmu herr (abs_nonneg _) (by norm_num)).trans (by simp)
    _ = _ := by simp only [div_eq_mul_inv,← Finset.mul_sum,reciprocalSum]

theorem coprimeRectangle_density_error {N A B : ℕ} (hN : 1 ≤ N)
    (hAN : A ≤ N) (hBN : B ≤ N) :
    |((coprimeRectangle A B).card : ℝ)-finiteCoprimeDensity N*A*B| ≤
      2*((A : ℝ)+B)*reciprocalSum N := by
  have hfirst := coprimeRectangle_moebius_error (B := B) hAN
  have hnormal := moebiusSquareSum_density_error hN
  have hAN' : (A : ℝ) ≤ N := by exact_mod_cast hAN
  have hBN' : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have harea : 2*(A : ℝ)*B ≤ ((A : ℝ)+B)*N := by
    have ha := mul_nonneg (sub_nonneg.mpr hAN') (Nat.cast_nonneg (α := ℝ) B)
    have hb := mul_nonneg (sub_nonneg.mpr hBN') (Nat.cast_nonneg (α := ℝ) A)
    nlinarith only [ha,hb]
  have hareaDiv : 2*(A : ℝ)*B/N ≤ (A : ℝ)+B := (div_le_iff₀ hNpos).mpr harea
  have hHnonneg : 0 ≤ reciprocalSum N := Finset.sum_nonneg (fun d _hd => by positivity)
  have herrorArea : (2*reciprocalSum N/N)*(A : ℝ)*B ≤ ((A : ℝ)+B)*reciprocalSum N := by
    have hh := mul_le_mul_of_nonneg_right hareaDiv hHnonneg
    calc
      _ = (2*(A : ℝ)*B/N)*reciprocalSum N := by ring
      _ ≤ _ := hh
  have hsecond : |moebiusSquareSum N*A*B-finiteCoprimeDensity N*A*B| ≤
      ((A : ℝ)+B)*reciprocalSum N := by
    calc
      _ = |moebiusSquareSum N-finiteCoprimeDensity N| * (A : ℝ)*B := by
        rw [show moebiusSquareSum N*A*B-finiteCoprimeDensity N*A*B =
          (moebiusSquareSum N-finiteCoprimeDensity N)*A*B by ring]
        simp only [abs_mul,Nat.abs_cast]
      _ ≤ (2*reciprocalSum N/N)*(A : ℝ)*B := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnormal
          (Nat.cast_nonneg A)) (Nat.cast_nonneg B)
      _ ≤ _ := herrorArea
  have hh := abs_sub_le ((coprimeRectangle A B).card : ℝ)
    (moebiusSquareSum N*A*B) (finiteCoprimeDensity N*A*B)
  linarith only [hh,hfirst,hsecond]

abbrev coprimeBox := MiddleJoint51.CoprimeBox

theorem coprimeBox_card_identity {A₀ A₁ B₀ B₁ : ℕ} (hA : A₀ ≤ A₁) (hB : B₀ ≤ B₁) :
    (coprimeBox A₀ A₁ B₀ B₁).card+(coprimeRectangle A₀ B₁).card+
      (coprimeRectangle A₁ B₀).card =
      (coprimeRectangle A₁ B₁).card+(coprimeRectangle A₀ B₀).card := by
  let S := (coprimeRectangle A₁ B₁).filter (fun p => ¬p.1 ≤ A₀)
  let T := (coprimeRectangle A₁ B₀).filter (fun p => ¬p.1 ≤ A₀)
  have hf₁ : (coprimeRectangle A₁ B₁).filter (fun p => p.1 ≤ A₀) =
      coprimeRectangle A₀ B₁ := by
    ext p
    simp only [coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hf₀ : (coprimeRectangle A₁ B₀).filter (fun p => p.1 ≤ A₀) =
      coprimeRectangle A₀ B₀ := by
    ext p
    simp only [coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hg₀ : S.filter (fun p => p.2 ≤ B₀) = T := by
    ext p
    simp only [S,T,coprimeRectangle,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc]
    omega
  have hg₁ : S.filter (fun p => ¬p.2 ≤ B₀) = coprimeBox A₀ A₁ B₀ B₁ := by
    ext p
    simp only [S,coprimeRectangle,coprimeBox,MiddleJoint51.CoprimeBox,Finset.product_eq_sprod,Finset.mem_filter,
      Finset.mem_product,Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hp₁ := Finset.card_filter_add_card_filter_not (s := coprimeRectangle A₁ B₁)
    (fun p => p.1 ≤ A₀)
  have hp₀ := Finset.card_filter_add_card_filter_not (s := coprimeRectangle A₁ B₀)
    (fun p => p.1 ≤ A₀)
  have hpS := Finset.card_filter_add_card_filter_not (s := S) (fun p => p.2 ≤ B₀)
  rw [hf₁] at hp₁
  rw [hf₀] at hp₀
  rw [hg₀,hg₁] at hpS
  change (coprimeRectangle A₀ B₁).card+S.card = _ at hp₁
  change (coprimeRectangle A₀ B₀).card+T.card = _ at hp₀
  omega

theorem coprimeBox_density_error {N A₀ A₁ B₀ B₁ : ℕ} (hN : 1 ≤ N)
    (hA : A₀ ≤ A₁) (hAN : A₁ ≤ N) (hB : B₀ ≤ B₁) (hBN : B₁ ≤ N) :
    |((coprimeBox A₀ A₁ B₀ B₁).card : ℝ)-
      finiteCoprimeDensity N*((A₁ : ℝ)-A₀)*((B₁ : ℝ)-B₀)| ≤
      8*((A₁ : ℝ)+B₁)*reciprocalSum N := by
  have h₁₁ := coprimeRectangle_density_error hN hAN hBN
  have h₀₁ := coprimeRectangle_density_error hN (hA.trans hAN) hBN
  have h₁₀ := coprimeRectangle_density_error hN hAN (hB.trans hBN)
  have h₀₀ := coprimeRectangle_density_error hN (hA.trans hAN) (hB.trans hBN)
  have hcard : ((coprimeBox A₀ A₁ B₀ B₁).card : ℝ)+(coprimeRectangle A₀ B₁).card+
      (coprimeRectangle A₁ B₀).card =
      (coprimeRectangle A₁ B₁).card+(coprimeRectangle A₀ B₀).card := by
    exact_mod_cast coprimeBox_card_identity hA hB
  have hAR : (A₀ : ℝ) ≤ A₁ := by exact_mod_cast hA
  have hBR : (B₀ : ℝ) ≤ B₁ := by exact_mod_cast hB
  have hHnonneg : 0 ≤ reciprocalSum N := Finset.sum_nonneg (fun d _hd => by positivity)
  have hAH := mul_le_mul_of_nonneg_right hAR hHnonneg
  have hBH := mul_le_mul_of_nonneg_right hBR hHnonneg
  obtain ⟨h₁₁l,h₁₁u⟩ := abs_le.mp h₁₁
  obtain ⟨h₀₁l,h₀₁u⟩ := abs_le.mp h₀₁
  obtain ⟨h₁₀l,h₁₀u⟩ := abs_le.mp h₁₀
  obtain ⟨h₀₀l,h₀₀u⟩ := abs_le.mp h₀₀
  apply abs_le.mpr
  constructor <;> nlinarith only [hcard,h₁₁l,h₁₁u,h₀₁l,h₀₁u,h₁₀l,h₁₀u,
    h₀₀l,h₀₀u,hAH,hBH]


theorem finiteCoprimeDensity_lower {N : ℕ} (hN : 1≤N) :
    (3/5:ℝ)≤finiteCoprimeDensity N := by
  have hb := reciprocalSquareSum_bounds hN
  have hp : 0<reciprocalSquareSum N := by linarith only [hb.1]
  change (3/5:ℝ)≤(reciprocalSquareSum N)⁻¹
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hp).mpr
  linarith only [hb.2]

theorem reciprocalSum_eq_Harmonic (N : ℕ) : reciprocalSum N=HarmonicAbel29.Harmonic N := by
  simp only [reciprocalSum,HarmonicAbel29.Harmonic,one_div]

theorem actual_upper_triangle_density {N A B : ℕ} (hN : 1≤N)
    (hAB : A≤B) (hBN : B≤N) :
    ((MiddleJoint51.UpperTriangle A B).card:ℝ)≤
      finiteCoprimeDensity N*((B:ℝ)-A)^2/2+8*B*reciprocalSum N := by
  have ht : 2*((MiddleJoint51.UpperTriangle A B).card:ℝ)≤(coprimeBox A B A B).card := by
    exact_mod_cast MiddleJoint51.twice_upper_triangle_card_le A B
  have hb := (abs_le.mp (coprimeBox_density_error hN hAB hBN hAB hBN)).2
  nlinarith only [ht,hb]

theorem actual_resource_density {N C A M e : ℕ} (hN : 1≤N)
    (hCN : C≤N) (hAe : A≤e) (heM : e≤M) (hMN : M≤N) :
    (MiddleJoint51.ResourceCount C A M e:ℝ)≤
      (C:ℝ)*((e:ℝ)-A)+finiteCoprimeDensity N*
        (((M:ℝ)-e)*(C+M)-((M:ℝ)-e)^2/2)+
      40*((C:ℝ)+M)*HarmonicAbel29.Harmonic N := by
  have h1 := (abs_le.mp (coprimeBox_density_error hN (Nat.zero_le C) hCN heM hMN)).2
  have h2 := (abs_le.mp (coprimeBox_density_error hN (Nat.zero_le e) (heM.trans hMN) heM hMN)).2
  have ht := actual_upper_triangle_density hN heM hMN
  have hAeR : (A:ℝ)≤e := by exact_mod_cast hAe
  have heMR : (e:ℝ)≤M := by exact_mod_cast heM
  have hH := HarmonicAbel29.harmonic_nonneg N
  rw [reciprocalSum_eq_Harmonic] at h1 h2 ht
  simp only [coprimeBox,Nat.cast_zero,sub_zero] at h1 h2
  have hpay := mul_le_mul_of_nonneg_right heMR hH
  simp only [MiddleJoint51.ResourceCount,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hAe]
  nlinarith only [h1,h2,ht,hpay,mul_nonneg (Nat.cast_nonneg (α:=ℝ) C) hH]

#print axioms coprime_moebius_indicator
#print axioms card_multiples_Icc
#print axioms nat_div_error_le_one
#print axioms reciprocalSquareSum_bounds
#print axioms truncated_product_fiber
#print axioms moebius_antidiagonal_weight
#print axioms truncated_moebius_product_sum
#print axioms moebius_product_full_sum
#print axioms divisors_eq_filter_Icc
#print axioms coprime_moebius_full_indicator
#print axioms coprimeRectangle_card_moebius
#print axioms nat_div_product_error
#print axioms reciprocal_product_row_tail
#print axioms reciprocal_product_tail_le
#print axioms moebiusSquareSum_normalization_error
#print axioms finiteCoprimeDensity_bounds
#print axioms moebiusSquareSum_density_error
#print axioms finiteCoprimeDensity_weights_sum
#print axioms coprimeRectangle_moebius_error
#print axioms coprimeRectangle_density_error
#print axioms coprimeBox_card_identity
#print axioms coprimeBox_density_error
#print axioms finiteCoprimeDensity_lower
#print axioms reciprocalSum_eq_Harmonic
#print axioms actual_upper_triangle_density
#print axioms actual_resource_density
end
end JSP233.CoprimeDensity52
