module

public import Erdos272.Core.N158375.StarCore158375
public import Erdos272.Core.N180000.AnalyticCore180000

@[expose] public section

namespace JSP233.StarActual158375
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
open CoreUnionSource200000 PrimeQuadratic200000 SharpPrime180000 PrimeReciprocal180000
open IndexedCorePairs200000 ActualCorePairs200000 StarCore158375
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem weights_le_choose {a : ℕ} (ha : 12 ≤ a) (hb : a ≤ 2^18) :
    (∑ q ∈ AllPrimes a, Weight a q) ≤ a.choose 2 := by
  have hs := Finset.sum_le_sum (s := AllPrimes a) (fun q hq =>
    twice_weight_bound a (Finset.mem_filter.mp hq).2.pos)
  have hs' : 2*((∑ q ∈ AllPrimes a, Weight a q : ℕ) : ℝ) ≤
      (a:ℝ)^2*(∑ q ∈ AllPrimes a, (1:ℝ)/(q:ℝ)^2)+
      (a:ℝ)*(∑ q ∈ AllPrimes a, (1:ℝ)/(q:ℝ)) := by
    simpa only [Nat.cast_sum, Finset.mul_sum, Finset.sum_add_distrib] using hs
  have hsq := mul_le_mul_of_nonneg_left (prime_square_sum_sharp a) (sq_nonneg (a:ℝ))
  have hc : 2*(a.choose 2:ℝ)+(a:ℝ) = (a:ℝ)*a := by
    exact_mod_cast APInterval208.choose_two_twice a
  have haR : (12:ℝ) ≤ a := by exact_mod_cast ha
  have hnonneg : (0:ℝ) ≤ a := Nat.cast_nonneg _
  by_cases hsmall : a ≤ 256
  · have hrec := mul_le_mul_of_nonneg_left (PrimeHead190000.small_reciprocal hsmall) hnonneg
    have hprod := mul_nonneg (show (0:ℝ) ≤ a by positivity)
      (show (0:ℝ) ≤ 27*(a:ℝ)-150 by linarith)
    have hout : ((∑ q ∈ AllPrimes a, Weight a q : ℕ):ℝ) ≤ a.choose 2 := by
      nlinarith only [hs', hsq, hrec, hc, hprod]
    exact_mod_cast hout
  · have haR' : (257:ℝ) ≤ a := by exact_mod_cast (show 257 ≤ a by omega)
    have hrec := mul_le_mul_of_nonneg_left (prime_reciprocal_half hb (by decide : 1 ≤ 18)) hnonneg
    norm_num only [Nat.cast_ofNat] at hrec
    have hprod := mul_nonneg (show (0:ℝ) ≤ a by positivity)
      (show (0:ℝ) ≤ 27*(a:ℝ)-525 by linarith)
    have hout : ((∑ q ∈ AllPrimes a, Weight a q : ℕ):ℝ) ≤ a.choose 2 := by
      nlinarith only [hs', hsq, hrec, hc, hprod]
    exact_mod_cast hout

theorem actual_single_star_source {N : ℕ} {S : Finset ℤ}
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hS : 2 ≤ S.card)
    (ha : 12 ≤ MaxAPSize S) :
    Defect S * (UnitBound (MaxAPSize S)+(MaxAPSize S/6).choose 2) ≤ (Pool S).card := by
  have hcard : S.card ≤ N := by
    simpa only [ground_card] using Finset.card_le_card hground
  have hmax : MaxAPSize S ≤ 2^18 := (maxAPSize_le_card S).trans (hcard.trans hN)
  apply actual_defect_source_of_index_bound hS
  intro h hh ell hc l hlen
  exact star_index_bound ha hh hc (weights_le_choose ha hmax) hlen

#print axioms weights_le_choose
#print axioms actual_single_star_source
end
end JSP233.StarActual158375
