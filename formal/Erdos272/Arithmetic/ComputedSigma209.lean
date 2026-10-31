import Erdos272.Arithmetic.SigmaSieve209
import Erdos272.Arithmetic.ForcedCheck209
namespace JSP233.ComputedSigma209
set_option maxHeartbeats 0

def value (base factor : Nat→Nat) (fuel n : Nat) : Nat :=
  if n≤32753 then base n else
  match fuel with
  | 0 => 0
  | k+1 =>
    let p := factor n
    if p=0 then n+1 else
      let m := n/p
      let sm := value base factor k m
      if p∣m then (p+1)*sm-p*value base factor k (m/p) else (p+1)*sm

theorem correct {base factor : Nat→Nat} {H : Nat}
    (hbase : ∀ n, n≤32753 → base n=SigmaSieve209.sigmaOne n)
    (hfactor : ∀ n, 32753<n → n≤H →
      (factor n=0 → n.Prime) ∧
      (factor n≠0 → (factor n).Prime ∧ factor n∣n))
    (fuel n : Nat) (hnH : n≤H) (hfuel : n<32754*2^fuel) :
    value base factor fuel n=SigmaSieve209.sigmaOne n := by
  induction fuel generalizing n with
  | zero =>
    have hnbase : n≤32753 := by norm_num at hfuel; omega
    rw [value, if_pos hnbase, hbase n hnbase]
  | succ k ih =>
    by_cases hnbase : n≤32753
    · rw [value, if_pos hnbase, hbase n hnbase]
    rw [value, if_neg hnbase]
    obtain ⟨hz,hp⟩ := hfactor n (by omega) hnH
    by_cases hp0 : factor n=0
    · rw [if_pos hp0, SigmaSieve209.sigmaOne_prime (hz hp0)]
    rw [if_neg hp0]
    obtain ⟨hpp,hpdvd⟩ := hp hp0
    have heq : factor n*(n/factor n)=n := Nat.mul_div_cancel' hpdvd
    have hmH : n/factor n≤H := (Nat.div_le_self _ _).trans hnH
    have hmfuel : n/factor n<32754*2^k := by
      have hp2 := hpp.two_le
      rw [pow_succ] at hfuel
      by_contra h
      have hlow : 32754*2^k≤n/factor n := by omega
      nlinarith only [heq,hp2,hlow,hfuel]
    have hm0 : n/factor n≠0 := by intro hh; rw [hh,mul_zero] at heq; omega
    have hmmH : n/factor n/factor n≤H := (Nat.div_le_self _ _).trans hmH
    have hmmfuel : n/factor n/factor n<32754*2^k :=
      lt_of_le_of_lt (Nat.div_le_self _ _) hmfuel
    dsimp only
    rw [ih _ hmH hmfuel]
    split_ifs with hdiv
    · rw [ih _ hmmH hmmfuel]
      have hh := SigmaSieve209.sigmaOne_mul_prime_dvd hpp hm0 hdiv
      rw [heq] at hh
      omega
    · simpa only [heq] using (SigmaSieve209.sigmaOne_mul_prime_not_dvd hpp hdiv).symm

/-- Matching the marker prevents call-by-name kernel evaluation from decoding it twice. -/
def fastValue (base factor : Nat→Nat) (fuel n : Nat) : Nat :=
  if n≤32753 then base n else
  match fuel with
  | 0 => 0
  | k+1 =>
    match factor n with
    | 0 => n+1
    | p+1 =>
      ForcedCheck209.withNat (n/(p+1)) (fun m =>
      ForcedCheck209.withNat (fastValue base factor k m) (fun sm =>
        if p+1∣m then (p+2)*sm-(p+1)*fastValue base factor k (m/(p+1))
        else (p+2)*sm))

theorem fastValue_eq (base factor : Nat→Nat) (fuel n : Nat) :
    fastValue base factor fuel n=value base factor fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ k ih =>
    by_cases hn : n≤32753
    · simp only [fastValue,value,if_pos hn]
    · simp only [fastValue,value,if_neg hn]
      cases hp : factor n with
      | zero => simp
      | succ p => simp only [Nat.add_one_ne_zero,if_false,ForcedCheck209.withNat_eq,ih,
          show p+1+1=p+2 by omega]

/-- Local finite sigma recurrence check. -/
def checkSteps (a factor : Nat→Nat) (lo : Nat) : Nat→Bool
  | 0 => true
  | k+1 =>
    ForcedCheck209.withNat (lo+k) (fun n =>
      decide (SigmaSieve209.Step a factor n) && checkSteps a factor lo k)

theorem checkSteps_sound {a factor : Nat→Nat} {lo len n : Nat}
    (hc : checkSteps a factor lo len=true) (hlo : lo≤n) (hhi : n<lo+len) :
    SigmaSieve209.Step a factor n := by
  induction len with
  | zero => omega
  | succ len ih =>
    have hh : SigmaSieve209.Step a factor (lo+len) ∧ checkSteps a factor lo len=true := by
      simpa only [checkSteps,ForcedCheck209.withNat_eq,Bool.and_eq_true_iff,decide_eq_true_eq] using hc
    by_cases hn : n=lo+len
    · simpa only [← hn] using hh.1
    · exact ih hh.2 (by omega)

#print axioms correct
#print axioms fastValue_eq
#print axioms checkSteps_sound
end JSP233.ComputedSigma209
