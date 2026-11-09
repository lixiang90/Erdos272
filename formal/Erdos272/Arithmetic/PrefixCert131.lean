module

public import Erdos272.Arithmetic.PrefixState131
public import Erdos272.Arithmetic.LogIncrement131

@[expose] public section
namespace JSP233.PrefixCert131
open PrefixState131 EndpointEval131 LogIncrement131
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def rowCheck (G n : ℕ) (r : Row) : Bool :=
  decide (tauEval n=r.tau) && stepCheck G n r.logLo r.logHi &&
    decide (G^2≤r.sqrtHi^2*n)

def chunkCheck (G n : ℕ) (s : State) : List Row → State → Bool
  | [],e => decide (s=e)
  | r::rs,e => rowCheck G (n+1) r && chunkCheck G (n+1) (next G (n+1) s r) rs e

noncomputable section
open scoped Classical

theorem row_check_sound {G n : ℕ} {r : Row} (hn : 2≤n) (hG : 0<G)
    (h : rowCheck G n r=true) :
    r.tau=n.divisors.card ∧
      (r.logLo:ℝ)/(G:ℝ)≤Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ) ∧
      Real.log (n:ℝ)-Real.log ((n-1:ℕ):ℝ)≤(r.logHi:ℝ)/(G:ℝ) ∧
      G^2≤r.sqrtHi^2*n := by
  simp only [rowCheck,Bool.and_eq_true,decide_eq_true_eq] at h
  obtain ⟨⟨ht,hl⟩,hr⟩ := h
  have hh := log_step_cert_sound hn hG hl
  refine ⟨?_,hh.1,hh.2,hr⟩
  rw [←ht,tauEval_sound]

theorem chunk_sound {G n : ℕ} {s e : State} (rs : List Row)
    (hG : 0<G) (hn : 1≤n) (hs : Valid G n s)
    (hc : chunkCheck G n s rs e=true) : Valid G (n+rs.length) e := by
  induction rs generalizing n s with
  | nil =>
    simp only [chunkCheck,decide_eq_true_eq] at hc
    simpa only [List.length_nil,Nat.add_zero,hc] using hs
  | cons r rs ih =>
    simp only [chunkCheck,Bool.and_eq_true] at hc
    obtain ⟨ht,hl,hu,hr⟩ := row_check_sound (by omega : 2≤n+1) hG hc.1
    have hl' : (r.logLo:ℝ)/(G:ℝ)≤Real.log ((n:ℝ)+1)-Real.log (n:ℝ) := by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hl
    have hu' : Real.log ((n:ℝ)+1)-Real.log (n:ℝ)≤(r.logHi:ℝ)/(G:ℝ) := by
      simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one] using hu
    have hv := next_valid hG hn hs ht hl' hu' hr
    have hh := ih (n:=n+1) (s:=next G (n+1) s r) (by omega) hv hc.2
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem valid_one (G : ℕ) : Valid G 1 ⟨0,0,G,G,0,0,G,1⟩ := by
  simp [Valid,PairWeighted131.A,PairWeighted131.J,PairWeighted131.S,
    SimplexMoment57.DivCount]

#print axioms row_check_sound
#print axioms chunk_sound
#print axioms valid_one
end
end JSP233.PrefixCert131
