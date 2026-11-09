module

public import Erdos272.Arithmetic.N291012.PrefixChecks291012
public import Erdos272.Arithmetic.N291012.SourceMoment291012
public import Erdos272.Arithmetic.FastDecode208

@[expose] public section

namespace JSP233.PrefixTableSound291012
open SourceMoment291012 PureSource208
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem lookup_phi (n : ℕ) : PrefixLookup291012.phi n = FastDecode208.phi n := by
  rw [FastDecode208.phi_eq]
  rfl

theorem check_sound {p q : ℕ → ℕ} {lo len n : ℕ}
    (hc : Check p q lo len = true) (hlo : lo ≤ n) (hhi : n < lo+len) :
    p (n+1) = p n + FastDecode208.phi n ∧
      q (n+1) = q n + n * FastDecode208.phi n := by
  have hj : n-lo ∈ List.range len := by simp only [List.mem_range]; omega
  have hh := (List.all_eq_true.mp hc) (n-lo) hj
  have he : lo+(n-lo) = n := by omega
  simpa only [he, decide_eq_true_eq, lookup_phi] using hh

theorem recurrence_correct {p q : ℕ → ℕ} {H : ℕ}
    (hH : H ≤ 32753) (hp : p 0 = 0) (hq : q 0 = 0)
    (hrec : ∀ n, n < H →
      p (n+1) = p n + FastDecode208.phi n ∧
        q (n+1) = q n + n * FastDecode208.phi n) :
    ∀ n, n ≤ H → p n = Prefix Nat.totient n ∧ q n = Moment Nat.totient n := by
  intro n
  induction n with
  | zero => intro _; simpa [Prefix, Moment] using And.intro hp hq
  | succ n ih =>
    intro hn
    have hprev := ih (by omega : n ≤ H)
    have hr := hrec n (by omega)
    have hphi := FastDecode208.phi_correct n (by omega)
    constructor
    · simpa only [Nat.succ_eq_add_one, Prefix, Finset.sum_range_succ,
        hphi, hprev.1] using hr.1
    · simpa only [Nat.succ_eq_add_one, Moment, Finset.sum_range_succ,
        hphi, hprev.2] using hr.2

theorem floor_sound {p q : ℕ → ℕ} {H lo hi e b : ℕ}
    (htable : ∀ n, n ≤ H → p n = Prefix Nat.totient n ∧ q n = Moment Nat.totient n)
    (he : e ≤ lo) (hhi : hi ≤ H) (hc : FloorCheck p q lo hi e b = true)
    {s : ℕ} (hslo : lo ≤ s) (hshi : s ≤ hi) : b ≤ physicalK s e := by
  have hj : s-lo ∈ List.range (hi+1-lo) := by simp only [List.mem_range]; omega
  have hh := (List.all_eq_true.mp hc) (s-lo) hj
  have heq : lo+(s-lo) = s := by omega
  have hv : b ≤ Value p q s e := by
    simpa only [heq, decide_eq_true_eq, PrefixLookup291012.Value, SourceMoment291012.Value] using hh
  have hs := htable s (hshi.trans hhi)
  have ht := htable (s-e) ((Nat.sub_le s e).trans (hshi.trans hhi))
  have hvalue : Value p q s e = Value (Prefix Nat.totient) (Moment Nat.totient) s e := by
    simp only [Value, hs.1, hs.2, ht.1, ht.2]
  rw [hvalue] at hv
  exact hv.trans (value_lower (he.trans hslo))

#print axioms lookup_phi
#print axioms check_sound
#print axioms recurrence_correct
#print axioms floor_sound
end JSP233.PrefixTableSound291012
