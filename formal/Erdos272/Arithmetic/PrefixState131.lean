import Erdos272.Arithmetic.PairWeighted131
import Erdos272.Arithmetic.EndpointEval131

namespace JSP233.PrefixState131
open PairWeighted131 SimplexMoment57
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure State where
  logLo : ℕ
  logHi : ℕ
  aLo : ℕ
  aHi : ℕ
  jLo : ℕ
  jHi : ℕ
  sHi : ℕ
  t : ℕ
  deriving DecidableEq, Repr

structure Row where
  tau : ℕ
  logLo : ℕ
  logHi : ℕ
  sqrtHi : ℕ
  deriving DecidableEq, Repr

def next (G n : ℕ) (s : State) (r : Row) : State :=
  let l := s.logLo+r.logLo
  let h := s.logHi+r.logHi
  ⟨l,h,s.aLo+G*r.tau/n,s.aHi+(G*r.tau/n+1),
    s.jLo+r.tau*l/n,s.jHi+(r.tau*h/n+1),s.sHi+r.tau*r.sqrtHi,s.t+r.tau⟩

noncomputable section
open scoped Classical

def Valid (G n : ℕ) (s : State) : Prop :=
  (s.logLo:ℝ)≤(G:ℝ)*Real.log n ∧ (G:ℝ)*Real.log n≤s.logHi ∧
  (s.aLo:ℝ)≤(G:ℝ)*A n ∧ (G:ℝ)*A n≤s.aHi ∧
  (s.jLo:ℝ)≤(G:ℝ)*J n ∧ (G:ℝ)*J n≤s.jHi ∧
  (G:ℝ)*S n≤s.sHi ∧ s.t=DivCount 1 n

theorem quotient_bounds (a n : ℕ) (hn : 0<n) :
    ((a/n:ℕ):ℝ)≤(a:ℝ)/n ∧ (a:ℝ)/n≤((a/n+1:ℕ):ℝ) := by
  refine ⟨Nat.cast_div_le,?_⟩
  apply (div_le_iff₀ (Nat.cast_pos.mpr hn)).mpr
  have he : (n:ℝ)*(a/n:ℕ)+(a%n:ℕ)=(a:ℝ) := by exact_mod_cast Nat.div_add_mod a n
  have hm : ((a%n:ℕ):ℝ)<n := by exact_mod_cast Nat.mod_lt a hn
  push_cast
  nlinarith only [he,hm]

theorem sqrt_upper_scaled {G n r : ℕ} (hn : 0<n) (h : G^2≤r^2*n) :
    (G:ℝ)/Real.sqrt n≤r := by
  have hn0 : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hs := Real.sq_sqrt hn0.le
  have hh : (G:ℝ)^2≤(r:ℝ)^2*n := by exact_mod_cast h
  have hsq : (G:ℝ)^2≤((r:ℝ)*Real.sqrt n)^2 := by nlinarith only [hs,hh]
  have hg : (G:ℝ)≤(r:ℝ)*Real.sqrt n :=
    (sq_le_sq₀ (Nat.cast_nonneg G) (by positivity)).mp hsq
  exact (div_le_iff₀ (Real.sqrt_pos.mpr hn0)).mpr hg

theorem a_succ (m : ℕ) : A (m+1)=A m+((m+1).divisors.card:ℝ)/(m+1) := by
  dsimp only [A]
  rw [Finset.sum_Icc_succ_top (by omega : 1≤m+1)]
  push_cast
  rfl

theorem j_succ (m : ℕ) : J (m+1)=J m+((m+1).divisors.card:ℝ)*Real.log (m+1)/(m+1) := by
  dsimp only [J]
  rw [Finset.sum_Icc_succ_top (by omega : 1≤m+1)]
  push_cast
  rfl

theorem s_succ (m : ℕ) : S (m+1)=S m+((m+1).divisors.card:ℝ)/Real.sqrt (m+1) := by
  dsimp only [S]
  rw [Finset.sum_Icc_succ_top (by omega : 1≤m+1)]
  push_cast
  rfl

theorem next_valid {G m : ℕ} {s : State} {r : Row}
    (hG : 0<G) (hm : 1≤m) (hs : Valid G m s)
    (ht : r.tau=(m+1).divisors.card)
    (hl : (r.logLo:ℝ)/(G:ℝ)≤Real.log (m+1)-Real.log m)
    (hu : Real.log (m+1)-Real.log m≤(r.logHi:ℝ)/(G:ℝ))
    (hr : G^2≤r.sqrtHi^2*(m+1)) : Valid G (m+1) (next G (m+1) s r) := by
  obtain ⟨hll,hlh,hal,hah,hjl,hjh,hsh,htt⟩ := hs
  have hGp : (0:ℝ)<G := Nat.cast_pos.mpr hG
  have hn : (0:ℝ)<m+1 := by positivity
  have hl' := (div_le_iff₀ hGp).mp hl
  have hu' := (le_div_iff₀ hGp).mp hu
  have qa := quotient_bounds (G*r.tau) (m+1) (by omega)
  have qjl := quotient_bounds (r.tau*(s.logLo+r.logLo)) (m+1) (by omega)
  have qjh := quotient_bounds (r.tau*(s.logHi+r.logHi)) (m+1) (by omega)
  have qsr := sqrt_upper_scaled (by omega : 0<m+1) hr
  have hlnew : ((s.logLo+r.logLo:ℕ):ℝ)≤(G:ℝ)*Real.log (m+1) := by
    push_cast
    nlinarith only [hll,hl']
  have hunew : (G:ℝ)*Real.log (m+1)≤((s.logHi+r.logHi:ℕ):ℝ) := by
    push_cast
    nlinarith only [hlh,hu']
  have htm : (r.tau:ℝ)=((m+1).divisors.card:ℝ) := by rw [ht]
  have hjl' := mul_le_mul_of_nonneg_left hlnew (show 0≤(r.tau:ℝ)/(m+1) by positivity)
  have hjh' := mul_le_mul_of_nonneg_left hunew (show 0≤(r.tau:ℝ)/(m+1) by positivity)
  have hsu := mul_le_mul_of_nonneg_left qsr (Nat.cast_nonneg r.tau)
  dsimp only [Valid,next]
  push_cast at hlnew hunew ⊢
  refine ⟨hlnew,hunew,?_,?_,?_,?_,?_,?_⟩
  · rw [a_succ]
    push_cast at qa ⊢
    rw [←htm]
    convert add_le_add hal qa.1 using 1 <;> first | rfl | ring
  · rw [a_succ]
    push_cast at qa ⊢
    rw [←htm]
    convert add_le_add hah qa.2 using 1 <;> first | rfl | ring
  · rw [j_succ]
    push_cast at qjl hjl' ⊢
    rw [←htm]
    have hh : ((r.tau*(s.logLo+r.logLo)/(m+1):ℕ):ℝ)≤
        (G:ℝ)*((r.tau:ℝ)*Real.log (m+1)/(m+1)) := by
      apply qjl.1.trans
      convert hjl' using 1 <;> first | rfl | ring
    convert add_le_add hjl hh using 1 <;> first | rfl | ring
  · rw [j_succ]
    push_cast at qjh hjh' ⊢
    rw [←htm]
    have hh : (G:ℝ)*((r.tau:ℝ)*Real.log (m+1)/(m+1))≤
        ((r.tau*(s.logHi+r.logHi)/(m+1):ℕ):ℝ)+1 := by
      apply le_trans _ qjh.2
      convert hjh' using 1 <;> first | rfl | ring
    convert add_le_add hjh hh using 1 <;> first | rfl | ring
  · rw [s_succ]
    push_cast at hsu ⊢
    rw [←htm]
    convert add_le_add hsh hsu using 1 <;> first | rfl | ring
  · rw [htt,ht,EndpointEval131.d1_successor]

#print axioms quotient_bounds
#print axioms sqrt_upper_scaled
#print axioms a_succ
#print axioms j_succ
#print axioms s_succ
#print axioms next_valid
end
end JSP233.PrefixState131
