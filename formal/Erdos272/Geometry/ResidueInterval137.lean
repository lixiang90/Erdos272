module

public import Erdos272.Geometry.DensePhase137
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.ResidueInterval137
open StarCompletion APGeometry
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def ResidueInterval (lo hi:ℤ) (d:ℕ) (p:ℤ) : Finset ℤ :=
  (Finset.Icc lo hi).filter (fun y=>(d:ℤ)∣y-p)
def ResidueOutside (N:ℕ) (L R:ℤ) (d:ℕ) (p:ℤ) : Finset ℤ :=
  (Ground N\Finset.Icc L R).filter (fun y=>(d:ℤ)∣y-p)

theorem residue_interval_mass (lo hi p:ℤ) {d:ℕ} (hd:0<d) :
    d*(ResidueInterval lo hi d p).card≤(hi-lo+1).toNat+(d-1) := by
  let C:=ResidueInterval lo hi d p
  change d*C.card≤(hi-lo+1).toNat+(d-1)
  by_cases hne:C.Nonempty
  · have hAP:APAt (d:ℤ) p C:=by
      refine ⟨by exact_mod_cast hd,lo,hi,?_⟩
      intro y
      simp only [C,ResidueInterval,Finset.mem_filter,Finset.mem_Icc]
      tauto
    have hspan:=apAt_span_eq hAP hne
    have hlo:=Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.min'_mem C hne)).1
    have hhi:=Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.max'_mem C hne)).1
    have hn:((hi-lo+1).toNat:ℤ)=hi-lo+1:=Int.toNat_of_nonneg (by omega)
    have hd1:1≤d:=by omega
    have hbound:((d*C.card:ℕ):ℤ)≤(((hi-lo+1).toNat+(d-1):ℕ):ℤ):=by
      rw [Nat.cast_mul,Nat.cast_add,Nat.cast_sub hd1,Nat.cast_one]
      nlinarith only [hspan,hlo.1,hhi.2,hn]
    exact_mod_cast hbound
  · have he:C=∅:=Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he]
    simp

theorem residue_outside_mass {N L R d:ℕ} (hL:1≤L) (hLR:L≤R) (hRN:R≤N)
    (hd:0<d) (p:ℤ) :
    d*(ResidueOutside N (L:ℤ) (R:ℤ) d p).card≤(L-1)+(N-R)+2*(d-1) := by
  let A:=ResidueInterval (1:ℤ) ((L:ℤ)-1) d p
  let B:=ResidueInterval ((R:ℤ)+1) (N:ℤ) d p
  have he:ResidueOutside N (L:ℤ) (R:ℤ) d p=A∪B:=by
    ext y
    simp only [ResidueOutside,A,B,ResidueInterval,Finset.mem_filter,
      Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_union,mem_ground]
    omega
  have hdj:Disjoint A B:=by
    apply Finset.disjoint_left.mpr
    intro y ha hb
    have ha':=Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hb':=Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1
    omega
  have ha:=residue_interval_mass 1 ((L:ℤ)-1) p hd
  have hb:=residue_interval_mass ((R:ℤ)+1) (N:ℤ) p hd
  have hleft:(((L:ℤ)-1)-1+1).toNat=L-1:=by omega
  have hright:((N:ℤ)-((R:ℤ)+1)+1).toNat=N-R:=by omega
  rw [hleft] at ha
  rw [hright] at hb
  rw [he,Finset.card_union_of_disjoint hdj,Nat.mul_add]
  change d*A.card+d*B.card≤(L-1)+(N-R)+2*(d-1)
  change d*A.card≤(L-1)+(d-1) at ha
  change d*B.card≤(N-R)+(d-1) at hb
  omega

#print axioms residue_interval_mass
#print axioms residue_outside_mass
end
end JSP233.ResidueInterval137
