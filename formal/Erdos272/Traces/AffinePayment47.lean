module

public import Erdos272.Certificates.FiniteAffine47
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.AffinePayment47
open AffineWitness47 PrimorialValue47 PrimorialPrefix46 AffineTrace46 FiniteAffine47
open TraceWitnessCodes36 DyadicTraceSupply36 NearAP36 FarCore37
open scoped Classical
noncomputable section

theorem actual_primorial19_prefix (k : ℕ) (hk : k≤2^19) :
    k≤8*(PrimePrefix35.CoprimePrefix (Primorial 19) k).card+62 := by
  have hh := actual_full_block.2 k (by norm_num at hk ⊢;exact hk)
  rw [block_zero_prefix] at hh
  simpa only [actual_primorial19] using hh

theorem actual_defect19_8_le62 : AffineDefect 19 (2^19) 8≤62 := by
  unfold AffineDefect
  apply Finset.sup_le
  intro k hk
  have hh := actual_primorial19_prefix k (Finset.mem_range.mp hk).le
  omega

theorem actual_positive_modulus_row8 (m k : ℕ) (hm : 0<m)
    (hw : m.primeFactors.card≤19) (hk : k<2^19) :
    k≤8*(PrimePrefix35.CoprimePrefix m k).card+62 := by
  exact (actual_affine_row m 19 (2^19) 8 k hm hw hk).trans
    (Nat.add_le_add_left actual_defect19_8_le62 _)

theorem actual_short_prefix8 {S : Finset ℤ} {c p : ℤ} {K B : ℕ}
    (hcp : c<p) (hc : c∈S) (hp : p∈S) (hK : 0<K)
    (hhead : 2*K≤(S∩Finset.Icc c p).card)
    (htail : 4*K≤(S.filter (fun z=>p≤z)).card)
    (hneighbors : (WitnessNeighbors S c p).card≤K)
    (hno : ∀d:ℕ,0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤2^19)
    (homega : ∀z∈S,p≤z → ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤19)
    (hsize : B^2≤K) :
    2*(B-62)*K^2≤8*(B+1)*(StructuralPairs c S).card := by
  have hh := actual_short_prefix_affine hcp hc hp hK hhead htail hneighbors
    hno hB hfinite homega hsize (a:=8)
  have hs : B-62≤B-AffineDefect 19 (2^19) 8 := by
    have hd := actual_defect19_8_le62
    omega
  exact (Nat.mul_le_mul_right (K^2) (Nat.mul_le_mul_left 2 hs)).trans hh

theorem actual_no_long_right_prefix8 {S : Finset ℤ} {c : ℤ} {K B : ℕ}
    (hc : c∈S) (hK : 0<K) (hright : 8*K≤(S.filter (fun x=>c<x)).card)
    (hno : ∀d:ℕ,0<d → ¬Prefix c d K⊆S)
    (hB : 0<B) (hfinite : K≤2^19)
    (homega : ∀p∈S,c<p → ∀z∈S,p≤z →
      ((p-c).natAbs*(z-c).natAbs).primeFactors.card≤19)
    (hsize : B^2≤K) :
    2*(B-62)*K^2≤8*(B+1)*(StructuralPairs c S).card := by
  have hh := actual_no_long_right_prefix_affine hc hK hright hno
    (by norm_num : 4≤8) hB hfinite homega hsize
  have hs : B-62≤B-AffineDefect 19 (2^19) 8 := by
    have hd := actual_defect19_8_le62
    omega
  exact (Nat.mul_le_mul_right (K^2) (Nat.mul_le_mul_left 2 hs)).trans hh

#print axioms actual_primorial19_prefix
#print axioms actual_defect19_8_le62
#print axioms actual_positive_modulus_row8
#print axioms actual_short_prefix8
#print axioms actual_no_long_right_prefix8
end
end JSP233.AffinePayment47
