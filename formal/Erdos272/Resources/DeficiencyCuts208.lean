import Erdos272.Resources.SevenFamily208
import Erdos272.Resources.UniformActualWindow209

namespace JSP233.DeficiencyCuts208
open StarCompletion APGeometry SourceBridge208 SourceCertified208 SourcePrefixSpecs208
open SevenFamily208 UniformPotential208 UniformActualWindow209
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

theorem actual_unit_cut {A : Finset (Finset ℤ)} {psi : ℕ→ℝ} {k e : ℕ} {S : Finset ℤ}
    (j : Fin 14) (hS : S∈PoolNear A psi k) (hs : rowStart j≤S.card) (hhi : S.card<2^50)
    (hq : psi (k+1)≤(floorAt j e : ℝ)) : Defect S<min e 184 := by
  have hnear := (Finset.mem_filter.mp hS).2
  by_contra he
  have hb := SourceCertified208.actual_source j hs hhi (by omega : min e 184≤Defect S)
  have hbR : (floorAt j e : ℝ)≤(IntrinsicTriples208.Pool S).card := by exact_mod_cast hb
  linarith only [hnear,hq,hbR]

theorem actual_uniform_cut242 {N : ℕ} {A : Finset (Finset ℤ)} {psi : ℕ→ℝ}
    {k v : ℕ} {S : Finset ℤ} (i : Fin 183) (b : Fin 7)
    (hhigh : N≤720896) (hground : S⊆Ground N) (hcard : 31≤S.card) (hv : 1≤v)
    (hsize : v*(edges242[i.val]!)[b.val]!≤S.card)
    (hq : psi (k+1)≤(heights242[i.val+1]! : ℝ))
    (hS : S∈JointNear N A v 242 psi k) : Defect S<v*(cuts242[i.val]!)[b.val]! := by
  have hnear := (Finset.mem_filter.mp hS).2
  by_contra hsmall
  have hdef : (v : ℝ)*((cuts242[i.val]!)[b.val]! : ℝ)≤(Defect S : ℝ) := by
    exact_mod_cast (show v*(cuts242[i.val]!)[b.val]!≤Defect S by omega)
  have hvR : (1 : ℝ)≤v := by exact_mod_cast hv
  have hv0 : (0 : ℝ)<v := by linarith only [hvR]
  have hy : ((edges242[i.val]!)[b.val]! : ℝ)≤(S.card : ℝ)/v := by
    apply (le_div_iff₀ hv0).mpr
    have hh : (v : ℝ)*((edges242[i.val]!)[b.val]! : ℝ)≤S.card := by exact_mod_cast hsize
    nlinarith only [hh]
  have heq : (S.card : ℝ)=(v : ℝ)*((S.card : ℝ)/v) := by field_simp
  have hp := actual_row242 hhigh hground hcard i b hvR hy heq hdef
  have hqpay := mul_le_mul_of_nonneg_left hq (sq_nonneg (v : ℝ))
  linarith only [hnear,hp,hqpay]

theorem actual_uniform_cut243 {N : ℕ} {A : Finset (Finset ℤ)} {psi : ℕ→ℝ}
    {k v : ℕ} {S : Finset ℤ} (i : Fin 184) (b : Fin 7)
    (hhigh : N≤720896) (hground : S⊆Ground N) (hcard : 31≤S.card) (hv : 1≤v)
    (hsize : v*(edges243[i.val]!)[b.val]!≤S.card)
    (hq : psi (k+1)≤(heights243[i.val+1]! : ℝ))
    (hS : S∈JointNear N A v 243 psi k) : Defect S<v*(cuts243[i.val]!)[b.val]! := by
  have hnear := (Finset.mem_filter.mp hS).2
  by_contra hsmall
  have hdef : (v : ℝ)*((cuts243[i.val]!)[b.val]! : ℝ)≤(Defect S : ℝ) := by
    exact_mod_cast (show v*(cuts243[i.val]!)[b.val]!≤Defect S by omega)
  have hvR : (1 : ℝ)≤v := by exact_mod_cast hv
  have hv0 : (0 : ℝ)<v := by linarith only [hvR]
  have hy : ((edges243[i.val]!)[b.val]! : ℝ)≤(S.card : ℝ)/v := by
    apply (le_div_iff₀ hv0).mpr
    have hh : (v : ℝ)*((edges243[i.val]!)[b.val]! : ℝ)≤S.card := by exact_mod_cast hsize
    nlinarith only [hh]
  have heq : (S.card : ℝ)=(v : ℝ)*((S.card : ℝ)/v) := by field_simp
  have hp := actual_row243 hhigh hground hcard i b hvR hy heq hdef
  have hqpay := mul_le_mul_of_nonneg_left hq (sq_nonneg (v : ℝ))
  linarith only [hnear,hp,hqpay]

#print axioms actual_unit_cut
#print axioms actual_uniform_cut242
#print axioms actual_uniform_cut243
end
end JSP233.DeficiencyCuts208
