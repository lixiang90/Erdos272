module

public import Erdos272.Arithmetic.UnitRows208
public import Erdos272.Resources.SourceCertified208
public import Erdos272.Arithmetic.ResidualTable208
public import Erdos272.Arithmetic.SevenPrices208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.UnitFeeArithmetic208
open SourceCertified208 UnitRecipeStatic208 UnitRows208 ResidualTable208 SevenPrices208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Delta (j : Fin 14) (k : ℕ) : ℕ := floorAt j (k+1)-floorAt j k

theorem delta_cast (j : Fin 14) (k : ℕ) :
    (Delta j k : ℝ)=potential j (k+1)-potential j k := by
  dsimp only [Delta,potential]
  exact Nat.cast_sub (floorAt_step j k)

structure Numbers where
  units : ℕ
  net : ℕ
  light : ℕ
  residual : ℕ
  deriving DecidableEq

def totals (j : Fin 14) (cap : ℕ) (units : ℕ→ℕ) (out : ℕ→CleanupMachine208.Totals) : Numbers :=
  ⟨∑k∈Finset.range cap,Delta j k*units (k+1),
    ∑k∈Finset.range cap,Delta j k*(out k).net,
    ∑k∈Finset.range cap,Delta j k*(out k).light,
    ∑k∈Finset.range cap,Delta j k*(if k=0 then 0 else 1)⟩

def upper (n : ℝ) (k : ℕ) (units : ℕ→ℕ) (out : ℕ→CleanupMachine208.Totals) : ℝ :=
  n^2*(units (k+1) : ℝ)/1000000000000+
    (if k=0 then 0 else (253/35 : ℝ))*n+(out k).light+n*(((out k).net : ℝ)/1000000000000)

def upper242 (N k : ℕ) : ℝ := upper N k Units242 expected242
def upper243 (N k : ℕ) : ℝ := upper N k Units243 expected243

theorem weighted_identity (j : Fin 14) (cap : ℕ) (units : ℕ→ℕ)
    (out : ℕ→CleanupMachine208.Totals) (n : ℝ) :
    (∑k∈Finset.range cap,(potential j (k+1)-potential j k)*upper n k units out)=
      n^2/1000000000000*((totals j cap units out).units : ℝ)+
      n/1000000000000*((totals j cap units out).net : ℝ)+
      ((totals j cap units out).light : ℝ)+(253/35 : ℝ)*n*((totals j cap units out).residual : ℝ) := by
  have hterm : ∀k∈Finset.range cap,(potential j (k+1)-potential j k)*upper n k units out=
      n^2/1000000000000*((Delta j k*units (k+1) : ℕ) : ℝ)+
      n/1000000000000*((Delta j k*(out k).net : ℕ) : ℝ)+
      ((Delta j k*(out k).light : ℕ) : ℝ)+
      (253/35 : ℝ)*n*((Delta j k*(if k=0 then 0 else 1) : ℕ) : ℝ) := by
    intro k hk
    rw [←delta_cast]
    unfold upper
    split_ifs <;> push_cast <;> ring
  rw [Finset.sum_congr rfl hterm]
  simp only [totals,Nat.cast_sum,Finset.sum_add_distrib,←Finset.mul_sum]

theorem numbers242 : totals base242 183 Units242 expected242=
    ⟨9302568497267474,2308133466601137870360,36815961752355856,1446874⟩ := by decide +kernel

theorem upper242_zero (N : ℕ) : upper242 N 0=0 := by
  have hu : Units242 1=0 := by decide +kernel
  have hn : (expected242 0).net=0 := by decide +kernel
  have hl : (expected242 0).light=0 := by decide +kernel
  norm_num [upper242,upper,hu,hn,hl]

theorem weighted_upper242 (N : ℕ) :
    6*G242*(∑k∈Finset.range 183,(potential base242 (k+1)-potential base242 k)*upper242 N k)≤
      U242*(N : ℝ)^2+Eta242*N+Light242 := by
  have he := weighted_identity base242 183 Units242 expected242 (N : ℝ)
  rw [numbers242] at he
  simp only [upper242]
  rw [he]
  norm_num [G242,U242,Eta242,Light242]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ)≤N)]

#print axioms numbers242
#print axioms weighted_upper242
theorem numbers243 : totals base243 184 Units243 expected243=
    ⟨9399931727549070,2339929011822162724016,37302526254993686,1468204⟩ := by decide +kernel

theorem upper243_zero (N : ℕ) : upper243 N 0=0 := by
  have hu : Units243 1=0 := by decide +kernel
  have hn : (expected243 0).net=0 := by decide +kernel
  have hl : (expected243 0).light=0 := by decide +kernel
  norm_num [upper243,upper,hu,hn,hl]

theorem weighted_upper243 (N : ℕ) :
    6*G243*(∑k∈Finset.range 184,(potential base243 (k+1)-potential base243 k)*upper243 N k)≤
      U243*(N : ℝ)^2+Eta243*N+Light243 := by
  have he := weighted_identity base243 184 Units243 expected243 (N : ℝ)
  rw [numbers243] at he
  simp only [upper243]
  rw [he]
  norm_num [G243,U243,Eta243,Light243]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ)≤N)]

#print axioms numbers243
#print axioms weighted_upper243
end
end JSP233.UnitFeeArithmetic208
