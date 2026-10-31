import Erdos272.Arithmetic.UnitFeeArithmetic208
import Erdos272.Resources.UnitNearAggregate208
import Erdos272.Resources.TruncatedAPResponse209
import Erdos272.Arithmetic.ReciprocalPrice208

namespace JSP233.TruncatedUnitPrices209
open SourceCertified208 UnitRecipeStatic208 UnitRows208 ResidualTable208
open UnitFeeArithmetic208 UnitNearAggregate208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def G : ℝ := 1/6164376
def U : ℝ := 641/100000
def Eta : ℝ := 1510
def Light : ℝ := 18160000000

theorem numbers150 : totals base242 150 Units242 expected242 =
    ⟨6580583760816304,1541873010325583270874,18657477732744756,1027324⟩ := by
  decide +kernel

theorem potential150 : floorAt base242 150 = 1027396 := by decide +kernel

theorem psi_eq (k : ℕ) : psi242 k = potential base242 k := rfl

theorem reciprocal : 6*G*psi242 150 = 1 := by
  rw [psi_eq]
  norm_num [G,potential,potential150]

theorem nonneg : 0 ≤ G ∧ 0 ≤ U ∧ 0 ≤ Eta ∧ 0 ≤ Light := by
  norm_num [G,U,Eta,Light]

theorem weighted_upper150 (N : ℕ) :
    6*G*(∑ k ∈ Finset.range 150,(psi242 (k+1)-psi242 k)*UnitFeeArithmetic208.upper242 N k) ≤
      U*(N : ℝ)^2+Eta*N+Light := by
  have he := weighted_identity base242 150 Units242 expected242 (N : ℝ)
  rw [numbers150] at he
  simp only [psi_eq,UnitFeeArithmetic208.upper242]
  rw [he]
  norm_num [G,U,Eta,Light]
  nlinarith only [(Nat.cast_nonneg N : (0 : ℝ) ≤ N),sq_nonneg (N : ℝ)]

theorem actual_price {N : ℕ} (hlo : 659912 ≤ N) (hhi : N ≤ 705097) :
    G*(N : ℝ) ≤ TruncatedAPResponse209.T ∧
    TruncatedAPResponse209.Kappa*G*(N : ℝ)+U+
      (Eta+142+968)/(N : ℝ)+Light/(N : ℝ)^2 < (71/800 : ℝ) := by
  have hl : (659912 : ℝ) ≤ N := by exact_mod_cast hlo
  have hh : (N : ℝ) ≤ 705097 := by exact_mod_cast hhi
  constructor
  · norm_num [G,TruncatedAPResponse209.T]
    linarith only [hh]
  · have hw := ReciprocalPrice208.window
      (a:=TruncatedAPResponse209.Kappa*G) (b:=U) (c:=Eta+142+968)
      (s:= -Light) (lo:=659912) (hi:=705097) (x:=(N : ℝ))
      (budget:=(887/10000 : ℝ)) (by norm_num) hl hh
      (by norm_num [Eta]) (by norm_num [Eta,Light])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,U,Eta,Light])
      (by norm_num [ReciprocalPrice208.Price,TruncatedAPResponse209.Kappa,G,U,Eta,Light])
    have he : ReciprocalPrice208.Price (TruncatedAPResponse209.Kappa*G) U
        (Eta+142+968) (-Light) (N : ℝ) =
        TruncatedAPResponse209.Kappa*G*(N : ℝ)+U+
          (Eta+142+968)/(N : ℝ)+Light/(N : ℝ)^2 := by
      simp only [ReciprocalPrice208.Price,neg_div,sub_neg_eq_add]
    rw [he] at hw
    linarith only [hw]

#print axioms numbers150
#print axioms reciprocal
#print axioms weighted_upper150
#print axioms actual_price
end
end JSP233.TruncatedUnitPrices209
