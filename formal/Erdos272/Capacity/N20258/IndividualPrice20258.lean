module

public import Erdos272.Capacity.N20258.ConcentratedPrice20258
public import Erdos272.Resources.N86412.StrictRunSource86412

@[expose] public section
namespace JSP233.IndividualPrice20258
open StarCompletion PrivatePairExistence SourceBridge208 IntrinsicTriples208
open scoped BigOperators Classical
set_option autoImplicit false

def physical (s e : ℕ) := FastSource208.fastPhysicalK UniformNumeric84364.phi s e

def middle (s e : ℕ) :=
  let h := (s+1)/2
  s.choose 3 - ∑ q∈Finset.Ico 2 (s-e),UniformNumeric84364.phi q*StrictRunSource86412.J s e h q

def analytic (s e : ℕ) :=
  let a := s-e
  e*((27*a*a-150*a)/100)

def value (s e : ℕ) :=
  let u := UniformNumeric84364.value s
  if e<2 then u else max u (max (analytic s e) (max (physical s e)
    (if (s+1)/2<s-e then middle s e else 0)))

private theorem phi {q : ℕ} (small : q≤256) : UniformNumeric84364.phi q=q.totient :=
  (UniformBridge84364.phi_eq (by omega)).trans (FastDecode208.phi_correct q (by omega))

theorem physical_le {S : Finset ℤ} {e : ℕ} (two : 2≤S.card) (small : S.card≤256)
    (defect : e≤Defect S) : physical S.card e≤(Pool S).card := by
  unfold physical
  rw [FastSource208.fastPhysicalK_eq (fun q hq => phi (hq.trans small)) le_rfl]
  exact actual_source_of_defect two defect

private theorem analytic_le {S : Finset ℤ} (two : 2≤S.card) (small : S.card≤256) :
    analytic S.card (Defect S)≤(Pool S).card := by
  let a := MaxAPSize S
  let u := (27*a*a-150*a)/100
  have fit : a≤256 := (maxAPSize_le_card S).trans small
  have eq : S.card-Defect S=a := by dsimp only [Defect,a]; have := maxAPSize_le_card S; omega
  simp only [analytic,eq]
  change Defect S*u≤_
  by_cases low : a<6
  · have zero : u=0 := by
      have smallProduct := Nat.mul_le_mul_right a (by omega : 27*a≤150)
      simp only [u,Nat.sub_eq_zero_of_le smallProduct,Nat.zero_div]
    simp only [zero,Nat.mul_zero,Nat.zero_le]
  have nonneg : 150*a≤27*a*a := Nat.mul_le_mul_right a (by omega : 150≤27*a)
  have unit : 100*u+150*a≤27*a*a := by
    have := Nat.div_mul_le_self (27*a*a-150*a) 100
    dsimp only [u]; omega
  exact (Nat.mul_le_mul_left _ (AnalyticCore180000.floor_small le_rfl fit (by omega) unit)).trans
    (CoreUnionSource200000.actual_union_core_source two)

private theorem middle_le {S : Finset ℤ} (four : 4≤S.card) (small : S.card≤256)
    (many : 2≤Defect S) (room : (S.card+1)/2<S.card-Defect S) : middle S.card (Defect S)≤(Pool S).card := by
  have equal : middle S.card (Defect S)=StrictRunSource86412.point S.card (Defect S) ((S.card+1)/2) := by
    dsimp only [middle,StrictRunSource86412.point]
    apply congrArg (fun z : ℕ => S.card.choose 3-z)
    apply Finset.sum_congr rfl
    intro q hq
    have bound := (Finset.mem_Ico.mp hq).2
    rw [UniformBridge84364.phi_eq (by omega : q<549)]
  rw [equal]
  exact StrictRunSource86412.actual_point_source (by omega) (by omega) many le_rfl (by omega) room

/-- The numerical fee of a size and a defect is guaranteed by that very
member. No natural defect-one price or exceptional set is assumed. -/
theorem actual {N : ℕ} {S : Finset ℤ} (cap : N≤2^18) (inside : S⊆Ground N)
    (bad : ¬IsAP S) (four : 4≤S.card) (small : S.card≤256) : value S.card (Defect S)≤(Pool S).card := by
  have uniform := UniformCardPool20258.pool_floor cap inside bad four (by omega) le_rfl le_rfl
  unfold value
  split_ifs with one room
  · exact uniform
  · exact max_le uniform (max_le (analytic_le (by omega) small)
      (max_le (physical_le (by omega) small le_rfl) (middle_le four small (by omega) room)))
  · exact max_le uniform (max_le (analytic_le (by omega) small)
      (max_le (physical_le (by omega) small le_rfl) (Nat.zero_le _)))

#print axioms actual
end JSP233.IndividualPrice20258
