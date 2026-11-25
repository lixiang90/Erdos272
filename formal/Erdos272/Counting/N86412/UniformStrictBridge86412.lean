module

public import Erdos272.Arithmetic.N86412.TotientStrict86412
public import Erdos272.Counting.N118533.RunCount118533
public import Erdos272.Arithmetic.TotientConvolution208

@[expose] public section

namespace JSP233.UniformStrictBridge86412
open StarCompletion SourceBridge208 IntrinsicTriples208 ActualAPCount208 TripleCodes208
open APInterval208 PureSource208 TotientStrict86412
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Credit (s q : ℕ) : ℕ := if 3 ≤ q ∧ ¬q ∣ s then 1 else 0

theorem weighted_credit {s : ℕ} (hs : 3 ≤ s) :
    (∑ q ∈ Finset.Ico 2 s, Nat.totient q*Credit s q) = U s := by
  have he : Finset.Ico 2 s = insert 2 (Finset.Ico 3 s) := by
    ext q
    simp only [Finset.mem_Ico, Finset.mem_insert]
    omega
  have hnot : 2 ∉ Finset.Ico 3 s := by simp
  rw [he, Finset.sum_insert hnot]
  have hz : Credit s 2 = 0 := by norm_num [Credit]
  rw [hz, Nat.mul_zero, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro q hq
  have hq3 := (Finset.mem_Ico.mp hq).1
  by_cases hd : q ∣ s <;> simp [Credit, hq3, hd]

theorem actual_uniform_of_counts {S : Finset ℤ} (hS : 4 ≤ S.card)
    (hcounts : ∀ q ∈ Finset.Ico 2 S.card,
      (Codes S q).card+Credit S.card q ≤ intervalMultiplicity S.card q) :
    U S.card ≤ (Pool S).card := by
  let f := fun q => intervalMultiplicity S.card q-Credit S.card q
  have hc : ∀ q ∈ Finset.Ico 2 S.card, (Codes S q).card ≤ f q := by
    intro q hq
    have hh := hcounts q hq
    dsimp only [f]
    omega
  have hp := RunCount118533.actual_intrinsic_of_counts f (maxAPSize_le_card S) hc
  have heach : ∀ q ∈ Finset.Ico 2 S.card,
      Nat.totient q*f q+Nat.totient q*Credit S.card q =
        Nat.totient q*intervalMultiplicity S.card q := by
    intro q hq
    have hh := hcounts q hq
    have hle : Credit S.card q ≤ intervalMultiplicity S.card q := by omega
    have he : f q+Credit S.card q = intervalMultiplicity S.card q := Nat.sub_add_cancel hle
    exact (Nat.mul_add (Nat.totient q) (f q) (Credit S.card q)).symm.trans
      (congrArg (fun n => Nat.totient q*n) he)
  have hsum : (∑ q ∈ Finset.Ico 2 S.card, Nat.totient q*f q)+
      (∑ q ∈ Finset.Ico 2 S.card, Nat.totient q*Credit S.card q) = S.card.choose 3 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ q ∈ Finset.Ico 2 S.card, Nat.totient q*intervalMultiplicity S.card q :=
        Finset.sum_congr rfl heach
      _ = _ := TotientConvolution208.full_triple_source (by omega)
  rw [weighted_credit (by omega : 3 ≤ S.card)] at hsum
  omega

#print axioms weighted_credit
#print axioms actual_uniform_of_counts
end
end JSP233.UniformStrictBridge86412
