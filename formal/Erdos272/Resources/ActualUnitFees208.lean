import Erdos272.Resources.ActualUnitLayer208
import Erdos272.Arithmetic.UnitRows208

namespace JSP233.ActualUnitFees208
open StarCompletion APGeometry NearAP36 SourceCertified208
open SevenFamily208 SevenPrices208 UnitNearAggregate208 ActualUnitLayer208
open CleanupMachineSound208 UnitRecipeStatic208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 200000

def Bill (M N : ℕ) (expected : ℕ→CleanupMachine208.Totals) (k : ℕ) : ℝ :=
  if k=0 then 0 else
    (N : ℝ)^2*ResidualAggregate208.Price (k+1) (ResidualTwoCensus208.H M)+
      (253/35 : ℝ)*N+(expected k).light+(N : ℝ)*((expected k).net/1000000000000 : ℝ)
def Bill242 (N k : ℕ) : ℝ := Bill 242 N UnitRows208.expected242 k
def Bill243 (N k : ℕ) : ℝ := Bill 243 N UnitRows208.expected243 k

def Facts242 (k : ℕ) : Prop := CleanupEval208.ChunkFacts
  (toRow (UnitRows208.row242 k)) 1 ((UnitRows208.row242 k).high/(242-(k+1)))
  (toTotals (UnitRows208.expected242 k))
def Facts243 (k : ℕ) : Prop := CleanupEval208.ChunkFacts
  (toRow (UnitRows208.row243 k)) 1 ((UnitRows208.row243 k).high/(243-(k+1)))
  (toTotals (UnitRows208.expected243 k))

theorem psi242_eq : psi242=potential base242 := by funext k;rfl
theorem psi243_eq : psi243=potential base243 := by funext k;rfl

theorem actual_bill242 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,242≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (k : ℕ) (hk : k<183) (hf : Facts242 k) :
    ((PoolNear A psi242 k).card : ℝ)≤Bill242 N k := by
  have hp:=UnitRows208.parameters242 k hk
  have hs:=UnitRows208.static242 k hk
  have hsmall : N<2^50 := by omega
  by_cases hk0 : k=0
  · subst k
    have he := actual_first_empty hs (by omega) (by decide : 2≤242) hsmall
      (fun n hn hsp=>cover242 hNh hn hsp) hlegal hbad hsize hsparse
    have hempty : PoolNear A psi242 0=∅ := by
      simpa only [hp.2.2.2,psi242_eq,Nat.add_sub_cancel] using he
    change ((PoolNear A psi242 0).card : ℝ)≤0
    rw [hempty]
    norm_num
  · have hb := actual_layer hs (by omega : 2≤(UnitRows208.row242 k).i) (by decide : 2≤242) hsmall
      (fun n hn hsp=>cover242 hNh hn hsp) hlegal hbad hsize hsparse
      (by simpa only [Facts242,hp.2.2.2] using hf)
      (by rw [hp.1];decide) (by rw [hp.2.1];decide) (by rw [hp.2.1];omega) (by rw [hp.2.2.1];exact hNh)
    simp only [Bill242,Bill,if_neg hk0]
    simpa only [hp.2.2.2,hp.1,Nat.add_sub_cancel,toTotals,Nat.cast_ofNat,
      psi242_eq] using hb

theorem actual_bill243 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,243≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (k : ℕ) (hk : k<184) (hf : Facts243 k) :
    ((PoolNear A psi243 k).card : ℝ)≤Bill243 N k := by
  have hp:=UnitRows208.parameters243 k hk
  have hs:=UnitRows208.static243 k hk
  have hsmall : N<2^50 := by omega
  by_cases hk0 : k=0
  · subst k
    have he := actual_first_empty hs (by omega) (by decide : 2≤243) hsmall
      (fun n hn hsp=>cover243 hNh hn hsp) hlegal hbad hsize hsparse
    have hempty : PoolNear A psi243 0=∅ := by
      simpa only [hp.2.2.2,psi243_eq,Nat.add_sub_cancel] using he
    change ((PoolNear A psi243 0).card : ℝ)≤0
    rw [hempty]
    norm_num
  · have hb := actual_layer hs (by omega : 2≤(UnitRows208.row243 k).i) (by decide : 2≤243) hsmall
      (fun n hn hsp=>cover243 hNh hn hsp) hlegal hbad hsize hsparse
      (by simpa only [Facts243,hp.2.2.2] using hf)
      (by rw [hp.1];decide) (by rw [hp.2.1];decide) (by rw [hp.2.1];omega) (by rw [hp.2.2.1];exact hNh)
    simp only [Bill243,Bill,if_neg hk0]
    simpa only [hp.2.2.2,hp.1,Nat.add_sub_cancel,toTotals,Nat.cast_ofNat,
      psi243_eq] using hb

theorem actual_unit242 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,242≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hrows : ∀k,k<183→Facts242 k)
    (harithmetic : 6*G242*(∑k∈Finset.range 183,(psi242 (k+1)-psi242 k)*Bill242 N k)≤
      U242*(N : ℝ)^2+Eta242*N+Light242) : UnitNearObligation N A G242 U242 Eta242 Light242 := by
  refine ⟨psi242,183,psi242_mono,psi242_zero,reciprocal242,?_⟩
  have hh := Finset.sum_le_sum (s := Finset.range 183) (fun k hk=>
    mul_le_mul_of_nonneg_left
      (actual_bill242 hN hNh hlegal hbad hsize hsparse k (Finset.mem_range.mp hk) (hrows k (Finset.mem_range.mp hk)))
      (sub_nonneg.mpr (psi242_mono (Nat.le_succ k))))
  exact (mul_le_mul_of_nonneg_left hh (by norm_num [G242] : 0≤6*G242)).trans harithmetic

theorem actual_unit243 {N : ℕ} {A : Finset (Finset ℤ)} (hN : 659912≤N) (hNh : N≤705097)
    (hlegal : Legal (Ground N) A) (hbad : ∀S∈A,¬IsAP S)
    (hsize : ∀S∈A,243≤S.card) (hsparse : ∀S∈A,11*S.card≤N)
    (hrows : ∀k,k<184→Facts243 k)
    (harithmetic : 6*G243*(∑k∈Finset.range 184,(psi243 (k+1)-psi243 k)*Bill243 N k)≤
      U243*(N : ℝ)^2+Eta243*N+Light243) : UnitNearObligation N A G243 U243 Eta243 Light243 := by
  refine ⟨psi243,184,psi243_mono,psi243_zero,reciprocal243,?_⟩
  have hh := Finset.sum_le_sum (s := Finset.range 184) (fun k hk=>
    mul_le_mul_of_nonneg_left
      (actual_bill243 hN hNh hlegal hbad hsize hsparse k (Finset.mem_range.mp hk) (hrows k (Finset.mem_range.mp hk)))
      (sub_nonneg.mpr (psi243_mono (Nat.le_succ k))))
  exact (mul_le_mul_of_nonneg_left hh (by norm_num [G243] : 0≤6*G243)).trans harithmetic

#print axioms actual_bill242
#print axioms actual_bill243
#print axioms actual_unit242
#print axioms actual_unit243
end
end JSP233.ActualUnitFees208
