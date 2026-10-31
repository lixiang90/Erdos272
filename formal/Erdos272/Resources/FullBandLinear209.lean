import Erdos272.Resources.FullBandCleanup209
import Erdos272.Arithmetic.HeavyFiniteSums209

namespace JSP233.FullBandLinear209
open StarCompletion APGeometry NearAP36 SourceBridge208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208 CrossBandMenu208
open FullBandGeometry209 FullBandCredit209 FullBandCleanup209 HeavyFiniteSums209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 200000

def Active (E : Band→ℕ) : Finset Band := Finset.univ.filter fun b=>1<E b
def aData (T E : Band→ℕ) (b : Band) : ℕ := T b-E b
def vData (U B : Band→ℕ) (b : Band) : ℕ := U b+B b-3
def hData (U B : Band→ℕ) (b : Band) : ℕ := (vData U B b-1)/B b+1
def spanData (U B : Band→ℕ) (b : Band) : ℕ := vData U B b+(vData U B b-1)/B b*B b
def middleData (T E U B : Band→ℕ) (b : Band) : ℕ :=
  LightClosed208.Count (vData U B b-E b-1) (aData T E b) (B b)*(vData U B b-T b)
def Coefficient (e : ℕ) (T E U B : Band→ℕ) (j : Band→Band→ℕ) : ℝ :=
  HeavyFiniteSums209.Coefficient (Active E) e (aData T E) (hData U B) (spanData U B) j+
    (∑b∈Active E,(middleData T E U B b : ℝ)/(aData T E b : ℝ))

theorem actual_linear (s : System) (v : Valid s) (T E U B : Band→ℕ) (j : Band→Band→ℕ)
    (hN : 0<s.N) (hET : ∀b,E b<T b) (hTU : ∀b,T b<U b) (hB : ∀b,2≤B b)
    (hfixed : ∀d∈Finset.Icc 1 s.D,∀b : Band,
      s.T d b=T b ∧ s.E d b=E b ∧ s.U d b=U b ∧ s.B d b=B b) :
    CleanupTotal s+MiddleTotal s≤(s.N : ℝ)*Coefficient s.e T E U B j := by
  have hA : ∀b,0<aData T E b := fun b=>Nat.sub_pos_of_lt (hET b)
  have hV : ∀b,0<vData U B b := by intro b;have := hET b;have := hTU b;have := hB b;dsimp only [vData];omega
  have hSpan : ∀b,0<spanData U B b := by intro b;exact (hV b).trans_le (Nat.le_add_right _ _)
  have hempty : ∀d∈Finset.Icc 1 s.D,∀b : Band,¬aData T E b≤s.N/d→Full s d b=∅ := by
    intro d hd b ha
    have hp:=piece_extinction s v hd b (by simpa only [(hfixed d hd b).1,(hfixed d hd b).2.1,aData] using Nat.lt_of_not_ge ha)
    simp only [Full,FullHeavySplit209.Full,Codes,hp,Finset.image_empty,Finset.filter_empty]
  have hinactive : ∀d∈Finset.Icc 1 s.D,∀b : Band,b∉Active E→
      (Full s d b).card=0 ∧ Raw s d b=0 ∧ MiddleFee s d b=0 := by
    intro d hd b hb
    have he : E b≤1 := by
      by_contra h
      exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
    have hs : s.E d b≤1 := by simpa only [(hfixed d hd b).2.1] using he
    have hp:=ActualBandEval208.actual_piece_empty v hd b hs
    have hf : Full s d b=∅ := by simp only [Full,FullHeavySplit209.Full,Codes,hp,Finset.image_empty,Finset.filter_empty]
    simp only [hf,Finset.card_empty,Raw,Finset.biUnion_empty,MiddleFee,if_pos hs,and_self]
  have hpoint : ∀d∈Finset.Icc 1 s.D,∀b : Band,
      ((Full s d b).card : ℝ)≤CountAt s.N (aData T E b) (hData U B b) d ∧
      (Raw s d b : ℝ)≤WindowAt s.N (aData T E b) (spanData U B b) d := by
    intro d hd b
    by_cases ha : aData T E b≤s.N/d
    · have hg:=FullBandGeometry209.actual_full_geometry s v hd b
      have hv : SizeV s d b=vData U B b := by simp only [SizeV,(hfixed d hd b).2.2.1,(hfixed d hd b).2.2.2,vData]
      have hspan : FullBandGeometry209.Span s d b=spanData U B b := by simp only [FullBandGeometry209.Span,hv,(hfixed d hd b).2.2.2,spanData]
      have hc : (Full s d b).card≤hData U B b := by simpa only [hv,(hfixed d hd b).2.2.2,hData] using hg.1
      have hw : Raw s d b≤min (spanData U B b) (s.N/d+1) := by simpa only [Raw,hspan] using hg.2
      simp only [CountAt,WindowAt,if_pos ha]
      exact ⟨by exact_mod_cast hc,by exact_mod_cast hw⟩
    · have hf:=hempty d hd b ha
      simp only [hf,Finset.card_empty,Raw,Finset.biUnion_empty,Nat.cast_zero,CountAt,WindowAt,if_neg ha,le_refl,and_self]
  have hMajor : CleanupTotal s≤Major (Active E) s.N s.D s.e (aData T E) (hData U B) (spanData U B) := by
    rw [major_product]
    unfold CleanupTotal
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro d hd
    have hheq : (∑b : Band,((Full s d b).card : ℝ))=∑b∈Active E,((Full s d b).card : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b hb hn
      simp only [(hinactive d hd b hn).1,Nat.cast_zero]
    have hweq : (∑b : Band,(Raw s d b : ℝ))=∑b∈Active E,(Raw s d b : ℝ) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro b hb hn
      simp only [(hinactive d hd b hn).2.1,Nat.cast_zero]
    have hh : (((∑b : Band,(Full s d b).card) : ℕ) : ℝ)≤∑b∈Active E,CountAt s.N (aData T E b) (hData U B b) d := by
      rw [Nat.cast_sum,hheq]
      exact Finset.sum_le_sum (fun b hb=>(hpoint d hd b).1)
    have hw : (((∑b : Band,Raw s d b) : ℕ) : ℝ)+((s.e-1 : ℕ) : ℝ)≤
        (∑b∈Active E,WindowAt s.N (aData T E b) (spanData U B b) d)+(s.e : ℝ) := by
      have hsmall : ((s.e-1 : ℕ) : ℝ)≤(s.e : ℝ) := by exact_mod_cast Nat.sub_le s.e 1
      have hsum : (((∑b : Band,Raw s d b) : ℕ) : ℝ)≤∑b∈Active E,WindowAt s.N (aData T E b) (spanData U B b) d := by
        rw [Nat.cast_sum,hweq]
        exact Finset.sum_le_sum (fun b hb=>(hpoint d hd b).2)
      linarith only [hsmall,hsum]
    have h0 : (0 : ℝ)≤∑b∈Active E,CountAt s.N (aData T E b) (hData U B b) d :=
      Finset.sum_nonneg (fun b hb=>countAt_nonneg _ _ _ _)
    have hm:=mul_le_mul hh hw (by positivity) h0
    simpa only [Nat.cast_mul,Nat.cast_add] using hm
  have hMid : MiddleTotal s≤(s.N : ℝ)*(∑b∈Active E,(middleData T E U B b : ℝ)/(aData T E b : ℝ)) := by
    have heq : MiddleTotal s=∑b∈Active E,∑d∈Finset.Icc 1 s.D,CountAt s.N (aData T E b) (middleData T E U B b) d := by
      unfold MiddleTotal
      rw [Finset.sum_comm]
      have hc : (∑b : Band,∑d∈Finset.Icc 1 s.D,(MiddleFee s d b : ℝ))=
          ∑b∈Active E,∑d∈Finset.Icc 1 s.D,(MiddleFee s d b : ℝ) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro b hb hn
        apply Finset.sum_eq_zero
        intro d hd
        simp only [(hinactive d hd b hn).2.2,Nat.cast_zero]
      rw [hc]
      apply Finset.sum_congr rfl
      intro b hb
      have hE1 : ¬E b≤1 := by have := (Finset.mem_filter.mp hb).2;omega
      apply Finset.sum_congr rfl
      intro d hd
      have hf : MiddleFee s d b=if aData T E b≤s.N/d then middleData T E U B b else 0 := by
        simp only [MiddleFee,(hfixed d hd b).2.1,if_neg hE1,(hfixed d hd b).1,
          Period,SizeV,(hfixed d hd b).2.2.1,(hfixed d hd b).2.2.2,aData,middleData,vData]
        rfl
      rw [hf]
      unfold CountAt
      split_ifs <;> simp only [Nat.cast_zero]
    rw [heq]
    have hs:=Finset.sum_le_sum (fun b (hb : b∈Active E)=>active_sum s.N s.D (aData T E b) (middleData T E U B b) (hA b))
    simpa only [Finset.mul_sum,mul_div_assoc] using hs
  have hFull:=hMajor.trans (major_bound (Active E) s.N s.D s.e (aData T E) (hData U B) (spanData U B) j hN
    (fun b hb=>hA b) (fun b hb=>hSpan b))
  unfold Coefficient
  nlinarith only [hFull,hMid]

#print axioms actual_linear
end
end JSP233.FullBandLinear209
