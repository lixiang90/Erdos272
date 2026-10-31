import Erdos272.Arithmetic.CleanupIntegral209

namespace JSP233.HeavyFiniteSums209
open CleanupIntegral209
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option maxRecDepth 200000

def CountAt (N A h d : ℕ) : ℝ := if A≤N/d then h else 0
def WindowAt (N A U d : ℕ) : ℝ := if A≤N/d then (min U (N/d+1) : ℕ) else 0

theorem countAt_nonneg (N A h d : ℕ) : 0≤CountAt N A h d := by unfold CountAt;split_ifs <;> positivity
theorem windowAt_nonneg (N A U d : ℕ) : 0≤WindowAt N A U d := by unfold WindowAt;split_ifs <;> positivity

theorem divisor_switch {N A d : ℕ} (hA : 0<A) (hd : 0<d) : A≤N/d ↔ d≤N/A := by
  rw [Nat.le_div_iff_mul_le hd,Nat.le_div_iff_mul_le hA,Nat.mul_comm]

theorem supported_sum (D Q : ℕ) (f g : ℕ→ℝ)
    (hzero : ∀d∈Finset.Icc 1 D,Q<d→f d=0)
    (hbound : ∀d∈Finset.Icc 1 D,f d≤g d) (hg : ∀d∈Finset.Icc 1 Q,0≤g d) :
    (∑d∈Finset.Icc 1 D,f d)≤∑d∈Finset.Icc 1 Q,g d := by
  let I:=Finset.Icc 1 D∩Finset.Icc 1 Q
  have he : (∑d∈I,f d)=∑d∈Finset.Icc 1 D,f d := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro d hd hnot
    apply hzero d hd
    by_contra h
    have hI : d∈I := Finset.mem_inter.mpr ⟨hd,Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,by omega⟩⟩
    exact hnot hI
  rw [←he]
  exact (Finset.sum_le_sum (fun d (hd : d∈I)=>hbound d (Finset.mem_inter.mp hd).1)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun d hd hn=>hg d hd))

theorem active_sum (N D A h : ℕ) (hA : 0<A) :
    (∑d∈Finset.Icc 1 D,CountAt N A h d)≤(N : ℝ)*h/A := by
  have hs:=supported_sum D (N/A) (CountAt N A h) (fun _=>(h : ℝ))
    (by
      intro d hd hlarge
      have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
      have hn : ¬A≤N/d := by intro hh;have := (divisor_switch hA hd0).mp hh;omega
      simp only [CountAt,if_neg hn])
    (by intro d hd;unfold CountAt;split_ifs <;> first | exact le_rfl | positivity)
    (by intros;exact Nat.cast_nonneg h)
  have hq : ((N/A : ℕ) : ℝ)≤(N : ℝ)/A := by
    apply (le_div_iff₀ (by exact_mod_cast hA : (0 : ℝ)<A)).mpr
    exact_mod_cast Nat.div_mul_le_self N A
  have hh:=mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg h)
  have he : (∑_d∈Finset.Icc 1 (N/A),(h : ℝ))=((N/A : ℕ) : ℝ)*h := by simp
  rw [he] at hs
  exact hs.trans (by simpa only [div_mul_eq_mul_div] using hh)

theorem pair_sum (N D A B U h j : ℕ) (hN : 0<N) (hA : 0<A) (hB : 0<B) (hU : 0<U) :
    (∑d∈Finset.Icc 1 D,CountAt N A h d*WindowAt N B U d)≤
      (N : ℝ)*h*(Tangent ((U : ℝ)/(max A B : ℕ)) j+1/((max A B : ℕ) : ℝ)) := by
  have hmax : 0<max A B := hA.trans_le (le_max_left _ _)
  have hs:=supported_sum D (N/max A B)
    (fun d=>CountAt N A h d*WindowAt N B U d)
    (fun d=>(h : ℝ)*(min U (N/d+1) : ℕ))
    (by
      intro d hd hlarge
      have hd0 : 0<d := by have := (Finset.mem_Icc.mp hd).1;omega
      by_cases ha : A≤N/d <;> by_cases hb : B≤N/d
      · have ha':=(divisor_switch hA hd0).mp ha
        have hb':=(divisor_switch hB hd0).mp hb
        have hm : d≤N/max A B := by
          by_cases hab : A≤B
          · simpa only [max_eq_right hab] using hb'
          · simpa only [max_eq_left (by omega : B≤A)] using ha'
        omega
      all_goals simp [CountAt,WindowAt,ha,hb])
    (by
      intro d hd
      unfold CountAt WindowAt
      split_ifs <;> first | exact le_rfl | (simp only [zero_mul,mul_zero];positivity))
    (by intros;positivity)
  have hc:=CleanupIntegral209.clipped_sum_tangent hN hU hmax (le_refl (N/max A B)) j
  have hp:=mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg h)
  calc
    _≤(h : ℝ)*((∑d∈Finset.Icc 1 (N/max A B),min U (N/d+1) : ℕ) : ℝ) := by
      simpa only [←Finset.mul_sum,←Nat.cast_sum] using hs
    _≤(h : ℝ)*((N : ℝ)*(Tangent ((U : ℝ)/(max A B : ℕ)) j+1/((max A B : ℕ) : ℝ))) := hp
    _=_ := by ring

def Major {ι : Type*} [DecidableEq ι] (s : Finset ι) (N D e : ℕ) (A h U : ι→ℕ) : ℝ :=
  (∑b∈s,∑c∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d)+
    (e : ℝ)*(∑b∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d)
def Coefficient {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ℕ)
    (A h U : ι→ℕ) (j : ι→ι→ℕ) : ℝ :=
  (e : ℝ)*(∑b∈s,(h b : ℝ)/(A b : ℝ))+
    (∑b∈s,∑c∈s,(h b : ℝ)*(Tangent ((U c : ℝ)/(max (A b) (A c) : ℕ)) (j b c)+
      1/((max (A b) (A c) : ℕ) : ℝ)))

theorem major_product {ι : Type*} [DecidableEq ι] (s : Finset ι) (N D e : ℕ) (A h U : ι→ℕ) :
    Major s N D e A h U=
      ∑d∈Finset.Icc 1 D,(∑b∈s,CountAt N (A b) (h b) d)*
        ((∑c∈s,WindowAt N (A c) (U c) d)+(e : ℝ)) := by
  have hp : (∑b∈s,∑c∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d)=
      ∑d∈Finset.Icc 1 D,∑b∈s,∑c∈s,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d := by
    calc
      _=∑b∈s,∑d∈Finset.Icc 1 D,∑c∈s,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d := by
        apply Finset.sum_congr rfl
        intro b hb
        exact Finset.sum_comm
      _=_ := Finset.sum_comm
  have hc : (∑b∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d)=
      ∑d∈Finset.Icc 1 D,∑b∈s,CountAt N (A b) (h b) d := Finset.sum_comm
  unfold Major
  rw [hp,hc,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  have he : (∑b∈s,∑c∈s,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d)=
      (∑b∈s,CountAt N (A b) (h b) d)*(∑c∈s,WindowAt N (A c) (U c) d) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.mul_sum]
  rw [he]
  ring

theorem major_bound {ι : Type*} [DecidableEq ι] (s : Finset ι) (N D e : ℕ)
    (A h U : ι→ℕ) (j : ι→ι→ℕ) (hN : 0<N) (hA : ∀b∈s,0<A b) (hU : ∀b∈s,0<U b) :
    Major s N D e A h U≤(N : ℝ)*Coefficient s e A h U j := by
  have hp:=Finset.sum_le_sum (fun b (hb : b∈s)=>Finset.sum_le_sum (fun c (hc : c∈s)=>
    pair_sum N D (A b) (A c) (U c) (h b) (j b c) hN (hA b hb) (hA c hc) (hU c hc)))
  have hp' : (∑b∈s,∑c∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d*WindowAt N (A c) (U c) d)≤
      (N : ℝ)*(∑b∈s,∑c∈s,(h b : ℝ)*(Tangent ((U c : ℝ)/(max (A b) (A c) : ℕ)) (j b c)+
        1/((max (A b) (A c) : ℕ) : ℝ))) := by
    simpa only [Finset.mul_sum,mul_assoc] using hp
  have hc:=Finset.sum_le_sum (fun b (hb : b∈s)=>active_sum N D (A b) (h b) (hA b hb))
  have hc' : (∑b∈s,∑d∈Finset.Icc 1 D,CountAt N (A b) (h b) d)≤
      (N : ℝ)*(∑b∈s,(h b : ℝ)/(A b : ℝ)) := by
    simpa only [Finset.mul_sum,mul_div_assoc] using hc
  have he:=mul_le_mul_of_nonneg_left hc' (Nat.cast_nonneg e)
  unfold Major Coefficient
  nlinarith only [hp',he]

#print axioms active_sum
#print axioms pair_sum
#print axioms major_bound
#print axioms major_product
end
end JSP233.HeavyFiniteSums209
