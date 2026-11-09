module

public import Erdos272.Resources.CoreFringe208
public import Erdos272.Resources.CommonCapacity208
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.ResidualSpan208
open StarCompletion APGeometry APCount41 NearAP36 FarSlot112
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem same_step_inter {P Q : Finset ℤ} {d a : ℤ}
    (hP : APAt d a P) (hQ : APAt d a Q) : APAt d a (P ∩ Q) := by
  obtain ⟨hd,l,r,hP⟩ := hP
  obtain ⟨_,u,v,hQ⟩ := hQ
  refine ⟨hd,max l u,min r v,?_⟩
  intro x
  simp only [Finset.mem_inter,hP,hQ]
  omega

theorem actual_overlap_bounds {Ω S T P Q : Finset ℤ} {F : Finset (Finset ℤ)}
    {d a x : ℤ} {p : ℕ}
    (hF : Legal Ω F) (hS : S ∈ F) (hT : T ∈ F) (hST : S ≠ T)
    (hP : MaximalAPCore S P) (hQ : Q ⊆ T)
    (hAtP : APAt d a P) (hAtQ : APAt d a Q)
    (hx : x ∈ S \ P) (hxT : x ∈ T)
    (hk : 2 ≤ (P ∩ Q).card)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ)*delta ≤ d)
    (hmax : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card) :
    ((P ∩ Q).card-1)*(p-1) ≤ (S \ P).card ∧
      p*((P ∩ Q).card-1)+1 ≤ P.card := by
  let I := P ∩ Q
  have hI := same_step_inter hAtP hAtQ
  obtain ⟨u,v,hu,huv,hv,hbounds,hspan⟩ := apAt_adjacent_min hI hk
  let R := S ∩ T
  have hR : IsAP R := hF.2 S hS T hT hST
  have hIR : I ⊆ R := Finset.inter_subset_inter hP.1 hQ
  obtain ⟨delta,phase,hRAt,_⟩ := (isAP_iff_exists_APAt R).mp hR
  have hdiv : delta ∣ d := by
    simpa only [add_sub_cancel_left] using apAt_dvd_sub hRAt (hIR hu) (hIR huv)
  have hle : delta ≤ d := Int.le_of_dvd hAtP.1 hdiv
  have hne : delta ≠ d := by
    intro heq
    have hRu : APAt d u R := by simpa only [heq] using apAt_rebase hRAt (hIR hu)
    have hPu := apAt_rebase hAtP (Finset.mem_inter.mp hu).1
    have hunion : APAt d u (P ∪ R) := by
      simpa only [APAt,Finset.mem_union] using
        PrivateUnion.union_APAt d u (fun y => y ∈ P) (fun y => y ∈ R)
          hPu hRu (Finset.mem_inter.mp hu).1 (hIR hu)
    have he := hP.2.2 (P ∪ R) Finset.subset_union_left
      (Finset.union_subset hP.1 Finset.inter_subset_left)
      ((isAP_iff_exists_APAt _).mpr ⟨d,u,hunion,Finset.mem_union_left _ (Finset.mem_inter.mp hu).1⟩)
    exact (Finset.mem_sdiff.mp hx).2 (he ▸ Finset.mem_union_right P
      (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1,hxT⟩))
  have hratio := hproper delta hRAt.1 hdiv (by omega)
  have hcast : (((I.card-1 : ℕ) : ℤ)) = (I.card : ℤ)-1 := by
    have : 1 ≤ I.card := by dsimp [I]; omega
    omega
  have hend : u+((I.card-1 : ℕ) : ℤ)*d = v := by
    rw [hcast]
    nlinarith only [hspan]
  have hfirst := CoreFringe208.extra_points hAtP hRAt
    (Finset.mem_inter.mp hu).1 (hIR hu) (hend ▸ hIR hv)
    Finset.inter_subset_left hdiv hratio
  have hsecond := CoreDensity208.ap_card_from_density hRAt (hIR hu)
    (hend ▸ hIR hv) hratio
  exact ⟨hfirst,hsecond.trans (hmax R hR Finset.inter_subset_left)⟩

def Span (a b p : ℕ) : ℕ := 2*a-min ((b-1)/(p-1)) (a/p)

theorem overlap_arithmetic {a b p n m K u : ℕ}
    (hp : 2 ≤ p) (hn : a+1 ≤ n) (hm : a+1 ≤ m)
    (hcard : u+K+1=n+m) (hsmall : K*(p-1) ≤ b-1)
    (hdn : p*K+1 ≤ n) (hdm : p*K+1 ≤ m) : Span a b p+1 ≤ u := by
  have hp0 : 0 < p := by omega
  have hp1 : 0 < p-1 := by omega
  have hfee : K ≤ (b-1)/(p-1) := (Nat.le_div_iff_mul_le hp1).mpr hsmall
  have hleft : 2*a+1 ≤ u+(b-1)/(p-1) := by omega
  have hdensity : ∀ z : ℕ, a+1 ≤ z → p*K+1 ≤ z → K ≤ a/p+2*(z-(a+1)) := by
    intro z hz hdz
    have hzEq : z=a+1+(z-(a+1)) := by omega
    have hrem := Nat.mod_lt a hp0
    have hsplit := Nat.mod_add_div a p
    by_contra hh
    have hb : a/p+2*(z-(a+1))+1 ≤ K := by omega
    have hmul := Nat.mul_le_mul_left p hb
    nlinarith only [hmul,hsplit,hrem,hp,hzEq,hdz]
  have hright : 2*a+1 ≤ u+a/p := by
    rcases le_total n m with hnm | hmn
    · have hK := hdensity n hn hdn
      omega
    · have hK := hdensity m hm hdm
      omega
  have hu : 1 ≤ u := by
    have hh := Nat.mul_le_mul_right K hp
    omega
  have hmin : 2*a+1 ≤ u+min ((b-1)/(p-1)) (a/p) := by
    rcases le_total ((b-1)/(p-1)) (a/p) with h | h
    · simpa only [min_eq_left h] using hleft
    · simpa only [min_eq_right h] using hright
  unfold Span
  omega

theorem actual_pair_span {N a b p : ℕ} {S T P Q : Finset ℤ}
    {F : Finset (Finset ℤ)} {d t x : ℤ}
    (hF : Legal (Ground N) F) (hS : S ∈ F) (hT : T ∈ F) (hST : S ≠ T)
    (hp : 2 ≤ p) (hP : MaximalAPCore S P) (hQ : MaximalAPCore T Q)
    (hAtP : APAt d t P) (hAtQ : APAt d t Q) (htP : t ∈ P) (htQ : t ∈ Q)
    (hxP : x ∈ S \ P) (hxQ : x ∈ T \ Q)
    (hnP : a+1 ≤ P.card) (hnQ : a+1 ≤ Q.card)
    (hsmall : (S \ P).card < b)
    (hproper : ∀ delta : ℤ, 0 < delta → delta ∣ d → delta < d → (p : ℤ)*delta ≤ d)
    (hmaxP : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ P.card)
    (hmaxQ : ∀ R : Finset ℤ, IsAP R → R ⊆ T → R.card ≤ Q.card) :
    d*(Span a b p : ℤ) ≤ (N : ℤ)-1 := by
  let K := (P ∩ Q).card-1
  have hk1 : 1 ≤ (P ∩ Q).card := Finset.card_pos.mpr ⟨t,Finset.mem_inter.mpr ⟨htP,htQ⟩⟩
  have hbounds : K*(p-1) ≤ b-1 ∧ p*K+1 ≤ P.card ∧ p*K+1 ≤ Q.card := by
    by_cases hk : 2 ≤ (P ∩ Q).card
    · have hPS := actual_overlap_bounds hF hS hT hST hP hQ.1 hAtP hAtQ hxP
        (Finset.mem_sdiff.mp hxQ).1 hk hproper hmaxP
      have hQT := actual_overlap_bounds hF hT hS hST.symm hQ hP.1 hAtQ hAtP hxQ
        (Finset.mem_sdiff.mp hxP).1 (by simpa only [Finset.inter_comm] using hk) hproper hmaxQ
      refine ⟨by dsimp [K]; omega,hPS.2,?_⟩
      simpa only [Finset.inter_comm] using hQT.2
    · have hzero : K=0 := by dsimp [K]; omega
      simp only [hzero,zero_mul,mul_zero,zero_add]
      omega
  have hcard := Finset.card_union_add_card_inter P Q
  have hU : Span a b p+1 ≤ (P ∪ Q).card := overlap_arithmetic hp hnP hnQ
    (by dsimp [K]; omega) hbounds.1 hbounds.2.1 hbounds.2.2
  have hAtU : APAt d t (P ∪ Q) := by
    simpa only [APAt,Finset.mem_union] using
      PrivateUnion.union_APAt d t (fun y => y ∈ P) (fun y => y ∈ Q) hAtP hAtQ htP htQ
  have hground : P ∪ Q ⊆ Finset.Icc 1 (N : ℤ) :=
    fun y hy => Finset.mem_Icc.mpr ((mem_ground N y).mp
      ((Finset.union_subset (hP.1.trans (hF.1 S hS)) (hQ.1.trans (hF.1 T hT))) hy))
  have hspan := apAt_card_span hAtU ⟨t,Finset.mem_union_left _ htP⟩ hground
  have hcZ : (Span a b p : ℤ)+1 ≤ (P ∪ Q).card := by exact_mod_cast hU
  have hmul := mul_le_mul_of_nonneg_left (show (Span a b p : ℤ) ≤ (P ∪ Q).card-1 by omega) hAtP.1.le
  omega

#print axioms same_step_inter
#print axioms actual_overlap_bounds
#print axioms overlap_arithmetic
#print axioms actual_pair_span
end
end JSP233.ResidualSpan208
