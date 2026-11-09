module

public import Erdos272.Arithmetic.Hyperbola131
public import Erdos272.Arithmetic.ParityPool123
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.PairHyperbola131
open SimplexMoment57 DivisorMoment45 ParityPool123 Hyperbola131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev PairPair := (ℕ×ℕ)×(ℕ×ℕ)
def pack (p : PairPair) : Quad := ⟨p.1.1,p.1.2,p.2.1,p.2.2⟩
def unpack (z : Quad) : PairPair := ((z.1,z.2.1),(z.2.2.1,z.2.2.2))
def firstProduct (z : Quad) : ℕ := z.1*z.2.1
def secondProduct (z : Quad) : ℕ := z.2.2.1*z.2.2.2
def PairLeft (N M : ℕ) := (QuadPool N).filter (fun z=>firstProduct z≤M)
def PairRight (N M : ℕ) := (QuadPool N).filter (fun z=>secondProduct z≤M)
def T (M : ℕ) : ℕ := DivCount 1 M
def Z (N M : ℕ) : ℕ := ∑a∈Finset.Icc 1 M,a.divisors.card*DivCount 1 (N/a)

theorem pack_injective : Function.Injective pack := by
  intro p q h
  exact congrArg unpack h

theorem unpack_injective : Function.Injective unpack := by
  intro z w h
  have hh := congrArg pack h
  simpa only [pack,unpack] using hh

theorem mem_pairs_self {N a b : ℕ} :
    (a,b)∈Pairs N N ↔ 0<a ∧ 0<b ∧ a*b≤N := by
  simp only [Pairs,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha,_⟩,⟨hb,_⟩⟩,hp⟩
    exact ⟨ha,hb,hp⟩
  · rintro ⟨ha,hb,hp⟩
    exact ⟨⟨⟨ha,(Nat.le_mul_of_pos_right a hb).trans hp⟩,
      ⟨hb,(Nat.le_mul_of_pos_left b ha).trans hp⟩⟩,hp⟩

theorem factor_pairs_card (a : ℕ) : a.divisorsAntidiagonal.card=a.divisors.card := by
  rw [←Nat.map_div_right_divisors]
  exact Finset.card_map _

theorem left_fiber_card {N M a : ℕ} (ha : a∈Finset.Icc 1 M) :
    ((PairLeft N M).filter (fun z=>firstProduct z=a)).card=
      a.divisors.card*DivCount 1 (N/a) := by
  obtain ⟨ha0,haM⟩ := Finset.mem_Icc.mp ha
  have hc : (a.divisorsAntidiagonal ×ˢ Pairs (N/a) (N/a)).card=
      ((PairLeft N M).filter (fun z=>firstProduct z=a)).card := by
    apply Finset.card_bij (fun p _hp=>pack p)
    · intro p hp
      obtain ⟨hfirst,hsecond⟩ := Finset.mem_product.mp hp
      obtain ⟨he,_⟩ := Nat.mem_divisorsAntidiagonal.mp hfirst
      obtain ⟨h10,h20⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hfirst
      obtain ⟨h30,h40,hprod⟩ := mem_pairs_self.mp hsecond
      have hbound := (Nat.le_div_iff_mul_le ha0).mp hprod
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_,?_⟩,?_⟩
      · apply mem_quad_pool.mpr
        refine ⟨Nat.pos_of_ne_zero h10,Nat.pos_of_ne_zero h20,h30,h40,?_⟩
        rw [←he] at hbound
        nlinarith only [hbound]
      · change p.1.1*p.1.2≤M
        exact he ▸ haM
      · exact he
    · intro p _hp q _hq he
      exact pack_injective he
    · intro z hz
      obtain ⟨hzL,he⟩ := Finset.mem_filter.mp hz
      obtain ⟨hzQ,_hzM⟩ := Finset.mem_filter.mp hzL
      obtain ⟨h10,h20,h30,h40,hprod⟩ := mem_quad_pool.mp hzQ
      have hsecond : z.2.2.1*z.2.2.2≤N/a := by
        apply (Nat.le_div_iff_mul_le ha0).mpr
        change z.1*z.2.1=a at he
        rw [←he]
        nlinarith only [hprod]
      refine ⟨unpack z,Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr ⟨he,by omega⟩
      · exact mem_pairs_self.mpr ⟨h30,h40,hsecond⟩
      · rfl
  rw [Finset.card_product,factor_pairs_card,pairs_card (le_refl (N/a))] at hc
  exact hc.symm

theorem pair_left_card (N M : ℕ) : (PairLeft N M).card=Z N M := by
  rw [Finset.card_eq_sum_card_fiberwise (f:=firstProduct) (t:=Finset.Icc 1 M)
    (by
      intro z hz
      obtain ⟨hz,hM⟩ := Finset.mem_filter.mp hz
      obtain ⟨h10,h20,_,_,_⟩ := mem_quad_pool.mp hz
      exact Finset.mem_Icc.mpr ⟨Nat.mul_pos h10 h20,hM⟩)]
  apply Finset.sum_congr rfl
  intro a ha
  exact left_fiber_card ha

def swapPairs (z : Quad) : Quad := ⟨z.2.2.1,z.2.2.2,z.1,z.2.1⟩

theorem swap_pairs_mem {N : ℕ} (z : Quad) : swapPairs z∈QuadPool N ↔ z∈QuadPool N := by
  rcases z with ⟨g,a,b,t⟩
  simp only [swapPairs,mem_quad_pool]
  constructor <;> rintro ⟨hg,ha,hb,ht,hp⟩ <;>
    refine ⟨hb,ht,hg,ha,?_⟩ <;> nlinarith only [hp]

theorem pair_right_card (N M : ℕ) : (PairRight N M).card=Z N M := by
  calc
    _=(PairLeft N M).card := by
      apply Finset.card_bij (fun z _hz=>swapPairs z)
      · intro z hz
        obtain ⟨hz,hM⟩ := Finset.mem_filter.mp hz
        exact Finset.mem_filter.mpr ⟨(swap_pairs_mem z).mpr hz,hM⟩
      · intro z _hz w _hw he
        exact congrArg swapPairs he
      · intro z hz
        refine ⟨swapPairs z,?_,?_⟩
        · obtain ⟨hz,hM⟩ := Finset.mem_filter.mp hz
          exact Finset.mem_filter.mpr ⟨(swap_pairs_mem z).mpr hz,hM⟩
        · rfl
    _=Z N M := pair_left_card N M

theorem pair_inter_card_upper (N M : ℕ) :
    (PairLeft N M∩PairRight N M).card≤T M^2 := by
  have hc : (PairLeft N M∩PairRight N M).card≤
      (Pairs M M×ˢ Pairs M M).card := by
    apply Finset.card_le_card_of_injOn unpack
    · intro z hz
      obtain ⟨hzL,hzR⟩ := Finset.mem_inter.mp hz
      obtain ⟨hzQ,hL⟩ := Finset.mem_filter.mp hzL
      obtain ⟨_hzQ,hR⟩ := Finset.mem_filter.mp hzR
      obtain ⟨h10,h20,h30,h40,_⟩ := mem_quad_pool.mp hzQ
      exact Finset.mem_product.mpr ⟨mem_pairs_self.mpr ⟨h10,h20,hL⟩,
        mem_pairs_self.mpr ⟨h30,h40,hR⟩⟩
    · exact unpack_injective.injOn
  simpa only [Finset.card_product,pairs_card (le_refl M),T,pow_two] using hc

theorem pair_union_eq {N M : ℕ} (hN : N≤M^2) :
    PairLeft N M∪PairRight N M=QuadPool N := by
  ext z
  simp only [PairLeft,PairRight,Finset.mem_union,Finset.mem_filter]
  constructor
  · tauto
  · intro hz
    by_cases hL : firstProduct z≤M
    · exact Or.inl ⟨hz,hL⟩
    · refine Or.inr ⟨hz,?_⟩
      by_contra hR
      have h1 : M+1≤firstProduct z := by omega
      have h2 : M+1≤secondProduct z := by omega
      have hmul := Nat.mul_le_mul h1 h2
      have hprod := (mem_quad_pool.mp hz).2.2.2.2
      dsimp only [firstProduct,secondProduct] at hmul
      nlinarith only [hN,hmul,hprod]

theorem pair_inter_card_lower {N M K : ℕ} (hKM : K≤M) (hK : K^2≤N) :
    T K^2≤(PairLeft N M∩PairRight N M).card := by
  have hc : (Pairs K K×ˢ Pairs K K).card≤
      (PairLeft N M∩PairRight N M).card := by
    apply Finset.card_le_card_of_injOn pack
    · intro p hp
      obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
      obtain ⟨h10,h20,hL⟩ := mem_pairs_self.mp hp1
      obtain ⟨h30,h40,hR⟩ := mem_pairs_self.mp hp2
      have hprod := (Nat.mul_le_mul hL hR).trans (by simpa only [pow_two] using hK)
      have hz : pack p∈QuadPool N := by
        apply mem_quad_pool.mpr
        refine ⟨h10,h20,h30,h40,?_⟩
        nlinarith only [hprod]
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨hz,hL.trans hKM⟩,
        Finset.mem_filter.mpr ⟨hz,hR.trans hKM⟩⟩
    · exact pack_injective.injOn
  simpa only [Finset.card_product,pairs_card (le_refl K),T,pow_two] using hc

theorem actual_pair_hyperbola_lower (N M : ℕ) :
    2*Z N M≤DivCount 3 N+T M^2 := by
  have he := Finset.card_union_add_card_inter (PairLeft N M) (PairRight N M)
  have hu : (PairLeft N M∪PairRight N M).card≤DivCount 3 N := by
    rw [←quad_pool_eq_div_count]
    apply Finset.card_le_card
    exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hi := pair_inter_card_upper N M
  rw [pair_left_card,pair_right_card] at he
  omega

theorem actual_pair_hyperbola_upper {N M K : ℕ}
    (hKM : K≤M) (hK : K^2≤N) (hN : N≤M^2) :
    DivCount 3 N+T K^2≤2*Z N M := by
  have he := Finset.card_union_add_card_inter (PairLeft N M) (PairRight N M)
  have hi := pair_inter_card_lower hKM hK
  rw [pair_union_eq hN,quad_pool_eq_div_count,pair_left_card,pair_right_card] at he
  omega

theorem actual_pair_hyperbola_lower_real (N M : ℕ) :
    2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (N/a):ℝ))-
      (DivCount 1 M:ℝ)^2≤(DivCount 3 N:ℝ) := by
  have h : 2*(Z N M:ℝ)≤(DivCount 3 N:ℝ)+(T M:ℝ)^2 := by
    exact_mod_cast actual_pair_hyperbola_lower N M
  dsimp only [Z,T] at h
  push_cast at h
  linarith only [h]

theorem actual_pair_hyperbola_upper_real {N M K : ℕ}
    (hKM : K≤M) (hK : K^2≤N) (hN : N≤M^2) :
    (DivCount 3 N:ℝ)≤
      2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (N/a):ℝ))-
        (DivCount 1 K:ℝ)^2 := by
  have h : (DivCount 3 N:ℝ)+(T K:ℝ)^2≤2*(Z N M:ℝ) := by
    exact_mod_cast actual_pair_hyperbola_upper hKM hK hN
  dsimp only [Z,T] at h
  push_cast at h
  linarith only [h]

#print axioms pack_injective
#print axioms unpack_injective
#print axioms mem_pairs_self
#print axioms factor_pairs_card
#print axioms left_fiber_card
#print axioms pair_left_card
#print axioms swap_pairs_mem
#print axioms pair_right_card
#print axioms pair_inter_card_upper
#print axioms pair_union_eq
#print axioms pair_inter_card_lower
#print axioms actual_pair_hyperbola_lower
#print axioms actual_pair_hyperbola_upper
#print axioms actual_pair_hyperbola_lower_real
#print axioms actual_pair_hyperbola_upper_real
end
end JSP233.PairHyperbola131
