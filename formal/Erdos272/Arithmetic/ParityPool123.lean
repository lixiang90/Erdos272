import Erdos272.Arithmetic.SimplexMoment57

/-! The actual gcd-factor encoder retains the coprimality of its two middle
coordinates. The complete both-even subpool is removed by an actual scaling
bijection, including zero and every small cutoff. No moment budget is assumed. -/
namespace JSP233.ParityPool123
open DivisorMoment45 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

abbrev Quad := Σ _g : ℕ, Σ _a : ℕ, Σ _b : ℕ, ℕ

def CoprimePool (N : ℕ) : Finset Quad :=
  (QuadPool N).filter (fun z=>Nat.Coprime z.2.1 z.2.2.1)

def EvenPool (N : ℕ) : Finset Quad :=
  (QuadPool N).filter (fun z=>2∣z.2.1 ∧ 2∣z.2.2.1)

def doubleMiddle (z : Quad) : Quad := ⟨z.1,2*z.2.1,2*z.2.2.1,z.2.2.2⟩

theorem mem_quad_pool {N : ℕ} {g a b t : ℕ} :
    (⟨g,a,b,t⟩:Quad)∈QuadPool N ↔
      0<g ∧ 0<a ∧ 0<b ∧ 0<t ∧ g*a*b*t≤N := by
  simp only [QuadPool,Finset.mem_sigma,Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hg,_hgN⟩,⟨⟨ha,_haN⟩,⟨⟨hb,_hbN⟩,⟨ht,hbound⟩⟩⟩⟩
    have hh := (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos hg ha) hb)).mp hbound
    exact ⟨hg,ha,hb,ht,by simpa only [Nat.mul_comm t] using hh⟩
  · rintro ⟨hg,ha,hb,ht,hprod⟩
    have hga := Nat.le_mul_of_pos_right (g*a) hb
    have hgab := Nat.le_mul_of_pos_right (g*a*b) ht
    have hgN := (Nat.le_mul_of_pos_right g ha).trans (hga.trans (hgab.trans hprod))
    have haN := (Nat.le_mul_of_pos_left a hg).trans (hga.trans (hgab.trans hprod))
    have hbN := (Nat.le_mul_of_pos_left b (Nat.mul_pos hg ha)).trans (hgab.trans hprod)
    refine ⟨⟨hg,hgN⟩,⟨⟨ha,haN⟩,⟨⟨hb,hbN⟩,⟨ht,?_⟩⟩⟩⟩
    exact (Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos hg ha) hb)).mpr
      (by simpa only [Nat.mul_comm t] using hprod)

theorem divisor_pair_coprime_factors {n d e : ℕ} (hn : 0<n)
    (hd : d∈n.divisors) (he : e∈n.divisors) :
    ∃g a b t:ℕ,0<g ∧ 0<a ∧ 0<b ∧ 0<t ∧ Nat.Coprime a b ∧
      d=g*a ∧ e=g*b ∧ n=g*a*b*t := by
  have hd0 := Nat.pos_of_mem_divisors hd
  have he0 := Nat.pos_of_mem_divisors he
  obtain ⟨a,b,hab,hda,heb⟩ := Nat.exists_coprime d e
  let g := Nat.gcd d e
  have hg : 0<g := Nat.gcd_pos_of_pos_left e hd0
  have hD : d=g*a := by simpa only [Nat.mul_comm,g] using hda
  have hE : e=g*b := by simpa only [Nat.mul_comm,g] using heb
  have ha : 0<a := Nat.pos_of_mul_pos_left (hD ▸ hd0)
  have hb : 0<b := Nat.pos_of_mul_pos_left (hE ▸ he0)
  have hl : Nat.lcm d e=g*a*b := by rw [hD,hE,Nat.lcm_mul_left,hab.lcm_eq_mul,Nat.mul_assoc]
  obtain ⟨t,ht⟩ := hl ▸ Nat.lcm_dvd (Nat.mem_divisors.mp hd).1 (Nat.mem_divisors.mp he).1
  have ht0 : 0<t := by
    by_contra h
    have hz : t=0 := by omega
    simp only [hz,mul_zero] at ht
    omega
  exact ⟨g,a,b,t,hg,ha,hb,ht0,hab,hD,hE,ht⟩

theorem actual_coprime_second_moment_encoding (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)≤(CoprimePool N).card := by
  let U := (Finset.Icc 1 N).sigma (fun n=>n.divisors.product n.divisors)
  have hex : ∀u:U,∃g a b t:ℕ,0<g ∧ 0<a ∧ 0<b ∧ 0<t ∧ Nat.Coprime a b ∧
      u.val.2.1=g*a ∧ u.val.2.2=g*b ∧ u.val.1=g*a*b*t := by
    intro u
    obtain ⟨hn,hde⟩ := Finset.mem_sigma.mp u.property
    obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
    exact divisor_pair_coprime_factors (Finset.mem_Icc.mp hn).1 hd he
  choose g a b t hg ha hb ht hco hD hE hn using hex
  let f : U→Quad := fun u=>⟨g u,a u,b u,t u⟩
  have hm : ∀u:U,f u∈CoprimePool N := by
    intro u
    apply Finset.mem_filter.mpr
    have hN := (Finset.mem_Icc.mp (Finset.mem_sigma.mp u.property).1).2
    exact ⟨mem_quad_pool.mpr ⟨hg u,ha u,hb u,ht u,by rwa [←hn u]⟩,hco u⟩
  let decode : Quad→(Σ _n:ℕ,ℕ×ℕ) :=
    fun z=>⟨z.1*z.2.1*z.2.2.1*z.2.2.2,z.1*z.2.1,z.1*z.2.2.1⟩
  have hrec : ∀u:U,decode (f u)=u.val := by
    intro u
    dsimp only [decode,f]
    rw [←hn u,←hD u,←hE u]
  have hi : Function.Injective f := by
    intro u v heq
    apply Subtype.ext
    rw [←hrec u,←hrec v,heq]
  have hc := Finset.card_le_card_of_injective (f:=fun u:U=>(⟨f u,hm u⟩:CoprimePool N))
    (by intro u v heq;exact hi (congrArg Subtype.val heq))
  simpa [U,Finset.card_sigma,Finset.card_product,pow_two] using hc

theorem double_middle_mem_even_pool {N : ℕ} {z : Quad} (hz : z∈QuadPool (N/4)) :
    doubleMiddle z∈EvenPool N := by
  rcases z with ⟨g,a,b,t⟩
  obtain ⟨hg,ha,hb,ht,hprod⟩ := mem_quad_pool.mp hz
  have hprod4 := (Nat.le_div_iff_mul_le (by decide : 0<4)).mp hprod
  apply Finset.mem_filter.mpr
  change (⟨g,2*a,2*b,t⟩:Quad)∈QuadPool N ∧ 2∣2*a ∧ 2∣2*b
  refine ⟨mem_quad_pool.mpr ⟨hg,by omega,by omega,ht,?_⟩,?_⟩
  · convert hprod4 using 1;ring
  · exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩

theorem double_middle_injective : Function.Injective doubleMiddle := by
  intro z w heq
  have hg := congrArg (fun u:Quad=>u.1) heq
  have ha := congrArg (fun u:Quad=>u.2.1) heq
  have hb := congrArg (fun u:Quad=>u.2.2.1) heq
  have ht := congrArg (fun u:Quad=>u.2.2.2) heq
  rcases z with ⟨g,a,b,t⟩
  rcases w with ⟨g',a',b',t'⟩
  change g=g' at hg
  change 2*a=2*a' at ha
  change 2*b=2*b' at hb
  change t=t' at ht
  have ha' : a=a' := by omega
  have hb' : b=b' := by omega
  subst g'
  subst a'
  subst b'
  subst t'
  rfl

theorem even_pool_card (N : ℕ) : (EvenPool N).card=(QuadPool (N/4)).card := by
  symm
  apply Finset.card_bij (fun z _hz=>doubleMiddle z)
  · intro z hz
    exact double_middle_mem_even_pool hz
  · intro z _hz w _hw heq
    exact double_middle_injective heq
  · intro z hz
    obtain ⟨hz,hdiva,hdivb⟩ := Finset.mem_filter.mp hz
    rcases z with ⟨g,a,b,t⟩
    obtain ⟨a',ha'⟩ := hdiva
    obtain ⟨b',hb'⟩ := hdivb
    change a=2*a' at ha'
    change b=2*b' at hb'
    obtain ⟨hg,ha,hb,ht,hprod⟩ := mem_quad_pool.mp hz
    refine ⟨(⟨g,a',b',t⟩:Quad),mem_quad_pool.mpr ⟨hg,by omega,by omega,ht,?_⟩,?_⟩
    · apply (Nat.le_div_iff_mul_le (by decide : 0<4)).mpr
      rw [ha',hb'] at hprod
      convert hprod using 1;ring
    · dsimp only [doubleMiddle]
      rw [←ha',←hb']

theorem coprime_even_disjoint (N : ℕ) : Disjoint (CoprimePool N) (EvenPool N) := by
  apply Finset.disjoint_left.mpr
  intro z hzC hzE
  have hco := (Finset.mem_filter.mp hzC).2
  obtain ⟨_hz,hda,hdb⟩ := Finset.mem_filter.mp hzE
  have hd := Nat.dvd_gcd hda hdb
  change Nat.gcd z.2.1 z.2.2.1=1 at hco
  rw [hco] at hd
  norm_num at hd

theorem actual_divisor_second_moment_parity_nat (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+DivCount 3 (N/4)≤DivCount 3 N := by
  have hs : CoprimePool N∪EvenPool N⊆QuadPool N := by
    intro z hz
    rcases Finset.mem_union.mp hz with hC | hE
    · exact (Finset.mem_filter.mp hC).1
    · exact (Finset.mem_filter.mp hE).1
  have hc : (∑n∈Finset.Icc 1 N,n.divisors.card^2)+(EvenPool N).card≤(QuadPool N).card := by
    calc
      _≤(CoprimePool N).card+(EvenPool N).card :=
        Nat.add_le_add (actual_coprime_second_moment_encoding N) (Nat.le_refl _)
      _=(CoprimePool N∪EvenPool N).card := (Finset.card_union_of_disjoint (coprime_even_disjoint N)).symm
      _≤_ := Finset.card_le_card hs
  rwa [even_pool_card,quad_pool_eq_div_count,quad_pool_eq_div_count] at hc

theorem actual_divisor_second_moment_parity (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(DivCount 3 (N/4):ℝ)≤(DivCount 3 N:ℝ) := by
  exact_mod_cast actual_divisor_second_moment_parity_nat N

theorem actual_divisor_second_moment_parity_sub (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤(DivCount 3 N:ℝ)-(DivCount 3 (N/4):ℝ) := by
  linarith only [actual_divisor_second_moment_parity N]

#print axioms mem_quad_pool
#print axioms divisor_pair_coprime_factors
#print axioms actual_coprime_second_moment_encoding
#print axioms double_middle_mem_even_pool
#print axioms double_middle_injective
#print axioms even_pool_card
#print axioms coprime_even_disjoint
#print axioms actual_divisor_second_moment_parity_nat
#print axioms actual_divisor_second_moment_parity
#print axioms actual_divisor_second_moment_parity_sub
end
end JSP233.ParityPool123
