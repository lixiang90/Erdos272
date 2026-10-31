import Erdos272.Traces.RestrictedWitness44
import Erdos272.Arithmetic.HarmonicSharp39

/-! Actual restricted witness exceptions paid by the divisor second moment.
The gcd-factor encoding is the finite argument at fixed KK source 4152--4331;
here it is proved in the local integer-ground model and applied to actual F.
-/
namespace JSP233.DivisorMoment45
open StarCompletion RestrictedWitness44 WitnessInterval43
open scoped Classical BigOperators
noncomputable section

def QuadPool (N : ℕ) : Finset (Σ _g : ℕ,Σ _a : ℕ,Σ _b : ℕ,ℕ) :=
  (Finset.Icc 1 N).sigma (fun g=>(Finset.Icc 1 N).sigma (fun a=>
    (Finset.Icc 1 N).sigma (fun b=>Finset.Icc 1 (N/(g*a*b)))))

theorem divisor_pair_factors {n d e : ℕ} (hn : 0<n)
    (hd : d∈n.divisors) (he : e∈n.divisors) :
    ∃ g a b t:ℕ,0<g ∧ 0<a ∧ 0<b ∧ 0<t ∧ d=g*a ∧ e=g*b ∧ n=g*a*b*t := by
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
  exact ⟨g,a,b,t,hg,ha,hb,ht0,hD,hE,ht⟩

theorem actual_second_moment_encoding (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,n.divisors.card^2)≤(QuadPool N).card := by
  let U := (Finset.Icc 1 N).sigma (fun n=>n.divisors.product n.divisors)
  have hex : ∀ u:U,∃ g a b t:ℕ,0<g ∧ 0<a ∧ 0<b ∧ 0<t ∧
      u.val.2.1=g*a ∧ u.val.2.2=g*b ∧ u.val.1=g*a*b*t := by
    intro u
    obtain ⟨hn,hde⟩ := Finset.mem_sigma.mp u.property
    obtain ⟨hd,he⟩ := Finset.mem_product.mp hde
    exact divisor_pair_factors (Finset.mem_Icc.mp hn).1 hd he
  choose g a b t hg ha hb ht hD hE hn using hex
  let f : U→(Σ _g:ℕ,Σ _a:ℕ,Σ _b:ℕ,ℕ) := fun u=>⟨g u,a u,b u,t u⟩
  have hm : ∀ u:U,f u∈QuadPool N := by
    intro u
    have hN := (Finset.mem_Icc.mp (Finset.mem_sigma.mp u.property).1).2
    have hprod : g u*a u*b u*t u≤N := by rwa [←hn u]
    have hga := Nat.le_mul_of_pos_right (g u*a u) (hb u)
    have hgab := Nat.le_mul_of_pos_right (g u*a u*b u) (ht u)
    have hgN := (Nat.le_mul_of_pos_right (g u) (ha u)).trans (hga.trans (hgab.trans hprod))
    have haN := (Nat.le_mul_of_pos_left (a u) (hg u)).trans (hga.trans (hgab.trans hprod))
    have hbN := (Nat.le_mul_of_pos_left (b u) (Nat.mul_pos (hg u) (ha u))).trans (hgab.trans hprod)
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hg u,hgN⟩,?_⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨ha u,haN⟩,?_⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hb u,hbN⟩,?_⟩
    exact Finset.mem_Icc.mpr ⟨ht u,(Nat.le_div_iff_mul_le (Nat.mul_pos (Nat.mul_pos (hg u) (ha u)) (hb u))).mpr
      (by simpa only [f,Nat.mul_comm (t u)] using hprod)⟩
  let decode : (Σ _g:ℕ,Σ _a:ℕ,Σ _b:ℕ,ℕ)→(Σ _n:ℕ,ℕ×ℕ) :=
    fun z=>⟨z.1*z.2.1*z.2.2.1*z.2.2.2,z.1*z.2.1,z.1*z.2.2.1⟩
  have hrec : ∀ u:U,decode (f u)=u.val := by intro u;dsimp only [decode,f];rw [←hn u,←hD u,←hE u]
  have hi : Function.Injective f := by
    intro u v heq
    apply Subtype.ext
    rw [←hrec u,←hrec v,heq]
  have hc := Finset.card_le_card_of_injective (f:=fun u:U=>(⟨f u,hm u⟩:QuadPool N))
    (by intro u v heq;exact hi (congrArg Subtype.val heq))
  simpa [U,Finset.card_sigma,Finset.card_product,pow_two] using hc

theorem quad_pool_harmonic_bound (N : ℕ) :
    ((QuadPool N).card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  calc
    ((QuadPool N).card:ℝ)=∑ g∈Finset.Icc 1 N,∑ a∈Finset.Icc 1 N,
        ∑ b∈Finset.Icc 1 N,((N/(g*a*b):ℕ):ℝ) := by
      simp [QuadPool,Finset.card_sigma,Nat.cast_sum]
    _≤∑ g∈Finset.Icc 1 N,∑ a∈Finset.Icc 1 N,∑ b∈Finset.Icc 1 N,
        (N:ℝ)*(g:ℝ)⁻¹*(a:ℝ)⁻¹*(b:ℝ)⁻¹ := by
      apply Finset.sum_le_sum;intro g hg
      apply Finset.sum_le_sum;intro a ha
      apply Finset.sum_le_sum;intro b hb
      simpa [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_left_comm,mul_comm]
        using (Nat.cast_div_le (α:=ℝ) (m:=N) (n:=g*a*b))
    _=(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
      simp only [←Finset.mul_sum,←Finset.sum_mul,HarmonicAbel29.Harmonic,one_div]
      ring

theorem actual_divisor_second_moment (N : ℕ) :
    (∑ n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)≤(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have h : ((∑ n∈Finset.Icc 1 N,n.divisors.card^2:ℕ):ℝ)≤((QuadPool N).card:ℝ) :=
    by exact_mod_cast actual_second_moment_encoding N
  simpa only [Nat.cast_sum,Nat.cast_pow] using h.trans (quad_pool_harmonic_bound N)

theorem distance_le_ground {N : ℕ} {c q : ℤ} (hc : c∈Ground N) (hq : q∈Ground N) :
    Distance c q≤N := by
  have hcc := (JSP233.mem_ground N c).mp hc
  have hqq := (JSP233.mem_ground N q).mp hq
  have hh : (Distance c q:ℤ)≤N := by
    dsimp [Distance]
    by_cases h : c≤q
    · rw [Int.natAbs_of_nonneg (by omega : 0≤q-c)];omega
    · rw [Int.ofNat_natAbs_of_nonpos (by omega : q-c≤0)];omega
  exact_mod_cast hh

theorem distance_side_injective {c q z : ℤ}
    (hd : Distance c q=Distance c z) (hs : decide (c≤q)=decide (c≤z)) : q=z := by
  have hh : (Distance c q:ℤ)=(Distance c z:ℤ) := congrArg Int.ofNat hd
  dsimp [Distance] at hh
  by_cases hq : c≤q <;> by_cases hz : c≤z
  · rw [Int.natAbs_of_nonneg (by omega : 0≤q-c),Int.natAbs_of_nonneg (by omega : 0≤z-c)] at hh
    omega
  · simp [hq,hz] at hs
  · simp [hq,hz] at hs
  · rw [Int.ofNat_natAbs_of_nonpos (by omega : q-c≤0),Int.ofNat_natAbs_of_nonpos (by omega : z-c≤0)] at hh
    omega

theorem actual_distance_sum_twice {N : ℕ} {c : ℤ} (hc : c∈Ground N)
    (f : ℕ→ℕ) (hf : f 0=0) :
    (∑ q∈Ground N,f (Distance c q))≤2*∑ n∈Finset.Icc 1 N,f n := by
  let U := (Ground N).erase c
  let V := (Finset.Icc 1 N).product (Finset.univ:Finset Bool)
  let code : ℤ→ℕ×Bool := fun q=>(Distance c q,decide (c≤q))
  have hs : U.image code⊆V := by
    intro z hz
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hqc,hq⟩ := Finset.mem_erase.mp hq
    have hp : 0<Distance c q := Int.natAbs_pos.mpr (by omega)
    exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hp,distance_le_ground hc hq⟩,Finset.mem_univ _⟩
  have hi : Set.InjOn code (U:Set ℤ) := by
    intro q _ z _ he
    exact distance_side_injective (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hsum : (∑ q∈U,f (Distance c q))≤∑ z∈V,f z.1 := by
    calc
      _=∑ z∈U.image code,f z.1 := by rw [Finset.sum_image hi]
      _≤_ := Finset.sum_le_sum_of_subset hs
  have he : (∑ q∈Ground N,f (Distance c q))=∑ q∈U,f (Distance c q) := by
    have hh := Finset.sum_erase_add (Ground N) (fun q=>f (Distance c q)) hc
    simpa only [Distance,sub_self,Int.natAbs_zero,hf,add_zero] using hh.symm
  rw [he]
  simpa [V,Finset.sum_product,Finset.sum_mul,Finset.mul_sum,mul_comm] using hsum

theorem actual_exception_second_moment {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    WitnessException (Ground N) c≤6*∑ n∈Finset.Icc 1 N,n.divisors.card^2 := by
  have hfirst : (∑ q∈Ground N,(Distance c q).divisors.card)≤
      ∑ q∈Ground N,(Distance c q).divisors.card^2 := by
    apply Finset.sum_le_sum;intro q hq;nlinarith only [Nat.zero_le ((Distance c q).divisors.card)]
  have hsecond := actual_distance_sum_twice hc (fun n=>n.divisors.card^2) (by simp)
  unfold WitnessException
  omega

theorem actual_exception_harmonic {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hn : (WitnessException (Ground N) c:ℝ)≤6*∑ n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2 :=
    by exact_mod_cast actual_exception_second_moment hc
  have hm := actual_divisor_second_moment N
  linarith only [hn,hm]

theorem actual_bad_members_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    ((BadMembers F c P).card:ℝ)≤6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hh : ((BadMembers F c P).card:ℝ)≤(WitnessException (Ground N) c:ℝ) :=
    by exact_mod_cast actual_restricted_bad_family_bound c P hF
  exact hh.trans (actual_exception_harmonic hc)

theorem actual_exception_tight_dyadic {N J : ℕ} {c : ℤ} (hc : c∈Ground N) (hN : N<2^J) :
    (WitnessException (Ground N) c:ℝ)≤6*(N:ℝ)*(53/100+(7/10:ℝ)*J)^3 := by
  have hh := HarmonicSharp39.actual_harmonic_tight N J hN
  have hnon : 0≤HarmonicAbel29.Harmonic N := by
    unfold HarmonicAbel29.Harmonic;exact Finset.sum_nonneg (fun _ _=>by positivity)
  have hp : HarmonicAbel29.Harmonic N^3≤(53/100+(7/10:ℝ)*J)^3 := by gcongr
  exact (actual_exception_harmonic hc).trans (mul_le_mul_of_nonneg_left hp (by positivity))

theorem actual_exception_natlog {N : ℕ} {c : ℤ} (hc : c∈Ground N) :
    WitnessException (Ground N) c≤48*N*(Nat.log 2 N+1)^3 := by
  let J := Nat.log 2 N+1
  have hjN : 1≤J := by dsimp [J];omega
  have hJ : (1:ℝ)≤J := by exact_mod_cast hjN
  have hh := actual_exception_tight_dyadic (J:=J) hc
    (Nat.lt_pow_succ_log_self (b:=2) (by decide) N)
  have hlin : (53/100:ℝ)+(7/10:ℝ)*J≤2*J := by linarith only [hJ]
  have hp : (53/100+(7/10:ℝ)*J)^3≤8*(J:ℝ)^3 := by
    calc
      _≤(2*(J:ℝ))^3 := by gcongr
      _=8*(J:ℝ)^3 := by ring
  have hm := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤6*(N:ℝ) by positivity)
  have he : (WitnessException (Ground N) c:ℝ)≤48*(N:ℝ)*(J:ℝ)^3 := by nlinarith only [hh,hm]
  exact_mod_cast he

theorem actual_bad_members_tight_dyadic {N J : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hc : c∈Ground N) (hN : N<2^J) (hF : Legal (Ground N) F) :
    ((BadMembers F c P).card:ℝ)≤6*(N:ℝ)*(53/100+(7/10:ℝ)*J)^3 := by
  have hh : ((BadMembers F c P).card:ℝ)≤(WitnessException (Ground N) c:ℝ) :=
    by exact_mod_cast actual_restricted_bad_family_bound c P hF
  exact hh.trans (actual_exception_tight_dyadic hc hN)

theorem actual_avoider_joint_harmonic {N : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hcN : c∈Ground N) (hF : Legal (Ground N) F)
    (hP : P∈F) (hcP : c∉P) (hc : ∀ S∈F,¬IsAP S→c∈S) :
    ∃ u v:ℤ,SupportedEnvelope F c u v ∧
      ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
        (IntervalPool (Ground N) c u v P).card+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  obtain ⟨u,v,hE,hh⟩ := actual_avoider_crooked_interval_budget c P hF hP hcP hc
  have hr : ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
      (IntervalPool (Ground N) c u v P).card+(WitnessException (Ground N) c:ℝ) := by exact_mod_cast hh
  exact ⟨u,v,hE,hr.trans (add_le_add_right (actual_exception_harmonic hcN) _)⟩

theorem actual_avoider_joint_tight_dyadic {N J : ℕ} {F : Finset (Finset ℤ)}
    (c : ℤ) (P : Finset ℤ) (hcN : c∈Ground N) (hN : N<2^J) (hF : Legal (Ground N) F)
    (hP : P∈F) (hcP : c∉P) (hc : ∀ S∈F,¬IsAP S→c∈S) :
    ∃ u v:ℤ,SupportedEnvelope F c u v ∧
      ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
        (IntervalPool (Ground N) c u v P).card+6*(N:ℝ)*(53/100+(7/10:ℝ)*J)^3 := by
  obtain ⟨u,v,hE,hh⟩ := actual_avoider_crooked_interval_budget c P hF hP hcP hc
  have hr : ((PrivatePairExistence.CrookedMembers F).card:ℝ)+(StraddledIntervals F c).card≤
      (IntervalPool (Ground N) c u v P).card+(WitnessException (Ground N) c:ℝ) := by exact_mod_cast hh
  exact ⟨u,v,hE,hr.trans (add_le_add_right (actual_exception_tight_dyadic hcN hN) _)⟩

#print axioms divisor_pair_factors
#print axioms actual_second_moment_encoding
#print axioms quad_pool_harmonic_bound
#print axioms actual_divisor_second_moment
#print axioms distance_le_ground
#print axioms distance_side_injective
#print axioms actual_distance_sum_twice
#print axioms actual_exception_second_moment
#print axioms actual_exception_harmonic
#print axioms actual_bad_members_harmonic
#print axioms actual_exception_tight_dyadic
#print axioms actual_exception_natlog
#print axioms actual_bad_members_tight_dyadic
#print axioms actual_avoider_joint_harmonic
#print axioms actual_avoider_joint_tight_dyadic
end
end JSP233.DivisorMoment45
