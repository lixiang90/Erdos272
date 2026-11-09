module

public import Erdos272.Resources.InitialPreparation208
public import Erdos272.Resources.SourceFees208
public import Erdos272.Resources.UniformFees208
public import Erdos272.Resources.APJoint208
public import Erdos272.Global.RootPaid208
public import Erdos272.Global.SparseSmall39

@[expose] public section

namespace JSP233.SevenFamily208
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39
open PrivateFinset IntrinsicTriples208
open SevenPrices208 HarmonicAbel29 ActualRecoveryChain208 RecoveryPrefix208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def PoolNear (A : Finset (Finset ℤ)) (psi : ℕ→ℝ) (i : ℕ) : Finset (Finset ℤ) :=
  A.filter fun S => ((Pool S).card : ℝ)<psi (i+1)

def JointNear (N : ℕ) (A : Finset (Finset ℤ)) (v M : ℝ) (psi : ℕ→ℝ) (i : ℕ) :
    Finset (Finset ℤ) := A.filter fun S => UniformCapacity208.JointMass N v M S<v^2*psi (i+1)

def UnitNearObligation (N : ℕ) (A : Finset (Finset ℤ)) (g u eta light : ℝ) : Prop :=
  ∃psi : ℕ→ℝ,∃cap : ℕ,Monotone psi ∧ psi 0=0 ∧ 6*g*psi cap=1 ∧
    6*g*(∑i∈Finset.range cap,(psi (i+1)-psi i)*((PoolNear A psi i).card : ℝ))≤
      u*(N : ℝ)^2+eta*N+light

def UniformNearObligation (N : ℕ) (A : Finset (Finset ℤ)) (v g u eta : ℝ) : Prop :=
  ∃psi : ℕ→ℝ,∃cap : ℕ,Monotone psi ∧ psi 0=0 ∧ 0<psi cap ∧
    1195/(42*242*psi cap)=g ∧
    (∑i∈Finset.range cap,(psi (i+1)-psi i)*((JointNear N A v 242 psi i).card : ℝ))/(psi cap)≤
      u*(N : ℝ)^2/v+eta*N

def Small (G : Finset (Finset ℤ)) (L : ℕ) : Finset (Finset ℤ) :=
  G.filter fun S=>S.card≤L

theorem actual_member_nonempty_of_two {N : ℕ} {G : Finset (Finset ℤ)}
    (hF : Legal (Ground N) G) (htwo : 2≤G.card) {T : Finset ℤ} (hT : T∈G) : T.Nonempty := by
  by_contra hn
  have he : T=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hall : ∀S∈G,S=T := by
    intro S hS
    by_contra hST
    obtain ⟨x,hx⟩ := isAP_nonempty (hF.2 S hS T hT hST)
    have hxT := (Finset.mem_inter.mp hx).2
    rw [he] at hxT
    exact Finset.notMem_empty _ hxT
  have hc : G.card≤1 := Finset.card_le_one.mpr (by
    intro S hS U hU
    exact (hall S hS).trans (hall U hU).symm)
  omega

theorem actual_minimum_omitter {G : Finset (Finset ℤ)} {c : ℤ}
    (homit : ∃T∈G,c∉T) :
    ∃T∈Avoiders G c,∀S∈Avoiders G c,T.card≤S.card := by
  have hn : (Avoiders G c).Nonempty := by
    obtain ⟨T,hT,hTc⟩ := homit
    exact ⟨T,Finset.mem_filter.mpr ⟨hT,hTc⟩⟩
  exact Finset.exists_min_image (Avoiders G c) Finset.card hn

theorem actual_small_empty_kernel_direct {N L : ℕ} {G : Finset (Finset ℤ)} {T : Finset ℤ}
    (hF : Legal (Ground N) G) (hbad : ∀S∈G,¬IsAP S) (hT : T∈G) (hne : T.Nonempty)
    (hkernel : Kernel (Ground N) (Small G L)=∅) : G.card≤T.card*L*N := by
  have hcover : G⊆T.biUnion (fun x=>RootPart G x) := by
    intro S hS
    have hST : (S∩T).Nonempty := by
      by_cases he : S=T
      · simpa only [he,Finset.inter_self] using hne
      · exact isAP_nonempty (hF.2 S hS T hT he)
    obtain ⟨x,hx⟩ := hST
    obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_biUnion.mpr ⟨x,hxT,Finset.mem_filter.mpr ⟨hS,hxS⟩⟩
  have hc : ∀x∈T,(RootPart G x).card≤L*N := by
    intro x hx
    obtain ⟨U,hU,hxU⟩ := actual_omitter_of_empty_kernel hkernel x (hF.1 T hT hx)
    obtain ⟨hUG,hUL⟩ := Finset.mem_filter.mp hU
    have hb := actual_degree_from_omitter hF hbad hUG hxU
    have hl : DegreeBudget N U.card≤U.card*N := by
      unfold DegreeBudget
      calc
        _≤∑_i∈Finset.range U.card,N := Finset.sum_le_sum (fun i hi=>by omega)
        _=_ := by simp [mul_comm]
    exact (hb.trans hl).trans (Nat.mul_le_mul_right N hUL)
  calc
    G.card≤(T.biUnion (fun x=>RootPart G x)).card := Finset.card_le_card hcover
    _≤∑x∈T,(RootPart G x).card := Finset.card_biUnion_le
    _≤∑_x∈T,L*N := Finset.sum_le_sum hc
    _=T.card*L*N := by simp [mul_assoc]

theorem actual_unit_source {N : ℕ} {A F : Finset (Finset ℤ)} {g u eta light : ℝ}
    (hAF : A⊆F) (hg : 0≤g) (hfee : UnitNearObligation N A g u eta light) :
    (A.card : ℝ)≤6*g*(∑S∈F,((Pool S).card : ℝ))+u*(N : ℝ)^2+eta*N+light := by
  obtain ⟨psi,cap,hpsi,hzero,hgp,hpaid⟩ := hfee
  have hcover : ∀S∈A,psi cap≤((Pool S).card : ℝ)+
      ∑i∈Finset.range cap,(psi (i+1)-psi i)*(if S∈PoolNear A psi i then 1 else 0) := by
    intro S hS
    have hh := UniformFees208.pointwise_cover psi hpsi
      (fun i => ((Pool S).card : ℝ)<psi (i+1)) cap ((Pool S).card : ℝ)
      (by rw [hzero];positivity) (by intro i hi hn;exact le_of_not_gt hn)
    simpa only [PoolNear,Finset.mem_filter,hS,true_and] using hh
  have hh := LayerPayment208.fractional_cover A (Finset.range cap) (PoolNear A psi)
    (fun S => ((Pool S).card : ℝ)) (fun i=>psi (i+1)-psi i) (psi cap)
    (fun i hi=>Finset.filter_subset _ _) hcover
  have hm := SourceFees208.pool_sum_subset hAF
  have hs := mul_le_mul_of_nonneg_left hh (show 0≤6*g by positivity)
  have ht := mul_le_mul_of_nonneg_left hm (show 0≤6*g by positivity)
  rw [←mul_assoc,hgp,one_mul,mul_add] at hs
  nlinarith only [hs,ht,hpaid]

theorem actual_uniform_source {N : ℕ} {A F : Finset (Finset ℤ)} {v g u eta : ℝ}
    (hN : 2≤N) (hv : 0<v) (hF : Legal (Ground N) F) (hAF : A⊆F)
    (hfee : UniformNearObligation N A v g u eta) :
    (A.card : ℝ)≤g*(N : ℝ)^3/v^3+u*(N : ℝ)^2/v+eta*N := by
  obtain ⟨psi,cap,hpsi,hzero,hpos,hg,hpaid⟩ := hfee
  have hh := UniformFees208.family_price hN hv (by norm_num : (0 : ℝ)<242) hF hAF
    psi hpsi hzero (JointNear N A v 242 psi)
    (fun i=>((JointNear N A v 242 psi i).card : ℝ)) cap hpos
    (fun i hi=>Finset.filter_subset _ _) (fun i hi=>le_rfl) (by
      intro S hS i hi hn
      by_contra hbad
      exact hn (Finset.mem_filter.mpr ⟨hS,lt_of_not_ge hbad⟩))
  rw [hg] at hh
  linarith only [hh,hpaid]

def SmallSingleton (G : Finset (Finset ℤ)) : Prop :=
  ∃A∈Small G 241,∃B∈Small G 241,∃c : ℤ,A∩B={c}

inductive Case (N : ℕ) (G : Finset (Finset ℤ)) : Prop where
  | single (T : Finset ℤ) (hT : T∈G) (hmin : ∀S∈G,T.card≤S.card)
      (hsmall : T.card≤241) (hkernel : Kernel (Ground N) (Small G 241)=∅)
      (hpattern : SmallSingleton G) : Case N G
  | multiple (T : Finset ℤ) (hT : T∈G) (hmin : ∀S∈G,T.card≤S.card)
      (hsmall : T.card≤241) (hkernel : Kernel (Ground N) (Small G 241)=∅)
      (hpattern : ¬SmallSingleton G) : Case N G
  | whole (hlow : ∀S∈G,242≤S.card) : Case N G
  | root_exact (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card) (hcard : T.card=242) : Case N G
  | root_tail (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card) (hlow : 243≤T.card) (hhigh : T.card≤483) : Case N G
  | root_two (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card)
      (hlow : 242*2^1≤T.card) (hhigh : T.card≤2*242*2^1) : Case N G
  | root_high (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card) (j : ℕ) (hj : 2≤j)
      (hlow : 242*2^j≤T.card) (hhigh : T.card≤2*242*2^j) : Case N G

theorem actual_scale {t : ℕ} (ht : 484≤t) :
    ∃j : ℕ,1≤j ∧ 242*2^j≤t ∧ t≤2*242*2^j := by
  let q := t/242
  have hq : 2≤q := (Nat.le_div_iff_mul_le (by decide : 0<242)).mpr (by omega)
  let j := Nat.log 2 q
  have hj : 1≤j := by
    apply (Nat.le_log_iff_pow_le (by decide : 1<2) (by omega : q≠0)).mpr
    norm_num
    exact hq
  have hl := Nat.pow_log_le_self 2 (by omega : q≠0)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1<2) q
  have hprod := Nat.div_mul_le_self t 242
  have hquot : t<2^(j+1)*242 := (Nat.div_lt_iff_lt_mul (by decide : 0<242)).mp hu
  have hm := Nat.mul_le_mul_right 242 hl
  refine ⟨j,hj,?_,?_⟩
  · dsimp only [j] at *
    change q*242≤t at hprod
    nlinarith only [hm,hprod]
  · rw [pow_succ] at hquot
    nlinarith only [hquot]

theorem actual_cases {N : ℕ} {G : Finset (Finset ℤ)}
    (hF : Legal (Ground N) G) (hbad : ∀S∈G,¬IsAP S) (htwo : 2≤G.card)
    (hkernel : Kernel (Ground N) G=∅) : Case N G := by
  by_cases hSmall : Small G 241=∅
  · apply Case.whole
    intro S hS
    by_contra hn
    have hm : S∈Small G 241 := Finset.mem_filter.mpr ⟨hS,by omega⟩
    rw [hSmall] at hm
    exact Finset.notMem_empty _ hm
  · by_cases hsk : Kernel (Ground N) (Small G 241)=∅
    · have hne : G.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image G Finset.card hne
      have hsmall : T.card≤241 := by
        obtain ⟨S,hS⟩ := Finset.nonempty_iff_ne_empty.mpr hSmall
        obtain ⟨hSG,hSc⟩ := Finset.mem_filter.mp hS
        exact (hmin S hSG).trans hSc
      by_cases hp : SmallSingleton G
      · exact Case.single T hT hmin hsmall hsk hp
      · exact Case.multiple T hT hmin hsmall hsk hp
    · obtain ⟨c,hc⟩ := Finset.nonempty_iff_ne_empty.mpr hsk
      obtain ⟨hcN,hcSmall⟩ := Finset.mem_filter.mp hc
      have homit := actual_omitter_of_empty_kernel hkernel c hcN
      obtain ⟨T,hT,hmin⟩ := actual_minimum_omitter homit
      have hsize : 242≤T.card := by
        obtain ⟨hTF,hTc⟩ := Finset.mem_filter.mp hT
        by_contra hn
        exact hTc (hcSmall T (Finset.mem_filter.mpr ⟨hTF,by omega⟩))
      by_cases he : T.card=242
      · exact Case.root_exact c hcN T hT hmin he
      · by_cases hu : T.card≤483
        · exact Case.root_tail c hcN T hT hmin (by omega) hu
        · obtain ⟨j,hj,hl,hu⟩ := actual_scale (by omega : 484≤T.card)
          by_cases hj1 : j=1
          · subst j
            exact Case.root_two c hcN T hT hmin hl hu
          · exact Case.root_high c hcN T hT hmin j (by omega) hl hu

theorem actual_small_payment {N : ℕ} {G : Finset (Finset ℤ)} {T : Finset ℤ}
    (hF : Legal (Ground N) G) (hbad : ∀S∈G,¬IsAP S) (htwo : 2≤G.card)
    (hT : T∈G) (hsmall : T.card≤241)
    (hkernel : Kernel (Ground N) (Small G 241)=∅) : G.card≤58081*N := by
  have hn := actual_member_nonempty_of_two hF htwo hT
  have hb := actual_small_empty_kernel_direct hF hbad hT hn hkernel
  nlinarith only [hb,Nat.mul_le_mul_right (241*N) hsmall]

#print axioms actual_unit_source
#print axioms actual_uniform_source
#print axioms actual_scale
#print axioms actual_cases
#print axioms actual_small_payment
end
end JSP233.SevenFamily208
