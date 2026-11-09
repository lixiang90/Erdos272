module

public import Erdos272.Global.IntegerWindowEndpoints209
public import Erdos272.Resources.IntegerShared209
public import Erdos272.Resources.RootedFinite209
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.IntegerGlobalCases209
open StarCompletion APGeometry NearAP36 DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 IntegerHighPrices209 UniformCapacity208 SharedUniform209
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 200000

inductive Case (N M : ℕ) (G : Finset (Finset ℤ)) : Prop where
  | common (c : ℤ) (hc : c∈Ground N) (hall : ∀S∈G,c∈S) : Case N M G
  | small (T : Finset ℤ) (hT : T∈G) (hsize : T.card<M)
      (hkernel : Kernel (Ground N) (Small G (M-1))=∅) : Case N M G
  | whole (hlow : ∀S∈G,M≤S.card) : Case N M G
  | root_low (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card) (hlow : M≤T.card) (hhigh : T.card<4*M) : Case N M G
  | root_high (c : ℤ) (hc : c∈Ground N) (T : Finset ℤ) (hT : T∈Avoiders G c)
      (hmin : ∀S∈Avoiders G c,T.card≤S.card) (hlow : 4*M≤T.card) : Case N M G

/-- Four actual non-common-root branches arise from the same small subfamily
and the same minimum omitter; no model geometry or cardinality bound is assumed. -/
theorem actual_cases {N M : ℕ} {G : Finset (Finset ℤ)} (hM : 0<M) : Case N M G := by
  by_cases hs : (Small G (M-1)).Nonempty
  · by_cases hk : (Kernel (Ground N) (Small G (M-1))).Nonempty
    · obtain ⟨c,hc⟩:=hk
      obtain ⟨hcN,hcommon⟩:=Finset.mem_filter.mp hc
      by_cases hall : ∀S∈G,c∈S
      · exact Case.common c hcN hall
      · push_neg at hall
        obtain ⟨T,hT,hmin⟩:=actual_minimum_omitter hall
        have hlow : M≤T.card := by
          obtain ⟨hTG,hTc⟩:=Finset.mem_filter.mp hT
          by_contra hn
          exact hTc (hcommon T (Finset.mem_filter.mpr ⟨hTG,by omega⟩))
        by_cases hhigh : T.card<4*M
        · exact Case.root_low c hcN T hT hmin hlow hhigh
        · exact Case.root_high c hcN T hT hmin (by omega)
    · obtain ⟨T,hT⟩:=hs
      obtain ⟨hTG,hsize⟩:=Finset.mem_filter.mp hT
      exact Case.small T hTG (by omega) (Finset.not_nonempty_iff_eq_empty.mp hk)
  · apply Case.whole
    intro S hS
    by_contra hn
    exact hs ⟨S,Finset.mem_filter.mpr ⟨hS,by omega⟩⟩

def NearFees (N M : ℕ) (G : Finset (Finset ℤ)) (g u eta : ℝ) : Prop :=
  ∀A⊆G,(∀S∈A,M≤S.card)→IntegerShared209.NearObligation N A M g u eta

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)} {g u eta : ℝ}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card) (hg : 0≤g)
    (hfees : NearFees N (M w) (SparseCrooked N 11 F) g u eta)
    (hcap : TripleShare*g*(N : ℝ)≤StrongAPResponse209.T)
    (hprice : SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+
      (eta+142+4*(M w : ℝ))/(N : ℝ)<(71/800 : ℝ)) :
    ∃c∈Ground N,∀S∈Retained N 11 F,¬IsAP S→c∈S := by
  let G:=SparseCrooked N 11 F
  have hw:=data_range w
  have hN:=hw.2.1.trans hlo
  have hNH:=hhi.trans hw.2.2.1
  have hNreal : (705098 : ℝ)≤N := by exact_mod_cast hN
  have hN0 : (0 : ℝ)<N := by linarith only [hNreal]
  have hM0 : (0 : ℝ)<M w := by exact_mod_cast (show 0<M w by omega)
  have hG:=actual_sparse_legal (r := 11) hF
  have hbad : ∀S∈G,¬IsAP S := fun S hS=>(actual_sparse_membership.mp hS).2.1
  have hH:=GlobalBootstrap209.harmonic_cap (by omega : 10902≤N) hNH
  have hpr : SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+(eta+142)/(N : ℝ)+
      (4*(M w : ℝ)*N)/(N : ℝ)^2<(71/800 : ℝ) := by
    have he : SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+(eta+142)/(N : ℝ)+
        (4*(M w : ℝ)*N)/(N : ℝ)^2=
        SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+(eta+142+4*(M w : ℝ))/(N : ℝ) := by
      field_simp
      <;> ring
    rwa [he]
  have hpay : ∀A⊆G,(∀S∈A,M w≤S.card)→
      ((G.card : ℝ)≤A.card+4*(M w : ℝ)*N)→False := by
    intro A hAG hlow hcover
    exact IntegerShared209.actual_shared_contradiction (by omega : 10902≤N) hM0 hF hcard hg
      hAG hcover (hfees A hAG hlow) hcap hH hpr
  cases actual_cases (N := N) (G := G) (show 0<M w by omega) with
  | common c hc hall =>
    exact ⟨c,hc,fun S hS hbad=>hall S (Finset.mem_filter.mpr ⟨hS,hbad⟩)⟩
  | small T hT hsize hkernel =>
    exact False.elim (IntegerWindowEndpoints209.actual_small_contradiction w hlo hhi hF hcard hT hsize hkernel)
  | whole hlow =>
    exact False.elim (hpay G (le_refl G) hlow (le_add_of_nonneg_right (by positivity)))
  | root_low c hc T hT hmin hlow hhigh =>
    obtain ⟨hTG,hTc⟩:=Finset.mem_filter.mp hT
    have hdegree:=actual_degree_from_omitter hG hbad hTG hTc
    have hlinear : DegreeBudget N T.card≤T.card*N := by
      unfold DegreeBudget
      calc
        _≤∑_i∈Finset.range T.card,N := Finset.sum_le_sum (fun i hi=>by omega)
        _=_ := by simp [mul_comm]
    have hb:=(hdegree.trans hlinear).trans (Nat.mul_le_mul_right N hhigh.le)
    have hbR : ((RootPart G c).card : ℝ)≤4*(M w : ℝ)*N := by exact_mod_cast hb
    have hp : ((RootPart G c).card : ℝ)+(Avoiders G c).card=G.card := by
      exact_mod_cast root_avoider_card_partition G c
    have hcover : (G.card : ℝ)≤(Avoiders G c).card+4*(M w : ℝ)*N := by linarith only [hbR,hp]
    exact False.elim (hpay (Avoiders G c) (Finset.filter_subset _ _)
      (fun S hS=>hlow.trans (hmin S hS)) hcover)
  | root_high c hc T hT hmin hlow =>
    exact False.elim (IntegerHighRoot209.actual_high_contradiction w hlo hhi hF hcard hT hmin hlow)

theorem actual_original_upper {N : ℕ} {F : Finset (Finset ℤ)} {g u eta : ℝ}
    (w : Fin 11) (hlo : Lower w≤N) (hhi : N≤Upper w)
    (hF : Legal (Ground N) F) (hg : 0≤g)
    (hfees : NearFees N (M w) (SparseCrooked N 11 F) g u eta)
    (hcap : TripleShare*g*(N : ℝ)≤StrongAPResponse209.T)
    (hprice : SharedUniformStrong209.CoupledShare*g*(N : ℝ)+u+
      (eta+142+4*(M w : ℝ))/(N : ℝ)<(71/800 : ℝ)) : F.card≤B N := by
  have hw:=data_range w
  by_cases hc : B N≤F.card
  · exact RootedFinite209.actual_original_upper_of_root11 (by omega) (hhi.trans hw.2.2.1) hF
      (actual_common_root w hlo hhi hF hc hg hfees hcap hprice)
  · omega

#print axioms actual_cases
#print axioms actual_common_root
#print axioms actual_original_upper
end
end JSP233.IntegerGlobalCases209
